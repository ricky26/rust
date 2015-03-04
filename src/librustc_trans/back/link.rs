// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::archive::{ArchiveBuilder, ArchiveConfig, METADATA_FILENAME};
use super::svh::Svh;

use super::link_gnu;
use super::link_msvc;

use session::config;
use session::config::{OutputFilenames, Input, OutputTypeBitcode, OutputTypeExe, OutputTypeObject};
use session::search_paths::PathKind;
use session::Session;
use metadata::common::LinkMeta;
use metadata::{encoder, cstore, csearch, creader};
use metadata::filesearch::FileDoesntMatch;
use trans::{CrateContext, CrateTranslation, gensym_name};
use middle::ty::{self, Ty};
use util::ppaux;
use util::sha2::{Digest, Sha256};

use std::old_io::fs::PathExtensions;
use std::old_io::{fs, TempDir};
use std::old_io;
use std::mem;
use std::string::String;
use flate;
use serialize::hex::ToHex;
use syntax::ast;
use syntax::ast_map::{PathElem, PathElems, PathName};
use syntax::attr::AttrMetaMethods;
use syntax::codemap::Span;
use syntax::parse::token;

// RLIB LLVM-BYTECODE OBJECT LAYOUT
// Version 1
// Bytes    Data
// 0..10    "RUST_OBJECT" encoded in ASCII
// 11..14   format version as little-endian u32
// 15..22   size in bytes of deflate compressed LLVM bitcode as
//          little-endian u64
// 23..     compressed LLVM bitcode

// This is the "magic number" expected at the beginning of a LLVM bytecode
// object in an rlib.
pub const RLIB_BYTECODE_OBJECT_MAGIC: &'static [u8] = b"RUST_OBJECT";

// The version number this compiler will write to bytecode objects in rlibs
pub const RLIB_BYTECODE_OBJECT_VERSION: u32 = 1;

// The offset in bytes the bytecode object format version number can be found at
pub const RLIB_BYTECODE_OBJECT_VERSION_OFFSET: uint = 11;

// The offset in bytes the size of the compressed bytecode can be found at in
// format version 1
pub const RLIB_BYTECODE_OBJECT_V1_DATASIZE_OFFSET: uint =
    RLIB_BYTECODE_OBJECT_VERSION_OFFSET + 4;

// The offset in bytes the compressed LLVM bytecode can be found at in format
// version 1
pub const RLIB_BYTECODE_OBJECT_V1_DATA_OFFSET: uint =
    RLIB_BYTECODE_OBJECT_V1_DATASIZE_OFFSET + 8;


/*
 * Name mangling and its relationship to metadata. This is complex. Read
 * carefully.
 *
 * The semantic model of Rust linkage is, broadly, that "there's no global
 * namespace" between crates. Our aim is to preserve the illusion of this
 * model despite the fact that it's not *quite* possible to implement on
 * modern linkers. We initially didn't use system linkers at all, but have
 * been convinced of their utility.
 *
 * There are a few issues to handle:
 *
 *  - Linkers operate on a flat namespace, so we have to flatten names.
 *    We do this using the C++ namespace-mangling technique. Foo::bar
 *    symbols and such.
 *
 *  - Symbols with the same name but different types need to get different
 *    linkage-names. We do this by hashing a string-encoding of the type into
 *    a fixed-size (currently 16-byte hex) cryptographic hash function (CHF:
 *    we use SHA256) to "prevent collisions". This is not airtight but 16 hex
 *    digits on uniform probability means you're going to need 2**32 same-name
 *    symbols in the same process before you're even hitting birthday-paradox
 *    collision probability.
 *
 *  - Symbols in different crates but with same names "within" the crate need
 *    to get different linkage-names.
 *
 *  - The hash shown in the filename needs to be predictable and stable for
 *    build tooling integration. It also needs to be using a hash function
 *    which is easy to use from Python, make, etc.
 *
 * So here is what we do:
 *
 *  - Consider the package id; every crate has one (specified with crate_id
 *    attribute).  If a package id isn't provided explicitly, we infer a
 *    versionless one from the output name. The version will end up being 0.0
 *    in this case. CNAME and CVERS are taken from this package id. For
 *    example, github.com/mozilla/CNAME#CVERS.
 *
 *  - Define CMH as SHA256(crateid).
 *
 *  - Define CMH8 as the first 8 characters of CMH.
 *
 *  - Compile our crate to lib CNAME-CMH8-CVERS.so
 *
 *  - Define STH(sym) as SHA256(CMH, type_str(sym))
 *
 *  - Suffix a mangled sym with ::STH@CVERS, so that it is unique in the
 *    name, non-name metadata, and type sense, and versioned in the way
 *    system linkers understand.
 */

pub fn find_crate_name(sess: Option<&Session>,
                       attrs: &[ast::Attribute],
                       input: &Input) -> String {
    let validate = |s: String, span: Option<Span>| {
        creader::validate_crate_name(sess, &s[..], span);
        s
    };

    // Look in attributes 100% of the time to make sure the attribute is marked
    // as used. After doing this, however, we still prioritize a crate name from
    // the command line over one found in the #[crate_name] attribute. If we
    // find both we ensure that they're the same later on as well.
    let attr_crate_name = attrs.iter().find(|at| at.check_name("crate_name"))
                               .and_then(|at| at.value_str().map(|s| (at, s)));

    if let Some(sess) = sess {
        if let Some(ref s) = sess.opts.crate_name {
            if let Some((attr, ref name)) = attr_crate_name {
                if *s != &name[..] {
                    let msg = format!("--crate-name and #[crate_name] are \
                                       required to match, but `{}` != `{}`",
                                      s, name);
                    sess.span_err(attr.span, &msg[..]);
                }
            }
            return validate(s.clone(), None);
        }
    }

    if let Some((attr, s)) = attr_crate_name {
        return validate(s.to_string(), Some(attr.span));
    }
    if let Input::File(ref path) = *input {
        if let Some(s) = path.filestem_str() {
            return validate(s.to_string(), None);
        }
    }

    "rust-out".to_string()
}

pub fn build_link_meta(sess: &Session, krate: &ast::Crate,
                       name: String) -> LinkMeta {
    let r = LinkMeta {
        crate_name: name,
        crate_hash: Svh::calculate(&sess.opts.cg.metadata, krate),
    };
    info!("{:?}", r);
    return r;
}

fn truncated_hash_result(symbol_hasher: &mut Sha256) -> String {
    let output = symbol_hasher.result_bytes();
    // 64 bits should be enough to avoid collisions.
    output[.. 8].to_hex().to_string()
}


// This calculates STH for a symbol, as defined above
fn symbol_hash<'tcx>(tcx: &ty::ctxt<'tcx>,
                     symbol_hasher: &mut Sha256,
                     t: Ty<'tcx>,
                     link_meta: &LinkMeta)
                     -> String {
    // NB: do *not* use abbrevs here as we want the symbol names
    // to be independent of one another in the crate.

    symbol_hasher.reset();
    symbol_hasher.input_str(&link_meta.crate_name[]);
    symbol_hasher.input_str("-");
    symbol_hasher.input_str(link_meta.crate_hash.as_str());
    for meta in &*tcx.sess.crate_metadata.borrow() {
        symbol_hasher.input_str(&meta[..]);
    }
    symbol_hasher.input_str("-");
    symbol_hasher.input_str(&encoder::encoded_ty(tcx, t)[]);
    // Prefix with 'h' so that it never blends into adjacent digits
    let mut hash = String::from_str("h");
    hash.push_str(&truncated_hash_result(symbol_hasher)[]);
    hash
}

fn get_symbol_hash<'a, 'tcx>(ccx: &CrateContext<'a, 'tcx>, t: Ty<'tcx>) -> String {
    match ccx.type_hashcodes().borrow().get(&t) {
        Some(h) => return h.to_string(),
        None => {}
    }

    let mut symbol_hasher = ccx.symbol_hasher().borrow_mut();
    let hash = symbol_hash(ccx.tcx(), &mut *symbol_hasher, t, ccx.link_meta());
    ccx.type_hashcodes().borrow_mut().insert(t, hash.clone());
    hash
}


// Name sanitation. LLVM will happily accept identifiers with weird names, but
// gas doesn't!
// gas accepts the following characters in symbols: a-z, A-Z, 0-9, ., _, $
pub fn sanitize(s: &str) -> String {
    let mut result = String::new();
    for c in s.chars() {
        match c {
            // Escape these with $ sequences
            '@' => result.push_str("$SP$"),
            '*' => result.push_str("$BP$"),
            '&' => result.push_str("$RF$"),
            '<' => result.push_str("$LT$"),
            '>' => result.push_str("$GT$"),
            '(' => result.push_str("$LP$"),
            ')' => result.push_str("$RP$"),
            ',' => result.push_str("$C$"),

            // '.' doesn't occur in types and functions, so reuse it
            // for ':' and '-'
            '-' | ':' => result.push('.'),

            // These are legal symbols
            'a' ... 'z'
            | 'A' ... 'Z'
            | '0' ... '9'
            | '_' | '.' | '$' => result.push(c),

            _ => {
                result.push('$');
                for c in c.escape_unicode().skip(1) {
                    match c {
                        '{' => {},
                        '}' => result.push('$'),
                        c => result.push(c),
                    }
                }
            }
        }
    }

    // Underscore-qualify anything that didn't start as an ident.
    if result.len() > 0 &&
        result.as_bytes()[0] != '_' as u8 &&
        ! (result.as_bytes()[0] as char).is_xid_start() {
        return format!("_{}", &result[..]);
    }

    return result;
}

pub fn mangle<PI: Iterator<Item=PathElem>>(path: PI,
                                      hash: Option<&str>) -> String {
    // Follow C++ namespace-mangling style, see
    // http://en.wikipedia.org/wiki/Name_mangling for more info.
    //
    // It turns out that on OSX you can actually have arbitrary symbols in
    // function names (at least when given to LLVM), but this is not possible
    // when using unix's linker. Perhaps one day when we just use a linker from LLVM
    // we won't need to do this name mangling. The problem with name mangling is
    // that it seriously limits the available characters. For example we can't
    // have things like &T or ~[T] in symbol names when one would theoretically
    // want them for things like impls of traits on that type.
    //
    // To be able to work on all platforms and get *some* reasonable output, we
    // use C++ name-mangling.

    let mut n = String::from_str("_ZN"); // _Z == Begin name-sequence, N == nested

    fn push(n: &mut String, s: &str) {
        let sani = sanitize(s);
        n.push_str(&format!("{}{}", sani.len(), sani)[]);
    }

    // First, connect each component with <len, name> pairs.
    for e in path {
        push(&mut n, &token::get_name(e.name()))
    }

    match hash {
        Some(s) => push(&mut n, s),
        None => {}
    }

    n.push('E'); // End name-sequence.
    n
}

pub fn exported_name(path: PathElems, hash: &str) -> String {
    mangle(path, Some(hash))
}

pub fn mangle_exported_name<'a, 'tcx>(ccx: &CrateContext<'a, 'tcx>, path: PathElems,
                                      t: Ty<'tcx>, id: ast::NodeId) -> String {
    let mut hash = get_symbol_hash(ccx, t);

    // Paths can be completely identical for different nodes,
    // e.g. `fn foo() { { fn a() {} } { fn a() {} } }`, so we
    // generate unique characters from the node id. For now
    // hopefully 3 characters is enough to avoid collisions.
    static EXTRA_CHARS: &'static str =
        "abcdefghijklmnopqrstuvwxyz\
         ABCDEFGHIJKLMNOPQRSTUVWXYZ\
         0123456789";
    let id = id as uint;
    let extra1 = id % EXTRA_CHARS.len();
    let id = id / EXTRA_CHARS.len();
    let extra2 = id % EXTRA_CHARS.len();
    let id = id / EXTRA_CHARS.len();
    let extra3 = id % EXTRA_CHARS.len();
    hash.push(EXTRA_CHARS.as_bytes()[extra1] as char);
    hash.push(EXTRA_CHARS.as_bytes()[extra2] as char);
    hash.push(EXTRA_CHARS.as_bytes()[extra3] as char);

    exported_name(path, &hash[..])
}

pub fn mangle_internal_name_by_type_and_seq<'a, 'tcx>(ccx: &CrateContext<'a, 'tcx>,
                                                      t: Ty<'tcx>,
                                                      name: &str) -> String {
    let s = ppaux::ty_to_string(ccx.tcx(), t);
    let path = [PathName(token::intern(&s[..])),
                gensym_name(name)];
    let hash = get_symbol_hash(ccx, t);
    mangle(path.iter().cloned(), Some(&hash[..]))
}

pub fn mangle_internal_name_by_path_and_seq(path: PathElems, flav: &str) -> String {
    mangle(path.chain(Some(gensym_name(flav)).into_iter()), None)
}

pub fn get_cc_prog(sess: &Session) -> String {
    match sess.opts.cg.linker {
        Some(ref linker) => return linker.to_string(),
        None => sess.target.target.options.linker.clone(),
    }
}

pub fn remove(sess: &Session, path: &Path) {
    match fs::unlink(path) {
        Ok(..) => {}
        Err(e) => {
            sess.err(&format!("failed to remove {}: {}",
                             path.display(),
                             e)[]);
        }
    }
}

/// Perform the linkage portion of the compilation phase. This will generate all
/// of the requested outputs for this compilation session.
pub fn link_binary(sess: &Session,
                   trans: &CrateTranslation,
                   outputs: &OutputFilenames,
                   crate_name: &str) -> Vec<Path> {
    let mut out_filenames = Vec::new();
    for &crate_type in &*sess.crate_types.borrow() {
        if invalid_output_for_target(sess, crate_type) {
            sess.bug(&format!("invalid output type `{:?}` for target os `{}`",
                             crate_type, sess.opts.target_triple)[]);
        }
        let out_file = link_binary_output(sess, trans, crate_type, outputs,
                                          crate_name);
        out_filenames.push(out_file);
    }

    // Remove the temporary object file and metadata if we aren't saving temps
    if !sess.opts.cg.save_temps {
        let obj_filename = outputs.temp_path(OutputTypeObject);
        if !sess.opts.output_types.contains(&OutputTypeObject) {
            remove(sess, &obj_filename);
        }
        remove(sess, &obj_filename.with_extension("metadata.o"));
    }

    out_filenames
}


/// Returns default crate type for target
///
/// Default crate type is used when crate type isn't provided neither
/// through cmd line arguments nor through crate attributes
///
/// It is CrateTypeExecutable for all platforms but iOS as there is no
/// way to run iOS binaries anyway without jailbreaking and
/// interaction with Rust code through static library is the only
/// option for now
pub fn default_output_for_target(sess: &Session) -> config::CrateType {
    if !sess.target.target.options.executables {
        config::CrateTypeStaticlib
    } else {
        config::CrateTypeExecutable
    }
}

/// Checks if target supports crate_type as output
pub fn invalid_output_for_target(sess: &Session,
                                 crate_type: config::CrateType) -> bool {
    match (sess.target.target.options.dynamic_linking,
           sess.target.target.options.executables, crate_type) {
        (false, _, config::CrateTypeDylib) => true,
        (_, false, config::CrateTypeExecutable) => true,
        _ => false
    }
}

fn is_writeable(p: &Path) -> bool {
    match p.stat() {
        Err(..) => true,
        Ok(m) => m.perm & old_io::USER_WRITE == old_io::USER_WRITE
    }
}

pub fn filename_for_input(sess: &Session,
                          crate_type: config::CrateType,
                          name: &str,
                          out_filename: &Path) -> Path {
    let libname = format!("{}{}", name, sess.opts.cg.extra_filename);
    match crate_type {
        config::CrateTypeRlib => {
            out_filename.with_filename(format!("lib{}.rlib", libname))
        }
        config::CrateTypeDylib => {
            let (prefix, suffix) = (&sess.target.target.options.dll_prefix[],
                                    &sess.target.target.options.dll_suffix[]);
            out_filename.with_filename(format!("{}{}{}",
                                               prefix,
                                               libname,
                                               suffix))
        }
        config::CrateTypeStaticlib => {
            out_filename.with_filename(format!("lib{}.a", libname))
        }
        config::CrateTypeExecutable => {
            let suffix = &sess.target.target.options.exe_suffix[];
            out_filename.with_filename(format!("{}{}", libname, suffix))
        }
    }
}

fn link_binary_output(sess: &Session,
                      trans: &CrateTranslation,
                      crate_type: config::CrateType,
                      outputs: &OutputFilenames,
                      crate_name: &str) -> Path {
    let obj_filename = outputs.temp_path(OutputTypeObject);
    let out_filename = match outputs.single_output_file {
        Some(ref file) => file.clone(),
        None => {
            let out_filename = outputs.path(OutputTypeExe);
            filename_for_input(sess, crate_type, crate_name, &out_filename)
        }
    };

    // Make sure the output and obj_filename are both writeable.
    // Mac, FreeBSD, and Windows system linkers check this already --
    // however, the Linux linker will happily overwrite a read-only file.
    // We should be consistent.
    let obj_is_writeable = is_writeable(&obj_filename);
    let out_is_writeable = is_writeable(&out_filename);
    if !out_is_writeable {
        sess.fatal(&format!("output file {} is not writeable -- check its \
                            permissions.",
                           out_filename.display())[]);
    }
    else if !obj_is_writeable {
        sess.fatal(&format!("object file {} is not writeable -- check its \
                            permissions.",
                           obj_filename.display())[]);
    }

    match crate_type {
        config::CrateTypeRlib => {
            link_rlib(sess, Some(trans), &obj_filename, &out_filename).build();
        }
        config::CrateTypeStaticlib => {
            link_staticlib(sess, &obj_filename, &out_filename);
        }
        config::CrateTypeExecutable => {
            link_natively(sess, trans, false, &obj_filename, &out_filename);
        }
        config::CrateTypeDylib => {
            link_natively(sess, trans, true, &obj_filename, &out_filename);
        }
    }

    out_filename
}

pub fn archive_search_paths(sess: &Session) -> Vec<Path> {
    let mut search = Vec::new();
    sess.target_filesearch(PathKind::Native).for_each_lib_search_path(|path, _| {
        search.push(path.clone());
        FileDoesntMatch
    });
    return search;
}

// Create an 'rlib'
//
// An rlib in its current incarnation is essentially a renamed .a file. The
// rlib primarily contains the object file of the crate, but it also contains
// all of the object files from native libraries. This is done by unzipping
// native libraries and inserting all of the contents into this archive.
fn link_rlib<'a>(sess: &'a Session,
                 trans: Option<&CrateTranslation>, // None == no metadata/bytecode
                 obj_filename: &Path,
                 out_filename: &Path) -> ArchiveBuilder<'a> {
    let handler = &sess.diagnostic().handler;
    let config = ArchiveConfig {
        handler: handler,
        dst: out_filename.clone(),
        lib_search_paths: archive_search_paths(sess),
        slib_prefix: sess.target.target.options.staticlib_prefix.clone(),
        slib_suffix: sess.target.target.options.staticlib_suffix.clone(),
        maybe_ar_prog: sess.opts.cg.ar.clone()
    };
    let mut ab = ArchiveBuilder::create(config);
    ab.add_file(obj_filename).unwrap();

    for &(ref l, kind) in &*sess.cstore.get_used_libraries().borrow() {
        match kind {
            cstore::NativeStatic => {
                ab.add_native_library(&l[..]).unwrap();
            }
            cstore::NativeFramework | cstore::NativeUnknown => {}
        }
    }

    // After adding all files to the archive, we need to update the
    // symbol table of the archive.
    ab.update_symbols();

    let mut ab = match sess.target.target.options.is_like_osx {
        // For OSX/iOS, we must be careful to update symbols only when adding
        // object files.  We're about to start adding non-object files, so run
        // `ar` now to process the object files.
        true => ab.build().extend(),
        false => ab,
    };

    // Note that it is important that we add all of our non-object "magical
    // files" *after* all of the object files in the archive. The reason for
    // this is as follows:
    //
    // * When performing LTO, this archive will be modified to remove
    //   obj_filename from above. The reason for this is described below.
    //
    // * When the system linker looks at an archive, it will attempt to
    //   determine the architecture of the archive in order to see whether its
    //   linkable.
    //
    //   The algorithm for this detection is: iterate over the files in the
    //   archive. Skip magical SYMDEF names. Interpret the first file as an
    //   object file. Read architecture from the object file.
    //
    // * As one can probably see, if "metadata" and "foo.bc" were placed
    //   before all of the objects, then the architecture of this archive would
    //   not be correctly inferred once 'foo.o' is removed.
    //
    // Basically, all this means is that this code should not move above the
    // code above.
    match trans {
        Some(trans) => {
            // Instead of putting the metadata in an object file section, rlibs
            // contain the metadata in a separate file. We use a temp directory
            // here so concurrent builds in the same directory don't try to use
            // the same filename for metadata (stomping over one another)
            let tmpdir = TempDir::new("rustc").ok().expect("needs a temp dir");
            let metadata = tmpdir.path().join(METADATA_FILENAME);
            match fs::File::create(&metadata).write_all(&trans.metadata[]) {
                Ok(..) => {}
                Err(e) => {
                    sess.err(&format!("failed to write {}: {}",
                                     metadata.display(),
                                     e)[]);
                    sess.abort_if_errors();
                }
            }
            ab.add_file(&metadata).unwrap();
            remove(sess, &metadata);

            // For LTO purposes, the bytecode of this library is also inserted
            // into the archive.  If codegen_units > 1, we insert each of the
            // bitcode files.
            for i in 0..sess.opts.cg.codegen_units {
                // Note that we make sure that the bytecode filename in the
                // archive is never exactly 16 bytes long by adding a 16 byte
                // extension to it. This is to work around a bug in LLDB that
                // would cause it to crash if the name of a file in an archive
                // was exactly 16 bytes.
                let bc_filename = obj_filename.with_extension(&format!("{}.bc", i));
                let bc_deflated_filename = obj_filename.with_extension(
                    &format!("{}.bytecode.deflate", i)[]);

                let bc_data = match fs::File::open(&bc_filename).read_to_end() {
                    Ok(buffer) => buffer,
                    Err(e) => sess.fatal(&format!("failed to read bytecode: {}",
                                                 e)[])
                };

                let bc_data_deflated = match flate::deflate_bytes(&bc_data[..]) {
                    Some(compressed) => compressed,
                    None => sess.fatal(&format!("failed to compress bytecode from {}",
                                               bc_filename.display())[])
                };

                let mut bc_file_deflated = match fs::File::create(&bc_deflated_filename) {
                    Ok(file) => file,
                    Err(e) => {
                        sess.fatal(&format!("failed to create compressed bytecode \
                                            file: {}", e)[])
                    }
                };

                match write_rlib_bytecode_object_v1(&mut bc_file_deflated,
                                                    bc_data_deflated.as_slice()) {
                    Ok(()) => {}
                    Err(e) => {
                        sess.err(&format!("failed to write compressed bytecode: \
                                          {}", e)[]);
                        sess.abort_if_errors()
                    }
                };

                ab.add_file(&bc_deflated_filename).unwrap();
                remove(sess, &bc_deflated_filename);

                // See the bottom of back::write::run_passes for an explanation
                // of when we do and don't keep .0.bc files around.
                let user_wants_numbered_bitcode =
                        sess.opts.output_types.contains(&OutputTypeBitcode) &&
                        sess.opts.cg.codegen_units > 1;
                if !sess.opts.cg.save_temps && !user_wants_numbered_bitcode {
                    remove(sess, &bc_filename);
                }
            }

            // After adding all files to the archive, we need to update the
            // symbol table of the archive. This currently dies on OSX (see
            // #11162), and isn't necessary there anyway
            if !sess.target.target.options.is_like_osx {
                ab.update_symbols();
            }
        }

        None => {}
    }

    ab
}

fn write_rlib_bytecode_object_v1<T: Writer>(writer: &mut T,
                                            bc_data_deflated: &[u8])
                                         -> ::std::old_io::IoResult<()> {
    let bc_data_deflated_size: u64 = bc_data_deflated.len() as u64;

    try! { writer.write_all(RLIB_BYTECODE_OBJECT_MAGIC) };
    try! { writer.write_le_u32(1) };
    try! { writer.write_le_u64(bc_data_deflated_size) };
    try! { writer.write_all(&bc_data_deflated[..]) };

    let number_of_bytes_written_so_far =
        RLIB_BYTECODE_OBJECT_MAGIC.len() +                // magic id
        mem::size_of_val(&RLIB_BYTECODE_OBJECT_VERSION) + // version
        mem::size_of_val(&bc_data_deflated_size) +        // data size field
        bc_data_deflated_size as uint;                    // actual data

    // If the number of bytes written to the object so far is odd, add a
    // padding byte to make it even. This works around a crash bug in LLDB
    // (see issue #15950)
    if number_of_bytes_written_so_far % 2 == 1 {
        try! { writer.write_u8(0) };
    }

    return Ok(());
}

// Create a static archive
//
// This is essentially the same thing as an rlib, but it also involves adding
// all of the upstream crates' objects into the archive. This will slurp in
// all of the native libraries of upstream dependencies as well.
//
// Additionally, there's no way for us to link dynamic libraries, so we warn
// about all dynamic library dependencies that they're not linked in.
//
// There's no need to include metadata in a static archive, so ensure to not
// link in the metadata object file (and also don't prepare the archive with a
// metadata file).
fn link_staticlib(sess: &Session, obj_filename: &Path, out_filename: &Path) {
    let ab = link_rlib(sess, None, obj_filename, out_filename);
    let mut ab = match sess.target.target.options.is_like_osx {
        true => ab.build().extend(),
        false => ab,
    };
    if sess.target.target.options.morestack {
        ab.add_native_library("morestack").unwrap();
    }
    if !sess.target.target.options.no_compiler_rt {
        ab.add_native_library("compiler-rt").unwrap();
    }

    let crates = sess.cstore.get_used_crates(cstore::RequireStatic);
    let mut all_native_libs = vec![];

    for &(cnum, ref path) in &crates {
        let ref name = sess.cstore.get_crate_data(cnum).name;
        let p = match *path {
            Some(ref p) => p.clone(), None => {
                sess.err(&format!("could not find rlib for: `{}`",
                                 name)[]);
                continue
            }
        };
        ab.add_rlib(&p, &name[..], sess.lto()).unwrap();

        let native_libs = csearch::get_native_libraries(&sess.cstore, cnum);
        all_native_libs.extend(native_libs.into_iter());
    }

    ab.update_symbols();
    let _ = ab.build();

    if !all_native_libs.is_empty() {
        sess.note("link against the following native artifacts when linking against \
                  this static library");
        sess.note("the order and any duplication can be significant on some platforms, \
                  and so may need to be preserved");
    }

    for &(kind, ref lib) in &all_native_libs {
        let name = match kind {
            cstore::NativeStatic => "static library",
            cstore::NativeUnknown => "library",
            cstore::NativeFramework => "framework",
        };
        sess.note(&format!("{}: {}", name, *lib)[]);
    }
}

// Create a dynamic library or executable
//
// This will invoke the system linker/cc to create the resulting file. This
// links to all upstream files as well.
fn link_natively(sess: &Session, trans: &CrateTranslation, dylib: bool,
                 obj_filename: &Path, out_filename: &Path) {

    if sess.target.target.options.is_like_msvc {
        link_msvc::link_natively(sess, trans, dylib, obj_filename, out_filename)
    } else {
        link_gnu::link_natively(sess, trans, dylib, obj_filename, out_filename)
    }
}
