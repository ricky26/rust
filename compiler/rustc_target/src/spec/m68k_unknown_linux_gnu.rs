use crate::spec::{LinkerFlavor, Target, TargetOptions};
use crate::abi::Endian;

pub fn target() -> Target {
    let base = super::linux_base::opts();
    Target {
        llvm_target: "m68k-unknown-linux-gnu".to_string(),
        pointer_width: 32,
        data_layout: "E-m:e-p:32:32-i8:8:8-i16:16:16-i32:32:32-n8:16:32-a:0:32-S16".to_string(),
        arch: "m68k".to_string(),
        options: TargetOptions {
            endian: Endian::Big,
            c_int_width: "32".to_string(),
            max_atomic_width: Some(0),
            os: "linux".to_string(),
            env: "gnu".to_string(),
            vendor: "unknown".to_string(),
            linker_flavor: LinkerFlavor::Gcc,
            features: "+soft-float".to_string(),

            ..base
        },
    }
}
