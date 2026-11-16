//! Standalone runtime discovery. Cargo clients retain their explicitly resolved
//! dependencies; an installed bundle is optional for programs without queries.
use std::path::Path;

pub(crate) fn extend_args(arguments: &mut Vec<String>, root: &Path) {
    let explicit = arguments.windows(2).any(|pair| {
        pair[0] == "--extern" && pair[1].split('=').next() == Some("verus_meter_runtime")
    }) || arguments
        .iter()
        .filter_map(|arg| arg.strip_prefix("--extern="))
        .any(|arg| arg.split('=').next() == Some("verus_meter_runtime"));
    if explicit {
        return;
    }
    let bundle = root.join("resource-runtime");
    let library = bundle.join("libverus_meter_runtime.rlib");
    if !library.is_file() {
        return;
    }
    arguments.extend([
        "--extern".to_owned(),
        format!("verus_meter_runtime={}", library.display()),
        "-L".to_owned(),
        format!("dependency={}", bundle.join("deps").display()),
    ]);
}
