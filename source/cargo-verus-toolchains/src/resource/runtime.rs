//! The runtime bundle is optional in older distributions. New prepared builds
//! include it with its complete dependency directory for standalone queries.
use std::path::Path;

pub(crate) fn copy_bundle(source: &Path, destination: &Path) -> std::io::Result<()> {
    let source = source.join("resource-runtime");
    if !source.exists() {
        return Ok(());
    }
    copy_directory(&source, &destination.join("resource-runtime"))
}

fn copy_directory(source: &Path, destination: &Path) -> std::io::Result<()> {
    std::fs::create_dir(destination)?;
    for entry in std::fs::read_dir(source)? {
        let entry = entry?;
        let target = destination.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            copy_directory(&entry.path(), &target)?;
        } else {
            std::fs::copy(entry.path(), target)?;
        }
    }
    Ok(())
}
