use crate::config::Args;
use crate::spans::FileStartEndPos;
use crate::verifier::io_vir_err;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use vir::ast::{Krate, Mode, VirErr};

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct CrateMetadata {
    pub crate_id: u64,
    pub original_files: HashMap<Vec<u8>, FileStartEndPos>,
}

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct CrateWithMetadata {
    krate: Krate,
    metadata: CrateMetadata,
}

pub(crate) struct ImportOutput {
    pub(crate) vir_crates: Vec<Krate>,
    pub(crate) metadatas: Vec<CrateMetadata>,
}

pub(crate) fn import_crates(
    args: &Args,
    import_virs_via_cargo: Vec<(String, String)>,
) -> Result<ImportOutput, VirErr> {
    let mut metadatas = Vec::new();
    let mut vir_crates = Vec::new();
    for (_, file_path) in args.import.iter().chain(import_virs_via_cargo.iter()) {
        let mut file = std::io::BufReader::new(match std::fs::File::open(file_path) {
            Ok(file) => file,
            Err(err) => {
                return Err(io_vir_err(
                    format!("could not open imported library file `{file_path}`"),
                    err,
                ));
            }
        });
        let CrateWithMetadata { krate, metadata } = match bincode_next::serde::decode_from_std_read(
            &mut file,
            bincode_next::config::legacy(),
        ) {
            Ok(crate_with_metadata) => crate_with_metadata,
            Err(_e) => {
                return Err(crate::util::error(format!(
                    "failed to deserialize imported library file `{file_path}` - it may need to be rebuilt by Verus"
                )));
            }
        };
        //   let libcrate: Krate = serde_json::from_reader(file).expect("read crate from file");
        // We can also look at other packages: https://github.com/djkoloski/rust_serialization_benchmark
        vir_crates.push(krate);
        metadatas.push(metadata);
    }
    Ok(ImportOutput { vir_crates, metadatas })
}

/// The ordinary Verus interface is exportable before lifetime and SMT checks.
/// A memory certificate becomes visible only after both checks succeed for the
/// whole crate. Keep only the already-pruned export while verification runs.
pub(crate) struct PendingExport {
    destination: PathBuf,
    value: CrateWithMetadata,
}

impl PendingExport {
    pub(crate) fn publish(&self) -> Result<(), VirErr> {
        let directory = self
            .destination
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let write_error =
            |e| io_vir_err(format!("writing exported library `{}`", self.destination.display()), e);
        let mut file = tempfile::NamedTempFile::new_in(directory).map_err(write_error)?;
        {
            let mut output = std::io::BufWriter::new(file.as_file_mut());
            bincode_next::serde::encode_into_std_write(
                &self.value,
                &mut output,
                bincode_next::config::legacy(),
            )
            .map_err(|e| crate::util::error(format!("encoding exported library: {e}")))?;
            output.flush().map_err(write_error)?;
        }
        file.persist(&self.destination).map_err(|e| write_error(e.error))?;
        Ok(())
    }
}

pub(crate) fn export_crate(
    args: &Args,
    export_vir_path_via_cargo: &Option<PathBuf>,
    metadata: CrateMetadata,
    vir_crate: Krate,
) -> Result<Option<PendingExport>, VirErr> {
    let export = args.export.as_ref().map(PathBuf::from);
    let Some(destination) = export.or_else(|| export_vir_path_via_cargo.clone()) else {
        return Ok(None);
    };
    let mut kratex = (*vir_crate).clone();
    kratex.functions.retain(|f| f.x.visibility.restricted_to.is_none());
    for func in kratex.functions.iter_mut() {
        let mut functionx = func.x.clone();
        functionx.decrease_by = None;
        functionx.return_opaque_type_eqs = Arc::new(vec![]);
        if (functionx.mode != Mode::Spec || !functionx.body_visibility.is_public())
            && !matches!(&functionx.kind, vir::ast::FunctionKind::TraitMethodDecl { .. })
        {
            functionx.body = None;
        }
        *func = func.new_x(functionx);
    }
    let mut certificates = Vec::new();
    for (index, fun) in kratex.functions.iter_mut().enumerate() {
        if let Some(body) = fun.x.attrs.resource_body {
            Arc::make_mut(&mut Arc::make_mut(fun).x.attrs).resource_body = None;
            certificates.push((index, body));
        }
    }
    let mut export = PendingExport {
        destination,
        value: CrateWithMetadata { krate: Arc::new(kratex), metadata },
    };
    export.publish()?;
    if certificates.is_empty() {
        return Ok(None);
    }
    for (index, body) in certificates {
        let fun = &mut Arc::make_mut(&mut export.value.krate).functions[index];
        Arc::make_mut(&mut Arc::make_mut(fun).x.attrs).resource_body = Some(body);
    }
    Ok(Some(export))
}
