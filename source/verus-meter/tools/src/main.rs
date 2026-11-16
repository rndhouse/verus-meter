//! Prepare a relocatable runtime library and exactly its Cargo-built dependencies.
use anyhow::{Context, Result, ensure};
use cargo_metadata::Message;
use clap::Parser;
use std::path::PathBuf;
use std::process::{Command, Stdio};

#[derive(Parser)]
struct Arguments {
    /// Verus artifact directory that will contain the managed resource-runtime bundle.
    destination: PathBuf,
    /// Cargo profile to build (release or dev).
    #[arg(long, default_value = "release", value_parser = ["release", "dev"])]
    profile: String,
}

fn main() -> Result<()> {
    let arguments = Arguments::parse();
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let mut child = Command::new(cargo)
        .current_dir(source)
        .args([
            "build",
            "--locked",
            "--package",
            "verus_meter_runtime",
            "--profile",
            &arguments.profile,
            "--message-format=json-render-diagnostics",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .context("building resource runtime")?;
    let output = child.stdout.take().context("Cargo stdout unavailable")?;
    let mut libraries = Vec::new();
    let mut runtime = None;
    for message in Message::parse_stream(std::io::BufReader::new(output)) {
        match message? {
            Message::CompilerArtifact(artifact) => {
                for filename in artifact.filenames {
                    if filename.extension() == Some("rlib") {
                        if artifact.target.name == "verus_meter_runtime" {
                            runtime = Some(filename.clone());
                        }
                        libraries.push(filename);
                    }
                }
            }
            Message::CompilerMessage(message) => {
                if let Some(rendered) = message.message.rendered {
                    eprint!("{rendered}");
                }
            }
            Message::TextLine(line) => eprintln!("{line}"),
            _ => {}
        }
    }
    ensure!(child.wait()?.success(), "resource runtime build failed");
    let runtime = runtime.context("Cargo did not produce the resource runtime rlib")?;
    std::fs::create_dir_all(&arguments.destination)?;
    let staging =
        tempfile::Builder::new().prefix("runtime-stage-").tempdir_in(&arguments.destination)?;
    let dependencies = staging.path().join("deps");
    std::fs::create_dir(&dependencies)?;
    for library in libraries {
        std::fs::copy(&library, dependencies.join(library.file_name().context("rlib filename")?))?;
    }
    std::fs::copy(runtime, staging.path().join("libverus_meter_runtime.rlib"))?;
    let destination = arguments.destination.join("resource-runtime");
    if destination.exists() {
        std::fs::remove_dir_all(&destination)?;
    }
    std::fs::rename(staging.path(), &destination).context("installing resource runtime bundle")?;
    println!("prepared {}", destination.display());
    Ok(())
}
