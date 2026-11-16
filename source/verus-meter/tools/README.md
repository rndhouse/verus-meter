# Runtime artifact preparation

`prepare-resource-runtime` is a source-tree development tool. It builds the runtime
through Cargo and uses Cargo's artifact messages to collect the runtime library
and its library dependencies. It replaces only the managed `resource-runtime/`
directory under the selected Verus artifact directory, removing stale dependency
files. The bundle contains no per-function formulas or generated source files.

From `source/`, after building Verus:

```sh
cargo run --release -p verus_meter_tools --bin prepare-resource-runtime -- target-verus/release
```

The default runtime profile is `release`; `--profile dev` prepares a development
runtime instead. The tool is used by the existing default build workflows and is
not needed by deployed applications. Standalone Verus discovers the bundle,
release staging includes it, and Cargo clients use their own declared dependency.
