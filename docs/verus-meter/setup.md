# Verus Meter development checkout

The project is developed directly in a fork of Verus. The original project
README is preserved in [design.md](design.md); the root README and build
instructions belong to upstream Verus.

## Repository baseline

- Fork: `git@github.com:rndhouse/verus-meter.git` (`origin`).
- Upstream: `git@github.com:verus-lang/verus.git` (`upstream`).
- Development branch: `verus-meter`.
- Starting upstream revision: `31e44e600408242839ff456e84550e9f849344e3`.
- Baseline tag: `verus-meter-base`.
- Rust: `1.99.1`, with components pinned by `rust-toolchain.toml`.
- Z3: `4.16.0`, obtained with `source/tools/get-z3.sh`.

Resource contracts are not implemented yet. See [design.md](design.md) for scope
and the next investigation.

## Local build environment

Follow [BUILD.md](../../BUILD.md) for general instructions. On the NixOS machine
used to establish this checkout, OpenSSL development files and `pkg-config` are
provided by a development shell:

```sh
nix-shell -p pkg-config openssl
cd source
rustup toolchain install
bash tools/get-z3.sh
```

Use `bash` explicitly for the download script on NixOS, where `/bin/bash` is
absent. Install build tools inside the ignored build directory:

```sh
export CARGO_INSTALL_ROOT="$PWD/target-verus/tools"
export PATH="$CARGO_INSTALL_ROOT/bin:$PATH"
cargo install cargo-make --version 0.37.24 --locked
```

Use SSH for GitHub dependency fetches as well as repository remotes, without
changing upstream dependency declarations or global Git settings:

```sh
export CARGO_NET_GIT_FETCH_WITH_CLI=true
export GIT_CONFIG_COUNT=1
export GIT_CONFIG_KEY_0='url.git@github.com:.insteadOf'
export GIT_CONFIG_VALUE_0='https://github.com/'
cargo make build
```

These environment variables apply to the current shell and its child processes.
The Z3 release download uses HTTPS; it is not a Git remote.

## Baseline checks

From `source`, in the same environment:

```sh
cargo run --release -p rust_verify -- ../examples/vectors.rs
cargo test --release -p rust_verify_test --test basic --test functions --test loops --test size_of --test mut_refs_slices_arrays
```

These are selected baseline regression suites. The complete verifier suite can
be run with `cargo test --release -p rust_verify_test`.

Initial validation on 2026-11-05:

- Release workspace build: passed.
- `cargo make build`: passed; standard library verification reported
  2,226 verified and zero errors.
- `examples/vectors.rs`: nine verified and zero errors.
- The five selected regression suites: 193 passed, zero failed, three ignored
  by upstream test annotations. The complete test suite was not run.
