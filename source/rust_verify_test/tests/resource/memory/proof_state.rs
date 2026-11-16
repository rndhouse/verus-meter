//! Scheduled metadata transitions must match source execution counts and order.

use super::support::{rejects, verifies};

#[track_caller]
fn check_peak(name: &str, code: &str, peak: u64) {
    verifies(name, &code.replace("BOUND", &format!("{peak}")));
    rejects(
        &format!("{name}_short"),
        &code.replace("BOUND", &format!("{short}", short = peak - 1)),
        "memory budget exceeded",
    );
}

#[test]
fn discarded_remove_preserves_the_reindexed_survivor() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut values = Vec::<Box<[u8;64]>>::with_capacity(2);
        let first = Box::new([0u8;64]); values.push(first);
        let second = Box::new([0u8;64]); values.push(second);
        values.remove(0);
        let scratch = [0u8;256];
    }";
    // Removal drops one payload. The survivor still overlaps scratch alongside
    // the 24-byte handle and unchanged 16-byte backing: 64 + 256 + 24 + 16.
    check_peak("discarded_remove_survivor", code, 360);
}

#[test]
fn buffer_growth_snapshots_and_commits_cover_execution_contexts() {
    for (name, parameter, body, peak) in [
        (
            "overlap",
            "",
            "let mut values = Vec::<u32>::with_capacity(1);
            values.push(1); values.push(2);",
            44,
        ),
        (
            "committed",
            "",
            "let mut values = Vec::<u32>::with_capacity(1);
            values.push(1); values.push(2);
            assert(current(memory) <= 40);
            let scratch = [0u8;128];",
            168,
        ),
        (
            "branch",
            "grow: bool",
            "let mut values = Vec::<u32>::with_capacity(1);
            values.push(1); if grow { values.push(2); }
            assert(current(memory) <= 41);
            let scratch = [0u8;128];",
            169,
        ),
        (
            "loop",
            "",
            "let mut i = 0u8;
            while i < 2
                invariant i <= 2,
                decreases 2 - i,
            {
                let mut values = Vec::<u32>::with_capacity(1);
                values.push(1); values.push(2);
                assert(current(memory) <= 41);
                let scratch = [0u8;128];
                i += 1;
            };",
            169,
        ),
        (
            "field",
            "",
            "let mut data = Data {
                values: Vec::<u32>::with_capacity(1), tag: Box::new([0u8;16]),
            };
            data.values.push(1); data.values.push(2);
            assert(current(memory) <= 64);
            let scratch = [0u8;128];",
            192,
        ),
    ] {
        // Growth overlaps the old 4-byte buffer with a new 16-byte buffer.
        // Afterwards the 24-byte handle retains 16 bytes, alongside scratch.
        // A Boolean/counter adds one; Data adds its 8-byte handle and 16-byte tag.
        let code = format!(
            "struct Data {{ values: Vec<u32>, tag: Box<[u8;16]> }}
            fn f({parameter}) resources peak(memory) <= BOUND {{ {body} }}"
        );
        check_peak(&format!("proof_state_growth_{name}"), &code, peak);
    }
}

#[test]
fn helper_commit_retains_the_declared_replacement_bound() {
    // The helper's 24-byte replacement bound remains charged in the caller:
    // vector handle 24 + retained replacement bound 24 + scratch 128 = 176.
    check_peak(
        "proof_state_helper_commit",
        "fn append(values: &mut Vec<u32>)
            requires old(values).len() == 1,
            ensures final(values).len() == 2,
            resources peak(memory) <= 24,
        { values.push(2); }
        fn f() resources peak(memory) <= BOUND {
            let mut values = Vec::<u32>::with_capacity(1); values.push(1);
            append(&mut values);
            assert(current(memory) <= 48);
            let scratch = [0u8;128];
        }",
        176,
    );
}

#[test]
fn section_commit_uses_its_local_ledger() {
    check_peak(
        "proof_state_section_commit",
        "fn f() resources peak(memory) <= 256 {
            resources peak(memory) <= BOUND {
                let mut values = Vec::<u32>::with_capacity(1);
                values.push(1); values.push(2);
                assert(current(memory) <= 40);
                let scratch = [0u8;128];
            }
        }",
        168,
    );
}
