//! A new buffer's carrier can finish in the publication loop while a peer
//! from each completed visit remains outstanding until a later drain.
use super::{GLOBAL, PRODUCT};
use crate::common::{assert_vir_error_msg, assert_vir_error_msgs};

#[test]
fn immediate_join_preserves_backings_across_publications() {
    let push = "handles.push(std::thread::spawn(move || root));";
    let pop = "handles.pop().unwrap()";
    for (case, declaration, membership, publish, receiver, cleanup, frame) in [
        ("direct", "", "", "let carrier = std::thread::spawn(move || root);", "carrier", "", 46),
        (
            "through_slot",
            "let mut handles = Vec::with_capacity(n as usize);",
            "handles.len() == 0,",
            push,
            pop,
            "drop(handles);",
            86,
        ),
        (
            "growing_slot",
            "let mut handles = Vec::new();",
            "handles.len() == 0,",
            push,
            pop,
            "drop(handles);",
            102,
        ),
    ] {
        // At n=2 a reserved vector has two slots. A vector grown on first push
        // retains four, even after pop. Each peer adds a tag and 59 backing bytes.
        let empty = if declaration.is_empty() { 30 } else { 54 };
        let one = frame + 60;
        let two = frame + 120;
        let program = format!(
            r#"
            use vstd::prelude::*;
            verus! {{
            {PRODUCT}
            fn publish(n: u16, b: u16)
                requires 0 <= n as int * (41 + b as int) <= 5000000000int,
                resources peak(memory) <= n * 17 + n * (41 + b) + 256
            {{
                proof {{ product(n as int, 41 + b as int); }}
                {declaration}
                let mut peers = Vec::with_capacity(n as usize);
                let mut i = 0u16;
                while i < n invariant {membership} peers.len() == i, i <= n, decreases n - i, {{
                    proof {{ product(n as int, 41 + b as int); }}
                    if i == 1 && n == 2 && b == 19 {{ assert(current(memory) <= {one}); }}
                    let root = std::sync::Arc::new(Vec::<u8>::with_capacity(b as usize));
                    let alias = root.clone();
                    peers.push(std::thread::spawn(move || alias));
                    {publish}
                    let returned = {receiver}.join().unwrap();
                    drop(returned);
                    i += 1;
                }}
                if n == 0 {{ assert(current(memory) <= {empty}); }}
                if n == 2 && b == 19 {{ assert(current(memory) <= {two}); }}
                while peers.len() > 0 invariant peers.len() <= n, decreases peers.len(), {{
                    proof {{ product(n as int, 41 + b as int); }}
                    let peer = peers.pop().unwrap().join().unwrap();
                    drop(peer);
                }}
                if n == 2 && b == 19 {{ assert(current(memory) <= {frame}); }}
                drop(peers); {cleanup}
                assert(current(memory) <= 6);
            }}
            }}
        "#
        );
        assert_vir_error_msg(
            crate::verify_one_file(case, program.clone(), &[]).unwrap_err(),
            GLOBAL,
        );
        for (stage, bound) in [("next_visit", one), ("after_publication", two)] {
            let short = program.replace(&format!("<= {bound}"), &format!("<= {}", bound - 1));
            assert_vir_error_msgs(
                crate::verify_one_file(&format!("{case}_{stage}"), short, &[]).unwrap_err(),
                &["conditional memory budget exceeded", GLOBAL],
            );
        }
    }
}
