# Second experiment: arithmetic, slices, and insertion sort

Historical milestone: **lexical-slots-v1-64**. See [model.md](model.md) for the
current rules, supported subset, implementation map, and run commands.

This experiment extended lexical storage checking to arithmetic, references,
and indexing, enough to verify in-place insertion sort over an arbitrary-length
mutable `u32` slice. The [executable and proof](../../examples/resource_insertion_sort.rs)
establish sortedness, preservation of elements, and an 84-model-byte storage bound.
The loops also prove termination; there are no assumptions or external-body proofs
in the example.

## Decisions carried forward

The conservative destination-plus-initializer rule was retained: it handles
copies consistently and makes the result independent of copy elision. Operand
results likewise overlap arithmetic results. The model uses fixed abstract
64-bit descriptor sizes, not the compiler target's physical layout.

Place evaluation gained explicit address scratch. Assignment retains its RHS
while evaluating the destination. Slice length is recognized by rustc's language
item, not a method-name match. Borrowed temporary backing storage remains rejected
because its extended lifetime requires a separate rule.

Ordinary calls and array-to-slice coercions were outside this milestone; the
[subsequent call experiment](calls.md) added them for the supported cases.

## Why insertion sort costs 84

Inside the inner loop, named storage is 44 bytes: the input slice descriptor (16),
`n` (8), `i` (8), `key` (4), and `j` (8).

Evaluating `values[j - 1]` first retains a 16-byte slice descriptor. The index
subtraction temporarily has two eight-byte operands and an eight-byte result.
That is 40 temporary bytes, giving a peak of `44 + 40 = 84`. Subsequent address
formation, element reads, comparison, and assignment stay within this peak.

The bound is independent of input length. Empty input, single elements, duplicate
elements, and all other lengths are covered by the same function proof. Branches
and loop bodies are conservatively analyzed even if a particular input would
skip them. Proof sequences and multiset calculations are erased.

The proof maintains an ordered prefix and an ordered region with one insertion
hole. A ghost multiset lemma proves that shifting an element and moving the hole
preserves the multiset when the saved key fills the hole. The final write restores
a sorted prefix. Normal Verus verification discharges these properties alongside
the structural resource check.

## Validation

Validated locally on 2026-11-05:

- Release workspace build and installed verifier build passed.
- Explicit vstd rebuild: 2,226 verified, zero errors.
- Resource suites: 65 passed (36 original tests and 29 extension tests).
- Existing `basic`, `functions`, `loops`, `size_of`, `mut_refs_slices_arrays`,
  `arrays`, `erase`, and `modes` suites: 373 passed, five upstream-ignored tests,
  zero failures. The complete upstream test suite was not run.
- A local compiled harness compared the actual sorter with Rust's sort on
  1,099 cases: every input of length zero through six over three values, plus
  empty, singleton, sorted, reverse, duplicate, and extreme-value examples.
  Only the harness was excluded from verification; the sorter and its proof
  were verified before compilation.
- Workspace formatting and `git diff --check` passed.
