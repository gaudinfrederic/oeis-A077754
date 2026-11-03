# A077754 — Murthy's conjecture, formalized in Lean 4

[![CI](https://github.com/USERNAME/a077754-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/USERNAME/a077754-lean/actions/workflows/ci.yml)

Machine-checked resolution of the conjecture recorded in the
comments of [OEIS A077754](https://oeis.org/A077754)
(Murthy, 2002).

## Theorem

For every `n ≥ 1`, there exists a multiple `N` of `n` with at
least two decimal digits, all nonzero, and digit sum exactly
`n`, **if and only if** `n ∉ {1, 2, 5, 11}` and `10 ∤ n`.
Both directions are proved.

```lean
theorem A077754 (n : ℕ) :
    (∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        (Nat.digits 10 N).length ≥ 2)
    ↔ n ∉ ({1, 2, 5, 11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ)
```

## Status

- Lean toolchain `v4.35.0`, mathlib `v4.35.0` (pinned manifest)
- `lake build` — full build, **zero `sorry`**
- Kernel re-verified: `lake env leanchecker A077754` and
  `lake env leanchecker CornerTable` both pass (exit 0)
- `#print axioms A077754` — only standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) plus
  `native_decide` evaluation axioms for the finite
  certificates; **no `sorryAx`** anywhere
- Finite certificates discharged by `native_decide` and
  independently re-derived by a stdlib-only Python verifier
  (`A077754-ANNEXE.py` in the archived deposit)

## Contents

- `A077754.lean` — the development (~2400 lines). Central lemma
  `residue_reach` (fixed-count fibre coset reachability);
  `stage_cover` (analytic, `M > 184`); `stage_cover_small'` /
  `stage_cover_2` / `corner_witness` (finite branches);
  `witSmall_all` (176 witnesses, `n ≤ 200`); `witCorner_all`
  (`native_decide` certificate over the `witCorner` table).
- `CornerTable.lean` — `witCorner` witness table (795 entries,
  `m ∈ {11,19,23}`, `L ∈ {7,8,9}`; data only — its
  `native_decide` certificate `witCorner_all` lives in
  `A077754.lean`).

## Reproduce

```sh
lake build        # installs toolchain via elan, fetches mathlib cache
```

## Reference

F. Gaudin, *Prescribed digit sums in residue classes and a
conjecture of Murthy (OEIS A077754)*. Paper + artifact archived
at https://doi.org/10.5281/zenodo.23879088
