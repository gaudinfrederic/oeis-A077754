# A077754 — Murthy's conjecture, formalized in Lean 4

[![CI](https://github.com/gaudinfrederic/oeis-A077754/actions/workflows/ci.yml/badge.svg)](https://github.com/gaudinfrederic/oeis-A077754/actions/workflows/ci.yml)

Machine-checked resolution of the conjecture recorded in the
comments of [OEIS A077754](https://oeis.org/A077754)
(Murthy, 2002).

## Theorem

For every `n ≥ 1`, there exists a multiple `N` of `n` whose usual
base-10 representation (no leading zeros) has at least two digits,
all nonzero, and digit sum exactly `n`, **if and only if**
(`n ∉ {1, 2, 5, 11}` and `10 ∤ n`). Both directions are proved.

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
- `#print axioms A077754` — **only the three standard axioms**
  (`propext`, `Classical.choice`, `Quot.sound`): every finite
  certificate is kernel-checked by `decide`; **no
  `native_decide`, no `sorryAx`** — the trusted base is the
  Lean kernel alone
- Finite certificates additionally re-derived by a
  stdlib-only Python verifier as an independent cross-check
  (`A077754-ANNEXE.py` in the archived deposit)

## Contents

- `A077754.lean` — the development (~2600 lines). Central lemma
  `residue_reach` (fixed-count fibre coset reachability);
  `stage_cover` (analytic, `M > 184`); `stage_cover_2` /
  `corner_witness` (finite branches); `witSmall_all`
  (176 witnesses, `n ≤ 200`); `witCorner_all` (kernel `decide`
  certificate over the `witCorner` table); `coverB_to_finset`
  (bitmap-to-`Finset` bridge).
- `A077754Cert.lean` — kernel `decide` coverage certificates
  `stage_cover_small_aux` (`M ≤ 184`) and
  `stage_cover_small_aux'` (`m ≤ 1656`), evaluated by the
  bit-parallel residue checker `checkCoverB`, split into
  20 top-level chunk lemmas.
- `CornerTable.lean` — `witCorner` witness table (795 entries,
  `m ∈ {11,19,23}`, `L ∈ {7,8,9}`; data only — its kernel
  `decide` certificate `witCorner_all` lives in
  `A077754.lean`).

## Reproduce

```sh
lake build        # installs toolchain via elan, fetches mathlib cache
```

## Reference

F. Gaudin, *Prescribed digit sums in residue classes and a
conjecture of Murthy (OEIS A077754)*. Paper + artifact archived
at https://doi.org/10.5281/zenodo.23879087 (all versions; the
kernel-pure artifact described here is v1.1.0:
https://doi.org/10.5281/zenodo.23954824)
