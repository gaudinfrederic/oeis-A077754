import A077754

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A077754 : énoncé pur auditable (protocole N0, Option B)

Surface de spécification minimale : importe le module
`A077754.lean` parce que l'énoncé utilise les définitions du
projet `sigma10` (somme des chiffres) et `allNonzero` (chiffres
tous non nuls, `Bool` coercé en `Prop`). Zéro `sorry`, zéro
tactique, zéro notation locale. La fermeture
`theorem proven_A077754 : SpecA077754 := ...` vit dans
`Check_Spec_A077754.lean`.

Le `↔` est explicite : la spec capture l'équivalence complète
(existence pour les non-exceptions ET impossibilité pour les
exceptions), pas seulement le sens direct.
-/

/-- Énoncé record : pour tout `n ≥ 1` (domaine OEIS, offset 1),
il existe un multiple `N` de `n` à chiffres tous non nuls, de
somme des chiffres `n`, avec au moins 2 chiffres, si et
seulement si `n ∉ {1,2,5,11} ∪ 10ℕ`. Correction (2026-11-07) :
domaine restreint à n ≥ 1, l'extension à n = 0 étant une
divergence du verbatim OEIS. -/
abbrev SpecA077754 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ((∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        (Nat.digits 10 N).length ≥ 2)
    ↔ n ∉ ({1, 2, 5, 11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ))
