import A077754

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVac_A077754 : protocole anti-vacuité pour A077754

Spec (`SpecA077754`) : `∃ N, n ∣ N ∧ allNonzero N ∧
sigma10 N = n ∧ longueur ≥ 2`  `↔`  `n ∉ {1,2,5,11} ∪ 10ℕ`.

Quatre exigences, toutes kernel-pures :
1. témoins explicites du membre gauche pour `n ∈ {3, 7, 9}`
   (`N = 12`, `N = 133`, `N = 18`) ;
2. satisfiabilité via le théorème `A077754` (`.mpr` sur un
   `n` hors exceptions) ;
3. obstruction : `n = 1` et `n = 10` (exceptions) n'ont aucun
   témoin, via `.mp` du théorème ;
4. ablation : `n = 5` et `n = 20` sans témoin - sans les clauses
   `{1,2,5,11}` et `10ℕ`, l'énoncé serait faux.

Note `decide` : uniquement sur des `Nat`/Bool clos (`dvd`,
`allNonzero`, `sigma10`, `length`) - jamais sur le `∃ N`.
-/

namespace CheckAntiVacA077754

-- 1. Témoins explicites.

/-- `n = 3`, `N = 12` : `3 ∣ 12`, chiffres non nuls, `1+2 = 3`,
2 chiffres. -/
theorem sat_three : ∃ N : ℕ, 3 ∣ N ∧ allNonzero N ∧
    sigma10 N = 3 ∧ (Nat.digits 10 N).length ≥ 2 :=
  ⟨12, by decide, by decide, by decide, by decide⟩

/-- `n = 7`, `N = 133` : `7 ∣ 133 = 7·19`, `1+3+3 = 7`,
3 chiffres non nuls. -/
theorem sat_seven : ∃ N : ℕ, 7 ∣ N ∧ allNonzero N ∧
    sigma10 N = 7 ∧ (Nat.digits 10 N).length ≥ 2 :=
  ⟨133, by decide, by decide, by decide, by decide⟩

/-- `n = 9`, `N = 18` : `9 ∣ 18`, `1+8 = 9`, 2 chiffres. -/
theorem sat_nine : ∃ N : ℕ, 9 ∣ N ∧ allNonzero N ∧
    sigma10 N = 9 ∧ (Nat.digits 10 N).length ≥ 2 :=
  ⟨18, by decide, by decide, by decide, by decide⟩

-- 2. Via le théorème compilé : `3` est hors des exceptions.

/-- `3 ∉ {1,2,5,11} ∪ 10ℕ`. -/
theorem three_not_exn :
    (3 : ℕ) ∉ ({1, 2, 5, 11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ) := by
  simp only [Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq]
  decide

/-- `4 ∉ {1,2,5,11} ∪ 10ℕ`. -/
theorem four_not_exn :
    (4 : ℕ) ∉ ({1, 2, 5, 11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ) := by
  simp only [Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_setOf_eq]
  decide

/-- `.mpr` du théorème produit un témoin à `n = 3`. -/
theorem sat_via_theorem : ∃ N : ℕ, 3 ∣ N ∧ allNonzero N ∧
    sigma10 N = 3 ∧ (Nat.digits 10 N).length ≥ 2 :=
  (A077754 3).mpr three_not_exn

/-- `.mpr` du théorème produit un témoin à `n = 4`. -/
theorem sat_via_theorem_four : ∃ N : ℕ, 4 ∣ N ∧ allNonzero N ∧
    sigma10 N = 4 ∧ (Nat.digits 10 N).length ≥ 2 :=
  (A077754 4).mpr four_not_exn

-- 3. Obstructions : les exceptions n'ont aucun témoin.

/-- `n = 1 ∈ {1,2,5,11}` : aucun `N`. -/
theorem obs_one : ¬ ∃ N : ℕ, 1 ∣ N ∧ allNonzero N ∧
    sigma10 N = 1 ∧ (Nat.digits 10 N).length ≥ 2 := fun h =>
  (A077754 1).mp h (by simp)

/-- `n = 10 ∈ 10ℕ` : aucun `N`. -/
theorem obs_ten : ¬ ∃ N : ℕ, 10 ∣ N ∧ allNonzero N ∧
    sigma10 N = 10 ∧ (Nat.digits 10 N).length ≥ 2 := fun h =>
  (A077754 10).mp h (by simp)

-- 4. Ablation : sans ces clauses, l'iff serait fausse.

/-- `n = 5 ∈ {1,2,5,11}` : clause ponctuelle indispensable. -/
theorem ablation_five : ¬ ∃ N : ℕ, 5 ∣ N ∧ allNonzero N ∧
    sigma10 N = 5 ∧ (Nat.digits 10 N).length ≥ 2 := fun h =>
  (A077754 5).mp h (by simp)

/-- `n = 20 ∈ 10ℕ` : clause `10ℕ` indispensable. -/
theorem ablation_twenty : ¬ ∃ N : ℕ, 20 ∣ N ∧ allNonzero N ∧
    sigma10 N = 20 ∧ (Nat.digits 10 N).length ≥ 2 := fun h =>
  (A077754 20).mp h (Or.inr ⟨2, rfl⟩)

end CheckAntiVacA077754

#print axioms CheckAntiVacA077754.sat_three
#print axioms CheckAntiVacA077754.sat_seven
#print axioms CheckAntiVacA077754.sat_nine
#print axioms CheckAntiVacA077754.three_not_exn
#print axioms CheckAntiVacA077754.four_not_exn
#print axioms CheckAntiVacA077754.sat_via_theorem
#print axioms CheckAntiVacA077754.sat_via_theorem_four
#print axioms CheckAntiVacA077754.obs_one
#print axioms CheckAntiVacA077754.obs_ten
#print axioms CheckAntiVacA077754.ablation_five
#print axioms CheckAntiVacA077754.ablation_twenty
