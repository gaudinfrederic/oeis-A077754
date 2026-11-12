import A077754

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A077754Val - la fonction `a(n)` de la fiche OEIS et la clause
# « smallest »

Module livre (promotion du correctif D2+, audit
`STATUS/D2PLUS/A077754.md` : VERDICT FAIL corrige, rapport
`STATUS/D2PLUS/A077754-FIX.md`). Le theoreme `A077754` (module
eponyme) prouve l'equivalence d'existence - zero-set
`{1,2,5,11} ∪ 10ℕ`, conjecture %C de Murthy. Ce module ajoute
la formalisation de l'objet-suite du %N « Smallest multiple of
n ... or 0 if no such multiple exists » :

- `a077754_val : ℕ → ℕ` - la fonction `a(n)` de la fiche,
  definie par `Nat.find` sous existence (junk `0` = clause
  « or 0 if no such multiple exists ») ;
- `a077754_val_isLeast` - hors exceptions, `a077754_val n`
  est `IsLeast` de l'ensemble admissible (membre + minore
  tout autre temoin) : la formalisation exacte de
  « smallest multiple » ;
- `a077754_val_eq_zero_iff` - `a(n) = 0 ↔ n ∈ {1,2,5,11} ∪ 10ℕ`,
  la conjecture lue sur la valeur ;
- ancres DATA (valeurs OEIS reelles, pas les temoins
  existentiels non minimaux de `witTab`) :
  `a(1)=a(2)=a(5)=a(10)=a(11)=a(20)=a(30)=a(40)=0` et
  `a(3)=12, a(4)=112, a(6)=24, a(7)=133, a(8)=152, a(9)=18,
  a(12)=48`, chacune avec minimalite kernel-certifiee par
  scan des SEULS multiples `n*j`, `j < a(n)/n` (idiome
  `decidableBallLT`).

Kernel-pur : `decide`/`Nat.find`/`IsLeast` uniquement ;
aucun trou de preuve, aucune evaluation native.
-/

namespace A077754Val

/-- La fonction `a(n)` du %N : plus petit `N` multiple de `n`,
    a >= 2 chiffres tous non nuls, de somme de chiffres `n` ;
    `0` s'il n'en existe pas (junk `0` canonique de la clause
    « or 0 »). -/
noncomputable def a077754_val (n : ℕ) : ℕ :=
  open Classical in
  if h : ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
      2 ≤ (Nat.digits 10 N).length
  then Nat.find h
  else 0

/-- Hors exceptions, `a077754_val n` est le `Nat.find` de
    l'existence prouvee par `A077754`. -/
theorem a077754_val_eq_find (n : ℕ)
    (hmem : n ∉ ({1,2,5,11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ)) :
    ∃ h : ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        2 ≤ (Nat.digits 10 N).length,
      a077754_val n = Nat.find h :=
  ⟨(A077754 n).mpr hmem, dif_pos _⟩

/-- Clause « smallest » : hors exceptions, `a077754_val n`
    appartient a l'ensemble admissible et minore tout autre
    admissible (`IsLeast` : membre + lowerBounds). -/
theorem a077754_val_isLeast (n : ℕ)
    (hmem : n ∉ ({1,2,5,11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ)) :
    IsLeast {N : ℕ | n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        2 ≤ (Nat.digits 10 N).length} (a077754_val n) := by
  obtain ⟨hex, hval⟩ := a077754_val_eq_find n hmem
  rw [hval]
  exact ⟨Nat.find_spec hex, fun M hM => Nat.find_min' hex hM⟩

/-- Sous une exception, `a077754_val n = 0` : l'absence de
    temoin est `A077754.mp`. -/
theorem a077754_val_eq_zero (n : ℕ)
    (hmem : n ∈ ({1,2,5,11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ)) :
    a077754_val n = 0 := by
  have hno : ¬ ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
      2 ≤ (Nat.digits 10 N).length :=
    fun h => (A077754 n).mp h hmem
  exact dif_neg hno

/-- `a(n) = 0` ssi exception : la conjecture %C lue sur la
    valeur elle-meme. -/
theorem a077754_val_eq_zero_iff (n : ℕ) :
    a077754_val n = 0 ↔
      n ∈ ({1,2,5,11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ) := by
  constructor
  · intro hz
    by_contra hmem
    have hle := a077754_val_isLeast n hmem
    have hl : 2 ≤ (Nat.digits 10 (a077754_val n)).length :=
      hle.1.2.2.2
    rw [hz] at hl
    simp [Nat.digits] at hl
  · exact a077754_val_eq_zero n

/-- Record complet du %N : `a(n) = 0` ssi exception, sinon
    `a(n)` est le plus petit multiple admissible. -/
theorem a077754_val_spec (n : ℕ) :
    (a077754_val n = 0 ↔
        n ∈ ({1,2,5,11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ)) ∧
    (n ∉ ({1,2,5,11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ) →
      IsLeast {N : ℕ | n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
          2 ≤ (Nat.digits 10 N).length} (a077754_val n)) :=
  ⟨a077754_val_eq_zero_iff n, a077754_val_isLeast n⟩

section MinimalityCerts

/-- Conversion predicat -> `witOk` (la table `witOk` du module
    eponyme teste les 4 clauses ; ici on s'en sert pour la
    minimalite). -/
theorem pred_witOk {n m : ℕ}
    (h : n ∣ m ∧ allNonzero m ∧ sigma10 m = n ∧
      2 ≤ (Nat.digits 10 m).length) : witOk n m = true := by
  obtain ⟨hd, ha, hs, hl⟩ := h
  unfold witOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨decide_eq_true_iff.mpr hd, ha⟩,
    decide_eq_true_iff.mpr hs⟩, decide_eq_true_iff.mpr hl⟩

/-- Scan kernel des multiples : aucun `3*j`, `j < 4`, n'est
    temoin (minimalite de `a(3) = 12 = 3*4`). -/
theorem certmin_3 : ∀ j : ℕ, j < 4 →
    ¬ (allNonzero (3 * j) ∧ sigma10 (3 * j) = 3 ∧
      2 ≤ (Nat.digits 10 (3 * j)).length) := by decide

/-- Aucun `4*j`, `j < 28`, temoin (minimalite de
    `a(4) = 112 = 4*28`). -/
theorem certmin_4 : ∀ j : ℕ, j < 28 →
    ¬ (allNonzero (4 * j) ∧ sigma10 (4 * j) = 4 ∧
      2 ≤ (Nat.digits 10 (4 * j)).length) := by decide

/-- Aucun `6*j`, `j < 4`, temoin (`a(6) = 24 = 6*4`). -/
theorem certmin_6 : ∀ j : ℕ, j < 4 →
    ¬ (allNonzero (6 * j) ∧ sigma10 (6 * j) = 6 ∧
      2 ≤ (Nat.digits 10 (6 * j)).length) := by decide

/-- Aucun `7*j`, `j < 19`, temoin (`a(7) = 133 = 7*19`). -/
theorem certmin_7 : ∀ j : ℕ, j < 19 →
    ¬ (allNonzero (7 * j) ∧ sigma10 (7 * j) = 7 ∧
      2 ≤ (Nat.digits 10 (7 * j)).length) := by decide

/-- Aucun `8*j`, `j < 19`, temoin (`a(8) = 152 = 8*19`). -/
theorem certmin_8 : ∀ j : ℕ, j < 19 →
    ¬ (allNonzero (8 * j) ∧ sigma10 (8 * j) = 8 ∧
      2 ≤ (Nat.digits 10 (8 * j)).length) := by decide

/-- Aucun `9*j`, `j < 2`, temoin (`a(9) = 18 = 9*2`). -/
theorem certmin_9 : ∀ j : ℕ, j < 2 →
    ¬ (allNonzero (9 * j) ∧ sigma10 (9 * j) = 9 ∧
      2 ≤ (Nat.digits 10 (9 * j)).length) := by decide

/-- Aucun `12*j`, `j < 4`, temoin (`a(12) = 48 = 12*4`). -/
theorem certmin_12 : ∀ j : ℕ, j < 4 →
    ¬ (allNonzero (12 * j) ∧ sigma10 (12 * j) = 12 ∧
      2 ≤ (Nat.digits 10 (12 * j)).length) := by decide

end MinimalityCerts

section ValueAnchors

/-- `a(3) = 12` : valeur DATA + minimalite kernel. -/
theorem a077754_val_3 : a077754_val 3 = 12 := by
  have hex : ∃ N : ℕ, 3 ∣ N ∧ allNonzero N ∧ sigma10 N = 3 ∧
      2 ≤ (Nat.digits 10 N).length :=
    ⟨12, by decide, by decide, by decide, by decide⟩
  rw [show a077754_val 3 = Nat.find hex from dif_pos hex]
  apply le_antisymm
  · exact Nat.find_min' hex
      ⟨by decide, by decide, by decide, by decide⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hdvd, hnon, hsum, hlen⟩ := Nat.find_spec hex
    obtain ⟨j, hjeq⟩ := hdvd
    rw [hjeq] at hlt hnon hsum hlen
    exact certmin_3 j (by omega) ⟨hnon, hsum, hlen⟩

/-- `a(4) = 112`. -/
theorem a077754_val_4 : a077754_val 4 = 112 := by
  have hex : ∃ N : ℕ, 4 ∣ N ∧ allNonzero N ∧ sigma10 N = 4 ∧
      2 ≤ (Nat.digits 10 N).length :=
    ⟨112, by decide, by decide, by decide, by decide⟩
  rw [show a077754_val 4 = Nat.find hex from dif_pos hex]
  apply le_antisymm
  · exact Nat.find_min' hex
      ⟨by decide, by decide, by decide, by decide⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hdvd, hnon, hsum, hlen⟩ := Nat.find_spec hex
    obtain ⟨j, hjeq⟩ := hdvd
    rw [hjeq] at hlt hnon hsum hlen
    exact certmin_4 j (by omega) ⟨hnon, hsum, hlen⟩

/-- `a(6) = 24`. -/
theorem a077754_val_6 : a077754_val 6 = 24 := by
  have hex : ∃ N : ℕ, 6 ∣ N ∧ allNonzero N ∧ sigma10 N = 6 ∧
      2 ≤ (Nat.digits 10 N).length :=
    ⟨24, by decide, by decide, by decide, by decide⟩
  rw [show a077754_val 6 = Nat.find hex from dif_pos hex]
  apply le_antisymm
  · exact Nat.find_min' hex
      ⟨by decide, by decide, by decide, by decide⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hdvd, hnon, hsum, hlen⟩ := Nat.find_spec hex
    obtain ⟨j, hjeq⟩ := hdvd
    rw [hjeq] at hlt hnon hsum hlen
    exact certmin_6 j (by omega) ⟨hnon, hsum, hlen⟩

/-- `a(7) = 133` (le temoin existentiel `witTab` = 511 n'est
    PAS minimal - c'est exactement ce que la clause smallest
    exige de separer). -/
theorem a077754_val_7 : a077754_val 7 = 133 := by
  have hex : ∃ N : ℕ, 7 ∣ N ∧ allNonzero N ∧ sigma10 N = 7 ∧
      2 ≤ (Nat.digits 10 N).length :=
    ⟨133, by decide, by decide, by decide, by decide⟩
  rw [show a077754_val 7 = Nat.find hex from dif_pos hex]
  apply le_antisymm
  · exact Nat.find_min' hex
      ⟨by decide, by decide, by decide, by decide⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hdvd, hnon, hsum, hlen⟩ := Nat.find_spec hex
    obtain ⟨j, hjeq⟩ := hdvd
    rw [hjeq] at hlt hnon hsum hlen
    exact certmin_7 j (by omega) ⟨hnon, hsum, hlen⟩

/-- `a(8) = 152` (witTab = 512, non minimal). -/
theorem a077754_val_8 : a077754_val 8 = 152 := by
  have hex : ∃ N : ℕ, 8 ∣ N ∧ allNonzero N ∧ sigma10 N = 8 ∧
      2 ≤ (Nat.digits 10 N).length :=
    ⟨152, by decide, by decide, by decide, by decide⟩
  rw [show a077754_val 8 = Nat.find hex from dif_pos hex]
  apply le_antisymm
  · exact Nat.find_min' hex
      ⟨by decide, by decide, by decide, by decide⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hdvd, hnon, hsum, hlen⟩ := Nat.find_spec hex
    obtain ⟨j, hjeq⟩ := hdvd
    rw [hjeq] at hlt hnon hsum hlen
    exact certmin_8 j (by omega) ⟨hnon, hsum, hlen⟩

/-- `a(9) = 18` (witTab = 81, non minimal). -/
theorem a077754_val_9 : a077754_val 9 = 18 := by
  have hex : ∃ N : ℕ, 9 ∣ N ∧ allNonzero N ∧ sigma10 N = 9 ∧
      2 ≤ (Nat.digits 10 N).length :=
    ⟨18, by decide, by decide, by decide, by decide⟩
  rw [show a077754_val 9 = Nat.find hex from dif_pos hex]
  apply le_antisymm
  · exact Nat.find_min' hex
      ⟨by decide, by decide, by decide, by decide⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hdvd, hnon, hsum, hlen⟩ := Nat.find_spec hex
    obtain ⟨j, hjeq⟩ := hdvd
    rw [hjeq] at hlt hnon hsum hlen
    exact certmin_9 j (by omega) ⟨hnon, hsum, hlen⟩

/-- `a(12) = 48` (witTab = 84, non minimal). -/
theorem a077754_val_12 : a077754_val 12 = 48 := by
  have hex : ∃ N : ℕ, 12 ∣ N ∧ allNonzero N ∧ sigma10 N = 12 ∧
      2 ≤ (Nat.digits 10 N).length :=
    ⟨48, by decide, by decide, by decide, by decide⟩
  rw [show a077754_val 12 = Nat.find hex from dif_pos hex]
  apply le_antisymm
  · exact Nat.find_min' hex
      ⟨by decide, by decide, by decide, by decide⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hdvd, hnon, hsum, hlen⟩ := Nat.find_spec hex
    obtain ⟨j, hjeq⟩ := hdvd
    rw [hjeq] at hlt hnon hsum hlen
    exact certmin_12 j (by omega) ⟨hnon, hsum, hlen⟩

/-- Ancres zero DATA : positions affichees `1, 2, 5, 10, 11,
    20, 30, 40` = exactement `{1,2,5,11} ∪ 10ℕ` vues sur la
    valeur. -/
theorem a077754_val_zero_1 : a077754_val 1 = 0 :=
  a077754_val_eq_zero 1 (Or.inl (by simp))

theorem a077754_val_zero_2 : a077754_val 2 = 0 :=
  a077754_val_eq_zero 2 (Or.inl (by simp))

theorem a077754_val_zero_5 : a077754_val 5 = 0 :=
  a077754_val_eq_zero 5 (Or.inl (by simp))

theorem a077754_val_zero_10 : a077754_val 10 = 0 :=
  a077754_val_eq_zero 10 (Or.inr (dvd_refl 10))

theorem a077754_val_zero_11 : a077754_val 11 = 0 :=
  a077754_val_eq_zero 11 (Or.inl (by simp))

theorem a077754_val_zero_20 : a077754_val 20 = 0 :=
  a077754_val_eq_zero 20 (Or.inr (by decide))

theorem a077754_val_zero_30 : a077754_val 30 = 0 :=
  a077754_val_eq_zero 30 (Or.inr (by decide))

theorem a077754_val_zero_40 : a077754_val 40 = 0 :=
  a077754_val_eq_zero 40 (Or.inr (by decide))

end ValueAnchors

end A077754Val

#print axioms A077754Val.a077754_val_spec
#print axioms A077754Val.a077754_val_isLeast
#print axioms A077754Val.a077754_val_eq_zero_iff
#print axioms A077754Val.a077754_val_3
#print axioms A077754Val.a077754_val_4
#print axioms A077754Val.a077754_val_6
#print axioms A077754Val.a077754_val_7
#print axioms A077754Val.a077754_val_8
#print axioms A077754Val.a077754_val_9
#print axioms A077754Val.a077754_val_12
#print axioms A077754Val.a077754_val_zero_1
#print axioms A077754Val.a077754_val_zero_10
#print axioms A077754Val.a077754_val_zero_40
