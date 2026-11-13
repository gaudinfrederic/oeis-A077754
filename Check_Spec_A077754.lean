import Spec_A077754
import A077754

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A077754 : fermeture Spec↔preuve (Option B)

Le Spec (`Spec_A077754.lean`) ne contient aucune preuve ; ce
fichier vérifie que le théorème compilé satisfait EXACTEMENT
l'énoncé de la spec. Le théorème `A077754` vit à la racine du
module `A077754.lean` (aucun namespace), d'où le nom qualifié
`A077754`. Le module importe transitivement `A077754Cert` et
`CornerTable` via `A077754.lean`.
-/

/-- La preuve compilée satisfait l'énoncé record (domaine
n ≥ 1 : le théorème prouve l'iff pour tout n, le guard est
satisfait a fortiori). -/
theorem proven_A077754 : SpecA077754 := by
  intro n _
  exact A077754 n

#print axioms proven_A077754
