import A077754Val

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_d2plus_A077754 - harnais de verification du module
# A077754Val

Historique : ce fichier contenait la premiere implementation de
la clause « smallest » (verifiee au kernel, axiomes trio). Le
contenu a ete PROMU dans le module livre `A077754Val`
(namespace `A077754Val`, termes de preuve identiques - seuls les
noms qualifies changent de `CheckD2plusA077754.*` a
`A077754Val.*`). Ce fichier reste le harnais de verification :
`lake env lean Check_d2plus_A077754.lean` re-imprime les axiomes
des theoremes livres.
-/

open A077754Val

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
