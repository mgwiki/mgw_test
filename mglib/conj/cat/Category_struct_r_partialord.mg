(** $I sig/PfgEJul2021Preamble7.mgs **)

Definition struct_r_partialord : set -> prop
 := fun X => struct_r X
     /\ unpack_r_o X
          (fun X' r => 
	        (forall x :e X', ~r x x) 
             /\ (forall x y z :e X', r x y -> r y z -> r x z)).

Theorem MetaCat_struct_r_partialord: MetaCat struct_r_partialord Hom_struct_r struct_id struct_comp.
claim L1: forall X, struct_r_partialord X -> struct_r X.
{ let X. assume HX. apply HX. assume H _. exact H. }
exact MetaCat_struct_r_gen struct_r_partialord L1.
Qed.

Theorem MetaCat_struct_r_partialord_Forgetful: MetaFunctor struct_r_partialord Hom_struct_r
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
claim L1: forall X, struct_r_partialord X -> struct_r X.
{ let X. assume HX. apply HX. assume H _. exact H. }
exact MetaCat_struct_r_Forgetful_gen struct_r_partialord L1.
Qed.

Proposition MetaCat_struct_r_partialord_initial: exists Y:set, exists uniqa:set -> set,
  initial_p struct_r_partialord Hom_struct_r struct_id struct_comp Y uniqa.
Admitted.

Proposition MetaCat_struct_r_partialord_terminal: exists Y:set, exists uniqa:set -> set,
  terminal_p struct_r_partialord Hom_struct_r struct_id struct_comp Y uniqa.
Admitted.

Proposition MetaCat_struct_r_partialord_coproduct_constr:
  exists coprod:set -> set -> set,
  exists i0 i1:set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set,
  coproduct_constr_p struct_r_partialord Hom_struct_r struct_id struct_comp coprod i0 i1 copair.
Admitted.

Proposition MetaCat_struct_r_partialord_product_constr:
  exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  product_constr_p struct_r_partialord Hom_struct_r struct_id struct_comp prod pi0 pi1 pair.
Admitted.

Proposition MetaCat_struct_r_partialord_coequalizer_constr:
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  coequalizer_constr_p struct_r_partialord Hom_struct_r struct_id struct_comp quot canonmap fac.
Admitted.

Proposition MetaCat_struct_r_partialord_equalizer_constr:
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  equalizer_constr_p struct_r_partialord Hom_struct_r struct_id struct_comp quot canonmap fac.
Admitted.

Proposition MetaCat_struct_r_partialord_pushout_constr:
  exists po:set -> set -> set -> set -> set -> set,
  exists i0:set -> set -> set -> set -> set -> set,
  exists i1:set -> set -> set -> set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pushout_constr_p struct_r_partialord Hom_struct_r struct_id struct_comp po i0 i1 copair.
Admitted.

Proposition MetaCat_struct_r_partialord_pullback_constr:
  exists pb:set -> set -> set -> set -> set -> set,
  exists pi0:set -> set -> set -> set -> set -> set,
  exists pi1:set -> set -> set -> set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pullback_constr_p struct_r_partialord Hom_struct_r struct_id struct_comp pb pi0 pi1 pair.
Admitted.

Proposition MetaCat_struct_r_partialord_product_exponent:
  exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  exists exp:set -> set -> set,
  exists a:set -> set -> set,
  exists lm:set -> set -> set -> set -> set,
  product_exponent_constr_p struct_r_partialord Hom_struct_r struct_id struct_comp prod pi0 pi1 pair exp a lm.
Admitted.

Proposition MetaCat_struct_r_partialord_subobject_classifier:
  exists one:set, exists uniqa:set -> set,
  exists Omega:set, exists tru:set,
  exists ch:set -> set -> set -> set,
  exists constr:set -> set -> set -> set -> set -> set -> set,
  subobject_classifier_p struct_r_partialord Hom_struct_r struct_id struct_comp one uniqa Omega tru ch constr.
Admitted.

Proposition MetaCat_struct_r_partialord_nno:
  exists one:set,
  exists uniqa:set -> set,
  exists N:set,
  exists zer suc:set,
  exists rec:set -> set -> set -> set,
  nno_p struct_r_partialord Hom_struct_r struct_id struct_comp one uniqa N zer suc rec.
Admitted.

Proposition MetaCat_struct_r_partialord_left_adjoint_forgetful:
  exists F0:set -> set,
  exists F1:set -> set -> set -> set,
  exists eta eps:set -> set,
  MetaAdjunction_strict
       (fun _ => True) SetHom
       (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
       struct_r_partialord Hom_struct_r struct_id struct_comp
       F0 F1 (fun X => X 0) (fun X Y f => f) eta eps.
Admitted.

