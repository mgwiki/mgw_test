(** $I sig/PfgEJul2021Preamble7.mgs **)

Theorem MetaCat_struct_b_b_e_e_cring: MetaCat CRing Hom_struct_b_b_e_e struct_id struct_comp.
claim L1: forall X, CRing X -> struct_b_b_e_e X.
{ let X. assume HX. apply HX. assume H _. exact H. }
exact MetaCat_struct_b_b_e_e_gen CRing L1.
Qed.

Theorem MetaCat_struct_b_b_e_e_cring_Forgetful: MetaFunctor CRing Hom_struct_b_b_e_e
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
claim L1: forall X, CRing X -> struct_b_b_e_e X.
{ let X. assume HX. apply HX. assume H _. exact H. }
exact MetaCat_struct_b_b_e_e_Forgetful_gen CRing L1.
Qed.

Proposition MetaCat_struct_b_b_e_e_cring_initial: exists Y:set, exists uniqa:set -> set,
  initial_p CRing Hom_struct_b_b_e_e struct_id struct_comp Y uniqa.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_terminal: exists Y:set, exists uniqa:set -> set,
  terminal_p CRing Hom_struct_b_b_e_e struct_id struct_comp Y uniqa.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_coproduct_constr:
  exists coprod:set -> set -> set,
  exists i0 i1:set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set,
  coproduct_constr_p CRing Hom_struct_b_b_e_e struct_id struct_comp coprod i0 i1 copair.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_product_constr:
  exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  product_constr_p CRing Hom_struct_b_b_e_e struct_id struct_comp prod pi0 pi1 pair.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_coequalizer_constr:
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  coequalizer_constr_p CRing Hom_struct_b_b_e_e struct_id struct_comp quot canonmap fac.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_equalizer_constr:
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  equalizer_constr_p CRing Hom_struct_b_b_e_e struct_id struct_comp quot canonmap fac.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_pushout_constr:
  exists po:set -> set -> set -> set -> set -> set,
  exists i0:set -> set -> set -> set -> set -> set,
  exists i1:set -> set -> set -> set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pushout_constr_p CRing Hom_struct_b_b_e_e struct_id struct_comp po i0 i1 copair.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_pullback_constr:
  exists pb:set -> set -> set -> set -> set -> set,
  exists pi0:set -> set -> set -> set -> set -> set,
  exists pi1:set -> set -> set -> set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pullback_constr_p CRing Hom_struct_b_b_e_e struct_id struct_comp pb pi0 pi1 pair.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_product_exponent:
  exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  exists exp:set -> set -> set,
  exists a:set -> set -> set,
  exists lm:set -> set -> set -> set -> set,
  product_exponent_constr_p CRing Hom_struct_b_b_e_e struct_id struct_comp prod pi0 pi1 pair exp a lm.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_subobject_classifier:
  exists one:set, exists uniqa:set -> set,
  exists Omega:set, exists tru:set,
  exists ch:set -> set -> set -> set,
  exists constr:set -> set -> set -> set -> set -> set -> set,
  subobject_classifier_p CRing Hom_struct_b_b_e_e struct_id struct_comp one uniqa Omega tru ch constr.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_nno:
  exists one:set,
  exists uniqa:set -> set,
  exists N:set,
  exists zer suc:set,
  exists rec:set -> set -> set -> set,
  nno_p CRing Hom_struct_b_b_e_e struct_id struct_comp one uniqa N zer suc rec.
Admitted.

Proposition MetaCat_struct_b_b_e_e_cring_left_adjoint_forgetful:
  exists F0:set -> set,
  exists F1:set -> set -> set -> set,
  exists eta eps:set -> set,
  MetaAdjunction_strict
       (fun _ => True) SetHom
       (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
       CRing Hom_struct_b_b_e_e struct_id struct_comp
       F0 F1 (fun X => X 0) (fun X Y f => f) eta eps.
Admitted.
