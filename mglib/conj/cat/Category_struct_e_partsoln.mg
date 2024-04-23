(** $I sig/PfgEJul2021Preamble7.mgs **)

Theorem MetaCat_struct_e: MetaCat struct_e Hom_struct_e struct_id struct_comp.
exact MetaCat_struct_e_gen struct_e (fun X H => H).
Qed.

Theorem MetaCat_struct_e_Forgetful: MetaFunctor struct_e Hom_struct_e
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
exact MetaCat_struct_e_Forgetful_gen struct_e (fun X H => H).
Qed.

Theorem MetaCat_struct_e_initial: exists Y:set, exists uniqa:set -> set,
  initial_p struct_e Hom_struct_e struct_id struct_comp Y uniqa.
witness pack_e 1 0.
witness (fun X => fun x :e 1 => X 1).
prove struct_e (pack_e 1 0)
   /\ forall X:set, struct_e X
         -> Hom_struct_e (pack_e 1 0) X (fun x :e 1 => X 1)
         /\ forall h':set, Hom_struct_e (pack_e 1 0) X h' -> h' = (fun x :e 1 => X 1).
apply andI.
- apply pack_struct_e_I. prove 0 :e 1. exact In_0_1.
- let X. assume HX: struct_e X.
  apply HX (fun u => Hom_struct_e (pack_e 1 0) u (fun x :e 1 => u 1)
         /\ forall h':set, Hom_struct_e (pack_e 1 0) u h' -> h' = (fun x :e 1 => u 1)).
  let X' e. assume He: e :e X'.
  prove Hom_struct_e (pack_e 1 0) (pack_e X' e) (fun x :e 1 => pack_e X' e 1)
     /\ forall h':set, Hom_struct_e (pack_e 1 0) (pack_e X' e) h' -> h' = (fun x :e 1 => pack_e X' e 1).
  rewrite <- pack_e_1_eq2.
  prove Hom_struct_e (pack_e 1 0) (pack_e X' e) (fun x :e 1 => e)
     /\ forall h':set, Hom_struct_e (pack_e 1 0) (pack_e X' e) h' -> h' = (fun x :e 1 => e).
  apply andI.
  - rewrite Hom_struct_e_pack.
    prove (fun x :e 1 => e) :e X' :^: 1
       /\ (fun x :e 1 => e) 0 = e.
    apply andI.
    + prove (fun x :e 1 => e) :e Pi_ x :e 1, X'.
      apply lam_Pi.
      let x. assume Hx. exact He.
    + exact beta 1 (fun x => e) 0 In_0_1.
  - let h'. rewrite Hom_struct_e_pack.
    assume Hh'. apply Hh'.
    assume Hh'1: h' :e X' :^: 1.
    assume Hh'2: h' 0 = e.
    prove h' = (fun x :e 1 => e).
    transitivity (fun x :e 1 => h' x).
    + symmetry. exact Pi_eta 1 (fun _ => X') h' Hh'1.
    + apply lam_ext.
      let x. assume Hx: x :e 1.
      prove h' x = e.
      apply cases_1 x Hx (fun u => h' u = e).
      prove h' 0 = e.
      exact Hh'2.
Qed.

Proposition MetaCat_struct_e_terminal: exists Y:set, exists uniqa:set -> set,
  terminal_p struct_e Hom_struct_e struct_id struct_comp Y uniqa.
Admitted.

Proposition MetaCat_struct_e_coproduct_constr:
  exists coprod:set -> set -> set,
  exists i0 i1:set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set,
  coproduct_constr_p struct_e Hom_struct_e struct_id struct_comp coprod i0 i1 copair.
Admitted.

Proposition MetaCat_struct_e_product_constr:
  exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  product_constr_p struct_e Hom_struct_e struct_id struct_comp prod pi0 pi1 pair.
Admitted.

Proposition MetaCat_struct_e_coequalizer_constr:
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  coequalizer_constr_p struct_e Hom_struct_e struct_id struct_comp quot canonmap fac.
Admitted.

Proposition MetaCat_struct_e_equalizer_constr:
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  equalizer_constr_p struct_e Hom_struct_e struct_id struct_comp quot canonmap fac.
Admitted.

Proposition MetaCat_struct_e_pushout_constr:
  exists po:set -> set -> set -> set -> set -> set,
  exists i0:set -> set -> set -> set -> set -> set,
  exists i1:set -> set -> set -> set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pushout_constr_p struct_e Hom_struct_e struct_id struct_comp po i0 i1 copair.
Admitted.

Proposition MetaCat_struct_e_pullback_constr:
  exists pb:set -> set -> set -> set -> set -> set,
  exists pi0:set -> set -> set -> set -> set -> set,
  exists pi1:set -> set -> set -> set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pullback_constr_p struct_e Hom_struct_e struct_id struct_comp pb pi0 pi1 pair.
Admitted.

Proposition MetaCat_struct_e_product_exponent:
  exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  exists exp:set -> set -> set,
  exists a:set -> set -> set,
  exists lm:set -> set -> set -> set -> set,
  product_exponent_constr_p struct_e Hom_struct_e struct_id struct_comp prod pi0 pi1 pair exp a lm.
Admitted.

Proposition MetaCat_struct_e_subobject_classifier:
  exists one:set, exists uniqa:set -> set,
  exists Omega:set, exists tru:set,
  exists ch:set -> set -> set -> set,
  exists constr:set -> set -> set -> set -> set -> set -> set,
  subobject_classifier_p struct_e Hom_struct_e struct_id struct_comp one uniqa Omega tru ch constr.
Admitted.

Proposition MetaCat_struct_e_nno:
  exists one:set,
  exists uniqa:set -> set,
  exists N:set,
  exists zer suc:set,
  exists rec:set -> set -> set -> set,
  nno_p struct_e Hom_struct_e struct_id struct_comp one uniqa N zer suc rec.
Admitted.

Theorem MetaCat_struct_e_left_adjoint_forgetful:
  exists F0:set -> set,
  exists F1:set -> set -> set -> set,
  exists eta eps:set -> set,
  MetaAdjunction_strict
       (fun _ => True) SetHom
       (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
       struct_e Hom_struct_e struct_id struct_comp
       F0 F1 (fun X => X 0) (fun X Y f => f) eta eps.
set F0:set -> set := fun X => pack_e (1 :+: X) 0.
set F1:set -> set -> set -> set := fun X Y f => (fun x' :e 1 :+: X => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) x').
set eta: set -> set := fun X => fun x :e X => Inj1 x.
set eps: set -> set := fun X => (fun x' :e 1 :+: (X 0) => combine_funcs 1 (X 0) (fun _ => X 1) (fun x => x) x').
witness F0. witness F1.
witness eta. witness eps.
claim L01X: forall X, 0 :e 1 :+: X.
{ let X. rewrite <- Inj0_0 at 1. prove Inj0 0 :e 1 :+: X. apply Inj0_setsum. exact In_0_1. }
claim LFX: forall X, struct_e (F0 X).
{ let X. prove struct_e (pack_e (1 :+: X) 0).
  apply pack_struct_e_I. prove 0 :e 1 :+: X.  exact L01X X.
}
claim LFX0: forall X, F0 X 0 = 1 :+: X.
{ let X. symmetry. exact pack_e_0_eq2 (1 :+: X) 0. }
claim LFX1: forall X, F0 X 1 = 0.
{ let X. symmetry. exact pack_e_1_eq2 (1 :+: X) 0. }
claim LFf: forall X Y f, SetHom X Y f -> Hom_struct_e (F0 X) (F0 Y) (F1 X Y f).
{ let X Y f.
  assume Hf: f :e Y :^: X.
  set f' := (fun x' :e 1 :+: X => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) x').
  prove Hom_struct_e (pack_e (1 :+: X) 0) (pack_e (1 :+: Y) 0) f'.
  rewrite Hom_struct_e_pack.
  prove f' :e (1 :+: Y) :^: (1 :+: X) /\ f' 0 = 0.
  apply andI.
  - prove f' :e Pi_ _ :e 1 :+: X, 1 :+: Y.
    apply lam_Pi.
    let x'. assume Hx': x' :e 1 :+: X.
    prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) x' :e 1 :+: Y.
    apply setsum_Inj_inv 1 X x' Hx'.
    + assume H1. apply H1. let x. assume Hx. apply Hx.
      assume Hx: x :e 1.
      assume Hx2: x' = Inj0 x.
      rewrite Hx2.
      prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) (Inj0 x) :e 1 :+: Y.
      rewrite combine_funcs_eq1.
      prove 0 :e 1 :+: Y.
      exact L01X Y.
    + assume H1. apply H1. let x. assume Hx. apply Hx.
      assume Hx: x :e X.
      assume Hx2: x' = Inj1 x.
      rewrite Hx2.
      prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) (Inj1 x) :e 1 :+: Y.
      rewrite combine_funcs_eq2.
      prove Inj1 (f x) :e 1 :+: Y.
      apply Inj1_setsum.
      prove f x :e Y.
      exact ap_Pi X (fun _ => Y) f x Hf Hx.
  - prove f' 0 = 0.
    rewrite beta (1 :+: X) (fun x' => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) x') 0 (L01X X).
    prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) 0 = 0.
    rewrite <- Inj0_0 at 3.
    prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) (Inj0 0) = 0.
    exact combine_funcs_eq1 1 X (fun _ => 0) (fun x => Inj1 (f x)) 0.
}
claim LFf0: forall X Y f, forall x :e 1, F1 X Y f (Inj0 x) = 0.
{ let X Y f x. assume Hx.
  prove (fun x' :e 1 :+: X => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) x') (Inj0 x) = 0.
  rewrite beta (1 :+: X) (fun x' => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) x') (Inj0 x) (Inj0_setsum 1 X x Hx).
  prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) (Inj0 x) = 0.
  exact combine_funcs_eq1 1 X (fun _ => 0) (fun x => Inj1 (f x)) x.
}
claim LFf0': forall X Y f, F1 X Y f 0 = 0.
{ let X Y f.
  rewrite <- Inj0_0 at 4.
  apply LFf0 X Y f 0. exact In_0_1.
}
claim LFf1: forall X Y f, forall x :e X, F1 X Y f (Inj1 x) = Inj1 (f x).
{ let X Y f x. assume Hx.
  prove (fun x' :e 1 :+: X => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) x') (Inj1 x) = Inj1 (f x).
  rewrite beta (1 :+: X) (fun x' => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) x') (Inj1 x) (Inj1_setsum 1 X x Hx).
  prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) (Inj1 x) = Inj1 (f x).
  exact combine_funcs_eq2 1 X (fun _ => 0) (fun x => Inj1 (f x)) x.
}
claim Leps0: forall X e, forall x :e 1, eps (pack_e X e) (Inj0 x) = e.
{ let X e x. assume Hx.
  claim Leps0a: combine_funcs 1 X (fun _ => pack_e X e 1) (fun x => x) (Inj0 x) = e.
  { apply pack_e_1_eq2 X e (fun u v => combine_funcs 1 X (fun _ => u) (fun x => x) (Inj0 x) = e).
    prove combine_funcs 1 X (fun _ => e) (fun x => x) (Inj0 x) = e.
    exact combine_funcs_eq1 1 X (fun _ => e) (fun x => x) x.
  }
  claim Leps0b: combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) (Inj0 x) = e.
  { exact pack_e_0_eq2 X e (fun u v => combine_funcs 1 u (fun _ => pack_e X e 1) (fun x => x) (Inj0 x) = e) Leps0a. }
  prove (fun x' :e 1 :+: (pack_e X e 0) => combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) x') (Inj0 x) = e.
  transitivity combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) (Inj0 x).
  - prove (fun x' :e 1 :+: (pack_e X e 0) => combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) x') (Inj0 x)
        = combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) (Inj0 x).
    apply pack_e_0_eq2 X e (fun u v => (fun x' :e 1 :+: u => combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) x') (Inj0 x)
        = combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) (Inj0 x)).
    prove (fun x' :e 1 :+: X => combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) x') (Inj0 x)
        = combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) (Inj0 x).
    exact beta (1 :+: X) (fun x' => combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) x') (Inj0 x) (Inj0_setsum 1 X x Hx).
  - exact Leps0b.
}
claim Leps0': forall X e, eps (pack_e X e) 0 = e.
{ let X e.
  apply Inj0_0 (fun u v => eps (pack_e X e) u = e).
  prove eps (pack_e X e) (Inj0 0) = e.
  apply Leps0.
  exact In_0_1.
}
claim Leps1: forall X e, forall x :e X, eps (pack_e X e) (Inj1 x) = x.
{ let X e x. assume Hx.
  claim Leps1a: combine_funcs 1 X (fun _ => pack_e X e 1) (fun x => x) (Inj1 x) = x.
  { exact combine_funcs_eq2 1 X (fun _ => pack_e X e 1) (fun x => x) x. }
  claim Leps1b: combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) (Inj1 x) = x.
  { exact pack_e_0_eq2 X e (fun u v => combine_funcs 1 u (fun _ => pack_e X e 1) (fun x => x) (Inj1 x) = x) Leps1a. }
  prove (fun x' :e 1 :+: (pack_e X e 0) => combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) x') (Inj1 x) = x.
  transitivity combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) (Inj1 x).
  - prove (fun x' :e 1 :+: (pack_e X e 0) => combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) x') (Inj1 x)
        = combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) (Inj1 x).
    apply pack_e_0_eq2 X e (fun u v => (fun x' :e 1 :+: u => combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) x') (Inj1 x)
        = combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) (Inj1 x)).
    prove (fun x' :e 1 :+: X => combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) x') (Inj1 x)
        = combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) (Inj1 x).
    exact beta (1 :+: X) (fun x' => combine_funcs 1 (pack_e X e 0) (fun _ => pack_e X e 1) (fun x => x) x') (Inj1 x) (Inj1_setsum 1 X x Hx).
  - exact Leps1b.
}
apply MetaAdjunction_strict_I.
- prove MetaFunctor_strict (fun _ => True) SetHom (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
         struct_e Hom_struct_e struct_id struct_comp
         F0 F1.
  apply MetaFunctor_strict_I.
  + exact MetaCatSet.
  + exact MetaCat_struct_e.
  + prove MetaFunctor (fun _ => True) SetHom (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
            struct_e Hom_struct_e struct_id struct_comp
            F0 F1.
    apply MetaFunctorI.
    * let X. assume HX. exact LFX X.
    * let X Y f. assume HX HY Hf. exact LFf X Y f Hf.
    * { let X. assume HX.
        prove F1 X X (lam_id X) = lam_id (F0 X 0).
        prove (fun x' :e 1 :+: X => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_id X x)) x')
            = (fun x' :e F0 X 0 => x').
        rewrite LFX0.
        prove (fun x' :e 1 :+: X => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_id X x)) x')
            = (fun x' :e 1 :+: X => x').
        apply lam_ext. let x'. assume Hx': x' :e 1 :+: X.
        prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_id X x)) x' = x'.
        apply setsum_Inj_inv 1 X x' Hx'.
        - assume H1. apply H1. let x. assume Hx. apply Hx.
          assume Hx: x :e 1.
          assume Hx2: x' = Inj0 x.
	  rewrite Hx2.
	  prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_id X x)) (Inj0 x) = (Inj0 x).
	  rewrite combine_funcs_eq1.
	  prove 0 = Inj0 x.
	  apply cases_1 x Hx.
	  prove 0 = Inj0 0.
	  symmetry. exact Inj0_0.
        - assume H1. apply H1. let x. assume Hx. apply Hx.
          assume Hx: x :e X.
          assume Hx2: x' = Inj1 x.
          rewrite Hx2.
	  prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_id X x)) (Inj1 x) = (Inj1 x).
	  rewrite combine_funcs_eq2.
	  prove Inj1 (lam_id X x) = Inj1 x.
	  f_equal.
	  exact beta X (fun x => x) x Hx.
      }
    * { let X Y Z f g. assume HX HY HZ Hf Hg.
        prove F1 X Z (lam_comp X g f) = lam_comp (F0 X 0) (F1 Y Z g) (F1 X Y f).
	prove (fun x' :e 1 :+: X => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) x')
            = (fun x' :e F0 X 0 => F1 Y Z g (F1 X Y f x')).
        rewrite LFX0.
        apply lam_ext. let x'. assume Hx': x' :e 1 :+: X.
        apply setsum_Inj_inv 1 X x' Hx'.
        - assume H1. apply H1. let x. assume Hx. apply Hx.
          assume Hx: x :e 1.
          assume Hx2: x' = Inj0 x.
	  rewrite Hx2.
	  prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) (Inj0 x)
	      = F1 Y Z g (F1 X Y f (Inj0 x)).
	  apply LFf0 X Y f x Hx
	         (fun u v => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) (Inj0 x)
                           = F1 Y Z g v).
	  prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) (Inj0 x)
	      = F1 Y Z g 0.
	  apply LFf0' Y Z g (fun u v => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) (Inj0 x) = v).
	  prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) (Inj0 x) = 0.
	  exact combine_funcs_eq1 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) x.
        - assume H1. apply H1. let x. assume Hx. apply Hx.
          assume Hx: x :e X.
          assume Hx2: x' = Inj1 x.
          rewrite Hx2.
	  prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) (Inj1 x)
	      = F1 Y Z g (F1 X Y f (Inj1 x)).
	  apply LFf1 X Y f x Hx
	         (fun u v => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) (Inj1 x)
                           = F1 Y Z g v).
	  prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) (Inj1 x)
	      = F1 Y Z g (Inj1 (f x)).
	  apply LFf1 Y Z g (f x) (ap_Pi X (fun _ => Y) f x Hf Hx)
	         (fun u v => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) (Inj1 x)
                           = v).
	  prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) (Inj1 x)
	      = Inj1 (g (f x)).
          apply combine_funcs_eq2 1 X (fun _ => 0) (fun x => Inj1 (lam_comp X g f x)) x
	          (fun u v => v = Inj1 (g (f x))).
	  prove Inj1 (lam_comp X g f x) = Inj1 (g (f x)).
	  f_equal.
	  prove (fun x :e X => g (f x)) x = g (f x).
	  exact beta X (fun x => g (f x)) x Hx.
      }
- prove MetaFunctor struct_e Hom_struct_e (fun X => lam_id (X 0)) (fun X Y Z f g => lam_comp (X 0) f g) (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g) (fun X => X 0) (fun X Y f => f).
  exact MetaCat_struct_e_Forgetful.
- prove MetaNatTrans (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g) (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g) (fun X => X) (fun X Y f => f) (fun X => F0 X 0) (fun X Y f => (F1 X Y f)) eta.
  apply MetaNatTransI.
  + let X. assume HX. prove eta X :e F0 X 0 :^: X.
    rewrite LFX0.
    prove eta X :e (1 :+: X) :^: X.
    prove (fun x :e X => Inj1 x) :e Pi_ _ :e X, 1 :+: X.
    apply lam_Pi. let x. assume Hx.
    prove Inj1 x :e 1 :+: X.
    apply Inj1_setsum. exact Hx.
  + let X Y f. assume HX HY. assume Hf: f :e Y :^: X.
    prove lam_comp X (F1 X Y f) (eta X) = lam_comp X (eta Y) f.
    prove (fun x :e X => F1 X Y f (eta X x)) = (fun x :e X => eta Y (f x)).
    apply lam_ext.
    let x. assume Hx: x :e X.
    prove F1 X Y f (eta X x) = eta Y (f x).
    prove F1 X Y f ((fun x :e X => Inj1 x) x) = eta Y (f x).
    rewrite beta X (fun x => Inj1 x) x Hx.
    prove F1 X Y f (Inj1 x) = (fun y :e Y => Inj1 y) (f x).
    rewrite beta Y (fun y => Inj1 y) (f x) (ap_Pi X (fun _ => Y) f x Hf Hx).
    prove F1 X Y f (Inj1 x) = Inj1 (f x).
    prove (fun x' :e 1 :+: X => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) x') (Inj1 x) = Inj1 (f x).
    rewrite beta (1 :+: X) (fun x' => combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) x') (Inj1 x) (Inj1_setsum 1 X x Hx).
    prove combine_funcs 1 X (fun _ => 0) (fun x => Inj1 (f x)) (Inj1 x) = Inj1 (f x).
    exact combine_funcs_eq2 1 X (fun _ => 0) (fun x => Inj1 (f x)) x.
- prove MetaNatTrans struct_e Hom_struct_e (fun X => lam_id (X 0)) (fun X Y Z f g => lam_comp (X 0) f g) struct_e Hom_struct_e (fun X => lam_id (X 0)) (fun X Y Z f g => lam_comp (X 0) f g) (fun Y => F0 (Y 0)) (fun X Y g => F1 (X 0) (Y 0) g) (fun Y => Y) (fun X Y g => g) eps.
  apply MetaNatTransI.
  + let X. assume HX: struct_e X.
    prove Hom_struct_e (F0 (X 0)) X (eps X).
    claim L1: forall X' e, e :e X' -> Hom_struct_e (F0 (pack_e X' e 0)) (pack_e X' e) (eps (pack_e X' e)).
    { let X' e. assume He: e :e X'.
      prove Hom_struct_e (F0 (pack_e X' e 0)) (pack_e X' e) (eps (pack_e X' e)).
      rewrite <- pack_e_0_eq2.
      prove Hom_struct_e (F0 X') (pack_e X' e) (eps (pack_e X' e)).
      prove Hom_struct_e (pack_e (1 :+: X') 0) (pack_e X' e) (eps (pack_e X' e)).
      claim L1a: eps (pack_e X' e) :e X' :^: (1 :+: X') /\ eps (pack_e X' e) 0 = e.
      { apply andI.
        - prove (fun x' :e 1 :+: (pack_e X' e 0) => combine_funcs 1 (pack_e X' e 0) (fun _ => pack_e X' e 1) (fun x => x) x') :e Pi_ _ :e 1 :+: X', X'.
	  apply pack_e_0_eq2 X' e (fun u v => (fun x' :e 1 :+: u => combine_funcs 1 u (fun _ => pack_e X' e 1) (fun x => x) x') :e Pi_ _ :e 1 :+: X', X').
	  prove (fun x' :e 1 :+: X' => combine_funcs 1 X' (fun _ => pack_e X' e 1) (fun x => x) x') :e Pi_ _ :e 1 :+: X', X'.
	  claim L1aa: (fun x' :e 1 :+: X' => combine_funcs 1 X' (fun _ => e) (fun x => x) x') :e Pi_ _ :e 1 :+: X', X'.
	  { apply lam_Pi.
            let x'. assume Hx'.
	    prove combine_funcs 1 X' (fun _ => e) (fun x => x) x' :e X'.
            apply setsum_Inj_inv 1 X' x' Hx'.
            - assume H1. apply H1. let x. assume Hx. apply Hx.
              assume Hx: x :e 1.
              assume Hx2: x' = Inj0 x.
              rewrite Hx2.
	      prove combine_funcs 1 X' (fun _ => e) (fun x => x) (Inj0 x) :e X'.
	      rewrite combine_funcs_eq1.
	      prove e :e X'. exact He.
            - assume H1. apply H1. let x. assume Hx. apply Hx.
              assume Hx: x :e X'.
              assume Hx2: x' = Inj1 x.
              rewrite Hx2.
	      prove combine_funcs 1 X' (fun _ => e) (fun x => x) (Inj1 x) :e X'.
	      rewrite combine_funcs_eq2.
	      exact Hx.
	  }
	  exact pack_e_1_eq2 X' e (fun u v => (fun x' :e 1 :+: X' => combine_funcs 1 X' (fun _ => u) (fun x => x) x') :e Pi_ _ :e 1 :+: X', X') L1aa.
	- exact Leps0' X' e.
      }
      exact Hom_struct_e_pack (1 :+: X') X' 0 e (eps (pack_e X' e)) (fun u v => v) L1a.
    }
    exact HX (fun u => Hom_struct_e (F0 (u 0)) u (eps u)) L1.
  + let X Y f.
    assume HX: struct_e X.
    assume HY: struct_e Y.
    prove Hom_struct_e X Y f -> lam_comp (F0 (X 0) 0) f (eps X) = lam_comp (F0 (X 0) 0) (eps Y) (F1 (X 0) (Y 0) f).
    apply HX (fun X => Hom_struct_e X Y f -> lam_comp (F0 (X 0) 0) f (eps X) = lam_comp (F0 (X 0) 0) (eps Y) (F1 (X 0) (Y 0) f)).
    let X' c. assume Hc: c :e X'.
    claim L2: Hom_struct_e (pack_e X' c) Y f -> lam_comp (F0 X' 0) f (eps (pack_e X' c)) = lam_comp (F0 X' 0) (eps Y) (F1 X' (Y 0) f).
    { apply HY (fun Y => Hom_struct_e (pack_e X' c) Y f -> lam_comp (F0 X' 0) f (eps (pack_e X' c)) = lam_comp (F0 X' 0) (eps Y) (F1 X' (Y 0) f)).
      let Y' d. assume Hd: d :e Y'.
      prove Hom_struct_e (pack_e X' c) (pack_e Y' d) f -> lam_comp (F0 X' 0) f (eps (pack_e X' c)) = lam_comp (F0 X' 0) (eps (pack_e Y' d)) (F1 X' (pack_e Y' d 0) f).
      claim L2a: Hom_struct_e (pack_e X' c) (pack_e Y' d) f -> lam_comp (F0 X' 0) f (eps (pack_e X' c)) = lam_comp (F0 X' 0) (eps (pack_e Y' d)) (F1 X' Y' f).
      { assume H1.
	apply Hom_struct_e_pack X' Y' c d f (fun u v => u) H1.
	assume H2: f :e Y' :^: X'.
	assume H3: f c = d.
	prove lam_comp (F0 X' 0) f (eps (pack_e X' c)) = lam_comp (F0 X' 0) (eps (pack_e Y' d)) (F1 X' Y' f).
	apply LFX0 X' (fun u v => lam_comp v f (eps (pack_e X' c)) = lam_comp v (eps (pack_e Y' d)) (F1 X' Y' f)).
	prove lam_comp (1 :+: X') f (eps (pack_e X' c)) = lam_comp (1 :+: X') (eps (pack_e Y' d)) (F1 X' Y' f).
	prove (fun x' :e (1 :+: X') => f (eps (pack_e X' c) x'))
	    = (fun x' :e (1 :+: X') => eps (pack_e Y' d) (F1 X' Y' f x')).
	apply lam_ext.
	let x'. assume Hx'.
        apply setsum_Inj_inv 1 X' x' Hx'.
	- assume H4. apply H4. let x. assume Hx. apply Hx.
          assume Hx: x :e 1.
          assume Hx2: x' = Inj0 x.
          rewrite Hx2.
          prove f (eps (pack_e X' c) (Inj0 x)) = eps (pack_e Y' d) (F1 X' Y' f (Inj0 x)).
	  transitivity f c, d, eps (pack_e Y' d) 0.
	  + f_equal. exact Leps0 X' c x Hx.
	  + exact H3.
	  + symmetry. exact Leps0' Y' d.
	  + f_equal. symmetry. exact LFf0 X' Y' f x Hx.
        - assume H4. apply H4. let x. assume Hx. apply Hx.
          assume Hx: x :e X'.
          assume Hx2: x' = Inj1 x.
          rewrite Hx2.
          prove f (eps (pack_e X' c) (Inj1 x)) = eps (pack_e Y' d) (F1 X' Y' f (Inj1 x)).
	  transitivity f x, eps (pack_e Y' d) (Inj1 (f x)).
	  + f_equal. exact Leps1 X' c x Hx.
	  + symmetry. exact Leps1 Y' d (f x) (ap_Pi X' (fun _ => Y') f x H2 Hx).
	  + f_equal. symmetry. exact LFf1 X' Y' f x Hx.
      }
      exact pack_e_0_eq2 Y' d (fun u v => Hom_struct_e (pack_e X' c) (pack_e Y' d) f -> lam_comp (F0 X' 0) f (eps (pack_e X' c)) = lam_comp (F0 X' 0) (eps (pack_e Y' d)) (F1 X' u f)) L2a.
    }
    exact pack_e_0_eq2 X' c (fun u v => Hom_struct_e (pack_e X' c) Y f -> lam_comp (F0 u 0) f (eps (pack_e X' c)) = lam_comp (F0 u 0) (eps Y) (F1 u (Y 0) f)) L2.
- prove MetaAdjunction
          (fun _ => True) SetHom (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
          struct_e Hom_struct_e struct_id struct_comp
          F0 F1 (fun X => X 0) (fun X Y f => f) eta eps.
  apply MetaAdjunctionI.
  + let X. assume HX.
    prove lam_comp (F0 X 0) (eps (F0 X)) (F1 X (F0 X 0) (eta X)) = lam_id (F0 X 0).
    rewrite LFX0.
    prove lam_comp (1 :+: X) (eps (F0 X)) (F1 X (1 :+: X) (eta X)) = lam_id (1 :+: X).
    prove (fun x' :e 1 :+: X => eps (F0 X) (F1 X (1 :+: X) (eta X) x'))
        = (fun x' :e 1 :+: X => x').
    apply lam_ext.
    let x'. assume Hx'.
    prove eps (F0 X) (F1 X (1 :+: X) (eta X) x') = x'.
    apply setsum_Inj_inv 1 X x' Hx'.
    * { assume H4. apply H4. let x. assume Hx. apply Hx.
        assume Hx: x :e 1.
        assume Hx2: x' = Inj0 x.
        rewrite Hx2.
        prove eps (F0 X) (F1 X (1 :+: X) (eta X) (Inj0 x)) = Inj0 x.
	transitivity eps (F0 X) 0, 0.
	- f_equal. exact LFf0 X (1 :+: X) (eta X) x Hx.
	- exact Leps0' (1 :+: X) 0.
	- prove 0 = Inj0 x. symmetry. exact cases_1 x Hx (fun u => Inj0 u = 0) Inj0_0.
      }
    * { assume H4. apply H4. let x. assume Hx. apply Hx.
        assume Hx: x :e X.
        assume Hx2: x' = Inj1 x.
        rewrite Hx2.
	prove eps (F0 X) (F1 X (1 :+: X) (eta X) (Inj1 x)) = Inj1 x.
	transitivity eps (F0 X) (Inj1 (eta X x)), eta X x.
	- f_equal. exact LFf1 X (1 :+: X) (eta X) x Hx.
	- apply Leps1 (1 :+: X) 0 (eta X x).
	  prove eta X x :e 1 :+: X.
	  prove (fun x :e X => Inj1 x) x :e 1 :+: X.
	  rewrite beta X Inj1 x Hx.
	  prove Inj1 x :e 1 :+: X.
	  exact Inj1_setsum 1 X x Hx.
	- prove eta X x = Inj1 x.
	  prove (fun x :e X => Inj1 x) x = Inj1 x.
	  exact beta X Inj1 x Hx.
      }
  + let Y. assume HY: struct_e Y.
    prove lam_comp (Y 0) (eps Y) (eta (Y 0)) = lam_id (Y 0).
    apply HY (fun Y => lam_comp (Y 0) (eps Y) (eta (Y 0)) = lam_id (Y 0)).
    let Y' e. assume He: e :e Y'.
    prove (fun y :e pack_e Y' e 0 => eps (pack_e Y' e) (eta (pack_e Y' e 0) y)) = (fun y :e pack_e Y' e 0 => y).
    apply pack_e_0_eq2 Y' e (fun u v => (fun y :e u => eps (pack_e Y' e) (eta u y)) = (fun y :e u => y)).
    prove (fun y :e Y' => eps (pack_e Y' e) (eta Y' y)) = (fun y :e Y' => y).
    apply lam_ext.
    let y. assume Hy: y :e Y'.
    prove eps (pack_e Y' e) (eta Y' y) = y.
    prove eps (pack_e Y' e) ((fun y :e Y' => Inj1 y) y) = y.
    rewrite beta Y' Inj1 y Hy.
    prove eps (pack_e Y' e) (Inj1 y) = y.
    exact Leps1 Y' e y Hy.
Qed.
