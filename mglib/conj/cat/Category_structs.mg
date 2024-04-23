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

Theorem MetaCat_struct_p: MetaCat struct_p Hom_struct_p struct_id struct_comp.
exact MetaCat_struct_p_gen struct_p (fun X H => H).
Qed.

Theorem MetaCat_struct_p_Forgetful: MetaFunctor struct_p Hom_struct_p
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
exact MetaCat_struct_p_Forgetful_gen struct_p (fun X H => H).
Qed.

Theorem MetaCat_struct_u: MetaCat struct_u Hom_struct_u struct_id struct_comp.
exact MetaCat_struct_u_gen struct_u (fun X H => H).
Qed.

Theorem MetaCat_struct_u_Forgetful: MetaFunctor struct_u Hom_struct_u
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
exact MetaCat_struct_u_Forgetful_gen struct_u (fun X H => H).
Qed.

Theorem MetaCat_struct_r: MetaCat struct_r Hom_struct_r struct_id struct_comp.
exact MetaCat_struct_r_gen struct_r (fun X H => H).
Qed.

Theorem MetaCat_struct_r_Forgetful: MetaFunctor struct_r Hom_struct_r
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
exact MetaCat_struct_r_Forgetful_gen struct_r (fun X H => H).
Qed.

Theorem MetaCat_struct_b: MetaCat struct_b Hom_struct_b struct_id struct_comp.
exact MetaCat_struct_b_gen struct_b (fun X H => H).
Qed.

Theorem MetaCat_struct_b_Forgetful: MetaFunctor struct_b Hom_struct_b
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
exact MetaCat_struct_b_Forgetful_gen struct_b (fun X H => H).
Qed.

Theorem MetaCat_struct_c: MetaCat struct_c Hom_struct_c struct_id struct_comp.
exact MetaCat_struct_c_gen struct_c (fun X H => H).
Qed.

Theorem MetaCat_struct_c_Forgetful: MetaFunctor struct_c Hom_struct_c
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
exact MetaCat_struct_c_Forgetful_gen struct_c (fun X H => H).
Qed.

Theorem MetaCat_struct_b_b_e: MetaCat struct_b_b_e Hom_struct_b_b_e struct_id struct_comp.
exact MetaCat_struct_b_b_e_gen struct_b_b_e (fun X H => H).
Qed.

Theorem MetaCat_struct_b_b_e_Forgetful: MetaFunctor struct_b_b_e Hom_struct_b_b_e
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
exact MetaCat_struct_b_b_e_Forgetful_gen struct_b_b_e (fun X H => H).
Qed.

Theorem MetaCat_struct_b_b_e_e: MetaCat struct_b_b_e_e Hom_struct_b_b_e_e struct_id struct_comp.
exact MetaCat_struct_b_b_e_e_gen struct_b_b_e_e (fun X H => H).
Qed.

Theorem MetaCat_struct_b_b_e_e_Forgetful: MetaFunctor struct_b_b_e_e Hom_struct_b_b_e_e
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
exact MetaCat_struct_b_b_e_e_Forgetful_gen struct_b_b_e_e (fun X H => H).
Qed.

Theorem MetaCat_struct_b_b_r_e_e: MetaCat struct_b_b_r_e_e Hom_struct_b_b_r_e_e struct_id struct_comp.
exact MetaCat_struct_b_b_r_e_e_gen struct_b_b_r_e_e (fun X H => H).
Qed.

Theorem MetaCat_struct_b_b_r_e_e_Forgetful: MetaFunctor struct_b_b_r_e_e Hom_struct_b_b_r_e_e
          struct_id struct_comp
          (fun _ => True) SetHom
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).
exact MetaCat_struct_b_b_r_e_e_Forgetful_gen struct_b_b_r_e_e (fun X H => H).
Qed.

