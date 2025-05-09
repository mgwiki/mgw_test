(** $I sig/Part1.mgs **)

(** Part 2 **)

(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.

(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.

(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

(* Superscript :^: *)
Infix :^: 430 left := setexp.

(* Parameter DescrR_i_io_1 "1f005fdad5c6f98763a15a5e5539088f5d43b7d1be866b0b204fda1ce9ed9248" "1d3fd4a14ef05bd43f5c147d7966cf05fd2fed808eea94f56380454b9a6044b2" *)
Definition DescrR_i_io_1 : (set->(set->prop)->prop) -> set := fun R => Eps_i (fun x => (exists y:set -> prop, R x y) /\ (forall y z:set -> prop, R x y -> R x z -> y = z)).

(* Parameter DescrR_i_io_2 "28d8599686476258c12dcc5fc5f5974335febd7d5259e1a8e5918b7f9b91ca03" "768eb2ad186988375e6055394e36e90c81323954b8a44eb08816fb7a84db2272" *)
Definition DescrR_i_io_2 : (set->(set->prop)->prop) -> set->prop := fun R => Descr_Vo1 (fun y => R (DescrR_i_io_1 R) y).

Theorem DescrR_i_io_12 : forall R:set->(set->prop)->prop, (exists x, (exists y:set->prop, R x y) /\ (forall y z:set -> prop, R x y -> R x z -> y = z)) -> R (DescrR_i_io_1 R) (DescrR_i_io_2 R).
let R.
assume H1: exists x, (exists y:set->prop, R x y) /\ (forall y z:set -> prop, R x y -> R x z -> y = z).
claim L1: (exists y:set->prop, R (DescrR_i_io_1 R) y) /\ (forall y z:set -> prop, R (DescrR_i_io_1 R) y -> R (DescrR_i_io_1 R) z -> y = z).
{ exact (Eps_i_ex (fun x => (exists y:set->prop, R x y) /\ (forall y z:set -> prop, R x y -> R x z -> y = z)) H1). }
apply L1.
assume H2 H3.
exact Descr_Vo1_prop (fun y => R (DescrR_i_io_1 R) y) H2 H3.
Qed.

(** Conway describes this way of formalizing in ZF in an appendix to Part Zero of his book,
    but rejects formalization in favor of "Mathematician's Liberation."
 **)

Definition PNoEq_ : set -> (set -> prop) -> (set -> prop) -> prop
 := fun alpha p q => forall beta :e alpha, p beta <-> q beta.

Theorem PNoEq_ref_ : forall alpha, forall p:set -> prop, PNoEq_ alpha p p.
let alpha p beta.
assume H2.
apply iff_refl.
Qed.

Theorem PNoEq_sym_ : forall alpha, forall p q:set -> prop, PNoEq_ alpha p q -> PNoEq_ alpha q p.
let alpha p q.
assume H1.
let beta. assume H2.
apply iff_sym.
exact H1 beta H2.
Qed.

Theorem PNoEq_tra_ : forall alpha, forall p q r:set -> prop, PNoEq_ alpha p q -> PNoEq_ alpha q r -> PNoEq_ alpha p r.
let alpha p q r.
assume H1 H2.
let beta. assume H3.
apply iff_trans (p beta) (q beta).
- exact H1 beta H3.
- exact H2 beta H3.
Qed.

Theorem PNoEq_antimon_ : forall p q:set -> prop, forall alpha, ordinal alpha -> forall beta :e alpha, PNoEq_ alpha p q -> PNoEq_ beta p q.
let p q alpha. assume Ha. let beta. assume Hb H1.
let gamma.
assume H2: gamma :e beta.
prove p gamma <-> q gamma.
apply H1.
prove gamma :e alpha.
apply Ha. assume Ha1 _. exact Ha1 beta Hb gamma H2.
Qed.

Definition PNoLt_ : set -> (set -> prop) -> (set -> prop) -> prop
 := fun alpha p q => exists beta :e alpha, PNoEq_ beta p q /\ ~p beta /\ q beta.

Theorem PNoLt_E_ : forall alpha, forall p q:set -> prop, PNoLt_ alpha p q ->
  forall R:prop, (forall beta, beta :e alpha -> PNoEq_ beta p q -> ~p beta -> q beta -> R) -> R.
let alpha p q. assume H1. let R. assume H2.
apply H1.
let beta. assume H3. apply H3.
assume H4: beta :e alpha.
assume H5. apply H5. assume H5. apply H5.
assume H6 H7 H8.
exact H2 beta H4 H6 H7 H8.
Qed.

Theorem PNoLt_irref_ : forall alpha, forall p:set -> prop, ~PNoLt_ alpha p p.
let alpha p. assume H1. apply H1.
let beta. assume H2. apply H2.
assume _ H3. apply H3. assume H3. apply H3.
assume _ H4 H5. exact H4 H5.
Qed.

Theorem PNoLt_mon_ : forall p q:set -> prop, forall alpha, ordinal alpha -> forall beta :e alpha, PNoLt_ beta p q -> PNoLt_ alpha p q.
let p q alpha. assume Ha. let beta. assume Hb H1.
apply H1. let gamma. assume H2. apply H2.
assume H2: gamma :e beta.
assume H3.
prove exists beta :e alpha, PNoEq_ beta p q /\ ~p beta /\ q beta.
witness gamma. apply andI.
- prove gamma :e alpha. apply Ha. assume Ha1 _. exact Ha1 beta Hb gamma H2.
- exact H3.
Qed.

Theorem PNoLt_trichotomy_or_ : forall p q:set -> prop, forall alpha, ordinal alpha
  -> PNoLt_ alpha p q \/ PNoEq_ alpha p q \/ PNoLt_ alpha q p.
let p q.
apply ordinal_ind.
let alpha. assume Ha.
assume IH: forall beta :e alpha, PNoLt_ beta p q \/ PNoEq_ beta p q \/ PNoLt_ beta q p.
apply xm (PNoEq_ alpha p q).
- assume H1: PNoEq_ alpha p q.
  apply orIL. apply orIR. exact H1.
- assume H1: ~PNoEq_ alpha p q.
  claim L1: exists beta, ~(beta :e alpha -> (p beta <-> q beta)).
  { exact not_all_ex_demorgan_i (fun beta => beta :e alpha -> (p beta <-> q beta)) H1. }
  apply L1. let beta. assume H2: ~(beta :e alpha -> (p beta <-> q beta)).
  claim L2: beta :e alpha /\ ~(p beta <-> q beta).
  { apply xm (beta :e alpha).
    - assume H3: beta :e alpha.
      apply xm (p beta <-> q beta).
      + assume H4: p beta <-> q beta.
        prove False.
        apply H2. assume _. exact H4.
      + assume H4: ~(p beta <-> q beta).
        apply andI.
        * exact H3.
        * exact H4.
    - assume H3: beta /:e alpha.
      prove False.
      apply H2.
      assume H4. prove False. exact H3 H4.
  }
  apply L2.
  assume H3: beta :e alpha.
  assume H4: ~(p beta <-> q beta).
  apply IH beta H3. assume H5. apply H5.
  + assume H5: PNoLt_ beta p q. apply orIL. apply orIL.
    exact PNoLt_mon_ p q alpha Ha beta H3 H5.
  + assume H5: PNoEq_ beta p q.
    apply xm (p beta).
    * { assume H6: p beta.
        apply xm (q beta).
        - assume H7: q beta.
          prove False. apply H4. apply iffI.
          + assume _. exact H7.
          + assume _. exact H6.
        - assume H7: ~q beta.
          apply orIR.
          prove exists beta :e alpha, PNoEq_ beta q p /\ ~q beta /\ p beta.
          witness beta. apply andI.
          + exact H3.
          + apply and3I.
            * apply PNoEq_sym_. exact H5.
            * exact H7.
            * exact H6.
      }
    * { assume H6: ~p beta.
        apply xm (q beta).
        - assume H7: q beta.
          apply orIL. apply orIL.
          prove exists beta :e alpha, PNoEq_ beta p q /\ ~p beta /\ q beta.
          witness beta. apply andI.
          + exact H3.
          + apply and3I.
            * exact H5.
            * exact H6.
            * exact H7.
        - assume H7: ~q beta.
          prove False. apply H4. apply iffI.
          + assume H8. prove False. exact H6 H8.
          + assume H8. prove False. exact H7 H8.
      }
  + assume H5: PNoLt_ beta q p. apply orIR.
    exact PNoLt_mon_ q p alpha Ha beta H3 H5.
Qed.

Theorem PNoLt_tra_ : forall alpha, ordinal alpha -> forall p q r:set -> prop, PNoLt_ alpha p q -> PNoLt_ alpha q r -> PNoLt_ alpha p r.
let alpha. assume Ha. let p q r. assume Hpq Hqr.
prove exists beta :e alpha, PNoEq_ beta p r /\ ~p beta /\ r beta.
apply PNoLt_E_ alpha p q Hpq.
let beta.
assume Hbeta1: beta :e alpha.
assume Hbeta2: PNoEq_ beta p q.
assume Hbeta3: ~p beta.
assume Hbeta4: q beta.
apply PNoLt_E_ alpha q r Hqr.
let gamma.
assume Hgamma1: gamma :e alpha.
assume Hgamma2: PNoEq_ gamma q r.
assume Hgamma3: ~q gamma.
assume Hgamma4: r gamma.
claim Lbeta: ordinal beta.
{ exact ordinal_Hered alpha Ha beta Hbeta1. }
claim Lgamma: ordinal gamma.
{ exact ordinal_Hered alpha Ha gamma Hgamma1. }
apply ordinal_trichotomy_or beta gamma Lbeta Lgamma.
assume H1. apply H1.
- assume H1: beta :e gamma.
  witness beta. apply andI.
  + exact Hbeta1.
  + apply and3I.
    * prove PNoEq_ beta p r.
      apply PNoEq_tra_ beta p q r Hbeta2.
      prove PNoEq_ beta q r.
      exact PNoEq_antimon_ q r gamma Lgamma beta H1 Hgamma2.
    * prove ~p beta. exact Hbeta3.
    * { prove r beta.
        apply Hgamma2 beta H1.
        assume H2 _. exact H2 Hbeta4.
      }
- assume H1: beta = gamma.
  witness beta. apply andI.
  + exact Hbeta1.
  + apply and3I.
    * prove PNoEq_ beta p r.
      apply PNoEq_tra_ beta p q r Hbeta2.
      prove PNoEq_ beta q r.
      rewrite H1.
      exact Hgamma2.
    * prove ~p beta. exact Hbeta3.
    * prove r beta. rewrite H1. exact Hgamma4.
- assume H1: gamma :e beta.
  witness gamma. apply andI.
  + exact Hgamma1.
  + apply and3I.
    * { prove PNoEq_ gamma p r.
        apply PNoEq_tra_ gamma p q r.
        - prove PNoEq_ gamma p q.
          exact PNoEq_antimon_ p q beta Lbeta gamma H1 Hbeta2.
        - exact Hgamma2.
      }
    * { prove ~p gamma.
        assume H2: p gamma.
        apply Hbeta2 gamma H1.
        assume H3 _.
        apply Hgamma3.
        prove q gamma.
        exact H3 H2.
      }
    * prove r gamma. exact Hgamma4.
Qed.

(* Parameter PNoLt "2336eb45d48549dd8a6a128edc17a8761fd9043c180691483bcf16e1acc9f00a" "8f57a05ce4764eff8bc94b278352b6755f1a46566cd7220a5488a4a595a47189" *)
Definition PNoLt : set -> (set -> prop) -> set -> (set -> prop) -> prop
 := fun alpha p beta q =>
        PNoLt_ (alpha :/\: beta) p q
     \/ alpha :e beta /\ PNoEq_ alpha p q /\ q alpha
     \/ beta :e alpha /\ PNoEq_ beta p q /\ ~p beta.

Theorem PNoLtI1 : forall alpha beta, forall p q:set -> prop,
  PNoLt_ (alpha :/\: beta) p q -> PNoLt alpha p beta q.
let alpha beta p q. assume H1.
prove PNoLt_ (alpha :/\: beta) p q
   \/ alpha :e beta /\ PNoEq_ alpha p q /\ q alpha
   \/ beta :e alpha /\ PNoEq_ beta p q /\ ~p beta.
apply or3I1. exact H1.
Qed.

Theorem PNoLtI2 : forall alpha beta, forall p q:set -> prop,
  alpha :e beta -> PNoEq_ alpha p q -> q alpha -> PNoLt alpha p beta q.
let alpha beta p q. assume H1 H2 H3.
prove PNoLt_ (alpha :/\: beta) p q
   \/ alpha :e beta /\ PNoEq_ alpha p q /\ q alpha
   \/ beta :e alpha /\ PNoEq_ beta p q /\ ~p beta.
apply or3I2. apply and3I.
- exact H1.
- exact H2.
- exact H3.
Qed.

Theorem PNoLtI3 : forall alpha beta, forall p q:set -> prop,
  beta :e alpha -> PNoEq_ beta p q -> ~p beta -> PNoLt alpha p beta q.
let alpha beta p q. assume H1 H2 H3.
prove PNoLt_ (alpha :/\: beta) p q
   \/ alpha :e beta /\ PNoEq_ alpha p q /\ q alpha
   \/ beta :e alpha /\ PNoEq_ beta p q /\ ~p beta.
apply or3I3. apply and3I.
- exact H1.
- exact H2.
- exact H3.
Qed.

Theorem PNoLtE : forall alpha beta, forall p q:set -> prop,
  PNoLt alpha p beta q ->
  forall R:prop,
      (PNoLt_ (alpha :/\: beta) p q -> R)
   -> (alpha :e beta -> PNoEq_ alpha p q -> q alpha -> R)
   -> (beta :e alpha -> PNoEq_ beta p q -> ~p beta -> R)
   -> R.
let alpha beta p q.
assume H1. let R. assume HC1 HC2 HC3.
apply H1. assume H1. apply H1.
- exact HC1.
- assume H1. apply H1. assume H1. apply H1. exact HC2.
- assume H1. apply H1. assume H1. apply H1. exact HC3.
Qed.

Theorem PNoLt_irref : forall alpha, forall p:set -> prop, ~PNoLt alpha p alpha p.
let alpha p. assume H1.
apply PNoLtE alpha alpha p p H1.
- assume H1: PNoLt_ (alpha :/\: alpha) p p.
  exact PNoLt_irref_ (alpha :/\: alpha) p H1.
- assume H1: alpha :e alpha. prove False.
  exact In_irref alpha H1.
- assume H1: alpha :e alpha. prove False.
  exact In_irref alpha H1.
Qed.

Theorem PNoLt_trichotomy_or : forall alpha beta, forall p q:set -> prop,
 ordinal alpha -> ordinal beta ->
 PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q \/ PNoLt beta q alpha p.
let alpha beta p q. assume Ha Hb.
apply Ha. assume Ha1 _.
apply Hb. assume Hb1 _.
claim Lab: ordinal (alpha :/\: beta).
{ exact ordinal_binintersect alpha beta Ha Hb. }
apply PNoLt_trichotomy_or_ p q (alpha :/\: beta) Lab. assume H1. apply H1.
- assume H1: PNoLt_ (alpha :/\: beta) p q.
  apply or3I1. apply PNoLtI1. exact H1.
- assume H1: PNoEq_ (alpha :/\: beta) p q.
  apply ordinal_trichotomy_or alpha beta Ha Hb. assume H2. apply H2.
  + assume H2: alpha :e beta.
    claim L1: alpha :/\: beta = alpha.
    { exact binintersect_Subq_eq_1 alpha beta (Hb1 alpha H2). }
    claim L2: PNoEq_ alpha p q.
    { rewrite <- L1. exact H1. }
    apply xm (q alpha).
    * { assume H3: q alpha.
        apply or3I1.
        apply PNoLtI2.
        - exact H2.
        - prove PNoEq_ alpha p q. exact L2.
        - exact H3.
      }
    * { assume H3: ~q alpha.
        apply or3I3.
        apply PNoLtI3.
        - exact H2.
        - prove PNoEq_ alpha q p. apply PNoEq_sym_. exact L2.
        - exact H3.
      }
  + assume H2: alpha = beta.
    claim L1: alpha :/\: beta = alpha.
    { rewrite <- H2. exact binintersect_Subq_eq_1 alpha alpha (Subq_ref alpha). }
    claim L2: PNoEq_ alpha p q.
    { rewrite <- L1. exact H1. }
    apply or3I2. apply andI.
    * exact H2.
    * prove PNoEq_ alpha p q. exact L2.
  + assume H2: beta :e alpha.
    claim L1: alpha :/\: beta = beta.
    { rewrite binintersect_com.
      exact binintersect_Subq_eq_1 beta alpha (Ha1 beta H2).
    }
    claim L2: PNoEq_ beta p q.
    { rewrite <- L1. exact H1. }
    apply xm (p beta).
    * { assume H3: p beta.
        apply or3I3.
        apply PNoLtI2.
        - exact H2.
        - prove PNoEq_ beta q p. apply PNoEq_sym_. exact L2.
        - exact H3.
      }
    * { assume H3: ~p beta.
        apply or3I1.
        apply PNoLtI3.
        - exact H2.
        - prove PNoEq_ beta p q. exact L2.
        - exact H3.
      }
- assume H1: PNoLt_ (alpha :/\: beta) q p.
  apply or3I3. apply PNoLtI1. rewrite binintersect_com. exact H1.
Qed.

Theorem PNoLtEq_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoEq_ beta q r -> PNoLt alpha p beta r.
let alpha beta. assume Ha Hb.
let p q r.
assume Hpq Hqr.
apply PNoLtE alpha beta p q Hpq.
- assume Hpq1: PNoLt_ (alpha :/\: beta) p q.
  apply Hpq1. let delta. assume Hpq2. apply Hpq2.
  assume Hd: delta :e alpha :/\: beta.
  apply binintersectE alpha beta delta Hd.
  assume Hd1 Hd2.
  assume Hpq3. apply Hpq3. assume Hpq3. apply Hpq3.
  assume Hpq3: PNoEq_ delta p q.
  assume Hpq4: ~p delta.
  assume Hpq5: q delta.
  prove PNoLt alpha p beta r.
  apply PNoLtI1.
  prove exists delta :e alpha :/\: beta, PNoEq_ delta p r /\ ~p delta /\ r delta.
  witness delta. apply andI.
  + exact Hd.
  + apply and3I.
    * { prove PNoEq_ delta p r. apply PNoEq_tra_ delta p q r.
        - prove PNoEq_ delta p q. exact Hpq3.
        - prove PNoEq_ delta q r.
          apply PNoEq_antimon_ q r beta Hb delta Hd2.
          prove PNoEq_ beta q r.
          exact Hqr.
      }
    * prove ~p delta. exact Hpq4.
    * prove r delta. exact iffEL (q delta) (r delta) (Hqr delta Hd2) Hpq5.
- assume Hpq1: alpha :e beta.
  assume Hpq2: PNoEq_ alpha p q.
  assume Hpq3: q alpha.
  prove PNoLt alpha p beta r.
  apply PNoLtI2.
  + prove alpha :e beta. exact Hpq1.
  + prove PNoEq_ alpha p r. apply PNoEq_tra_ alpha p q r.
    * exact Hpq2.
    * prove PNoEq_ alpha q r.
      apply PNoEq_antimon_ q r beta Hb alpha Hpq1.
      exact Hqr.
  + prove r alpha.
    exact iffEL (q alpha) (r alpha) (Hqr alpha Hpq1) Hpq3.
- assume Hpq1: beta :e alpha.
  assume Hpq2: PNoEq_ beta p q.
  assume Hpq3: ~p beta.
  prove PNoLt alpha p beta r.
  apply PNoLtI3.
  + prove beta :e alpha. exact Hpq1.
  + prove PNoEq_ beta p r. apply PNoEq_tra_ beta p q r.
    * exact Hpq2.
    * exact Hqr.
  + prove ~p beta. exact Hpq3.
Qed.

Theorem PNoEqLt_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoEq_ alpha p q -> PNoLt alpha q beta r -> PNoLt alpha p beta r.
let alpha beta. assume Ha Hb.
let p q r.
assume Hpq Hqr.
apply PNoLtE alpha beta q r Hqr.
- assume Hqr1: PNoLt_ (alpha :/\: beta) q r.
  apply Hqr1. let delta. assume Hqr2. apply Hqr2.
  assume Hd: delta :e alpha :/\: beta.
  apply binintersectE alpha beta delta Hd.
  assume Hd1 Hd2.
  assume Hqr3. apply Hqr3. assume Hqr3. apply Hqr3.
  assume Hqr3: PNoEq_ delta q r.
  assume Hqr4: ~q delta.
  assume Hqr5: r delta.
  prove PNoLt alpha p beta r.
  apply PNoLtI1.
  prove exists delta :e alpha :/\: beta, PNoEq_ delta p r /\ ~p delta /\ r delta.
  witness delta. apply andI.
  + exact Hd.
  + apply and3I.
    * { prove PNoEq_ delta p r. apply PNoEq_tra_ delta p q r.
        - prove PNoEq_ delta p q.
          apply PNoEq_antimon_ p q alpha Ha delta Hd1.
          prove PNoEq_ alpha p q.
          exact Hpq.
        - prove PNoEq_ delta q r. exact Hqr3.
      }
    * prove ~p delta.
      assume H1: p delta.
      apply Hqr4.
      prove q delta.
      exact iffEL (p delta) (q delta) (Hpq delta Hd1) H1.
    * prove r delta. exact Hqr5.
- assume Hqr1: alpha :e beta.
  assume Hqr2: PNoEq_ alpha q r.
  assume Hqr3: r alpha.
  prove PNoLt alpha p beta r.
  apply PNoLtI2.
  + prove alpha :e beta. exact Hqr1.
  + prove PNoEq_ alpha p r. apply PNoEq_tra_ alpha p q r.
    * exact Hpq.
    * exact Hqr2.
  + prove r alpha. exact Hqr3.
- assume Hqr1: beta :e alpha.
  assume Hqr2: PNoEq_ beta q r.
  assume Hqr3: ~q beta.
  prove PNoLt alpha p beta r.
  apply PNoLtI3.
  + prove beta :e alpha. exact Hqr1.
  + prove PNoEq_ beta p r. apply PNoEq_tra_ beta p q r.
    * apply PNoEq_antimon_ p q alpha Ha beta Hqr1. exact Hpq.
    * exact Hqr2.
  + prove ~p beta.
    assume H1: p beta.
    apply Hqr3.
    exact iffEL (p beta) (q beta) (Hpq beta Hqr1) H1.
Qed.

Theorem PNoLt_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoLt beta q gamma r -> PNoLt alpha p gamma r.
let alpha beta gamma. assume Ha Hb Hc.
apply Ha. assume Ha1 _.
apply Hc. assume Hc1 _.
let p q r.
assume Hpq Hqr.
apply PNoLtE alpha beta p q Hpq.
- assume Hpq1: PNoLt_ (alpha :/\: beta) p q.
  apply Hpq1. let delta. assume Hpq2. apply Hpq2.
  assume Hd: delta :e alpha :/\: beta.
  apply binintersectE alpha beta delta Hd.
  assume Hd1 Hd2.
  assume Hpq3. apply Hpq3. assume Hpq3. apply Hpq3.
  assume Hpq3: PNoEq_ delta p q.
  assume Hpq4: ~p delta.
  assume Hpq5: q delta.
  claim Ld: ordinal delta.
  { exact ordinal_Hered beta Hb delta Hd2. }
  apply PNoLtE beta gamma q r Hqr.
  + assume Hqr1: PNoLt_ (beta :/\: gamma) q r.
    apply Hqr1. let eps. assume Hqr2. apply Hqr2.
    assume He: eps :e beta :/\: gamma.
    apply binintersectE beta gamma eps He.
    assume He1 He2.
    assume Hqr3. apply Hqr3. assume Hqr3. apply Hqr3.
    assume Hqr3: PNoEq_ eps q r.
    assume Hqr4: ~q eps.
    assume Hqr5: r eps.
    claim Le: ordinal eps.
    { exact ordinal_Hered beta Hb eps He1. }
    prove PNoLt alpha p gamma r.
    apply PNoLtI1.
    prove exists delta :e alpha :/\: gamma, PNoEq_ delta p r /\ ~p delta /\ r delta.
    apply ordinal_trichotomy_or delta eps Ld Le. assume H1. apply H1.
    * { assume H1: delta :e eps.
        witness delta. apply andI.
        - prove delta :e alpha :/\: gamma. apply binintersectI.
          + exact Hd1.
          + prove delta :e gamma. exact Hc1 eps He2 delta H1.
        - apply and3I.
          + prove PNoEq_ delta p r.
            apply PNoEq_tra_ delta p q r.
            * prove PNoEq_ delta p q. exact Hpq3.
            * prove PNoEq_ delta q r.
              apply PNoEq_antimon_ q r eps Le delta H1.
              prove PNoEq_ eps q r. exact Hqr3.
          + prove ~p delta. exact Hpq4.
          + prove r delta.
            exact iffEL (q delta) (r delta) (Hqr3 delta H1) Hpq5.
      }
    * { assume H1: delta = eps.
        witness delta. apply andI.
        - prove delta :e alpha :/\: gamma. apply binintersectI.
          + exact Hd1.
          + prove delta :e gamma. rewrite H1. exact He2.
        - apply and3I.
          + prove PNoEq_ delta p r.
            apply PNoEq_tra_ delta p q r.
            * prove PNoEq_ delta p q. exact Hpq3.
            * prove PNoEq_ delta q r. rewrite H1. exact Hqr3.
          + prove ~p delta. exact Hpq4.
          + prove r delta. rewrite H1. exact Hqr5.
      }
    * { assume H1: eps :e delta.
        witness eps. apply andI.
        - prove eps :e alpha :/\: gamma. apply binintersectI.
          + prove eps :e alpha. exact Ha1 delta Hd1 eps H1.
          + exact He2.
        - apply and3I.
          + prove PNoEq_ eps p r.
            apply PNoEq_tra_ eps p q r.
            * prove PNoEq_ eps p q. apply PNoEq_antimon_ p q delta Ld eps H1.
              prove PNoEq_ delta p q. exact Hpq3.
            * prove PNoEq_ eps q r. exact Hqr3.
          + prove ~p eps.
            assume H2: p eps.
            apply Hqr4.
            exact iffEL (p eps) (q eps) (Hpq3 eps H1) H2.
          + prove r eps. exact Hqr5.
      }
  + assume Hqr1: beta :e gamma.
    assume Hqr2: PNoEq_ beta q r.
    assume Hqr3: r beta.
    apply PNoLtI1.
    prove exists delta :e alpha :/\: gamma, PNoEq_ delta p r /\ ~p delta /\ r delta.
    witness delta. apply andI.
    * { prove delta :e alpha :/\: gamma. apply binintersectI.
        - exact Hd1.
        - prove delta :e gamma. exact Hc1 beta Hqr1 delta Hd2.
      }
    * { apply and3I.
        - prove PNoEq_ delta p r.
          apply PNoEq_tra_ delta p q r.
          + prove PNoEq_ delta p q. exact Hpq3.
          + prove PNoEq_ delta q r.
            apply PNoEq_antimon_ q r beta Hb delta Hd2.
            prove PNoEq_ beta q r. exact Hqr2.
        - prove ~p delta. exact Hpq4.
        - prove r delta.
          exact iffEL (q delta) (r delta) (Hqr2 delta Hd2) Hpq5.
      }
  + assume Hqr1: gamma :e beta.
    assume Hqr2: PNoEq_ gamma q r.
    assume Hqr3: ~q gamma.
    apply ordinal_trichotomy_or delta gamma Ld Hc. assume H1. apply H1.
    * { assume H1: delta :e gamma.
        prove PNoLt alpha p gamma r.
        apply PNoLtI1.
        prove exists delta :e alpha :/\: gamma, PNoEq_ delta p r /\ ~p delta /\ r delta.
        witness delta. apply andI.
        - prove delta :e alpha :/\: gamma. apply binintersectI.
          + exact Hd1.
          + prove delta :e gamma. exact H1.
        - apply and3I.
          + prove PNoEq_ delta p r.
            apply PNoEq_tra_ delta p q r.
            * prove PNoEq_ delta p q. exact Hpq3.
            * prove PNoEq_ delta q r.
              apply PNoEq_antimon_ q r gamma Hc delta H1.
              prove PNoEq_ gamma q r. exact Hqr2.
          + prove ~p delta. exact Hpq4.
          + prove r delta.
            exact iffEL (q delta) (r delta) (Hqr2 delta H1) Hpq5.
      }
    * { assume H1: delta = gamma.
        apply PNoLtI3.
        - prove gamma :e alpha. rewrite <- H1. exact Hd1.
        - prove PNoEq_ gamma p r. apply PNoEq_tra_ gamma p q r.
          + prove PNoEq_ gamma p q. rewrite <- H1. exact Hpq3.
          + prove PNoEq_ gamma q r. exact Hqr2.
        - prove ~p gamma. rewrite <- H1. exact Hpq4.
      }
    * { assume H1: gamma :e delta.
        apply PNoLtI3.
        - prove gamma :e alpha. exact Ha1 delta Hd1 gamma H1.
        - prove PNoEq_ gamma p r. apply PNoEq_tra_ gamma p q r.
          + prove PNoEq_ gamma p q.
            apply PNoEq_antimon_ p q delta Ld gamma H1.
            exact Hpq3.
          + prove PNoEq_ gamma q r. exact Hqr2.
        - prove ~p gamma.
          assume H2: p gamma.
          apply Hqr3.
          prove q gamma.
          exact iffEL (p gamma) (q gamma) (Hpq3 gamma H1) H2.
      }
- assume Hpq1: alpha :e beta.
  assume Hpq2: PNoEq_ alpha p q.
  assume Hpq3: q alpha.
  apply PNoLtE beta gamma q r Hqr.
  + assume Hqr1: PNoLt_ (beta :/\: gamma) q r.
    apply Hqr1. let eps. assume Hqr2. apply Hqr2.
    assume He: eps :e beta :/\: gamma.
    apply binintersectE beta gamma eps He.
    assume He1 He2.
    assume Hqr3. apply Hqr3. assume Hqr3. apply Hqr3.
    assume Hqr3: PNoEq_ eps q r.
    assume Hqr4: ~q eps.
    assume Hqr5: r eps.
    claim Le: ordinal eps.
    { exact ordinal_Hered beta Hb eps He1. }
    apply ordinal_trichotomy_or alpha eps Ha Le. assume H1. apply H1.
    * { assume H1: alpha :e eps.
        prove PNoLt alpha p gamma r.
        apply PNoLtI2.
        - prove alpha :e gamma. exact Hc1 eps He2 alpha H1.
        - prove PNoEq_ alpha p r. apply PNoEq_tra_ alpha p q r.
          + prove PNoEq_ alpha p q. exact Hpq2.
          + prove PNoEq_ alpha q r.
            apply PNoEq_antimon_ q r eps Le alpha H1.
            prove PNoEq_ eps q r.
            exact Hqr3.
        - prove r alpha.
          exact iffEL (q alpha) (r alpha) (Hqr3 alpha H1) Hpq3.
      }
    * { assume H1: alpha = eps.
        prove PNoLt alpha p gamma r.
        apply PNoLtI2.
        - prove alpha :e gamma. rewrite H1. exact He2.
        - prove PNoEq_ alpha p r. apply PNoEq_tra_ alpha p q r.
          + prove PNoEq_ alpha p q. exact Hpq2.
          + prove PNoEq_ alpha q r. rewrite H1.
            prove PNoEq_ eps q r.
            exact Hqr3.
        - prove r alpha. rewrite H1. exact Hqr5.
      }
    * { assume H1: eps :e alpha.
        prove PNoLt alpha p gamma r.
        apply PNoLtI1.
        prove exists delta :e alpha :/\: gamma, PNoEq_ delta p r /\ ~p delta /\ r delta.
        witness eps. apply andI.
        - prove eps :e alpha :/\: gamma. apply binintersectI.
          + exact H1.
          + exact He2.
        - apply and3I.
          + prove PNoEq_ eps p r. apply PNoEq_tra_ eps p q r.
            * prove PNoEq_ eps p q.
              apply PNoEq_antimon_ p q alpha Ha eps H1.
              prove PNoEq_ alpha p q.
              exact Hpq2.
            * prove PNoEq_ eps q r. exact Hqr3.
          + prove ~p eps.
            assume H2: p eps.
            apply Hqr4.
            prove q eps.
            exact iffEL (p eps) (q eps) (Hpq2 eps H1) H2.
          + prove r eps. exact Hqr5.
      }
  + assume Hqr1: beta :e gamma.
    assume Hqr2: PNoEq_ beta q r.
    assume Hqr3: r beta.
    apply PNoLtI2.
    * prove alpha :e gamma. exact Hc1 beta Hqr1 alpha Hpq1.
    * { prove PNoEq_ alpha p r. apply PNoEq_tra_ alpha p q r.
        - exact Hpq2.
        - apply PNoEq_antimon_ q r beta Hb alpha Hpq1.
          exact Hqr2.
      }
    * prove r alpha. exact iffEL (q alpha) (r alpha) (Hqr2 alpha Hpq1) Hpq3.
  + assume Hqr1: gamma :e beta.
    assume Hqr2: PNoEq_ gamma q r.
    assume Hqr3: ~q gamma.
    prove PNoLt alpha p gamma r.
    apply ordinal_trichotomy_or alpha gamma Ha Hc. assume H1. apply H1.
    * { assume H1: alpha :e gamma.
        apply PNoLtI2.
        - prove alpha :e gamma. exact H1.
        - prove PNoEq_ alpha p r. apply PNoEq_tra_ alpha p q r.
          + exact Hpq2.
          + apply PNoEq_antimon_ q r gamma Hc alpha H1.
            exact Hqr2.
        - prove r alpha.
          exact iffEL (q alpha) (r alpha) (Hqr2 alpha H1) Hpq3.
      }
    * assume H1: alpha = gamma. prove False. apply Hqr3. rewrite <- H1. exact Hpq3.
    * { assume H1: gamma :e alpha.
        apply PNoLtI3.
        - prove gamma :e alpha. exact H1.
        - prove PNoEq_ gamma p r. apply PNoEq_tra_ gamma p q r.
          + apply PNoEq_antimon_ p q alpha Ha gamma H1.
            exact Hpq2.
          + exact Hqr2.
        - prove ~p gamma.
          assume H2: p gamma.
          apply Hqr3. prove q gamma.
          exact iffEL (p gamma) (q gamma) (Hpq2 gamma H1) H2.
      }
- assume Hpq1: beta :e alpha.
  assume Hpq2: PNoEq_ beta p q.
  assume Hpq3: ~p beta.
  apply PNoLtE beta gamma q r Hqr.
  + assume Hqr1: PNoLt_ (beta :/\: gamma) q r.
    apply Hqr1. let eps. assume Hqr2. apply Hqr2.
    assume He: eps :e beta :/\: gamma.
    apply binintersectE beta gamma eps He.
    assume He1 He2.
    assume Hqr3. apply Hqr3. assume Hqr3. apply Hqr3.
    assume Hqr3: PNoEq_ eps q r.
    assume Hqr4: ~q eps.
    assume Hqr5: r eps.
    prove PNoLt alpha p gamma r.
    apply PNoLtI1.
    prove exists delta :e alpha :/\: gamma, PNoEq_ delta p r /\ ~p delta /\ r delta.
    witness eps. apply andI.
    * { prove eps :e alpha :/\: gamma. apply binintersectI.
        - prove eps :e alpha. exact Ha1 beta Hpq1 eps He1.
        - exact He2.
      }
    * { apply and3I.
        - prove PNoEq_ eps p r. apply PNoEq_tra_ eps p q r.
          + prove PNoEq_ eps p q.
            apply PNoEq_antimon_ p q beta Hb eps He1.
            exact Hpq2.
          + exact Hqr3.
        - prove ~p eps.
          assume H1: p eps.
          apply Hqr4.
          prove q eps.
          exact iffEL (p eps) (q eps) (Hpq2 eps He1) H1.
        - prove r eps. exact Hqr5.
      }
  + assume Hqr1: beta :e gamma.
    assume Hqr2: PNoEq_ beta q r.
    assume Hqr3: r beta.
    apply PNoLtI1.
    prove exists delta :e alpha :/\: gamma, PNoEq_ delta p r /\ ~p delta /\ r delta.
    witness beta. apply andI.
    * { apply binintersectI.
        - exact Hpq1.
        - exact Hqr1.
      }
    * { apply and3I.
        - apply PNoEq_tra_ beta p q r.
          + exact Hpq2.
          + exact Hqr2.
        - prove ~p beta. exact Hpq3.
        - prove r beta. exact Hqr3.
      }
  + assume Hqr1: gamma :e beta.
    assume Hqr2: PNoEq_ gamma q r.
    assume Hqr3: ~q gamma.
    apply PNoLtI3.
    * prove gamma :e alpha. exact Ha1 beta Hpq1 gamma Hqr1.
    * { prove PNoEq_ gamma p r. apply PNoEq_tra_ gamma p q r.
        - prove PNoEq_ gamma p q.
          apply PNoEq_antimon_ p q beta Hb gamma Hqr1.
          exact Hpq2.
        - exact Hqr2.
      }
    * prove ~p gamma.
      assume H1: p gamma.
      apply Hqr3. prove q gamma.
      exact iffEL (p gamma) (q gamma) (Hpq2 gamma Hqr1) H1.
Qed.

Definition PNoLe : set -> (set -> prop) -> set -> (set -> prop) -> prop
   := fun alpha p beta q => PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q.

Theorem PNoLeI1 : forall alpha beta, forall p q:set -> prop,
   PNoLt alpha p beta q -> PNoLe alpha p beta q.
let alpha beta p q.
assume H1.
prove PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q.
apply orIL. exact H1.
Qed.

Theorem PNoLeI2 : forall alpha, forall p q:set -> prop,
   PNoEq_ alpha p q -> PNoLe alpha p alpha q.
let alpha p q.
assume H1.
prove PNoLt alpha p alpha q \/ alpha = alpha /\ PNoEq_ alpha p q.
apply orIR. apply andI.
- reflexivity.
- exact H1.
Qed.

Theorem PNoLe_ref : forall alpha, forall p:set -> prop, PNoLe alpha p alpha p.
let alpha p.
apply PNoLeI2.
apply PNoEq_ref_.
Qed.

Theorem PNoLe_antisym : forall alpha beta, ordinal alpha -> ordinal beta ->
 forall p q:set -> prop,
 PNoLe alpha p beta q -> PNoLe beta q alpha p -> alpha = beta /\ PNoEq_ alpha p q.
let alpha beta. assume Ha Hb.
let p q.
assume H1: PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q.
assume H2: PNoLt beta q alpha p \/ beta = alpha /\ PNoEq_ beta q p.
apply H1.
- assume H1: PNoLt alpha p beta q.
  prove False.
  apply H2.
  + assume H2: PNoLt beta q alpha p.
    apply PNoLt_irref alpha p.
    apply PNoLt_tra alpha beta alpha Ha Hb Ha p q p.
    * exact H1.
    * exact H2.
  + assume H2. apply H2.
    assume H2a: beta = alpha.
    assume H2b: PNoEq_ beta q p.
    apply PNoLtE alpha beta p q H1.
    * assume Hpq1: PNoLt_ (alpha :/\: beta) p q.
      apply Hpq1. let delta. assume Hpq2. apply Hpq2.
      assume Hd: delta :e alpha :/\: beta.
      apply binintersectE alpha beta delta Hd.
      assume Hd1 Hd2.
      assume Hpq3. apply Hpq3. assume Hpq3. apply Hpq3.
      assume Hpq3: PNoEq_ delta p q.
      assume Hpq4: ~p delta.
      assume Hpq5: q delta.
      apply Hpq4.
      exact iffEL (q delta) (p delta) (H2b delta Hd2) Hpq5.
    * assume Hpq1: alpha :e beta.
      assume Hpq2: PNoEq_ alpha p q.
      assume Hpq3: q alpha.
      apply In_irref alpha.
      rewrite <- H2a at 2.
      exact Hpq1.
    * assume Hpq1: beta :e alpha.
      assume Hpq2: PNoEq_ beta p q.
      assume Hpq3: ~p beta.
      apply In_irref alpha.
      rewrite <- H2a at 1.
      exact Hpq1.
- assume H1. exact H1.
Qed.

Theorem PNoLtLe_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoLe beta q gamma r -> PNoLt alpha p gamma r.
let alpha beta gamma. assume Ha Hb Hc.
let p q r.
assume H1: PNoLt alpha p beta q.
assume H2: PNoLt beta q gamma r \/ beta = gamma /\ PNoEq_ beta q r.
apply H2.
- assume H2: PNoLt beta q gamma r.
  exact PNoLt_tra alpha beta gamma Ha Hb Hc p q r H1 H2.
- assume H2. apply H2.
  assume H2a: beta = gamma.
  assume H2b: PNoEq_ beta q r.
  prove PNoLt alpha p gamma r.
  rewrite <- H2a.
  prove PNoLt alpha p beta r.
  exact PNoLtEq_tra alpha beta Ha Hb p q r H1 H2b.
Qed.

Theorem PNoLeLt_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLe alpha p beta q -> PNoLt beta q gamma r -> PNoLt alpha p gamma r.
let alpha beta gamma. assume Ha Hb Hc.
let p q r.
assume H1: PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q.
assume H2: PNoLt beta q gamma r.
apply H1.
- assume H1: PNoLt alpha p beta q.
  exact PNoLt_tra alpha beta gamma Ha Hb Hc p q r H1 H2.
- assume H1. apply H1.
  assume H1a: alpha = beta.
  assume H1b: PNoEq_ alpha p q.
  prove PNoLt alpha p gamma r.
  rewrite H1a.
  prove PNoLt beta p gamma r.
  apply PNoEqLt_tra beta gamma Hb Hc p q r.
  + prove PNoEq_ beta p q. rewrite <- H1a. exact H1b.
  + exact H2.
Qed.

Theorem PNoEqLe_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoEq_ alpha p q -> PNoLe alpha q beta r -> PNoLe alpha p beta r.
let alpha beta. assume Ha Hb.
let p q r.
assume Hpq.
assume Hqr: PNoLt alpha q beta r \/ alpha = beta /\ PNoEq_ alpha q r.
prove PNoLt alpha p beta r \/ alpha = beta /\ PNoEq_ alpha p r.
apply Hqr.
- assume Hqr1.
  apply orIL.
  exact PNoEqLt_tra alpha beta Ha Hb p q r Hpq Hqr1.
- assume Hqr. apply Hqr.
  assume Hqr1: alpha = beta.
  assume Hqr2: PNoEq_ alpha q r.
  apply orIR.
  apply andI.
  + exact Hqr1.
  + exact PNoEq_tra_ alpha p q r Hpq Hqr2.
Qed.

Theorem PNoLe_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLe alpha p beta q -> PNoLe beta q gamma r -> PNoLe alpha p gamma r.
let alpha beta gamma. assume Ha Hb Hc.
let p q r.
assume H1: PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q.
assume H2: PNoLe beta q gamma r.
apply H1.
- assume H1: PNoLt alpha p beta q.
  prove PNoLt alpha p gamma r \/ alpha = gamma /\ PNoEq_ alpha p r.
  apply orIL.
  exact PNoLtLe_tra alpha beta gamma Ha Hb Hc p q r H1 H2.
- assume H1. apply H1.
  assume H1a: alpha = beta.
  assume H1b: PNoEq_ alpha p q.
  prove PNoLe alpha p gamma r.
  rewrite H1a.
  prove PNoLe beta p gamma r.
  claim L1: PNoEq_ beta p q.
  { rewrite <- H1a. exact H1b. }
  exact PNoEqLe_tra beta gamma Hb Hc p q r L1 H2.
Qed.

Definition PNo_downc : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
 := fun L alpha p => exists beta, ordinal beta /\ exists q:set -> prop, L beta q /\ PNoLe alpha p beta q.

Definition PNo_upc : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
 := fun R alpha p => exists beta, ordinal beta /\ exists q:set -> prop, R beta q /\ PNoLe beta q alpha p.

Theorem PNoLe_downc : forall L:set -> (set -> prop) -> prop, forall alpha beta, forall p q:set -> prop,
  ordinal alpha -> ordinal beta ->
  PNo_downc L alpha p -> PNoLe beta q alpha p -> PNo_downc L beta q.
let L alpha beta p q. assume Ha Hb.
assume H1: PNo_downc L alpha p.
assume H2: PNoLe beta q alpha p.
prove PNo_downc L beta q.
apply H1. let gamma. assume H3. apply H3.
assume Hc: ordinal gamma. assume H3. apply H3.
let r. assume H3. apply H3.
assume H3: L gamma r.
assume H4: PNoLe alpha p gamma r.
prove exists delta, ordinal delta /\ exists r:set -> prop, L delta r /\ PNoLe beta q delta r.
witness gamma. apply andI.
- exact Hc.
- witness r. apply andI.
  + exact H3.
  + exact PNoLe_tra beta alpha gamma Hb Ha Hc q p r H2 H4.
Qed.

Theorem PNo_downc_ref : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, L alpha p -> PNo_downc L alpha p.
let L alpha. assume Ha. let p.
assume H1: L alpha p.
prove exists beta, ordinal beta /\ exists q:set -> prop, L beta q /\ PNoLe alpha p beta q.
witness alpha. apply andI.
- exact Ha.
- witness p. apply andI.
  + exact H1.
  + apply PNoLe_ref.
Qed.

Theorem PNo_upc_ref : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, R alpha p -> PNo_upc R alpha p.
let R alpha. assume Ha. let p.
assume H1: R alpha p.
prove exists beta, ordinal beta /\ exists q:set -> prop, R beta q /\ PNoLe beta q alpha p.
witness alpha. apply andI.
- exact Ha.
- witness p. apply andI.
  + exact H1.
  + apply PNoLe_ref.
Qed.

Theorem PNoLe_upc : forall R:set -> (set -> prop) -> prop, forall alpha beta, forall p q:set -> prop,
  ordinal alpha -> ordinal beta ->
  PNo_upc R alpha p -> PNoLe alpha p beta q -> PNo_upc R beta q.
let R alpha beta p q. assume Ha Hb.
assume H1: PNo_upc R alpha p.
assume H2: PNoLe alpha p beta q.
prove PNo_upc R beta q.
apply H1. let gamma. assume H3. apply H3.
assume Hc: ordinal gamma. assume H3. apply H3.
let r. assume H3. apply H3.
assume H3: R gamma r.
assume H4: PNoLe gamma r alpha p.
prove exists delta, ordinal delta /\ exists r:set -> prop, R delta r /\ PNoLe delta r beta q.
witness gamma. apply andI.
- exact Hc.
- witness r. apply andI.
  + exact H3.
  + exact PNoLe_tra gamma alpha beta Hc Ha Hb r p q H4 H2.
Qed.

Definition PNoLt_pwise : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> prop
  := fun L R => forall gamma, ordinal gamma -> forall p:set -> prop, L gamma p -> forall delta, ordinal delta -> forall q:set -> prop, R delta q -> PNoLt gamma p delta q.

Theorem PNoLt_pwise_downc_upc : forall L R:set -> (set -> prop) -> prop,
    PNoLt_pwise L R -> PNoLt_pwise (PNo_downc L) (PNo_upc R).
let L R. assume HLR.
prove PNoLt_pwise (PNo_downc L) (PNo_upc R).
let gamma. assume Hc. let p. assume Hp.
let delta. assume Hd. let q. assume Hq.
apply Hp. let alpha. assume H1. apply H1.
assume H2: ordinal alpha. assume H3. apply H3.
let p2. assume H3. apply H3.
assume H4: L alpha p2.
assume H5: PNoLe gamma p alpha p2.
apply Hq. let beta. assume H6. apply H6.
assume H7: ordinal beta. assume H8. apply H8.
let q2. assume H9. apply H9.
assume H10: R beta q2.
assume H11: PNoLe beta q2 delta q.
claim L1: PNoLt gamma p delta q.
{ apply PNoLeLt_tra gamma alpha delta Hc H2 Hd p p2 q H5.
  prove PNoLt alpha p2 delta q.
  apply PNoLtLe_tra alpha beta delta H2 H7 Hd p2 q2 q (HLR alpha H2 p2 H4 beta H7 q2 H10).
  prove PNoLe beta q2 delta q.
  exact H11.
}
apply PNoLt_trichotomy_or delta gamma q p Hd Hc. assume H12. apply H12.
- assume H12: PNoLt delta q gamma p.
  apply PNoLt_irref gamma p.
  prove PNoLt gamma p gamma p.
  apply PNoLt_tra gamma delta gamma Hc Hd Hc p q p L1.
  exact H12.
- assume H12: delta = gamma /\ PNoEq_ delta q p.
  apply PNoLt_irref delta q.
  prove PNoLt delta q delta q.
  apply PNoLeLt_tra delta gamma delta Hd Hc Hd q p q.
  + prove PNoLe delta q gamma p.
    prove PNoLt delta q gamma p \/ delta = gamma /\ PNoEq_ delta q p.
    apply orIR. exact H12.
  + prove PNoLt gamma p delta q. exact L1.
- assume H12: PNoLt gamma p delta q.
  exact H12.
Qed.

Definition PNo_rel_strict_upperbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L alpha p =>
       forall beta :e alpha, forall q:set -> prop, PNo_downc L beta q -> PNoLt beta q alpha p.

Definition PNo_rel_strict_lowerbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun R alpha p =>
       forall beta :e alpha, forall q:set -> prop, PNo_upc R beta q -> PNoLt alpha p beta q.

Definition PNo_rel_strict_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_rel_strict_upperbd L alpha p /\ PNo_rel_strict_lowerbd R alpha p.

Theorem PNoEq_rel_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L alpha q.
let L alpha. assume Ha. let p q.
assume Hpq: PNoEq_ alpha p q.
assume H1: PNo_rel_strict_upperbd L alpha p.
prove PNo_rel_strict_upperbd L alpha q.
let beta. assume Hb: beta :e alpha.
let r. assume H2: PNo_downc L beta r.
claim Lb: ordinal beta.
{ exact ordinal_Hered alpha Ha beta Hb. }
prove PNoLt beta r alpha q.
apply PNoLtEq_tra beta alpha Lb Ha r p q.
- prove PNoLt beta r alpha p.
  exact H1 beta Hb r H2.
- prove PNoEq_ alpha p q. exact Hpq.
Qed.

Theorem PNo_rel_strict_upperbd_antimon : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L beta p.
let L alpha. assume Ha. let p beta. assume Hb.
apply Ha. assume Ha1 _.
claim Lb: ordinal beta.
{ exact ordinal_Hered alpha Ha beta Hb. }
claim Lbt: TransSet beta.
{ apply Lb. assume H2 _. exact H2. }
assume H1: forall gamma :e alpha, forall q:set -> prop, PNo_downc L gamma q -> PNoLt gamma q alpha p.
prove forall gamma :e beta, forall q:set -> prop, PNo_downc L gamma q -> PNoLt gamma q beta p.
let gamma. assume Hc. let q. assume H4.
prove PNoLt gamma q beta p.
claim Lca: gamma :e alpha.
{ exact Ha1 beta Hb gamma Hc. }
claim L1: PNoLt gamma q alpha p.
{ apply H1.
  - prove gamma :e alpha. exact Lca.
  - prove PNo_downc L gamma q. exact H4.
}
apply PNoLtE gamma alpha q p L1.
+ assume H5: PNoLt_ (gamma :/\: alpha) q p.
  claim L2: gamma :/\: alpha = gamma.
  { apply binintersect_Subq_eq_1. exact Ha1 gamma Lca. }
  claim L3: gamma :/\: beta = gamma.
  { apply binintersect_Subq_eq_1. exact Lbt gamma Hc. }
  apply PNoLtI1.
  rewrite L3.
  rewrite <- L2.
  exact H5.
+ assume H5: gamma :e alpha.
  assume H6: PNoEq_ gamma q p.
  assume H7: p gamma.
  apply PNoLtI2.
  * prove gamma :e beta. exact Hc.
  * prove PNoEq_ gamma q p. exact H6.
  * prove p gamma. exact H7.
+ assume H5: alpha :e gamma.
  prove False.
  exact In_no2cycle alpha gamma H5 Lca.
Qed.

Theorem PNoEq_rel_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R alpha q.
let R alpha. assume Ha. let p q.
assume Hpq: PNoEq_ alpha p q.
assume H1: PNo_rel_strict_lowerbd R alpha p.
prove PNo_rel_strict_lowerbd R alpha q.
let beta. assume Hb: beta :e alpha.
let r. assume H2: PNo_upc R beta r.
claim Lb: ordinal beta.
{ exact ordinal_Hered alpha Ha beta Hb. }
prove PNoLt alpha q beta r.
apply PNoEqLt_tra alpha beta Ha Lb q p r.
- prove PNoEq_ alpha q p. apply PNoEq_sym_. exact Hpq.
- prove PNoLt alpha p beta r.
  exact H1 beta Hb r H2.
Qed.

Theorem PNo_rel_strict_lowerbd_antimon : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R beta p.
let R alpha. assume Ha. let p beta. assume Hb.
apply Ha. assume Ha1 _.
claim Lb: ordinal beta.
{ exact ordinal_Hered alpha Ha beta Hb. }
claim Lbt: TransSet beta.
{ apply Lb. assume H2 _. exact H2. }
assume H1: forall gamma :e alpha, forall q:set -> prop, PNo_upc R gamma q -> PNoLt alpha p gamma q.
prove forall gamma :e beta, forall q:set -> prop, PNo_upc R gamma q -> PNoLt beta p gamma q.
let gamma. assume Hc. let q. assume H4.
prove PNoLt beta p gamma q.
claim Lca: gamma :e alpha.
{ exact Ha1 beta Hb gamma Hc. }
claim L1: PNoLt alpha p gamma q.
{ apply H1.
  - prove gamma :e alpha. exact Lca.
  - prove PNo_upc R gamma q. exact H4.
}
apply PNoLtE alpha gamma p q L1.
+ assume H5: PNoLt_ (alpha :/\: gamma) p q.
  claim L2: alpha :/\: gamma = gamma.
  { rewrite binintersect_com. apply binintersect_Subq_eq_1. exact Ha1 gamma Lca. }
  claim L3: beta :/\: gamma = gamma.
  { rewrite binintersect_com. apply binintersect_Subq_eq_1. exact Lbt gamma Hc. }
  apply PNoLtI1.
  rewrite L3.
  rewrite <- L2.
  exact H5.
+ assume H5: alpha :e gamma.
  prove False.
  exact In_no2cycle alpha gamma H5 Lca.
+ assume H5: gamma :e alpha.
  assume H6: PNoEq_ gamma p q.
  assume H7: ~p gamma.
  apply PNoLtI3.
  * prove gamma :e beta. exact Hc.
  * prove PNoEq_ gamma p q. exact H6.
  * prove ~p gamma. exact H7.
Qed.

Theorem PNoEq_rel_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R alpha q.
let L R alpha. assume Ha. let p q. assume Hpq H1.
apply H1. assume H2 H3.
prove PNo_rel_strict_upperbd L alpha q /\ PNo_rel_strict_lowerbd R alpha q.
apply andI.
- exact PNoEq_rel_strict_upperbd L alpha Ha p q Hpq H2.
- exact PNoEq_rel_strict_lowerbd R alpha Ha p q Hpq H3.
Qed.

Theorem PNo_rel_strict_imv_antimon : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R beta p.
let L R alpha. assume Ha. let p beta. assume Hb H1.
apply H1. assume H2 H3.
prove PNo_rel_strict_upperbd L beta p /\ PNo_rel_strict_lowerbd R beta p.
apply andI.
- exact PNo_rel_strict_upperbd_antimon L alpha Ha p beta Hb H2.
- exact PNo_rel_strict_lowerbd_antimon R alpha Ha p beta Hb H3.
Qed.

Definition PNo_rel_strict_uniq_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_rel_strict_imv L R alpha p /\ forall q:set -> prop, PNo_rel_strict_imv L R alpha q -> PNoEq_ alpha p q.

Definition PNo_rel_strict_split_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p =>
         PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta /\ delta <> alpha)
      /\ PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta \/ delta = alpha).

Theorem PNo_extend0_eq : forall alpha, forall p:set -> prop, PNoEq_ alpha p (fun delta => p delta /\ delta <> alpha).
let alpha p.
set p0 : set -> prop := fun delta => p delta /\ delta <> alpha.
let beta. assume Hb: beta :e alpha.
prove p beta <-> p0 beta.
apply iffI.
- assume H1: p beta.
  prove p beta /\ beta <> alpha.
  apply andI.
  + exact H1.
  + prove beta <> alpha.
    assume H2: beta = alpha.
    apply In_irref alpha. rewrite <- H2 at 1. exact Hb.
- assume H1: p0 beta.
  apply H1. assume H2 _. exact H2.
Qed.

Theorem PNo_extend1_eq : forall alpha, forall p:set -> prop, PNoEq_ alpha p (fun delta => p delta \/ delta = alpha).
let alpha p.
set p1 : set -> prop := fun delta => p delta \/ delta = alpha.
let beta. assume Hb: beta :e alpha.
prove p beta <-> p1 beta.
apply iffI.
- assume H1: p beta.
  prove p beta \/ beta = alpha.
  apply orIL. exact H1.
- assume H1: p1 beta.
  apply H1.
  + assume H2: p beta. exact H2.
  + assume H2: beta = alpha.
    prove False.
    apply In_irref alpha. rewrite <- H2 at 1. exact Hb.
Qed.

Theorem PNo_rel_imv_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha ->
      (exists p:set -> prop, PNo_rel_strict_uniq_imv L R alpha p)
   \/ (exists tau :e alpha, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p).
let L R. assume HLR.
claim LLR: PNoLt_pwise (PNo_downc L) (PNo_upc R).
{ exact PNoLt_pwise_downc_upc L R HLR. }
apply ordinal_ind.
let alpha. assume Ha. apply Ha. assume Ha1 _.
assume IH: forall gamma :e alpha,
      (exists p:set -> prop, PNo_rel_strict_uniq_imv L R gamma p)
   \/ (exists tau :e gamma, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p).
apply dneg.
assume HNC: ~((exists p:set -> prop, PNo_rel_strict_uniq_imv L R alpha p)
   \/ (exists tau :e alpha, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p)).
apply not_or_and_demorgan (exists p:set -> prop, PNo_rel_strict_uniq_imv L R alpha p) (exists tau :e alpha, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p) HNC.
assume HNC1: ~(exists p:set -> prop, PNo_rel_strict_uniq_imv L R alpha p).
assume HNC2: ~(exists tau :e alpha, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p).
claim LIH: forall gamma :e alpha, exists p:set -> prop, PNo_rel_strict_uniq_imv L R gamma p.
{ let gamma.
  assume Hc: gamma :e alpha.
  apply IH gamma Hc.
  - assume H1. exact H1.
  - assume H1: exists tau :e gamma, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p.
    apply H1.
    let tau.
    assume H2. apply H2.
    assume Ht: tau :e gamma.
    assume H2. apply H2.
    let p.
    assume H3: PNo_rel_strict_split_imv L R tau p.
    apply HNC2.
    witness tau. apply andI.
    + prove tau :e alpha. exact Ha1 gamma Hc tau Ht.
    + witness p. prove PNo_rel_strict_split_imv L R tau p. exact H3.
}
apply ordinal_lim_or_succ alpha Ha.
- assume H1: forall beta :e alpha, ordsucc beta :e alpha.
  set pl : set -> prop := fun delta => forall p:set -> prop, PNo_rel_strict_imv L R (ordsucc delta) p -> p delta.
  claim Lpl1 : forall gamma, ordinal gamma -> gamma :e alpha -> PNo_rel_strict_uniq_imv L R gamma pl.
  { apply ordinal_ind.
    let gamma.
    assume Hc: ordinal gamma.
    assume IH2: forall delta :e gamma, delta :e alpha -> PNo_rel_strict_uniq_imv L R delta pl.
    assume Hc1: gamma :e alpha.
    apply LIH gamma Hc1.
    let p. assume Hp. apply Hp.
    assume Hp1: PNo_rel_strict_imv L R gamma p.
    apply Hp1. assume Hp1a Hp1b.
    assume Hp2: forall q:set -> prop, PNo_rel_strict_imv L R gamma q -> PNoEq_ gamma p q.
    claim Lplpe: PNoEq_ gamma pl p.
    { let delta. assume Hd: delta :e gamma.
      apply ordinal_ordsucc_In_eq gamma delta Hc Hd.
      - assume Hsd: ordsucc delta :e gamma.
        claim Lsda: ordsucc delta :e alpha.
        { exact Ha1 gamma Hc1 (ordsucc delta) Hsd. }
        apply IH2 (ordsucc delta) Hsd Lsda.
        assume Hpl1: PNo_rel_strict_imv L R (ordsucc delta) pl.
        assume Hpl2: forall q:set -> prop, PNo_rel_strict_imv L R (ordsucc delta) q -> PNoEq_ (ordsucc delta) pl q.
        prove pl delta <-> p delta.
        apply Hpl2 p.
        + prove PNo_rel_strict_imv L R (ordsucc delta) p.
          exact PNo_rel_strict_imv_antimon L R gamma Hc p (ordsucc delta) Hsd Hp1.
        + prove delta :e ordsucc delta. apply ordsuccI2.
      - assume Hsd: gamma = ordsucc delta.
        prove pl delta <-> p delta.
        apply iffI.
        + assume H2: pl delta.
          prove p delta.
          apply H2 p.
          prove PNo_rel_strict_imv L R (ordsucc delta) p.
          rewrite <- Hsd.
          exact Hp1.
        + assume H2: p delta.
          let q.
          rewrite <- Hsd.
          assume Hq: PNo_rel_strict_imv L R gamma q.
          prove q delta.
          exact iffEL (p delta) (q delta) (Hp2 q Hq delta Hd) H2.
    }
    prove PNo_rel_strict_uniq_imv L R gamma pl.
    prove PNo_rel_strict_imv L R gamma pl /\ forall q:set -> prop, PNo_rel_strict_imv L R gamma q -> PNoEq_ gamma pl q.
    apply andI.
    - prove PNo_rel_strict_imv L R gamma pl.
      prove PNo_rel_strict_upperbd L gamma pl /\ PNo_rel_strict_lowerbd R gamma pl.
      apply andI.
      + prove PNo_rel_strict_upperbd L gamma pl.
        let beta. assume Hb: beta :e gamma.
        let q. assume Hq: PNo_downc L beta q.
        claim Lb: ordinal beta.
        { exact ordinal_Hered gamma Hc beta Hb. }
        prove PNoLt beta q gamma pl.
        apply PNoLtEq_tra beta gamma Lb Hc q p pl.
        * prove PNoLt beta q gamma p. exact Hp1a beta Hb q Hq.
        * prove PNoEq_ gamma p pl. apply PNoEq_sym_. exact Lplpe.
      + prove PNo_rel_strict_lowerbd R gamma pl.
        let beta. assume Hb: beta :e gamma.
        let q. assume Hq: PNo_upc R beta q.
        claim Lb: ordinal beta.
        { exact ordinal_Hered gamma Hc beta Hb. }
        prove PNoLt gamma pl beta q.
        apply PNoEqLt_tra gamma beta Hc Lb pl p q.
        * prove PNoEq_ gamma pl p. exact Lplpe.
        * prove PNoLt gamma p beta q. exact Hp1b beta Hb q Hq.
    - prove forall q:set -> prop, PNo_rel_strict_imv L R gamma q -> PNoEq_ gamma pl q.
      let q.
      assume Hq: PNo_rel_strict_imv L R gamma q.
      prove PNoEq_ gamma pl q.
      apply PNoEq_tra_ gamma pl p q.
      + prove PNoEq_ gamma pl p. exact Lplpe.
      + prove PNoEq_ gamma p q. exact Hp2 q Hq.
  }
  claim Lpl2 : forall gamma :e alpha, PNo_rel_strict_uniq_imv L R gamma pl.
  { let gamma. assume Hc: gamma :e alpha.
    claim Lc: ordinal gamma.
    { exact ordinal_Hered alpha Ha gamma Hc. }
    exact Lpl1 gamma Lc Hc.
  }
  apply HNC1.
  witness pl.
  prove PNo_rel_strict_uniq_imv L R alpha pl.
  prove PNo_rel_strict_imv L R alpha pl /\ forall q:set -> prop, PNo_rel_strict_imv L R alpha q -> PNoEq_ alpha pl q.
  apply andI.
  + prove PNo_rel_strict_imv L R alpha pl.
    prove PNo_rel_strict_upperbd L alpha pl /\ PNo_rel_strict_lowerbd R alpha pl.
    apply andI.
    * { prove PNo_rel_strict_upperbd L alpha pl.
        let beta. assume Hb: beta :e alpha.
        let q. assume Hq: PNo_downc L beta q.
        claim Lb: ordinal beta.
        { exact ordinal_Hered alpha Ha beta Hb. }
        claim Lsb: ordinal (ordsucc beta).
        { exact ordinal_ordsucc beta Lb. }
        prove PNoLt beta q alpha pl.
        apply PNoLt_trichotomy_or beta alpha q pl Lb Ha. assume H2. apply H2.
        - assume H2: PNoLt beta q alpha pl. exact H2.
        - assume H2. apply H2. assume H2: beta = alpha. prove False.
          apply In_irref alpha. rewrite <- H2 at 1. exact Hb.
        - assume H2: PNoLt alpha pl beta q.
          apply PNoLtE alpha beta pl q H2.
          + assume H3: PNoLt_ (alpha :/\: beta) pl q.
            apply H3.
            let gamma. assume H4. apply H4.
            assume Hc: gamma :e alpha :/\: beta.
            apply binintersectE alpha beta gamma Hc.
            assume Hc1 Hc2.
            assume H5. apply H5. assume H5. apply H5.
            assume H5: PNoEq_ gamma pl q.
            assume H6: ~pl gamma.
            assume H7: q gamma.
            claim Lc: ordinal gamma.
            { exact ordinal_Hered beta Lb gamma Hc2. }
            claim Lsc: ordinal (ordsucc gamma).
            { exact ordinal_ordsucc gamma Lc. }
            prove False.
            apply H6.
            prove pl gamma.
            let p.
            assume Hp: PNo_rel_strict_imv L R (ordsucc gamma) p.
            prove p gamma.
            apply Hp. assume Hp1 Hp2.
            claim Lqp: PNoLt gamma q (ordsucc gamma) p.
            { apply Hp1 gamma (ordsuccI2 gamma) q.
              prove PNo_downc L gamma q.
              apply PNoLe_downc L beta gamma q q Lb Lc.
              - prove PNo_downc L beta q. exact Hq.
              - prove PNoLe gamma q beta q.
                apply PNoLeI1.
                prove PNoLt gamma q beta q.
                apply PNoLtI2.
                + prove gamma :e beta. exact Hc2.
                + prove PNoEq_ gamma q q. apply PNoEq_ref_.
                + prove q gamma. exact H7.
            }
            apply PNoLtE gamma (ordsucc gamma) q p Lqp.
            * assume H6: PNoLt_ (gamma :/\: ordsucc gamma) q p.
              apply H6.
              let delta. assume H7. apply H7.
              assume Hd: delta :e gamma :/\: ordsucc gamma.
              apply binintersectE gamma (ordsucc gamma) delta Hd.
              assume Hd1 Hd2.
              assume H7. apply H7. assume H7. apply H7.
              assume H7: PNoEq_ delta q p.
              assume H8: ~q delta.
              assume H9: p delta.
              claim Ld: ordinal delta.
              { exact ordinal_Hered gamma Lc delta Hd1. }
              claim Lda: delta :e alpha.
              { exact Ha1 gamma Hc1 delta Hd1. }
              claim Lsda: ordsucc delta :e alpha.
              { exact H1 delta Lda. }
              claim Lpld: pl delta.
              { apply Lpl2 (ordsucc delta) Lsda.
                assume _.
                assume Hpl3: forall q:set -> prop, PNo_rel_strict_imv L R (ordsucc delta) q -> PNoEq_ (ordsucc delta) pl q.
                claim Lpld1: PNoEq_ (ordsucc delta) pl p.
                { apply Hpl3 p.
                  prove PNo_rel_strict_imv L R (ordsucc delta) p.
                  apply PNo_rel_strict_imv_antimon L R (ordsucc gamma) Lsc p.
                  - prove ordsucc delta :e ordsucc gamma.
                    apply ordinal_ordsucc_In.
                    + exact Lc.
                    + prove delta :e gamma.
                      exact Hd1.
                  - exact Hp.
                }
                exact iffER (pl delta) (p delta) (Lpld1 delta (ordsuccI2 delta)) H9.
              }
              claim Lnpld: ~pl delta.
              { assume H10: pl delta.
                apply H8.
                exact iffEL (pl delta) (q delta) (H5 delta Hd1) H10.
              }
              prove False. exact Lnpld Lpld.
            * assume H6: gamma :e ordsucc gamma.
              assume H7: PNoEq_ gamma q p.
              assume H8: p gamma.
              exact H8.
            * assume H6: ordsucc gamma :e gamma.
              prove False.
              exact In_no2cycle gamma (ordsucc gamma) (ordsuccI2 gamma) H6.
          + assume H3: alpha :e beta. prove False.
            exact In_no2cycle beta alpha Hb H3.
          + assume H3: beta :e alpha.
            assume H4: PNoEq_ beta pl q.
            assume H5: ~pl beta.
            prove False.
            apply H5.
            prove pl beta.
            let p.
            assume Hp: PNo_rel_strict_imv L R (ordsucc beta) p.
            prove p beta.
            apply Hp. assume Hp1 Hp2.
            claim Lqp: PNoLt beta q (ordsucc beta) p.
            { exact Hp1 beta (ordsuccI2 beta) q Hq. }
            apply PNoLtE beta (ordsucc beta) q p Lqp.
            * assume H6: PNoLt_ (beta :/\: ordsucc beta) q p.
              apply H6.
              let delta. assume H7. apply H7.
              assume Hd: delta :e beta :/\: ordsucc beta.
              apply binintersectE beta (ordsucc beta) delta Hd.
              assume Hd1 Hd2.
              assume H7. apply H7. assume H7. apply H7.
              assume H7: PNoEq_ delta q p.
              assume H8: ~q delta.
              assume H9: p delta.
              claim Ld: ordinal delta.
              { exact ordinal_Hered beta Lb delta Hd1. }
              claim Lda: delta :e alpha.
              { exact Ha1 beta Hb delta Hd1. }
              claim Lsda: ordsucc delta :e alpha.
              { exact H1 delta Lda. }
              claim Lpld: pl delta.
              { apply Lpl2 (ordsucc delta) Lsda.
                assume _.
                assume Hpl3: forall q:set -> prop, PNo_rel_strict_imv L R (ordsucc delta) q -> PNoEq_ (ordsucc delta) pl q.
                claim Lpld1: PNoEq_ (ordsucc delta) pl p.
                { apply Hpl3 p.
                  prove PNo_rel_strict_imv L R (ordsucc delta) p.
                  apply PNo_rel_strict_imv_antimon L R (ordsucc beta) Lsb p.
                  - prove ordsucc delta :e ordsucc beta.
                    apply ordinal_ordsucc_In.
                    + exact Lb.
                    + prove delta :e beta.
                      exact Hd1.
                  - exact Hp.
                }
                exact iffER (pl delta) (p delta) (Lpld1 delta (ordsuccI2 delta)) H9.
              }
              claim Lnpld: ~pl delta.
              { assume H10: pl delta.
                apply H8.
                exact iffEL (pl delta) (q delta) (H4 delta Hd1) H10.
              }
              prove False. exact Lnpld Lpld.
            * assume H6: beta :e ordsucc beta.
              assume H7: PNoEq_ beta q p.
              assume H8: p beta.
              exact H8.
            * assume H6: ordsucc beta :e beta.
              prove False.
              exact In_no2cycle beta (ordsucc beta) (ordsuccI2 beta) H6.
      }
    * { prove PNo_rel_strict_lowerbd R alpha pl.
        let beta. assume Hb: beta :e alpha.
        let q. assume Hq: PNo_upc R beta q.
        claim Lb: ordinal beta.
        { exact ordinal_Hered alpha Ha beta Hb. }
        claim Lsb: ordinal (ordsucc beta).
        { exact ordinal_ordsucc beta Lb. }
        claim Lsba: ordsucc beta :e alpha.
        { exact H1 beta Hb. }
        prove PNoLt alpha pl beta q.
        apply PNoLt_trichotomy_or alpha beta pl q Ha Lb. assume H2. apply H2.
        - assume H2: PNoLt alpha pl beta q. exact H2.
        - assume H2. apply H2. assume H2: alpha = beta. prove False.
          apply In_irref alpha. rewrite H2 at 1. exact Hb.
        - assume H2: PNoLt beta q alpha pl.
          apply PNoLtE beta alpha q pl H2.
          + assume H3: PNoLt_ (beta :/\: alpha) q pl.
            apply H3.
            let gamma. assume H4. apply H4.
            assume Hc: gamma :e beta :/\: alpha.
            apply binintersectE beta alpha gamma Hc.
            assume Hc2 Hc1.
            assume H5. apply H5. assume H5. apply H5.
            assume H5: PNoEq_ gamma q pl.
            assume H6: ~q gamma.
            assume H7: pl gamma.
            claim Lc: ordinal gamma.
            { exact ordinal_Hered beta Lb gamma Hc2. }
            claim Lsc: ordinal (ordsucc gamma).
            { exact ordinal_ordsucc gamma Lc. }
            claim Lsca: ordsucc gamma :e alpha.
            { exact H1 gamma Hc1. }
            prove False.
            apply Lpl2 (ordsucc gamma) Lsca.
            assume Hpl2: PNo_rel_strict_imv L R (ordsucc gamma) pl.
            assume _.
            apply Hpl2.
            assume _.
            assume Hpl2b: PNo_rel_strict_lowerbd R (ordsucc gamma) pl.
            claim Lplq: PNoLt (ordsucc gamma) pl gamma q.
            { apply Hpl2b gamma (ordsuccI2 gamma) q.
              prove PNo_upc R gamma q.
              apply PNoLe_upc R beta gamma q q Lb Lc.
              - prove PNo_upc R beta q. exact Hq.
              - prove PNoLe beta q gamma q.
                apply PNoLeI1 beta gamma q q.
                prove PNoLt beta q gamma q.
                apply PNoLtI3.
                + prove gamma :e beta. exact Hc2.
                + prove PNoEq_ gamma q q. apply PNoEq_ref_.
                + prove ~q gamma. exact H6.
            }
            claim Lqpl: PNoLt gamma q (ordsucc gamma) pl.
            { apply PNoLtI2.
              - prove gamma :e ordsucc gamma. apply ordsuccI2.
              - prove PNoEq_ gamma q pl. exact H5.
              - prove pl gamma. exact H7.
            }
            prove False.
            apply PNoLt_irref gamma q.
            exact PNoLt_tra gamma (ordsucc gamma) gamma Lc Lsc Lc q pl q Lqpl Lplq.
          + assume H3: beta :e alpha.
            assume H4: PNoEq_ beta q pl.
            assume H5: pl beta.
            apply Lpl2 (ordsucc beta) Lsba.
            assume Hpl2: PNo_rel_strict_imv L R (ordsucc beta) pl.
            assume _.
            apply Hpl2.
            assume _.
            assume Hpl2b: PNo_rel_strict_lowerbd R (ordsucc beta) pl.
            claim Lplq: PNoLt (ordsucc beta) pl beta q.
            { apply Hpl2b beta (ordsuccI2 beta) q.
              prove PNo_upc R beta q.
              exact Hq.
            }
            claim Lqpl: PNoLt beta q (ordsucc beta) pl.
            { apply PNoLtI2.
              - prove beta :e ordsucc beta. apply ordsuccI2.
              - prove PNoEq_ beta q pl. exact H4.
              - prove pl beta. exact H5.
            }
            prove False.
            apply PNoLt_irref beta q.
            exact PNoLt_tra beta (ordsucc beta) beta Lb Lsb Lb q pl q Lqpl Lplq.
          + assume H3: alpha :e beta. prove False.
            exact In_no2cycle beta alpha Hb H3.
      }
  + prove forall q:set -> prop, PNo_rel_strict_imv L R alpha q -> PNoEq_ alpha pl q.
    let q.
    assume Hq: PNo_rel_strict_imv L R alpha q.
    let gamma.
    assume Hc: gamma :e alpha.
    prove pl gamma <-> q gamma.
    claim Lsca: ordsucc gamma :e alpha.
    { exact H1 gamma Hc. }
    apply Lpl2 (ordsucc gamma) Lsca.
    assume _.
    assume Hpl3: forall q:set -> prop, PNo_rel_strict_imv L R (ordsucc gamma) q -> PNoEq_ (ordsucc gamma) pl q.
    apply Hpl3.
    * prove PNo_rel_strict_imv L R (ordsucc gamma) q.
      exact PNo_rel_strict_imv_antimon L R alpha Ha q (ordsucc gamma) Lsca Hq.
    * prove gamma :e ordsucc gamma. apply ordsuccI2.
- assume H1: exists beta :e alpha, alpha = ordsucc beta.
  apply H1.
  let beta. assume H1. apply H1.
  assume Hb: beta :e alpha.
  assume Hab: alpha = ordsucc beta.
  claim Lb: ordinal beta.
  { exact ordinal_Hered alpha Ha beta Hb. }
  claim Lsb: ordinal (ordsucc beta).
  { rewrite <- Hab. exact Ha. }
  claim Lbsb1: beta :/\: ordsucc beta = beta.
  { apply binintersect_Subq_eq_1. apply ordsuccI1. }
  claim Lbsb2: ordsucc beta :/\: beta = beta.
  { rewrite binintersect_com. exact Lbsb1. }
  apply LIH beta Hb.
  let p.
  assume Hp: PNo_rel_strict_uniq_imv L R beta p.
  apply Hp.
  assume Hp0: PNo_rel_strict_imv L R beta p.
  apply Hp0.
  assume Hp1: forall gamma :e beta, forall q:set -> prop, PNo_downc L gamma q -> PNoLt gamma q beta p.
  assume Hp2: forall gamma :e beta, forall q:set -> prop, PNo_upc R gamma q -> PNoLt beta p gamma q.
  assume Hp3: forall q:set -> prop, PNo_rel_strict_imv L R beta q -> PNoEq_ beta p q.
  set p0 : set -> prop := fun delta => p delta /\ delta <> beta.
  set p1 : set -> prop := fun delta => p delta \/ delta = beta.
  claim Lp0e: PNoEq_ beta p0 p.
  { let gamma. assume Hc: gamma :e beta.
    prove p0 gamma <-> p gamma.
    apply iffI.
    - assume H2: p gamma /\ gamma <> beta. prove p gamma. apply H2. assume H2 _. exact H2.
    - assume H2: p gamma. prove p gamma /\ gamma <> beta. apply andI.
      + exact H2.
      + assume H3: gamma = beta. apply In_irref beta. rewrite <- H3 at 1. exact Hc.
  }
  claim Lp0b: ~p0 beta.
  { assume H2: p beta /\ beta <> beta. apply H2. assume _ H2. apply H2. reflexivity. }
  claim Lp0p: PNoLt (ordsucc beta) p0 beta p.
  { apply PNoLtI3.
    - prove beta :e ordsucc beta. apply ordsuccI2.
    - prove PNoEq_ beta p0 p. exact Lp0e.
    - prove ~p0 beta. exact Lp0b.
  }
  claim Lp1e: PNoEq_ beta p p1.
  { let gamma. assume Hc: gamma :e beta.
    prove p gamma <-> p1 gamma.
    apply iffI.
    - assume H2: p gamma. prove p gamma \/ gamma = beta. apply orIL. exact H2.
    - assume H2: p gamma \/ gamma = beta. prove p gamma. apply H2.
      + assume H3: p gamma. exact H3.
      + assume H3: gamma = beta. prove False. apply In_irref beta. rewrite <- H3 at 1. exact Hc.
  }
  claim Lp1b: p1 beta.
  { prove p beta \/ beta = beta. apply orIR. reflexivity. }
  claim Lpp1: PNoLt beta p (ordsucc beta) p1.
  { apply PNoLtI2.
    - prove beta :e ordsucc beta. apply ordsuccI2.
    - prove PNoEq_ beta p p1. exact Lp1e.
    - prove p1 beta. exact Lp1b.
  }
  claim Lnotboth: ~(PNo_rel_strict_imv L R alpha p0 /\ PNo_rel_strict_imv L R alpha p1).
  { rewrite Hab. assume H2.
    apply HNC2. witness beta. apply andI.
    - prove beta :e alpha. exact Hb.
    - witness p.
      prove PNo_rel_strict_split_imv L R beta p.
      exact H2.
  }
  claim Lcases : (forall q:set -> prop, PNo_downc L beta q -> ~PNoEq_ beta p q)
              \/ (forall q:set -> prop, PNo_upc R beta q -> ~PNoEq_ beta p q).
  {  rewrite eq_or_nand.
     assume H2. apply H2.
     assume H2: ~(forall q:set -> prop, PNo_downc L beta q -> ~PNoEq_ beta p q).
     assume H3: ~(forall q:set -> prop, PNo_upc R beta q -> ~PNoEq_ beta p q).
     apply H2.
     let q0.
     assume H4: PNo_downc L beta q0.
     assume H5: PNoEq_ beta p q0.
     apply H3.
     let q1.
     assume H6: PNo_upc R beta q1.
     assume H7: PNoEq_ beta p q1.
     claim L2: PNoLt beta q0 beta q1.
     { exact LLR beta Lb q0 H4 beta Lb q1 H6. }
     apply PNoLt_irref beta q0.
     apply PNoLtLe_tra beta beta beta Lb Lb Lb q0 q1 q0 L2.
     prove PNoLe beta q1 beta q0.
     prove PNoLt beta q1 beta q0 \/ beta = beta /\ PNoEq_ beta q1 q0.
     apply orIR.
     apply andI.
     - reflexivity.
     - prove PNoEq_ beta q1 q0. apply PNoEq_tra_ beta q1 p q0.      
       + prove PNoEq_ beta q1 p. apply PNoEq_sym_. exact H7.
       + prove PNoEq_ beta p q0. exact H5.
  }
  prove False.
  apply Lcases.
  + assume H2: forall q:set -> prop, PNo_downc L beta q -> ~PNoEq_ beta p q.
    claim Lp0imv: PNo_rel_strict_imv L R (ordsucc beta) p0.
    { prove PNo_rel_strict_upperbd L (ordsucc beta) p0
         /\ PNo_rel_strict_lowerbd R (ordsucc beta) p0.
      apply andI.
      - let gamma. assume Hc: gamma :e ordsucc beta. let q.
        assume H3: PNo_downc L gamma q.
        claim Lc: ordinal gamma.
        { exact ordinal_Hered (ordsucc beta) Lsb gamma Hc. }
        prove PNoLt gamma q (ordsucc beta) p0.
        apply ordsuccE beta gamma Hc.
        + assume H4: gamma :e beta.
          claim L1: PNoLt gamma q beta p.
          { exact Hp1 gamma H4 q H3. }
          apply PNoLtE gamma beta q p L1.
          * { assume H5: PNoLt_ (gamma :/\: beta) q p.
              apply H5.
              let delta. assume H6. apply H6.
              assume Hd: delta :e gamma :/\: beta.
              assume H6. apply H6. assume H6. apply H6.
              assume H6: PNoEq_ delta q p.
              assume H7: ~q delta.
              assume H8: p delta.
              apply binintersectE gamma beta delta Hd.
              assume Hd1: delta :e gamma.
              assume Hd2: delta :e beta.
              prove PNoLt gamma q (ordsucc beta) p0.
              apply PNoLtI1.
              prove PNoLt_ (gamma :/\: ordsucc beta) q p0.
              prove exists beta :e gamma :/\: ordsucc beta, PNoEq_ beta q p0 /\ ~q beta /\ p0 beta.
              witness delta.
              apply andI.
              - prove delta :e gamma :/\: ordsucc beta. apply binintersectI.
                + exact Hd1.
                + apply ordsuccI1. exact Hd2.
              - apply and3I.
                + prove PNoEq_ delta q p0. apply PNoEq_tra_ delta q p p0.
                  * exact H6.
                  * apply PNoEq_sym_.
                    apply PNoEq_antimon_ p0 p beta Lb delta Hd2.
                    exact Lp0e.
                + prove ~q delta. exact H7.
                + prove p0 delta.
                  prove p delta /\ delta <> beta.
                  apply andI.
                  * exact H8.
                  * assume H9: delta = beta.
                    apply In_irref beta.
                    rewrite <- H9 at 1. exact Hd2.
            }
          * { assume H5: gamma :e beta.
              assume H6: PNoEq_ gamma q p.
              assume H7: p gamma.
              prove PNoLt gamma q (ordsucc beta) p0.
              apply PNoLtI2.
              - prove gamma :e ordsucc beta. apply ordsuccI1. exact H5.
              - prove PNoEq_ gamma q p0.
                apply PNoEq_tra_ gamma q p p0.
                + prove PNoEq_ gamma q p. exact H6.
                + prove PNoEq_ gamma p p0. apply PNoEq_sym_.
                  apply PNoEq_antimon_ p0 p beta Lb gamma H5.
                  exact Lp0e.
              - prove p0 gamma.
                prove p gamma /\ gamma <> beta.
                apply andI.
                + exact H7.
                + assume H8: gamma = beta. apply In_irref gamma. rewrite H8 at 2. exact H5.
            }
          * assume H5: beta :e gamma.
            prove False.
            exact In_no2cycle gamma beta H4 H5.
        + assume H4: gamma = beta.
          rewrite H4.
          prove PNoLt beta q (ordsucc beta) p0.
          apply PNoLt_trichotomy_or beta (ordsucc beta) q p0 Lb Lsb. assume H5. apply H5.
          * assume H5. exact H5.
          * assume H5. apply H5. assume H5: beta = ordsucc beta. prove False.
            apply In_irref beta. rewrite H5 at 2. apply ordsuccI2.
          * { assume H5: PNoLt (ordsucc beta) p0 beta q.
              apply PNoLtE (ordsucc beta) beta p0 q H5.
              - rewrite Lbsb2.
                assume H6: PNoLt_ beta p0 q.
                apply H6.
                let delta. assume H7. apply H7.
                assume Hd: delta :e beta.
                assume H7. apply H7. assume H7. apply H7.
                assume H7: PNoEq_ delta p0 q.
                assume H8: ~p0 delta.
                assume H9: q delta.
                claim Ld: ordinal delta.
                { exact ordinal_Hered beta Lb delta Hd. }
                claim L2: PNoLt beta p delta q.
                { apply PNoLtI3.
                  - prove delta :e beta. exact Hd.
                  - prove PNoEq_ delta p q. apply PNoEq_tra_ delta p p0 q.
                    + prove PNoEq_ delta p p0. apply PNoEq_sym_.
                      apply PNoEq_antimon_ p0 p beta Lb delta Hd.
                      exact Lp0e.
                    + prove PNoEq_ delta p0 q. exact H7.
                  - prove ~p delta.
                    assume H10: p delta.
                    apply H8.
                    prove p delta /\ delta <> beta.
                    apply andI.
                    + exact H10.
                    + assume H11: delta = beta. apply In_irref beta. rewrite <- H11 at 1.
                      exact Hd.
                }
                claim L3: PNoLt delta q beta p.
                { apply Hp1 delta Hd q.
                  prove PNo_downc L delta q. (** This is where I need to use PNo_downc L instead of just L since all I know is PNo_downc L gamma q where gamma=beta here. **)
                  apply PNoLe_downc L gamma delta q q Lc Ld H3.
                  prove PNoLe delta q gamma q.
                  apply PNoLeI1.
                  prove PNoLt delta q gamma q.
                  apply PNoLtI2.
                  - prove delta :e gamma. rewrite H4. exact Hd.
                  - prove PNoEq_ delta q q. apply PNoEq_ref_.
                  - prove q delta. exact H9.
                }
              apply PNoLt_irref delta q.
              prove PNoLt delta q delta q.
              exact PNoLt_tra delta beta delta Ld Lb Ld q p q L3 L2.
              - assume H6: ordsucc beta :e beta. prove False.
                apply In_no2cycle (ordsucc beta) beta H6.
                apply ordsuccI2.
              - assume H6: beta :e ordsucc beta.
                assume H7: PNoEq_ beta p0 q.
                prove False.
                apply H2 q.
                + prove PNo_downc L beta q.
                  rewrite <- H4.
                  exact H3.
                + prove PNoEq_ beta p q.
                  apply PNoEq_tra_ beta p p0 q.
                  * apply PNoEq_sym_. exact Lp0e.
                  * exact H7.
            }
      - let gamma. assume Hc: gamma :e ordsucc beta. let q.
        assume H3: PNo_upc R gamma q.
        claim Lc: ordinal gamma.
        { exact ordinal_Hered (ordsucc beta) Lsb gamma Hc. }
        prove PNoLt (ordsucc beta) p0 gamma q.
        apply ordsuccE beta gamma Hc.
        + assume H4: gamma :e beta.
          apply PNoLt_tra (ordsucc beta) beta gamma Lsb Lb Lc p0 p q Lp0p.
          prove PNoLt beta p gamma q.
          apply Hp2 gamma H4 q.
          prove PNo_upc R gamma q.
          exact H3.
        + assume H4: gamma = beta.
          rewrite H4.
          prove PNoLt (ordsucc beta) p0 beta q.
          apply PNoLt_trichotomy_or beta (ordsucc beta) q p0 Lb Lsb. assume H5. apply H5.
          * { assume H5: PNoLt beta q (ordsucc beta) p0.
              apply PNoLtE beta (ordsucc beta) q p0 H5.
              - rewrite Lbsb1.
                assume H6: PNoLt_ beta q p0.
                apply H6.
                let delta.
                assume H7. apply H7.
                assume H8: delta :e beta.
                assume H9. apply H9. assume H9. apply H9.
                assume H9: PNoEq_ delta q p0.
                assume H10: ~q delta.
                assume H11: p0 delta.
                prove False.
                claim Ld: ordinal delta.
                { exact ordinal_Hered beta Lb delta H8. }
                claim L4: PNoLt beta p delta q.
                { apply Hp2 delta H8 q.
                  prove PNo_upc R delta q. (** Using PNo_upc R instead of R in an apparently important way. **)
                  apply PNoLe_upc R gamma delta q q Lc Ld H3.
                  prove PNoLe gamma q delta q.
                  apply PNoLeI1.
                  prove PNoLt gamma q delta q.
                  apply PNoLtI3.
                  - prove delta :e gamma. rewrite H4. exact H8.
                  - prove PNoEq_ delta q q. apply PNoEq_ref_.
                  - prove ~q delta. exact H10.
                }
                claim L5: PNoLt delta q beta p.
                { apply PNoLtI2.
                  - prove delta :e beta. exact H8.
                  - prove PNoEq_ delta q p. apply PNoEq_tra_ delta q p0 p.
                    + exact H9.
                    + prove PNoEq_ delta p0 p.
                      apply PNoEq_antimon_ p0 p beta Lb delta H8.
                      exact Lp0e.
                  - prove p delta. apply H11. assume H12 _. exact H12.
                }
                apply PNoLt_irref beta p.
                exact PNoLt_tra beta delta beta Lb Ld Lb p q p L4 L5.
              - assume H6: beta :e ordsucc beta.
                assume H7: PNoEq_ beta q p0.
                assume H8: p beta /\ beta <> beta.
                prove False.
                apply H8. assume _ H9. apply H9. reflexivity.
              - assume H6: ordsucc beta :e beta.
                prove False.
                apply In_no2cycle (ordsucc beta) beta H6.
                apply ordsuccI2.
            }
          * assume H5. apply H5. assume H5: beta = ordsucc beta.
            prove False.
            apply In_irref beta.
            rewrite H5 at 2.
            apply ordsuccI2.
          * assume H5: PNoLt (ordsucc beta) p0 beta q. exact H5.
    }
    apply HNC1.
    witness p0.
    rewrite Hab.
    prove PNo_rel_strict_uniq_imv L R (ordsucc beta) p0.
    prove PNo_rel_strict_imv L R (ordsucc beta) p0
       /\ forall q:set -> prop, PNo_rel_strict_imv L R (ordsucc beta) q -> PNoEq_ (ordsucc beta) p0 q.
    apply andI.
    * exact Lp0imv.
    * { let q. assume Hq: PNo_rel_strict_imv L R (ordsucc beta) q.
        prove PNoEq_ (ordsucc beta) p0 q.
        claim Lqb: PNo_rel_strict_imv L R beta q.
        { exact PNo_rel_strict_imv_antimon L R (ordsucc beta) Lsb q beta (ordsuccI2 beta) Hq. }
        claim Lpqe: PNoEq_ beta p q.
        { exact Hp3 q Lqb. }
        apply xm (q beta).
        - assume Hq1: q beta.
          prove False.
          apply Lnotboth. rewrite Hab.
          apply andI.
          + prove PNo_rel_strict_imv L R (ordsucc beta) p0. exact Lp0imv.
          + prove PNo_rel_strict_imv L R (ordsucc beta) p1.
            apply PNoEq_rel_strict_imv L R (ordsucc beta) Lsb q p1.
            * { prove PNoEq_ (ordsucc beta) q p1.
                let gamma. assume Hc: gamma :e ordsucc beta.
                apply ordsuccE beta gamma Hc.
                - assume H3: gamma :e beta.
                  claim Lpqce: p gamma <-> q gamma.
                  { exact Lpqe gamma H3. }
                  apply Lpqce. assume Hpqc Hqpc.
                  prove q gamma <-> p1 gamma.
                  apply iffI.
                  + assume H4: q gamma.
                    prove p gamma \/ gamma = beta.
                    apply orIL.
                    exact Hqpc H4.
                  + assume H4: p gamma \/ gamma = beta.
                    apply H4.
                    * exact Hpqc.
                    * assume H5: gamma = beta. prove False.
                      apply In_irref beta. rewrite <- H5 at 1. exact H3.
                - assume H3: gamma = beta.
                  prove q gamma <-> p1 gamma.
                  apply iffI.
                  + assume _.
                    prove p gamma \/ gamma = beta.
                    apply orIR. exact H3.
                  + assume _.
                    prove q gamma. rewrite H3. exact Hq1.
              }
            * prove PNo_rel_strict_imv L R (ordsucc beta) q. exact Hq.
        - assume Hq0: ~ q beta.
          prove PNoEq_ (ordsucc beta) p0 q.
          let gamma. assume Hc: gamma :e ordsucc beta.
          apply ordsuccE beta gamma Hc.
          + assume H3: gamma :e beta.
            claim Lpqce: p gamma <-> q gamma.
            { exact Lpqe gamma H3. }
            apply Lpqce. assume Hpqc Hqpc.
            prove p0 gamma <-> q gamma.
            apply iffI.
            * { assume H4: p gamma /\ gamma <> beta.
                apply H4.
                assume H5: p gamma.
                assume _. exact Hpqc H5.
              }
            * { assume H4: q gamma.
                prove p gamma /\ gamma <> beta.
                apply andI.
                - prove p gamma. exact Hqpc H4.
                - prove gamma <> beta. assume H5: gamma = beta.
                  apply In_irref beta. rewrite <- H5 at 1. exact H3.
              }
          + assume H3: gamma = beta.
            prove p0 gamma <-> q gamma.
            apply iffI.
            * assume H4: p gamma /\ gamma <> beta.
              apply H4. assume _ H5. prove False. exact H5 H3.
            * assume H4: q gamma. prove False. apply Hq0.
              prove q beta. rewrite <- H3. exact H4.
      }
  + assume H2: forall q:set -> prop, PNo_upc R beta q -> ~PNoEq_ beta p q.
    claim Lp1imv: PNo_rel_strict_imv L R (ordsucc beta) p1.
    { prove PNo_rel_strict_upperbd L (ordsucc beta) p1
         /\ PNo_rel_strict_lowerbd R (ordsucc beta) p1.
      apply andI.
      - let gamma. assume Hc: gamma :e ordsucc beta. let q.
        assume H3: PNo_downc L gamma q.
        claim Lc: ordinal gamma.
        { exact ordinal_Hered (ordsucc beta) Lsb gamma Hc. }
        prove PNoLt gamma q (ordsucc beta) p1.
        apply ordsuccE beta gamma Hc.
        + assume H4: gamma :e beta.
          apply PNoLt_tra gamma beta (ordsucc beta) Lc Lb Lsb q p p1.
          * prove PNoLt gamma q beta p.
            apply Hp1 gamma H4 q.
            prove PNo_downc L gamma q.
            exact H3.
          * exact Lpp1.
        + assume H4: gamma = beta.
          rewrite H4.
          prove PNoLt beta q (ordsucc beta) p1.
          apply PNoLt_trichotomy_or beta (ordsucc beta) q p1 Lb Lsb. assume H5. apply H5.
          * assume H5: PNoLt beta q (ordsucc beta) p1. exact H5.
          * assume H5. apply H5. assume H5: beta = ordsucc beta.
            prove False.
            apply In_irref beta.
            rewrite H5 at 2.
            apply ordsuccI2.
          * { assume H5: PNoLt (ordsucc beta) p1 beta q.
              apply PNoLtE (ordsucc beta) beta p1 q H5.
              - rewrite Lbsb2.
                assume H6: PNoLt_ beta p1 q.
                apply H6.
                let delta.
                assume H7. apply H7.
                assume H8: delta :e beta.
                assume H9. apply H9. assume H9. apply H9.
                assume H9: PNoEq_ delta p1 q.
                assume H10: ~p1 delta.
                assume H11: q delta.
                prove False.
                claim Ld: ordinal delta.
                { exact ordinal_Hered beta Lb delta H8. }
                claim L4: PNoLt delta q beta p.
                { apply Hp1 delta H8 q.
                  prove PNo_downc L delta q. (** Using PNo_downc L instead of L in an apparently important way. **)
                  apply PNoLe_downc L gamma delta q q Lc Ld H3.
                  prove PNoLe delta q gamma q.
                  apply PNoLeI1.
                  prove PNoLt delta q gamma q.
                  apply PNoLtI2.
                  - prove delta :e gamma. rewrite H4. exact H8.
                  - prove PNoEq_ delta q q. apply PNoEq_ref_.
                  - prove q delta. exact H11.
                }
                claim L5: PNoLt beta p delta q.
                { apply PNoLtI3.
                  - prove delta :e beta. exact H8.
                  - prove PNoEq_ delta p q. apply PNoEq_tra_ delta p p1 q.
                    + prove PNoEq_ delta p p1.
                      apply PNoEq_antimon_ p p1 beta Lb delta H8.
                      exact Lp1e.
                    + exact H9.
                  - prove ~p delta. 
                    assume H12: p delta.
                    apply H10.
                    prove p delta \/ delta = beta.
                    apply orIL. exact H12.
                }
                apply PNoLt_irref beta p.
                exact PNoLt_tra beta delta beta Lb Ld Lb p q p L5 L4.
              - assume H6: ordsucc beta :e beta.
                prove False.
                apply In_no2cycle (ordsucc beta) beta H6.
                apply ordsuccI2.
              - assume H6: beta :e ordsucc beta.
                assume H7: PNoEq_ beta p1 q.
                assume H8: ~p1 beta.
                prove False.
                apply H8.
                prove p beta \/ beta = beta.
                apply orIR. reflexivity.
            }
      - let gamma. assume Hc: gamma :e ordsucc beta. let q.
        assume H3: PNo_upc R gamma q.
        claim Lc: ordinal gamma.
        { exact ordinal_Hered (ordsucc beta) Lsb gamma Hc. }
        prove PNoLt (ordsucc beta) p1 gamma q.
        apply ordsuccE beta gamma Hc.
        + assume H4: gamma :e beta.
          claim L1: PNoLt beta p gamma q.
          { exact Hp2 gamma H4 q H3. }
          apply PNoLtE beta gamma p q L1.
          * { assume H5: PNoLt_ (beta :/\: gamma) p q.
              apply H5.
              let delta. assume H6. apply H6.
              assume Hd: delta :e beta :/\: gamma.
              assume H6. apply H6. assume H6. apply H6.
              assume H6: PNoEq_ delta p q.
              assume H7: ~p delta.
              assume H8: q delta.
              apply binintersectE beta gamma delta Hd.
              assume Hd2: delta :e beta.
              assume Hd1: delta :e gamma.
              prove PNoLt (ordsucc beta) p1 gamma q.
              apply PNoLtI1.
              prove PNoLt_ (ordsucc beta :/\: gamma) p1 q.
              prove exists beta :e ordsucc beta :/\: gamma, PNoEq_ beta p1 q /\ ~p1 beta /\ q beta.
              witness delta.
              apply andI.
              - prove delta :e ordsucc beta :/\: gamma. apply binintersectI.
                + apply ordsuccI1. exact Hd2.
                + exact Hd1.
              - apply and3I.
                + prove PNoEq_ delta p1 q. apply PNoEq_tra_ delta p1 p q.
                  * apply PNoEq_antimon_ p1 p beta Lb delta Hd2.
                    apply PNoEq_sym_.
                    exact Lp1e.
                  * exact H6.
                + prove ~p1 delta.
                  assume H9: p delta \/ delta = beta.
                  prove False.
                  apply H9.
                  * exact H7.
                  * assume H10: delta = beta.
                    apply In_irref beta. rewrite <- H10 at 1. exact Hd2.
                + prove q delta. exact H8.
            }
          * assume H5: beta :e gamma.
            prove False.
            exact In_no2cycle gamma beta H4 H5.
          * { assume H5: gamma :e beta.
              assume H6: PNoEq_ gamma p q. 
              assume H7: ~p gamma.
              prove PNoLt (ordsucc beta) p1 gamma q.
              apply PNoLtI3.
              - prove gamma :e ordsucc beta. apply ordsuccI1. exact H5.
              - prove PNoEq_ gamma p1 q.
                apply PNoEq_tra_ gamma p1 p q.
                + prove PNoEq_ gamma p1 p.
                  apply PNoEq_antimon_ p1 p beta Lb gamma H5.
                  apply PNoEq_sym_.
                  exact Lp1e.
                + prove PNoEq_ gamma p q. exact H6.
              - prove ~p1 gamma.
                assume H8: p gamma \/ gamma = beta.
                apply H8.
                + exact H7.
                + assume H9: gamma = beta.
                  apply In_irref beta.
                  rewrite <- H9 at 1.
                  exact H5.
            }
        + assume H4: gamma = beta.
          rewrite H4.
          prove PNoLt (ordsucc beta) p1 beta q.
          apply PNoLt_trichotomy_or beta (ordsucc beta) q p1 Lb Lsb. assume H5. apply H5.
          * { assume H5: PNoLt beta q (ordsucc beta) p1.
              apply PNoLtE beta (ordsucc beta) q p1 H5.
              - rewrite Lbsb1.
                assume H6: PNoLt_ beta q p1.
                apply H6.
                let delta. assume H7. apply H7.
                assume Hd: delta :e beta.
                assume H7. apply H7. assume H7. apply H7.
                assume H7: PNoEq_ delta q p1.
                assume H8: ~q delta.
                assume H9: p1 delta.
                claim Ld: ordinal delta.
                { exact ordinal_Hered beta Lb delta Hd. }
                claim L2: PNoLt delta q beta p.
                { apply PNoLtI2.
                  - prove delta :e beta. exact Hd.
                  - prove PNoEq_ delta q p. apply PNoEq_tra_ delta q p1 p.
                    + prove PNoEq_ delta q p1. exact H7.
                    + prove PNoEq_ delta p1 p.
                      apply PNoEq_antimon_ p1 p beta Lb delta Hd.
                      apply PNoEq_sym_.
                      exact Lp1e.
                  - prove p delta.
                    apply H9.
                    + assume H10: p delta. exact H10.
                    + assume H10: delta = beta. prove False.
                      apply In_irref beta. rewrite <- H10 at 1. exact Hd.
                }
                claim L3: PNoLt beta p delta q.
                { apply Hp2 delta Hd q.
                  prove PNo_upc R delta q. (** This is where I need to use PNo_upc R instead of just R since all I know is PNo_upc R gamma q where gamma=beta here. **)
                  apply PNoLe_upc R gamma delta q q Lc Ld H3.
                  prove PNoLe gamma q delta q.
                  apply PNoLeI1.
                  prove PNoLt gamma q delta q.
                  apply PNoLtI3.
                  - prove delta :e gamma. rewrite H4. exact Hd.
                  - prove PNoEq_ delta q q. apply PNoEq_ref_.
                  - prove ~q delta. exact H8.
                }
              apply PNoLt_irref delta q.
              prove PNoLt delta q delta q.
              exact PNoLt_tra delta beta delta Ld Lb Ld q p q L2 L3.
              - assume H6: beta :e ordsucc beta.
                assume H7: PNoEq_ beta q p1.
                prove False.
                apply H2 q.
                + prove PNo_upc R beta q.
                  rewrite <- H4.
                  exact H3.
                + prove PNoEq_ beta p q.
                  apply PNoEq_tra_ beta p p1 q.
                  * exact Lp1e.
                  * apply PNoEq_sym_. exact H7.
              - assume H6: ordsucc beta :e beta. prove False.
                apply In_no2cycle (ordsucc beta) beta H6.
                apply ordsuccI2.
            }
          * assume H5. apply H5. assume H5: beta = ordsucc beta. prove False.
            apply In_irref beta. rewrite H5 at 2. apply ordsuccI2.
          * assume H5. exact H5.
    }
    apply HNC1.
    witness p1.
    rewrite Hab.
    prove PNo_rel_strict_uniq_imv L R (ordsucc beta) p1.
    prove PNo_rel_strict_imv L R (ordsucc beta) p1
       /\ forall q:set -> prop, PNo_rel_strict_imv L R (ordsucc beta) q -> PNoEq_ (ordsucc beta) p1 q.
    apply andI.
    * exact Lp1imv.
    * { let q. assume Hq: PNo_rel_strict_imv L R (ordsucc beta) q.
        prove PNoEq_ (ordsucc beta) p1 q.
        claim Lqb: PNo_rel_strict_imv L R beta q.
        { exact PNo_rel_strict_imv_antimon L R (ordsucc beta) Lsb q beta (ordsuccI2 beta) Hq. }
        claim Lpqe: PNoEq_ beta p q.
        { exact Hp3 q Lqb. }
        apply xm (q beta).
        - assume Hq1: q beta.
          prove PNoEq_ (ordsucc beta) p1 q.
          let gamma. assume Hc: gamma :e ordsucc beta.
          apply ordsuccE beta gamma Hc.
          + assume H3: gamma :e beta.
            claim Lpqce: p gamma <-> q gamma.
            { exact Lpqe gamma H3. }
            apply Lpqce. assume Hpqc Hqpc.
            prove p1 gamma <-> q gamma.
            apply iffI.
            * { assume H4: p gamma \/ gamma = beta.
                apply H4.
                - assume H5: p gamma. exact Hpqc H5.
                - assume H5: gamma = beta. prove False.
                  apply In_irref beta. rewrite <- H5 at 1. exact H3.
              }
            * { assume H4: q gamma.
                prove p gamma \/ gamma = beta.
                apply orIL.
                prove p gamma. exact Hqpc H4.
              }
          + assume H3: gamma = beta.
            prove p1 gamma <-> q gamma.
            apply iffI.
            * { assume _. prove q gamma. rewrite H3. prove q beta. exact Hq1. }
            * { assume H4: q gamma. prove p gamma \/ gamma = beta.
                apply orIR. exact H3.
              }
        - assume Hq0: ~ q beta.
          prove False.
          apply Lnotboth. rewrite Hab.
          apply andI.
          + prove PNo_rel_strict_imv L R (ordsucc beta) p0.
            apply PNoEq_rel_strict_imv L R (ordsucc beta) Lsb q p0.
            * { prove PNoEq_ (ordsucc beta) q p0.
                let gamma. assume Hc: gamma :e ordsucc beta.
                apply ordsuccE beta gamma Hc.
                - assume H3: gamma :e beta.
                  claim Lpqce: p gamma <-> q gamma.
                  { exact Lpqe gamma H3. }
                  apply Lpqce. assume Hpqc Hqpc.
                  prove q gamma <-> p0 gamma.
                  apply iffI.
                  + assume H4: q gamma.
                    prove p gamma /\ gamma <> beta.
                    apply andI.
                    * prove p gamma.
                      exact Hqpc H4.
                    * prove gamma <> beta.
                      assume H5: gamma = beta.
                      apply In_irref beta.
                      rewrite <- H5 at 1.
                      exact H3.
                  + assume H4: p gamma /\ gamma <> beta.
                    apply H4. assume H5 _. exact Hpqc H5.
                - assume H3: gamma = beta.
                  prove q gamma <-> p0 gamma.
                  apply iffI.
                  + assume H4: q gamma.
                    prove False.
                    apply Hq0.
                    rewrite <- H3.
                    exact H4.
                  + assume H4: p0 gamma.
                    apply H4.
                    assume _ H5. prove False. apply H5. exact H3.
              }
            * prove PNo_rel_strict_imv L R (ordsucc beta) q. exact Hq.
          + prove PNo_rel_strict_imv L R (ordsucc beta) p1. exact Lp1imv.
      }
Qed.

Definition PNo_lenbdd : set -> (set -> (set -> prop) -> prop) -> prop
  := fun alpha L => forall beta, forall p:set -> prop, L beta p -> beta :e alpha.

Theorem PNo_lenbdd_strict_imv_extend0 : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta /\ delta <> alpha).
let L R.
let alpha. assume Ha. apply Ha. assume Ha1 _.
assume HaL HaR.
let p.
assume Hp1: PNo_rel_strict_imv L R alpha p.
apply Hp1.
assume Hp1a Hp1b.
set p0 : set -> prop := fun delta => p delta /\ delta <> alpha.
claim Lsa: ordinal (ordsucc alpha).
{ exact ordinal_ordsucc alpha Ha. }
claim Lpp0e: PNoEq_ alpha p p0.
{ exact PNo_extend0_eq alpha p. }
prove PNo_rel_strict_upperbd L (ordsucc alpha) p0 /\ PNo_rel_strict_lowerbd R (ordsucc alpha) p0.
apply andI.
- prove PNo_rel_strict_upperbd L (ordsucc alpha) p0.
  let gamma. assume Hc: gamma :e ordsucc alpha.
  let q. assume Hq: PNo_downc L gamma q.
  claim Lc: ordinal gamma.
  { exact ordinal_Hered (ordsucc alpha) Lsa gamma Hc. }
  prove PNoLt gamma q (ordsucc alpha) p0.
  apply Hq.
  let delta. assume Hq1. apply Hq1.
  assume Hd: ordinal delta. assume Hq1. apply Hq1.
  let r. assume Hq1. apply Hq1.
  assume Hr: L delta r.
  assume Hqr: PNoLe gamma q delta r.
  apply PNoLeLt_tra gamma delta (ordsucc alpha) Lc Hd Lsa q r p0 Hqr.
  prove PNoLt delta r (ordsucc alpha) p0.
  claim Lda: delta :e alpha.
  { exact HaL delta r Hr. }
  claim Ldsa: delta :e ordsucc alpha.
  { apply ordsuccI1. exact Lda. }
  claim Ldr: PNo_downc L delta r.
  { exact PNo_downc_ref L delta Hd r Hr. }
  claim Lrp : PNoLt delta r alpha p.
  { exact Hp1a delta Lda r Ldr. }
  apply PNoLt_trichotomy_or delta (ordsucc alpha) r p0 Hd Lsa. assume H1. apply H1.
  + assume H1. exact H1.
  + assume H1. apply H1.
    assume H2: delta = ordsucc alpha.
    prove False.
    apply In_irref delta. rewrite H2 at 2. exact Ldsa.
  + assume H1: PNoLt (ordsucc alpha) p0 delta r.
    prove False.
    apply PNoLt_irref delta r.
    apply PNoLt_tra delta alpha delta Hd Ha Hd r p r Lrp.
    prove PNoLt alpha p delta r.
    apply PNoLtE (ordsucc alpha) delta p0 r H1.
    * { assume H2: PNoLt_ (ordsucc alpha :/\: delta) p0 r.
        apply H2.
        let eps. assume H3. apply H3.
        assume He: eps :e ordsucc alpha :/\: delta.
        apply binintersectE (ordsucc alpha) delta eps He.
        assume He1 He2.
        claim Lea: eps :e alpha.
        { exact Ha1 delta Lda eps He2. }
        assume H3. apply H3. assume H3. apply H3.
        assume H3: PNoEq_ eps p0 r.
        assume H4: ~p0 eps.
        assume H5: r eps.
        apply PNoLtI1.
        prove PNoLt_ (alpha :/\: delta) p r.
        prove exists beta :e alpha :/\: delta, PNoEq_ beta p r /\ ~p beta /\ r beta.
        witness eps.
        apply andI.
        - prove eps :e alpha :/\: delta. apply binintersectI.
          + exact Lea.
          + exact He2.
        - apply and3I.
          + prove PNoEq_ eps p r.
            apply PNoEq_tra_ eps p p0 r.
            * apply PNoEq_antimon_ p p0 alpha Ha eps Lea.
              exact Lpp0e.
            * exact H3.
          + prove ~p eps.
            assume H5: p eps. apply H4.
            prove p eps /\ eps <> alpha.
            apply andI.
            * exact H5.
            * prove eps <> alpha. assume H6: eps = alpha.
              apply In_irref alpha. rewrite <- H6 at 1. exact Lea.
          + prove r eps. exact H5.
      }
    * assume H2: ordsucc alpha :e delta.
      prove False.
      exact In_no2cycle delta (ordsucc alpha) Ldsa H2.
    * { assume H2: delta :e ordsucc alpha.
        assume H3: PNoEq_ delta p0 r.
        assume H4: ~p0 delta.
        apply PNoLtI3 alpha delta p r Lda.
        - prove PNoEq_ delta p r.
          apply PNoEq_tra_ delta p p0 r.
          + apply PNoEq_antimon_ p p0 alpha Ha delta Lda.
            exact Lpp0e.
          + exact H3.
        - prove ~p delta.
          assume H5: p delta. apply H4.
          prove p delta /\ delta <> alpha.
          apply andI.
          + exact H5.
          + prove delta <> alpha. assume H6: delta = alpha.
            apply In_irref alpha. rewrite <- H6 at 1. exact Lda.
      }
- prove PNo_rel_strict_lowerbd R (ordsucc alpha) p0.
  let gamma. assume Hc: gamma :e ordsucc alpha.
  let q. assume Hq: PNo_upc R gamma q.
  claim Lc: ordinal gamma.
  { exact ordinal_Hered (ordsucc alpha) Lsa gamma Hc. }
  prove PNoLt (ordsucc alpha) p0 gamma q.
  apply PNoLt_tra (ordsucc alpha) alpha gamma Lsa Ha Lc p0 p q.
  + prove PNoLt (ordsucc alpha) p0 alpha p.
    apply PNoLtI3.
    * prove alpha :e ordsucc alpha. apply ordsuccI2.
    * prove PNoEq_ alpha p0 p. apply PNoEq_sym_. exact Lpp0e.
    * { prove ~p0 alpha.
        assume H2: p0 alpha. apply H2.
        assume H3: p alpha.
        assume H4: alpha <> alpha. apply H4. reflexivity.
      }
  + prove PNoLt alpha p gamma q.
    apply Hq.
    let delta. assume Hq1. apply Hq1.
    assume Hd: ordinal delta. assume Hq1. apply Hq1.
    let r. assume Hq1. apply Hq1.
    assume Hr: R delta r.
    assume Hrq: PNoLe delta r gamma q.
    claim Ldr: PNo_upc R delta r.
    { exact PNo_upc_ref R delta Hd r Hr. }
    apply (fun H:PNoLt alpha p delta r => PNoLtLe_tra alpha delta gamma Ha Hd Lc p r q H Hrq).
    prove PNoLt alpha p delta r.
    exact Hp1b delta (HaR delta r Hr) r Ldr.
Qed.

Theorem PNo_lenbdd_strict_imv_extend1 : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta \/ delta = alpha).
let L R.
let alpha. assume Ha. apply Ha. assume Ha1 _.
assume HaL HaR.
let p.
assume Hp1: PNo_rel_strict_imv L R alpha p.
apply Hp1.
assume Hp1a Hp1b.
set p1 : set -> prop := fun delta => p delta \/ delta = alpha.
claim Lsa: ordinal (ordsucc alpha).
{ exact ordinal_ordsucc alpha Ha. }
claim Lpp1e: PNoEq_ alpha p p1.
{ exact PNo_extend1_eq alpha p. }
prove PNo_rel_strict_upperbd L (ordsucc alpha) p1 /\ PNo_rel_strict_lowerbd R (ordsucc alpha) p1.
apply andI.
- prove PNo_rel_strict_upperbd L (ordsucc alpha) p1.
  let gamma. assume Hc: gamma :e ordsucc alpha.
  let q. assume Hq: PNo_downc L gamma q.
  claim Lc: ordinal gamma.
  { exact ordinal_Hered (ordsucc alpha) Lsa gamma Hc. }
  prove PNoLt gamma q (ordsucc alpha) p1.
  apply PNoLt_tra gamma alpha (ordsucc alpha) Lc Ha Lsa q p p1.
  + prove PNoLt gamma q alpha p.
    apply Hq.
    let delta. assume Hq1. apply Hq1.
    assume Hd: ordinal delta. assume Hq1. apply Hq1.
    let r. assume Hq1. apply Hq1.
    assume Hr: L delta r.
    assume Hqr: PNoLe gamma q delta r.
    claim Ldr: PNo_downc L delta r.
    { prove exists beta, ordinal beta /\ exists q:set -> prop, L beta q /\ PNoLe delta r beta q.
      witness delta. apply andI.
      - exact Hd.
      - witness r. apply andI.
        + exact Hr.
        + apply PNoLe_ref.
    }
    apply PNoLeLt_tra gamma delta alpha Lc Hd Ha q r p Hqr.
    prove PNoLt delta r alpha p.
    exact Hp1a delta (HaL delta r Hr) r Ldr.
  + prove PNoLt alpha p (ordsucc alpha) p1.
    apply PNoLtI2.
    * prove alpha :e ordsucc alpha. apply ordsuccI2.
    * prove PNoEq_ alpha p p1. exact Lpp1e.
    * prove p1 alpha. prove p alpha \/ alpha = alpha. apply orIR. reflexivity.
- prove PNo_rel_strict_lowerbd R (ordsucc alpha) p1.
  let gamma. assume Hc: gamma :e ordsucc alpha.
  let q. assume Hq: PNo_upc R gamma q.
  claim Lc: ordinal gamma.
  { exact ordinal_Hered (ordsucc alpha) Lsa gamma Hc. }
  prove PNoLt (ordsucc alpha) p1 gamma q.
  apply Hq.
  let delta. assume Hq1. apply Hq1.
  assume Hd: ordinal delta. assume Hq1. apply Hq1.
  let r. assume Hq1. apply Hq1.
  assume Hr: R delta r.
  assume Hrq: PNoLe delta r gamma q.
  apply (fun H:PNoLt (ordsucc alpha) p1 delta r => PNoLtLe_tra (ordsucc alpha) delta gamma Lsa Hd Lc p1 r q H Hrq).
  prove PNoLt (ordsucc alpha) p1 delta r.
  claim Lda: delta :e alpha.
  { exact HaR delta r Hr. }
  claim Ldsa: delta :e ordsucc alpha.
  { apply ordsuccI1. exact Lda. }
  claim Ldr: PNo_upc R delta r.
  { prove exists beta, ordinal beta /\ exists q:set -> prop, R beta q /\ PNoLe beta q delta r.
    witness delta. apply andI.
    - exact Hd.
    - witness r. apply andI.
      + exact Hr.
      + apply PNoLe_ref.
  }
  claim Lpr : PNoLt alpha p delta r.
  { exact Hp1b delta Lda r Ldr. }
  apply PNoLt_trichotomy_or delta (ordsucc alpha) r p1 Hd Lsa. assume H1. apply H1.
  + assume H1: PNoLt delta r (ordsucc alpha) p1.
    prove False.
    apply PNoLt_irref alpha p.
    prove PNoLt alpha p alpha p.
    apply PNoLt_tra alpha delta alpha Ha Hd Ha p r p Lpr.
    prove PNoLt delta r alpha p.
    apply PNoLtE delta (ordsucc alpha) r p1 H1.
    * { assume H2: PNoLt_ (delta :/\: ordsucc alpha) r p1.
        apply H2.
        let eps. assume H3. apply H3.
        assume He: eps :e delta :/\: ordsucc alpha.
        apply binintersectE delta (ordsucc alpha) eps He.
        assume He1 He2.
        claim Lea: eps :e alpha.
        { exact Ha1 delta Lda eps He1. }
        assume H3. apply H3. assume H3. apply H3.
        assume H3: PNoEq_ eps r p1.
        assume H4: ~r eps.
        assume H5: p1 eps.
        apply PNoLtI1.
        prove PNoLt_ (delta :/\: alpha) r p.
        prove exists beta :e delta :/\: alpha, PNoEq_ beta r p /\ ~r beta /\ p beta.
        witness eps.
        apply andI.
        - prove eps :e delta :/\: alpha. apply binintersectI.
          + exact He1.
          + exact Lea.
        - apply and3I.
          + prove PNoEq_ eps r p.
            apply PNoEq_tra_ eps r p1 p.
            * exact H3.
            * apply PNoEq_antimon_ p1 p alpha Ha eps Lea.
              apply PNoEq_sym_. exact Lpp1e.
          + prove ~r eps. exact H4.
          + prove p eps.
            apply H5.
            * exact (fun H => H).
            * assume H6: eps = alpha. prove False.
              apply In_irref alpha. rewrite <- H6 at 1. exact Lea.
      }
    * { assume H2: delta :e ordsucc alpha.
        assume H3: PNoEq_ delta r p1.
        assume H4: p1 delta.
        apply PNoLtI2 delta alpha r p Lda.
        - prove PNoEq_ delta r p.
          apply PNoEq_tra_ delta r p1 p.
          + exact H3.
          + apply PNoEq_antimon_ p1 p alpha Ha delta Lda.
            apply PNoEq_sym_. exact Lpp1e.
        - prove p delta.
          apply H4.
          * exact (fun H => H).
          * assume H5: delta = alpha. prove False.
            apply In_irref alpha. rewrite <- H5 at 1. exact Lda.
      }
    * assume H2: ordsucc alpha :e delta.
      prove False.
      exact In_no2cycle delta (ordsucc alpha) Ldsa H2.
  + assume H1. apply H1.
    assume H2: delta = ordsucc alpha.
    prove False.
    apply In_irref delta. rewrite H2 at 2. exact Ldsa.
  + assume H1. exact H1.
Qed.

Theorem PNo_lenbdd_strict_imv_split : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_split_imv L R alpha p.
let L R.
let alpha. assume Ha.
assume HaL HaR.
let p.
assume Hp1.
prove PNo_rel_strict_split_imv L R alpha p.
exact andI (PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta /\ delta <> alpha))
           (PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta \/ delta = alpha))
           (PNo_lenbdd_strict_imv_extend0 L R alpha Ha HaL HaR p Hp1)
           (PNo_lenbdd_strict_imv_extend1 L R alpha Ha HaL HaR p Hp1).
Qed.

Theorem PNo_rel_imv_bdd_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta :e ordsucc alpha,
      exists p:set -> prop, PNo_rel_strict_split_imv L R beta p.
let L R. assume HLR.
let alpha. assume Ha.
apply Ha. assume Ha1 _.
assume HaL HaR.
claim Lsa: ordinal (ordsucc alpha).
{ exact ordinal_ordsucc alpha Ha. }
apply PNo_rel_imv_ex L R HLR alpha Ha.
- assume H2. apply H2.
  let p. assume Hp: PNo_rel_strict_uniq_imv L R alpha p.
  apply Hp.
  assume Hp1: PNo_rel_strict_imv L R alpha p.
  apply Hp1.
  assume Hp1a Hp1b.
  assume Hp2: forall q:set -> prop, PNo_rel_strict_imv L R alpha q -> PNoEq_ alpha p q.
  witness alpha. apply andI.
  + prove alpha :e ordsucc alpha. apply ordsuccI2.
  + witness p.
    prove PNo_rel_strict_split_imv L R alpha p.
    exact PNo_lenbdd_strict_imv_split L R alpha Ha HaL HaR p Hp1.
- assume H1. apply H1.
  let beta. assume H1. apply H1.
  assume Hb: beta :e alpha. assume H1.
  witness beta. apply andI.
  + prove beta :e ordsucc alpha. apply ordsuccI1. exact Hb.
  + exact H1.
Qed.

Definition PNo_strict_upperbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L alpha p =>
       forall beta, ordinal beta -> forall q:set -> prop, L beta q -> PNoLt beta q alpha p.

Definition PNo_strict_lowerbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun R alpha p =>
       forall beta, ordinal beta -> forall q:set -> prop, R beta q -> PNoLt alpha p beta q.

Definition PNo_strict_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_strict_upperbd L alpha p /\ PNo_strict_lowerbd R alpha p.

Theorem PNoEq_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_upperbd L alpha p -> PNo_strict_upperbd L alpha q.
let L alpha. assume Ha. let p q.
assume Hpq: PNoEq_ alpha p q.
assume H1: PNo_strict_upperbd L alpha p.
prove PNo_strict_upperbd L alpha q.
let beta. assume Hb: ordinal beta.
let r. assume H2: L beta r.
prove PNoLt beta r alpha q.
apply PNoLtEq_tra beta alpha Hb Ha r p q.
- prove PNoLt beta r alpha p.
  exact H1 beta Hb r H2.
- prove PNoEq_ alpha p q. exact Hpq.
Qed.

Theorem PNoEq_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_lowerbd R alpha p -> PNo_strict_lowerbd R alpha q.
let R alpha. assume Ha. let p q.
assume Hpq: PNoEq_ alpha p q.
assume H1: PNo_strict_lowerbd R alpha p.
prove PNo_strict_lowerbd R alpha q.
let beta. assume Hb: ordinal beta.
let r. assume H2: R beta r.
prove PNoLt alpha q beta r.
apply PNoEqLt_tra alpha beta Ha Hb q p r.
- prove PNoEq_ alpha q p. apply PNoEq_sym_. exact Hpq.
- prove PNoLt alpha p beta r.
  exact H1 beta Hb r H2.
Qed.

Theorem PNoEq_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_imv L R alpha p -> PNo_strict_imv L R alpha q.
let L R alpha. assume Ha. let p q. assume Hpq H1.
apply H1. assume H2 H3.
prove PNo_strict_upperbd L alpha q /\ PNo_strict_lowerbd R alpha q.
apply andI.
- exact PNoEq_strict_upperbd L alpha Ha p q Hpq H2.
- exact PNoEq_strict_lowerbd R alpha Ha p q Hpq H3.
Qed.

Theorem PNo_strict_upperbd_imp_rel_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L beta p.
let L alpha.
assume Ha: ordinal alpha.
let beta.
assume Hb: beta :e ordsucc alpha.
let p.
assume H1: PNo_strict_upperbd L alpha p.
let gamma. assume Hc: gamma :e beta.
let q. assume Hq: PNo_downc L gamma q.
apply Ha. assume Ha1 _.
claim Lsa: ordinal (ordsucc alpha).
{ exact ordinal_ordsucc alpha Ha. }
claim Lb: ordinal beta.
{ exact ordinal_Hered (ordsucc alpha) Lsa beta Hb. }
claim Lb1: TransSet beta.
{ apply Lb. assume H _. exact H. }
claim Lc: ordinal gamma.
{ exact ordinal_Hered beta Lb gamma Hc. }
claim Lcb: gamma c= beta.
{ exact Lb1 gamma Hc. }
prove PNoLt gamma q beta p.
apply Hq.
let delta. assume H2. apply H2.
assume Hd: ordinal delta. assume H2. apply H2.
let r. assume H2. apply H2.
assume H2: L delta r.
assume H3: PNoLe gamma q delta r.
claim L1: PNoLt delta r alpha p.
{ exact H1 delta Hd r H2. }
claim L2: PNoLt gamma q alpha p.
{ exact PNoLeLt_tra gamma delta alpha Lc Hd Ha q r p H3 L1. }
claim Lca: gamma :e alpha.
{ apply ordsuccE alpha beta Hb.
  - assume Hb1: beta :e alpha. exact Ha1 beta Hb1 gamma Hc.
  - assume Hb1: beta = alpha. rewrite <- Hb1. exact Hc.
}
claim Lca2: gamma c= alpha.
{ exact Ha1 gamma Lca. }
prove PNoLt gamma q beta p.
apply PNoLt_trichotomy_or gamma beta q p Lc Lb. assume H4. apply H4.
- assume H4. exact H4.
- assume H4. apply H4.
  assume H4: gamma = beta.
  prove False.
  apply In_irref beta. rewrite <- H4 at 1. exact Hc.
- assume H4: PNoLt beta p gamma q.
  prove False.
  apply PNoLtE beta gamma p q H4.
  + rewrite binintersect_com.
    rewrite binintersect_Subq_eq_1 gamma beta Lcb.
    assume H5: PNoLt_ gamma p q.
    apply H5.
    apply PNoLt_irref alpha p.
    apply PNoLt_tra alpha gamma alpha Ha Lc Ha p q p.
    * prove PNoLt alpha p gamma q.
      apply PNoLtI1.
      prove PNoLt_ (alpha :/\: gamma) p q.
      rewrite binintersect_com.
      rewrite binintersect_Subq_eq_1 gamma alpha Lca2.
      prove PNoLt_ gamma p q.
      exact H5.
    * prove PNoLt gamma q alpha p. exact L2.
  + assume H5: beta :e gamma.
    prove False.
    exact In_no2cycle beta gamma H5 Hc.
  + assume H5: gamma :e beta.
    assume H6: PNoEq_ gamma p q.
    assume H7: ~p gamma.
    apply PNoLt_irref alpha p.
    apply PNoLt_tra alpha gamma alpha Ha Lc Ha p q p.
    * { prove PNoLt alpha p gamma q.
        apply PNoLtI3.
        - prove gamma :e alpha. exact Lca.
        - prove PNoEq_ gamma p q. exact H6.
        - prove ~p gamma. exact H7.
      }
    * prove PNoLt gamma q alpha p. exact L2.
Qed.

Theorem PNo_strict_lowerbd_imp_rel_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R beta p.
let R alpha.
assume Ha: ordinal alpha.
let beta.
assume Hb: beta :e ordsucc alpha.
let p.
assume H1: PNo_strict_lowerbd R alpha p.
let gamma. assume Hc: gamma :e beta.
let q. assume Hq: PNo_upc R gamma q.
apply Ha. assume Ha1 _.
claim Lsa: ordinal (ordsucc alpha).
{ exact ordinal_ordsucc alpha Ha. }
claim Lb: ordinal beta.
{ exact ordinal_Hered (ordsucc alpha) Lsa beta Hb. }
claim Lb1: TransSet beta.
{ apply Lb. assume H _. exact H. }
claim Lc: ordinal gamma.
{ exact ordinal_Hered beta Lb gamma Hc. }
claim Lcb: gamma c= beta.
{ exact Lb1 gamma Hc. }
prove PNoLt beta p gamma q.
apply Hq.
let delta. assume H2. apply H2.
assume Hd: ordinal delta. assume H2. apply H2.
let r. assume H2. apply H2.
assume H2: R delta r.
assume H3: PNoLe delta r gamma q.
claim L1: PNoLt alpha p delta r.
{ exact H1 delta Hd r H2. }
claim L2: PNoLt alpha p gamma q.
{ exact PNoLtLe_tra alpha delta gamma Ha Hd Lc p r q L1 H3. }
claim Lca: gamma :e alpha.
{ apply ordsuccE alpha beta Hb.
  - assume Hb1: beta :e alpha. exact Ha1 beta Hb1 gamma Hc.
  - assume Hb1: beta = alpha. rewrite <- Hb1. exact Hc.
}
claim Lca2: gamma c= alpha.
{ exact Ha1 gamma Lca. }
prove PNoLt beta p gamma q.
apply PNoLt_trichotomy_or gamma beta q p Lc Lb. assume H4. apply H4.
- assume H4: PNoLt gamma q beta p.
  prove False.
  apply PNoLtE gamma beta q p H4.
  + rewrite binintersect_Subq_eq_1 gamma beta Lcb.
    assume H5: PNoLt_ gamma q p.
    apply H5.
    apply PNoLt_irref alpha p.
    apply PNoLt_tra alpha gamma alpha Ha Lc Ha p q p.
    * prove PNoLt alpha p gamma q. exact L2.
    * prove PNoLt gamma q alpha p.
      apply PNoLtI1.
      prove PNoLt_ (gamma :/\: alpha) q p.
      rewrite binintersect_Subq_eq_1 gamma alpha Lca2.
      prove PNoLt_ gamma q p.
      exact H5.
  + assume H5: gamma :e beta.
    assume H6: PNoEq_ gamma q p.
    assume H7: p gamma.
    apply PNoLt_irref alpha p.
    apply PNoLt_tra alpha gamma alpha Ha Lc Ha p q p.
    * prove PNoLt alpha p gamma q. exact L2.
    * { prove PNoLt gamma q alpha p.
        apply PNoLtI2.
        - prove gamma :e alpha. exact Lca.
        - prove PNoEq_ gamma q p. exact H6.
        - prove p gamma. exact H7.
      }
  + assume H5: beta :e gamma.
    prove False.
    exact In_no2cycle beta gamma H5 Hc.
- assume H4. apply H4.
  assume H4: gamma = beta.
  prove False.
  apply In_irref beta. rewrite <- H4 at 1. exact Hc.
- assume H4. exact H4.
Qed.

Theorem PNo_strict_imv_imp_rel_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_imv L R alpha p -> PNo_rel_strict_imv L R beta p.
let L R alpha.
assume Ha: ordinal alpha.
let beta.
assume Hb: beta :e ordsucc alpha.
let p.
assume H1: PNo_strict_imv L R alpha p.
apply H1.
assume H2: PNo_strict_upperbd L alpha p.
assume H3: PNo_strict_lowerbd R alpha p.
prove PNo_rel_strict_imv L R beta p.
prove PNo_rel_strict_upperbd L beta p /\ PNo_rel_strict_lowerbd R beta p.
apply andI.
- exact PNo_strict_upperbd_imp_rel_strict_upperbd L alpha Ha beta Hb p H2.
- exact PNo_strict_lowerbd_imp_rel_strict_lowerbd R alpha Ha beta Hb p H3.
Qed.

Theorem PNo_rel_split_imv_imp_strict_imv : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> forall p:set -> prop,
       PNo_rel_strict_split_imv L R alpha p
    -> PNo_strict_imv L R alpha p.
let L R.
let alpha.
assume Ha: ordinal alpha.
let p.
assume Hp: PNo_rel_strict_split_imv L R alpha p.
claim Lsa: ordinal (ordsucc alpha).
{ exact ordinal_ordsucc alpha Ha. }
set p0 : set -> prop := fun delta => p delta /\ delta <> alpha.
set p1 : set -> prop := fun delta => p delta \/ delta = alpha.
apply Hp.
assume Hp0: PNo_rel_strict_imv L R (ordsucc alpha) p0.
assume Hp1: PNo_rel_strict_imv L R (ordsucc alpha) p1.
apply Hp0.
assume Hp0a: PNo_rel_strict_upperbd L (ordsucc alpha) p0.
assume Hp0b: PNo_rel_strict_lowerbd R (ordsucc alpha) p0.
apply Hp1.
assume Hp1a: PNo_rel_strict_upperbd L (ordsucc alpha) p1.
assume Hp1b: PNo_rel_strict_lowerbd R (ordsucc alpha) p1.
claim Lnp0a: ~p0 alpha.
{ assume H10. apply H10.
  assume H11: p alpha.
  assume H12: alpha <> alpha.
  apply H12. reflexivity.
}
claim Lp1a: p1 alpha.
{ prove p alpha \/ alpha = alpha.
  apply orIR. reflexivity.
}
claim Lap0p: PNoLt (ordsucc alpha) p0 alpha p.
{ apply PNoLtI3.
  - apply ordsuccI2.
  - prove PNoEq_ alpha p0 p. apply PNoEq_sym_. apply PNo_extend0_eq.
  - prove ~p0 alpha. exact Lnp0a.
}
claim Lapp1: PNoLt alpha p (ordsucc alpha) p1.
{ apply PNoLtI2.
  - apply ordsuccI2.
  - prove PNoEq_ alpha p p1. apply PNo_extend1_eq.
  - prove p1 alpha. exact Lp1a.
}
prove PNo_strict_upperbd L alpha p /\ PNo_strict_lowerbd R alpha p.
apply andI.
- let beta.
  assume Hb: ordinal beta.
  let q.
  assume Hq: L beta q.
  prove PNoLt beta q alpha p.
  claim L4: PNo_downc L beta q.
  { apply PNo_downc_ref L beta Hb. exact Hq. }
  claim L5: beta :e ordsucc alpha -> PNoLt beta q alpha p.
  { assume H10: beta :e ordsucc alpha.
    apply PNoLt_tra beta (ordsucc alpha) alpha Hb Lsa Ha q p0 p.
    - prove PNoLt beta q (ordsucc alpha) p0.
      apply Hp0a beta H10 q.
      prove PNo_downc L beta q.
      exact L4.
    - exact Lap0p.
  }
  claim L6: forall gamma :e ordsucc alpha, gamma :e beta -> PNoEq_ gamma p q -> q gamma -> p0 gamma.
  { let gamma.
    assume Hc1: gamma :e ordsucc alpha.
    assume Hc2: gamma :e beta.
    assume H10: PNoEq_ gamma p q.
    assume H11: q gamma.
    apply dneg.
    assume HNC: ~p0 gamma.
    claim Lc: ordinal gamma.
    { exact ordinal_Hered beta Hb gamma Hc2. }
    claim L6a: PNoLt gamma q beta q.
    { apply PNoLtI2.
      - exact Hc2.
      - prove PNoEq_ gamma q q.
        apply PNoEq_ref_.
      - prove q gamma. exact H11.
    }
    claim L6b: PNo_downc L gamma q.
    { prove exists delta, ordinal delta /\ exists r:set -> prop, L delta r /\ PNoLe gamma q delta r.
      witness beta. apply andI.
      - exact Hb.
      - witness q. apply andI.
        + exact Hq.
        + apply PNoLeI1. exact L6a.
    }
    claim L6c: PNoLt gamma q (ordsucc alpha) p0.
    { exact Hp0a gamma Hc1 q L6b. }
    claim L6d: PNoLt (ordsucc alpha) p0 gamma q.
    { apply PNoLtI3.
      - exact Hc1.
      - prove PNoEq_ gamma p0 q.
        apply PNoEq_tra_ gamma p0 p q.
        + apply PNoEq_sym_. 
          prove PNoEq_ gamma p p0.
          apply ordsuccE alpha gamma Hc1.
          * assume H12: gamma :e alpha.
            apply PNoEq_antimon_ p p0 alpha Ha gamma H12.
            prove PNoEq_ alpha p p0.
            exact PNo_extend0_eq alpha p.
          * assume H12: gamma = alpha.
            rewrite H12.
            prove PNoEq_ alpha p p0.
            exact PNo_extend0_eq alpha p.
        + exact H10.
      - prove ~p0 gamma. exact HNC.
    }
    apply PNoLt_irref gamma q.
    exact PNoLt_tra gamma (ordsucc alpha) gamma Lc Lsa Lc q p0 q L6c L6d.
  }
  apply PNoLt_trichotomy_or alpha beta p q Ha Hb. assume H10. apply H10.
  + assume H10: PNoLt alpha p beta q.
    apply PNoLtE alpha beta p q H10.
    * assume H11: PNoLt_ (alpha :/\: beta) p q.
      apply H11.
      let gamma. assume H12. apply H12.
      assume Hc: gamma :e alpha :/\: beta.
      assume H12. apply H12. assume H12. apply H12.
      assume H12: PNoEq_ gamma p q.
      assume H13: ~p gamma.
      assume H14: q gamma.
      prove False.
      apply binintersectE alpha beta gamma Hc.
      assume Hc1: gamma :e alpha.
      assume Hc2: gamma :e beta.
      apply L6 gamma (ordsuccI1 alpha gamma Hc1) Hc2 H12 H14.
      assume H15: p gamma. assume _.
      apply H13. exact H15.
    * assume H11: alpha :e beta.
      assume H12: PNoEq_ alpha p q.
      assume H13: q alpha.
      prove False.
      apply Lnp0a.
      prove p0 alpha.
      exact L6 alpha (ordsuccI2 alpha) H11 H12 H13.
    * assume H11: beta :e alpha. assume _ _.
      apply L5. apply ordsuccI1. exact H11.
  + assume H10. apply H10.
    assume H10a: alpha = beta.
    assume H10b: PNoEq_ alpha p q.
    apply L5.
    prove beta :e ordsucc alpha.
    rewrite <- H10a. apply ordsuccI2.
  + assume H10: PNoLt beta q alpha p. exact H10.
- let beta.
  assume Hb: ordinal beta.
  let q.
  assume Hq: R beta q.
  prove PNoLt alpha p beta q.
  claim L4: PNo_upc R beta q.
  { apply PNo_upc_ref R beta Hb. exact Hq. }
  claim L5: beta :e ordsucc alpha -> PNoLt alpha p beta q.
  { assume H10: beta :e ordsucc alpha.
    apply PNoLt_tra alpha (ordsucc alpha) beta Ha Lsa Hb p p1 q.
    - exact Lapp1.
    - prove PNoLt (ordsucc alpha) p1 beta q.
      apply Hp1b beta H10 q.
      prove PNo_upc R beta q.
      exact L4.
  }
  claim L6: forall gamma :e ordsucc alpha, gamma :e beta -> PNoEq_ gamma q p -> p1 gamma -> q gamma.
  { let gamma.
    assume Hc1: gamma :e ordsucc alpha.
    assume Hc2: gamma :e beta.
    assume H10: PNoEq_ gamma q p.
    assume H11: p1 gamma.
    apply dneg.
    assume HNC: ~q gamma.
    claim Lc: ordinal gamma.
    { exact ordinal_Hered beta Hb gamma Hc2. }
    claim L6a: PNoLt beta q gamma q.
    { apply PNoLtI3.
      - exact Hc2.
      - prove PNoEq_ gamma q q.
        apply PNoEq_ref_.
      - prove ~q gamma. exact HNC.
    }
    claim L6b: PNo_upc R gamma q.
    { prove exists delta, ordinal delta /\ exists r:set -> prop, R delta r /\ PNoLe delta r gamma q.
      witness beta. apply andI.
      - exact Hb.
      - witness q. apply andI.
        + exact Hq.
        + apply PNoLeI1. exact L6a.
    }
    claim L6c: PNoLt (ordsucc alpha) p1 gamma q.
    { exact Hp1b gamma Hc1 q L6b. }
    claim L6d: PNoLt gamma q (ordsucc alpha) p1.
    { apply PNoLtI2.
      - exact Hc1.
      - prove PNoEq_ gamma q p1.
        apply PNoEq_tra_ gamma q p p1.
        + exact H10.
        + prove PNoEq_ gamma p p1.
          apply ordsuccE alpha gamma Hc1.
          * assume H12: gamma :e alpha.
            apply PNoEq_antimon_ p p1 alpha Ha gamma H12.
            prove PNoEq_ alpha p p1.
            exact PNo_extend1_eq alpha p.
          * assume H12: gamma = alpha.
            rewrite H12.
            prove PNoEq_ alpha p p1.
            exact PNo_extend1_eq alpha p.
      - prove p1 gamma. exact H11.
    }
    apply PNoLt_irref gamma q.
    exact PNoLt_tra gamma (ordsucc alpha) gamma Lc Lsa Lc q p1 q L6d L6c.
  }
  apply PNoLt_trichotomy_or alpha beta p q Ha Hb. assume H10. apply H10.
  - assume H10. exact H10.
  - assume H10. apply H10.
    assume H10a: alpha = beta.
    assume H10b: PNoEq_ alpha p q.
    apply L5.
    prove beta :e ordsucc alpha.
    rewrite <- H10a. apply ordsuccI2.
  - assume H10: PNoLt beta q alpha p.
    apply PNoLtE beta alpha q p H10.
    + assume H11: PNoLt_ (beta :/\: alpha) q p.
      apply H11.
      let gamma. assume H12. apply H12.
      assume Hc: gamma :e beta :/\: alpha.
      assume H12. apply H12. assume H12. apply H12.
      assume H12: PNoEq_ gamma q p.
      assume H13: ~q gamma.
      assume H14: p gamma.
      prove False.
      apply binintersectE beta alpha gamma Hc.
      assume Hc2: gamma :e beta.
      assume Hc1: gamma :e alpha.
      apply H13.
      apply L6 gamma (ordsuccI1 alpha gamma Hc1) Hc2 H12.
      prove p1 gamma.
      prove p gamma \/ gamma = alpha.
      apply orIL. exact H14.
    + assume H11: beta :e alpha. assume _ _.
      apply L5. apply ordsuccI1. exact H11.
    + assume H11: alpha :e beta.
      assume H12: PNoEq_ alpha q p.
      assume H13: ~q alpha.
      prove False.
      apply H13.
      exact L6 alpha (ordsuccI2 alpha) H11 H12 Lp1a.
Qed.

Theorem PNo_lenbdd_strict_imv_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta :e ordsucc alpha,
      exists p:set -> prop, PNo_strict_imv L R beta p.
let L R. assume HLR.
let alpha. assume Ha.
assume HaL HaR.
apply PNo_rel_imv_bdd_ex L R HLR alpha Ha HaL HaR.
let beta. assume H1. apply H1.
assume Hb: beta :e ordsucc alpha. assume H1. apply H1.
let p.
assume Hp: PNo_rel_strict_split_imv L R beta p.
claim Lsa: ordinal (ordsucc alpha).
{ exact ordinal_ordsucc alpha Ha. }
claim Lb: ordinal beta.
{ exact ordinal_Hered (ordsucc alpha) Lsa beta Hb. }
witness beta. apply andI.
- exact Hb.
- witness p.
  prove PNo_strict_imv L R beta p.
  exact PNo_rel_split_imv_imp_strict_imv L R beta Lb p Hp.
Qed.

Definition PNo_least_rep : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R beta p => ordinal beta
       /\ PNo_strict_imv L R beta p
       /\ forall gamma :e beta,
           forall q:set -> prop, ~PNo_strict_imv L R gamma q.

Definition PNo_least_rep2 : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R beta p => PNo_least_rep L R beta p /\ forall x, x /:e beta -> ~p x.

Theorem PNo_strict_imv_pred_eq : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha -> forall p q:set -> prop,
     PNo_least_rep L R alpha p
  -> PNo_strict_imv L R alpha q
  -> forall beta :e alpha, p beta <-> q beta.
let L R. assume HLR. let alpha. assume Ha. let p q.
assume Hp.
assume Hq.
apply Ha. assume Ha1 _.
apply Hp. assume Hp1. apply Hp1.
assume _.
assume Hp1: PNo_strict_imv L R alpha p.
assume Hp2: forall beta :e alpha, forall r:set -> prop, ~PNo_strict_imv L R beta r.
apply Hp1.
assume Hp1a: PNo_strict_upperbd L alpha p.
assume Hp1b: PNo_strict_lowerbd R alpha p.
apply Hq.
assume Hq1: PNo_strict_upperbd L alpha q.
assume Hq2: PNo_strict_lowerbd R alpha q.
claim L1: forall beta, ordinal beta -> beta :e alpha -> (p beta <-> q beta).
{ apply ordinal_ind.
  let beta. assume Hb1: ordinal beta.
  assume IH: forall gamma :e beta, gamma :e alpha -> (p gamma <-> q gamma).
  assume Hb2: beta :e alpha.
  claim Lbpq: PNoEq_ beta p q.
  { let gamma. assume Hc: gamma :e beta.
    exact IH gamma Hc (Ha1 beta Hb2 gamma Hc).
  }
  prove p beta <-> q beta.
  apply iffI.
  - assume H1: p beta.
    prove q beta.
    apply dneg.
    assume H2: ~q beta.
    claim Lqp: PNoLt beta q alpha p.
    { apply PNoLtI2.
      - prove beta :e alpha. exact Hb2.
      - prove PNoEq_ beta q p. apply PNoEq_sym_. exact Lbpq. (** IH used in pf of Lbpq **)
      - prove p beta. exact H1.
    }
    claim Lqq: PNoLt alpha q beta q.
    { apply PNoLtI3.
      - prove beta :e alpha. exact Hb2.
      - prove PNoEq_ beta q q. apply PNoEq_ref_.
      - prove ~q beta. exact H2.
    }
    apply Hp2 beta Hb2 q.
    prove PNo_strict_imv L R beta q.
    prove PNo_strict_upperbd L beta q /\ PNo_strict_lowerbd R beta q.
    apply andI.
    + let gamma. assume Hc: ordinal gamma. let r. assume Hr: L gamma r.
      prove PNoLt gamma r beta q.
      apply PNoLt_tra gamma alpha beta Hc Ha Hb1 r q q.
      * prove PNoLt gamma r alpha q. exact Hq1 gamma Hc r Hr.
      * prove PNoLt alpha q beta q. exact Lqq.
    + let gamma. assume Hc: ordinal gamma. let r. assume Hr: R gamma r.
      prove PNoLt beta q gamma r.
      apply PNoLt_tra beta alpha gamma Hb1 Ha Hc q p r.
      * prove PNoLt beta q alpha p. exact Lqp.
      * prove PNoLt alpha p gamma r. exact Hp1b gamma Hc r Hr.
  - assume H1: q beta.
    prove p beta.
    apply dneg.
    assume H2: ~p beta.
    claim Lpq: PNoLt alpha p beta q.
    { apply PNoLtI3.
      - prove beta :e alpha. exact Hb2.
      - prove PNoEq_ beta p q. exact Lbpq. (** IH used in pf of Lbpq **)
      - prove ~p beta. exact H2.
    }
    claim Lqq: PNoLt beta q alpha q.
    { apply PNoLtI2.
      - prove beta :e alpha. exact Hb2.
      - prove PNoEq_ beta q q. apply PNoEq_ref_.
      - prove q beta. exact H1.
    }
    apply Hp2 beta Hb2 q.
    prove PNo_strict_imv L R beta q.
    prove PNo_strict_upperbd L beta q /\ PNo_strict_lowerbd R beta q.
    apply andI.
    + let gamma. assume Hc: ordinal gamma. let r. assume Hr: L gamma r.
      prove PNoLt gamma r beta q.
      apply PNoLt_tra gamma alpha beta Hc Ha Hb1 r p q.
      * prove PNoLt gamma r alpha p. exact Hp1a gamma Hc r Hr.
      * prove PNoLt alpha p beta q. exact Lpq.
    + let gamma. assume Hc: ordinal gamma. let r. assume Hr: R gamma r.
      prove PNoLt beta q gamma r.
      apply PNoLt_tra beta alpha gamma Hb1 Ha Hc q q r.
      * prove PNoLt beta q alpha q. exact Lqq.
      * prove PNoLt alpha q gamma r. exact Hq2 gamma Hc r Hr.
}
let beta. assume Hb: beta :e alpha.
exact L1 beta (ordinal_Hered alpha Ha beta Hb) Hb.
Qed.

Theorem PNo_lenbdd_least_rep2_exuniq2 : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta,
        (exists p:set -> prop, PNo_least_rep2 L R beta p)
     /\ (forall p q:set -> prop, PNo_least_rep2 L R beta p -> PNo_least_rep2 L R beta q -> p = q).
let L R. assume HLR. let alpha. assume Ha HaL HaR.
claim L1: exists beta, ordinal beta /\ (exists p:set -> prop, PNo_strict_imv L R beta p) /\ forall gamma :e beta, ~(exists p:set -> prop, PNo_strict_imv L R gamma p).
{ apply least_ordinal_ex (fun beta => exists p:set -> prop, PNo_strict_imv L R beta p).
  prove exists beta, ordinal beta /\ exists p:set -> prop, PNo_strict_imv L R beta p.
  apply PNo_lenbdd_strict_imv_ex L R HLR alpha Ha HaL HaR.
  let beta. assume H1. apply H1.
  assume Hb: beta :e ordsucc alpha.
  assume H1. apply H1.
  let p. assume Hp: PNo_strict_imv L R beta p.
  claim Lsa: ordinal (ordsucc alpha).
  { exact ordinal_ordsucc alpha Ha. }
  witness beta. apply andI.
  - exact ordinal_Hered (ordsucc alpha) Lsa beta Hb.
  - witness p. exact Hp.
}
apply L1.
let beta. assume H1. apply H1. assume H1. apply H1.
assume H1: ordinal beta.
assume H2: exists p:set -> prop, PNo_strict_imv L R beta p.
assume H3: forall gamma :e beta, ~exists p:set -> prop, PNo_strict_imv L R gamma p.
apply H2.
let p. assume Hp: PNo_strict_imv L R beta p.
witness beta.
apply andI.
- witness (fun x => x :e beta /\ p x).
  prove PNo_least_rep L R beta (fun x => x :e beta /\ p x) /\ forall x, x /:e beta -> ~(x :e beta /\ p x).
  apply andI.
  + prove ordinal beta
     /\ PNo_strict_imv L R beta (fun x => x :e beta /\ p x)
     /\ forall gamma :e beta,
         forall q:set -> prop, ~PNo_strict_imv L R gamma q.
    apply and3I.
    * exact H1.
    * { apply PNoEq_strict_imv L R beta H1 p (fun x => x :e beta /\ p x).
        - prove PNoEq_ beta p (fun x => x :e beta /\ p x).
          let x. assume Hx: x :e beta.
          prove p x <-> x :e beta /\ p x.
          apply iffI.
          + assume H4. apply andI.
            * exact Hx.
            * exact H4.
          + assume H4. apply H4. assume _ H5. exact H5.
        - exact Hp.
      }
    * let gamma. assume Hc: gamma :e beta. let q.
      assume H4: PNo_strict_imv L R gamma q.
      prove False.
      apply H3 gamma Hc.
      prove exists p:set -> prop, PNo_strict_imv L R gamma p.
      witness q.
      prove PNo_strict_imv L R gamma q.
      exact H4.
  + prove forall x, x /:e beta -> ~(x :e beta /\ p x).
    let x. assume Hx. assume H4. apply H4. assume H5 _. exact Hx H5.
- let q r.
  assume Hq: PNo_least_rep2 L R beta q.
  assume Hr: PNo_least_rep2 L R beta r.
  apply Hq.
  assume Hq1 Hq2.
  apply Hr.
  assume Hr1 Hr2.
  prove q = r.
  apply pred_ext.
  let x.
  apply xm (x :e beta).
  + assume H4: x :e beta.
    prove q x <-> r x.
    apply Hr1. assume Hr1a. apply Hr1a.
    assume _.
    assume Hr1a: PNo_strict_imv L R beta r.
    assume _.
    exact PNo_strict_imv_pred_eq L R HLR beta H1 q r Hq1 Hr1a x H4.
  + assume H4: x /:e beta.
    apply iffI.
    * assume H5: q x. prove False. apply Hq2 x H4. exact H5.
    * assume H5: r x. prove False. apply Hr2 x H4. exact H5.
Qed.

(* Parameter PNo_bd "1b39e85278dd9e820e7b6258957386ac55934d784aa3702c57a28ec807453b01" "ed76e76de9b58e621daa601cca73b4159a437ba0e73114924cb92ec8044f2aa2" *)
Definition PNo_bd : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set
 := fun L R => DescrR_i_io_1 (PNo_least_rep2 L R).

(* Parameter PNo_pred "be07c39b18a3aa93f066f4c064fee3941ec27cfd07a4728b6209135c77ce5704" "b2d51dcfccb9527e9551b0d0c47d891c9031a1d4ee87bba5a9ae5215025d107a" *)
Definition PNo_pred : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> prop
 := fun L R => DescrR_i_io_2 (PNo_least_rep2 L R).

Theorem PNo_bd_pred_lem : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_least_rep2 L R (PNo_bd L R) (PNo_pred L R).
let L R. assume HLR. let alpha. assume Ha HaL HaR.
exact DescrR_i_io_12
          (PNo_least_rep2 L R)
          (PNo_lenbdd_least_rep2_exuniq2 L R HLR alpha Ha HaL HaR).
Qed.

Theorem PNo_bd_pred : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_least_rep L R (PNo_bd L R) (PNo_pred L R).
let L R. assume HLR. let alpha. assume Ha HaL HaR.
apply PNo_bd_pred_lem L R HLR alpha Ha HaL HaR.
assume H _. exact H.
Qed.

Theorem PNo_bd_In : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_bd L R :e ordsucc alpha.
let L R. assume HLR. let alpha. assume Ha HaL HaR.
apply PNo_bd_pred L R HLR alpha Ha HaL HaR.
assume H1. apply H1.
assume H1: ordinal (PNo_bd L R).
assume H2: PNo_strict_imv L R (PNo_bd L R) (PNo_pred L R).
assume H3: forall gamma :e PNo_bd L R,
           forall q:set -> prop, ~PNo_strict_imv L R gamma q.
apply PNo_lenbdd_strict_imv_ex L R HLR alpha Ha HaL HaR.
let beta. assume H4. apply H4.
assume Hb: beta :e ordsucc alpha.
assume H4. apply H4.
let p. assume Hp: PNo_strict_imv L R beta p.
claim Lsa: ordinal (ordsucc alpha).
{ exact ordinal_ordsucc alpha Ha. }
apply ordinal_In_Or_Subq (PNo_bd L R) (ordsucc alpha) H1 Lsa.
- assume H4: PNo_bd L R :e ordsucc alpha. exact H4.
- assume H4: ordsucc alpha c= PNo_bd L R.
  prove False.
  claim Lb: beta :e PNo_bd L R.
  { apply H4. exact Hb. }
  apply H3 beta Lb p.
  exact Hp.
Qed.

Opaque DescrR_i_io_1.
Opaque DescrR_i_io_2.
Opaque PNoLt.
Opaque PNo_downc.
Opaque PNo_upc.
Opaque PNo_rel_strict_upperbd.
Opaque PNo_rel_strict_lowerbd.
Opaque PNo_rel_strict_imv.
Opaque PNo_rel_strict_uniq_imv.
Opaque PNo_least_rep2.
Opaque PNo_bd.
Opaque PNo_pred.
