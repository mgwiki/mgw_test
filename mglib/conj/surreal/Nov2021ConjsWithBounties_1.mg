(** $I sig/Nov2021ConjPreamble.mgs **)

(** Conj_ZF_UPair_closed__1__1 TMRiWfwZrGZRqqLu4PMvcC1SGNsi55EAL7o bounty of about 25 bars **)
Section Conj_ZF_UPair_closed__1__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: z :e UPair x y.
Theorem Conj_ZF_UPair_closed__1__1: If_i (x :e Empty) x y :e Repl (Power (Power x)) (fun w:set => If_i (x :e w) x y) -> z :e Repl (Power (Power x)) (fun w:set => If_i (x :e w) x y).
Admitted.

End Conj_ZF_UPair_closed__1__1.
(** Conj_ZF_UPair_closed__5__1 TMaKuZgYoxjnJZ4Wuj7xF141Rxsgr8YPNL9 bounty of about 25 bars **)
Section Conj_ZF_UPair_closed__5__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ZF_closed x.
Hypothesis H2: z :e x.
Theorem Conj_ZF_UPair_closed__5__1: Repl (Power (Power y)) (fun w:set => If_i (y :e w) y z) = UPair y z -> UPair y z :e x.
Admitted.

End Conj_ZF_UPair_closed__5__1.
(** Conj_ordinal_ordsucc_In_eq__1__1 TMZCED7PCCQYHAZMjpTYoEJYVQDV8dHMvdh bounty of about 25 bars **)
Section Conj_ordinal_ordsucc_In_eq__1__1.
Variable x:set.
Variable y:set.
Hypothesis H0: ordinal x.
Theorem Conj_ordinal_ordsucc_In_eq__1__1: ordinal (ordsucc y) -> ordsucc y :e x \/ x = ordsucc y.
Admitted.

End Conj_ordinal_ordsucc_In_eq__1__1.
(** Conj_ordinal_famunion__2__0 TMJimBpWJPHahokERpFVVLW5CYscT9BPAMs bounty of about 25 bars **)
Section Conj_ordinal_famunion__2__0.
Variable x:set.
Variable f:(set -> set).
Variable y:set.
Variable z:set.
Hypothesis H1: z :e x.
Hypothesis H2: y :e f z.
Theorem Conj_ordinal_famunion__2__0: ordinal (f z) -> TransSet y.
Admitted.

End Conj_ordinal_famunion__2__0.
(** Conj_KnasterTarski_set__3__0 TMTN8gEBmZAHcVLDs3TPLxhWfwYgXqpCcwE bounty of about 25 bars **)
Section Conj_KnasterTarski_set__3__0.
Variable x:set.
Variable f:(set -> set).
Hypothesis H1: Sep x (fun y:set => forall z:set, z :e Power x -> Subq (f z) z -> y :e z) :e Power x.
Hypothesis H2: f (Sep x (fun y:set => forall z:set, z :e Power x -> Subq (f z) z -> y :e z)) :e Power x.
Hypothesis H3: (forall y:set, y :e Power x -> Subq (f y) y -> Subq (Sep x (fun z:set => forall w:set, w :e Power x -> Subq (f w) w -> z :e w)) y).
Hypothesis H4: Subq (f (Sep x (fun y:set => forall z:set, z :e Power x -> Subq (f z) z -> y :e z))) (Sep x (fun y:set => forall z:set, z :e Power x -> Subq (f z) z -> y :e z)).
Theorem Conj_KnasterTarski_set__3__0: Subq (f (f (Sep x (fun y:set => forall z:set, z :e Power x -> Subq (f z) z -> y :e z)))) (f (Sep x (fun y:set => forall z:set, z :e Power x -> Subq (f z) z -> y :e z))) -> (exists y:set, y :e Power x /\ f y = y).
Admitted.

End Conj_KnasterTarski_set__3__0.
(** Conj_KnasterTarski_set__4__0 TMLnrrDkmqrBbqmF3ezkji7rXkTCqVBhSXd bounty of about 25 bars **)
Section Conj_KnasterTarski_set__4__0.
Variable x:set.
Variable f:(set -> set).
Hypothesis H1: Sep x (fun y:set => forall z:set, z :e Power x -> Subq (f z) z -> y :e z) :e Power x.
Hypothesis H2: f (Sep x (fun y:set => forall z:set, z :e Power x -> Subq (f z) z -> y :e z)) :e Power x.
Hypothesis H3: (forall y:set, y :e Power x -> Subq (f y) y -> Subq (Sep x (fun z:set => forall w:set, w :e Power x -> Subq (f w) w -> z :e w)) y).
Theorem Conj_KnasterTarski_set__4__0: Subq (f (Sep x (fun y:set => forall z:set, z :e Power x -> Subq (f z) z -> y :e z))) (Sep x (fun y:set => forall z:set, z :e Power x -> Subq (f z) z -> y :e z)) -> (exists y:set, y :e Power x /\ f y = y).
Admitted.

End Conj_KnasterTarski_set__4__0.
(** Conj_SchroederBernstein__3__3 TMKiPykZFC3QousKfBFHUgTgsLHCrirmDkq bounty of about 25 bars **)
Section Conj_SchroederBernstein__3__3.
Variable x:set.
Variable y:set.
Variable f:(set -> set).
Variable f2:(set -> set).
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, x2 :e y -> (forall y2:set, y2 :e y -> f2 x2 = f2 y2 -> x2 = y2)).
Hypothesis H1: (fun x2:set => Repl (setminus y (Repl (setminus x x2) (fun y2:set => f y2))) (fun y2:set => f2 y2)) z = z.
Hypothesis H2: w = f2 v.
Hypothesis H4: u :e z.
Theorem Conj_SchroederBernstein__3__3: u :e Repl (setminus y (Repl (setminus x z) f)) f2 -> inv y f2 w = inv y f2 u -> w = u.
Admitted.

End Conj_SchroederBernstein__3__3.
(** Conj_PigeonHole_nat__1__0 TMY6v5YLkAD1d4QmaWZ9fBv1YhzzzzQ1XUJ bounty of about 25 bars **)
Section Conj_PigeonHole_nat__1__0.
Variable x:set.
Variable f:(set -> set).
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H1: z :e ordsucc (ordsucc x).
Hypothesis H2: ordsucc w :e ordsucc (ordsucc x).
Hypothesis H3: ~ Subq y z.
Hypothesis H4: Subq y w.
Hypothesis H5: f z = f (ordsucc w).
Theorem Conj_PigeonHole_nat__1__0: z <> ordsucc w.
Admitted.

End Conj_PigeonHole_nat__1__0.
(** Conj_PigeonHole_nat__5__1 TMVNArkhAjey8vvB2gCaVbmjaagwcyLiKYJ bounty of about 25 bars **)
Section Conj_PigeonHole_nat__5__1.
Variable x:set.
Variable f:(set -> set).
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: nat_p x.
Hypothesis H2: z :e ordsucc x.
Hypothesis H3: w :e ordsucc x.
Hypothesis H4: z :e ordsucc (ordsucc x).
Theorem Conj_PigeonHole_nat__5__1: ordsucc z :e ordsucc (ordsucc x) -> If_i (Subq y z) (f (ordsucc z)) (f z) = If_i (Subq y w) (f (ordsucc w)) (f w) -> z = w.
Admitted.

End Conj_PigeonHole_nat__5__1.
(** Conj_PigeonHole_nat_bij__2__2 TMRBHaXMizXz3nGHf4Ci1rJ5HnrVvffoWRX bounty of about 25 bars **)
Section Conj_PigeonHole_nat_bij__2__2.
Variable x:set.
Variable f:(set -> set).
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e x -> (forall v:set, v :e x -> f u = f v -> u = v)).
Hypothesis H1: ~ (exists u:set, u :e x /\ f u = y).
Hypothesis H3: w :e ordsucc x.
Theorem Conj_PigeonHole_nat_bij__2__2: (z <> x -> z :e x) -> If_i (z = x) y (f z) = If_i (w = x) y (f w) -> z = w.
Admitted.

End Conj_PigeonHole_nat_bij__2__2.
(** Conj_finite_ind__2__4 TMFUphzWSx8aKB1kaSnJBNNwYBgscuJiQRf bounty of about 25 bars **)
Section Conj_finite_ind__2__4.
Variable p:(set -> prop).
Variable x:set.
Variable y:set.
Variable f:(set -> set).
Hypothesis H0: (forall z:set, forall w:set, finite z -> nIn w z -> p z -> p (binunion z (Sing w))).
Hypothesis H1: nat_p x.
Hypothesis H2: (forall z:set, equip z x -> p z).
Hypothesis H3: (forall z:set, z :e ordsucc x -> f z :e y).
Hypothesis H5: (forall z:set, z :e y -> (exists w:set, w :e ordsucc x /\ f w = z)).
Theorem Conj_finite_ind__2__4: y = binunion (Repl x f) (Sing (f x)) -> p y.
Admitted.

End Conj_finite_ind__2__4.
(** Conj_Descr_Vo1_prop__1__1 TMJEbBAX7t489skSyDBk87B3VJq3fD9y9y5 bounty of about 25 bars **)
Section Conj_Descr_Vo1_prop__1__1.
Variable P:((set -> prop) -> prop).
Variable p:(set -> prop).
Hypothesis H0: (forall q:set -> prop, forall p2:set -> prop, P q -> P p2 -> q = p2).
Theorem Conj_Descr_Vo1_prop__1__1: p = Descr_Vo1 P -> P (Descr_Vo1 P).
Admitted.

End Conj_Descr_Vo1_prop__1__1.
(** Conj_nat_setsum1_ordsucc__1__0 TMMkVv89B6dVBXNwMmBjyF8JAxVrG367z1V bounty of about 25 bars **)
Section Conj_nat_setsum1_ordsucc__1__0.
Variable x:set.
Variable y:set.
Hypothesis H1: x = ordsucc y.
Theorem Conj_nat_setsum1_ordsucc__1__0: y :e x -> ordsucc y :e Inj1 x.
Admitted.

End Conj_nat_setsum1_ordsucc__1__0.
(** Conj_PNoLt_trichotomy_or__6__2 TMGdSYRypREbaCMjdgDuCTtKdaRoH3nfknc bounty of about 25 bars **)
Section Conj_PNoLt_trichotomy_or__6__2.
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Hypothesis H0: TransSet y.
Hypothesis H1: PNoEq_ (binintersect x y) p q.
Theorem Conj_PNoLt_trichotomy_or__6__2: binintersect x y = x -> PNoLt x p y q \/ x = y /\ PNoEq_ x p q \/ PNoLt y q x p.
Admitted.

End Conj_PNoLt_trichotomy_or__6__2.
(** Conj_PNoLt_trichotomy_or__7__2 TMGAPyaWQWbvFHmMnj2nVubcV9WdEQYbgEg bounty of about 25 bars **)
Section Conj_PNoLt_trichotomy_or__7__2.
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal y.
Hypothesis H3: TransSet y.
Theorem Conj_PNoLt_trichotomy_or__7__2: ordinal (binintersect x y) -> PNoLt x p y q \/ x = y /\ PNoEq_ x p q \/ PNoLt y q x p.
Admitted.

End Conj_PNoLt_trichotomy_or__7__2.
(** Conj_PNoLt_tra__1__0 TMP2S2f7eN72k7Ft9eqBGUwGr685mV2iun8 bounty of about 25 bars **)
Section Conj_PNoLt_tra__1__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Variable p2:(set -> prop).
Variable w:set.
Hypothesis H1: ordinal y.
Hypothesis H2: TransSet z.
Hypothesis H3: PNoEq_ x p q.
Hypothesis H4: q x.
Hypothesis H5: w :e y.
Hypothesis H6: w :e z.
Hypothesis H7: PNoEq_ w q p2.
Hypothesis H8: ~ q w.
Hypothesis H9: p2 w.
Theorem Conj_PNoLt_tra__1__0: ordinal w -> PNoLt x p z p2.
Admitted.

End Conj_PNoLt_tra__1__0.
(** Conj_PNoLt_tra__2__12 TMbsKqES3JZ25sb39E5FLWXfezbnLFGPCif bounty of about 25 bars **)
Section Conj_PNoLt_tra__2__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Variable p2:(set -> prop).
Variable w:set.
Variable u:set.
Hypothesis H0: ordinal y.
Hypothesis H1: TransSet x.
Hypothesis H2: TransSet z.
Hypothesis H3: w :e x.
Hypothesis H4: PNoEq_ w p q.
Hypothesis H5: ~ p w.
Hypothesis H6: q w.
Hypothesis H7: ordinal w.
Hypothesis H8: u :e y.
Hypothesis H9: u :e z.
Hypothesis H10: PNoEq_ u q p2.
Hypothesis H11: ~ q u.
Theorem Conj_PNoLt_tra__2__12: ordinal u -> PNoLt x p z p2.
Admitted.

End Conj_PNoLt_tra__2__12.
(** Conj_PNoLe_tra__1__0 TMZo1t6fSzg6H75vQLBhtHhzmjjdKUHaJa8 bounty of about 25 bars **)
Section Conj_PNoLe_tra__1__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Variable p2:(set -> prop).
Hypothesis H1: ordinal z.
Hypothesis H2: PNoLe y q z p2.
Hypothesis H3: x = y.
Hypothesis H4: PNoEq_ x p q.
Theorem Conj_PNoLe_tra__1__0: PNoEq_ y p q -> PNoLe y p z p2.
Admitted.

End Conj_PNoLe_tra__1__0.
(** Conj_PNo_rel_strict_upperbd_antimon__6__1 TMcET1NKGkLLHZkqeXZ6wrGiUNehBwPcHQV bounty of about 25 bars **)
Section Conj_PNo_rel_strict_upperbd_antimon__6__1.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H2: TransSet x.
Theorem Conj_PNo_rel_strict_upperbd_antimon__6__1: ordinal y -> (forall z:set, z :e x -> (forall q:set -> prop, PNo_downc P z q -> PNoLt z q x p)) -> (forall z:set, z :e y -> (forall q:set -> prop, PNo_downc P z q -> PNoLt z q y p)).
Admitted.

End Conj_PNo_rel_strict_upperbd_antimon__6__1.
(** Conj_PNo_rel_strict_upperbd_antimon__6__2 TMJywbFerFTHWRLM6wsuE5PWHEc8X7X8P6z bounty of about 25 bars **)
Section Conj_PNo_rel_strict_upperbd_antimon__6__2.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H1: y :e x.
Theorem Conj_PNo_rel_strict_upperbd_antimon__6__2: ordinal y -> (forall z:set, z :e x -> (forall q:set -> prop, PNo_downc P z q -> PNoLt z q x p)) -> (forall z:set, z :e y -> (forall q:set -> prop, PNo_downc P z q -> PNoLt z q y p)).
Admitted.

End Conj_PNo_rel_strict_upperbd_antimon__6__2.
(** Conj_PNo_rel_strict_lowerbd_antimon__4__0 TMZeqeGZKBwUwRbq92ceL6K1Vmtb5irrQst bounty of about 25 bars **)
Section Conj_PNo_rel_strict_lowerbd_antimon__4__0.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable z:set.
Variable q:(set -> prop).
Hypothesis H1: TransSet x.
Hypothesis H2: TransSet y.
Hypothesis H3: (forall w:set, w :e x -> (forall p2:set -> prop, PNo_upc P w p2 -> PNoLt x p w p2)).
Hypothesis H4: z :e y.
Hypothesis H5: PNo_upc P z q.
Theorem Conj_PNo_rel_strict_lowerbd_antimon__4__0: z :e x -> PNoLt y p z q.
Admitted.

End Conj_PNo_rel_strict_lowerbd_antimon__4__0.
(** Conj_PNo_rel_imv_ex__4__9 TMPkhVJkFy9Ms7gkgDoFpsQKxepoVTDKUxj bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__4__9.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Variable z:set.
Hypothesis H0: ordinal x.
Hypothesis H1: (forall w:set, w :e x -> (forall p2:set -> prop, PNo_upc P w p2 -> PNoLt x p w p2)).
Hypothesis H2: PNoEq_ x p (fun w:set => p w \/ w = x).
Hypothesis H3: PNo_upc P y q.
Hypothesis H4: ordinal y.
Hypothesis H5: y = x.
Hypothesis H6: z :e x.
Hypothesis H7: PNoEq_ z q (fun w:set => p w \/ w = x).
Hypothesis H8: ~ q z.
Theorem Conj_PNo_rel_imv_ex__4__9: ordinal z -> PNoLt (ordsucc x) (fun w:set => p w \/ w = x) x q.
Admitted.

End Conj_PNo_rel_imv_ex__4__9.
(** Conj_PNo_rel_imv_ex__7__0 TMUqnU2Yz3CfJbQ6v5hbWEn8MujYPvVExsP bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__7__0.
Variable x:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Variable y:set.
Hypothesis H1: PNoEq_ x p (fun z:set => p z \/ z = x).
Hypothesis H2: y :e x.
Hypothesis H3: PNoEq_ y (fun z:set => p z \/ z = x) q.
Hypothesis H4: ~ (p y \/ y = x).
Hypothesis H5: ordinal y.
Hypothesis H6: PNoLt y q x p.
Theorem Conj_PNo_rel_imv_ex__7__0: ~ PNoLt x p y q.
Admitted.

End Conj_PNo_rel_imv_ex__7__0.
(** Conj_PNo_rel_imv_ex__7__3 TMMECdQEe62jktMZnRd6z9ZFpoDkuuVcofU bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__7__3.
Variable x:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H1: PNoEq_ x p (fun z:set => p z \/ z = x).
Hypothesis H2: y :e x.
Hypothesis H4: ~ (p y \/ y = x).
Hypothesis H5: ordinal y.
Hypothesis H6: PNoLt y q x p.
Theorem Conj_PNo_rel_imv_ex__7__3: ~ PNoLt x p y q.
Admitted.

End Conj_PNo_rel_imv_ex__7__3.
(** Conj_PNo_rel_imv_ex__7__4 TMQfmyfL9TveWvprJ64AKc7umWBsurN1bf3 bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__7__4.
Variable x:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H1: PNoEq_ x p (fun z:set => p z \/ z = x).
Hypothesis H2: y :e x.
Hypothesis H3: PNoEq_ y (fun z:set => p z \/ z = x) q.
Hypothesis H5: ordinal y.
Hypothesis H6: PNoLt y q x p.
Theorem Conj_PNo_rel_imv_ex__7__4: ~ PNoLt x p y q.
Admitted.

End Conj_PNo_rel_imv_ex__7__4.
(** Conj_PNo_rel_imv_ex__15__3 TMdaA3PkxB8s49rta6HPT6QuMuNfzfAR39H bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__15__3.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Hypothesis H0: ~ (exists q:set -> prop, PNo_rel_strict_uniq_imv P Q x q).
Hypothesis H1: x = ordsucc y.
Hypothesis H2: ordinal y.
Hypothesis H4: binintersect y (ordsucc y) = y.
Hypothesis H5: binintersect (ordsucc y) y = y.
Hypothesis H6: (forall z:set, z :e y -> (forall q:set -> prop, PNo_downc P z q -> PNoLt z q y p)).
Hypothesis H7: (forall z:set, z :e y -> (forall q:set -> prop, PNo_upc Q z q -> PNoLt y p z q)).
Hypothesis H8: (forall q:set -> prop, PNo_rel_strict_imv P Q y q -> PNoEq_ y p q).
Hypothesis H9: PNoEq_ y p (fun z:set => p z \/ z = y).
Hypothesis H10: PNoLt y p (ordsucc y) (fun z:set => p z \/ z = y).
Hypothesis H11: ~ (PNo_rel_strict_imv P Q x (fun z:set => p z /\ z <> y) /\ PNo_rel_strict_imv P Q x (fun z:set => p z \/ z = y)).
Hypothesis H12: (forall q:set -> prop, PNo_upc Q y q -> ~ PNoEq_ y p q).
Theorem Conj_PNo_rel_imv_ex__15__3: ~ PNo_rel_strict_imv P Q (ordsucc y) (fun z:set => p z \/ z = y).
Admitted.

End Conj_PNo_rel_imv_ex__15__3.
(** Conj_PNo_rel_imv_ex__15__11 TMcFGbZa7n4xC3Kk7XJMkVTM2TQtc9TDmND bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__15__11.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Hypothesis H0: ~ (exists q:set -> prop, PNo_rel_strict_uniq_imv P Q x q).
Hypothesis H1: x = ordsucc y.
Hypothesis H2: ordinal y.
Hypothesis H3: ordinal (ordsucc y).
Hypothesis H4: binintersect y (ordsucc y) = y.
Hypothesis H5: binintersect (ordsucc y) y = y.
Hypothesis H6: (forall z:set, z :e y -> (forall q:set -> prop, PNo_downc P z q -> PNoLt z q y p)).
Hypothesis H7: (forall z:set, z :e y -> (forall q:set -> prop, PNo_upc Q z q -> PNoLt y p z q)).
Hypothesis H8: (forall q:set -> prop, PNo_rel_strict_imv P Q y q -> PNoEq_ y p q).
Hypothesis H9: PNoEq_ y p (fun z:set => p z \/ z = y).
Hypothesis H10: PNoLt y p (ordsucc y) (fun z:set => p z \/ z = y).
Hypothesis H12: (forall q:set -> prop, PNo_upc Q y q -> ~ PNoEq_ y p q).
Theorem Conj_PNo_rel_imv_ex__15__11: ~ PNo_rel_strict_imv P Q (ordsucc y) (fun z:set => p z \/ z = y).
Admitted.

End Conj_PNo_rel_imv_ex__15__11.
(** Conj_PNo_rel_imv_ex__16__2 TMP1ZTggZrEcrc8QArKuhb2NVS3udxnaFfT bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__16__2.
Variable x:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H1: PNoEq_ x (fun z:set => p z /\ z <> x) p.
Hypothesis H3: PNoEq_ y q (fun z:set => p z /\ z <> x).
Hypothesis H4: p y /\ y <> x.
Hypothesis H5: ordinal y.
Hypothesis H6: PNoLt x p y q.
Theorem Conj_PNo_rel_imv_ex__16__2: ~ PNoLt y q x p.
Admitted.

End Conj_PNo_rel_imv_ex__16__2.
(** Conj_PNo_rel_imv_ex__17__0 TMJHXAcqP2jrpeSxezB2zfZpacvRoMAStkT bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__17__0.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Variable z:set.
Hypothesis H1: (forall w:set, w :e x -> (forall p2:set -> prop, PNo_upc P w p2 -> PNoLt x p w p2)).
Hypothesis H2: PNoEq_ x (fun w:set => p w /\ w <> x) p.
Hypothesis H3: PNo_upc P y q.
Hypothesis H4: ordinal y.
Hypothesis H5: y = x.
Hypothesis H6: z :e x.
Hypothesis H7: PNoEq_ z q (fun w:set => p w /\ w <> x).
Hypothesis H8: ~ q z.
Hypothesis H9: p z /\ z <> x.
Hypothesis H10: ordinal z.
Theorem Conj_PNo_rel_imv_ex__17__0: ~ PNoLt x p z q.
Admitted.

End Conj_PNo_rel_imv_ex__17__0.
(** Conj_PNo_rel_imv_ex__19__3 TMZ4Krnt5Syu2fEJSsAsgwz1hfSqaGNNDUW bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__19__3.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal (ordsucc x).
Hypothesis H2: binintersect x (ordsucc x) = x.
Hypothesis H4: PNoEq_ x (fun z:set => p z /\ z <> x) p.
Hypothesis H5: PNoLt (ordsucc x) (fun z:set => p z /\ z <> x) x p.
Hypothesis H6: y :e ordsucc x.
Hypothesis H7: PNo_upc P y q.
Theorem Conj_PNo_rel_imv_ex__19__3: ordinal y -> PNoLt (ordsucc x) (fun z:set => p z /\ z <> x) y q.
Admitted.

End Conj_PNo_rel_imv_ex__19__3.
(** Conj_PNo_rel_imv_ex__20__5 TMUDoiz2H8EVUYnshq47r2ZTj1j3fmGo66s bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__20__5.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Variable z:set.
Hypothesis H0: ordinal x.
Hypothesis H1: (forall w:set, w :e x -> (forall p2:set -> prop, PNo_downc P w p2 -> PNoLt w p2 x p)).
Hypothesis H2: PNo_downc P y q.
Hypothesis H3: ordinal y.
Hypothesis H4: y = x.
Hypothesis H6: q z.
Hypothesis H7: ordinal z.
Hypothesis H8: PNoLt x p z q.
Theorem Conj_PNo_rel_imv_ex__20__5: PNoLt z q x p -> PNoLt x q (ordsucc x) (fun w:set => p w /\ w <> x).
Admitted.

End Conj_PNo_rel_imv_ex__20__5.
(** Conj_PNo_rel_imv_ex__22__6 TMYo2KqyE14yVRUbzyppxd9PeSZ4hWGzH4k bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__22__6.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Variable z:set.
Hypothesis H0: ordinal x.
Hypothesis H1: (forall w:set, w :e x -> (forall p2:set -> prop, PNo_downc P w p2 -> PNoLt w p2 x p)).
Hypothesis H2: PNoEq_ x (fun w:set => p w /\ w <> x) p.
Hypothesis H3: PNo_downc P y q.
Hypothesis H4: ordinal y.
Hypothesis H5: y = x.
Hypothesis H7: PNoEq_ z (fun w:set => p w /\ w <> x) q.
Hypothesis H8: ~ (p z /\ z <> x).
Hypothesis H9: q z.
Theorem Conj_PNo_rel_imv_ex__22__6: ordinal z -> PNoLt x q (ordsucc x) (fun w:set => p w /\ w <> x).
Admitted.

End Conj_PNo_rel_imv_ex__22__6.
(** Conj_PNo_rel_imv_ex__29__1 TMRjXrmeJcsW4Zp9nEgAZkMWqz8uDRWNfEi bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__29__1.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Hypothesis H0: ~ (exists q:set -> prop, PNo_rel_strict_uniq_imv P Q x q).
Hypothesis H2: ordinal y.
Hypothesis H3: ordinal (ordsucc y).
Hypothesis H4: binintersect y (ordsucc y) = y.
Hypothesis H5: binintersect (ordsucc y) y = y.
Hypothesis H6: (forall z:set, z :e y -> (forall q:set -> prop, PNo_downc P z q -> PNoLt z q y p)).
Hypothesis H7: (forall z:set, z :e y -> (forall q:set -> prop, PNo_upc Q z q -> PNoLt y p z q)).
Hypothesis H8: (forall q:set -> prop, PNo_rel_strict_imv P Q y q -> PNoEq_ y p q).
Hypothesis H9: PNoEq_ y (fun z:set => p z /\ z <> y) p.
Hypothesis H10: PNoLt (ordsucc y) (fun z:set => p z /\ z <> y) y p.
Hypothesis H11: ~ (PNo_rel_strict_imv P Q x (fun z:set => p z /\ z <> y) /\ PNo_rel_strict_imv P Q x (fun z:set => p z \/ z = y)).
Hypothesis H12: (forall q:set -> prop, PNo_downc P y q -> ~ PNoEq_ y p q).
Theorem Conj_PNo_rel_imv_ex__29__1: ~ PNo_rel_strict_imv P Q (ordsucc y) (fun z:set => p z /\ z <> y).
Admitted.

End Conj_PNo_rel_imv_ex__29__1.
(** Conj_PNo_rel_imv_ex__32__9 TMSa3THJvaCmqeT9cm6ArY2DGZB2Njhc7v3 bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__32__9.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Hypothesis H0: PNoLt_pwise (PNo_downc P) (PNo_upc Q).
Hypothesis H1: ~ (exists q:set -> prop, PNo_rel_strict_uniq_imv P Q x q).
Hypothesis H2: ~ (exists z:set, z :e x /\ (exists q:set -> prop, PNo_rel_strict_split_imv P Q z q)).
Hypothesis H3: y :e x.
Hypothesis H4: x = ordsucc y.
Hypothesis H5: ordinal y.
Hypothesis H6: ordinal (ordsucc y).
Hypothesis H7: binintersect y (ordsucc y) = y.
Hypothesis H8: binintersect (ordsucc y) y = y.
Hypothesis H10: (forall z:set, z :e y -> (forall q:set -> prop, PNo_upc Q z q -> PNoLt y p z q)).
Hypothesis H11: (forall q:set -> prop, PNo_rel_strict_imv P Q y q -> PNoEq_ y p q).
Hypothesis H12: PNoEq_ y (fun z:set => p z /\ z <> y) p.
Hypothesis H13: PNoLt (ordsucc y) (fun z:set => p z /\ z <> y) y p.
Hypothesis H14: PNoEq_ y p (fun z:set => p z \/ z = y).
Hypothesis H15: p y \/ y = y.
Theorem Conj_PNo_rel_imv_ex__32__9: ~ PNoLt y p (ordsucc y) (fun z:set => p z \/ z = y).
Admitted.

End Conj_PNo_rel_imv_ex__32__9.
(** Conj_PNo_rel_imv_ex__32__11 TMbTncLNNpNfkERbUjx8kv5pSWrwxxdAwYV bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__32__11.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Hypothesis H0: PNoLt_pwise (PNo_downc P) (PNo_upc Q).
Hypothesis H1: ~ (exists q:set -> prop, PNo_rel_strict_uniq_imv P Q x q).
Hypothesis H2: ~ (exists z:set, z :e x /\ (exists q:set -> prop, PNo_rel_strict_split_imv P Q z q)).
Hypothesis H3: y :e x.
Hypothesis H4: x = ordsucc y.
Hypothesis H5: ordinal y.
Hypothesis H6: ordinal (ordsucc y).
Hypothesis H7: binintersect y (ordsucc y) = y.
Hypothesis H8: binintersect (ordsucc y) y = y.
Hypothesis H9: (forall z:set, z :e y -> (forall q:set -> prop, PNo_downc P z q -> PNoLt z q y p)).
Hypothesis H10: (forall z:set, z :e y -> (forall q:set -> prop, PNo_upc Q z q -> PNoLt y p z q)).
Hypothesis H12: PNoEq_ y (fun z:set => p z /\ z <> y) p.
Hypothesis H13: PNoLt (ordsucc y) (fun z:set => p z /\ z <> y) y p.
Hypothesis H14: PNoEq_ y p (fun z:set => p z \/ z = y).
Hypothesis H15: p y \/ y = y.
Theorem Conj_PNo_rel_imv_ex__32__11: ~ PNoLt y p (ordsucc y) (fun z:set => p z \/ z = y).
Admitted.

End Conj_PNo_rel_imv_ex__32__11.
(** Conj_PNo_rel_imv_ex__37__7 TMcJMYMAiAXtcxRJSe51e3P5atj4uZXxDxB bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__37__7.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Hypothesis H0: PNoLt_pwise (PNo_downc P) (PNo_upc Q).
Hypothesis H1: ~ (exists q:set -> prop, PNo_rel_strict_uniq_imv P Q x q).
Hypothesis H2: ~ (exists z:set, z :e x /\ (exists q:set -> prop, PNo_rel_strict_split_imv P Q z q)).
Hypothesis H3: y :e x.
Hypothesis H4: x = ordsucc y.
Hypothesis H5: ordinal y.
Hypothesis H6: ordinal (ordsucc y).
Hypothesis H8: binintersect (ordsucc y) y = y.
Hypothesis H9: (forall z:set, z :e y -> (forall q:set -> prop, PNo_downc P z q -> PNoLt z q y p)).
Hypothesis H10: (forall z:set, z :e y -> (forall q:set -> prop, PNo_upc Q z q -> PNoLt y p z q)).
Hypothesis H11: (forall q:set -> prop, PNo_rel_strict_imv P Q y q -> PNoEq_ y p q).
Theorem Conj_PNo_rel_imv_ex__37__7: ~ PNoEq_ y (fun z:set => p z /\ z <> y) p.
Admitted.

End Conj_PNo_rel_imv_ex__37__7.
(** Conj_PNo_rel_imv_ex__38__8 TMbM6LC8i8uFLu3U3VFDbweyiHuAPXPBKzH bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__38__8.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Hypothesis H0: PNoLt_pwise (PNo_downc P) (PNo_upc Q).
Hypothesis H1: ~ (exists p:set -> prop, PNo_rel_strict_uniq_imv P Q x p).
Hypothesis H2: ~ (exists z:set, z :e x /\ (exists p:set -> prop, PNo_rel_strict_split_imv P Q z p)).
Hypothesis H3: (forall z:set, z :e x -> (exists p:set -> prop, PNo_rel_strict_uniq_imv P Q z p)).
Hypothesis H4: y :e x.
Hypothesis H5: x = ordsucc y.
Hypothesis H6: ordinal y.
Hypothesis H7: ordinal (ordsucc y).
Theorem Conj_PNo_rel_imv_ex__38__8: binintersect (ordsucc y) y <> y.
Admitted.

End Conj_PNo_rel_imv_ex__38__8.
(** Conj_PNo_rel_imv_ex__39__1 TMaJTxrE2RP1uZqiXFTk3KPKGrdXfrJ6Lp7 bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__39__1.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Hypothesis H0: PNoLt_pwise (PNo_downc P) (PNo_upc Q).
Hypothesis H2: ~ (exists z:set, z :e x /\ (exists p:set -> prop, PNo_rel_strict_split_imv P Q z p)).
Hypothesis H3: (forall z:set, z :e x -> (exists p:set -> prop, PNo_rel_strict_uniq_imv P Q z p)).
Hypothesis H4: y :e x.
Hypothesis H5: x = ordsucc y.
Hypothesis H6: ordinal y.
Hypothesis H7: ordinal (ordsucc y).
Theorem Conj_PNo_rel_imv_ex__39__1: binintersect y (ordsucc y) <> y.
Admitted.

End Conj_PNo_rel_imv_ex__39__1.
(** Conj_PNo_rel_imv_ex__40__5 TMQVSK5chGYgFcx6Ybq4xeT6zLbkzBzTAcj bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__40__5.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Hypothesis H0: PNoLt_pwise (PNo_downc P) (PNo_upc Q).
Hypothesis H1: ordinal x.
Hypothesis H2: ~ (exists p:set -> prop, PNo_rel_strict_uniq_imv P Q x p).
Hypothesis H3: ~ (exists z:set, z :e x /\ (exists p:set -> prop, PNo_rel_strict_split_imv P Q z p)).
Hypothesis H4: (forall z:set, z :e x -> (exists p:set -> prop, PNo_rel_strict_uniq_imv P Q z p)).
Hypothesis H6: x = ordsucc y.
Hypothesis H7: ordinal y.
Theorem Conj_PNo_rel_imv_ex__40__5: ~ ordinal (ordsucc y).
Admitted.

End Conj_PNo_rel_imv_ex__40__5.
(** Conj_PNo_rel_imv_ex__45__7 TMSMeR1ffX7wZjXdhctDSLiu8PCv4wcJV7Q bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__45__7.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Hypothesis H0: TransSet x.
Hypothesis H1: ordinal y.
Hypothesis H2: (forall z:set, z :e y -> z :e x -> PNo_rel_strict_uniq_imv P Q z (fun w:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc w) q -> q w)).
Hypothesis H3: y :e x.
Hypothesis H4: PNo_rel_strict_imv P Q y p.
Hypothesis H5: PNo_rel_strict_upperbd P y p.
Hypothesis H6: PNo_rel_strict_lowerbd Q y p.
Theorem Conj_PNo_rel_imv_ex__45__7: PNoEq_ y (fun z:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z) p -> PNo_rel_strict_imv P Q y (fun z:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z) /\ (forall q:set -> prop, PNo_rel_strict_imv P Q y q -> PNoEq_ y (fun z:set => forall p2:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) p2 -> p2 z) q).
Admitted.

End Conj_PNo_rel_imv_ex__45__7.
(** Conj_PNo_rel_imv_ex__49__2 TMdG6zUPs33QZ9w9NuB9kM5zMdx1CT9RFEG bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__49__2.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Hypothesis H0: PNo_upc Q y p.
Hypothesis H1: ordinal y.
Hypothesis H3: PNoEq_ y p (fun z:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z).
Hypothesis H4: (forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc y) q -> q y).
Hypothesis H5: PNo_rel_strict_lowerbd Q (ordsucc y) (fun z:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z).
Theorem Conj_PNo_rel_imv_ex__49__2: PNoLt (ordsucc y) (fun z:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z) y p -> PNoLt x (fun z:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z) y p.
Admitted.

End Conj_PNo_rel_imv_ex__49__2.
(** Conj_PNo_rel_imv_ex__54__4 TMLjymvpMEP9p77j9wc3pY7XjBEiBhjdWyp bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__54__4.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Hypothesis H0: (forall w:set, w :e x -> ordsucc w :e x).
Hypothesis H1: (forall w:set, w :e x -> PNo_rel_strict_uniq_imv P Q w (fun u:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc u) q -> q u)).
Hypothesis H2: PNo_upc Q y p.
Hypothesis H3: ordinal y.
Hypothesis H5: z :e x.
Hypothesis H6: PNoEq_ z p (fun w:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc w) q -> q w).
Hypothesis H7: ~ p z.
Hypothesis H8: (forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z).
Theorem Conj_PNo_rel_imv_ex__54__4: ordinal z -> PNoLt x (fun w:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc w) q -> q w) y p.
Admitted.

End Conj_PNo_rel_imv_ex__54__4.
(** Conj_PNo_rel_imv_ex__58__3 TMXsABnafy262JXapKahHoNdMf1hQwMdh71 bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__58__3.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal (ordsucc x).
Hypothesis H2: PNo_rel_strict_imv P Q (ordsucc x) p.
Hypothesis H4: p y.
Hypothesis H5: (forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc y) q -> PNoEq_ (ordsucc y) (fun z:set => forall p2:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) p2 -> p2 z) q).
Theorem Conj_PNo_rel_imv_ex__58__3: PNoEq_ (ordsucc y) (fun z:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z) p -> (forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc y) q -> q y).
Admitted.

End Conj_PNo_rel_imv_ex__58__3.
(** Conj_PNo_rel_imv_ex__62__6 TMZ1CZUr9oZDmUpi9P6Y1JMLDXLAtHAN1sq bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__62__6.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Variable z:set.
Hypothesis H0: TransSet x.
Hypothesis H1: (forall w:set, w :e x -> ordsucc w :e x).
Hypothesis H2: (forall w:set, w :e x -> PNo_rel_strict_uniq_imv P Q w (fun u:set => forall p2:set -> prop, PNo_rel_strict_imv P Q (ordsucc u) p2 -> p2 u)).
Hypothesis H3: y :e x.
Hypothesis H4: ordinal y.
Hypothesis H5: ordinal (ordsucc y).
Hypothesis H7: PNo_rel_strict_imv P Q (ordsucc y) q.
Hypothesis H8: z :e y.
Hypothesis H9: ~ p z.
Hypothesis H10: q z.
Theorem Conj_PNo_rel_imv_ex__62__6: z :e x -> q y.
Admitted.

End Conj_PNo_rel_imv_ex__62__6.
(** Conj_PNo_rel_imv_ex__64__8 TMVSk81mccW1NNMSJtNsBrXmaBcmnqAuQvW bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__64__8.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Hypothesis H0: TransSet x.
Hypothesis H1: (forall z:set, z :e x -> ordsucc z :e x).
Hypothesis H2: (forall z:set, z :e x -> PNo_rel_strict_uniq_imv P Q z (fun w:set => forall p2:set -> prop, PNo_rel_strict_imv P Q (ordsucc w) p2 -> p2 w)).
Hypothesis H3: y :e x.
Hypothesis H4: PNo_downc P y p.
Hypothesis H5: ordinal y.
Hypothesis H6: ordinal (ordsucc y).
Hypothesis H7: PNoEq_ y (fun z:set => forall p2:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) p2 -> p2 z) p.
Hypothesis H9: PNo_rel_strict_upperbd P (ordsucc y) q.
Theorem Conj_PNo_rel_imv_ex__64__8: PNoLt y p (ordsucc y) q -> q y.
Admitted.

End Conj_PNo_rel_imv_ex__64__8.
(** Conj_PNo_rel_imv_ex__65__3 TMXsABnafy262JXapKahHoNdMf1hQwMdh71 bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__65__3.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal (ordsucc x).
Hypothesis H2: PNo_rel_strict_imv P Q (ordsucc x) p.
Hypothesis H4: p y.
Hypothesis H5: (forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc y) q -> PNoEq_ (ordsucc y) (fun z:set => forall p2:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) p2 -> p2 z) q).
Theorem Conj_PNo_rel_imv_ex__65__3: PNoEq_ (ordsucc y) (fun z:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z) p -> (forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc y) q -> q y).
Admitted.

End Conj_PNo_rel_imv_ex__65__3.
(** Conj_PNo_rel_imv_ex__68__8 TMNr25UtU3bGKrNRzZ9a1G9dTQcmv7z44ah bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__68__8.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Variable z:set.
Hypothesis H0: (forall w:set, w :e x -> ordsucc w :e x).
Hypothesis H1: (forall w:set, w :e x -> PNo_rel_strict_uniq_imv P Q w (fun u:set => forall p2:set -> prop, PNo_rel_strict_imv P Q (ordsucc u) p2 -> p2 u)).
Hypothesis H2: PNoEq_ y (fun w:set => forall p2:set -> prop, PNo_rel_strict_imv P Q (ordsucc w) p2 -> p2 w) p.
Hypothesis H3: ordinal y.
Hypothesis H4: ordinal (ordsucc y).
Hypothesis H5: PNo_rel_strict_imv P Q (ordsucc y) q.
Hypothesis H6: z :e y.
Hypothesis H7: ~ p z.
Hypothesis H9: z :e x.
Theorem Conj_PNo_rel_imv_ex__68__8: ordsucc z :e x -> q y.
Admitted.

End Conj_PNo_rel_imv_ex__68__8.
(** Conj_PNo_rel_imv_ex__71__8 TMcyfwW5fwja3EhvFF2VMY3PzBkQqpzC9re bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__71__8.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Variable q:(set -> prop).
Hypothesis H0: TransSet x.
Hypothesis H1: (forall w:set, w :e x -> ordsucc w :e x).
Hypothesis H2: (forall w:set, w :e x -> PNo_rel_strict_uniq_imv P Q w (fun u:set => forall p2:set -> prop, PNo_rel_strict_imv P Q (ordsucc u) p2 -> p2 u)).
Hypothesis H3: PNo_downc P y p.
Hypothesis H4: ordinal y.
Hypothesis H5: z :e x.
Hypothesis H6: z :e y.
Hypothesis H7: PNoEq_ z (fun w:set => forall p2:set -> prop, PNo_rel_strict_imv P Q (ordsucc w) p2 -> p2 w) p.
Hypothesis H9: ordinal z.
Hypothesis H10: ordinal (ordsucc z).
Hypothesis H11: PNo_rel_strict_imv P Q (ordsucc z) q.
Hypothesis H12: PNo_rel_strict_upperbd P (ordsucc z) q.
Theorem Conj_PNo_rel_imv_ex__71__8: PNoLt z p (ordsucc z) q -> q z.
Admitted.

End Conj_PNo_rel_imv_ex__71__8.
(** Conj_PNo_rel_imv_ex__73__4 TMTZNeDzxBf2Paf1Ak1kw7jGphtHhn12HUc bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__73__4.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Hypothesis H0: TransSet x.
Hypothesis H1: (forall w:set, w :e x -> ordsucc w :e x).
Hypothesis H2: (forall w:set, w :e x -> PNo_rel_strict_uniq_imv P Q w (fun u:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc u) q -> q u)).
Hypothesis H3: PNo_downc P y p.
Hypothesis H5: z :e x.
Hypothesis H6: z :e y.
Hypothesis H7: PNoEq_ z (fun w:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc w) q -> q w) p.
Hypothesis H8: ~ (forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z).
Hypothesis H9: p z.
Theorem Conj_PNo_rel_imv_ex__73__4: ordinal z -> PNoLt y p x (fun w:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc w) q -> q w).
Admitted.

End Conj_PNo_rel_imv_ex__73__4.
(** Conj_PNo_rel_imv_ex__75__0 TMcYEpLRNq6iyc94Ea8qin2z3nWN7gRtU4E bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__75__0.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Hypothesis H1: TransSet x.
Hypothesis H2: (forall z:set, z :e x -> ordsucc z :e x).
Hypothesis H3: (forall z:set, z :e x -> PNo_rel_strict_uniq_imv P Q z (fun w:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc w) q -> q w)).
Hypothesis H4: y :e x.
Hypothesis H5: PNo_downc P y p.
Theorem Conj_PNo_rel_imv_ex__75__0: ordinal y -> PNoLt y p x (fun z:set => forall q:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) q -> q z).
Admitted.

End Conj_PNo_rel_imv_ex__75__0.
(** Conj_PNo_rel_imv_ex__77__2 TMRhqLyJ5fYxZwYa4CqwpZhTBg3fFGZvY2n bounty of about 25 bars **)
Section Conj_PNo_rel_imv_ex__77__2.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Hypothesis H0: ordinal x.
Hypothesis H1: TransSet x.
Hypothesis H3: (forall y:set, y :e x -> (exists p:set -> prop, PNo_rel_strict_uniq_imv P Q y p)).
Hypothesis H4: (forall y:set, y :e x -> ordsucc y :e x).
Theorem Conj_PNo_rel_imv_ex__77__2: ~ (forall y:set, ordinal y -> y :e x -> PNo_rel_strict_uniq_imv P Q y (fun z:set => forall p:set -> prop, PNo_rel_strict_imv P Q (ordsucc z) p -> p z)).
Admitted.

End Conj_PNo_rel_imv_ex__77__2.
(** Conj_PNo_lenbdd_strict_imv_extend0__3__3 TMHFSDDLMoqRPaTU6EkA9DePhT8cdJWQ6H4 bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend0__3__3.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: PNo_lenbdd x P.
Hypothesis H2: PNo_rel_strict_lowerbd P x p.
Hypothesis H4: PNoEq_ x p (fun z:set => p z /\ z <> x).
Hypothesis H5: y :e ordsucc x.
Hypothesis H6: PNo_upc P y q.
Theorem Conj_PNo_lenbdd_strict_imv_extend0__3__3: ordinal y -> PNoLt (ordsucc x) (fun z:set => p z /\ z <> x) y q.
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend0__3__3.
(** Conj_PNo_lenbdd_strict_imv_extend0__4__2 TMKoYkwGP2qYik5hxqWGwirkimZ9JarWCPu bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend0__4__2.
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Variable z:set.
Hypothesis H0: ordinal x.
Hypothesis H1: TransSet x.
Hypothesis H3: y :e x.
Hypothesis H4: z :e y.
Theorem Conj_PNo_lenbdd_strict_imv_extend0__4__2: z :e x -> PNoEq_ z (fun w:set => p w /\ w <> x) q /\ ~ (p z /\ z <> x) /\ q z -> PNoLt x p y q.
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend0__4__2.
(** Conj_PNo_lenbdd_strict_imv_extend0__5__0 TMJjZGcGRQQ2Ce13nNH5rvihU47HrNvukAc bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend0__5__0.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H1: TransSet x.
Hypothesis H2: PNo_rel_strict_upperbd P x p.
Hypothesis H3: ordinal (ordsucc x).
Hypothesis H4: PNoEq_ x p (fun z:set => p z /\ z <> x).
Hypothesis H5: ordinal y.
Hypothesis H6: y :e x.
Hypothesis H7: y :e ordsucc x.
Hypothesis H8: PNo_downc P y q.
Theorem Conj_PNo_lenbdd_strict_imv_extend0__5__0: PNoLt y q x p -> PNoLt y q (ordsucc x) (fun z:set => p z /\ z <> x).
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend0__5__0.
(** Conj_PNo_lenbdd_strict_imv_extend0__6__7 TMUBiU1chGGXj36SUYxwP6wggWDbLFNXhKn bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend0__6__7.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: TransSet x.
Hypothesis H2: PNo_rel_strict_upperbd P x p.
Hypothesis H3: ordinal (ordsucc x).
Hypothesis H4: PNoEq_ x p (fun z:set => p z /\ z <> x).
Hypothesis H5: ordinal y.
Hypothesis H6: P y q.
Hypothesis H8: y :e ordsucc x.
Theorem Conj_PNo_lenbdd_strict_imv_extend0__6__7: PNo_downc P y q -> PNoLt y q (ordsucc x) (fun z:set => p z /\ z <> x).
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend0__6__7.
(** Conj_PNo_lenbdd_strict_imv_extend0__9__0 TMdEFEo47d5rFP7v9XENqvQhExHMXarWWA6 bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend0__9__0.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H1: TransSet x.
Hypothesis H2: PNo_lenbdd x P.
Hypothesis H3: PNo_rel_strict_upperbd P x p.
Hypothesis H4: ordinal (ordsucc x).
Hypothesis H5: PNoEq_ x p (fun z:set => p z /\ z <> x).
Hypothesis H6: y :e ordsucc x.
Hypothesis H7: PNo_downc P y q.
Theorem Conj_PNo_lenbdd_strict_imv_extend0__9__0: ordinal y -> PNoLt y q (ordsucc x) (fun z:set => p z /\ z <> x).
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend0__9__0.
(** Conj_PNo_lenbdd_strict_imv_extend0__10__0 TMN8mYxu4LJAyaWvaGFtVRLA9uv1trJQGam bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend0__10__0.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Hypothesis H1: TransSet x.
Hypothesis H2: PNo_lenbdd x P.
Hypothesis H3: PNo_lenbdd x Q.
Hypothesis H4: PNo_rel_strict_upperbd P x p.
Hypothesis H5: PNo_rel_strict_lowerbd Q x p.
Hypothesis H6: ordinal (ordsucc x).
Theorem Conj_PNo_lenbdd_strict_imv_extend0__10__0: PNoEq_ x p (fun y:set => p y /\ y <> x) -> PNo_rel_strict_upperbd P (ordsucc x) (fun y:set => p y /\ y <> x) /\ PNo_rel_strict_lowerbd Q (ordsucc x) (fun y:set => p y /\ y <> x).
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend0__10__0.
(** Conj_PNo_lenbdd_strict_imv_extend1__2__0 TMSZSeFY78qUQwvLBeQLwxMVzvgWzZb3Vim bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend1__2__0.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H1: TransSet x.
Hypothesis H2: PNo_rel_strict_lowerbd P x p.
Hypothesis H3: ordinal (ordsucc x).
Hypothesis H4: PNoEq_ x p (fun z:set => p z \/ z = x).
Hypothesis H5: ordinal y.
Hypothesis H6: y :e x.
Hypothesis H7: y :e ordsucc x.
Hypothesis H8: PNo_upc P y q.
Theorem Conj_PNo_lenbdd_strict_imv_extend1__2__0: PNoLt x p y q -> PNoLt (ordsucc x) (fun z:set => p z \/ z = x) y q.
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend1__2__0.
(** Conj_PNo_lenbdd_strict_imv_extend1__2__1 TMHPVZsv2MoYfbFNYANEqTw8XNS7UGjworc bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend1__2__1.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H2: PNo_rel_strict_lowerbd P x p.
Hypothesis H3: ordinal (ordsucc x).
Hypothesis H4: PNoEq_ x p (fun z:set => p z \/ z = x).
Hypothesis H5: ordinal y.
Hypothesis H6: y :e x.
Hypothesis H7: y :e ordsucc x.
Hypothesis H8: PNo_upc P y q.
Theorem Conj_PNo_lenbdd_strict_imv_extend1__2__1: PNoLt x p y q -> PNoLt (ordsucc x) (fun z:set => p z \/ z = x) y q.
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend1__2__1.
(** Conj_PNo_lenbdd_strict_imv_extend1__2__5 TMULkU7fQWJBbHSXaGeNqtRGiJQAEj9LyvD bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend1__2__5.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: TransSet x.
Hypothesis H2: PNo_rel_strict_lowerbd P x p.
Hypothesis H3: ordinal (ordsucc x).
Hypothesis H4: PNoEq_ x p (fun z:set => p z \/ z = x).
Hypothesis H6: y :e x.
Hypothesis H7: y :e ordsucc x.
Hypothesis H8: PNo_upc P y q.
Theorem Conj_PNo_lenbdd_strict_imv_extend1__2__5: PNoLt x p y q -> PNoLt (ordsucc x) (fun z:set => p z \/ z = x) y q.
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend1__2__5.
(** Conj_PNo_lenbdd_strict_imv_extend1__4__6 TMSw5T2HCVFdjpAYPLQTbmnrSAcevxwLM9f bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend1__4__6.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: TransSet x.
Hypothesis H2: PNo_rel_strict_lowerbd P x p.
Hypothesis H3: ordinal (ordsucc x).
Hypothesis H4: PNoEq_ x p (fun z:set => p z \/ z = x).
Hypothesis H5: ordinal y.
Hypothesis H7: y :e x.
Theorem Conj_PNo_lenbdd_strict_imv_extend1__4__6: y :e ordsucc x -> PNoLt (ordsucc x) (fun z:set => p z \/ z = x) y q.
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend1__4__6.
(** Conj_PNo_lenbdd_strict_imv_extend1__7__6 TMGBcjtjfJvCNPbgY63jS4MXjmAh2nCw51Y bounty of about 25 bars **)
Section Conj_PNo_lenbdd_strict_imv_extend1__7__6.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: TransSet x.
Hypothesis H2: PNo_lenbdd x P.
Hypothesis H3: PNo_rel_strict_lowerbd P x p.
Hypothesis H4: ordinal (ordsucc x).
Hypothesis H5: PNoEq_ x p (fun z:set => p z \/ z = x).
Hypothesis H7: PNo_upc P y q.
Theorem Conj_PNo_lenbdd_strict_imv_extend1__7__6: ordinal y -> PNoLt (ordsucc x) (fun z:set => p z \/ z = x) y q.
Admitted.

End Conj_PNo_lenbdd_strict_imv_extend1__7__6.
(** Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__1__5 TMTyWYggM9BDvitg8kQK4KBANdTcrEhebZp bounty of about 25 bars **)
Section Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__1__5.
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: z :e y.
Hypothesis H2: TransSet x.
Hypothesis H3: ordinal y.
Hypothesis H4: ordinal z.
Hypothesis H6: PNoLt z q x p.
Hypothesis H7: z :e x.
Theorem Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__1__5: Subq z x -> PNoLt z q y p.
Admitted.

End Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__1__5.
(** Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__3__9 TMasZ9DTBvLQ4CXZa8ALpPeTfMwvWvRQsnR bounty of about 25 bars **)
Section Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__3__9.
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Variable q:(set -> prop).
Variable w:set.
Variable p2:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: y :e ordsucc x.
Hypothesis H2: z :e y.
Hypothesis H3: TransSet x.
Hypothesis H4: ordinal y.
Hypothesis H5: ordinal z.
Hypothesis H6: Subq z y.
Hypothesis H7: ordinal w.
Hypothesis H8: PNoLe z q w p2.
Theorem Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__3__9: PNoLt z q x p -> PNoLt z q y p.
Admitted.

End Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__3__9.
(** Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__4__0 TMEh2ZQdZ49iaw8LqRZuDkfDA6pa4wSmZ6a bounty of about 25 bars **)
Section Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__4__0.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Variable q:(set -> prop).
Variable w:set.
Variable p2:(set -> prop).
Hypothesis H1: y :e ordsucc x.
Hypothesis H2: PNo_strict_upperbd P x p.
Hypothesis H3: z :e y.
Hypothesis H4: TransSet x.
Hypothesis H5: ordinal y.
Hypothesis H6: ordinal z.
Hypothesis H7: Subq z y.
Hypothesis H8: ordinal w.
Hypothesis H9: P w p2.
Hypothesis H10: PNoLe z q w p2.
Theorem Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__4__0: PNoLt w p2 x p -> PNoLt z q y p.
Admitted.

End Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__4__0.
(** Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__7__4 TMRegrq8pGGwApkFnhLQM3YWz51XuJxNi7R bounty of about 25 bars **)
Section Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__7__4.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: y :e ordsucc x.
Hypothesis H2: PNo_strict_upperbd P x p.
Hypothesis H3: z :e y.
Hypothesis H5: TransSet x.
Hypothesis H6: ordinal y.
Theorem Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__7__4: TransSet y -> PNoLt z q y p.
Admitted.

End Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__7__4.
(** Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__9__2 TMUu9yndFHGkhCkWCG8EGHLuB2xjSi1V65E bounty of about 25 bars **)
Section Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__9__2.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: y :e ordsucc x.
Hypothesis H3: z :e y.
Hypothesis H4: PNo_downc P z q.
Hypothesis H5: TransSet x.
Theorem Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__9__2: ordinal (ordsucc x) -> PNoLt z q y p.
Admitted.

End Conj_PNo_strict_upperbd_imp_rel_strict_upperbd__9__2.
(** Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__4__8 TMMyqikEgkE3KEQcbUPAPGYcGC6o9TiBxeb bounty of about 25 bars **)
Section Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__4__8.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Variable q:(set -> prop).
Variable w:set.
Variable p2:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: y :e ordsucc x.
Hypothesis H2: PNo_strict_lowerbd P x p.
Hypothesis H3: z :e y.
Hypothesis H4: TransSet x.
Hypothesis H5: ordinal y.
Hypothesis H6: ordinal z.
Hypothesis H7: Subq z y.
Hypothesis H9: P w p2.
Hypothesis H10: PNoLe w p2 z q.
Theorem Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__4__8: PNoLt x p w p2 -> PNoLt y p z q.
Admitted.

End Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__4__8.
(** Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__5__5 TMS99xStnfrm5WUUEpTTeQkD81zKpQpFf5X bounty of about 25 bars **)
Section Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__5__5.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: y :e ordsucc x.
Hypothesis H2: PNo_strict_lowerbd P x p.
Hypothesis H3: z :e y.
Hypothesis H4: PNo_upc P z q.
Hypothesis H6: ordinal y.
Hypothesis H7: TransSet y.
Hypothesis H8: ordinal z.
Theorem Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__5__5: Subq z y -> PNoLt y p z q.
Admitted.

End Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__5__5.
(** Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__7__2 TMWcaUDiL2YQAZvFqthnj1zU3twtmTtDoVi bounty of about 25 bars **)
Section Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__7__2.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Variable z:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: y :e ordsucc x.
Hypothesis H3: z :e y.
Hypothesis H4: PNo_upc P z q.
Hypothesis H5: TransSet x.
Hypothesis H6: ordinal y.
Theorem Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__7__2: TransSet y -> PNoLt y p z q.
Admitted.

End Conj_PNo_strict_lowerbd_imp_rel_strict_lowerbd__7__2.
(** Conj_PNo_rel_split_imv_imp_strict_imv__3__0 TMGGCEt3CDedULNRck7Nu1mJwFb4VNuDtR6 bounty of about 25 bars **)
Section Conj_PNo_rel_split_imv_imp_strict_imv__3__0.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Variable z:set.
Hypothesis H1: ordinal (ordsucc x).
Hypothesis H2: PNo_rel_strict_lowerbd P (ordsucc x) (fun w:set => p w \/ w = x).
Hypothesis H3: ordinal y.
Hypothesis H4: P y q.
Hypothesis H5: z :e ordsucc x.
Hypothesis H6: PNoEq_ z q p.
Hypothesis H7: p z \/ z = x.
Hypothesis H8: ordinal z.
Hypothesis H9: PNoLt y q z q.
Theorem Conj_PNo_rel_split_imv_imp_strict_imv__3__0: ~ PNo_upc P z q.
Admitted.

End Conj_PNo_rel_split_imv_imp_strict_imv__3__0.
(** Conj_PNo_rel_split_imv_imp_strict_imv__11__7 TMSD52yYnoeDoRvRq2hdSf2SqgfYbvqV3bz bounty of about 25 bars **)
Section Conj_PNo_rel_split_imv_imp_strict_imv__11__7.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Variable z:set.
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal (ordsucc x).
Hypothesis H2: PNo_rel_strict_upperbd P (ordsucc x) (fun w:set => p w /\ w <> x).
Hypothesis H3: ordinal y.
Hypothesis H4: P y q.
Hypothesis H5: z :e ordsucc x.
Hypothesis H6: PNoEq_ z p q.
Hypothesis H8: ordinal z.
Hypothesis H9: PNoLt z q y q.
Theorem Conj_PNo_rel_split_imv_imp_strict_imv__11__7: ~ PNo_downc P z q.
Admitted.

End Conj_PNo_rel_split_imv_imp_strict_imv__11__7.
(** Conj_PNo_rel_split_imv_imp_strict_imv__14__6 TMEybc8mW9dUVZFgriZ2xToEKv1pkzpxKGD bounty of about 25 bars **)
Section Conj_PNo_rel_split_imv_imp_strict_imv__14__6.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal (ordsucc x).
Hypothesis H2: PNo_rel_strict_upperbd P (ordsucc x) (fun z:set => p z /\ z <> x).
Hypothesis H3: ~ (p x /\ x <> x).
Hypothesis H4: ordinal y.
Hypothesis H5: P y q.
Theorem Conj_PNo_rel_split_imv_imp_strict_imv__14__6: (forall z:set, z :e ordsucc x -> z :e y -> PNoEq_ z p q -> q z -> p z /\ z <> x) -> PNoLt y q x p.
Admitted.

End Conj_PNo_rel_split_imv_imp_strict_imv__14__6.
(** Conj_PNo_rel_split_imv_imp_strict_imv__15__2 TMbfvvkKvVMX9j8Y3tH6RGeVJUTv9tPThhQ bounty of about 25 bars **)
Section Conj_PNo_rel_split_imv_imp_strict_imv__15__2.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal (ordsucc x).
Hypothesis H3: ~ (p x /\ x <> x).
Hypothesis H4: PNoLt (ordsucc x) (fun z:set => p z /\ z <> x) x p.
Hypothesis H5: ordinal y.
Hypothesis H6: P y q.
Hypothesis H7: PNo_downc P y q.
Theorem Conj_PNo_rel_split_imv_imp_strict_imv__15__2: (y :e ordsucc x -> PNoLt y q x p) -> PNoLt y q x p.
Admitted.

End Conj_PNo_rel_split_imv_imp_strict_imv__15__2.
(** Conj_PNo_rel_split_imv_imp_strict_imv__15__6 TMK1xNLseFgMdUN3vMWZzqAQdY4enZMUv1p bounty of about 25 bars **)
Section Conj_PNo_rel_split_imv_imp_strict_imv__15__6.
Variable P:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable y:set.
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal (ordsucc x).
Hypothesis H2: PNo_rel_strict_upperbd P (ordsucc x) (fun z:set => p z /\ z <> x).
Hypothesis H3: ~ (p x /\ x <> x).
Hypothesis H4: PNoLt (ordsucc x) (fun z:set => p z /\ z <> x) x p.
Hypothesis H5: ordinal y.
Hypothesis H7: PNo_downc P y q.
Theorem Conj_PNo_rel_split_imv_imp_strict_imv__15__6: (y :e ordsucc x -> PNoLt y q x p) -> PNoLt y q x p.
Admitted.

End Conj_PNo_rel_split_imv_imp_strict_imv__15__6.
(** Conj_PNo_rel_split_imv_imp_strict_imv__19__4 TMazkeAkLcpM35R9Mvf1d6AWB8zmEK1KoBZ bounty of about 25 bars **)
Section Conj_PNo_rel_split_imv_imp_strict_imv__19__4.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal (ordsucc x).
Hypothesis H2: PNo_rel_strict_upperbd P (ordsucc x) (fun y:set => p y /\ y <> x).
Hypothesis H3: PNo_rel_strict_lowerbd Q (ordsucc x) (fun y:set => p y \/ y = x).
Theorem Conj_PNo_rel_split_imv_imp_strict_imv__19__4: p x \/ x = x -> PNo_strict_upperbd P x p /\ PNo_strict_lowerbd Q x p.
Admitted.

End Conj_PNo_rel_split_imv_imp_strict_imv__19__4.
(** Conj_PNo_strict_imv_pred_eq__3__7 TMcwTwpZaM7Zax4fqkzuER6wGJn4kjRkjwC bounty of about 25 bars **)
Section Conj_PNo_strict_imv_pred_eq__3__7.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H1: (forall z:set, z :e x -> (forall p2:set -> prop, ~ PNo_strict_imv P Q z p2)).
Hypothesis H2: PNo_strict_lowerbd Q x p.
Hypothesis H3: PNo_strict_upperbd P x q.
Hypothesis H4: ordinal y.
Hypothesis H5: y :e x.
Hypothesis H6: ~ q y.
Theorem Conj_PNo_strict_imv_pred_eq__3__7: ~ PNoLt x q y q.
Admitted.

End Conj_PNo_strict_imv_pred_eq__3__7.
(** Conj_PNo_strict_imv_pred_eq__6__3 TMTmARE13etB6hE9K6uH4uXvLhPh8BePC2V bounty of about 25 bars **)
Section Conj_PNo_strict_imv_pred_eq__6__3.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable p:(set -> prop).
Variable q:(set -> prop).
Hypothesis H0: ordinal x.
Hypothesis H1: TransSet x.
Hypothesis H2: (forall y:set, y :e x -> (forall p2:set -> prop, ~ PNo_strict_imv P Q y p2)).
Hypothesis H4: PNo_strict_lowerbd Q x p.
Hypothesis H5: PNo_strict_upperbd P x q.
Hypothesis H6: PNo_strict_lowerbd Q x q.
Theorem Conj_PNo_strict_imv_pred_eq__6__3: (forall y:set, ordinal y -> y :e x -> (p y <-> q y)) -> (forall y:set, y :e x -> (p y <-> q y)).
Admitted.

End Conj_PNo_strict_imv_pred_eq__6__3.
(** Conj_PNo_bd_In__1__3 TMSNNhhLCkfPpfVWqdZMxaxp1kwpbknsyAq bounty of about 25 bars **)
Section Conj_PNo_bd_In__1__3.
Variable P:(set -> ((set -> prop) -> prop)).
Variable Q:(set -> ((set -> prop) -> prop)).
Variable x:set.
Variable y:set.
Variable p:(set -> prop).
Hypothesis H0: (forall z:set, z :e PNo_bd P Q -> (forall q:set -> prop, ~ PNo_strict_imv P Q z q)).
Hypothesis H1: y :e ordsucc x.
Hypothesis H2: PNo_strict_imv P Q y p.
Theorem Conj_PNo_bd_In__1__3: ~ y :e PNo_bd P Q.
Admitted.

End Conj_PNo_bd_In__1__3.
(** Conj_SNoLtE__1__3 TMdQPqnVozoS1DBSku1D8KJe6vQLp5cUVa1 bounty of about 25 bars **)
Section Conj_SNoLtE__1__3.
Variable x:set.
Variable y:set.
Variable P:prop.
Variable z:set.
Hypothesis H0: (forall w:set, SNo w -> SNoLev w :e binintersect (SNoLev x) (SNoLev y) -> SNoEq_ (SNoLev w) w x -> SNoEq_ (SNoLev w) w y -> x < w -> w < y -> nIn (SNoLev w) x -> SNoLev w :e y -> P).
Hypothesis H1: z :e binintersect (SNoLev x) (SNoLev y).
Hypothesis H2: PNoEq_ z (fun w:set => w :e x) (fun w:set => w :e y).
Hypothesis H4: z :e y.
Hypothesis H5: z :e SNoLev x.
Hypothesis H6: z :e SNoLev y.
Hypothesis H7: SNo (PSNo z (fun w:set => w :e x)).
Hypothesis H8: SNoLev (PSNo z (fun w:set => w :e x)) = z.
Hypothesis H9: SNoEq_ z (PSNo z (fun w:set => w :e x)) x.
Theorem Conj_SNoLtE__1__3: SNoEq_ z (PSNo z (fun w:set => w :e x)) y -> P.
Admitted.

End Conj_SNoLtE__1__3.
(** Conj_SNoLtE__1__4 TMJgjL45h6ziFXBioksUVwe7ZeE7AvUXWAC bounty of about 25 bars **)
Section Conj_SNoLtE__1__4.
Variable x:set.
Variable y:set.
Variable P:prop.
Variable z:set.
Hypothesis H0: (forall w:set, SNo w -> SNoLev w :e binintersect (SNoLev x) (SNoLev y) -> SNoEq_ (SNoLev w) w x -> SNoEq_ (SNoLev w) w y -> x < w -> w < y -> nIn (SNoLev w) x -> SNoLev w :e y -> P).
Hypothesis H1: z :e binintersect (SNoLev x) (SNoLev y).
Hypothesis H2: PNoEq_ z (fun w:set => w :e x) (fun w:set => w :e y).
Hypothesis H3: ~ z :e x.
Hypothesis H5: z :e SNoLev x.
Hypothesis H6: z :e SNoLev y.
Hypothesis H7: SNo (PSNo z (fun w:set => w :e x)).
Hypothesis H8: SNoLev (PSNo z (fun w:set => w :e x)) = z.
Hypothesis H9: SNoEq_ z (PSNo z (fun w:set => w :e x)) x.
Theorem Conj_SNoLtE__1__4: SNoEq_ z (PSNo z (fun w:set => w :e x)) y -> P.
Admitted.

End Conj_SNoLtE__1__4.
(** Conj_SNoLtE__1__5 TMKJPxmBAFbH7XXj2fJ5pWNasTPbKWbMb7G bounty of about 25 bars **)
Section Conj_SNoLtE__1__5.
Variable x:set.
Variable y:set.
Variable P:prop.
Variable z:set.
Hypothesis H0: (forall w:set, SNo w -> SNoLev w :e binintersect (SNoLev x) (SNoLev y) -> SNoEq_ (SNoLev w) w x -> SNoEq_ (SNoLev w) w y -> x < w -> w < y -> nIn (SNoLev w) x -> SNoLev w :e y -> P).
Hypothesis H1: z :e binintersect (SNoLev x) (SNoLev y).
Hypothesis H2: PNoEq_ z (fun w:set => w :e x) (fun w:set => w :e y).
Hypothesis H3: ~ z :e x.
Hypothesis H4: z :e y.
Hypothesis H6: z :e SNoLev y.
Hypothesis H7: SNo (PSNo z (fun w:set => w :e x)).
Hypothesis H8: SNoLev (PSNo z (fun w:set => w :e x)) = z.
Hypothesis H9: SNoEq_ z (PSNo z (fun w:set => w :e x)) x.
Theorem Conj_SNoLtE__1__5: SNoEq_ z (PSNo z (fun w:set => w :e x)) y -> P.
Admitted.

End Conj_SNoLtE__1__5.
(** Conj_SNoLtE__1__8 TMMKbr6xKkKmuxkFx4vUPZ1ESib4K5C3dTA bounty of about 25 bars **)
Section Conj_SNoLtE__1__8.
Variable x:set.
Variable y:set.
Variable P:prop.
Variable z:set.
Hypothesis H0: (forall w:set, SNo w -> SNoLev w :e binintersect (SNoLev x) (SNoLev y) -> SNoEq_ (SNoLev w) w x -> SNoEq_ (SNoLev w) w y -> x < w -> w < y -> nIn (SNoLev w) x -> SNoLev w :e y -> P).
Hypothesis H1: z :e binintersect (SNoLev x) (SNoLev y).
Hypothesis H2: PNoEq_ z (fun w:set => w :e x) (fun w:set => w :e y).
Hypothesis H3: ~ z :e x.
Hypothesis H4: z :e y.
Hypothesis H5: z :e SNoLev x.
Hypothesis H6: z :e SNoLev y.
Hypothesis H7: SNo (PSNo z (fun w:set => w :e x)).
Hypothesis H9: SNoEq_ z (PSNo z (fun w:set => w :e x)) x.
Theorem Conj_SNoLtE__1__8: SNoEq_ z (PSNo z (fun w:set => w :e x)) y -> P.
Admitted.

End Conj_SNoLtE__1__8.
(** Conj_SNoLtE__1__9 TMaJh4YBa7noJ5vCMzbZiPyPmw7oqYkr2W1 bounty of about 25 bars **)
Section Conj_SNoLtE__1__9.
Variable x:set.
Variable y:set.
Variable P:prop.
Variable z:set.
Hypothesis H0: (forall w:set, SNo w -> SNoLev w :e binintersect (SNoLev x) (SNoLev y) -> SNoEq_ (SNoLev w) w x -> SNoEq_ (SNoLev w) w y -> x < w -> w < y -> nIn (SNoLev w) x -> SNoLev w :e y -> P).
Hypothesis H1: z :e binintersect (SNoLev x) (SNoLev y).
Hypothesis H2: PNoEq_ z (fun w:set => w :e x) (fun w:set => w :e y).
Hypothesis H3: ~ z :e x.
Hypothesis H4: z :e y.
Hypothesis H5: z :e SNoLev x.
Hypothesis H6: z :e SNoLev y.
Hypothesis H7: SNo (PSNo z (fun w:set => w :e x)).
Hypothesis H8: SNoLev (PSNo z (fun w:set => w :e x)) = z.
Theorem Conj_SNoLtE__1__9: SNoEq_ z (PSNo z (fun w:set => w :e x)) y -> P.
Admitted.

End Conj_SNoLtE__1__9.
(** Conj_SNoLtE__6__5 TMGP9P8sY3CFbBbXaB82XSjAVKrqfT6dEqA bounty of about 25 bars **)
Section Conj_SNoLtE__6__5.
Variable x:set.
Variable y:set.
Variable P:prop.
Variable z:set.
Hypothesis H0: (forall w:set, SNo w -> SNoLev w :e binintersect (SNoLev x) (SNoLev y) -> SNoEq_ (SNoLev w) w x -> SNoEq_ (SNoLev w) w y -> x < w -> w < y -> nIn (SNoLev w) x -> SNoLev w :e y -> P).
Hypothesis H1: ordinal (SNoLev x).
Hypothesis H2: z :e binintersect (SNoLev x) (SNoLev y).
Hypothesis H3: PNoEq_ z (fun w:set => w :e x) (fun w:set => w :e y).
Hypothesis H4: ~ z :e x.
Hypothesis H6: z :e SNoLev x.
Hypothesis H7: z :e SNoLev y.
Theorem Conj_SNoLtE__6__5: ordinal z -> P.
Admitted.

End Conj_SNoLtE__6__5.
(** Conj_SNoLtE__8__3 TMVrqu7AeB67D8CtBz4oWD87dGHLjfaeKZN bounty of about 25 bars **)
Section Conj_SNoLtE__8__3.
Variable x:set.
Variable y:set.
Variable P:prop.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: x < y.
Hypothesis H4: SNoLev x :e SNoLev y -> SNoEq_ (SNoLev x) x y -> SNoLev x :e y -> P.
Hypothesis H5: SNoLev y :e SNoLev x -> SNoEq_ (SNoLev y) x y -> nIn (SNoLev y) x -> P.
Theorem Conj_SNoLtE__8__3: ordinal (SNoLev x) -> P.
Admitted.

End Conj_SNoLtE__8__3.
(** Conj_SNoCutP_SNoCut__1__4 TMFfd7YezCcxhJoZLfd2pQayMKkmji9UvjZ bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__1__4.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ordinal (PNo_bd (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y)).
Hypothesis H1: PNo_strict_upperbd (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (PNo_bd (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y)) (PNo_pred (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y)).
Hypothesis H2: z :e x.
Hypothesis H3: ordinal (SNoLev z).
Theorem Conj_SNoCutP_SNoCut__1__4: ordinal (SNoLev z) /\ PSNo (SNoLev z) (fun w:set => w :e z) :e x -> z < PSNo (PNo_bd (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y)) (PNo_pred (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y)).
Admitted.

End Conj_SNoCutP_SNoCut__1__4.
(** Conj_SNoCutP_SNoCut__9__3 TMPhgADvu7SX3HqSNXWvtZAtQ5aRGDAnpzg bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__9__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H1: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H2: (forall u:set, u :e PNo_bd (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e x) (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e y) -> (forall p:set -> prop, ~ PNo_strict_imv (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e x) (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e y) u p)).
Hypothesis H4: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (SNoLev z) (fun u:set => u :e z).
Hypothesis H5: Subq (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (SNoLev z).
Hypothesis H6: w :e PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y).
Hypothesis H7: PNoEq_ w (fun u:set => u :e z) (PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H8: nIn w z.
Hypothesis H9: PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) w.
Hypothesis H10: ordinal w.
Hypothesis H11: ordinal (ordsucc w).
Hypothesis H12: ~ (w :e z /\ w <> w).
Theorem Conj_SNoCutP_SNoCut__9__3: ~ (w :e z \/ w = w).
Admitted.

End Conj_SNoCutP_SNoCut__9__3.
(** Conj_SNoCutP_SNoCut__9__11 TMLBTvhZReSf3EJGVFXvM3XKu8uFfwBVHMG bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__9__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H1: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H2: (forall u:set, u :e PNo_bd (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e x) (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e y) -> (forall p:set -> prop, ~ PNo_strict_imv (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e x) (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e y) u p)).
Hypothesis H3: ordinal (SNoLev z).
Hypothesis H4: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (SNoLev z) (fun u:set => u :e z).
Hypothesis H5: Subq (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (SNoLev z).
Hypothesis H6: w :e PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y).
Hypothesis H7: PNoEq_ w (fun u:set => u :e z) (PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H8: nIn w z.
Hypothesis H9: PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) w.
Hypothesis H10: ordinal w.
Hypothesis H12: ~ (w :e z /\ w <> w).
Theorem Conj_SNoCutP_SNoCut__9__11: ~ (w :e z \/ w = w).
Admitted.

End Conj_SNoCutP_SNoCut__9__11.
(** Conj_SNoCutP_SNoCut__10__0 TMJdq8XLSQYPaMSsGxLGNYwJwRYeGHJPhds bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__10__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H1: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H2: (forall u:set, u :e PNo_bd (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e x) (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e y) -> (forall p:set -> prop, ~ PNo_strict_imv (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e x) (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e y) u p)).
Hypothesis H3: ordinal (SNoLev z).
Hypothesis H4: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (SNoLev z) (fun u:set => u :e z).
Hypothesis H5: Subq (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (SNoLev z).
Hypothesis H6: w :e PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y).
Hypothesis H7: PNoEq_ w (fun u:set => u :e z) (PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H8: nIn w z.
Hypothesis H9: PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) w.
Hypothesis H10: ordinal w.
Hypothesis H11: ordinal (ordsucc w).
Theorem Conj_SNoCutP_SNoCut__10__0: ~ ~ (w :e z /\ w <> w).
Admitted.

End Conj_SNoCutP_SNoCut__10__0.
(** Conj_SNoCutP_SNoCut__12__7 TMEvgoKq2HNz7B21Y3F9MjnqevRyE15e6sp bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__12__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H1: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H2: (forall u:set, u :e PNo_bd (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e x) (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e y) -> (forall p:set -> prop, ~ PNo_strict_imv (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e x) (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e y) u p)).
Hypothesis H3: ordinal (SNoLev z).
Hypothesis H4: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (SNoLev z) (fun u:set => u :e z).
Hypothesis H5: Subq (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (SNoLev z).
Hypothesis H6: w :e PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y).
Hypothesis H8: nIn w z.
Hypothesis H9: PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) w.
Theorem Conj_SNoCutP_SNoCut__12__7: ~ ordinal w.
Admitted.

End Conj_SNoCutP_SNoCut__12__7.
(** Conj_SNoCutP_SNoCut__14__7 TMPSDC4rZZxZELQSdd3JKvLq7z9R2KaXV6g bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__14__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H1: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H2: (forall u:set, u :e PNo_bd (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e x) (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e y) -> (forall p:set -> prop, ~ PNo_strict_imv (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e x) (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e y) u p)).
Hypothesis H3: ordinal (SNoLev z).
Hypothesis H4: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (SNoLev z) (fun u:set => u :e z).
Hypothesis H5: Subq (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (SNoLev z).
Hypothesis H6: w :e PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y).
Hypothesis H8: ~ PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) w.
Hypothesis H9: w :e z.
Hypothesis H10: ordinal w.
Hypothesis H11: ordinal (ordsucc w).
Theorem Conj_SNoCutP_SNoCut__14__7: ~ ~ (w :e z /\ w <> w).
Admitted.

End Conj_SNoCutP_SNoCut__14__7.
(** Conj_SNoCutP_SNoCut__15__3 TMPE5WnELYkkzrvYw2YJcsm3JmDnBS7fnEw bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__15__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H1: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)).
Hypothesis H2: (forall u:set, u :e PNo_bd (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e x) (fun v:set => fun p:set -> prop => ordinal v /\ PSNo v p :e y) -> (forall p:set -> prop, ~ PNo_strict_imv (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e x) (fun v:set => fun q:set -> prop => ordinal v /\ PSNo v q :e y) u p)).
Hypothesis H4: PNo_strict_imv (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) (SNoLev z) (fun u:set => u :e z).
Hypothesis H5: Subq (PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (SNoLev z).
Hypothesis H6: w :e PNo_bd (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y).
Hypothesis H7: PNoEq_ w (PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y)) (fun u:set => u :e z).
Hypothesis H8: ~ PNo_pred (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e x) (fun u:set => fun p:set -> prop => ordinal u /\ PSNo u p :e y) w.
Hypothesis H9: w :e z.
Hypothesis H10: ordinal w.
Theorem Conj_SNoCutP_SNoCut__15__3: ~ ordinal (ordsucc w).
Admitted.

End Conj_SNoCutP_SNoCut__15__3.
(** Conj_SNoCutP_SNoCut__20__2 TMMYndscEdRQjjCuK4nkZGLXyE1tDkBy9gd bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__20__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ordinal (PNo_bd (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y)).
Hypothesis H1: PNo_strict_imv (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y) (PNo_bd (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y)) (PNo_pred (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y)).
Hypothesis H3: SNoLev (SNoCut x y) = PNo_bd (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y).
Hypothesis H4: PNoEq_ (PNo_bd (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y)) (fun w:set => w :e SNoCut x y) (PNo_pred (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y)).
Hypothesis H5: SNo z.
Hypothesis H6: (forall w:set, w :e x -> w < z).
Hypothesis H7: (forall w:set, w :e y -> z < w).
Theorem Conj_SNoCutP_SNoCut__20__2: ordinal (SNoLev z) -> Subq (SNoLev (SNoCut x y)) (SNoLev z) /\ PNoEq_ (SNoLev (SNoCut x y)) (fun w:set => w :e SNoCut x y) (fun w:set => w :e z).
Admitted.

End Conj_SNoCutP_SNoCut__20__2.
(** Conj_SNoCutP_SNoCut__21__7 TMVjJiy6dQ4D55oC9yfHEYM8R3GXkUHgkDQ bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__21__7.
Variable x:set.
Variable y:set.
Hypothesis H0: (forall z:set, z :e y -> SNo z).
Hypothesis H1: ordinal (PNo_bd (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y)).
Hypothesis H2: PNo_strict_imv (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y) (PNo_bd (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y)) (PNo_pred (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y)).
Hypothesis H3: (forall z:set, z :e PNo_bd (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e x) (fun w:set => fun p:set -> prop => ordinal w /\ PSNo w p :e y) -> (forall p:set -> prop, ~ PNo_strict_imv (fun w:set => fun q:set -> prop => ordinal w /\ PSNo w q :e x) (fun w:set => fun q:set -> prop => ordinal w /\ PSNo w q :e y) z p)).
Hypothesis H4: PNo_strict_lowerbd (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y) (PNo_bd (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y)) (PNo_pred (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y)).
Hypothesis H5: SNo (SNoCut x y).
Hypothesis H6: SNoLev (SNoCut x y) = PNo_bd (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y).
Hypothesis H8: PNoEq_ (PNo_bd (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y)) (fun z:set => z :e SNoCut x y) (PNo_pred (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y)).
Hypothesis H9: (forall z:set, z :e x -> z < SNoCut x y).
Theorem Conj_SNoCutP_SNoCut__21__7: (forall z:set, z :e y -> SNoCut x y < z) -> SNo (SNoCut x y) /\ SNoLev (SNoCut x y) :e ordsucc (binunion (famunion x (fun z:set => ordsucc (SNoLev z))) (famunion y (fun z:set => ordsucc (SNoLev z)))) /\ (forall z:set, z :e x -> z < SNoCut x y) /\ (forall z:set, z :e y -> SNoCut x y < z) /\ (forall z:set, SNo z -> (forall w:set, w :e x -> w < z) -> (forall w:set, w :e y -> z < w) -> Subq (SNoLev (SNoCut x y)) (SNoLev z) /\ PNoEq_ (SNoLev (SNoCut x y)) (fun w:set => w :e SNoCut x y) (fun w:set => w :e z)).
Admitted.

End Conj_SNoCutP_SNoCut__21__7.
(** Conj_SNoCutP_SNoCut__29__1 TMLVpfJkzoimAXdGs8iGqtCYRLqYCmNZpyb bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__29__1.
Variable x:set.
Variable y:set.
Hypothesis H0: (forall z:set, z :e x -> SNo z).
Hypothesis H2: PNoLt_pwise (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y).
Hypothesis H3: ordinal (binunion (famunion x (fun z:set => ordsucc (SNoLev z))) (famunion y (fun z:set => ordsucc (SNoLev z)))).
Hypothesis H4: PNo_lenbdd (binunion (famunion x (fun z:set => ordsucc (SNoLev z))) (famunion y (fun z:set => ordsucc (SNoLev z)))) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x).
Theorem Conj_SNoCutP_SNoCut__29__1: PNo_lenbdd (binunion (famunion x (fun z:set => ordsucc (SNoLev z))) (famunion y (fun z:set => ordsucc (SNoLev z)))) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y) -> SNo (SNoCut x y) /\ SNoLev (SNoCut x y) :e ordsucc (binunion (famunion x (fun z:set => ordsucc (SNoLev z))) (famunion y (fun z:set => ordsucc (SNoLev z)))) /\ (forall z:set, z :e x -> z < SNoCut x y) /\ (forall z:set, z :e y -> SNoCut x y < z) /\ (forall z:set, SNo z -> (forall w:set, w :e x -> w < z) -> (forall w:set, w :e y -> z < w) -> Subq (SNoLev (SNoCut x y)) (SNoLev z) /\ PNoEq_ (SNoLev (SNoCut x y)) (fun w:set => w :e SNoCut x y) (fun w:set => w :e z)).
Admitted.

End Conj_SNoCutP_SNoCut__29__1.
(** Conj_SNoCutP_SNoCut__34__2 TMU8tJRdhMB8wNMgDDHkWXZvZxFQqnoVmNN bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut__34__2.
Variable x:set.
Variable y:set.
Hypothesis H0: (forall z:set, z :e x -> SNo z).
Hypothesis H1: (forall z:set, z :e y -> SNo z).
Theorem Conj_SNoCutP_SNoCut__34__2: PNoLt_pwise (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e x) (fun z:set => fun p:set -> prop => ordinal z /\ PSNo z p :e y) -> SNo (SNoCut x y) /\ SNoLev (SNoCut x y) :e ordsucc (binunion (famunion x (fun z:set => ordsucc (SNoLev z))) (famunion y (fun z:set => ordsucc (SNoLev z)))) /\ (forall z:set, z :e x -> z < SNoCut x y) /\ (forall z:set, z :e y -> SNoCut x y < z) /\ (forall z:set, SNo z -> (forall w:set, w :e x -> w < z) -> (forall w:set, w :e y -> z < w) -> Subq (SNoLev (SNoCut x y)) (SNoLev z) /\ PNoEq_ (SNoLev (SNoCut x y)) (fun w:set => w :e SNoCut x y) (fun w:set => w :e z)).
Admitted.

End Conj_SNoCutP_SNoCut__34__2.
(** Conj_SNoCutP_SNoL_SNoR__5__1 TMFbe6neX8VWV2t3CHXwkWXdRg3r7sUoJPX bounty of about 25 bars **)
Section Conj_SNoCutP_SNoL_SNoR__5__1.
Variable x:set.
Hypothesis H0: SNo x.
Theorem Conj_SNoCutP_SNoL_SNoR__5__1: (forall y:set, y :e SNoL x -> SNo y) -> (forall y:set, y :e SNoL x -> SNo y) /\ (forall y:set, y :e SNoR x -> SNo y) /\ (forall y:set, y :e SNoL x -> (forall z:set, z :e SNoR x -> y < z)).
Admitted.

End Conj_SNoCutP_SNoL_SNoR__5__1.
(** Conj_SNo_eta__5__1 TMRfQzg5NL8NU3amqk6E87dxtNkT7Hs1MHr bounty of about 25 bars **)
Section Conj_SNo_eta__5__1.
Variable x:set.
Hypothesis H0: SNo x.
Theorem Conj_SNo_eta__5__1: SNoCutP (SNoL x) (SNoR x) -> x = SNoCut (SNoL x) (SNoR x).
Admitted.

End Conj_SNo_eta__5__1.
(** Conj_SNoCut_Le__3__5 TMZfF8PwXiyBcFk2sujnRVmcZnxbez7xVBV bounty of about 25 bars **)
Section Conj_SNoCut_Le__3__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, v :e y -> SNo v).
Hypothesis H1: SNo (SNoCut x y).
Hypothesis H2: (forall v:set, v :e y -> SNoCut x y < v).
Hypothesis H3: (forall v:set, SNo v -> (forall x2:set, x2 :e x -> x2 < v) -> (forall x2:set, x2 :e y -> v < x2) -> Subq (SNoLev (SNoCut x y)) (SNoLev v) /\ SNoEq_ (SNoLev (SNoCut x y)) (SNoCut x y) v).
Hypothesis H4: SNo u.
Hypothesis H6: u < SNoCut x y.
Hypothesis H7: (forall v:set, v :e x -> v < u).
Theorem Conj_SNoCut_Le__3__5: ~ (forall v:set, v :e y -> u < v).
Admitted.

End Conj_SNoCut_Le__3__5.
(** Conj_SNoCut_ext__2__3 TMVesvRm7y9ZgCK8rPkvkjttuyp38mhq1py bounty of about 25 bars **)
Section Conj_SNoCut_ext__2__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNoCutP x y.
Hypothesis H1: SNoCutP z w.
Hypothesis H2: (forall u:set, u :e x -> u < SNoCut z w).
Hypothesis H4: (forall u:set, u :e z -> u < SNoCut x y).
Hypothesis H5: (forall u:set, u :e w -> SNoCut x y < u).
Theorem Conj_SNoCut_ext__2__3: SNo (SNoCut x y) -> SNoCut x y = SNoCut z w.
Admitted.

End Conj_SNoCut_ext__2__3.
(** Conj_SNoCut_ext__2__5 TMNPnuT7rAi2w2HcfLcxg492v7UJby7KJ56 bounty of about 25 bars **)
Section Conj_SNoCut_ext__2__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNoCutP x y.
Hypothesis H1: SNoCutP z w.
Hypothesis H2: (forall u:set, u :e x -> u < SNoCut z w).
Hypothesis H3: (forall u:set, u :e y -> SNoCut z w < u).
Hypothesis H4: (forall u:set, u :e z -> u < SNoCut x y).
Theorem Conj_SNoCut_ext__2__5: SNo (SNoCut x y) -> SNoCut x y = SNoCut z w.
Admitted.

End Conj_SNoCut_ext__2__5.
(** Conj_ordinal_SNoR__1__0 TMVQwMnbn97bXvYgjVmrgVeK2dw2UrWSxMs bounty of about 25 bars **)
Section Conj_ordinal_SNoR__1__0.
Variable x:set.
Hypothesis H1: SNo x.
Theorem Conj_ordinal_SNoR__1__0: SNoLev x = x -> SNoR x = Empty.
Admitted.

End Conj_ordinal_SNoR__1__0.
(** Conj_ordinal_In_SNoLt__1__0 TMUJE4wUTMt4gTiSmWQCcRMK1FsoL7qwcwi bounty of about 25 bars **)
Section Conj_ordinal_In_SNoLt__1__0.
Variable x:set.
Variable y:set.
Hypothesis H1: y :e x.
Hypothesis H2: ordinal y.
Hypothesis H3: SNo y.
Theorem Conj_ordinal_In_SNoLt__1__0: SNoLev y = y -> y < x.
Admitted.

End Conj_ordinal_In_SNoLt__1__0.
(** Conj_ordinal_SNoLev_max_2__5__0 TMQX5WYsnF4PJHigkSixPiikryhh7HNusSo bounty of about 25 bars **)
Section Conj_ordinal_SNoLev_max_2__5__0.
Variable x:set.
Variable y:set.
Hypothesis H1: TransSet x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo x.
Hypothesis H4: SNoLev x = x.
Hypothesis H5: SNoLev y = x.
Hypothesis H6: ~ y <= x.
Theorem Conj_ordinal_SNoLev_max_2__5__0: ~ (forall z:set, ordinal z -> z :e x -> z :e y).
Admitted.

End Conj_ordinal_SNoLev_max_2__5__0.
(** Conj_SNoL_1__1__0 TMNKDisa8NheGiCvicXJ6wVH1obD3tZceHx bounty of about 25 bars **)
Section Conj_SNoL_1__1__0.
Variable x:set.
Hypothesis H1: SNoLev x :e ordsucc Empty.
Theorem Conj_SNoL_1__1__0: Empty = x -> x :e ordsucc Empty.
Admitted.

End Conj_SNoL_1__1__0.
(** Conj_SNo__eps___3__3 TMTRSHCcJvMLiFsE2YUk9Dx4EYihupZeRDj bounty of about 25 bars **)
Section Conj_SNo__eps___3__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: nat_p x.
Hypothesis H1: y :e ordsucc x.
Hypothesis H2: nat_p z.
Theorem Conj_SNo__eps___3__3: nat_p y -> exactly1of2 (SetAdjoin y (Sing (ordsucc Empty)) :e eps_ x) (y :e eps_ x).
Admitted.

End Conj_SNo__eps___3__3.
(** Conj_SNo_pos_eps_Lt__1__3 TMS6aFHTyDgS14PKbJq5oEuZLpzjp1ZSKZE bounty of about 25 bars **)
Section Conj_SNo_pos_eps_Lt__1__3.
Variable x:set.
Variable y:set.
Hypothesis H0: Empty < y.
Hypothesis H1: ordinal (SNoLev y).
Hypothesis H2: SNo y.
Theorem Conj_SNo_pos_eps_Lt__1__3: y <> Empty.
Admitted.

End Conj_SNo_pos_eps_Lt__1__3.
(** Conj_SNo_pos_eps_Lt__2__3 TMQaNRh2ysPgPsg2g52o7ETFgCFiGcWZj6d bounty of about 25 bars **)
Section Conj_SNo_pos_eps_Lt__2__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: Empty < y.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H4: SNoLev z :e eps_ x.
Theorem Conj_SNo_pos_eps_Lt__2__3: z <> Empty.
Admitted.

End Conj_SNo_pos_eps_Lt__2__3.
(** Conj_SNo_pos_eps_Le__1__3 TMS6aFHTyDgS14PKbJq5oEuZLpzjp1ZSKZE bounty of about 25 bars **)
Section Conj_SNo_pos_eps_Le__1__3.
Variable x:set.
Variable y:set.
Hypothesis H0: Empty < y.
Hypothesis H1: ordinal (SNoLev y).
Hypothesis H2: SNo y.
Theorem Conj_SNo_pos_eps_Le__1__3: y <> Empty.
Admitted.

End Conj_SNo_pos_eps_Le__1__3.
(** Conj_SNo_pos_eps_Le__2__3 TMQaNRh2ysPgPsg2g52o7ETFgCFiGcWZj6d bounty of about 25 bars **)
Section Conj_SNo_pos_eps_Le__2__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: Empty < y.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H4: SNoLev z :e eps_ x.
Theorem Conj_SNo_pos_eps_Le__2__3: z <> Empty.
Admitted.

End Conj_SNo_pos_eps_Le__2__3.
(** Conj_eps_SNoCut__5__2 TMRCi8wYQz3GsEqVAgiPR3oLt2viCevNkuo bounty of about 25 bars **)
Section Conj_eps_SNoCut__5__2.
Variable x:set.
Variable y:set.
Hypothesis H0: (forall z:set, z :e Repl x eps_ -> SNo z).
Hypothesis H1: SNo (SNoCut (Sing Empty) (Repl x eps_)).
Hypothesis H3: (forall z:set, SNo z -> (forall w:set, w :e Sing Empty -> w < z) -> (forall w:set, w :e Repl x eps_ -> z < w) -> Subq (SNoLev (SNoCut (Sing Empty) (Repl x eps_))) (SNoLev z) /\ SNoEq_ (SNoLev (SNoCut (Sing Empty) (Repl x eps_))) (SNoCut (Sing Empty) (Repl x eps_)) z).
Hypothesis H4: SNo y.
Hypothesis H5: SNoLev y :e binintersect (SNoLev (eps_ x)) (SNoLev (SNoCut (Sing Empty) (Repl x eps_))).
Hypothesis H6: y < SNoCut (Sing Empty) (Repl x eps_).
Hypothesis H7: (forall z:set, z :e Sing Empty -> z < y).
Theorem Conj_eps_SNoCut__5__2: ~ (forall z:set, z :e Repl x eps_ -> y < z).
Admitted.

End Conj_eps_SNoCut__5__2.
(** Conj_eps_SNoCut__6__5 TMap7RCHu1waWo4TxmKcjmpbz8GKQY6tFqh bounty of about 25 bars **)
Section Conj_eps_SNoCut__6__5.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e omega.
Hypothesis H1: (forall z:set, z :e Repl x eps_ -> SNo z).
Hypothesis H2: SNo (SNoCut (Sing Empty) (Repl x eps_)).
Hypothesis H3: (forall z:set, z :e Repl x eps_ -> SNoCut (Sing Empty) (Repl x eps_) < z).
Hypothesis H4: (forall z:set, SNo z -> (forall w:set, w :e Sing Empty -> w < z) -> (forall w:set, w :e Repl x eps_ -> z < w) -> Subq (SNoLev (SNoCut (Sing Empty) (Repl x eps_))) (SNoLev z) /\ SNoEq_ (SNoLev (SNoCut (Sing Empty) (Repl x eps_))) (SNoCut (Sing Empty) (Repl x eps_)) z).
Hypothesis H6: SNoLev y :e binintersect (SNoLev (eps_ x)) (SNoLev (SNoCut (Sing Empty) (Repl x eps_))).
Hypothesis H7: eps_ x < y.
Hypothesis H8: y < SNoCut (Sing Empty) (Repl x eps_).
Theorem Conj_eps_SNoCut__6__5: ~ (forall z:set, z :e Sing Empty -> z < y).
Admitted.

End Conj_eps_SNoCut__6__5.
(** Conj_SNo_etaE__2__1 TMRNa2WLKRRLuwfLFughua4sbsJWH4q9QDk bounty of about 25 bars **)
Section Conj_SNo_etaE__2__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: y < x.
Hypothesis H2: SNo_ z y.
Hypothesis H3: ordinal z.
Hypothesis H4: SNo y.
Theorem Conj_SNo_etaE__2__1: SNoLev y = z -> SNo y /\ SNoLev y :e SNoLev x /\ y < x.
Admitted.

End Conj_SNo_etaE__2__1.
(** Conj_SNo_etaE__3__2 TMNwQD2Q8KgikwWtQC3xRypmDaB9o2Qeoop bounty of about 25 bars **)
Section Conj_SNo_etaE__3__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: y < x.
Hypothesis H1: z :e SNoLev x.
Hypothesis H3: ordinal z.
Theorem Conj_SNo_etaE__3__2: SNo y -> SNo y /\ SNoLev y :e SNoLev x /\ y < x.
Admitted.

End Conj_SNo_etaE__3__2.
(** Conj_SNo_etaE__5__0 TMJitoTRoqNStjvXMfcHsD2CzNYzYn2sJsF bounty of about 25 bars **)
Section Conj_SNo_etaE__5__0.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H1: z :e SNoLev x.
Hypothesis H2: SNo y.
Hypothesis H3: SNoLev y = z.
Theorem Conj_SNo_etaE__5__0: SNoLev y :e SNoLev x -> SNo y /\ SNoLev y :e SNoLev x /\ x < y.
Admitted.

End Conj_SNo_etaE__5__0.
(** Conj_SNo_etaE__5__1 TMMQBSNwvR4q8BZRJicSctkatQUj6pn9s4B bounty of about 25 bars **)
Section Conj_SNo_etaE__5__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: x < y.
Hypothesis H2: SNo y.
Hypothesis H3: SNoLev y = z.
Theorem Conj_SNo_etaE__5__1: SNoLev y :e SNoLev x -> SNo y /\ SNoLev y :e SNoLev x /\ x < y.
Admitted.

End Conj_SNo_etaE__5__1.
(** Conj_SNo_etaE__7__0 TMSVU1xcXQYeamkRBqXc9msW472NiSLYZMq bounty of about 25 bars **)
Section Conj_SNo_etaE__7__0.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H1: z :e SNoLev x.
Hypothesis H2: SNo_ z y.
Hypothesis H3: ordinal z.
Theorem Conj_SNo_etaE__7__0: SNo y -> SNo y /\ SNoLev y :e SNoLev x /\ x < y.
Admitted.

End Conj_SNo_etaE__7__0.
(** Conj_SNo_etaE__12__1 TMZH7xP2gJz7gabR9dZUUqatMFhuQjeN12z bounty of about 25 bars **)
Section Conj_SNo_etaE__12__1.
Variable x:set.
Variable P:prop.
Hypothesis H0: SNo x.
Theorem Conj_SNo_etaE__12__1: ordinal (SNoLev x) -> P.
Admitted.

End Conj_SNo_etaE__12__1.
(** Conj_SNo_rec2_eq_1__1__2 TMMYsKaPdYQ7Txzch9GgTGJvPU1QBCfsTqg bounty of about 25 bars **)
Section Conj_SNo_rec2_eq_1__1__2.
Variable P:(set -> (set -> ((set -> (set -> set)) -> set))).
Variable x:set.
Variable g:(set -> (set -> set)).
Variable y:set.
Variable f:(set -> set).
Variable f2:(set -> set).
Hypothesis H0: (forall z:set, SNo z -> (forall w:set, SNo w -> (forall h:set -> set -> set, forall g2:set -> set -> set, (forall u:set, u :e SNoS_ (SNoLev z) -> (forall v:set, SNo v -> h u v = g2 u v)) -> (forall u:set, u :e SNoS_ (SNoLev w) -> h z u = g2 z u) -> P z w h = P z w g2))).
Hypothesis H1: SNo x.
Hypothesis H3: (forall z:set, z :e SNoS_ (SNoLev y) -> f z = f2 z).
Theorem Conj_SNo_rec2_eq_1__1__2: (forall z:set, z :e SNoS_ (SNoLev x) -> g z = g z) -> P x y (fun z:set => fun w:set => If_i (z = x) (f w) (g z w)) = P x y (fun z:set => fun w:set => If_i (z = x) (f2 w) (g z w)).
Admitted.

End Conj_SNo_rec2_eq_1__1__2.
(** Conj_SNo_rec2_eq__1__1 TML53N3CLmcpvTytFsYxprPnDpSX8nYwswb bounty of about 25 bars **)
Section Conj_SNo_rec2_eq__1__1.
Variable P:(set -> (set -> ((set -> (set -> set)) -> set))).
Variable x:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable y:set.
Hypothesis H0: (forall z:set, SNo z -> (forall w:set, SNo w -> (forall g2:set -> set -> set, forall h2:set -> set -> set, (forall u:set, u :e SNoS_ (SNoLev z) -> (forall v:set, SNo v -> g2 u v = h2 u v)) -> (forall u:set, u :e SNoS_ (SNoLev w) -> g2 z u = h2 z u) -> P z w g2 = P z w h2))).
Hypothesis H2: (forall z:set, z :e SNoS_ (SNoLev x) -> g z = h z).
Hypothesis H3: SNo y.
Theorem Conj_SNo_rec2_eq__1__1: (forall z:set, ordinal z -> (forall w:set, w :e SNoS_ z -> SNo_rec_i (fun u:set => fun f:set -> set => P x u (fun v:set => fun x2:set => If_i (v = x) (f x2) (g v x2))) w = SNo_rec_i (fun u:set => fun f:set -> set => P x u (fun v:set => fun x2:set => If_i (v = x) (f x2) (h v x2))) w)) -> SNo_rec_i (fun z:set => fun f:set -> set => P x z (fun w:set => fun u:set => If_i (w = x) (f u) (g w u))) y = SNo_rec_i (fun z:set => fun f:set -> set => P x z (fun w:set => fun u:set => If_i (w = x) (f u) (h w u))) y.
Admitted.

End Conj_SNo_rec2_eq__1__1.
(** Conj_SNo_rec2_eq__4__1 TMXh7nGgfUKMtiFGeTfpiavob3GMjgnCvYi bounty of about 25 bars **)
Section Conj_SNo_rec2_eq__4__1.
Variable P:(set -> (set -> ((set -> (set -> set)) -> set))).
Variable x:set.
Variable y:set.
Hypothesis H0: (forall z:set, SNo z -> (forall w:set, SNo w -> (forall g:set -> set -> set, forall h:set -> set -> set, (forall u:set, u :e SNoS_ (SNoLev z) -> (forall v:set, SNo v -> g u v = h u v)) -> (forall u:set, u :e SNoS_ (SNoLev w) -> g z u = h z u) -> P z w g = P z w h))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall z:set, SNo z -> (forall g:set -> set -> set, forall h:set -> set -> set, (forall w:set, w :e SNoS_ (SNoLev z) -> g w = h w) -> (fun w:set => If_i (SNo w) (SNo_rec_i (fun u:set => fun f:set -> set => P z u (fun v:set => fun x2:set => If_i (v = z) (f x2) (g v x2))) w) Empty) = (fun w:set => If_i (SNo w) (SNo_rec_i (fun u:set => fun f:set -> set => P z u (fun v:set => fun x2:set => If_i (v = z) (f x2) (h v x2))) w) Empty))).
Hypothesis H4: (forall z:set, z :e SNoS_ (SNoLev x) -> (forall w:set, SNo w -> If_i (z = x) (SNo_rec_i (fun u:set => fun f:set -> set => P x u (fun v:set => fun x2:set => If_i (v = x) (f x2) (SNo_rec_ii (fun y2:set => fun g:set -> set -> set => fun z2:set => If_i (SNo z2) (SNo_rec_i (fun w2:set => fun f2:set -> set => P y2 w2 (fun u2:set => fun v2:set => If_i (u2 = y2) (f2 v2) (g u2 v2))) z2) Empty) v x2))) w) (SNo_rec_ii (fun u:set => fun g:set -> set -> set => fun v:set => If_i (SNo v) (SNo_rec_i (fun x2:set => fun f:set -> set => P u x2 (fun y2:set => fun z2:set => If_i (y2 = u) (f z2) (g y2 z2))) v) Empty) z w) = SNo_rec_ii (fun u:set => fun g:set -> set -> set => fun v:set => If_i (SNo v) (SNo_rec_i (fun x2:set => fun f:set -> set => P u x2 (fun y2:set => fun z2:set => If_i (y2 = u) (f z2) (g y2 z2))) v) Empty) z w)).
Theorem Conj_SNo_rec2_eq__4__1: (forall z:set, z :e SNoS_ (SNoLev y) -> If_i (x = x) (SNo_rec_i (fun w:set => fun f:set -> set => P x w (fun u:set => fun v:set => If_i (u = x) (f v) (SNo_rec_ii (fun x2:set => fun g:set -> set -> set => fun y2:set => If_i (SNo y2) (SNo_rec_i (fun z2:set => fun f2:set -> set => P x2 z2 (fun w2:set => fun u2:set => If_i (w2 = x2) (f2 u2) (g w2 u2))) y2) Empty) u v))) z) (SNo_rec_ii (fun w:set => fun g:set -> set -> set => fun u:set => If_i (SNo u) (SNo_rec_i (fun v:set => fun f:set -> set => P w v (fun x2:set => fun y2:set => If_i (x2 = w) (f y2) (g x2 y2))) u) Empty) x z) = SNo_rec_ii (fun w:set => fun g:set -> set -> set => fun u:set => If_i (SNo u) (SNo_rec_i (fun v:set => fun f:set -> set => P w v (fun x2:set => fun y2:set => If_i (x2 = w) (f y2) (g x2 y2))) u) Empty) x z) -> P x y (fun z:set => fun w:set => If_i (z = x) (SNo_rec_i (fun u:set => fun f:set -> set => P x u (fun v:set => fun x2:set => If_i (v = x) (f x2) (SNo_rec_ii (fun y2:set => fun g:set -> set -> set => fun z2:set => If_i (SNo z2) (SNo_rec_i (fun w2:set => fun f2:set -> set => P y2 w2 (fun u2:set => fun v2:set => If_i (u2 = y2) (f2 v2) (g u2 v2))) z2) Empty) v x2))) w) (SNo_rec_ii (fun u:set => fun g:set -> set -> set => fun v:set => If_i (SNo v) (SNo_rec_i (fun x2:set => fun f:set -> set => P u x2 (fun y2:set => fun z2:set => If_i (y2 = u) (f z2) (g y2 z2))) v) Empty) z w)) = P x y (SNo_rec_ii (fun z:set => fun g:set -> set -> set => fun w:set => If_i (SNo w) (SNo_rec_i (fun u:set => fun f:set -> set => P z u (fun v:set => fun x2:set => If_i (v = z) (f x2) (g v x2))) w) Empty)).
Admitted.

End Conj_SNo_rec2_eq__4__1.
(** Conj_SNo_ordinal_ind__2__1 TMaLcBMMLVMkDnt3hMFd2dG1B7cPd2cAwqi bounty of about 25 bars **)
Section Conj_SNo_ordinal_ind__2__1.
Variable p:(set -> prop).
Variable x:set.
Hypothesis H0: (forall y:set, ordinal y -> (forall z:set, z :e SNoS_ y -> p z)).
Hypothesis H2: ordinal (SNoLev x).
Theorem Conj_SNo_ordinal_ind__2__1: ordinal (ordsucc (SNoLev x)) -> p x.
Admitted.

End Conj_SNo_ordinal_ind__2__1.
(** Conj_SNo_ordinal_ind2__5__1 TMRV7jRCE2Hbm73kXk7UHgitPiadAhKSe5E bounty of about 25 bars **)
Section Conj_SNo_ordinal_ind2__5__1.
Variable r:(set -> (set -> prop)).
Variable x:set.
Variable y:set.
Hypothesis H0: (forall z:set, ordinal z -> (forall w:set, ordinal w -> (forall u:set, u :e SNoS_ z -> (forall v:set, v :e SNoS_ w -> r u v)))).
Hypothesis H2: SNo y.
Hypothesis H3: ordinal (SNoLev x).
Theorem Conj_SNo_ordinal_ind2__5__1: ordinal (ordsucc (SNoLev x)) -> r x y.
Admitted.

End Conj_SNo_ordinal_ind2__5__1.
(** Conj_SNo_ordinal_ind3__6__1 TMdnNAhgcmZDNgNpP3FZXkPp4LVP7wZ4Zwy bounty of about 25 bars **)
Section Conj_SNo_ordinal_ind3__6__1.
Variable P:(set -> (set -> (set -> prop))).
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: (forall w:set, ordinal w -> (forall u:set, ordinal u -> (forall v:set, ordinal v -> (forall x2:set, x2 :e SNoS_ w -> (forall y2:set, y2 :e SNoS_ u -> (forall z2:set, z2 :e SNoS_ v -> P x2 y2 z2)))))).
Hypothesis H2: SNo z.
Hypothesis H3: ordinal (ordsucc (SNoLev x)).
Hypothesis H4: x :e SNoS_ (ordsucc (SNoLev x)).
Theorem Conj_SNo_ordinal_ind3__6__1: ordinal (SNoLev y) -> P x y z.
Admitted.

End Conj_SNo_ordinal_ind3__6__1.
(** Conj_restr_SNo__1__2 TMGAwJLMQCYx8RJYcWuEpPGpVpvdFVZJEua bounty of about 25 bars **)
Section Conj_restr_SNo__1__2.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H1: y :e SNoLev x.
Theorem Conj_restr_SNo__1__2: SNo_ y (binintersect x (SNoElts_ y)) -> SNo (binintersect x (SNoElts_ y)).
Admitted.

End Conj_restr_SNo__1__2.
(** Conj_minus_SNo_prop1__1__2 TMYMaxzU2JUeroyyJpkPCqYSb9Pddj41aNu bounty of about 25 bars **)
Section Conj_minus_SNo_prop1__1__2.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall z:set, z :e SNoS_ (SNoLev x) -> SNo (- z) /\ (forall w:set, w :e SNoL z -> - z < - w) /\ (forall w:set, w :e SNoR z -> - w < - z) /\ SNoCutP (Repl (SNoR z) minus_SNo) (Repl (SNoL z) minus_SNo)).
Hypothesis H3: SNoLev y :e SNoLev x.
Theorem Conj_minus_SNo_prop1__1__2: y :e SNoS_ (SNoLev x) -> SNo (- y) /\ (forall z:set, z :e SNoL y -> - y < - z) /\ (forall z:set, z :e SNoR y -> - z < - y).
Admitted.

End Conj_minus_SNo_prop1__1__2.
(** Conj_minus_SNo_prop1__2__2 TMYMaxzU2JUeroyyJpkPCqYSb9Pddj41aNu bounty of about 25 bars **)
Section Conj_minus_SNo_prop1__2__2.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall z:set, z :e SNoS_ (SNoLev x) -> SNo (- z) /\ (forall w:set, w :e SNoL z -> - z < - w) /\ (forall w:set, w :e SNoR z -> - w < - z) /\ SNoCutP (Repl (SNoR z) minus_SNo) (Repl (SNoL z) minus_SNo)).
Hypothesis H3: SNoLev y :e SNoLev x.
Theorem Conj_minus_SNo_prop1__2__2: y :e SNoS_ (SNoLev x) -> SNo (- y) /\ (forall z:set, z :e SNoL y -> - y < - z) /\ (forall z:set, z :e SNoR y -> - z < - y).
Admitted.

End Conj_minus_SNo_prop1__2__2.
(** Conj_minus_SNo_prop1__4__5 TMc44dd7T2UPwDcwP5tCPP4eguntjsziPKv bounty of about 25 bars **)
Section Conj_minus_SNo_prop1__4__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> SNo (- u) /\ (forall v:set, v :e SNoL u -> - u < - v) /\ (forall v:set, v :e SNoR u -> - v < - u) /\ SNoCutP (Repl (SNoR u) minus_SNo) (Repl (SNoL u) minus_SNo)).
Hypothesis H2: SNo y.
Hypothesis H3: SNoLev y :e SNoLev x.
Hypothesis H4: SNo z.
Hypothesis H6: (forall u:set, u :e SNoR z -> - u < - z).
Hypothesis H7: SNo (- y).
Hypothesis H8: (forall u:set, u :e SNoL y -> - y < - u).
Hypothesis H9: SNo w.
Hypothesis H10: z < w.
Hypothesis H11: w < y.
Hypothesis H12: SNoLev w :e SNoLev z.
Hypothesis H13: SNoLev w :e SNoLev y.
Theorem Conj_minus_SNo_prop1__4__5: w :e SNoS_ (SNoLev x) -> - y < - z.
Admitted.

End Conj_minus_SNo_prop1__4__5.
(** Conj_minus_SNo_prop1__5__7 TMRCM2vqC6pwsN5o8v87EbyJTHhZscDb9Qx bounty of about 25 bars **)
Section Conj_minus_SNo_prop1__5__7.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> SNo (- w) /\ (forall u:set, u :e SNoL w -> - w < - u) /\ (forall u:set, u :e SNoR w -> - u < - w) /\ SNoCutP (Repl (SNoR w) minus_SNo) (Repl (SNoL w) minus_SNo)).
Hypothesis H2: SNo y.
Hypothesis H3: SNoLev y :e SNoLev x.
Hypothesis H4: x < y.
Hypothesis H5: SNo z.
Hypothesis H6: z < x.
Hypothesis H8: (forall w:set, w :e SNoR z -> - w < - z).
Hypothesis H9: SNo (- y).
Hypothesis H10: (forall w:set, w :e SNoL y -> - y < - w).
Theorem Conj_minus_SNo_prop1__5__7: z < y -> - y < - z.
Admitted.

End Conj_minus_SNo_prop1__5__7.
(** Conj_minus_SNo_prop1__5__9 TMGsHhRAEY3AHtueVYYnzTnFQtJyjgBz993 bounty of about 25 bars **)
Section Conj_minus_SNo_prop1__5__9.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> SNo (- w) /\ (forall u:set, u :e SNoL w -> - w < - u) /\ (forall u:set, u :e SNoR w -> - u < - w) /\ SNoCutP (Repl (SNoR w) minus_SNo) (Repl (SNoL w) minus_SNo)).
Hypothesis H2: SNo y.
Hypothesis H3: SNoLev y :e SNoLev x.
Hypothesis H4: x < y.
Hypothesis H5: SNo z.
Hypothesis H6: z < x.
Hypothesis H7: SNo (- z).
Hypothesis H8: (forall w:set, w :e SNoR z -> - w < - z).
Hypothesis H10: (forall w:set, w :e SNoL y -> - y < - w).
Theorem Conj_minus_SNo_prop1__5__9: z < y -> - y < - z.
Admitted.

End Conj_minus_SNo_prop1__5__9.
(** Conj_minus_SNo_prop1__9__3 TMNfkJud6RAy5eEa4GpHHy4Qyj1bK18ndcM bounty of about 25 bars **)
Section Conj_minus_SNo_prop1__9__3.
Variable x:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall y:set, y :e SNoS_ (SNoLev x) -> SNo (- y) /\ (forall z:set, z :e SNoL y -> - y < - z) /\ (forall z:set, z :e SNoR y -> - z < - y) /\ SNoCutP (Repl (SNoR y) minus_SNo) (Repl (SNoL y) minus_SNo)).
Hypothesis H2: (forall y:set, y :e SNoL x -> SNo (- y) /\ (forall z:set, z :e SNoL y -> - y < - z) /\ (forall z:set, z :e SNoR y -> - z < - y)).
Theorem Conj_minus_SNo_prop1__9__3: SNoCutP (Repl (SNoR x) minus_SNo) (Repl (SNoL x) minus_SNo) -> SNo (- x) /\ (forall y:set, y :e SNoL x -> - x < - y) /\ (forall y:set, y :e SNoR x -> - y < - x) /\ SNoCutP (Repl (SNoR x) minus_SNo) (Repl (SNoL x) minus_SNo).
Admitted.

End Conj_minus_SNo_prop1__9__3.
(** Conj_minus_SNo_prop1__11__0 TMGmmVHFG98AkaZHQiK8reWvC1kS6umcyRh bounty of about 25 bars **)
Section Conj_minus_SNo_prop1__11__0.
Variable x:set.
Hypothesis H1: (forall y:set, y :e SNoS_ (SNoLev x) -> SNo (- y) /\ (forall z:set, z :e SNoL y -> - y < - z) /\ (forall z:set, z :e SNoR y -> - z < - y) /\ SNoCutP (Repl (SNoR y) minus_SNo) (Repl (SNoL y) minus_SNo)).
Theorem Conj_minus_SNo_prop1__11__0: (forall y:set, y :e SNoL x -> SNo (- y) /\ (forall z:set, z :e SNoL y -> - y < - z) /\ (forall z:set, z :e SNoR y -> - z < - y)) -> SNo (- x) /\ (forall y:set, y :e SNoL x -> - x < - y) /\ (forall y:set, y :e SNoR x -> - y < - x) /\ SNoCutP (Repl (SNoR x) minus_SNo) (Repl (SNoL x) minus_SNo).
Admitted.

End Conj_minus_SNo_prop1__11__0.
(** Conj_minus_SNo_Lev_lem1__1__2 TMbz4EZRNA5qWZytgvu5NQSdFz3cs5xQT4X bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__1__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: y :e ordsucc (SNoLev z).
Hypothesis H1: z = - w.
Hypothesis H3: Subq (SNoLev (- w)) (SNoLev w).
Hypothesis H4: Subq (SNoLev x) y.
Theorem Conj_minus_SNo_Lev_lem1__1__2: ~ SNoLev w :e y.
Admitted.

End Conj_minus_SNo_Lev_lem1__1__2.
(** Conj_minus_SNo_Lev_lem1__3__1 TMTcdQMXjPauR7ukwDWvXgM1CQD5RfWRvMK bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__3__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (SNoLev x).
Hypothesis H2: z = - w.
Hypothesis H3: SNoLev w :e SNoLev x.
Hypothesis H4: Subq (SNoLev (- w)) (SNoLev w).
Hypothesis H5: ordinal (SNoLev (- w)).
Theorem Conj_minus_SNo_Lev_lem1__3__1: ordinal (ordsucc (SNoLev z)) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__3__1.
(** Conj_minus_SNo_Lev_lem1__3__3 TMGKC3265aZ5x4ucFBVkQ6VSH6Lf3yW87sQ bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__3__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (SNoLev x).
Hypothesis H1: y :e ordsucc (SNoLev z).
Hypothesis H2: z = - w.
Hypothesis H4: Subq (SNoLev (- w)) (SNoLev w).
Hypothesis H5: ordinal (SNoLev (- w)).
Theorem Conj_minus_SNo_Lev_lem1__3__3: ordinal (ordsucc (SNoLev z)) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__3__3.
(** Conj_minus_SNo_Lev_lem1__3__5 TMMiWkkRySxd5enup94kHp8QmguThngroFh bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__3__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (SNoLev x).
Hypothesis H1: y :e ordsucc (SNoLev z).
Hypothesis H2: z = - w.
Hypothesis H3: SNoLev w :e SNoLev x.
Hypothesis H4: Subq (SNoLev (- w)) (SNoLev w).
Theorem Conj_minus_SNo_Lev_lem1__3__5: ordinal (ordsucc (SNoLev z)) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__3__5.
(** Conj_minus_SNo_Lev_lem1__4__5 TMRUHMoq6t53Y4jjAmfAhBWst6aAzq3dPTJ bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__4__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (SNoLev x).
Hypothesis H1: y :e ordsucc (SNoLev z).
Hypothesis H2: z = - w.
Hypothesis H3: SNoLev w :e SNoLev x.
Hypothesis H4: Subq (SNoLev (- w)) (SNoLev w).
Theorem Conj_minus_SNo_Lev_lem1__4__5: ordinal (SNoLev (- w)) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__4__5.
(** Conj_minus_SNo_Lev_lem1__6__0 TMZeWUTfWrms4y6Mkb9RwkpPMAGKzAPahBB bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__6__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H1: y :e ordsucc (SNoLev z).
Hypothesis H2: z = - w.
Hypothesis H3: SNo w.
Hypothesis H4: SNoLev w :e SNoLev x.
Hypothesis H5: Subq (SNoLev (- w)) (SNoLev w).
Theorem Conj_minus_SNo_Lev_lem1__6__0: ordinal (SNoLev w) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__6__0.
(** Conj_minus_SNo_Lev_lem1__6__4 TMTi4TJu6UYp4Rdsc3HT5DJUXUGHZgEX1ad bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__6__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (SNoLev x).
Hypothesis H1: y :e ordsucc (SNoLev z).
Hypothesis H2: z = - w.
Hypothesis H3: SNo w.
Hypothesis H5: Subq (SNoLev (- w)) (SNoLev w).
Theorem Conj_minus_SNo_Lev_lem1__6__4: ordinal (SNoLev w) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__6__4.
(** Conj_minus_SNo_Lev_lem1__7__1 TMNmDQRRPPFEkN5jEiHbXYwEFqRQ9pJKxNT bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__7__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, v :e x -> (forall x2:set, x2 :e SNoS_ v -> Subq (SNoLev (- x2)) (SNoLev x2))).
Hypothesis H2: z :e ordsucc (SNoLev w).
Hypothesis H3: w = - u.
Hypothesis H4: SNo u.
Hypothesis H5: SNoLev u :e SNoLev y.
Hypothesis H6: u :e SNoS_ (ordsucc (SNoLev u)).
Hypothesis H7: ordsucc (SNoLev u) :e x.
Theorem Conj_minus_SNo_Lev_lem1__7__1: Subq (SNoLev (- u)) (SNoLev u) -> z :e SNoLev y.
Admitted.

End Conj_minus_SNo_Lev_lem1__7__1.
(** Conj_minus_SNo_Lev_lem1__10__2 TMbz4EZRNA5qWZytgvu5NQSdFz3cs5xQT4X bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__10__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: y :e ordsucc (SNoLev z).
Hypothesis H1: z = - w.
Hypothesis H3: Subq (SNoLev (- w)) (SNoLev w).
Hypothesis H4: Subq (SNoLev x) y.
Theorem Conj_minus_SNo_Lev_lem1__10__2: ~ SNoLev w :e y.
Admitted.

End Conj_minus_SNo_Lev_lem1__10__2.
(** Conj_minus_SNo_Lev_lem1__12__1 TMTcdQMXjPauR7ukwDWvXgM1CQD5RfWRvMK bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__12__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (SNoLev x).
Hypothesis H2: z = - w.
Hypothesis H3: SNoLev w :e SNoLev x.
Hypothesis H4: Subq (SNoLev (- w)) (SNoLev w).
Hypothesis H5: ordinal (SNoLev (- w)).
Theorem Conj_minus_SNo_Lev_lem1__12__1: ordinal (ordsucc (SNoLev z)) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__12__1.
(** Conj_minus_SNo_Lev_lem1__12__3 TMGKC3265aZ5x4ucFBVkQ6VSH6Lf3yW87sQ bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__12__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (SNoLev x).
Hypothesis H1: y :e ordsucc (SNoLev z).
Hypothesis H2: z = - w.
Hypothesis H4: Subq (SNoLev (- w)) (SNoLev w).
Hypothesis H5: ordinal (SNoLev (- w)).
Theorem Conj_minus_SNo_Lev_lem1__12__3: ordinal (ordsucc (SNoLev z)) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__12__3.
(** Conj_minus_SNo_Lev_lem1__12__5 TMMiWkkRySxd5enup94kHp8QmguThngroFh bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__12__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (SNoLev x).
Hypothesis H1: y :e ordsucc (SNoLev z).
Hypothesis H2: z = - w.
Hypothesis H3: SNoLev w :e SNoLev x.
Hypothesis H4: Subq (SNoLev (- w)) (SNoLev w).
Theorem Conj_minus_SNo_Lev_lem1__12__5: ordinal (ordsucc (SNoLev z)) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__12__5.
(** Conj_minus_SNo_Lev_lem1__13__5 TMRUHMoq6t53Y4jjAmfAhBWst6aAzq3dPTJ bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__13__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (SNoLev x).
Hypothesis H1: y :e ordsucc (SNoLev z).
Hypothesis H2: z = - w.
Hypothesis H3: SNoLev w :e SNoLev x.
Hypothesis H4: Subq (SNoLev (- w)) (SNoLev w).
Theorem Conj_minus_SNo_Lev_lem1__13__5: ordinal (SNoLev (- w)) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__13__5.
(** Conj_minus_SNo_Lev_lem1__15__0 TMZeWUTfWrms4y6Mkb9RwkpPMAGKzAPahBB bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__15__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H1: y :e ordsucc (SNoLev z).
Hypothesis H2: z = - w.
Hypothesis H3: SNo w.
Hypothesis H4: SNoLev w :e SNoLev x.
Hypothesis H5: Subq (SNoLev (- w)) (SNoLev w).
Theorem Conj_minus_SNo_Lev_lem1__15__0: ordinal (SNoLev w) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__15__0.
(** Conj_minus_SNo_Lev_lem1__15__4 TMTi4TJu6UYp4Rdsc3HT5DJUXUGHZgEX1ad bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__15__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: ordinal (SNoLev x).
Hypothesis H1: y :e ordsucc (SNoLev z).
Hypothesis H2: z = - w.
Hypothesis H3: SNo w.
Hypothesis H5: Subq (SNoLev (- w)) (SNoLev w).
Theorem Conj_minus_SNo_Lev_lem1__15__4: ordinal (SNoLev w) -> y :e SNoLev x.
Admitted.

End Conj_minus_SNo_Lev_lem1__15__4.
(** Conj_minus_SNo_Lev_lem1__16__1 TMNmDQRRPPFEkN5jEiHbXYwEFqRQ9pJKxNT bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__16__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, v :e x -> (forall x2:set, x2 :e SNoS_ v -> Subq (SNoLev (- x2)) (SNoLev x2))).
Hypothesis H2: z :e ordsucc (SNoLev w).
Hypothesis H3: w = - u.
Hypothesis H4: SNo u.
Hypothesis H5: SNoLev u :e SNoLev y.
Hypothesis H6: u :e SNoS_ (ordsucc (SNoLev u)).
Hypothesis H7: ordsucc (SNoLev u) :e x.
Theorem Conj_minus_SNo_Lev_lem1__16__1: Subq (SNoLev (- u)) (SNoLev u) -> z :e SNoLev y.
Admitted.

End Conj_minus_SNo_Lev_lem1__16__1.
(** Conj_minus_SNo_Lev_lem1__22__2 TMU48qLBFhsvPGcawgwznT1u9bcVtEjztaz bounty of about 25 bars **)
Section Conj_minus_SNo_Lev_lem1__22__2.
Variable x:set.
Variable y:set.
Hypothesis H0: TransSet x.
Hypothesis H1: (forall z:set, z :e x -> (forall w:set, w :e SNoS_ z -> Subq (SNoLev (- w)) (SNoLev w))).
Hypothesis H3: ordinal (SNoLev y).
Hypothesis H4: SNo y.
Theorem Conj_minus_SNo_Lev_lem1__22__2: SNoCutP (Repl (SNoR y) minus_SNo) (Repl (SNoL y) minus_SNo) -> Subq (SNoLev (- y)) (SNoLev y).
Admitted.

End Conj_minus_SNo_Lev_lem1__22__2.
(** Conj_minus_SNo_invol__5__6 TMJwhNkd4azSgkPG1XNNhfDTvh9J7Bk89Kk bounty of about 25 bars **)
Section Conj_minus_SNo_invol__5__6.
Variable x:set.
Variable y:set.
Hypothesis H0: SNoCutP x y.
Hypothesis H1: (forall z:set, z :e x -> - (- z) = z).
Hypothesis H2: (forall z:set, z :e y -> - (- z) = z).
Hypothesis H3: (forall z:set, z :e x -> SNo z).
Hypothesis H4: (forall z:set, z :e y -> SNo z).
Hypothesis H5: SNo (SNoCut x y).
Hypothesis H7: SNo (- (- (SNoCut x y))).
Theorem Conj_minus_SNo_invol__5__6: Subq (SNoLev (SNoCut x y)) (SNoLev (- (- (SNoCut x y)))) /\ SNoEq_ (SNoLev (SNoCut x y)) (SNoCut x y) (- (- (SNoCut x y))) -> - (- (SNoCut x y)) = SNoCut x y.
Admitted.

End Conj_minus_SNo_invol__5__6.
(** Conj_minus_SNo_invol__8__0 TMHW2CxWY88b3KHixxku1tPi4ij2bKsnqZg bounty of about 25 bars **)
Section Conj_minus_SNo_invol__8__0.
Variable x:set.
Variable y:set.
Hypothesis H1: (forall z:set, z :e x -> - (- z) = z).
Hypothesis H2: (forall z:set, z :e y -> - (- z) = z).
Hypothesis H3: (forall z:set, z :e x -> SNo z).
Hypothesis H4: (forall z:set, z :e y -> SNo z).
Theorem Conj_minus_SNo_invol__8__0: SNo (SNoCut x y) -> - (- (SNoCut x y)) = SNoCut x y.
Admitted.

End Conj_minus_SNo_invol__8__0.
(** Conj_minus_SNo_invol__8__2 TMXsedNVbmFjSwfHzrhgczVZTRQVZfS1BLt bounty of about 25 bars **)
Section Conj_minus_SNo_invol__8__2.
Variable x:set.
Variable y:set.
Hypothesis H0: SNoCutP x y.
Hypothesis H1: (forall z:set, z :e x -> - (- z) = z).
Hypothesis H3: (forall z:set, z :e x -> SNo z).
Hypothesis H4: (forall z:set, z :e y -> SNo z).
Theorem Conj_minus_SNo_invol__8__2: SNo (SNoCut x y) -> - (- (SNoCut x y)) = SNoCut x y.
Admitted.

End Conj_minus_SNo_invol__8__2.
(** Conj_minus_SNoCut_eq_lem__5__2 TMJY5ReEfidqQ4c388Zwk6gKtPa5ataYPgZ bounty of about 25 bars **)
Section Conj_minus_SNoCut_eq_lem__5__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> (forall u:set, forall v:set, SNoCutP u v -> w = SNoCut u v -> - w = SNoCut (Repl v minus_SNo) (Repl u minus_SNo))).
Hypothesis H3: (forall w:set, w :e z -> SNo w).
Hypothesis H4: x = SNoCut y z.
Hypothesis H5: SNoCutP (Repl z minus_SNo) (Repl y minus_SNo).
Hypothesis H6: SNo (SNoCut (Repl z minus_SNo) (Repl y minus_SNo)).
Hypothesis H7: SNoLev (SNoCut (Repl z (fun w:set => - w)) (Repl y (fun w:set => - w))) :e SNoLev (- x).
Theorem Conj_minus_SNoCut_eq_lem__5__2: ~ SNoCut (Repl z minus_SNo) (Repl y minus_SNo) :e SNoS_ (SNoLev x).
Admitted.

End Conj_minus_SNoCut_eq_lem__5__2.
(** Conj_minus_SNoCut_eq_lem__6__2 TMQs6FJxebzQkiULnjLJv2kNcZzc1tm3Gpp bounty of about 25 bars **)
Section Conj_minus_SNoCut_eq_lem__6__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> (forall u:set, forall v:set, SNoCutP u v -> w = SNoCut u v -> - w = SNoCut (Repl v minus_SNo) (Repl u minus_SNo))).
Hypothesis H3: (forall w:set, w :e z -> SNo w).
Hypothesis H4: x = SNoCut y z.
Hypothesis H5: SNoCutP (Repl z minus_SNo) (Repl y minus_SNo).
Hypothesis H6: SNo (SNoCut (Repl z minus_SNo) (Repl y minus_SNo)).
Hypothesis H7: Subq (SNoLev (SNoCut (Repl z (fun w:set => - w)) (Repl y (fun w:set => - w)))) (SNoLev (- x)).
Hypothesis H8: SNoEq_ (SNoLev (SNoCut (Repl z (fun w:set => - w)) (Repl y (fun w:set => - w)))) (SNoCut (Repl z (fun w:set => - w)) (Repl y (fun w:set => - w))) (- x).
Hypothesis H9: ordinal (SNoLev (SNoCut (Repl z minus_SNo) (Repl y minus_SNo))).
Theorem Conj_minus_SNoCut_eq_lem__6__2: ordinal (SNoLev (- x)) -> - x = SNoCut (Repl z minus_SNo) (Repl y minus_SNo).
Admitted.

End Conj_minus_SNoCut_eq_lem__6__2.
(** Conj_minus_SNoCut_eq_lem__6__9 TMNSN1otPMhzUcCre292qvZS7oWjpSniFJR bounty of about 25 bars **)
Section Conj_minus_SNoCut_eq_lem__6__9.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> (forall u:set, forall v:set, SNoCutP u v -> w = SNoCut u v -> - w = SNoCut (Repl v minus_SNo) (Repl u minus_SNo))).
Hypothesis H2: (forall w:set, w :e y -> SNo w).
Hypothesis H3: (forall w:set, w :e z -> SNo w).
Hypothesis H4: x = SNoCut y z.
Hypothesis H5: SNoCutP (Repl z minus_SNo) (Repl y minus_SNo).
Hypothesis H6: SNo (SNoCut (Repl z minus_SNo) (Repl y minus_SNo)).
Hypothesis H7: Subq (SNoLev (SNoCut (Repl z (fun w:set => - w)) (Repl y (fun w:set => - w)))) (SNoLev (- x)).
Hypothesis H8: SNoEq_ (SNoLev (SNoCut (Repl z (fun w:set => - w)) (Repl y (fun w:set => - w)))) (SNoCut (Repl z (fun w:set => - w)) (Repl y (fun w:set => - w))) (- x).
Theorem Conj_minus_SNoCut_eq_lem__6__9: ordinal (SNoLev (- x)) -> - x = SNoCut (Repl z minus_SNo) (Repl y minus_SNo).
Admitted.

End Conj_minus_SNoCut_eq_lem__6__9.
(** Conj_minus_SNoCut_eq_lem__7__5 TMUYD4A4JwUUvGwfXE2qtXXpxcVNTrsFbcD bounty of about 25 bars **)
Section Conj_minus_SNoCut_eq_lem__7__5.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> (forall u:set, forall v:set, SNoCutP u v -> w = SNoCut u v -> - w = SNoCut (Repl v minus_SNo) (Repl u minus_SNo))).
Hypothesis H2: (forall w:set, w :e y -> SNo w).
Hypothesis H3: (forall w:set, w :e z -> SNo w).
Hypothesis H4: x = SNoCut y z.
Hypothesis H6: SNo (SNoCut (Repl z minus_SNo) (Repl y minus_SNo)).
Hypothesis H7: Subq (SNoLev (SNoCut (Repl z (fun w:set => - w)) (Repl y (fun w:set => - w)))) (SNoLev (- x)).
Hypothesis H8: SNoEq_ (SNoLev (SNoCut (Repl z (fun w:set => - w)) (Repl y (fun w:set => - w)))) (SNoCut (Repl z (fun w:set => - w)) (Repl y (fun w:set => - w))) (- x).
Theorem Conj_minus_SNoCut_eq_lem__7__5: ordinal (SNoLev (SNoCut (Repl z minus_SNo) (Repl y minus_SNo))) -> - x = SNoCut (Repl z minus_SNo) (Repl y minus_SNo).
Admitted.

End Conj_minus_SNoCut_eq_lem__7__5.
(** Conj_minus_SNoCut_eq_lem__8__3 TMX2KpJVpuZxNFRvX767d4WM8rsqHBM25nQ bounty of about 25 bars **)
Section Conj_minus_SNoCut_eq_lem__8__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> (forall u:set, forall v:set, SNoCutP u v -> w = SNoCut u v -> - w = SNoCut (Repl v minus_SNo) (Repl u minus_SNo))).
Hypothesis H2: SNoCutP y z.
Hypothesis H4: (forall w:set, w :e z -> SNo w).
Hypothesis H5: x = SNoCut y z.
Hypothesis H6: SNoCutP (Repl z minus_SNo) (Repl y minus_SNo).
Hypothesis H7: SNo (SNoCut (Repl z minus_SNo) (Repl y minus_SNo)).
Hypothesis H8: (forall w:set, SNo w -> (forall u:set, u :e Repl z minus_SNo -> u < w) -> (forall u:set, u :e Repl y minus_SNo -> w < u) -> Subq (SNoLev (SNoCut (Repl z minus_SNo) (Repl y minus_SNo))) (SNoLev w) /\ SNoEq_ (SNoLev (SNoCut (Repl z minus_SNo) (Repl y minus_SNo))) (SNoCut (Repl z minus_SNo) (Repl y minus_SNo)) w).
Hypothesis H9: (forall w:set, w :e Repl z minus_SNo -> w < - x).
Theorem Conj_minus_SNoCut_eq_lem__8__3: (forall w:set, w :e Repl y minus_SNo -> - x < w) -> - x = SNoCut (Repl z minus_SNo) (Repl y minus_SNo).
Admitted.

End Conj_minus_SNoCut_eq_lem__8__3.
(** Conj_minus_SNoCut_eq_lem__11__3 TMKGQeB1XUrhM9NfGuRKuUiMi2HJpfwBiic bounty of about 25 bars **)
Section Conj_minus_SNoCut_eq_lem__11__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> (forall u:set, forall v:set, SNoCutP u v -> w = SNoCut u v -> - w = SNoCut (Repl v minus_SNo) (Repl u minus_SNo))).
Hypothesis H2: SNoCutP y z.
Hypothesis H4: (forall w:set, w :e z -> SNo w).
Hypothesis H5: x = SNoCut y z.
Theorem Conj_minus_SNoCut_eq_lem__11__3: SNo (SNoCut y z) -> - x = SNoCut (Repl z minus_SNo) (Repl y minus_SNo).
Admitted.

End Conj_minus_SNoCut_eq_lem__11__3.
(** Conj_minus_SNoCut_eq_lem__11__5 TMbRofhjHsY9yRSNkXz96bUsSSPJxZGpbt4 bounty of about 25 bars **)
Section Conj_minus_SNoCut_eq_lem__11__5.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> (forall u:set, forall v:set, SNoCutP u v -> w = SNoCut u v -> - w = SNoCut (Repl v minus_SNo) (Repl u minus_SNo))).
Hypothesis H2: SNoCutP y z.
Hypothesis H3: (forall w:set, w :e y -> SNo w).
Hypothesis H4: (forall w:set, w :e z -> SNo w).
Theorem Conj_minus_SNoCut_eq_lem__11__5: SNo (SNoCut y z) -> - x = SNoCut (Repl z minus_SNo) (Repl y minus_SNo).
Admitted.

End Conj_minus_SNoCut_eq_lem__11__5.
(** Conj_add_SNo_prop1__1__1 TMQbpF2vyGvRi3eTTudZXQqybuv9mEMX1Nf bounty of about 25 bars **)
Section Conj_add_SNo_prop1__1__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: SNoLev z :e SNoLev x.
Theorem Conj_add_SNo_prop1__1__1: z :e SNoS_ (SNoLev x) -> SNo (z + y) /\ (forall w:set, w :e SNoL z -> (w + y) < z + y) /\ (forall w:set, w :e SNoR z -> (z + y) < w + y) /\ (forall w:set, w :e SNoL y -> (z + w) < z + y) /\ (forall w:set, w :e SNoR y -> (z + y) < z + w) /\ SNoCutP (binunion (Repl (SNoL z) (fun w:set => w + y)) (Repl (SNoL y) (add_SNo z))) (binunion (Repl (SNoR z) (fun w:set => w + y)) (Repl (SNoR y) (add_SNo z))).
Admitted.

End Conj_add_SNo_prop1__1__1.
(** Conj_add_SNo_prop1__2__1 TMQbpF2vyGvRi3eTTudZXQqybuv9mEMX1Nf bounty of about 25 bars **)
Section Conj_add_SNo_prop1__2__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: SNoLev z :e SNoLev x.
Theorem Conj_add_SNo_prop1__2__1: z :e SNoS_ (SNoLev x) -> SNo (z + y) /\ (forall w:set, w :e SNoL z -> (w + y) < z + y) /\ (forall w:set, w :e SNoR z -> (z + y) < w + y) /\ (forall w:set, w :e SNoL y -> (z + w) < z + y) /\ (forall w:set, w :e SNoR y -> (z + y) < z + w) /\ SNoCutP (binunion (Repl (SNoL z) (fun w:set => w + y)) (Repl (SNoL y) (add_SNo z))) (binunion (Repl (SNoR z) (fun w:set => w + y)) (Repl (SNoR y) (add_SNo z))).
Admitted.

End Conj_add_SNo_prop1__2__1.
(** Conj_add_SNo_prop1__3__2 TMHM1qpBJnAKvuTu4rk82JYirdUm9tPbxMS bounty of about 25 bars **)
Section Conj_add_SNo_prop1__3__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev y) -> SNo (x + w) /\ (forall u:set, u :e SNoL x -> (u + w) < x + w) /\ (forall u:set, u :e SNoR x -> (x + w) < u + w) /\ (forall u:set, u :e SNoL w -> (x + u) < x + w) /\ (forall u:set, u :e SNoR w -> (x + w) < x + u) /\ SNoCutP (binunion (Repl (SNoL x) (fun u:set => u + w)) (Repl (SNoL w) (add_SNo x))) (binunion (Repl (SNoR x) (fun u:set => u + w)) (Repl (SNoR w) (add_SNo x)))).
Hypothesis H3: SNoLev z :e SNoLev y.
Theorem Conj_add_SNo_prop1__3__2: z :e SNoS_ (SNoLev y) -> SNo (x + z) /\ (forall w:set, w :e SNoL x -> (w + z) < x + z) /\ (forall w:set, w :e SNoR x -> (x + z) < w + z) /\ (forall w:set, w :e SNoL z -> (x + w) < x + z) /\ (forall w:set, w :e SNoR z -> (x + z) < x + w) /\ SNoCutP (binunion (Repl (SNoL x) (fun w:set => w + z)) (Repl (SNoL z) (add_SNo x))) (binunion (Repl (SNoR x) (fun w:set => w + z)) (Repl (SNoR z) (add_SNo x))).
Admitted.

End Conj_add_SNo_prop1__3__2.
(** Conj_add_SNo_prop1__4__2 TMHM1qpBJnAKvuTu4rk82JYirdUm9tPbxMS bounty of about 25 bars **)
Section Conj_add_SNo_prop1__4__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev y) -> SNo (x + w) /\ (forall u:set, u :e SNoL x -> (u + w) < x + w) /\ (forall u:set, u :e SNoR x -> (x + w) < u + w) /\ (forall u:set, u :e SNoL w -> (x + u) < x + w) /\ (forall u:set, u :e SNoR w -> (x + w) < x + u) /\ SNoCutP (binunion (Repl (SNoL x) (fun u:set => u + w)) (Repl (SNoL w) (add_SNo x))) (binunion (Repl (SNoR x) (fun u:set => u + w)) (Repl (SNoR w) (add_SNo x)))).
Hypothesis H3: SNoLev z :e SNoLev y.
Theorem Conj_add_SNo_prop1__4__2: z :e SNoS_ (SNoLev y) -> SNo (x + z) /\ (forall w:set, w :e SNoL x -> (w + z) < x + z) /\ (forall w:set, w :e SNoR x -> (x + z) < w + z) /\ (forall w:set, w :e SNoL z -> (x + w) < x + z) /\ (forall w:set, w :e SNoR z -> (x + z) < x + w) /\ SNoCutP (binunion (Repl (SNoL x) (fun w:set => w + z)) (Repl (SNoL z) (add_SNo x))) (binunion (Repl (SNoR x) (fun w:set => w + z)) (Repl (SNoR z) (add_SNo x))).
Admitted.

End Conj_add_SNo_prop1__4__2.
(** Conj_add_SNo_prop1__5__5 TMLYedyBf7ofvYkyoZuiAKYb5HbYK1aogzd bounty of about 25 bars **)
Section Conj_add_SNo_prop1__5__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))) -> (forall P:prop, (SNo (v + x2) -> (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) -> (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) -> (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) -> (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) -> P) -> P)).
Hypothesis H1: (forall v:set, v :e SNoS_ (SNoLev y) -> SNo (x + v) /\ (forall x2:set, x2 :e SNoL x -> (x2 + v) < x + v) /\ (forall x2:set, x2 :e SNoR x -> (x + v) < x2 + v) /\ (forall x2:set, x2 :e SNoL v -> (x + x2) < x + v) /\ (forall x2:set, x2 :e SNoR v -> (x + v) < x + x2) /\ SNoCutP (binunion (Repl (SNoL x) (fun x2:set => x2 + v)) (Repl (SNoL v) (add_SNo x))) (binunion (Repl (SNoR x) (fun x2:set => x2 + v)) (Repl (SNoR v) (add_SNo x)))).
Hypothesis H2: SNo z.
Hypothesis H3: SNo (x + z).
Hypothesis H4: (forall v:set, v :e SNoR z -> (x + z) < x + v).
Hypothesis H6: SNo (x + w).
Hypothesis H7: (forall v:set, v :e SNoL w -> (x + v) < x + w).
Hypothesis H8: SNo u.
Hypothesis H9: z < u.
Hypothesis H10: u < w.
Hypothesis H11: SNoLev u :e SNoLev z.
Hypothesis H12: SNoLev u :e SNoLev w.
Hypothesis H13: u :e SNoS_ (SNoLev y).
Theorem Conj_add_SNo_prop1__5__5: SNo (x + u) -> (x + z) < x + w.
Admitted.

End Conj_add_SNo_prop1__5__5.
(** Conj_add_SNo_prop1__5__13 TMGiWmj3rRpgA2Fo8vBHq3ob2rkhDY6VsTe bounty of about 25 bars **)
Section Conj_add_SNo_prop1__5__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))) -> (forall P:prop, (SNo (v + x2) -> (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) -> (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) -> (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) -> (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) -> P) -> P)).
Hypothesis H1: (forall v:set, v :e SNoS_ (SNoLev y) -> SNo (x + v) /\ (forall x2:set, x2 :e SNoL x -> (x2 + v) < x + v) /\ (forall x2:set, x2 :e SNoR x -> (x + v) < x2 + v) /\ (forall x2:set, x2 :e SNoL v -> (x + x2) < x + v) /\ (forall x2:set, x2 :e SNoR v -> (x + v) < x + x2) /\ SNoCutP (binunion (Repl (SNoL x) (fun x2:set => x2 + v)) (Repl (SNoL v) (add_SNo x))) (binunion (Repl (SNoR x) (fun x2:set => x2 + v)) (Repl (SNoR v) (add_SNo x)))).
Hypothesis H2: SNo z.
Hypothesis H3: SNo (x + z).
Hypothesis H4: (forall v:set, v :e SNoR z -> (x + z) < x + v).
Hypothesis H5: SNo w.
Hypothesis H6: SNo (x + w).
Hypothesis H7: (forall v:set, v :e SNoL w -> (x + v) < x + w).
Hypothesis H8: SNo u.
Hypothesis H9: z < u.
Hypothesis H10: u < w.
Hypothesis H11: SNoLev u :e SNoLev z.
Hypothesis H12: SNoLev u :e SNoLev w.
Theorem Conj_add_SNo_prop1__5__13: SNo (x + u) -> (x + z) < x + w.
Admitted.

End Conj_add_SNo_prop1__5__13.
(** Conj_add_SNo_prop1__6__4 TMX1z1mBc5iGivDCfsZzNaVQQjP2eDTttnk bounty of about 25 bars **)
Section Conj_add_SNo_prop1__6__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))) -> (forall P:prop, (SNo (v + x2) -> (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) -> (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) -> (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) -> (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) -> P) -> P)).
Hypothesis H1: SNo y.
Hypothesis H2: (forall v:set, v :e SNoS_ (SNoLev y) -> SNo (x + v) /\ (forall x2:set, x2 :e SNoL x -> (x2 + v) < x + v) /\ (forall x2:set, x2 :e SNoR x -> (x + v) < x2 + v) /\ (forall x2:set, x2 :e SNoL v -> (x + x2) < x + v) /\ (forall x2:set, x2 :e SNoR v -> (x + v) < x + x2) /\ SNoCutP (binunion (Repl (SNoL x) (fun x2:set => x2 + v)) (Repl (SNoL v) (add_SNo x))) (binunion (Repl (SNoR x) (fun x2:set => x2 + v)) (Repl (SNoR v) (add_SNo x)))).
Hypothesis H3: SNo z.
Hypothesis H5: (forall v:set, v :e SNoR z -> (x + z) < x + v).
Hypothesis H6: SNo w.
Hypothesis H7: SNo (x + w).
Hypothesis H8: (forall v:set, v :e SNoL w -> (x + v) < x + w).
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: u < w.
Hypothesis H12: SNoLev u :e SNoLev z.
Hypothesis H13: SNoLev u :e SNoLev w.
Hypothesis H14: SNoLev u :e SNoLev y.
Theorem Conj_add_SNo_prop1__6__4: u :e SNoS_ (SNoLev y) -> (x + z) < x + w.
Admitted.

End Conj_add_SNo_prop1__6__4.
(** Conj_add_SNo_prop1__8__1 TMZJETyhtdueWQKMyKqiHb2zZA88t4QosBt bounty of about 25 bars **)
Section Conj_add_SNo_prop1__8__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, forall v:set, SNo (u + v) /\ (forall x2:set, x2 :e SNoL u -> (x2 + v) < u + v) /\ (forall x2:set, x2 :e SNoR u -> (u + v) < x2 + v) /\ (forall x2:set, x2 :e SNoL v -> (u + x2) < u + v) /\ (forall x2:set, x2 :e SNoR v -> (u + v) < u + x2) /\ SNoCutP (binunion (Repl (SNoL u) (fun x2:set => x2 + v)) (Repl (SNoL v) (add_SNo u))) (binunion (Repl (SNoR u) (fun x2:set => x2 + v)) (Repl (SNoR v) (add_SNo u))) -> (forall P:prop, (SNo (u + v) -> (forall x2:set, x2 :e SNoL u -> (x2 + v) < u + v) -> (forall x2:set, x2 :e SNoR u -> (u + v) < x2 + v) -> (forall x2:set, x2 :e SNoL v -> (u + x2) < u + v) -> (forall x2:set, x2 :e SNoR v -> (u + v) < u + x2) -> P) -> P)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> SNo (x + u) /\ (forall v:set, v :e SNoL x -> (v + u) < x + u) /\ (forall v:set, v :e SNoR x -> (x + u) < v + u) /\ (forall v:set, v :e SNoL u -> (x + v) < x + u) /\ (forall v:set, v :e SNoR u -> (x + u) < x + v) /\ SNoCutP (binunion (Repl (SNoL x) (fun v:set => v + u)) (Repl (SNoL u) (add_SNo x))) (binunion (Repl (SNoR x) (fun v:set => v + u)) (Repl (SNoR u) (add_SNo x)))).
Hypothesis H3: TransSet (SNoLev y).
Hypothesis H4: SNo z.
Hypothesis H5: z < y.
Hypothesis H6: SNo (x + z).
Hypothesis H7: (forall u:set, u :e SNoR z -> (x + z) < x + u).
Hypothesis H8: SNo w.
Hypothesis H9: SNoLev w :e SNoLev y.
Hypothesis H10: y < w.
Hypothesis H11: SNo (x + w).
Hypothesis H12: (forall u:set, u :e SNoL w -> (x + u) < x + w).
Theorem Conj_add_SNo_prop1__8__1: z < w -> (x + z) < x + w.
Admitted.

End Conj_add_SNo_prop1__8__1.
(** Conj_add_SNo_prop1__8__10 TMQ2FVWnir38Dfj24h3U6hRgZoHCxjMHyvD bounty of about 25 bars **)
Section Conj_add_SNo_prop1__8__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, forall v:set, SNo (u + v) /\ (forall x2:set, x2 :e SNoL u -> (x2 + v) < u + v) /\ (forall x2:set, x2 :e SNoR u -> (u + v) < x2 + v) /\ (forall x2:set, x2 :e SNoL v -> (u + x2) < u + v) /\ (forall x2:set, x2 :e SNoR v -> (u + v) < u + x2) /\ SNoCutP (binunion (Repl (SNoL u) (fun x2:set => x2 + v)) (Repl (SNoL v) (add_SNo u))) (binunion (Repl (SNoR u) (fun x2:set => x2 + v)) (Repl (SNoR v) (add_SNo u))) -> (forall P:prop, (SNo (u + v) -> (forall x2:set, x2 :e SNoL u -> (x2 + v) < u + v) -> (forall x2:set, x2 :e SNoR u -> (u + v) < x2 + v) -> (forall x2:set, x2 :e SNoL v -> (u + x2) < u + v) -> (forall x2:set, x2 :e SNoR v -> (u + v) < u + x2) -> P) -> P)).
Hypothesis H1: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> SNo (x + u) /\ (forall v:set, v :e SNoL x -> (v + u) < x + u) /\ (forall v:set, v :e SNoR x -> (x + u) < v + u) /\ (forall v:set, v :e SNoL u -> (x + v) < x + u) /\ (forall v:set, v :e SNoR u -> (x + u) < x + v) /\ SNoCutP (binunion (Repl (SNoL x) (fun v:set => v + u)) (Repl (SNoL u) (add_SNo x))) (binunion (Repl (SNoR x) (fun v:set => v + u)) (Repl (SNoR u) (add_SNo x)))).
Hypothesis H3: TransSet (SNoLev y).
Hypothesis H4: SNo z.
Hypothesis H5: z < y.
Hypothesis H6: SNo (x + z).
Hypothesis H7: (forall u:set, u :e SNoR z -> (x + z) < x + u).
Hypothesis H8: SNo w.
Hypothesis H9: SNoLev w :e SNoLev y.
Hypothesis H11: SNo (x + w).
Hypothesis H12: (forall u:set, u :e SNoL w -> (x + u) < x + w).
Theorem Conj_add_SNo_prop1__8__10: z < w -> (x + z) < x + w.
Admitted.

End Conj_add_SNo_prop1__8__10.
(** Conj_add_SNo_prop1__10__9 TMHm7uoYzB4dWZTHHTnrEDXfuube3z1xSUY bounty of about 25 bars **)
Section Conj_add_SNo_prop1__10__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))) -> (forall P:prop, (SNo (v + x2) -> (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) -> (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) -> (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) -> (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) -> P) -> P)).
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev y) -> SNo (x + v) /\ (forall x2:set, x2 :e SNoL x -> (x2 + v) < x + v) /\ (forall x2:set, x2 :e SNoR x -> (x + v) < x2 + v) /\ (forall x2:set, x2 :e SNoL v -> (x + x2) < x + v) /\ (forall x2:set, x2 :e SNoR v -> (x + v) < x + x2) /\ SNoCutP (binunion (Repl (SNoL x) (fun x2:set => x2 + v)) (Repl (SNoL v) (add_SNo x))) (binunion (Repl (SNoR x) (fun x2:set => x2 + v)) (Repl (SNoR v) (add_SNo x)))).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))))).
Hypothesis H5: TransSet (SNoLev y).
Hypothesis H6: (forall v:set, v :e SNoR x -> SNo (v + y) /\ (forall x2:set, x2 :e SNoL v -> (x2 + y) < v + y) /\ (forall x2:set, x2 :e SNoR v -> (v + y) < x2 + y) /\ (forall x2:set, x2 :e SNoL y -> (v + x2) < v + y) /\ (forall x2:set, x2 :e SNoR y -> (v + y) < v + x2) /\ SNoCutP (binunion (Repl (SNoL v) (fun x2:set => x2 + y)) (Repl (SNoL y) (add_SNo v))) (binunion (Repl (SNoR v) (fun x2:set => x2 + y)) (Repl (SNoR y) (add_SNo v)))).
Hypothesis H7: (forall v:set, v :e SNoL y -> SNo (x + v) /\ (forall x2:set, x2 :e SNoL x -> (x2 + v) < x + v) /\ (forall x2:set, x2 :e SNoR x -> (x + v) < x2 + v) /\ (forall x2:set, x2 :e SNoL v -> (x + x2) < x + v) /\ (forall x2:set, x2 :e SNoR v -> (x + v) < x + x2) /\ SNoCutP (binunion (Repl (SNoL x) (fun x2:set => x2 + v)) (Repl (SNoL v) (add_SNo x))) (binunion (Repl (SNoR x) (fun x2:set => x2 + v)) (Repl (SNoR v) (add_SNo x)))).
Hypothesis H8: (forall v:set, v :e SNoR y -> SNo (x + v) /\ (forall x2:set, x2 :e SNoL x -> (x2 + v) < x + v) /\ (forall x2:set, x2 :e SNoR x -> (x + v) < x2 + v) /\ (forall x2:set, x2 :e SNoL v -> (x + x2) < x + v) /\ (forall x2:set, x2 :e SNoR v -> (x + v) < x + x2) /\ SNoCutP (binunion (Repl (SNoL x) (fun x2:set => x2 + v)) (Repl (SNoL v) (add_SNo x))) (binunion (Repl (SNoR x) (fun x2:set => x2 + v)) (Repl (SNoR v) (add_SNo x)))).
Hypothesis H10: u :e SNoL y.
Hypothesis H11: z = x + u.
Hypothesis H12: SNo u.
Hypothesis H13: SNoLev u :e SNoLev y.
Hypothesis H14: u < y.
Theorem Conj_add_SNo_prop1__10__9: u :e SNoS_ (SNoLev y) -> z < w.
Admitted.

End Conj_add_SNo_prop1__10__9.
(** Conj_add_SNo_prop1__11__8 TMJjD8VWjPjQsD8BY5Cf4iNQ2SyAZD3eguq bounty of about 25 bars **)
Section Conj_add_SNo_prop1__11__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))) -> (forall P:prop, (SNo (v + x2) -> (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) -> (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) -> (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) -> (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) -> P) -> P)).
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))))).
Hypothesis H4: (forall v:set, v :e SNoR y -> SNo (x + v) /\ (forall x2:set, x2 :e SNoL x -> (x2 + v) < x + v) /\ (forall x2:set, x2 :e SNoR x -> (x + v) < x2 + v) /\ (forall x2:set, x2 :e SNoL v -> (x + x2) < x + v) /\ (forall x2:set, x2 :e SNoR v -> (x + v) < x + x2) /\ SNoCutP (binunion (Repl (SNoL x) (fun x2:set => x2 + v)) (Repl (SNoL v) (add_SNo x))) (binunion (Repl (SNoR x) (fun x2:set => x2 + v)) (Repl (SNoR v) (add_SNo x)))).
Hypothesis H5: SNo w.
Hypothesis H6: SNoLev w :e SNoLev x.
Hypothesis H7: w < x.
Hypothesis H9: SNo (w + y).
Hypothesis H10: (forall v:set, v :e SNoR y -> (w + y) < w + v).
Hypothesis H11: u :e SNoR y.
Hypothesis H12: z = x + u.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev y.
Hypothesis H15: y < u.
Theorem Conj_add_SNo_prop1__11__8: u :e SNoS_ (SNoLev y) -> (w + y) < z.
Admitted.

End Conj_add_SNo_prop1__11__8.
(** Conj_add_SNo_prop1__13__13 TMXhoDqXufNnYUqK65nAXv3zKC1pzTtgBvN bounty of about 25 bars **)
Section Conj_add_SNo_prop1__13__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))) -> (forall P:prop, (SNo (v + x2) -> (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) -> (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) -> (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) -> (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) -> P) -> P)).
Hypothesis H1: SNo x.
Hypothesis H2: (forall v:set, v :e SNoS_ (SNoLev x) -> SNo (v + y) /\ (forall x2:set, x2 :e SNoL v -> (x2 + y) < v + y) /\ (forall x2:set, x2 :e SNoR v -> (v + y) < x2 + y) /\ (forall x2:set, x2 :e SNoL y -> (v + x2) < v + y) /\ (forall x2:set, x2 :e SNoR y -> (v + y) < v + x2) /\ SNoCutP (binunion (Repl (SNoL v) (fun x2:set => x2 + y)) (Repl (SNoL y) (add_SNo v))) (binunion (Repl (SNoR v) (fun x2:set => x2 + y)) (Repl (SNoR y) (add_SNo v)))).
Hypothesis H3: SNo z.
Hypothesis H4: SNo (z + y).
Hypothesis H5: (forall v:set, v :e SNoR z -> (z + y) < v + y).
Hypothesis H6: SNo w.
Hypothesis H7: SNo (w + y).
Hypothesis H8: (forall v:set, v :e SNoL w -> (v + y) < w + y).
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: u < w.
Hypothesis H12: SNoLev u :e SNoLev z.
Hypothesis H14: SNoLev u :e SNoLev x.
Theorem Conj_add_SNo_prop1__13__13: u :e SNoS_ (SNoLev x) -> (z + y) < w + y.
Admitted.

End Conj_add_SNo_prop1__13__13.
(** Conj_add_SNo_prop1__14__3 TMbHrxQUgmMPHhFFRw5GuT9N9eLNYCzrWbx bounty of about 25 bars **)
Section Conj_add_SNo_prop1__14__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))) -> (forall P:prop, (SNo (v + x2) -> (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) -> (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) -> (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) -> (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) -> P) -> P)).
Hypothesis H1: SNo x.
Hypothesis H2: (forall v:set, v :e SNoS_ (SNoLev x) -> SNo (v + y) /\ (forall x2:set, x2 :e SNoL v -> (x2 + y) < v + y) /\ (forall x2:set, x2 :e SNoR v -> (v + y) < x2 + y) /\ (forall x2:set, x2 :e SNoL y -> (v + x2) < v + y) /\ (forall x2:set, x2 :e SNoR y -> (v + y) < v + x2) /\ SNoCutP (binunion (Repl (SNoL v) (fun x2:set => x2 + y)) (Repl (SNoL y) (add_SNo v))) (binunion (Repl (SNoR v) (fun x2:set => x2 + y)) (Repl (SNoR y) (add_SNo v)))).
Hypothesis H4: SNo z.
Hypothesis H5: SNoLev z :e SNoLev x.
Hypothesis H6: SNo (z + y).
Hypothesis H7: (forall v:set, v :e SNoR z -> (z + y) < v + y).
Hypothesis H8: SNo w.
Hypothesis H9: SNo (w + y).
Hypothesis H10: (forall v:set, v :e SNoL w -> (v + y) < w + y).
Hypothesis H11: SNo u.
Hypothesis H12: z < u.
Hypothesis H13: u < w.
Hypothesis H14: SNoLev u :e SNoLev z.
Hypothesis H15: SNoLev u :e SNoLev w.
Theorem Conj_add_SNo_prop1__14__3: SNoLev u :e SNoLev x -> (z + y) < w + y.
Admitted.

End Conj_add_SNo_prop1__14__3.
(** Conj_add_SNo_prop1__16__5 TMNFMUEv3yFcwmtyjwitM6wH1sFvdWwjuxG bounty of about 25 bars **)
Section Conj_add_SNo_prop1__16__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))) -> (forall P:prop, (SNo (v + x2) -> (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) -> (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) -> (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) -> (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) -> P) -> P)).
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> SNo (v + y) /\ (forall x2:set, x2 :e SNoL v -> (x2 + y) < v + y) /\ (forall x2:set, x2 :e SNoR v -> (v + y) < x2 + y) /\ (forall x2:set, x2 :e SNoL y -> (v + x2) < v + y) /\ (forall x2:set, x2 :e SNoR y -> (v + y) < v + x2) /\ SNoCutP (binunion (Repl (SNoL v) (fun x2:set => x2 + y)) (Repl (SNoL y) (add_SNo v))) (binunion (Repl (SNoR v) (fun x2:set => x2 + y)) (Repl (SNoR y) (add_SNo v)))).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> SNo (v + x2) /\ (forall y2:set, y2 :e SNoL v -> (y2 + x2) < v + x2) /\ (forall y2:set, y2 :e SNoR v -> (v + x2) < y2 + x2) /\ (forall y2:set, y2 :e SNoL x2 -> (v + y2) < v + x2) /\ (forall y2:set, y2 :e SNoR x2 -> (v + x2) < v + y2) /\ SNoCutP (binunion (Repl (SNoL v) (fun y2:set => y2 + x2)) (Repl (SNoL x2) (add_SNo v))) (binunion (Repl (SNoR v) (fun y2:set => y2 + x2)) (Repl (SNoR x2) (add_SNo v))))).
Hypothesis H6: (forall v:set, v :e SNoL x -> SNo (v + y) /\ (forall x2:set, x2 :e SNoL v -> (x2 + y) < v + y) /\ (forall x2:set, x2 :e SNoR v -> (v + y) < x2 + y) /\ (forall x2:set, x2 :e SNoL y -> (v + x2) < v + y) /\ (forall x2:set, x2 :e SNoR y -> (v + y) < v + x2) /\ SNoCutP (binunion (Repl (SNoL v) (fun x2:set => x2 + y)) (Repl (SNoL y) (add_SNo v))) (binunion (Repl (SNoR v) (fun x2:set => x2 + y)) (Repl (SNoR y) (add_SNo v)))).
Hypothesis H7: (forall v:set, v :e SNoR x -> SNo (v + y) /\ (forall x2:set, x2 :e SNoL v -> (x2 + y) < v + y) /\ (forall x2:set, x2 :e SNoR v -> (v + y) < x2 + y) /\ (forall x2:set, x2 :e SNoL y -> (v + x2) < v + y) /\ (forall x2:set, x2 :e SNoR y -> (v + y) < v + x2) /\ SNoCutP (binunion (Repl (SNoL v) (fun x2:set => x2 + y)) (Repl (SNoL y) (add_SNo v))) (binunion (Repl (SNoR v) (fun x2:set => x2 + y)) (Repl (SNoR y) (add_SNo v)))).
Hypothesis H8: (forall v:set, v :e SNoR y -> SNo (x + v) /\ (forall x2:set, x2 :e SNoL x -> (x2 + v) < x + v) /\ (forall x2:set, x2 :e SNoR x -> (x + v) < x2 + v) /\ (forall x2:set, x2 :e SNoL v -> (x + x2) < x + v) /\ (forall x2:set, x2 :e SNoR v -> (x + v) < x + x2) /\ SNoCutP (binunion (Repl (SNoL x) (fun x2:set => x2 + v)) (Repl (SNoL v) (add_SNo x))) (binunion (Repl (SNoR x) (fun x2:set => x2 + v)) (Repl (SNoR v) (add_SNo x)))).
Hypothesis H9: w :e binunion (Repl (SNoR x) (fun v:set => v + y)) (Repl (SNoR y) (add_SNo x)).
Hypothesis H10: u :e SNoL x.
Hypothesis H11: z = u + y.
Hypothesis H12: SNo u.
Hypothesis H13: SNoLev u :e SNoLev x.
Hypothesis H14: u < x.
Theorem Conj_add_SNo_prop1__16__5: u :e SNoS_ (SNoLev x) -> z < w.
Admitted.

End Conj_add_SNo_prop1__16__5.
(** Conj_add_SNo_prop1__21__2 TMQC3GwuMGCnP4M83sEPpvZeFb6PB2LFTra bounty of about 25 bars **)
Section Conj_add_SNo_prop1__21__2.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Theorem Conj_add_SNo_prop1__21__2: SNo (SNoCut (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x)))) -> SNo (x + y) /\ (forall z:set, z :e SNoL x -> (z + y) < x + y) /\ (forall z:set, z :e SNoR x -> (x + y) < z + y) /\ (forall z:set, z :e SNoL y -> (x + z) < x + y) /\ (forall z:set, z :e SNoR y -> (x + y) < x + z) /\ SNoCutP (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x))).
Admitted.

End Conj_add_SNo_prop1__21__2.
(** Conj_add_SNo_prop1__28__1 TMUWb5q21SbYbkqj22czGW7myn98AaLuYsZ bounty of about 25 bars **)
Section Conj_add_SNo_prop1__28__1.
Variable x:set.
Variable y:set.
Hypothesis H0: (forall z:set, forall w:set, SNo (z + w) /\ (forall u:set, u :e SNoL z -> (u + w) < z + w) /\ (forall u:set, u :e SNoR z -> (z + w) < u + w) /\ (forall u:set, u :e SNoL w -> (z + u) < z + w) /\ (forall u:set, u :e SNoR w -> (z + w) < z + u) /\ SNoCutP (binunion (Repl (SNoL z) (fun u:set => u + w)) (Repl (SNoL w) (add_SNo z))) (binunion (Repl (SNoR z) (fun u:set => u + w)) (Repl (SNoR w) (add_SNo z))) -> (forall P:prop, (SNo (z + w) -> (forall u:set, u :e SNoL z -> (u + w) < z + w) -> (forall u:set, u :e SNoR z -> (z + w) < u + w) -> (forall u:set, u :e SNoL w -> (z + u) < z + w) -> (forall u:set, u :e SNoR w -> (z + w) < z + u) -> P) -> P)).
Hypothesis H2: SNo y.
Hypothesis H3: (forall z:set, z :e SNoS_ (SNoLev x) -> SNo (z + y) /\ (forall w:set, w :e SNoL z -> (w + y) < z + y) /\ (forall w:set, w :e SNoR z -> (z + y) < w + y) /\ (forall w:set, w :e SNoL y -> (z + w) < z + y) /\ (forall w:set, w :e SNoR y -> (z + y) < z + w) /\ SNoCutP (binunion (Repl (SNoL z) (fun w:set => w + y)) (Repl (SNoL y) (add_SNo z))) (binunion (Repl (SNoR z) (fun w:set => w + y)) (Repl (SNoR y) (add_SNo z)))).
Hypothesis H4: (forall z:set, z :e SNoS_ (SNoLev y) -> SNo (x + z) /\ (forall w:set, w :e SNoL x -> (w + z) < x + z) /\ (forall w:set, w :e SNoR x -> (x + z) < w + z) /\ (forall w:set, w :e SNoL z -> (x + w) < x + z) /\ (forall w:set, w :e SNoR z -> (x + z) < x + w) /\ SNoCutP (binunion (Repl (SNoL x) (fun w:set => w + z)) (Repl (SNoL z) (add_SNo x))) (binunion (Repl (SNoR x) (fun w:set => w + z)) (Repl (SNoR z) (add_SNo x)))).
Hypothesis H5: (forall z:set, z :e SNoS_ (SNoLev x) -> (forall w:set, w :e SNoS_ (SNoLev y) -> SNo (z + w) /\ (forall u:set, u :e SNoL z -> (u + w) < z + w) /\ (forall u:set, u :e SNoR z -> (z + w) < u + w) /\ (forall u:set, u :e SNoL w -> (z + u) < z + w) /\ (forall u:set, u :e SNoR w -> (z + w) < z + u) /\ SNoCutP (binunion (Repl (SNoL z) (fun u:set => u + w)) (Repl (SNoL w) (add_SNo z))) (binunion (Repl (SNoR z) (fun u:set => u + w)) (Repl (SNoR w) (add_SNo z))))).
Hypothesis H6: TransSet (SNoLev x).
Theorem Conj_add_SNo_prop1__28__1: ordinal (SNoLev y) -> SNo (x + y) /\ (forall z:set, z :e SNoL x -> (z + y) < x + y) /\ (forall z:set, z :e SNoR x -> (x + y) < z + y) /\ (forall z:set, z :e SNoL y -> (x + z) < x + y) /\ (forall z:set, z :e SNoR y -> (x + y) < x + z) /\ SNoCutP (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x))).
Admitted.

End Conj_add_SNo_prop1__28__1.
(** Conj_add_SNo_com__1__1 TMMr9BebDgWDvTzt31sDU87QgwsZdMcb1By bounty of about 25 bars **)
Section Conj_add_SNo_com__1__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: SNoLev z :e SNoLev x.
Theorem Conj_add_SNo_com__1__1: z :e SNoS_ (SNoLev x) -> z + y = y + z.
Admitted.

End Conj_add_SNo_com__1__1.
(** Conj_add_SNo_com__1__3 TMQ3dCmi7VjLptv3kYXBZ9NZ9a7XTTVzHa5 bounty of about 25 bars **)
Section Conj_add_SNo_com__1__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> w + y = y + w).
Hypothesis H2: SNo z.
Theorem Conj_add_SNo_com__1__3: z :e SNoS_ (SNoLev x) -> z + y = y + z.
Admitted.

End Conj_add_SNo_com__1__3.
(** Conj_add_SNo_com__2__1 TMMr9BebDgWDvTzt31sDU87QgwsZdMcb1By bounty of about 25 bars **)
Section Conj_add_SNo_com__2__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: SNoLev z :e SNoLev x.
Theorem Conj_add_SNo_com__2__1: z :e SNoS_ (SNoLev x) -> z + y = y + z.
Admitted.

End Conj_add_SNo_com__2__1.
(** Conj_add_SNo_com__2__3 TMQ3dCmi7VjLptv3kYXBZ9NZ9a7XTTVzHa5 bounty of about 25 bars **)
Section Conj_add_SNo_com__2__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> w + y = y + w).
Hypothesis H2: SNo z.
Theorem Conj_add_SNo_com__2__3: z :e SNoS_ (SNoLev x) -> z + y = y + z.
Admitted.

End Conj_add_SNo_com__2__3.
(** Conj_add_SNo_com__6__2 TMSdbAk47ZEakrp4zJaRfdbpr9C6kXQmx7r bounty of about 25 bars **)
Section Conj_add_SNo_com__6__2.
Variable x:set.
Variable y:set.
Hypothesis H0: (forall z:set, z :e SNoR x -> z + y = y + z).
Hypothesis H1: (forall z:set, z :e SNoR y -> x + z = z + x).
Hypothesis H3: Repl (SNoL y) (add_SNo x) = Repl (SNoL y) (fun z:set => z + x).
Theorem Conj_add_SNo_com__6__2: Repl (SNoR x) (fun z:set => z + y) = Repl (SNoR x) (add_SNo y) -> SNoCut (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x))) = SNoCut (binunion (Repl (SNoL y) (fun z:set => z + x)) (Repl (SNoL x) (add_SNo y))) (binunion (Repl (SNoR y) (fun z:set => z + x)) (Repl (SNoR x) (add_SNo y))).
Admitted.

End Conj_add_SNo_com__6__2.
(** Conj_add_SNo_com__9__0 TMX6ruLrKqAb7bzfgTV3uomLxXeLCg5jjrU bounty of about 25 bars **)
Section Conj_add_SNo_com__9__0.
Variable x:set.
Variable y:set.
Hypothesis H1: SNo y.
Hypothesis H2: (forall z:set, z :e SNoS_ (SNoLev y) -> x + z = z + x).
Hypothesis H3: (forall z:set, z :e SNoL x -> z + y = y + z).
Hypothesis H4: (forall z:set, z :e SNoR x -> z + y = y + z).
Hypothesis H5: (forall z:set, z :e SNoL y -> x + z = z + x).
Theorem Conj_add_SNo_com__9__0: (forall z:set, z :e SNoR y -> x + z = z + x) -> x + y = y + x.
Admitted.

End Conj_add_SNo_com__9__0.
(** Conj_add_SNo_com__10__1 TMTGNuBh48GHgeyLGF4bb4Gdq3hWYJcMXea bounty of about 25 bars **)
Section Conj_add_SNo_com__10__1.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H2: (forall z:set, z :e SNoS_ (SNoLev y) -> x + z = z + x).
Hypothesis H3: (forall z:set, z :e SNoL x -> z + y = y + z).
Hypothesis H4: (forall z:set, z :e SNoR x -> z + y = y + z).
Theorem Conj_add_SNo_com__10__1: (forall z:set, z :e SNoL y -> x + z = z + x) -> x + y = y + x.
Admitted.

End Conj_add_SNo_com__10__1.
(** Conj_add_SNo_minus_SNo_linv__4__0 TMGF59iGxxsUQDcsZi8viHS8DHm43emcanL bounty of about 25 bars **)
Section Conj_add_SNo_minus_SNo_linv__4__0.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H1: SNo (- x).
Hypothesis H2: y = z + x.
Hypothesis H3: SNo z.
Hypothesis H4: - x < z.
Hypothesis H5: SNo (- z).
Hypothesis H6: - z + z = Empty.
Theorem Conj_add_SNo_minus_SNo_linv__4__0: - z < x -> Empty < y.
Admitted.

End Conj_add_SNo_minus_SNo_linv__4__0.
(** Conj_add_SNo_minus_SNo_linv__8__6 TMTCBnUbcVnTAyupe8YC4zvAzBURvfcHWyD bounty of about 25 bars **)
Section Conj_add_SNo_minus_SNo_linv__8__6.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> - w + w = Empty).
Hypothesis H2: SNo (- x).
Hypothesis H3: y = - x + z.
Hypothesis H4: SNo z.
Hypothesis H5: SNoLev z :e SNoLev x.
Hypothesis H7: SNo (- z).
Theorem Conj_add_SNo_minus_SNo_linv__8__6: - z + z = Empty -> y < Empty.
Admitted.

End Conj_add_SNo_minus_SNo_linv__8__6.
(** Conj_add_SNo_minus_SNo_linv__9__5 TMdGzUydD3SDVNxX8zyvzhrTjpwWMiWYUnd bounty of about 25 bars **)
Section Conj_add_SNo_minus_SNo_linv__9__5.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall w:set, w :e SNoS_ (SNoLev x) -> - w + w = Empty).
Hypothesis H2: SNo (- x).
Hypothesis H3: y = - x + z.
Hypothesis H4: SNo z.
Hypothesis H6: z < x.
Theorem Conj_add_SNo_minus_SNo_linv__9__5: SNo (- z) -> y < Empty.
Admitted.

End Conj_add_SNo_minus_SNo_linv__9__5.
(** Conj_add_SNo_ordinal_ordinal__3__3 TMaFBae8DHzqkLw9HWhhDtDy7yU2BLJEJV3 bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_ordinal__3__3.
Variable x:set.
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal y.
Hypothesis H2: SNo x.
Theorem Conj_add_SNo_ordinal_ordinal__3__3: SNo (x + y) -> ordinal (x + y).
Admitted.

End Conj_add_SNo_ordinal_ordinal__3__3.
(** Conj_add_SNo_ordinal_ordinal__4__1 TMHuBSyrVwnSJLJFTifwFTvXkDUk3LqmWFr bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_ordinal__4__1.
Variable x:set.
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H2: SNo x.
Theorem Conj_add_SNo_ordinal_ordinal__4__1: SNo y -> ordinal (x + y).
Admitted.

End Conj_add_SNo_ordinal_ordinal__4__1.
(** Conj_add_SNo_ordinal_ordinal__4__2 TMXMHL28V7j1WUH1azsPwPtybhuppowfTjv bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_ordinal__4__2.
Variable x:set.
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal y.
Theorem Conj_add_SNo_ordinal_ordinal__4__2: SNo y -> ordinal (x + y).
Admitted.

End Conj_add_SNo_ordinal_ordinal__4__2.
(** Conj_add_SNo_ordinal_SL__1__0 TMaTFttmxYnPgmEbgWdLQb9Ke5tzkbq2atf bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_SL__1__0.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: ordinal (x + y).
Hypothesis H4: SNo (ordsucc x).
Hypothesis H5: ordinal (ordsucc (x + y)).
Hypothesis H6: SNo (ordsucc (x + y)).
Hypothesis H7: SNoLev z :e y.
Hypothesis H8: ordinal (SNoLev z).
Hypothesis H9: SNo z.
Hypothesis H10: ordsucc x + SNoLev z = ordsucc (x + SNoLev z).
Hypothesis H11: SNo (ordsucc x + z).
Hypothesis H12: ordinal (x + SNoLev z).
Hypothesis H13: ordinal (ordsucc x + SNoLev z).
Theorem Conj_add_SNo_ordinal_SL__1__0: SNo (ordsucc x + SNoLev z) -> (ordsucc x + z) < ordsucc (x + y).
Admitted.

End Conj_add_SNo_ordinal_SL__1__0.
(** Conj_add_SNo_ordinal_SL__1__4 TMagMnTJRWaacTqz4M68DbjRns82xUdAymA bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_SL__1__4.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ordinal y.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: ordinal (x + y).
Hypothesis H5: ordinal (ordsucc (x + y)).
Hypothesis H6: SNo (ordsucc (x + y)).
Hypothesis H7: SNoLev z :e y.
Hypothesis H8: ordinal (SNoLev z).
Hypothesis H9: SNo z.
Hypothesis H10: ordsucc x + SNoLev z = ordsucc (x + SNoLev z).
Hypothesis H11: SNo (ordsucc x + z).
Hypothesis H12: ordinal (x + SNoLev z).
Hypothesis H13: ordinal (ordsucc x + SNoLev z).
Theorem Conj_add_SNo_ordinal_SL__1__4: SNo (ordsucc x + SNoLev z) -> (ordsucc x + z) < ordsucc (x + y).
Admitted.

End Conj_add_SNo_ordinal_SL__1__4.
(** Conj_add_SNo_ordinal_SL__6__8 TMJE6wA9R179pjakH1EFJLShz58GZK1AykM bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_SL__6__8.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ordinal x.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: ordinal (x + y).
Hypothesis H4: ordinal (ordsucc (x + y)).
Hypothesis H5: SNo (ordsucc (x + y)).
Hypothesis H6: SNoLev z :e ordsucc x.
Hypothesis H7: ordinal (SNoLev z).
Hypothesis H9: ordinal (SNoLev z + y).
Theorem Conj_add_SNo_ordinal_SL__6__8: SNo (SNoLev z + y) -> (z + y) < ordsucc (x + y).
Admitted.

End Conj_add_SNo_ordinal_SL__6__8.
(** Conj_add_SNo_ordinal_SL__7__1 TMT6Q1Ne4tKhtSHYyhJb8Q5KXRQw1TfrEdJ bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_SL__7__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ordinal x.
Hypothesis H2: SNo x.
Hypothesis H3: SNo y.
Hypothesis H4: ordinal (x + y).
Hypothesis H5: ordinal (ordsucc (x + y)).
Hypothesis H6: SNo (ordsucc (x + y)).
Hypothesis H7: SNoLev z :e ordsucc x.
Hypothesis H8: ordinal (SNoLev z).
Hypothesis H9: SNo z.
Theorem Conj_add_SNo_ordinal_SL__7__1: ordinal (SNoLev z + y) -> (z + y) < ordsucc (x + y).
Admitted.

End Conj_add_SNo_ordinal_SL__7__1.
(** Conj_add_SNo_ordinal_SL__7__3 TMYFj8hNJwk8usjNAB1DzkWx51ZNtFzpYqJ bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_SL__7__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal y.
Hypothesis H2: SNo x.
Hypothesis H4: ordinal (x + y).
Hypothesis H5: ordinal (ordsucc (x + y)).
Hypothesis H6: SNo (ordsucc (x + y)).
Hypothesis H7: SNoLev z :e ordsucc x.
Hypothesis H8: ordinal (SNoLev z).
Hypothesis H9: SNo z.
Theorem Conj_add_SNo_ordinal_SL__7__3: ordinal (SNoLev z + y) -> (z + y) < ordsucc (x + y).
Admitted.

End Conj_add_SNo_ordinal_SL__7__3.
(** Conj_add_SNo_ordinal_SL__11__9 TMdkjd9fhMh4ZvHPtn1sLrBJEBDBJSZkrLz bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_SL__11__9.
Variable x:set.
Variable y:set.
Hypothesis H0: ordinal x.
Hypothesis H1: ordinal y.
Hypothesis H2: (forall z:set, z :e y -> ordsucc x + z = ordsucc (x + z)).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: ordinal (x + y).
Hypothesis H6: ordinal (ordsucc x).
Hypothesis H7: SNo (ordsucc x).
Hypothesis H8: ordinal (ordsucc x + y).
Hypothesis H10: ordsucc (x + y) :e ordsucc x + y.
Theorem Conj_add_SNo_ordinal_SL__11__9: ~ ordinal (ordsucc (x + y)).
Admitted.

End Conj_add_SNo_ordinal_SL__11__9.
(** Conj_add_SNo_ordinal_SL__14__0 TMPuzCEbNAmuev4kGXCya7U7chkJW3MfJyN bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_SL__14__0.
Variable x:set.
Variable y:set.
Hypothesis H1: ordinal y.
Hypothesis H2: (forall z:set, z :e y -> ordsucc x + z = ordsucc (x + z)).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: ordinal (x + y).
Hypothesis H6: ordinal (ordsucc x).
Theorem Conj_add_SNo_ordinal_SL__14__0: SNo (ordsucc x) -> ordsucc x + y = ordsucc (x + y).
Admitted.

End Conj_add_SNo_ordinal_SL__14__0.
(** Conj_add_SNo_ordinal_SR__4__0 TMKzrR1a9aqcMhLSQeiyFYgwCQHvProN8Bg bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_SR__4__0.
Variable x:set.
Variable y:set.
Hypothesis H1: ordinal y.
Theorem Conj_add_SNo_ordinal_SR__4__0: SNo y -> x + ordsucc y = ordsucc (x + y).
Admitted.

End Conj_add_SNo_ordinal_SR__4__0.
(** Conj_add_SNo_ordinal_SR__5__1 TMQ3ME9j8CRf3C1j5v6Xf3dGj6SwY5FjpeC bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_SR__5__1.
Variable x:set.
Variable y:set.
Hypothesis H0: ordinal x.
Theorem Conj_add_SNo_ordinal_SR__5__1: SNo x -> x + ordsucc y = ordsucc (x + y).
Admitted.

End Conj_add_SNo_ordinal_SR__5__1.
(** Conj_add_SNo_ordinal_InR__1__1 TMVjjW9pc9n7Ayt6bsCFaGJNhJ2xjvMPjUj bounty of about 25 bars **)
Section Conj_add_SNo_ordinal_InR__1__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ordinal x.
Hypothesis H2: z :e y.
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: ordinal z.
Theorem Conj_add_SNo_ordinal_InR__1__1: SNo z -> x + z :e x + y.
Admitted.

End Conj_add_SNo_ordinal_InR__1__1.
(** Conj_add_nat_add_SNo__1__1 TMUWXmW5XTH3eedUHHdLT1fgohTdeoTbsLV bounty of about 25 bars **)
Section Conj_add_nat_add_SNo__1__1.
Variable x:set.
Hypothesis H0: ordinal x.
Theorem Conj_add_nat_add_SNo__1__1: (forall y:set, nat_p y -> add_nat x y = x + y) -> (forall y:set, y :e omega -> add_nat x y = x + y).
Admitted.

End Conj_add_nat_add_SNo__1__1.
(** Conj_add_SNo_SNoL_interpolate__2__11 TMPDccnwSGkXWNQfdRA9SDRCoa7d9E87qp8 bounty of about 25 bars **)
Section Conj_add_SNo_SNoL_interpolate__2__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x + y).
Hypothesis H3: SNo z.
Hypothesis H4: (forall u:set, u :e SNoS_ (SNoLev z) -> SNoLev u :e SNoLev (x + y) -> u < x + y -> (exists v:set, v :e SNoL x /\ u <= v + y) \/ (exists v:set, v :e SNoL y /\ u <= x + v)).
Hypothesis H5: SNoLev z :e SNoLev (x + y).
Hypothesis H6: ~ ((exists u:set, u :e SNoL x /\ z <= u + y) \/ (exists u:set, u :e SNoL y /\ z <= x + u)).
Hypothesis H7: w :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNoLev w :e SNoLev z.
Hypothesis H10: z < w.
Theorem Conj_add_SNo_SNoL_interpolate__2__11: ~ w :e SNoS_ (SNoLev z).
Admitted.

End Conj_add_SNo_SNoL_interpolate__2__11.
(** Conj_add_SNo_SNoR_interpolate__1__1 TMVJUyQgEeBpr2MSP1ZC2ZHKS62rPQcU8Dp bounty of about 25 bars **)
Section Conj_add_SNo_SNoR_interpolate__1__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H2: ~ ((exists u:set, u :e SNoR x /\ (u + y) <= z) \/ (exists u:set, u :e SNoR y /\ (x + u) <= z)).
Hypothesis H3: w :e SNoR y.
Hypothesis H4: SNo w.
Theorem Conj_add_SNo_SNoR_interpolate__1__1: SNo (x + w) -> z < x + w.
Admitted.

End Conj_add_SNo_SNoR_interpolate__1__1.
(** Conj_add_SNo_assoc__3__0 TMXsit1Vzi1NNsJuNcvocHtXeNgLzJvooae bounty of about 25 bars **)
Section Conj_add_SNo_assoc__3__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> v + y + z = (v + y) + z).
Hypothesis H4: SNo (y + z).
Hypothesis H5: SNo w.
Hypothesis H6: u :e SNoR x.
Hypothesis H7: (u + y) <= w.
Hypothesis H8: SNo u.
Hypothesis H9: x < u.
Theorem Conj_add_SNo_assoc__3__0: u + y + z = (u + y) + z -> (x + y + z) < w + z.
Admitted.

End Conj_add_SNo_assoc__3__0.
(** Conj_add_SNo_assoc__6__7 TMW1Jjp6Nvat9sxCvmBheLCQTXhsEDkviwo bounty of about 25 bars **)
Section Conj_add_SNo_assoc__6__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> v + y + z = (v + y) + z).
Hypothesis H4: SNo (y + z).
Hypothesis H5: SNo w.
Hypothesis H6: u :e SNoL x.
Hypothesis H8: SNo u.
Hypothesis H9: u < x.
Theorem Conj_add_SNo_assoc__6__7: u + y + z = (u + y) + z -> (w + z) < x + y + z.
Admitted.

End Conj_add_SNo_assoc__6__7.
(** Conj_add_SNo_assoc__7__3 TMXsWRSQ997vqfdp7f9S4kbfZfvgqKkxoAZ bounty of about 25 bars **)
Section Conj_add_SNo_assoc__7__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H4: SNo (x + y).
Hypothesis H5: SNo w.
Hypothesis H6: u :e SNoR z.
Hypothesis H7: (y + u) <= w.
Hypothesis H8: SNo u.
Hypothesis H9: z < u.
Theorem Conj_add_SNo_assoc__7__3: x + y + u = (x + y) + u -> ((x + y) + z) < x + w.
Admitted.

End Conj_add_SNo_assoc__7__3.
(** Conj_add_SNo_assoc__10__0 TMa6BZWrSrLGV7YSyMBPpeMvY3rLHXxFPSC bounty of about 25 bars **)
Section Conj_add_SNo_assoc__10__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev z) -> x + y + v = (x + y) + v).
Hypothesis H4: SNo (x + y).
Hypothesis H5: SNo w.
Hypothesis H6: u :e SNoL z.
Hypothesis H7: w <= y + u.
Hypothesis H8: SNo u.
Hypothesis H9: u < z.
Theorem Conj_add_SNo_assoc__10__0: x + y + u = (x + y) + u -> (x + w) < (x + y) + z.
Admitted.

End Conj_add_SNo_assoc__10__0.
(** Conj_add_SNo_assoc__14__4 TMTuKP6ArXdEmRoimjWtdgMJZ4HRoGW4P4f bounty of about 25 bars **)
Section Conj_add_SNo_assoc__14__4.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall w:set, w :e SNoS_ (SNoLev x) -> w + y + z = (w + y) + z).
Hypothesis H5: (forall w:set, w :e SNoS_ (SNoLev z) -> x + y + w = (x + y) + w).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo (y + z).
Theorem Conj_add_SNo_assoc__14__4: SNoCutP (binunion (Repl (SNoL x) (fun w:set => w + y + z)) (Repl (SNoL (y + z)) (add_SNo x))) (binunion (Repl (SNoR x) (fun w:set => w + y + z)) (Repl (SNoR (y + z)) (add_SNo x))) -> SNoCut (binunion (Repl (SNoL x) (fun w:set => w + y + z)) (Repl (SNoL (y + z)) (add_SNo x))) (binunion (Repl (SNoR x) (fun w:set => w + y + z)) (Repl (SNoR (y + z)) (add_SNo x))) = SNoCut (binunion (Repl (SNoL (x + y)) (fun w:set => w + z)) (Repl (SNoL z) (add_SNo (x + y)))) (binunion (Repl (SNoR (x + y)) (fun w:set => w + z)) (Repl (SNoR z) (add_SNo (x + y)))).
Admitted.

End Conj_add_SNo_assoc__14__4.
(** Conj_add_SNo_cancel_L__2__3 TMQ3vxQuuyn1Q4vk43S1xSA8Zz5J8ZaofiG bounty of about 25 bars **)
Section Conj_add_SNo_cancel_L__2__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H4: SNo (- x).
Theorem Conj_add_SNo_cancel_L__2__3: - x + x + y = y -> y = z.
Admitted.

End Conj_add_SNo_cancel_L__2__3.
(** Conj_minus_add_SNo_distr__1__0 TMJEeETSrTdiebrNZo2udReSYGb37mJUNY6 bounty of about 25 bars **)
Section Conj_minus_add_SNo_distr__1__0.
Variable x:set.
Variable y:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (- x).
Hypothesis H3: SNo (- y).
Hypothesis H4: SNo (x + y).
Theorem Conj_minus_add_SNo_distr__1__0: (x + y) + - (x + y) = (x + y) + - x + - y -> - (x + y) = - x + - y.
Admitted.

End Conj_minus_add_SNo_distr__1__0.
(** Conj_minus_add_SNo_distr__3__2 TMQeaR1rvGbFrxrXdp8YaE98CMMTSoiTegz bounty of about 25 bars **)
Section Conj_minus_add_SNo_distr__3__2.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Theorem Conj_minus_add_SNo_distr__3__2: SNo (- y) -> - (x + y) = - x + - y.
Admitted.

End Conj_minus_add_SNo_distr__3__2.
(** Conj_add_SNo_Lev_bd__3__0 TMbuRaCZBt6Gr3LVPVb1rwEULiauyDEENss bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__3__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable p:(set -> prop).
Variable w:set.
Hypothesis H1: w :e SNoR x.
Hypothesis H2: z = w + y.
Theorem Conj_add_SNo_Lev_bd__3__0: w :e SNoS_ (SNoLev x) -> SNo w -> SNoLev w :e SNoLev x -> x < w -> p (w + y).
Admitted.

End Conj_add_SNo_Lev_bd__3__0.
(** Conj_add_SNo_Lev_bd__6__2 TMRTZ3HrGidEjbTRVuq1tVf4xjohsQ1gibQ bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__6__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: z :e ordsucc (SNoLev (x + w)).
Hypothesis H4: ordinal z.
Hypothesis H5: Subq (SNoLev x + SNoLev y) z.
Hypothesis H6: Subq (SNoLev (x + w)) (SNoLev x + SNoLev w).
Hypothesis H7: SNoLev x + SNoLev w :e SNoLev x + SNoLev y.
Theorem Conj_add_SNo_Lev_bd__6__2: ~ Subq (SNoLev x + SNoLev w) (SNoLev x + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__6__2.
(** Conj_add_SNo_Lev_bd__7__7 TMFy7YVW2vf3xvNmm1QA6bRRvSzYJJKZj5r bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__7__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: SNo w.
Hypothesis H4: SNoLev w :e SNoLev y.
Hypothesis H5: z :e ordsucc (SNoLev (x + w)).
Hypothesis H6: ordinal z.
Hypothesis H8: Subq (SNoLev (x + w)) (SNoLev x + SNoLev w).
Theorem Conj_add_SNo_Lev_bd__7__7: ~ SNoLev x + SNoLev w :e SNoLev x + SNoLev y.
Admitted.

End Conj_add_SNo_Lev_bd__7__7.
(** Conj_add_SNo_Lev_bd__10__5 TMHVYfyhxYKFVawbnbFsZ4HwQkTsi65xnCC bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__10__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: SNo w.
Hypothesis H2: z :e ordsucc (SNoLev (w + y)).
Hypothesis H3: ordinal z.
Hypothesis H4: Subq (SNoLev x + SNoLev y) z.
Hypothesis H6: SNoLev w + SNoLev y :e SNoLev x + SNoLev y.
Theorem Conj_add_SNo_Lev_bd__10__5: ~ Subq z (SNoLev (w + y)).
Admitted.

End Conj_add_SNo_Lev_bd__10__5.
(** Conj_add_SNo_Lev_bd__11__2 TMXgUeJGYffmMUWGm6xudY5g5voEb2CEKTL bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__11__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: z :e ordsucc (SNoLev (w + y)).
Hypothesis H4: ordinal z.
Hypothesis H5: Subq (SNoLev x + SNoLev y) z.
Hypothesis H6: Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Hypothesis H7: SNoLev w + SNoLev y :e SNoLev x + SNoLev y.
Theorem Conj_add_SNo_Lev_bd__11__2: ~ Subq (SNoLev w + SNoLev y) (SNoLev x + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__11__2.
(** Conj_add_SNo_Lev_bd__12__6 TMVCFjRzpyxJX4Ma39CJrKqoDKAEhAxmbtj bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__12__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: SNo w.
Hypothesis H4: SNoLev w :e SNoLev x.
Hypothesis H5: z :e ordsucc (SNoLev (w + y)).
Hypothesis H7: Subq (SNoLev x + SNoLev y) z.
Hypothesis H8: Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Theorem Conj_add_SNo_Lev_bd__12__6: ~ SNoLev w + SNoLev y :e SNoLev x + SNoLev y.
Admitted.

End Conj_add_SNo_Lev_bd__12__6.
(** Conj_add_SNo_Lev_bd__13__3 TMXPkP3ALi7mCddXRumP7vezPZkG7LV6K1J bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__13__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H4: w :e SNoS_ (SNoLev x).
Hypothesis H5: SNo w.
Hypothesis H6: SNoLev w :e SNoLev x.
Hypothesis H7: z :e ordsucc (SNoLev (w + y)).
Hypothesis H8: ordinal z.
Hypothesis H9: Subq (SNoLev x + SNoLev y) z.
Theorem Conj_add_SNo_Lev_bd__13__3: ~ Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__13__3.
(** Conj_add_SNo_Lev_bd__13__5 TMW2nLeL2Rd146GsAgGY4WjrySEBhppfQ6G bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__13__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev x) -> Subq (SNoLev (u + y)) (SNoLev u + SNoLev y)).
Hypothesis H4: w :e SNoS_ (SNoLev x).
Hypothesis H6: SNoLev w :e SNoLev x.
Hypothesis H7: z :e ordsucc (SNoLev (w + y)).
Hypothesis H8: ordinal z.
Hypothesis H9: Subq (SNoLev x + SNoLev y) z.
Theorem Conj_add_SNo_Lev_bd__13__5: ~ Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__13__5.
(** Conj_add_SNo_Lev_bd__13__6 TMbJLfVumt2xXTEw8dH7j5gNxbSBHG8u4mS bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__13__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev x) -> Subq (SNoLev (u + y)) (SNoLev u + SNoLev y)).
Hypothesis H4: w :e SNoS_ (SNoLev x).
Hypothesis H5: SNo w.
Hypothesis H7: z :e ordsucc (SNoLev (w + y)).
Hypothesis H8: ordinal z.
Hypothesis H9: Subq (SNoLev x + SNoLev y) z.
Theorem Conj_add_SNo_Lev_bd__13__6: ~ Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__13__6.
(** Conj_add_SNo_Lev_bd__13__7 TMXCCfK7otff4E9jAQUHzmsLbPY9r6pLSP5 bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__13__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev x) -> Subq (SNoLev (u + y)) (SNoLev u + SNoLev y)).
Hypothesis H4: w :e SNoS_ (SNoLev x).
Hypothesis H5: SNo w.
Hypothesis H6: SNoLev w :e SNoLev x.
Hypothesis H8: ordinal z.
Hypothesis H9: Subq (SNoLev x + SNoLev y) z.
Theorem Conj_add_SNo_Lev_bd__13__7: ~ Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__13__7.
(** Conj_add_SNo_Lev_bd__14__5 TMLam8FtVoJ8UqUYZWgQtQesbKLeHCeQhBi bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__14__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev x) -> Subq (SNoLev (u + y)) (SNoLev u + SNoLev y)).
Hypothesis H4: w :e SNoS_ (SNoLev x).
Hypothesis H6: SNoLev w :e SNoLev x.
Hypothesis H7: z :e ordsucc (SNoLev (w + y)).
Theorem Conj_add_SNo_Lev_bd__14__5: ordinal z -> z :e SNoLev x + SNoLev y.
Admitted.

End Conj_add_SNo_Lev_bd__14__5.
(** Conj_add_SNo_Lev_bd__16__2 TMRTZ3HrGidEjbTRVuq1tVf4xjohsQ1gibQ bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__16__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: z :e ordsucc (SNoLev (x + w)).
Hypothesis H4: ordinal z.
Hypothesis H5: Subq (SNoLev x + SNoLev y) z.
Hypothesis H6: Subq (SNoLev (x + w)) (SNoLev x + SNoLev w).
Hypothesis H7: SNoLev x + SNoLev w :e SNoLev x + SNoLev y.
Theorem Conj_add_SNo_Lev_bd__16__2: ~ Subq (SNoLev x + SNoLev w) (SNoLev x + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__16__2.
(** Conj_add_SNo_Lev_bd__17__7 TMFy7YVW2vf3xvNmm1QA6bRRvSzYJJKZj5r bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__17__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: SNo w.
Hypothesis H4: SNoLev w :e SNoLev y.
Hypothesis H5: z :e ordsucc (SNoLev (x + w)).
Hypothesis H6: ordinal z.
Hypothesis H8: Subq (SNoLev (x + w)) (SNoLev x + SNoLev w).
Theorem Conj_add_SNo_Lev_bd__17__7: ~ SNoLev x + SNoLev w :e SNoLev x + SNoLev y.
Admitted.

End Conj_add_SNo_Lev_bd__17__7.
(** Conj_add_SNo_Lev_bd__20__5 TMHVYfyhxYKFVawbnbFsZ4HwQkTsi65xnCC bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__20__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: SNo w.
Hypothesis H2: z :e ordsucc (SNoLev (w + y)).
Hypothesis H3: ordinal z.
Hypothesis H4: Subq (SNoLev x + SNoLev y) z.
Hypothesis H6: SNoLev w + SNoLev y :e SNoLev x + SNoLev y.
Theorem Conj_add_SNo_Lev_bd__20__5: ~ Subq z (SNoLev (w + y)).
Admitted.

End Conj_add_SNo_Lev_bd__20__5.
(** Conj_add_SNo_Lev_bd__21__2 TMXgUeJGYffmMUWGm6xudY5g5voEb2CEKTL bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__21__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: z :e ordsucc (SNoLev (w + y)).
Hypothesis H4: ordinal z.
Hypothesis H5: Subq (SNoLev x + SNoLev y) z.
Hypothesis H6: Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Hypothesis H7: SNoLev w + SNoLev y :e SNoLev x + SNoLev y.
Theorem Conj_add_SNo_Lev_bd__21__2: ~ Subq (SNoLev w + SNoLev y) (SNoLev x + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__21__2.
(** Conj_add_SNo_Lev_bd__22__6 TMVCFjRzpyxJX4Ma39CJrKqoDKAEhAxmbtj bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__22__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: SNo w.
Hypothesis H4: SNoLev w :e SNoLev x.
Hypothesis H5: z :e ordsucc (SNoLev (w + y)).
Hypothesis H7: Subq (SNoLev x + SNoLev y) z.
Hypothesis H8: Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Theorem Conj_add_SNo_Lev_bd__22__6: ~ SNoLev w + SNoLev y :e SNoLev x + SNoLev y.
Admitted.

End Conj_add_SNo_Lev_bd__22__6.
(** Conj_add_SNo_Lev_bd__23__3 TMXPkP3ALi7mCddXRumP7vezPZkG7LV6K1J bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__23__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H4: w :e SNoS_ (SNoLev x).
Hypothesis H5: SNo w.
Hypothesis H6: SNoLev w :e SNoLev x.
Hypothesis H7: z :e ordsucc (SNoLev (w + y)).
Hypothesis H8: ordinal z.
Hypothesis H9: Subq (SNoLev x + SNoLev y) z.
Theorem Conj_add_SNo_Lev_bd__23__3: ~ Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__23__3.
(** Conj_add_SNo_Lev_bd__23__5 TMW2nLeL2Rd146GsAgGY4WjrySEBhppfQ6G bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__23__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev x) -> Subq (SNoLev (u + y)) (SNoLev u + SNoLev y)).
Hypothesis H4: w :e SNoS_ (SNoLev x).
Hypothesis H6: SNoLev w :e SNoLev x.
Hypothesis H7: z :e ordsucc (SNoLev (w + y)).
Hypothesis H8: ordinal z.
Hypothesis H9: Subq (SNoLev x + SNoLev y) z.
Theorem Conj_add_SNo_Lev_bd__23__5: ~ Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__23__5.
(** Conj_add_SNo_Lev_bd__23__6 TMbJLfVumt2xXTEw8dH7j5gNxbSBHG8u4mS bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__23__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev x) -> Subq (SNoLev (u + y)) (SNoLev u + SNoLev y)).
Hypothesis H4: w :e SNoS_ (SNoLev x).
Hypothesis H5: SNo w.
Hypothesis H7: z :e ordsucc (SNoLev (w + y)).
Hypothesis H8: ordinal z.
Hypothesis H9: Subq (SNoLev x + SNoLev y) z.
Theorem Conj_add_SNo_Lev_bd__23__6: ~ Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__23__6.
(** Conj_add_SNo_Lev_bd__23__7 TMXCCfK7otff4E9jAQUHzmsLbPY9r6pLSP5 bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__23__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev x) -> Subq (SNoLev (u + y)) (SNoLev u + SNoLev y)).
Hypothesis H4: w :e SNoS_ (SNoLev x).
Hypothesis H5: SNo w.
Hypothesis H6: SNoLev w :e SNoLev x.
Hypothesis H8: ordinal z.
Hypothesis H9: Subq (SNoLev x + SNoLev y) z.
Theorem Conj_add_SNo_Lev_bd__23__7: ~ Subq (SNoLev (w + y)) (SNoLev w + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__23__7.
(** Conj_add_SNo_Lev_bd__24__5 TMLam8FtVoJ8UqUYZWgQtQesbKLeHCeQhBi bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__24__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev x) -> Subq (SNoLev (u + y)) (SNoLev u + SNoLev y)).
Hypothesis H4: w :e SNoS_ (SNoLev x).
Hypothesis H6: SNoLev w :e SNoLev x.
Hypothesis H7: z :e ordsucc (SNoLev (w + y)).
Theorem Conj_add_SNo_Lev_bd__24__5: ordinal z -> z :e SNoLev x + SNoLev y.
Admitted.

End Conj_add_SNo_Lev_bd__24__5.
(** Conj_add_SNo_Lev_bd__29__1 TMLrX1FqqLWS1fFPzPzads9SeKw15jcheat bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__29__1.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall z:set, z :e SNoS_ (SNoLev x) -> Subq (SNoLev (z + y)) (SNoLev z + SNoLev y)).
Hypothesis H4: (forall z:set, z :e SNoS_ (SNoLev y) -> Subq (SNoLev (x + z)) (SNoLev x + SNoLev z)).
Hypothesis H5: SNoLev (SNoCut (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x)))) :e ordsucc (binunion (famunion (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (fun z:set => ordsucc (SNoLev z))) (famunion (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x))) (fun z:set => ordsucc (SNoLev z)))).
Hypothesis H6: (forall z:set, z :e Repl (SNoL x) (fun w:set => w + y) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev x) -> z = w + y -> SNo w -> SNoLev w :e SNoLev x -> w < x -> p (w + y)) -> p z)).
Hypothesis H7: (forall z:set, z :e Repl (SNoL y) (add_SNo x) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev y) -> z = x + w -> SNo w -> SNoLev w :e SNoLev y -> w < y -> p (x + w)) -> p z)).
Hypothesis H8: (forall z:set, z :e Repl (SNoR x) (fun w:set => w + y) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev x) -> z = w + y -> SNo w -> SNoLev w :e SNoLev x -> x < w -> p (w + y)) -> p z)).
Hypothesis H9: (forall z:set, z :e Repl (SNoR y) (add_SNo x) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev y) -> z = x + w -> SNo w -> SNoLev w :e SNoLev y -> y < w -> p (x + w)) -> p z)).
Hypothesis H10: (forall z:set, z :e Repl (SNoL x) (fun w:set => w + y) -> SNo z).
Hypothesis H11: (forall z:set, z :e Repl (SNoL y) (add_SNo x) -> SNo z).
Theorem Conj_add_SNo_Lev_bd__29__1: (forall z:set, z :e Repl (SNoR x) (fun w:set => w + y) -> SNo z) -> Subq (SNoLev (SNoCut (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x))))) (SNoLev x + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__29__1.
(** Conj_add_SNo_Lev_bd__29__4 TMSXhzeQQJdgvuVACNwLkFgbAje914asX6N bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__29__4.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall z:set, z :e SNoS_ (SNoLev x) -> Subq (SNoLev (z + y)) (SNoLev z + SNoLev y)).
Hypothesis H5: SNoLev (SNoCut (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x)))) :e ordsucc (binunion (famunion (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (fun z:set => ordsucc (SNoLev z))) (famunion (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x))) (fun z:set => ordsucc (SNoLev z)))).
Hypothesis H6: (forall z:set, z :e Repl (SNoL x) (fun w:set => w + y) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev x) -> z = w + y -> SNo w -> SNoLev w :e SNoLev x -> w < x -> p (w + y)) -> p z)).
Hypothesis H7: (forall z:set, z :e Repl (SNoL y) (add_SNo x) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev y) -> z = x + w -> SNo w -> SNoLev w :e SNoLev y -> w < y -> p (x + w)) -> p z)).
Hypothesis H8: (forall z:set, z :e Repl (SNoR x) (fun w:set => w + y) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev x) -> z = w + y -> SNo w -> SNoLev w :e SNoLev x -> x < w -> p (w + y)) -> p z)).
Hypothesis H9: (forall z:set, z :e Repl (SNoR y) (add_SNo x) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev y) -> z = x + w -> SNo w -> SNoLev w :e SNoLev y -> y < w -> p (x + w)) -> p z)).
Hypothesis H10: (forall z:set, z :e Repl (SNoL x) (fun w:set => w + y) -> SNo z).
Hypothesis H11: (forall z:set, z :e Repl (SNoL y) (add_SNo x) -> SNo z).
Theorem Conj_add_SNo_Lev_bd__29__4: (forall z:set, z :e Repl (SNoR x) (fun w:set => w + y) -> SNo z) -> Subq (SNoLev (SNoCut (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x))))) (SNoLev x + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__29__4.
(** Conj_add_SNo_Lev_bd__29__5 TMQXTk36PjeswuqCuKuaL9UtahR13RK4TjB bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__29__5.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall z:set, z :e SNoS_ (SNoLev x) -> Subq (SNoLev (z + y)) (SNoLev z + SNoLev y)).
Hypothesis H4: (forall z:set, z :e SNoS_ (SNoLev y) -> Subq (SNoLev (x + z)) (SNoLev x + SNoLev z)).
Hypothesis H6: (forall z:set, z :e Repl (SNoL x) (fun w:set => w + y) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev x) -> z = w + y -> SNo w -> SNoLev w :e SNoLev x -> w < x -> p (w + y)) -> p z)).
Hypothesis H7: (forall z:set, z :e Repl (SNoL y) (add_SNo x) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev y) -> z = x + w -> SNo w -> SNoLev w :e SNoLev y -> w < y -> p (x + w)) -> p z)).
Hypothesis H8: (forall z:set, z :e Repl (SNoR x) (fun w:set => w + y) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev x) -> z = w + y -> SNo w -> SNoLev w :e SNoLev x -> x < w -> p (w + y)) -> p z)).
Hypothesis H9: (forall z:set, z :e Repl (SNoR y) (add_SNo x) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev y) -> z = x + w -> SNo w -> SNoLev w :e SNoLev y -> y < w -> p (x + w)) -> p z)).
Hypothesis H10: (forall z:set, z :e Repl (SNoL x) (fun w:set => w + y) -> SNo z).
Hypothesis H11: (forall z:set, z :e Repl (SNoL y) (add_SNo x) -> SNo z).
Theorem Conj_add_SNo_Lev_bd__29__5: (forall z:set, z :e Repl (SNoR x) (fun w:set => w + y) -> SNo z) -> Subq (SNoLev (SNoCut (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x))))) (SNoLev x + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__29__5.
(** Conj_add_SNo_Lev_bd__34__6 TMTSVhgQwhRwZ3p8XDLdqtkioQTu9dVgnwZ bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__34__6.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: ordinal (SNoLev x + SNoLev y).
Hypothesis H3: (forall z:set, z :e SNoS_ (SNoLev x) -> Subq (SNoLev (z + y)) (SNoLev z + SNoLev y)).
Hypothesis H4: (forall z:set, z :e SNoS_ (SNoLev y) -> Subq (SNoLev (x + z)) (SNoLev x + SNoLev z)).
Hypothesis H5: SNoLev (SNoCut (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x)))) :e ordsucc (binunion (famunion (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (fun z:set => ordsucc (SNoLev z))) (famunion (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x))) (fun z:set => ordsucc (SNoLev z)))).
Theorem Conj_add_SNo_Lev_bd__34__6: (forall z:set, z :e Repl (SNoL y) (add_SNo x) -> (forall p:set -> prop, (forall w:set, w :e SNoS_ (SNoLev y) -> z = x + w -> SNo w -> SNoLev w :e SNoLev y -> w < y -> p (x + w)) -> p z)) -> Subq (SNoLev (SNoCut (binunion (Repl (SNoL x) (fun z:set => z + y)) (Repl (SNoL y) (add_SNo x))) (binunion (Repl (SNoR x) (fun z:set => z + y)) (Repl (SNoR y) (add_SNo x))))) (SNoLev x + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__34__6.
(** Conj_add_SNo_Lev_bd__38__0 TMYuMyHAiGLVkiryeWSrYc3pjFaLxbdxwc7 bounty of about 25 bars **)
Section Conj_add_SNo_Lev_bd__38__0.
Variable x:set.
Variable y:set.
Hypothesis H1: SNo y.
Theorem Conj_add_SNo_Lev_bd__38__0: SNo (x + y) -> (forall z:set, z :e SNoS_ (SNoLev x) -> Subq (SNoLev (z + y)) (SNoLev z + SNoLev y)) -> (forall z:set, z :e SNoS_ (SNoLev y) -> Subq (SNoLev (x + z)) (SNoLev x + SNoLev z)) -> (forall z:set, z :e SNoS_ (SNoLev x) -> (forall w:set, w :e SNoS_ (SNoLev y) -> Subq (SNoLev (z + w)) (SNoLev z + SNoLev w))) -> Subq (SNoLev (x + y)) (SNoLev x + SNoLev y).
Admitted.

End Conj_add_SNo_Lev_bd__38__0.
(** Conj_add_SNo_SNoS_omega__1__2 TMHecR1j4ZYbMm1pvFmw1Bm8bxJUrEY5KgA bounty of about 25 bars **)
Section Conj_add_SNo_SNoS_omega__1__2.
Variable x:set.
Variable y:set.
Hypothesis H0: SNoLev x :e omega.
Hypothesis H1: SNo x.
Hypothesis H3: SNo y.
Theorem Conj_add_SNo_SNoS_omega__1__2: ordinal (SNoLev (x + y)) -> SNoLev (x + y) :e omega.
Admitted.

End Conj_add_SNo_SNoS_omega__1__2.
(** Conj_add_SNo_minus_Lt_lem__2__6 TMLkvCjKdTWPrJaMwtmGX7t1XXAsEUhaECE bounty of about 25 bars **)
Section Conj_add_SNo_minus_Lt_lem__2__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: SNo u.
Hypothesis H5: SNo v.
Hypothesis H7: SNo (- z).
Hypothesis H8: SNo (- v).
Theorem Conj_add_SNo_minus_Lt_lem__2__6: SNo (x + y) -> (x + y + - z) < w + u + - v.
Admitted.

End Conj_add_SNo_minus_Lt_lem__2__6.
(** Conj_add_SNo_Lt_subprop3c__2__3 TMQaci4f6pqnx4w8NLzy5jwpmUCcAu6Aa3C bounty of about 25 bars **)
Section Conj_add_SNo_Lt_subprop3c__2__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H4: SNo u.
Hypothesis H5: SNo v.
Hypothesis H6: (y + v) < u.
Hypothesis H7: (x + z) < v + w.
Theorem Conj_add_SNo_Lt_subprop3c__2__3: SNo (x + z) -> (x + y + z) < w + u.
Admitted.

End Conj_add_SNo_Lt_subprop3c__2__3.
(** Conj_add_SNo_Lt_subprop3c__2__7 TMaot6HShaD8fYeXCtFqFkcZq8AkD1BQ7W6 bounty of about 25 bars **)
Section Conj_add_SNo_Lt_subprop3c__2__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: SNo u.
Hypothesis H5: SNo v.
Hypothesis H6: (y + v) < u.
Theorem Conj_add_SNo_Lt_subprop3c__2__7: SNo (x + z) -> (x + y + z) < w + u.
Admitted.

End Conj_add_SNo_Lt_subprop3c__2__7.
(** Conj_add_SNo_Lt_subprop3c__3__0 TMUrc8oR5bhWTwTv55xSL2e2aMEfaTAmjCc bounty of about 25 bars **)
Section Conj_add_SNo_Lt_subprop3c__3__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: SNo u.
Hypothesis H5: SNo v.
Hypothesis H6: SNo x2.
Hypothesis H7: SNo y2.
Hypothesis H8: (x + v) < x2 + y2.
Hypothesis H9: (y + y2) < u.
Hypothesis H10: (x2 + z) < w + v.
Theorem Conj_add_SNo_Lt_subprop3c__3__0: (x + z) < y2 + w -> (x + y + z) < w + u.
Admitted.

End Conj_add_SNo_Lt_subprop3c__3__0.
(** Conj_add_SNo_Lt_subprop3c__3__6 TMQKTMTy1p4K93n7jXgxNHg26euZrRjZTQc bounty of about 25 bars **)
Section Conj_add_SNo_Lt_subprop3c__3__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: SNo u.
Hypothesis H5: SNo v.
Hypothesis H7: SNo y2.
Hypothesis H8: (x + v) < x2 + y2.
Hypothesis H9: (y + y2) < u.
Hypothesis H10: (x2 + z) < w + v.
Theorem Conj_add_SNo_Lt_subprop3c__3__6: (x + z) < y2 + w -> (x + y + z) < w + u.
Admitted.

End Conj_add_SNo_Lt_subprop3c__3__6.
(** Conj_add_SNo_Lt_subprop3d__2__4 TMYDaeETVd7deMPazHtzGPu4THoRLSTRuMW bounty of about 25 bars **)
Section Conj_add_SNo_Lt_subprop3d__2__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H5: SNo v.
Hypothesis H6: (x + u) < v + w.
Theorem Conj_add_SNo_Lt_subprop3d__2__4: x + y + z + u = (y + z) + x + u -> (x + y + z + u) < (y + z + w) + v.
Admitted.

End Conj_add_SNo_Lt_subprop3d__2__4.
(** Conj_mul_SNo_eq__1__0 TMHNaUMQnp8mygqy5bkQwBG1Td5cZVPmmfL bounty of about 25 bars **)
Section Conj_mul_SNo_eq__1__0.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H1: z :e SNoS_ (SNoLev x).
Hypothesis H2: SNo w.
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__1__0: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__1__0.
(** Conj_mul_SNo_eq__1__1 TMaU7woDD25pzpeo87GUsLTfT2MR71x4vAP bounty of about 25 bars **)
Section Conj_mul_SNo_eq__1__1.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: SNo w.
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__1__1: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__1__1.
(** Conj_mul_SNo_eq__1__2 TML44XGPM1TnRxBFEotSt3DiX9pCv8byiYt bounty of about 25 bars **)
Section Conj_mul_SNo_eq__1__2.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H1: z :e SNoS_ (SNoLev x).
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__1__2: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__1__2.
(** Conj_mul_SNo_eq__2__3 TMYevhbTJiUkHxoZCg315NG4SJi3UUacxR5 bounty of about 25 bars **)
Section Conj_mul_SNo_eq__2__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H2: z :e SNoS_ (SNoLev x).
Hypothesis H4: SNo w.
Hypothesis H5: g z y = h z y.
Theorem Conj_mul_SNo_eq__2__3: g x w = h x w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__2__3.
(** Conj_mul_SNo_eq__3__3 TMc9x9bnxHCRdv9pdrLT23SFMWU723q3CF5 bounty of about 25 bars **)
Section Conj_mul_SNo_eq__3__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H4: w :e SNoS_ (SNoLev y).
Hypothesis H5: SNo w.
Theorem Conj_mul_SNo_eq__3__3: g z y = h z y -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__3__3.
(** Conj_mul_SNo_eq__3__4 TMbKdCNpgb8ceK8K44wes4z26jE2eV5bUXK bounty of about 25 bars **)
Section Conj_mul_SNo_eq__3__4.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H3: z :e SNoS_ (SNoLev x).
Hypothesis H5: SNo w.
Theorem Conj_mul_SNo_eq__3__4: g z y = h z y -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__3__4.
(** Conj_mul_SNo_eq__4__1 TMauMmtuJKRSxbZsSigSs3qQzCRTArRKSzx bounty of about 25 bars **)
Section Conj_mul_SNo_eq__4__1.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H3: w :e SNoL y.
Hypothesis H4: z :e SNoS_ (SNoLev x).
Hypothesis H5: w :e SNoS_ (SNoLev y).
Theorem Conj_mul_SNo_eq__4__1: SNo w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__4__1.
(** Conj_mul_SNo_eq__4__3 TMM9PLC4canhoRGg8wSstnVhUP3kwndnHts bounty of about 25 bars **)
Section Conj_mul_SNo_eq__4__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H4: z :e SNoS_ (SNoLev x).
Hypothesis H5: w :e SNoS_ (SNoLev y).
Theorem Conj_mul_SNo_eq__4__3: SNo w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__4__3.
(** Conj_mul_SNo_eq__5__1 TMbMyv2xSKFXdojrpPHAhGYYnxTvNRzKX1W bounty of about 25 bars **)
Section Conj_mul_SNo_eq__5__1.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H3: w :e SNoL y.
Hypothesis H4: z :e SNoS_ (SNoLev x).
Theorem Conj_mul_SNo_eq__5__1: w :e SNoS_ (SNoLev y) -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__5__1.
(** Conj_mul_SNo_eq__6__0 TMTv14qJ7Jd2ukEaCcgcTkSCrLZto6mzqXU bounty of about 25 bars **)
Section Conj_mul_SNo_eq__6__0.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H1: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H4: z :e SNoL x.
Hypothesis H5: w :e SNoL y.
Theorem Conj_mul_SNo_eq__6__0: z :e SNoS_ (SNoLev x) -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__6__0.
(** Conj_mul_SNo_eq__7__0 TMHNaUMQnp8mygqy5bkQwBG1Td5cZVPmmfL bounty of about 25 bars **)
Section Conj_mul_SNo_eq__7__0.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H1: z :e SNoS_ (SNoLev x).
Hypothesis H2: SNo w.
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__7__0: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__7__0.
(** Conj_mul_SNo_eq__7__1 TMaU7woDD25pzpeo87GUsLTfT2MR71x4vAP bounty of about 25 bars **)
Section Conj_mul_SNo_eq__7__1.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: SNo w.
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__7__1: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__7__1.
(** Conj_mul_SNo_eq__7__2 TML44XGPM1TnRxBFEotSt3DiX9pCv8byiYt bounty of about 25 bars **)
Section Conj_mul_SNo_eq__7__2.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H1: z :e SNoS_ (SNoLev x).
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__7__2: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__7__2.
(** Conj_mul_SNo_eq__8__3 TMYevhbTJiUkHxoZCg315NG4SJi3UUacxR5 bounty of about 25 bars **)
Section Conj_mul_SNo_eq__8__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H2: z :e SNoS_ (SNoLev x).
Hypothesis H4: SNo w.
Hypothesis H5: g z y = h z y.
Theorem Conj_mul_SNo_eq__8__3: g x w = h x w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__8__3.
(** Conj_mul_SNo_eq__9__3 TMc9x9bnxHCRdv9pdrLT23SFMWU723q3CF5 bounty of about 25 bars **)
Section Conj_mul_SNo_eq__9__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H4: w :e SNoS_ (SNoLev y).
Hypothesis H5: SNo w.
Theorem Conj_mul_SNo_eq__9__3: g z y = h z y -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__9__3.
(** Conj_mul_SNo_eq__9__4 TMbKdCNpgb8ceK8K44wes4z26jE2eV5bUXK bounty of about 25 bars **)
Section Conj_mul_SNo_eq__9__4.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H3: z :e SNoS_ (SNoLev x).
Hypothesis H5: SNo w.
Theorem Conj_mul_SNo_eq__9__4: g z y = h z y -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__9__4.
(** Conj_mul_SNo_eq__10__1 TMMYeriypZ4Zd8fgKdEqbdRRZqqUQHWn8Nv bounty of about 25 bars **)
Section Conj_mul_SNo_eq__10__1.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H3: w :e SNoR y.
Hypothesis H4: z :e SNoS_ (SNoLev x).
Hypothesis H5: w :e SNoS_ (SNoLev y).
Theorem Conj_mul_SNo_eq__10__1: SNo w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__10__1.
(** Conj_mul_SNo_eq__10__3 TMM9PLC4canhoRGg8wSstnVhUP3kwndnHts bounty of about 25 bars **)
Section Conj_mul_SNo_eq__10__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H4: z :e SNoS_ (SNoLev x).
Hypothesis H5: w :e SNoS_ (SNoLev y).
Theorem Conj_mul_SNo_eq__10__3: SNo w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__10__3.
(** Conj_mul_SNo_eq__12__4 TMM7v72BuE8LgBLome7o2XeS32ZynDx9b1u bounty of about 25 bars **)
Section Conj_mul_SNo_eq__12__4.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H5: w :e SNoR y.
Theorem Conj_mul_SNo_eq__12__4: z :e SNoS_ (SNoLev x) -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__12__4.
(** Conj_mul_SNo_eq__13__0 TMHNaUMQnp8mygqy5bkQwBG1Td5cZVPmmfL bounty of about 25 bars **)
Section Conj_mul_SNo_eq__13__0.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H1: z :e SNoS_ (SNoLev x).
Hypothesis H2: SNo w.
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__13__0: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__13__0.
(** Conj_mul_SNo_eq__13__1 TMaU7woDD25pzpeo87GUsLTfT2MR71x4vAP bounty of about 25 bars **)
Section Conj_mul_SNo_eq__13__1.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: SNo w.
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__13__1: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__13__1.
(** Conj_mul_SNo_eq__13__2 TML44XGPM1TnRxBFEotSt3DiX9pCv8byiYt bounty of about 25 bars **)
Section Conj_mul_SNo_eq__13__2.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H1: z :e SNoS_ (SNoLev x).
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__13__2: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__13__2.
(** Conj_mul_SNo_eq__14__3 TMYevhbTJiUkHxoZCg315NG4SJi3UUacxR5 bounty of about 25 bars **)
Section Conj_mul_SNo_eq__14__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H2: z :e SNoS_ (SNoLev x).
Hypothesis H4: SNo w.
Hypothesis H5: g z y = h z y.
Theorem Conj_mul_SNo_eq__14__3: g x w = h x w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__14__3.
(** Conj_mul_SNo_eq__15__3 TMc9x9bnxHCRdv9pdrLT23SFMWU723q3CF5 bounty of about 25 bars **)
Section Conj_mul_SNo_eq__15__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H4: w :e SNoS_ (SNoLev y).
Hypothesis H5: SNo w.
Theorem Conj_mul_SNo_eq__15__3: g z y = h z y -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__15__3.
(** Conj_mul_SNo_eq__15__4 TMbKdCNpgb8ceK8K44wes4z26jE2eV5bUXK bounty of about 25 bars **)
Section Conj_mul_SNo_eq__15__4.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H3: z :e SNoS_ (SNoLev x).
Hypothesis H5: SNo w.
Theorem Conj_mul_SNo_eq__15__4: g z y = h z y -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__15__4.
(** Conj_mul_SNo_eq__16__1 TMMYeriypZ4Zd8fgKdEqbdRRZqqUQHWn8Nv bounty of about 25 bars **)
Section Conj_mul_SNo_eq__16__1.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H3: w :e SNoR y.
Hypothesis H4: z :e SNoS_ (SNoLev x).
Hypothesis H5: w :e SNoS_ (SNoLev y).
Theorem Conj_mul_SNo_eq__16__1: SNo w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__16__1.
(** Conj_mul_SNo_eq__16__3 TMM9PLC4canhoRGg8wSstnVhUP3kwndnHts bounty of about 25 bars **)
Section Conj_mul_SNo_eq__16__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H4: z :e SNoS_ (SNoLev x).
Hypothesis H5: w :e SNoS_ (SNoLev y).
Theorem Conj_mul_SNo_eq__16__3: SNo w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__16__3.
(** Conj_mul_SNo_eq__18__4 TMM7v72BuE8LgBLome7o2XeS32ZynDx9b1u bounty of about 25 bars **)
Section Conj_mul_SNo_eq__18__4.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H5: w :e SNoR y.
Theorem Conj_mul_SNo_eq__18__4: z :e SNoS_ (SNoLev x) -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__18__4.
(** Conj_mul_SNo_eq__19__0 TMHNaUMQnp8mygqy5bkQwBG1Td5cZVPmmfL bounty of about 25 bars **)
Section Conj_mul_SNo_eq__19__0.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H1: z :e SNoS_ (SNoLev x).
Hypothesis H2: SNo w.
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__19__0: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__19__0.
(** Conj_mul_SNo_eq__19__1 TMaU7woDD25pzpeo87GUsLTfT2MR71x4vAP bounty of about 25 bars **)
Section Conj_mul_SNo_eq__19__1.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: SNo w.
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__19__1: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__19__1.
(** Conj_mul_SNo_eq__19__2 TML44XGPM1TnRxBFEotSt3DiX9pCv8byiYt bounty of about 25 bars **)
Section Conj_mul_SNo_eq__19__2.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H1: z :e SNoS_ (SNoLev x).
Hypothesis H3: g z y = h z y.
Hypothesis H4: g x w = h x w.
Theorem Conj_mul_SNo_eq__19__2: g z w = h z w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__19__2.
(** Conj_mul_SNo_eq__20__3 TMYevhbTJiUkHxoZCg315NG4SJi3UUacxR5 bounty of about 25 bars **)
Section Conj_mul_SNo_eq__20__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H2: z :e SNoS_ (SNoLev x).
Hypothesis H4: SNo w.
Hypothesis H5: g z y = h z y.
Theorem Conj_mul_SNo_eq__20__3: g x w = h x w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__20__3.
(** Conj_mul_SNo_eq__21__3 TMc9x9bnxHCRdv9pdrLT23SFMWU723q3CF5 bounty of about 25 bars **)
Section Conj_mul_SNo_eq__21__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H4: w :e SNoS_ (SNoLev y).
Hypothesis H5: SNo w.
Theorem Conj_mul_SNo_eq__21__3: g z y = h z y -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__21__3.
(** Conj_mul_SNo_eq__21__4 TMbKdCNpgb8ceK8K44wes4z26jE2eV5bUXK bounty of about 25 bars **)
Section Conj_mul_SNo_eq__21__4.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H3: z :e SNoS_ (SNoLev x).
Hypothesis H5: SNo w.
Theorem Conj_mul_SNo_eq__21__4: g z y = h z y -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__21__4.
(** Conj_mul_SNo_eq__22__1 TMauMmtuJKRSxbZsSigSs3qQzCRTArRKSzx bounty of about 25 bars **)
Section Conj_mul_SNo_eq__22__1.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H3: w :e SNoL y.
Hypothesis H4: z :e SNoS_ (SNoLev x).
Hypothesis H5: w :e SNoS_ (SNoLev y).
Theorem Conj_mul_SNo_eq__22__1: SNo w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__22__1.
(** Conj_mul_SNo_eq__22__3 TMM9PLC4canhoRGg8wSstnVhUP3kwndnHts bounty of about 25 bars **)
Section Conj_mul_SNo_eq__22__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H4: z :e SNoS_ (SNoLev x).
Hypothesis H5: w :e SNoS_ (SNoLev y).
Theorem Conj_mul_SNo_eq__22__3: SNo w -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__22__3.
(** Conj_mul_SNo_eq__23__1 TMbMyv2xSKFXdojrpPHAhGYYnxTvNRzKX1W bounty of about 25 bars **)
Section Conj_mul_SNo_eq__23__1.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev y) -> g x u = h x u).
Hypothesis H3: w :e SNoL y.
Hypothesis H4: z :e SNoS_ (SNoLev x).
Theorem Conj_mul_SNo_eq__23__1: w :e SNoS_ (SNoLev y) -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__23__1.
(** Conj_mul_SNo_eq__24__3 TMHm1Yw84cnyNYCAX3wytiGYt3WyS6TD8jc bounty of about 25 bars **)
Section Conj_mul_SNo_eq__24__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> g u v = h u v)).
Hypothesis H4: z :e SNoR x.
Hypothesis H5: w :e SNoL y.
Theorem Conj_mul_SNo_eq__24__3: z :e SNoS_ (SNoLev x) -> g z y + g x w + - (g z w) = h z y + h x w + - (h z w).
Admitted.

End Conj_mul_SNo_eq__24__3.
(** Conj_mul_SNo_eq__25__0 TMSVjHnyGhnvGyUsVy7a8bmeVh1RXJVvgjg bounty of about 25 bars **)
Section Conj_mul_SNo_eq__25__0.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Hypothesis H1: SNo y.
Hypothesis H2: (forall z:set, z :e SNoS_ (SNoLev x) -> (forall w:set, SNo w -> g z w = h z w)).
Hypothesis H3: (forall z:set, z :e SNoS_ (SNoLev y) -> g x z = h x z).
Hypothesis H4: Repl (setprod (SNoL x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoL x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Hypothesis H5: Repl (setprod (SNoR x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoR x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Hypothesis H6: Repl (setprod (SNoL x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoL x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Theorem Conj_mul_SNo_eq__25__0: Repl (setprod (SNoR x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoR x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))) -> SNoCut (binunion (Repl (setprod (SNoL x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))))) (binunion (Repl (setprod (SNoL x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))))) = SNoCut (binunion (Repl (setprod (SNoL x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))))) (binunion (Repl (setprod (SNoL x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))))).
Admitted.

End Conj_mul_SNo_eq__25__0.
(** Conj_mul_SNo_eq__25__3 TMPpyQvo4dmoKVv3eMdMETbbwQS3VoRXNPq bounty of about 25 bars **)
Section Conj_mul_SNo_eq__25__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall z:set, z :e SNoS_ (SNoLev x) -> (forall w:set, SNo w -> g z w = h z w)).
Hypothesis H4: Repl (setprod (SNoL x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoL x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Hypothesis H5: Repl (setprod (SNoR x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoR x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Hypothesis H6: Repl (setprod (SNoL x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoL x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Theorem Conj_mul_SNo_eq__25__3: Repl (setprod (SNoR x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoR x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))) -> SNoCut (binunion (Repl (setprod (SNoL x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))))) (binunion (Repl (setprod (SNoL x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))))) = SNoCut (binunion (Repl (setprod (SNoL x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))))) (binunion (Repl (setprod (SNoL x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))))).
Admitted.

End Conj_mul_SNo_eq__25__3.
(** Conj_mul_SNo_eq__25__4 TMLFUH5mm6w6g7asL61fiVzmsX3gaVcvcd7 bounty of about 25 bars **)
Section Conj_mul_SNo_eq__25__4.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall z:set, z :e SNoS_ (SNoLev x) -> (forall w:set, SNo w -> g z w = h z w)).
Hypothesis H3: (forall z:set, z :e SNoS_ (SNoLev y) -> g x z = h x z).
Hypothesis H5: Repl (setprod (SNoR x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoR x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Hypothesis H6: Repl (setprod (SNoL x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoL x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Theorem Conj_mul_SNo_eq__25__4: Repl (setprod (SNoR x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoR x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))) -> SNoCut (binunion (Repl (setprod (SNoL x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))))) (binunion (Repl (setprod (SNoL x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))))) = SNoCut (binunion (Repl (setprod (SNoL x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))))) (binunion (Repl (setprod (SNoL x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))))).
Admitted.

End Conj_mul_SNo_eq__25__4.
(** Conj_mul_SNo_eq__26__3 TMFHNBzkKbpRnRahKMHtwK7yTzoHXFXsA5a bounty of about 25 bars **)
Section Conj_mul_SNo_eq__26__3.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall z:set, z :e SNoS_ (SNoLev x) -> (forall w:set, SNo w -> g z w = h z w)).
Hypothesis H4: Repl (setprod (SNoL x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoL x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Hypothesis H5: Repl (setprod (SNoR x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoR x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Theorem Conj_mul_SNo_eq__26__3: Repl (setprod (SNoL x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoL x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))) -> SNoCut (binunion (Repl (setprod (SNoL x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))))) (binunion (Repl (setprod (SNoL x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))))) = SNoCut (binunion (Repl (setprod (SNoL x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))))) (binunion (Repl (setprod (SNoL x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))))).
Admitted.

End Conj_mul_SNo_eq__26__3.
(** Conj_mul_SNo_eq__27__2 TMd6GTSPub86kSBSYDMKkhw1WjnDKssSgBt bounty of about 25 bars **)
Section Conj_mul_SNo_eq__27__2.
Variable x:set.
Variable y:set.
Variable g:(set -> (set -> set)).
Variable h:(set -> (set -> set)).
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall z:set, z :e SNoS_ (SNoLev y) -> g x z = h x z).
Hypothesis H4: Repl (setprod (SNoL x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoL x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))).
Theorem Conj_mul_SNo_eq__27__2: Repl (setprod (SNoR x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))) = Repl (setprod (SNoR x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))) -> SNoCut (binunion (Repl (setprod (SNoL x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))))) (binunion (Repl (setprod (SNoL x) (SNoR y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoL y)) (fun z:set => g (ap z Empty) y + g x (ap z (ordsucc Empty)) + - (g (ap z Empty) (ap z (ordsucc Empty)))))) = SNoCut (binunion (Repl (setprod (SNoL x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))))) (binunion (Repl (setprod (SNoL x) (SNoR y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty))))) (Repl (setprod (SNoR x) (SNoL y)) (fun z:set => h (ap z Empty) y + h x (ap z (ordsucc Empty)) + - (h (ap z Empty) (ap z (ordsucc Empty)))))).
Admitted.

End Conj_mul_SNo_eq__27__2.
(** Conj_mul_SNo_prop_1__2__0 TMVrz6btCAk4frmaKByxBXAZeVa5DqQjEUR bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__2__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: SNo (w * v).
Hypothesis H2: SNo (z * y).
Hypothesis H3: SNo (x * u).
Hypothesis H4: SNo (w * y).
Hypothesis H5: SNo (x * v).
Hypothesis H6: (z * y + x * u + w * v) < w * y + x * v + z * u.
Theorem Conj_mul_SNo_prop_1__2__0: (z * y + x * u + - (z * u)) + z * u + w * v = z * y + x * u + w * v -> ((z * y + x * u + - (z * u)) + z * u + w * v) < (w * y + x * v + - (w * v)) + z * u + w * v.
Admitted.

End Conj_mul_SNo_prop_1__2__0.
(** Conj_mul_SNo_prop_1__3__6 TML5g8m58GqjEw5fqVcfNiMr5zfT16iJzMX bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__3__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall P:prop, (SNo (z2 * w2) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoL w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoR w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoR w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoL w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> P) -> P))).
Hypothesis H1: v :e SNoS_ (SNoLev x).
Hypothesis H2: SNo x2.
Hypothesis H3: SNo (u * x2).
Hypothesis H4: SNo (v * y2).
Hypothesis H5: SNo (u * y).
Hypothesis H7: SNo (v * y).
Hypothesis H8: SNo (x * y2).
Hypothesis H9: SNo (u * y2).
Theorem Conj_mul_SNo_prop_1__3__6: SNo (v * x2) -> (forall P:prop, (SNo (u * y) -> SNo (x * x2) -> SNo (u * x2) -> SNo (v * y) -> SNo (x * y2) -> SNo (v * y2) -> SNo (u * y2) -> SNo (v * x2) -> (z = u * y + x * x2 + - (u * x2) -> w = v * y + x * y2 + - (v * y2) -> (u * y + x * x2 + v * y2) < v * y + x * y2 + u * x2 -> z < w) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__3__6.
(** Conj_mul_SNo_prop_1__6__1 TMJj8RpLFJETYBj2N7Dqxo1PE8ZeuSKwzwu bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__6__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall P:prop, (SNo (z2 * w2) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoL w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoR w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoR w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoL w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> P) -> P))).
Hypothesis H2: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * z2) -> (forall w2:set, w2 :e SNoL x -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + x * u2) < x * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR x -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + x * u2) < x * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL x -> (forall u2:set, u2 :e SNoR z2 -> (x * z2 + w2 * u2) < w2 * z2 + x * u2)) -> (forall w2:set, w2 :e SNoR x -> (forall u2:set, u2 :e SNoL z2 -> (x * z2 + w2 * u2) < w2 * z2 + x * u2)) -> P) -> P)).
Hypothesis H3: u :e SNoS_ (SNoLev x).
Hypothesis H4: v :e SNoS_ (SNoLev x).
Hypothesis H5: y2 :e SNoS_ (SNoLev y).
Hypothesis H6: SNo x2.
Hypothesis H7: SNo y2.
Hypothesis H8: SNo (u * x2).
Hypothesis H9: SNo (v * y2).
Hypothesis H10: SNo (u * y).
Hypothesis H11: SNo (x * x2).
Theorem Conj_mul_SNo_prop_1__6__1: SNo (v * y) -> (forall P:prop, (SNo (u * y) -> SNo (x * x2) -> SNo (u * x2) -> SNo (v * y) -> SNo (x * y2) -> SNo (v * y2) -> SNo (u * y2) -> SNo (v * x2) -> (z = u * y + x * x2 + - (u * x2) -> w = v * y + x * y2 + - (v * y2) -> (u * y + x * x2 + v * y2) < v * y + x * y2 + u * x2 -> z < w) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__6__1.
(** Conj_mul_SNo_prop_1__7__11 TMGvacqUPn3QdeinwN9k3WHnmtydV9cg8s3 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__7__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall P:prop, (SNo (z2 * w2) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoL w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoR w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoR w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoL w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> P) -> P))).
Hypothesis H1: SNo y.
Hypothesis H2: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * z2) -> (forall w2:set, w2 :e SNoL x -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + x * u2) < x * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR x -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + x * u2) < x * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL x -> (forall u2:set, u2 :e SNoR z2 -> (x * z2 + w2 * u2) < w2 * z2 + x * u2)) -> (forall w2:set, w2 :e SNoR x -> (forall u2:set, u2 :e SNoL z2 -> (x * z2 + w2 * u2) < w2 * z2 + x * u2)) -> P) -> P)).
Hypothesis H3: u :e SNoS_ (SNoLev x).
Hypothesis H4: v :e SNoS_ (SNoLev x).
Hypothesis H5: x2 :e SNoS_ (SNoLev y).
Hypothesis H6: y2 :e SNoS_ (SNoLev y).
Hypothesis H7: SNo x2.
Hypothesis H8: SNo y2.
Hypothesis H9: SNo (u * x2).
Hypothesis H10: SNo (v * y2).
Theorem Conj_mul_SNo_prop_1__7__11: SNo (x * x2) -> (forall P:prop, (SNo (u * y) -> SNo (x * x2) -> SNo (u * x2) -> SNo (v * y) -> SNo (x * y2) -> SNo (v * y2) -> SNo (u * y2) -> SNo (v * x2) -> (z = u * y + x * x2 + - (u * x2) -> w = v * y + x * y2 + - (v * y2) -> (u * y + x * x2 + v * y2) < v * y + x * y2 + u * x2 -> z < w) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__7__11.
(** Conj_mul_SNo_prop_1__8__5 TMKjpLMGuhE4aLTe9gb214P12yjLkWWY2KR bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__8__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall P:prop, (SNo (z2 * w2) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoL w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoR w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoR w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoL w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> P) -> P))).
Hypothesis H1: SNo y.
Hypothesis H2: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * z2) -> (forall w2:set, w2 :e SNoL x -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + x * u2) < x * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR x -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + x * u2) < x * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL x -> (forall u2:set, u2 :e SNoR z2 -> (x * z2 + w2 * u2) < w2 * z2 + x * u2)) -> (forall w2:set, w2 :e SNoR x -> (forall u2:set, u2 :e SNoL z2 -> (x * z2 + w2 * u2) < w2 * z2 + x * u2)) -> P) -> P)).
Hypothesis H3: u :e SNoS_ (SNoLev x).
Hypothesis H4: v :e SNoS_ (SNoLev x).
Hypothesis H6: y2 :e SNoS_ (SNoLev y).
Hypothesis H7: SNo x2.
Hypothesis H8: SNo y2.
Hypothesis H9: SNo (u * x2).
Hypothesis H10: SNo (v * y2).
Theorem Conj_mul_SNo_prop_1__8__5: SNo (u * y) -> (forall P:prop, (SNo (u * y) -> SNo (x * x2) -> SNo (u * x2) -> SNo (v * y) -> SNo (x * y2) -> SNo (v * y2) -> SNo (u * y2) -> SNo (v * x2) -> (z = u * y + x * x2 + - (u * x2) -> w = v * y + x * y2 + - (v * y2) -> (u * y + x * x2 + v * y2) < v * y + x * y2 + u * x2 -> z < w) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__8__5.
(** Conj_mul_SNo_prop_1__9__1 TMMxdg4CN8UzgoS1utojiQaJDUfRsckhB3c bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__9__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall P:prop, (SNo (z2 * w2) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoL w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoR w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoR w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoL w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> P) -> P))).
Hypothesis H2: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * z2) -> (forall w2:set, w2 :e SNoL x -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + x * u2) < x * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR x -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + x * u2) < x * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL x -> (forall u2:set, u2 :e SNoR z2 -> (x * z2 + w2 * u2) < w2 * z2 + x * u2)) -> (forall w2:set, w2 :e SNoR x -> (forall u2:set, u2 :e SNoL z2 -> (x * z2 + w2 * u2) < w2 * z2 + x * u2)) -> P) -> P)).
Hypothesis H3: u :e SNoS_ (SNoLev x).
Hypothesis H4: v :e SNoS_ (SNoLev x).
Hypothesis H5: x2 :e SNoS_ (SNoLev y).
Hypothesis H6: y2 :e SNoS_ (SNoLev y).
Hypothesis H7: SNo x2.
Hypothesis H8: SNo y2.
Hypothesis H9: SNo (u * x2).
Theorem Conj_mul_SNo_prop_1__9__1: SNo (v * y2) -> (forall P:prop, (SNo (u * y) -> SNo (x * x2) -> SNo (u * x2) -> SNo (v * y) -> SNo (x * y2) -> SNo (v * y2) -> SNo (u * y2) -> SNo (v * x2) -> (z = u * y + x * x2 + - (u * x2) -> w = v * y + x * y2 + - (v * y2) -> (u * y + x * x2 + v * y2) < v * y + x * y2 + u * x2 -> z < w) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__9__1.
(** Conj_mul_SNo_prop_1__9__6 TMaZ2Pm7ChBMXhMnqAte7CAQq6t4DWRwuFT bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__9__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall P:prop, (SNo (z2 * w2) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoL w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoR w2 -> (u2 * w2 + z2 * v2) < z2 * w2 + u2 * v2)) -> (forall u2:set, u2 :e SNoL z2 -> (forall v2:set, v2 :e SNoR w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> (forall u2:set, u2 :e SNoR z2 -> (forall v2:set, v2 :e SNoL w2 -> (z2 * w2 + u2 * v2) < u2 * w2 + z2 * v2)) -> P) -> P))).
Hypothesis H1: SNo y.
Hypothesis H2: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * z2) -> (forall w2:set, w2 :e SNoL x -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + x * u2) < x * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR x -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + x * u2) < x * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL x -> (forall u2:set, u2 :e SNoR z2 -> (x * z2 + w2 * u2) < w2 * z2 + x * u2)) -> (forall w2:set, w2 :e SNoR x -> (forall u2:set, u2 :e SNoL z2 -> (x * z2 + w2 * u2) < w2 * z2 + x * u2)) -> P) -> P)).
Hypothesis H3: u :e SNoS_ (SNoLev x).
Hypothesis H4: v :e SNoS_ (SNoLev x).
Hypothesis H5: x2 :e SNoS_ (SNoLev y).
Hypothesis H7: SNo x2.
Hypothesis H8: SNo y2.
Hypothesis H9: SNo (u * x2).
Theorem Conj_mul_SNo_prop_1__9__6: SNo (v * y2) -> (forall P:prop, (SNo (u * y) -> SNo (x * x2) -> SNo (u * x2) -> SNo (v * y) -> SNo (x * y2) -> SNo (v * y2) -> SNo (u * y2) -> SNo (v * x2) -> (z = u * y + x * x2 + - (u * x2) -> w = v * y + x * y2 + - (v * y2) -> (u * y + x * x2 + v * y2) < v * y + x * y2 + u * x2 -> z < w) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__9__6.
(** Conj_mul_SNo_prop_1__13__4 TMK7gT5Nt7Q8RXz7BYodQXSz1P9USKnFQ5b bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__13__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: z :e SNoR y.
Hypothesis H3: w :e SNoL y.
Hypothesis H5: SNo (x * w).
Hypothesis H6: u :e SNoR x.
Hypothesis H7: SNo (u * z).
Hypothesis H8: SNo (u * w).
Hypothesis H9: v :e SNoL z.
Hypothesis H10: v :e SNoR w.
Hypothesis H11: v :e SNoS_ (SNoLev y).
Hypothesis H12: SNo (u * v).
Theorem Conj_mul_SNo_prop_1__13__4: SNo (x * v) -> (x * z + u * w) < u * z + x * w.
Admitted.

End Conj_mul_SNo_prop_1__13__4.
(** Conj_mul_SNo_prop_1__13__5 TMVyzndZqEtDSJBiHqqK1rsEtpANkCTDKpk bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__13__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: z :e SNoR y.
Hypothesis H3: w :e SNoL y.
Hypothesis H4: SNo (x * z).
Hypothesis H6: u :e SNoR x.
Hypothesis H7: SNo (u * z).
Hypothesis H8: SNo (u * w).
Hypothesis H9: v :e SNoL z.
Hypothesis H10: v :e SNoR w.
Hypothesis H11: v :e SNoS_ (SNoLev y).
Hypothesis H12: SNo (u * v).
Theorem Conj_mul_SNo_prop_1__13__5: SNo (x * v) -> (x * z + u * w) < u * z + x * w.
Admitted.

End Conj_mul_SNo_prop_1__13__5.
(** Conj_mul_SNo_prop_1__17__11 TMJdiXoTF8q2Ctv3kA6kpGsvR3XVKnSJRro bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__17__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * v) -> (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL v -> (x2 * v + x * y2) < x * v + x2 * y2)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR v -> (x2 * v + x * y2) < x * v + x2 * y2)) -> (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR v -> (x * v + x2 * y2) < x2 * v + x * y2)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL v -> (x * v + x2 * y2) < x2 * v + x * y2)) -> P) -> P)).
Hypothesis H2: (forall v:set, v :e SNoR x -> (forall x2:set, SNo x2 -> SNo (v * x2))).
Hypothesis H3: z :e SNoR y.
Hypothesis H4: SNo z.
Hypothesis H5: SNoLev z :e SNoLev y.
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (x * w).
Hypothesis H10: w < z.
Theorem Conj_mul_SNo_prop_1__17__11: SNo (u * z) -> (x * z + u * w) < u * z + x * w.
Admitted.

End Conj_mul_SNo_prop_1__17__11.
(** Conj_mul_SNo_prop_1__18__5 TMUBBZ4iytUoskdnE2gNzcT97cfufmZkbUb bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__18__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, SNo z2 -> (forall P:prop, (SNo (y2 * z2) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoR z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoL z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H4: (forall y2:set, y2 :e SNoR x -> SNo (y2 * y)).
Hypothesis H6: v :e SNoL y.
Hypothesis H7: SNo v.
Hypothesis H8: SNo (z * y).
Hypothesis H9: SNo (x * w).
Hypothesis H10: SNo (z * w).
Hypothesis H11: SNo (u * y).
Hypothesis H12: SNo (x * v).
Hypothesis H13: SNo (u * v).
Hypothesis H14: SNo (z * v).
Hypothesis H15: (x * w + z * v) < z * w + x * v.
Hypothesis H16: x2 :e SNoL u.
Hypothesis H17: x2 :e SNoR x.
Hypothesis H18: (z * y + x2 * v) < x2 * y + z * v.
Theorem Conj_mul_SNo_prop_1__18__5: (x2 * y + u * v) < u * y + x2 * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__18__5.
(** Conj_mul_SNo_prop_1__19__5 TMMpG3fBq2rPV6if2kMt7fJaog1qMqGXcNL bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__19__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, SNo z2 -> (forall P:prop, (SNo (y2 * z2) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoR z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoL z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H4: (forall y2:set, y2 :e SNoR x -> SNo (y2 * y)).
Hypothesis H6: u :e SNoR x.
Hypothesis H7: v :e SNoL y.
Hypothesis H8: SNo v.
Hypothesis H9: SNo (z * y).
Hypothesis H10: SNo (x * w).
Hypothesis H11: SNo (z * w).
Hypothesis H12: SNo (u * y).
Hypothesis H13: SNo (x * v).
Hypothesis H14: SNo (u * v).
Hypothesis H15: SNo (z * v).
Hypothesis H16: (x * w + z * v) < z * w + x * v.
Hypothesis H17: x2 :e SNoR z.
Hypothesis H18: x2 :e SNoL u.
Hypothesis H19: x2 :e SNoR x.
Theorem Conj_mul_SNo_prop_1__19__5: (z * y + x2 * v) < x2 * y + z * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__19__5.
(** Conj_mul_SNo_prop_1__20__0 TMVPHdyk9jpfya3CYgH2QKb6qjfxdnbfWyd bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__20__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, SNo z2 -> (forall P:prop, (SNo (y2 * z2) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoR z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoL z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H4: (forall y2:set, y2 :e SNoR x -> SNo (y2 * y)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: SNo z.
Hypothesis H7: SNoLev z :e SNoLev x.
Hypothesis H8: x < z.
Hypothesis H9: u :e SNoR x.
Hypothesis H10: v :e SNoL y.
Hypothesis H11: SNo v.
Hypothesis H12: SNo (z * y).
Hypothesis H13: SNo (x * w).
Hypothesis H14: SNo (z * w).
Hypothesis H15: SNo (u * y).
Hypothesis H16: SNo (x * v).
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (z * v).
Hypothesis H19: (x * w + z * v) < z * w + x * v.
Hypothesis H20: x2 :e SNoR z.
Hypothesis H21: x2 :e SNoL u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNoLev x2 :e SNoLev z.
Hypothesis H24: z < x2.
Theorem Conj_mul_SNo_prop_1__20__0: x2 :e SNoR x -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__20__0.
(** Conj_mul_SNo_prop_1__20__19 TMYTkKd8JDKsJd4wkca1HaRz1JFEZAZt25q bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__20__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, SNo z2 -> (forall P:prop, (SNo (y2 * z2) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoR z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoL z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H4: (forall y2:set, y2 :e SNoR x -> SNo (y2 * y)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: SNo z.
Hypothesis H7: SNoLev z :e SNoLev x.
Hypothesis H8: x < z.
Hypothesis H9: u :e SNoR x.
Hypothesis H10: v :e SNoL y.
Hypothesis H11: SNo v.
Hypothesis H12: SNo (z * y).
Hypothesis H13: SNo (x * w).
Hypothesis H14: SNo (z * w).
Hypothesis H15: SNo (u * y).
Hypothesis H16: SNo (x * v).
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (z * v).
Hypothesis H20: x2 :e SNoR z.
Hypothesis H21: x2 :e SNoL u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNoLev x2 :e SNoLev z.
Hypothesis H24: z < x2.
Theorem Conj_mul_SNo_prop_1__20__19: x2 :e SNoR x -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__20__19.
(** Conj_mul_SNo_prop_1__20__24 TMUZozXVomEwAATkkEWDczRzpaVctYnSmZw bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__20__24.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, SNo z2 -> (forall P:prop, (SNo (y2 * z2) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoR z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoL z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H4: (forall y2:set, y2 :e SNoR x -> SNo (y2 * y)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: SNo z.
Hypothesis H7: SNoLev z :e SNoLev x.
Hypothesis H8: x < z.
Hypothesis H9: u :e SNoR x.
Hypothesis H10: v :e SNoL y.
Hypothesis H11: SNo v.
Hypothesis H12: SNo (z * y).
Hypothesis H13: SNo (x * w).
Hypothesis H14: SNo (z * w).
Hypothesis H15: SNo (u * y).
Hypothesis H16: SNo (x * v).
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (z * v).
Hypothesis H19: (x * w + z * v) < z * w + x * v.
Hypothesis H20: x2 :e SNoR z.
Hypothesis H21: x2 :e SNoL u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNoLev x2 :e SNoLev z.
Theorem Conj_mul_SNo_prop_1__20__24: x2 :e SNoR x -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__20__24.
(** Conj_mul_SNo_prop_1__23__4 TMKMjywM9qUXFY45cw55JwB9wmETHUXjGKs bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__23__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, SNo z2 -> (forall P:prop, (SNo (y2 * z2) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoR z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoL z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: w :e SNoR y.
Hypothesis H7: SNo w.
Hypothesis H8: u :e SNoR x.
Hypothesis H9: SNo u.
Hypothesis H10: SNoLev u :e SNoLev x.
Hypothesis H11: x < u.
Hypothesis H12: SNo (z * y).
Hypothesis H13: SNo (x * w).
Hypothesis H14: SNo (z * w).
Hypothesis H15: SNo (u * y).
Hypothesis H16: SNo (x * v).
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u * w).
Hypothesis H19: (x * w + u * v) < u * w + x * v.
Hypothesis H20: x2 :e SNoL z.
Hypothesis H21: x2 :e SNoR u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNoLev x2 :e SNoLev u.
Hypothesis H24: u < x2.
Theorem Conj_mul_SNo_prop_1__23__4: x2 :e SNoR x -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__23__4.
(** Conj_mul_SNo_prop_1__25__24 TMRifuMyoJrgRcxL3ceZ4FMNeySvSHFKE9h bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__25__24.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoR x -> SNo (x2 * y)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: w :e SNoR y.
Hypothesis H7: SNo z.
Hypothesis H8: SNoLev z :e SNoLev x.
Hypothesis H9: x < z.
Hypothesis H10: SNo w.
Hypothesis H11: u :e SNoR x.
Hypothesis H12: v :e SNoL y.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev x.
Hypothesis H15: x < u.
Hypothesis H16: SNo v.
Hypothesis H17: SNo (z * y).
Hypothesis H18: SNo (x * w).
Hypothesis H19: SNo (z * w).
Hypothesis H20: SNo (u * y).
Hypothesis H21: SNo (x * v).
Hypothesis H22: SNo (u * v).
Hypothesis H23: SNo (z * v).
Hypothesis H25: (x * w + z * v) < z * w + x * v.
Hypothesis H26: (x * w + u * v) < u * w + x * v.
Theorem Conj_mul_SNo_prop_1__25__24: ((z * y + u * v) < u * y + z * v -> (z * y + x * w + u * v) < u * y + x * v + z * w) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__25__24.
(** Conj_mul_SNo_prop_1__26__15 TMGiBqnCadKN41Du1yReNN3piRmxHw1py8d bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__26__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoR x -> SNo (x2 * y)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: w :e SNoR y.
Hypothesis H7: SNo z.
Hypothesis H8: SNoLev z :e SNoLev x.
Hypothesis H9: x < z.
Hypothesis H10: SNo w.
Hypothesis H11: u :e SNoR x.
Hypothesis H12: v :e SNoL y.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev x.
Hypothesis H16: SNo v.
Hypothesis H17: SNo (z * y).
Hypothesis H18: SNo (x * w).
Hypothesis H19: SNo (z * w).
Hypothesis H20: SNo (u * y).
Hypothesis H21: SNo (x * v).
Hypothesis H22: SNo (u * v).
Hypothesis H23: SNo (z * v).
Hypothesis H24: SNo (u * w).
Hypothesis H25: (forall x2:set, x2 :e SNoR x -> (x * w + x2 * v) < x2 * w + x * v).
Hypothesis H26: (x * w + z * v) < z * w + x * v.
Theorem Conj_mul_SNo_prop_1__26__15: (x * w + u * v) < u * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__26__15.
(** Conj_mul_SNo_prop_1__27__8 TMTswzTWRarKb5uYw6NmLnyxAMnCPgiHcqY bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__27__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoR x -> SNo (x2 * y)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: w :e SNoR y.
Hypothesis H7: SNo z.
Hypothesis H9: x < z.
Hypothesis H10: SNo w.
Hypothesis H11: u :e SNoR x.
Hypothesis H12: v :e SNoL y.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev x.
Hypothesis H15: x < u.
Hypothesis H16: SNo v.
Hypothesis H17: SNo (z * y).
Hypothesis H18: SNo (x * w).
Hypothesis H19: SNo (z * w).
Hypothesis H20: SNo (u * y).
Hypothesis H21: SNo (x * v).
Hypothesis H22: SNo (u * v).
Hypothesis H23: SNo (z * v).
Hypothesis H24: SNo (u * w).
Hypothesis H25: (forall x2:set, x2 :e SNoR x -> (x * w + x2 * v) < x2 * w + x * v).
Theorem Conj_mul_SNo_prop_1__27__8: (x * w + z * v) < z * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__27__8.
(** Conj_mul_SNo_prop_1__28__0 TMKbE1bdjRbvCFLPcGZFzuMmTYQ9gTAv7tS bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__28__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> SNo (x2 * y)).
Hypothesis H6: z :e SNoR x.
Hypothesis H7: w :e SNoR y.
Hypothesis H8: SNo z.
Hypothesis H9: SNoLev z :e SNoLev x.
Hypothesis H10: x < z.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H13: u :e SNoR x.
Hypothesis H14: v :e SNoL y.
Hypothesis H15: SNo u.
Hypothesis H16: SNoLev u :e SNoLev x.
Hypothesis H17: x < u.
Hypothesis H18: SNo v.
Hypothesis H19: SNo (z * y).
Hypothesis H20: SNo (x * w).
Hypothesis H21: SNo (z * w).
Hypothesis H22: SNo (u * y).
Hypothesis H23: SNo (x * v).
Hypothesis H24: SNo (u * v).
Hypothesis H25: SNo (z * v).
Hypothesis H26: SNo (u * w).
Hypothesis H27: v < w.
Theorem Conj_mul_SNo_prop_1__28__0: (forall x2:set, x2 :e SNoR x -> (x * w + x2 * v) < x2 * w + x * v) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__28__0.
(** Conj_mul_SNo_prop_1__28__13 TMR831BWAdvaEpS2616V4Gd9pzgtvoABtNH bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__28__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> SNo (x2 * y)).
Hypothesis H6: z :e SNoR x.
Hypothesis H7: w :e SNoR y.
Hypothesis H8: SNo z.
Hypothesis H9: SNoLev z :e SNoLev x.
Hypothesis H10: x < z.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H14: v :e SNoL y.
Hypothesis H15: SNo u.
Hypothesis H16: SNoLev u :e SNoLev x.
Hypothesis H17: x < u.
Hypothesis H18: SNo v.
Hypothesis H19: SNo (z * y).
Hypothesis H20: SNo (x * w).
Hypothesis H21: SNo (z * w).
Hypothesis H22: SNo (u * y).
Hypothesis H23: SNo (x * v).
Hypothesis H24: SNo (u * v).
Hypothesis H25: SNo (z * v).
Hypothesis H26: SNo (u * w).
Hypothesis H27: v < w.
Theorem Conj_mul_SNo_prop_1__28__13: (forall x2:set, x2 :e SNoR x -> (x * w + x2 * v) < x2 * w + x * v) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__28__13.
(** Conj_mul_SNo_prop_1__28__18 TMXnpbhJNJkTf1338bGH7xwHL48xrz8RNrK bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__28__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> SNo (x2 * y)).
Hypothesis H6: z :e SNoR x.
Hypothesis H7: w :e SNoR y.
Hypothesis H8: SNo z.
Hypothesis H9: SNoLev z :e SNoLev x.
Hypothesis H10: x < z.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H13: u :e SNoR x.
Hypothesis H14: v :e SNoL y.
Hypothesis H15: SNo u.
Hypothesis H16: SNoLev u :e SNoLev x.
Hypothesis H17: x < u.
Hypothesis H19: SNo (z * y).
Hypothesis H20: SNo (x * w).
Hypothesis H21: SNo (z * w).
Hypothesis H22: SNo (u * y).
Hypothesis H23: SNo (x * v).
Hypothesis H24: SNo (u * v).
Hypothesis H25: SNo (z * v).
Hypothesis H26: SNo (u * w).
Hypothesis H27: v < w.
Theorem Conj_mul_SNo_prop_1__28__18: (forall x2:set, x2 :e SNoR x -> (x * w + x2 * v) < x2 * w + x * v) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__28__18.
(** Conj_mul_SNo_prop_1__29__15 TMP7jVhEQZ4nc3TLqJTrjcumTZvEYEZmrHR bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__29__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> SNo (x2 * y)).
Hypothesis H6: z :e SNoR x.
Hypothesis H7: w :e SNoR y.
Hypothesis H8: SNo z.
Hypothesis H9: SNoLev z :e SNoLev x.
Hypothesis H10: x < z.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H13: y < w.
Hypothesis H14: u :e SNoR x.
Hypothesis H16: SNo u.
Hypothesis H17: SNoLev u :e SNoLev x.
Hypothesis H18: x < u.
Hypothesis H19: SNo v.
Hypothesis H20: v < y.
Hypothesis H21: SNo (z * y).
Hypothesis H22: SNo (x * w).
Hypothesis H23: SNo (z * w).
Hypothesis H24: SNo (u * y).
Hypothesis H25: SNo (x * v).
Hypothesis H26: SNo (u * v).
Hypothesis H27: SNo (z * v).
Hypothesis H28: SNo (u * w).
Theorem Conj_mul_SNo_prop_1__29__15: v < w -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__29__15.
(** Conj_mul_SNo_prop_1__29__22 TMT7sZTYvkgjFvy8zYquTee2QQeeCXt12aQ bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__29__22.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> SNo (x2 * y)).
Hypothesis H6: z :e SNoR x.
Hypothesis H7: w :e SNoR y.
Hypothesis H8: SNo z.
Hypothesis H9: SNoLev z :e SNoLev x.
Hypothesis H10: x < z.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H13: y < w.
Hypothesis H14: u :e SNoR x.
Hypothesis H15: v :e SNoL y.
Hypothesis H16: SNo u.
Hypothesis H17: SNoLev u :e SNoLev x.
Hypothesis H18: x < u.
Hypothesis H19: SNo v.
Hypothesis H20: v < y.
Hypothesis H21: SNo (z * y).
Hypothesis H23: SNo (z * w).
Hypothesis H24: SNo (u * y).
Hypothesis H25: SNo (x * v).
Hypothesis H26: SNo (u * v).
Hypothesis H27: SNo (z * v).
Hypothesis H28: SNo (u * w).
Theorem Conj_mul_SNo_prop_1__29__22: v < w -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__29__22.
(** Conj_mul_SNo_prop_1__29__23 TMLW5dUF6k5Jxm2JD1o9k6jLDsdAJEuJhYz bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__29__23.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> SNo (x2 * y)).
Hypothesis H6: z :e SNoR x.
Hypothesis H7: w :e SNoR y.
Hypothesis H8: SNo z.
Hypothesis H9: SNoLev z :e SNoLev x.
Hypothesis H10: x < z.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H13: y < w.
Hypothesis H14: u :e SNoR x.
Hypothesis H15: v :e SNoL y.
Hypothesis H16: SNo u.
Hypothesis H17: SNoLev u :e SNoLev x.
Hypothesis H18: x < u.
Hypothesis H19: SNo v.
Hypothesis H20: v < y.
Hypothesis H21: SNo (z * y).
Hypothesis H22: SNo (x * w).
Hypothesis H24: SNo (u * y).
Hypothesis H25: SNo (x * v).
Hypothesis H26: SNo (u * v).
Hypothesis H27: SNo (z * v).
Hypothesis H28: SNo (u * w).
Theorem Conj_mul_SNo_prop_1__29__23: v < w -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__29__23.
(** Conj_mul_SNo_prop_1__29__26 TMFwRocbYCoAMZt9dxHUntt2MNBM95icjAr bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__29__26.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> SNo (x2 * y)).
Hypothesis H6: z :e SNoR x.
Hypothesis H7: w :e SNoR y.
Hypothesis H8: SNo z.
Hypothesis H9: SNoLev z :e SNoLev x.
Hypothesis H10: x < z.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H13: y < w.
Hypothesis H14: u :e SNoR x.
Hypothesis H15: v :e SNoL y.
Hypothesis H16: SNo u.
Hypothesis H17: SNoLev u :e SNoLev x.
Hypothesis H18: x < u.
Hypothesis H19: SNo v.
Hypothesis H20: v < y.
Hypothesis H21: SNo (z * y).
Hypothesis H22: SNo (x * w).
Hypothesis H23: SNo (z * w).
Hypothesis H24: SNo (u * y).
Hypothesis H25: SNo (x * v).
Hypothesis H27: SNo (z * v).
Hypothesis H28: SNo (u * w).
Theorem Conj_mul_SNo_prop_1__29__26: v < w -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__29__26.
(** Conj_mul_SNo_prop_1__30__3 TMJWwbsYzbBenTSXEqvuscAGr23EDPZAebU bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__30__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H4: SNo (z * y).
Hypothesis H5: SNo (w * y).
Hypothesis H6: u :e SNoR y.
Hypothesis H7: SNo (z * u).
Hypothesis H8: SNo (w * u).
Hypothesis H9: v :e SNoR w.
Hypothesis H10: SNo (v * u).
Hypothesis H11: SNo (v * y).
Hypothesis H12: (z * y + v * u) < z * u + v * y.
Theorem Conj_mul_SNo_prop_1__30__3: (w * u + v * y) < w * y + v * u -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__30__3.
(** Conj_mul_SNo_prop_1__31__4 TMHqjm8xstCfcJ1ximjvdU7CcjiMih21cm6 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__31__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: z :e SNoR x.
Hypothesis H5: SNo (z * y).
Hypothesis H6: SNo (w * y).
Hypothesis H7: u :e SNoR y.
Hypothesis H8: SNo (z * u).
Hypothesis H9: SNo (w * u).
Hypothesis H10: v :e SNoL z.
Hypothesis H11: v :e SNoR w.
Hypothesis H12: SNo (v * u).
Hypothesis H13: SNo (v * y).
Theorem Conj_mul_SNo_prop_1__31__4: (z * y + v * u) < z * u + v * y -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__31__4.
(** Conj_mul_SNo_prop_1__32__6 TMddyo9bXU62qgCsjWv5BUADyLwjeaqdKLP bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__32__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: z :e SNoR x.
Hypothesis H4: w :e SNoL x.
Hypothesis H5: SNo (z * y).
Hypothesis H7: u :e SNoR y.
Hypothesis H8: SNo (z * u).
Hypothesis H9: SNo (w * u).
Hypothesis H10: v :e SNoL z.
Hypothesis H11: v :e SNoR w.
Hypothesis H12: v :e SNoS_ (SNoLev x).
Hypothesis H13: SNo (v * u).
Theorem Conj_mul_SNo_prop_1__32__6: SNo (v * y) -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__32__6.
(** Conj_mul_SNo_prop_1__32__7 TMQpdtERREELk5UuA8DtZjY1SoCHXbGkWE8 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__32__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: z :e SNoR x.
Hypothesis H4: w :e SNoL x.
Hypothesis H5: SNo (z * y).
Hypothesis H6: SNo (w * y).
Hypothesis H8: SNo (z * u).
Hypothesis H9: SNo (w * u).
Hypothesis H10: v :e SNoL z.
Hypothesis H11: v :e SNoR w.
Hypothesis H12: v :e SNoS_ (SNoLev x).
Hypothesis H13: SNo (v * u).
Theorem Conj_mul_SNo_prop_1__32__7: SNo (v * y) -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__32__7.
(** Conj_mul_SNo_prop_1__33__2 TMPXPKmUfM2JAfJKHmbCkCsEUrdb69xjKe3 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__33__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H3: z :e SNoR x.
Hypothesis H4: w :e SNoL x.
Hypothesis H5: SNo (z * y).
Hypothesis H6: SNo (w * y).
Hypothesis H7: u :e SNoR y.
Hypothesis H8: SNo u.
Hypothesis H9: SNo (z * u).
Hypothesis H10: SNo (w * u).
Hypothesis H11: v :e SNoL z.
Hypothesis H12: v :e SNoR w.
Hypothesis H13: v :e SNoS_ (SNoLev x).
Theorem Conj_mul_SNo_prop_1__33__2: SNo (v * u) -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__33__2.
(** Conj_mul_SNo_prop_1__33__6 TMKZMkNfJcpWu4cxgoRT4E3Goh6BQLaVDyn bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__33__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: z :e SNoR x.
Hypothesis H4: w :e SNoL x.
Hypothesis H5: SNo (z * y).
Hypothesis H7: u :e SNoR y.
Hypothesis H8: SNo u.
Hypothesis H9: SNo (z * u).
Hypothesis H10: SNo (w * u).
Hypothesis H11: v :e SNoL z.
Hypothesis H12: v :e SNoR w.
Hypothesis H13: v :e SNoS_ (SNoLev x).
Theorem Conj_mul_SNo_prop_1__33__6: SNo (v * u) -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__33__6.
(** Conj_mul_SNo_prop_1__35__2 TMQLLtZctYKRgFR4zo262tWJaGEkWa3zUAE bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__35__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H3: z :e SNoR x.
Hypothesis H4: SNoLev z :e SNoLev x.
Hypothesis H5: w :e SNoL x.
Hypothesis H6: SNo (z * y).
Hypothesis H7: SNo (w * y).
Hypothesis H8: u :e SNoR y.
Hypothesis H9: SNo u.
Hypothesis H10: SNo (z * u).
Hypothesis H11: SNo (w * u).
Hypothesis H12: v :e SNoL z.
Hypothesis H13: v :e SNoR w.
Hypothesis H14: SNo v.
Hypothesis H15: SNoLev v :e SNoLev z.
Theorem Conj_mul_SNo_prop_1__35__2: SNoLev v :e SNoLev x -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__35__2.
(** Conj_mul_SNo_prop_1__39__15 TMaE15KFJJNTrPoiDrJJ7AxFnuXy8vjtjNR bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__39__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * y2) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> P) -> P)).
Hypothesis H2: (forall y2:set, y2 :e SNoL x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H3: (forall y2:set, y2 :e SNoR y -> SNo (x * y2)).
Hypothesis H4: w :e SNoR y.
Hypothesis H5: u :e SNoL x.
Hypothesis H6: v :e SNoR y.
Hypothesis H7: SNo (z * y).
Hypothesis H8: SNo (x * w).
Hypothesis H9: SNo (z * w).
Hypothesis H10: SNo (u * y).
Hypothesis H11: SNo (x * v).
Hypothesis H12: SNo (u * v).
Hypothesis H13: SNo (u * w).
Hypothesis H14: (z * y + u * w) < u * y + z * w.
Hypothesis H16: x2 :e SNoL v.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 :e SNoR y.
Theorem Conj_mul_SNo_prop_1__39__15: (x * w + u * x2) < x * x2 + u * w -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__39__15.
(** Conj_mul_SNo_prop_1__42__16 TMRzchoronbkspw5vJW1hPicyeoehU3zFLn bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__42__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * y2) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> P) -> P)).
Hypothesis H2: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H3: (forall y2:set, y2 :e SNoR y -> SNo (x * y2)).
Hypothesis H4: z :e SNoR x.
Hypothesis H5: w :e SNoR y.
Hypothesis H6: v :e SNoR y.
Hypothesis H7: SNo (z * y).
Hypothesis H8: SNo (x * w).
Hypothesis H9: SNo (z * w).
Hypothesis H10: SNo (u * y).
Hypothesis H11: SNo (x * v).
Hypothesis H12: SNo (u * v).
Hypothesis H13: SNo (z * v).
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: x2 :e SNoL w.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 :e SNoR y.
Theorem Conj_mul_SNo_prop_1__42__16: (x * w + z * x2) < x * x2 + z * w -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__42__16.
(** Conj_mul_SNo_prop_1__43__9 TMb8wBe8siM1CeCwNPqbGioUQFDF3WBtcw7 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__43__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * y2) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> P) -> P)).
Hypothesis H2: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H3: (forall y2:set, y2 :e SNoR y -> SNo (x * y2)).
Hypothesis H4: z :e SNoR x.
Hypothesis H5: w :e SNoR y.
Hypothesis H6: v :e SNoR y.
Hypothesis H7: SNo v.
Hypothesis H8: SNoLev v :e SNoLev y.
Hypothesis H10: SNo (z * y).
Hypothesis H11: SNo (x * w).
Hypothesis H12: SNo (z * w).
Hypothesis H13: SNo (u * y).
Hypothesis H14: SNo (x * v).
Hypothesis H15: SNo (u * v).
Hypothesis H16: SNo (z * v).
Hypothesis H17: (z * y + u * v) < u * y + z * v.
Hypothesis H18: x2 :e SNoL w.
Hypothesis H19: x2 :e SNoR v.
Hypothesis H20: SNo x2.
Hypothesis H21: SNoLev x2 :e SNoLev v.
Hypothesis H22: v < x2.
Theorem Conj_mul_SNo_prop_1__43__9: x2 :e SNoR y -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__43__9.
(** Conj_mul_SNo_prop_1__43__17 TMcfHhnu5Ycxw1wxrN2JjrGVaMXdMw4VsM1 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__43__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * y2) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> P) -> P)).
Hypothesis H2: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H3: (forall y2:set, y2 :e SNoR y -> SNo (x * y2)).
Hypothesis H4: z :e SNoR x.
Hypothesis H5: w :e SNoR y.
Hypothesis H6: v :e SNoR y.
Hypothesis H7: SNo v.
Hypothesis H8: SNoLev v :e SNoLev y.
Hypothesis H9: y < v.
Hypothesis H10: SNo (z * y).
Hypothesis H11: SNo (x * w).
Hypothesis H12: SNo (z * w).
Hypothesis H13: SNo (u * y).
Hypothesis H14: SNo (x * v).
Hypothesis H15: SNo (u * v).
Hypothesis H16: SNo (z * v).
Hypothesis H18: x2 :e SNoL w.
Hypothesis H19: x2 :e SNoR v.
Hypothesis H20: SNo x2.
Hypothesis H21: SNoLev x2 :e SNoLev v.
Hypothesis H22: v < x2.
Theorem Conj_mul_SNo_prop_1__43__17: x2 :e SNoR y -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__43__17.
(** Conj_mul_SNo_prop_1__44__12 TMZ2aAX36kuGCc5aYPtLGQNoWFQqGTJr4yF bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__44__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoR y -> SNo (x * x2)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: w :e SNoR y.
Hypothesis H7: SNo w.
Hypothesis H8: SNoLev w :e SNoLev y.
Hypothesis H9: y < w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR y.
Hypothesis H13: SNoLev v :e SNoLev y.
Hypothesis H14: y < v.
Hypothesis H15: SNo (z * y).
Hypothesis H16: SNo (x * w).
Hypothesis H17: SNo (z * w).
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (x * v).
Hypothesis H20: SNo (u * v).
Hypothesis H21: SNo (z * v).
Hypothesis H22: SNo (u * w).
Hypothesis H23: (z * y + u * w) < u * y + z * w.
Hypothesis H24: (z * y + u * v) < u * y + z * v.
Hypothesis H25: (x * w + u * v) < u * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Theorem Conj_mul_SNo_prop_1__44__12: ((x * w + z * v) < x * v + z * w -> (z * y + x * w + u * v) < u * y + x * v + z * w) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__44__12.
(** Conj_mul_SNo_prop_1__44__19 TMRfA5BuCZuaDYGw2YFPQJAxGxsUgA3LHaX bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__44__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoR y -> SNo (x * x2)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: w :e SNoR y.
Hypothesis H7: SNo w.
Hypothesis H8: SNoLev w :e SNoLev y.
Hypothesis H9: y < w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR y.
Hypothesis H12: SNo v.
Hypothesis H13: SNoLev v :e SNoLev y.
Hypothesis H14: y < v.
Hypothesis H15: SNo (z * y).
Hypothesis H16: SNo (x * w).
Hypothesis H17: SNo (z * w).
Hypothesis H18: SNo (u * y).
Hypothesis H20: SNo (u * v).
Hypothesis H21: SNo (z * v).
Hypothesis H22: SNo (u * w).
Hypothesis H23: (z * y + u * w) < u * y + z * w.
Hypothesis H24: (z * y + u * v) < u * y + z * v.
Hypothesis H25: (x * w + u * v) < u * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Theorem Conj_mul_SNo_prop_1__44__19: ((x * w + z * v) < x * v + z * w -> (z * y + x * w + u * v) < u * y + x * v + z * w) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__44__19.
(** Conj_mul_SNo_prop_1__44__25 TMVmXL12KbM5FiTcQEbr6PVhvPTALkK5tGo bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__44__25.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoR y -> SNo (x * x2)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: w :e SNoR y.
Hypothesis H7: SNo w.
Hypothesis H8: SNoLev w :e SNoLev y.
Hypothesis H9: y < w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR y.
Hypothesis H12: SNo v.
Hypothesis H13: SNoLev v :e SNoLev y.
Hypothesis H14: y < v.
Hypothesis H15: SNo (z * y).
Hypothesis H16: SNo (x * w).
Hypothesis H17: SNo (z * w).
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (x * v).
Hypothesis H20: SNo (u * v).
Hypothesis H21: SNo (z * v).
Hypothesis H22: SNo (u * w).
Hypothesis H23: (z * y + u * w) < u * y + z * w.
Hypothesis H24: (z * y + u * v) < u * y + z * v.
Theorem Conj_mul_SNo_prop_1__44__25: ((x * w + z * v) < x * v + z * w -> (z * y + x * w + u * v) < u * y + x * v + z * w) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__44__25.
(** Conj_mul_SNo_prop_1__45__10 TMbhVdqtAMQiUPuMPRFFYdyctmibMMvGdL4 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__45__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoR y -> SNo (x * x2)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: w :e SNoR y.
Hypothesis H7: SNo w.
Hypothesis H8: SNoLev w :e SNoLev y.
Hypothesis H9: y < w.
Hypothesis H11: v :e SNoR y.
Hypothesis H12: SNo v.
Hypothesis H13: SNoLev v :e SNoLev y.
Hypothesis H14: y < v.
Hypothesis H15: SNo (z * y).
Hypothesis H16: SNo (x * w).
Hypothesis H17: SNo (z * w).
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (x * v).
Hypothesis H20: SNo (u * v).
Hypothesis H21: SNo (z * v).
Hypothesis H22: SNo (u * w).
Hypothesis H23: (z * y + u * w) < u * y + z * w.
Hypothesis H24: (z * y + u * v) < u * y + z * v.
Theorem Conj_mul_SNo_prop_1__45__10: ((x * w + u * v) < u * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__45__10.
(** Conj_mul_SNo_prop_1__46__15 TMKDHokpSB1qGgVrt2R5c1JczgKm3r8yFih bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__46__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoR y -> SNo (x * x2)).
Hypothesis H5: z :e SNoR x.
Hypothesis H6: w :e SNoR y.
Hypothesis H7: SNo w.
Hypothesis H8: SNoLev w :e SNoLev y.
Hypothesis H9: y < w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR y.
Hypothesis H12: SNo v.
Hypothesis H13: SNoLev v :e SNoLev y.
Hypothesis H14: y < v.
Hypothesis H16: SNo (x * w).
Hypothesis H17: SNo (z * w).
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (x * v).
Hypothesis H20: SNo (u * v).
Hypothesis H21: SNo (z * v).
Hypothesis H22: SNo (u * w).
Hypothesis H23: (forall x2:set, x2 :e SNoR y -> (z * y + u * x2) < u * y + z * x2).
Hypothesis H24: (z * y + u * w) < u * y + z * w.
Theorem Conj_mul_SNo_prop_1__46__15: (z * y + u * v) < u * y + z * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__46__15.
(** Conj_mul_SNo_prop_1__48__5 TMTQdHn8p7KcNs7EcTWn8mvm9b3aukMakyA bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__48__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H6: (forall x2:set, x2 :e SNoR y -> SNo (x * x2)).
Hypothesis H7: z :e SNoR x.
Hypothesis H8: w :e SNoR y.
Hypothesis H9: SNo z.
Hypothesis H10: SNoLev z :e SNoLev x.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H13: y < w.
Hypothesis H14: u :e SNoL x.
Hypothesis H15: v :e SNoR y.
Hypothesis H16: SNo u.
Hypothesis H17: SNo v.
Hypothesis H18: SNoLev v :e SNoLev y.
Hypothesis H19: y < v.
Hypothesis H20: SNo (z * y).
Hypothesis H21: SNo (x * w).
Hypothesis H22: SNo (z * w).
Hypothesis H23: SNo (u * y).
Hypothesis H24: SNo (x * v).
Hypothesis H25: SNo (u * v).
Hypothesis H26: SNo (z * v).
Hypothesis H27: SNo (u * w).
Hypothesis H28: u < z.
Theorem Conj_mul_SNo_prop_1__48__5: (forall x2:set, x2 :e SNoR y -> (z * y + u * x2) < u * y + z * x2) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__48__5.
(** Conj_mul_SNo_prop_1__49__9 TMGzkC27BsSYzFDQBPWS269mwz4ydMRj7wd bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__49__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H6: (forall x2:set, x2 :e SNoR y -> SNo (x * x2)).
Hypothesis H7: z :e SNoR x.
Hypothesis H8: w :e SNoR y.
Hypothesis H10: SNoLev z :e SNoLev x.
Hypothesis H11: x < z.
Hypothesis H12: SNo w.
Hypothesis H13: SNoLev w :e SNoLev y.
Hypothesis H14: y < w.
Hypothesis H15: u :e SNoL x.
Hypothesis H16: v :e SNoR y.
Hypothesis H17: SNo u.
Hypothesis H18: u < x.
Hypothesis H19: SNo v.
Hypothesis H20: SNoLev v :e SNoLev y.
Hypothesis H21: y < v.
Hypothesis H22: SNo (z * y).
Hypothesis H23: SNo (x * w).
Hypothesis H24: SNo (z * w).
Hypothesis H25: SNo (u * y).
Hypothesis H26: SNo (x * v).
Hypothesis H27: SNo (u * v).
Hypothesis H28: SNo (z * v).
Hypothesis H29: SNo (u * w).
Theorem Conj_mul_SNo_prop_1__49__9: u < z -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__49__9.
(** Conj_mul_SNo_prop_1__49__15 TMWcHKwu2R8RcEwvkTcaFNaPBT8mKLsLSnX bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__49__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H6: (forall x2:set, x2 :e SNoR y -> SNo (x * x2)).
Hypothesis H7: z :e SNoR x.
Hypothesis H8: w :e SNoR y.
Hypothesis H9: SNo z.
Hypothesis H10: SNoLev z :e SNoLev x.
Hypothesis H11: x < z.
Hypothesis H12: SNo w.
Hypothesis H13: SNoLev w :e SNoLev y.
Hypothesis H14: y < w.
Hypothesis H16: v :e SNoR y.
Hypothesis H17: SNo u.
Hypothesis H18: u < x.
Hypothesis H19: SNo v.
Hypothesis H20: SNoLev v :e SNoLev y.
Hypothesis H21: y < v.
Hypothesis H22: SNo (z * y).
Hypothesis H23: SNo (x * w).
Hypothesis H24: SNo (z * w).
Hypothesis H25: SNo (u * y).
Hypothesis H26: SNo (x * v).
Hypothesis H27: SNo (u * v).
Hypothesis H28: SNo (z * v).
Hypothesis H29: SNo (u * w).
Theorem Conj_mul_SNo_prop_1__49__15: u < z -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__49__15.
(** Conj_mul_SNo_prop_1__51__0 TMHMzpNex99xmrp3V29PLXXCFhce1x9TPXG bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__51__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: z :e SNoL x.
Hypothesis H4: w :e SNoR x.
Hypothesis H5: SNo (z * y).
Hypothesis H6: SNo (w * y).
Hypothesis H7: u :e SNoL y.
Hypothesis H8: SNo (z * u).
Hypothesis H9: SNo (w * u).
Hypothesis H10: v :e SNoL w.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: SNo (v * u).
Hypothesis H13: SNo (v * y).
Theorem Conj_mul_SNo_prop_1__51__0: (z * y + v * u) < z * u + v * y -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__51__0.
(** Conj_mul_SNo_prop_1__51__2 TMTFZyTEfkCkEXiPpP6WQQ4Eqote9LNmJh7 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__51__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H3: z :e SNoL x.
Hypothesis H4: w :e SNoR x.
Hypothesis H5: SNo (z * y).
Hypothesis H6: SNo (w * y).
Hypothesis H7: u :e SNoL y.
Hypothesis H8: SNo (z * u).
Hypothesis H9: SNo (w * u).
Hypothesis H10: v :e SNoL w.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: SNo (v * u).
Hypothesis H13: SNo (v * y).
Theorem Conj_mul_SNo_prop_1__51__2: (z * y + v * u) < z * u + v * y -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__51__2.
(** Conj_mul_SNo_prop_1__51__12 TMaHVkV1AdjrPSGRJKH2vMU2LTyam4mSF4E bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__51__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: z :e SNoL x.
Hypothesis H4: w :e SNoR x.
Hypothesis H5: SNo (z * y).
Hypothesis H6: SNo (w * y).
Hypothesis H7: u :e SNoL y.
Hypothesis H8: SNo (z * u).
Hypothesis H9: SNo (w * u).
Hypothesis H10: v :e SNoL w.
Hypothesis H11: v :e SNoR z.
Hypothesis H13: SNo (v * y).
Theorem Conj_mul_SNo_prop_1__51__12: (z * y + v * u) < z * u + v * y -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__51__12.
(** Conj_mul_SNo_prop_1__52__12 TMZpNvsMkcESbzvC1UrsPQKFgGYekkiwmbL bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__52__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: z :e SNoL x.
Hypothesis H4: w :e SNoR x.
Hypothesis H5: SNo (z * y).
Hypothesis H6: SNo (w * y).
Hypothesis H7: u :e SNoL y.
Hypothesis H8: SNo (z * u).
Hypothesis H9: SNo (w * u).
Hypothesis H10: v :e SNoL w.
Hypothesis H11: v :e SNoR z.
Hypothesis H13: SNo (v * u).
Theorem Conj_mul_SNo_prop_1__52__12: SNo (v * y) -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__52__12.
(** Conj_mul_SNo_prop_1__54__4 TMK18JiQ6Qf9cM3ycUAigsbnuQLn39wiQPs bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__54__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: z :e SNoL x.
Hypothesis H5: SNo (z * y).
Hypothesis H6: SNo (w * y).
Hypothesis H7: u :e SNoL y.
Hypothesis H8: SNo u.
Hypothesis H9: SNo (z * u).
Hypothesis H10: SNo (w * u).
Hypothesis H11: v :e SNoL w.
Hypothesis H12: v :e SNoR z.
Hypothesis H13: SNo v.
Hypothesis H14: SNoLev v :e SNoLev x.
Theorem Conj_mul_SNo_prop_1__54__4: v :e SNoS_ (SNoLev x) -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__54__4.
(** Conj_mul_SNo_prop_1__55__1 TMG2rXoggoXeMrFpkPrsYH4gMMYYmyuGdzo bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__55__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: z :e SNoL x.
Hypothesis H4: SNoLev z :e SNoLev x.
Hypothesis H5: w :e SNoR x.
Hypothesis H6: SNo (z * y).
Hypothesis H7: SNo (w * y).
Hypothesis H8: u :e SNoL y.
Hypothesis H9: SNo u.
Hypothesis H10: SNo (z * u).
Hypothesis H11: SNo (w * u).
Hypothesis H12: v :e SNoL w.
Hypothesis H13: v :e SNoR z.
Hypothesis H14: SNo v.
Hypothesis H15: SNoLev v :e SNoLev z.
Theorem Conj_mul_SNo_prop_1__55__1: SNoLev v :e SNoLev x -> (z * y + w * u) < w * y + z * u.
Admitted.

End Conj_mul_SNo_prop_1__55__1.
(** Conj_mul_SNo_prop_1__58__11 TMFHGR3w1KWUEB8TttZsGmGYdgVujMhLqDM bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__58__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * y2) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> P) -> P)).
Hypothesis H2: (forall y2:set, y2 :e SNoL x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H3: (forall y2:set, y2 :e SNoL y -> SNo (x * y2)).
Hypothesis H4: z :e SNoL x.
Hypothesis H5: v :e SNoL y.
Hypothesis H6: SNo (z * y).
Hypothesis H7: SNo (x * w).
Hypothesis H8: SNo (z * w).
Hypothesis H9: SNo (u * y).
Hypothesis H10: SNo (x * v).
Hypothesis H12: SNo (z * v).
Hypothesis H13: (z * y + u * v) < u * y + z * v.
Hypothesis H14: x2 :e SNoL v.
Hypothesis H15: SNo x2.
Hypothesis H16: x2 :e SNoL y.
Hypothesis H17: (x * w + z * x2) < x * x2 + z * w.
Theorem Conj_mul_SNo_prop_1__58__11: (x * x2 + z * v) < x * v + z * x2 -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__58__11.
(** Conj_mul_SNo_prop_1__58__17 TMadhBP2tARcVgvEQjb92i4PKxmwfrH1fxb bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__58__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * y2) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> P) -> P)).
Hypothesis H2: (forall y2:set, y2 :e SNoL x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H3: (forall y2:set, y2 :e SNoL y -> SNo (x * y2)).
Hypothesis H4: z :e SNoL x.
Hypothesis H5: v :e SNoL y.
Hypothesis H6: SNo (z * y).
Hypothesis H7: SNo (x * w).
Hypothesis H8: SNo (z * w).
Hypothesis H9: SNo (u * y).
Hypothesis H10: SNo (x * v).
Hypothesis H11: SNo (u * v).
Hypothesis H12: SNo (z * v).
Hypothesis H13: (z * y + u * v) < u * y + z * v.
Hypothesis H14: x2 :e SNoL v.
Hypothesis H15: SNo x2.
Hypothesis H16: x2 :e SNoL y.
Theorem Conj_mul_SNo_prop_1__58__17: (x * x2 + z * v) < x * v + z * x2 -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__58__17.
(** Conj_mul_SNo_prop_1__62__10 TMJWxfjahZWQnm2Z8ag5DgsnwdCmBjt8qeM bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__62__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * y2) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> P) -> P)).
Hypothesis H2: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H3: (forall y2:set, y2 :e SNoL y -> SNo (x * y2)).
Hypothesis H4: w :e SNoL y.
Hypothesis H5: u :e SNoR x.
Hypothesis H6: v :e SNoL y.
Hypothesis H7: SNo (z * y).
Hypothesis H8: SNo (x * w).
Hypothesis H9: SNo (z * w).
Hypothesis H11: SNo (x * v).
Hypothesis H12: SNo (u * v).
Hypothesis H13: SNo (u * w).
Hypothesis H14: (z * y + u * w) < u * y + z * w.
Hypothesis H15: x2 :e SNoL w.
Hypothesis H16: x2 :e SNoR v.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 :e SNoL y.
Theorem Conj_mul_SNo_prop_1__62__10: (x * w + u * x2) < x * x2 + u * w -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__62__10.
(** Conj_mul_SNo_prop_1__62__17 TMWmUqtMvcvpsSKQZSNcSRXBVPAfAXzanvu bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__62__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * y2) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x * w2) < x * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y2 -> (x * y2 + z2 * w2) < z2 * y2 + x * w2)) -> P) -> P)).
Hypothesis H2: (forall y2:set, y2 :e SNoR x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H3: (forall y2:set, y2 :e SNoL y -> SNo (x * y2)).
Hypothesis H4: w :e SNoL y.
Hypothesis H5: u :e SNoR x.
Hypothesis H6: v :e SNoL y.
Hypothesis H7: SNo (z * y).
Hypothesis H8: SNo (x * w).
Hypothesis H9: SNo (z * w).
Hypothesis H10: SNo (u * y).
Hypothesis H11: SNo (x * v).
Hypothesis H12: SNo (u * v).
Hypothesis H13: SNo (u * w).
Hypothesis H14: (z * y + u * w) < u * y + z * w.
Hypothesis H15: x2 :e SNoL w.
Hypothesis H16: x2 :e SNoR v.
Hypothesis H18: x2 :e SNoL y.
Theorem Conj_mul_SNo_prop_1__62__17: (x * w + u * x2) < x * x2 + u * w -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__62__17.
(** Conj_mul_SNo_prop_1__65__5 TMK53EJuJx72mEV2YTRSPeg6j1bf2Jwe6jY bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__65__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL y -> SNo (x * x2)).
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo w.
Hypothesis H8: SNoLev w :e SNoLev y.
Hypothesis H9: w < y.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL y.
Hypothesis H12: SNo v.
Hypothesis H13: SNoLev v :e SNoLev y.
Hypothesis H14: v < y.
Hypothesis H15: SNo (z * y).
Hypothesis H16: SNo (x * w).
Hypothesis H17: SNo (z * w).
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (x * v).
Hypothesis H20: SNo (u * v).
Hypothesis H21: SNo (z * v).
Hypothesis H22: SNo (u * w).
Hypothesis H23: (z * y + u * w) < u * y + z * w.
Hypothesis H24: (z * y + u * v) < u * y + z * v.
Theorem Conj_mul_SNo_prop_1__65__5: ((x * w + u * v) < u * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__65__5.
(** Conj_mul_SNo_prop_1__65__15 TMQHvDANbkyAzj79EqP3qYr6o2SUdSdWb2g bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__65__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL y -> SNo (x * x2)).
Hypothesis H5: z :e SNoL x.
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo w.
Hypothesis H8: SNoLev w :e SNoLev y.
Hypothesis H9: w < y.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL y.
Hypothesis H12: SNo v.
Hypothesis H13: SNoLev v :e SNoLev y.
Hypothesis H14: v < y.
Hypothesis H16: SNo (x * w).
Hypothesis H17: SNo (z * w).
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (x * v).
Hypothesis H20: SNo (u * v).
Hypothesis H21: SNo (z * v).
Hypothesis H22: SNo (u * w).
Hypothesis H23: (z * y + u * w) < u * y + z * w.
Hypothesis H24: (z * y + u * v) < u * y + z * v.
Theorem Conj_mul_SNo_prop_1__65__15: ((x * w + u * v) < u * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__65__15.
(** Conj_mul_SNo_prop_1__66__7 TMZNugXfyHChGQpdxDctKgrQ9PrHUjsFcwD bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__66__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL y -> SNo (x * x2)).
Hypothesis H5: z :e SNoL x.
Hypothesis H6: w :e SNoL y.
Hypothesis H8: SNoLev w :e SNoLev y.
Hypothesis H9: w < y.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL y.
Hypothesis H12: SNo v.
Hypothesis H13: SNoLev v :e SNoLev y.
Hypothesis H14: v < y.
Hypothesis H15: SNo (z * y).
Hypothesis H16: SNo (x * w).
Hypothesis H17: SNo (z * w).
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (x * v).
Hypothesis H20: SNo (u * v).
Hypothesis H21: SNo (z * v).
Hypothesis H22: SNo (u * w).
Hypothesis H23: (forall x2:set, x2 :e SNoL y -> (z * y + u * x2) < u * y + z * x2).
Hypothesis H24: (z * y + u * w) < u * y + z * w.
Theorem Conj_mul_SNo_prop_1__66__7: (z * y + u * v) < u * y + z * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__66__7.
(** Conj_mul_SNo_prop_1__67__5 TMN87rRJmRWisZVw9bktEpDqpRRpDchYKTb bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__67__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL y -> SNo (x * x2)).
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo w.
Hypothesis H8: SNoLev w :e SNoLev y.
Hypothesis H9: w < y.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL y.
Hypothesis H12: SNo v.
Hypothesis H13: SNoLev v :e SNoLev y.
Hypothesis H14: v < y.
Hypothesis H15: SNo (z * y).
Hypothesis H16: SNo (x * w).
Hypothesis H17: SNo (z * w).
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (x * v).
Hypothesis H20: SNo (u * v).
Hypothesis H21: SNo (z * v).
Hypothesis H22: SNo (u * w).
Hypothesis H23: (forall x2:set, x2 :e SNoL y -> (z * y + u * x2) < u * y + z * x2).
Theorem Conj_mul_SNo_prop_1__67__5: (z * y + u * w) < u * y + z * w -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__67__5.
(** Conj_mul_SNo_prop_1__68__13 TMLZku422zzc6voMUCnt6roL8PiuofkncqC bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__68__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H6: (forall x2:set, x2 :e SNoL y -> SNo (x * x2)).
Hypothesis H7: z :e SNoL x.
Hypothesis H8: w :e SNoL y.
Hypothesis H9: SNo z.
Hypothesis H10: SNoLev z :e SNoLev x.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H14: u :e SNoR x.
Hypothesis H15: v :e SNoL y.
Hypothesis H16: SNo u.
Hypothesis H17: SNo v.
Hypothesis H18: SNoLev v :e SNoLev y.
Hypothesis H19: v < y.
Hypothesis H20: SNo (z * y).
Hypothesis H21: SNo (x * w).
Hypothesis H22: SNo (z * w).
Hypothesis H23: SNo (u * y).
Hypothesis H24: SNo (x * v).
Hypothesis H25: SNo (u * v).
Hypothesis H26: SNo (z * v).
Hypothesis H27: SNo (u * w).
Hypothesis H28: z < u.
Theorem Conj_mul_SNo_prop_1__68__13: (forall x2:set, x2 :e SNoL y -> (z * y + u * x2) < u * y + z * x2) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__68__13.
(** Conj_mul_SNo_prop_1__69__0 TMQqZyabXML6eBsMAdGKPVNQytW287r9FvS bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__69__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H6: (forall x2:set, x2 :e SNoL y -> SNo (x * x2)).
Hypothesis H7: z :e SNoL x.
Hypothesis H8: w :e SNoL y.
Hypothesis H9: SNo z.
Hypothesis H10: SNoLev z :e SNoLev x.
Hypothesis H11: z < x.
Hypothesis H12: SNo w.
Hypothesis H13: SNoLev w :e SNoLev y.
Hypothesis H14: w < y.
Hypothesis H15: u :e SNoR x.
Hypothesis H16: v :e SNoL y.
Hypothesis H17: SNo u.
Hypothesis H18: x < u.
Hypothesis H19: SNo v.
Hypothesis H20: SNoLev v :e SNoLev y.
Hypothesis H21: v < y.
Hypothesis H22: SNo (z * y).
Hypothesis H23: SNo (x * w).
Hypothesis H24: SNo (z * w).
Hypothesis H25: SNo (u * y).
Hypothesis H26: SNo (x * v).
Hypothesis H27: SNo (u * v).
Hypothesis H28: SNo (z * v).
Hypothesis H29: SNo (u * w).
Theorem Conj_mul_SNo_prop_1__69__0: z < u -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__69__0.
(** Conj_mul_SNo_prop_1__71__10 TMXTiSf4Xp2S8PCJpUC6Y6fYHKrGvPJiJLb bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__71__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: z :e SNoL y.
Hypothesis H3: w :e SNoR y.
Hypothesis H4: SNo (x * z).
Hypothesis H5: SNo (x * w).
Hypothesis H6: u :e SNoL x.
Hypothesis H7: SNo (u * z).
Hypothesis H8: SNo (u * w).
Hypothesis H9: v :e SNoL w.
Hypothesis H11: SNo (u * v).
Hypothesis H12: SNo (x * v).
Theorem Conj_mul_SNo_prop_1__71__10: (u * w + x * v) < x * w + u * v -> (x * z + u * w) < u * z + x * w.
Admitted.

End Conj_mul_SNo_prop_1__71__10.
(** Conj_mul_SNo_prop_1__73__4 TMdakstiETEwm1MNzP56MyibSAGLpXVieRH bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__73__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H2: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H3: z :e SNoL y.
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (x * w).
Hypothesis H7: u :e SNoL x.
Hypothesis H8: SNo (u * z).
Hypothesis H9: SNo (u * w).
Hypothesis H10: v :e SNoL w.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: SNo v.
Hypothesis H13: v :e SNoS_ (SNoLev y).
Theorem Conj_mul_SNo_prop_1__73__4: SNo (u * v) -> (x * z + u * w) < u * z + x * w.
Admitted.

End Conj_mul_SNo_prop_1__73__4.
(** Conj_mul_SNo_prop_1__76__0 TMTydfwLB2avggdVUwgi3qZhQwwSPzogzHg bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__76__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H1: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * v) -> (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL v -> (x2 * v + x * y2) < x * v + x2 * y2)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR v -> (x2 * v + x * y2) < x * v + x2 * y2)) -> (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR v -> (x * v + x2 * y2) < x2 * v + x * y2)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL v -> (x * v + x2 * y2) < x2 * v + x * y2)) -> P) -> P)).
Hypothesis H2: (forall v:set, v :e SNoL x -> (forall x2:set, SNo x2 -> SNo (v * x2))).
Hypothesis H3: z :e SNoL y.
Hypothesis H4: SNo z.
Hypothesis H5: SNoLev z :e SNoLev y.
Hypothesis H6: w :e SNoR y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (x * w).
Hypothesis H10: z < w.
Hypothesis H11: u :e SNoL x.
Theorem Conj_mul_SNo_prop_1__76__0: SNo (u * z) -> (x * z + u * w) < u * z + x * w.
Admitted.

End Conj_mul_SNo_prop_1__76__0.
(** Conj_mul_SNo_prop_1__78__0 TMP2eeazDWma3JpH27FpCHEBvmzEc9tbMno bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__78__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, SNo z2 -> (forall P:prop, (SNo (y2 * z2) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoR z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoL z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall y2:set, y2 :e SNoL x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H4: (forall y2:set, y2 :e SNoL x -> SNo (y2 * y)).
Hypothesis H5: z :e SNoL x.
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: SNoLev u :e SNoLev x.
Hypothesis H10: u < x.
Hypothesis H11: SNo (z * y).
Hypothesis H12: SNo (x * w).
Hypothesis H13: SNo (z * w).
Hypothesis H14: SNo (u * y).
Hypothesis H15: SNo (x * v).
Hypothesis H16: SNo (u * v).
Hypothesis H17: SNo (u * w).
Hypothesis H18: (x * w + u * v) < u * w + x * v.
Hypothesis H19: x2 :e SNoR z.
Hypothesis H20: x2 :e SNoL u.
Hypothesis H21: (x2 * y + u * w) < u * y + x2 * w.
Theorem Conj_mul_SNo_prop_1__78__0: (z * y + x2 * w) < x2 * y + z * w -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__78__0.
(** Conj_mul_SNo_prop_1__81__2 TMQwvgY6pLBzKZb4QrM29iTGXMF2dBvzELW bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__81__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, SNo z2 -> (forall P:prop, (SNo (y2 * z2) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoR z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoL z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> P) -> P))).
Hypothesis H3: (forall y2:set, y2 :e SNoL x -> (forall z2:set, SNo z2 -> SNo (y2 * z2))).
Hypothesis H4: (forall y2:set, y2 :e SNoL x -> SNo (y2 * y)).
Hypothesis H5: SNo z.
Hypothesis H6: SNoLev z :e SNoLev x.
Hypothesis H7: z < x.
Hypothesis H8: u :e SNoL x.
Hypothesis H9: v :e SNoR y.
Hypothesis H10: SNo v.
Hypothesis H11: SNo (z * y).
Hypothesis H12: SNo (x * w).
Hypothesis H13: SNo (z * w).
Hypothesis H14: SNo (u * y).
Hypothesis H15: SNo (x * v).
Hypothesis H16: SNo (u * v).
Hypothesis H17: SNo (z * v).
Hypothesis H18: (x * w + z * v) < z * w + x * v.
Hypothesis H19: x2 :e SNoL z.
Hypothesis H20: x2 :e SNoR u.
Hypothesis H21: (z * y + x2 * v) < x2 * y + z * v.
Theorem Conj_mul_SNo_prop_1__81__2: (x2 * y + u * v) < u * y + x2 * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__81__2.
(** Conj_mul_SNo_prop_1__81__3 TMc6hoJ3TapeX6iyJamS8JUpRjTYpMqzVf8 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__81__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, SNo z2 -> (forall P:prop, (SNo (y2 * z2) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoL z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoR z2 -> (w2 * z2 + y2 * u2) < y2 * z2 + w2 * u2)) -> (forall w2:set, w2 :e SNoL y2 -> (forall u2:set, u2 :e SNoR z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> (forall w2:set, w2 :e SNoR y2 -> (forall u2:set, u2 :e SNoL z2 -> (y2 * z2 + w2 * u2) < w2 * z2 + y2 * u2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H4: (forall y2:set, y2 :e SNoL x -> SNo (y2 * y)).
Hypothesis H5: SNo z.
Hypothesis H6: SNoLev z :e SNoLev x.
Hypothesis H7: z < x.
Hypothesis H8: u :e SNoL x.
Hypothesis H9: v :e SNoR y.
Hypothesis H10: SNo v.
Hypothesis H11: SNo (z * y).
Hypothesis H12: SNo (x * w).
Hypothesis H13: SNo (z * w).
Hypothesis H14: SNo (u * y).
Hypothesis H15: SNo (x * v).
Hypothesis H16: SNo (u * v).
Hypothesis H17: SNo (z * v).
Hypothesis H18: (x * w + z * v) < z * w + x * v.
Hypothesis H19: x2 :e SNoL z.
Hypothesis H20: x2 :e SNoR u.
Hypothesis H21: (z * y + x2 * v) < x2 * y + z * v.
Theorem Conj_mul_SNo_prop_1__81__3: (x2 * y + u * v) < u * y + x2 * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__81__3.
(** Conj_mul_SNo_prop_1__83__6 TMHEucZqS6Kp9uKVoztJr2GeybxKyRxYP5J bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__83__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> SNo (x2 * y)).
Hypothesis H5: z :e SNoL x.
Hypothesis H7: SNo z.
Hypothesis H8: SNoLev z :e SNoLev x.
Hypothesis H9: z < x.
Hypothesis H10: SNo w.
Hypothesis H11: u :e SNoL x.
Hypothesis H12: v :e SNoR y.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev x.
Hypothesis H15: u < x.
Hypothesis H16: SNo v.
Hypothesis H17: SNo (z * y).
Hypothesis H18: SNo (x * w).
Hypothesis H19: SNo (z * w).
Hypothesis H20: SNo (u * y).
Hypothesis H21: SNo (x * v).
Hypothesis H22: SNo (u * v).
Hypothesis H23: SNo (z * v).
Hypothesis H24: SNo (u * w).
Hypothesis H25: (x * w + z * v) < z * w + x * v.
Hypothesis H26: (x * w + u * v) < u * w + x * v.
Hypothesis H27: (z * y + u * v) < u * y + z * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Theorem Conj_mul_SNo_prop_1__83__6: ((z * y + u * w) < u * y + z * w -> (z * y + x * w + u * v) < u * y + x * v + z * w) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__83__6.
(** Conj_mul_SNo_prop_1__83__21 TMXakydoGNtjsaTyzSSMC7XDECZZpkRLbCm bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__83__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> SNo (x2 * y)).
Hypothesis H5: z :e SNoL x.
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo z.
Hypothesis H8: SNoLev z :e SNoLev x.
Hypothesis H9: z < x.
Hypothesis H10: SNo w.
Hypothesis H11: u :e SNoL x.
Hypothesis H12: v :e SNoR y.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev x.
Hypothesis H15: u < x.
Hypothesis H16: SNo v.
Hypothesis H17: SNo (z * y).
Hypothesis H18: SNo (x * w).
Hypothesis H19: SNo (z * w).
Hypothesis H20: SNo (u * y).
Hypothesis H22: SNo (u * v).
Hypothesis H23: SNo (z * v).
Hypothesis H24: SNo (u * w).
Hypothesis H25: (x * w + z * v) < z * w + x * v.
Hypothesis H26: (x * w + u * v) < u * w + x * v.
Hypothesis H27: (z * y + u * v) < u * y + z * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Theorem Conj_mul_SNo_prop_1__83__21: ((z * y + u * w) < u * y + z * w -> (z * y + x * w + u * v) < u * y + x * v + z * w) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__83__21.
(** Conj_mul_SNo_prop_1__84__18 TMYeTkCobZWuwiYNubz566BQ9RpbC6ajKjs bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__84__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> SNo (x2 * y)).
Hypothesis H5: z :e SNoL x.
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo z.
Hypothesis H8: SNoLev z :e SNoLev x.
Hypothesis H9: z < x.
Hypothesis H10: SNo w.
Hypothesis H11: u :e SNoL x.
Hypothesis H12: v :e SNoR y.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev x.
Hypothesis H15: u < x.
Hypothesis H16: SNo v.
Hypothesis H17: SNo (z * y).
Hypothesis H19: SNo (z * w).
Hypothesis H20: SNo (u * y).
Hypothesis H21: SNo (x * v).
Hypothesis H22: SNo (u * v).
Hypothesis H23: SNo (z * v).
Hypothesis H24: SNo (u * w).
Hypothesis H25: (x * w + z * v) < z * w + x * v.
Hypothesis H26: (x * w + u * v) < u * w + x * v.
Theorem Conj_mul_SNo_prop_1__84__18: ((z * y + u * v) < u * y + z * v -> (z * y + x * w + u * v) < u * y + x * v + z * w) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__84__18.
(** Conj_mul_SNo_prop_1__85__16 TMX6VLTGgXnQe3uADa4PtjmzbxLN2E6XTq7 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__85__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> SNo (x2 * y)).
Hypothesis H5: z :e SNoL x.
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo z.
Hypothesis H8: SNoLev z :e SNoLev x.
Hypothesis H9: z < x.
Hypothesis H10: SNo w.
Hypothesis H11: u :e SNoL x.
Hypothesis H12: v :e SNoR y.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev x.
Hypothesis H15: u < x.
Hypothesis H17: SNo (z * y).
Hypothesis H18: SNo (x * w).
Hypothesis H19: SNo (z * w).
Hypothesis H20: SNo (u * y).
Hypothesis H21: SNo (x * v).
Hypothesis H22: SNo (u * v).
Hypothesis H23: SNo (z * v).
Hypothesis H24: SNo (u * w).
Hypothesis H25: (forall x2:set, x2 :e SNoL x -> (x * w + x2 * v) < x2 * w + x * v).
Hypothesis H26: (x * w + z * v) < z * w + x * v.
Theorem Conj_mul_SNo_prop_1__85__16: (x * w + u * v) < u * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__85__16.
(** Conj_mul_SNo_prop_1__85__24 TMK68LwebqizwKxuB3iSwDa7fYr62ANByt3 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__85__24.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> SNo (x2 * y)).
Hypothesis H5: z :e SNoL x.
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo z.
Hypothesis H8: SNoLev z :e SNoLev x.
Hypothesis H9: z < x.
Hypothesis H10: SNo w.
Hypothesis H11: u :e SNoL x.
Hypothesis H12: v :e SNoR y.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev x.
Hypothesis H15: u < x.
Hypothesis H16: SNo v.
Hypothesis H17: SNo (z * y).
Hypothesis H18: SNo (x * w).
Hypothesis H19: SNo (z * w).
Hypothesis H20: SNo (u * y).
Hypothesis H21: SNo (x * v).
Hypothesis H22: SNo (u * v).
Hypothesis H23: SNo (z * v).
Hypothesis H25: (forall x2:set, x2 :e SNoL x -> (x * w + x2 * v) < x2 * w + x * v).
Hypothesis H26: (x * w + z * v) < z * w + x * v.
Theorem Conj_mul_SNo_prop_1__85__24: (x * w + u * v) < u * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__85__24.
(** Conj_mul_SNo_prop_1__86__11 TMFaK6wjQZsMkHciUswxtYR3aQXzMiTR7a6 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__86__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> SNo (x2 * y)).
Hypothesis H5: z :e SNoL x.
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo z.
Hypothesis H8: SNoLev z :e SNoLev x.
Hypothesis H9: z < x.
Hypothesis H10: SNo w.
Hypothesis H12: v :e SNoR y.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev x.
Hypothesis H15: u < x.
Hypothesis H16: SNo v.
Hypothesis H17: SNo (z * y).
Hypothesis H18: SNo (x * w).
Hypothesis H19: SNo (z * w).
Hypothesis H20: SNo (u * y).
Hypothesis H21: SNo (x * v).
Hypothesis H22: SNo (u * v).
Hypothesis H23: SNo (z * v).
Hypothesis H24: SNo (u * w).
Hypothesis H25: (forall x2:set, x2 :e SNoL x -> (x * w + x2 * v) < x2 * w + x * v).
Theorem Conj_mul_SNo_prop_1__86__11: (x * w + z * v) < z * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__86__11.
(** Conj_mul_SNo_prop_1__86__25 TMd6S7dtSnz7wu5UARtZjZsPhDeaH3wHVgB bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__86__25.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> SNo (x2 * y)).
Hypothesis H5: z :e SNoL x.
Hypothesis H6: w :e SNoL y.
Hypothesis H7: SNo z.
Hypothesis H8: SNoLev z :e SNoLev x.
Hypothesis H9: z < x.
Hypothesis H10: SNo w.
Hypothesis H11: u :e SNoL x.
Hypothesis H12: v :e SNoR y.
Hypothesis H13: SNo u.
Hypothesis H14: SNoLev u :e SNoLev x.
Hypothesis H15: u < x.
Hypothesis H16: SNo v.
Hypothesis H17: SNo (z * y).
Hypothesis H18: SNo (x * w).
Hypothesis H19: SNo (z * w).
Hypothesis H20: SNo (u * y).
Hypothesis H21: SNo (x * v).
Hypothesis H22: SNo (u * v).
Hypothesis H23: SNo (z * v).
Hypothesis H24: SNo (u * w).
Theorem Conj_mul_SNo_prop_1__86__25: (x * w + z * v) < z * w + x * v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__86__25.
(** Conj_mul_SNo_prop_1__87__23 TMUAmSDYB9cdDmsky3whD26f6wMGsaPmbq7 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__87__23.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> SNo (x2 * y)).
Hypothesis H6: z :e SNoL x.
Hypothesis H7: w :e SNoL y.
Hypothesis H8: SNo z.
Hypothesis H9: SNoLev z :e SNoLev x.
Hypothesis H10: z < x.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H13: u :e SNoL x.
Hypothesis H14: v :e SNoR y.
Hypothesis H15: SNo u.
Hypothesis H16: SNoLev u :e SNoLev x.
Hypothesis H17: u < x.
Hypothesis H18: SNo v.
Hypothesis H19: SNo (z * y).
Hypothesis H20: SNo (x * w).
Hypothesis H21: SNo (z * w).
Hypothesis H22: SNo (u * y).
Hypothesis H24: SNo (u * v).
Hypothesis H25: SNo (z * v).
Hypothesis H26: SNo (u * w).
Hypothesis H27: w < v.
Theorem Conj_mul_SNo_prop_1__87__23: (forall x2:set, x2 :e SNoL x -> (x * w + x2 * v) < x2 * w + x * v) -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__87__23.
(** Conj_mul_SNo_prop_1__88__25 TMV66ZpU4SAZNwpNqeUAqDwmSirFtgnxqVg bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__88__25.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> SNo (x2 * y)).
Hypothesis H6: z :e SNoL x.
Hypothesis H7: w :e SNoL y.
Hypothesis H8: SNo z.
Hypothesis H9: SNoLev z :e SNoLev x.
Hypothesis H10: z < x.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H13: w < y.
Hypothesis H14: u :e SNoL x.
Hypothesis H15: v :e SNoR y.
Hypothesis H16: SNo u.
Hypothesis H17: SNoLev u :e SNoLev x.
Hypothesis H18: u < x.
Hypothesis H19: SNo v.
Hypothesis H20: y < v.
Hypothesis H21: SNo (z * y).
Hypothesis H22: SNo (x * w).
Hypothesis H23: SNo (z * w).
Hypothesis H24: SNo (u * y).
Hypothesis H26: SNo (u * v).
Hypothesis H27: SNo (z * v).
Hypothesis H28: SNo (u * w).
Theorem Conj_mul_SNo_prop_1__88__25: w < v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__88__25.
(** Conj_mul_SNo_prop_1__88__27 TMZiXDXeWQnPki8fYvTtoxwgFgyD8ZxNotb bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__88__27.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall P:prop, (SNo (x2 * y2) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoL y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoR y2 -> (z2 * y2 + x2 * w2) < x2 * y2 + z2 * w2)) -> (forall z2:set, z2 :e SNoL x2 -> (forall w2:set, w2 :e SNoR y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> (forall z2:set, z2 :e SNoR x2 -> (forall w2:set, w2 :e SNoL y2 -> (x2 * y2 + z2 * w2) < z2 * y2 + x2 * w2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * x2) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR x2 -> (y2 * x2 + x * z2) < x * x2 + y2 * z2)) -> (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL x2 -> (x * x2 + y2 * z2) < y2 * x2 + x * z2)) -> P) -> P)).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, SNo y2 -> SNo (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> SNo (x2 * y)).
Hypothesis H6: z :e SNoL x.
Hypothesis H7: w :e SNoL y.
Hypothesis H8: SNo z.
Hypothesis H9: SNoLev z :e SNoLev x.
Hypothesis H10: z < x.
Hypothesis H11: SNo w.
Hypothesis H12: SNoLev w :e SNoLev y.
Hypothesis H13: w < y.
Hypothesis H14: u :e SNoL x.
Hypothesis H15: v :e SNoR y.
Hypothesis H16: SNo u.
Hypothesis H17: SNoLev u :e SNoLev x.
Hypothesis H18: u < x.
Hypothesis H19: SNo v.
Hypothesis H20: y < v.
Hypothesis H21: SNo (z * y).
Hypothesis H22: SNo (x * w).
Hypothesis H23: SNo (z * w).
Hypothesis H24: SNo (u * y).
Hypothesis H25: SNo (x * v).
Hypothesis H26: SNo (u * v).
Hypothesis H28: SNo (u * w).
Theorem Conj_mul_SNo_prop_1__88__27: w < v -> (z * y + x * w + u * v) < u * y + x * v + z * w.
Admitted.

End Conj_mul_SNo_prop_1__88__27.
(** Conj_mul_SNo_prop_1__94__4 TMT4MRm2shfbo1gPkYRxAsjD3Btsd4JWiG9 bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__94__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> u * y + x * v + - (u * v) :e z)).
Hypothesis H2: (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoR y -> u * y + x * v + - (u * v) :e z)).
Hypothesis H3: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> u * y + x * v + - (u * v) :e w)).
Hypothesis H5: x * y = SNoCut z w.
Hypothesis H6: (forall u:set, u :e SNoL x -> (forall v:set, SNo v -> SNo (u * v))).
Hypothesis H7: (forall u:set, u :e SNoR x -> (forall v:set, SNo v -> SNo (u * v))).
Hypothesis H8: (forall u:set, u :e SNoL y -> SNo (x * u)).
Hypothesis H9: (forall u:set, u :e SNoR y -> SNo (x * u)).
Hypothesis H10: SNoCutP z w.
Theorem Conj_mul_SNo_prop_1__94__4: SNo (x * y) -> (forall P:prop, (SNo (x * y) -> (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> (u * y + x * v) < x * y + u * v)) -> (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoR y -> (u * y + x * v) < x * y + u * v)) -> (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> (x * y + u * v) < u * y + x * v)) -> (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoL y -> (x * y + u * v) < u * y + x * v)) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__94__4.
(** Conj_mul_SNo_prop_1__96__3 TMdzKjxZ8BPSVoPLgJLGeLvhj2VBgqs5VbY bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__96__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> (forall P:prop, (SNo (u * v) -> (forall x2:set, x2 :e SNoL u -> (forall y2:set, y2 :e SNoL v -> (x2 * v + u * y2) < u * v + x2 * y2)) -> (forall x2:set, x2 :e SNoR u -> (forall y2:set, y2 :e SNoR v -> (x2 * v + u * y2) < u * v + x2 * y2)) -> (forall x2:set, x2 :e SNoL u -> (forall y2:set, y2 :e SNoR v -> (u * v + x2 * y2) < x2 * v + u * y2)) -> (forall x2:set, x2 :e SNoR u -> (forall y2:set, y2 :e SNoL v -> (u * v + x2 * y2) < x2 * v + u * y2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H4: (forall u:set, u :e z -> (forall P:prop, (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> u = v * y + x * x2 + - (v * x2) -> P)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoR y -> u = v * y + x * x2 + - (v * x2) -> P)) -> P)).
Hypothesis H5: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> u * y + x * v + - (u * v) :e z)).
Hypothesis H6: (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoR y -> u * y + x * v + - (u * v) :e z)).
Hypothesis H7: (forall u:set, u :e w -> (forall P:prop, (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR y -> u = v * y + x * x2 + - (v * x2) -> P)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoL y -> u = v * y + x * x2 + - (v * x2) -> P)) -> P)).
Hypothesis H8: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> u * y + x * v + - (u * v) :e w)).
Hypothesis H9: (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoL y -> u * y + x * v + - (u * v) :e w)).
Hypothesis H10: x * y = SNoCut z w.
Hypothesis H11: (forall u:set, u :e SNoL x -> (forall v:set, SNo v -> SNo (u * v))).
Hypothesis H12: (forall u:set, u :e SNoR x -> (forall v:set, SNo v -> SNo (u * v))).
Hypothesis H13: (forall u:set, u :e SNoL x -> SNo (u * y)).
Hypothesis H14: (forall u:set, u :e SNoR x -> SNo (u * y)).
Hypothesis H15: (forall u:set, u :e SNoL y -> SNo (x * u)).
Theorem Conj_mul_SNo_prop_1__96__3: (forall u:set, u :e SNoR y -> SNo (x * u)) -> (forall P:prop, (SNo (x * y) -> (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> (u * y + x * v) < x * y + u * v)) -> (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoR y -> (u * y + x * v) < x * y + u * v)) -> (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> (x * y + u * v) < u * y + x * v)) -> (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoL y -> (x * y + u * v) < u * y + x * v)) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__96__3.
(** Conj_mul_SNo_prop_1__97__6 TMafv7YQUBjTo9jQPgaohTzYWX1CHFHA3FL bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__97__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> (forall P:prop, (SNo (u * v) -> (forall x2:set, x2 :e SNoL u -> (forall y2:set, y2 :e SNoL v -> (x2 * v + u * y2) < u * v + x2 * y2)) -> (forall x2:set, x2 :e SNoR u -> (forall y2:set, y2 :e SNoR v -> (x2 * v + u * y2) < u * v + x2 * y2)) -> (forall x2:set, x2 :e SNoL u -> (forall y2:set, y2 :e SNoR v -> (u * v + x2 * y2) < x2 * v + u * y2)) -> (forall x2:set, x2 :e SNoR u -> (forall y2:set, y2 :e SNoL v -> (u * v + x2 * y2) < x2 * v + u * y2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * u) -> (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL u -> (v * u + x * x2) < x * u + v * x2)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoR u -> (v * u + x * x2) < x * u + v * x2)) -> (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR u -> (x * u + v * x2) < v * u + x * x2)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoL u -> (x * u + v * x2) < v * u + x * x2)) -> P) -> P)).
Hypothesis H4: (forall u:set, u :e z -> (forall P:prop, (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> u = v * y + x * x2 + - (v * x2) -> P)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoR y -> u = v * y + x * x2 + - (v * x2) -> P)) -> P)).
Hypothesis H5: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> u * y + x * v + - (u * v) :e z)).
Hypothesis H7: (forall u:set, u :e w -> (forall P:prop, (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR y -> u = v * y + x * x2 + - (v * x2) -> P)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoL y -> u = v * y + x * x2 + - (v * x2) -> P)) -> P)).
Hypothesis H8: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> u * y + x * v + - (u * v) :e w)).
Hypothesis H9: (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoL y -> u * y + x * v + - (u * v) :e w)).
Hypothesis H10: x * y = SNoCut z w.
Hypothesis H11: (forall u:set, u :e SNoL x -> (forall v:set, SNo v -> SNo (u * v))).
Hypothesis H12: (forall u:set, u :e SNoR x -> (forall v:set, SNo v -> SNo (u * v))).
Hypothesis H13: (forall u:set, u :e SNoL x -> SNo (u * y)).
Hypothesis H14: (forall u:set, u :e SNoR x -> SNo (u * y)).
Theorem Conj_mul_SNo_prop_1__97__6: (forall u:set, u :e SNoL y -> SNo (x * u)) -> (forall P:prop, (SNo (x * y) -> (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> (u * y + x * v) < x * y + u * v)) -> (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoR y -> (u * y + x * v) < x * y + u * v)) -> (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> (x * y + u * v) < u * y + x * v)) -> (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoL y -> (x * y + u * v) < u * y + x * v)) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__97__6.
(** Conj_mul_SNo_prop_1__98__11 TMUEwwJf8LwyD5ohrL6KfvCN2rtEiyNk9Xy bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__98__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> (forall P:prop, (SNo (u * v) -> (forall x2:set, x2 :e SNoL u -> (forall y2:set, y2 :e SNoL v -> (x2 * v + u * y2) < u * v + x2 * y2)) -> (forall x2:set, x2 :e SNoR u -> (forall y2:set, y2 :e SNoR v -> (x2 * v + u * y2) < u * v + x2 * y2)) -> (forall x2:set, x2 :e SNoL u -> (forall y2:set, y2 :e SNoR v -> (u * v + x2 * y2) < x2 * v + u * y2)) -> (forall x2:set, x2 :e SNoR u -> (forall y2:set, y2 :e SNoL v -> (u * v + x2 * y2) < x2 * v + u * y2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * u) -> (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL u -> (v * u + x * x2) < x * u + v * x2)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoR u -> (v * u + x * x2) < x * u + v * x2)) -> (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR u -> (x * u + v * x2) < v * u + x * x2)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoL u -> (x * u + v * x2) < v * u + x * x2)) -> P) -> P)).
Hypothesis H4: (forall u:set, u :e z -> (forall P:prop, (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> u = v * y + x * x2 + - (v * x2) -> P)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoR y -> u = v * y + x * x2 + - (v * x2) -> P)) -> P)).
Hypothesis H5: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> u * y + x * v + - (u * v) :e z)).
Hypothesis H6: (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoR y -> u * y + x * v + - (u * v) :e z)).
Hypothesis H7: (forall u:set, u :e w -> (forall P:prop, (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR y -> u = v * y + x * x2 + - (v * x2) -> P)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoL y -> u = v * y + x * x2 + - (v * x2) -> P)) -> P)).
Hypothesis H8: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> u * y + x * v + - (u * v) :e w)).
Hypothesis H9: (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoL y -> u * y + x * v + - (u * v) :e w)).
Hypothesis H10: x * y = SNoCut z w.
Hypothesis H12: (forall u:set, u :e SNoR x -> (forall v:set, SNo v -> SNo (u * v))).
Hypothesis H13: (forall u:set, u :e SNoL x -> SNo (u * y)).
Theorem Conj_mul_SNo_prop_1__98__11: (forall u:set, u :e SNoR x -> SNo (u * y)) -> (forall P:prop, (SNo (x * y) -> (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> (u * y + x * v) < x * y + u * v)) -> (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoR y -> (u * y + x * v) < x * y + u * v)) -> (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> (x * y + u * v) < u * y + x * v)) -> (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoL y -> (x * y + u * v) < u * y + x * v)) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__98__11.
(** Conj_mul_SNo_prop_1__101__4 TMFtEU3REsyooDgzQdBDus1qsuNqas1n9Wn bounty of about 25 bars **)
Section Conj_mul_SNo_prop_1__101__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e SNoS_ (SNoLev x) -> (forall v:set, SNo v -> (forall P:prop, (SNo (u * v) -> (forall x2:set, x2 :e SNoL u -> (forall y2:set, y2 :e SNoL v -> (x2 * v + u * y2) < u * v + x2 * y2)) -> (forall x2:set, x2 :e SNoR u -> (forall y2:set, y2 :e SNoR v -> (x2 * v + u * y2) < u * v + x2 * y2)) -> (forall x2:set, x2 :e SNoL u -> (forall y2:set, y2 :e SNoR v -> (u * v + x2 * y2) < x2 * v + u * y2)) -> (forall x2:set, x2 :e SNoR u -> (forall y2:set, y2 :e SNoL v -> (u * v + x2 * y2) < x2 * v + u * y2)) -> P) -> P))).
Hypothesis H2: SNo y.
Hypothesis H3: (forall u:set, u :e SNoS_ (SNoLev y) -> (forall P:prop, (SNo (x * u) -> (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL u -> (v * u + x * x2) < x * u + v * x2)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoR u -> (v * u + x * x2) < x * u + v * x2)) -> (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR u -> (x * u + v * x2) < v * u + x * x2)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoL u -> (x * u + v * x2) < v * u + x * x2)) -> P) -> P)).
Hypothesis H5: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> u * y + x * v + - (u * v) :e z)).
Hypothesis H6: (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoR y -> u * y + x * v + - (u * v) :e z)).
Hypothesis H7: (forall u:set, u :e w -> (forall P:prop, (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR y -> u = v * y + x * x2 + - (v * x2) -> P)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoL y -> u = v * y + x * x2 + - (v * x2) -> P)) -> P)).
Hypothesis H8: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> u * y + x * v + - (u * v) :e w)).
Hypothesis H9: (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoL y -> u * y + x * v + - (u * v) :e w)).
Hypothesis H10: x * y = SNoCut z w.
Theorem Conj_mul_SNo_prop_1__101__4: (forall u:set, u :e SNoL x -> (forall v:set, SNo v -> SNo (u * v))) -> (forall P:prop, (SNo (x * y) -> (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> (u * y + x * v) < x * y + u * v)) -> (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoR y -> (u * y + x * v) < x * y + u * v)) -> (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> (x * y + u * v) < u * y + x * v)) -> (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoL y -> (x * y + u * v) < u * y + x * v)) -> P) -> P).
Admitted.

End Conj_mul_SNo_prop_1__101__4.
(** Conj_mul_SNo_eq_3__2__1 TMK1eztCy8yifbWE5UCyb9KKJZLv6MiKpYi bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__2__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H2: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H3: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H4: u :e SNoR x.
Hypothesis H5: v :e SNoR y.
Hypothesis H6: z = u * y + x * v + - (u * v).
Hypothesis H7: SNo (u * y).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (u * v).
Hypothesis H10: x2 :e SNoR x.
Hypothesis H11: y2 :e SNoL y.
Hypothesis H12: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H13: SNo x2.
Hypothesis H14: SNo y2.
Hypothesis H15: SNo (x2 * y).
Theorem Conj_mul_SNo_eq_3__2__1: SNo (x * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__2__1.
(** Conj_mul_SNo_eq_3__2__9 TMaEBcUwJZoTiPyBHhHaPxow6bK3FizSqqY bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__2__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo (x * y).
Hypothesis H2: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H3: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H4: u :e SNoR x.
Hypothesis H5: v :e SNoR y.
Hypothesis H6: z = u * y + x * v + - (u * v).
Hypothesis H7: SNo (u * y).
Hypothesis H8: SNo (x * v).
Hypothesis H10: x2 :e SNoR x.
Hypothesis H11: y2 :e SNoL y.
Hypothesis H12: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H13: SNo x2.
Hypothesis H14: SNo y2.
Hypothesis H15: SNo (x2 * y).
Theorem Conj_mul_SNo_eq_3__2__9: SNo (x * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__2__9.
(** Conj_mul_SNo_eq_3__3__10 TMNocM1yrjDUPfxtNpiHCx2JcEdRQpGfgdT bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__3__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H4: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H5: u :e SNoR x.
Hypothesis H6: v :e SNoR y.
Hypothesis H7: z = u * y + x * v + - (u * v).
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (x * v).
Hypothesis H11: x2 :e SNoR x.
Hypothesis H12: y2 :e SNoL y.
Hypothesis H13: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H14: SNo x2.
Hypothesis H15: SNo y2.
Theorem Conj_mul_SNo_eq_3__3__10: SNo (x2 * y) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__3__10.
(** Conj_mul_SNo_eq_3__3__13 TMaMiaVSWy3YUYNBoYTRiiL7QT8ByWv2fm4 bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__3__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H4: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H5: u :e SNoR x.
Hypothesis H6: v :e SNoR y.
Hypothesis H7: z = u * y + x * v + - (u * v).
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (x * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: x2 :e SNoR x.
Hypothesis H12: y2 :e SNoL y.
Hypothesis H14: SNo x2.
Hypothesis H15: SNo y2.
Theorem Conj_mul_SNo_eq_3__3__13: SNo (x2 * y) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__3__13.
(** Conj_mul_SNo_eq_3__7__14 TMEmvSygZRa2gu92SpLVLk9mq9P6ACPkKKS bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__7__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall y2:set, y2 :e z -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> y2 = z2 * y + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> y2 = z2 * y + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H3: SNo (x * y).
Hypothesis H4: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> (y2 * y + x * z2) < x * y + y2 * z2)).
Hypothesis H5: (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H6: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H7: u :e z.
Hypothesis H8: v :e SNoR x.
Hypothesis H9: x2 :e SNoR y.
Hypothesis H10: w = v * y + x * x2 + - (v * x2).
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (v * y).
Theorem Conj_mul_SNo_eq_3__7__14: SNo (v * x2) -> w < u.
Admitted.

End Conj_mul_SNo_eq_3__7__14.
(** Conj_mul_SNo_eq_3__8__0 TMNN93asp2pVJta9q1nyWeN24sxa36szYSk bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__8__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H1: SNo y.
Hypothesis H2: (forall y2:set, y2 :e z -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> y2 = z2 * y + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> y2 = z2 * y + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H3: SNo (x * y).
Hypothesis H4: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> (y2 * y + x * z2) < x * y + y2 * z2)).
Hypothesis H5: (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H6: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H7: u :e z.
Hypothesis H8: v :e SNoR x.
Hypothesis H9: x2 :e SNoR y.
Hypothesis H10: w = v * y + x * x2 + - (v * x2).
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (v * y).
Theorem Conj_mul_SNo_eq_3__8__0: SNo (x * x2) -> w < u.
Admitted.

End Conj_mul_SNo_eq_3__8__0.
(** Conj_mul_SNo_eq_3__8__2 TMSBS9FGwaXcQZKArwxx7hw79etCtumQmZ5 bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__8__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> (y2 * y + x * z2) < x * y + y2 * z2)).
Hypothesis H5: (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H6: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H7: u :e z.
Hypothesis H8: v :e SNoR x.
Hypothesis H9: x2 :e SNoR y.
Hypothesis H10: w = v * y + x * x2 + - (v * x2).
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (v * y).
Theorem Conj_mul_SNo_eq_3__8__2: SNo (x * x2) -> w < u.
Admitted.

End Conj_mul_SNo_eq_3__8__2.
(** Conj_mul_SNo_eq_3__8__4 TMRAzhSVoBEfg3KDAhBNRU2PZRNqwePp4cx bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__8__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall y2:set, y2 :e z -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> y2 = z2 * y + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> y2 = z2 * y + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H3: SNo (x * y).
Hypothesis H5: (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H6: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H7: u :e z.
Hypothesis H8: v :e SNoR x.
Hypothesis H9: x2 :e SNoR y.
Hypothesis H10: w = v * y + x * x2 + - (v * x2).
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (v * y).
Theorem Conj_mul_SNo_eq_3__8__4: SNo (x * x2) -> w < u.
Admitted.

End Conj_mul_SNo_eq_3__8__4.
(** Conj_mul_SNo_eq_3__8__8 TMWFFbDwkDUG4mMndpMnUkMHYAGojVrAHC6 bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__8__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall y2:set, y2 :e z -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> y2 = z2 * y + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> y2 = z2 * y + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H3: SNo (x * y).
Hypothesis H4: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> (y2 * y + x * z2) < x * y + y2 * z2)).
Hypothesis H5: (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H6: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H7: u :e z.
Hypothesis H9: x2 :e SNoR y.
Hypothesis H10: w = v * y + x * x2 + - (v * x2).
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (v * y).
Theorem Conj_mul_SNo_eq_3__8__8: SNo (x * x2) -> w < u.
Admitted.

End Conj_mul_SNo_eq_3__8__8.
(** Conj_mul_SNo_eq_3__8__12 TMSJGbUy1ePEHeFxZ2iC2xe36goVLctVivc bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__8__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall y2:set, y2 :e z -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> y2 = z2 * y + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> y2 = z2 * y + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H3: SNo (x * y).
Hypothesis H4: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> (y2 * y + x * z2) < x * y + y2 * z2)).
Hypothesis H5: (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H6: (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> (x * y + y2 * z2) < y2 * y + x * z2)).
Hypothesis H7: u :e z.
Hypothesis H8: v :e SNoR x.
Hypothesis H9: x2 :e SNoR y.
Hypothesis H10: w = v * y + x * x2 + - (v * x2).
Hypothesis H11: SNo v.
Hypothesis H13: SNo (v * y).
Theorem Conj_mul_SNo_eq_3__8__12: SNo (x * x2) -> w < u.
Admitted.

End Conj_mul_SNo_eq_3__8__12.
(** Conj_mul_SNo_eq_3__10__3 TMKsvDDvK4YHLBv3omHWg4pMuWhx6wNTnLG bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__10__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H2: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H4: v :e SNoL y.
Hypothesis H5: z = u * y + x * v + - (u * v).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (x * v).
Hypothesis H8: SNo (u * v).
Hypothesis H9: x2 :e SNoR x.
Hypothesis H10: y2 :e SNoL y.
Hypothesis H11: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H12: SNo x2.
Hypothesis H13: SNo y2.
Hypothesis H14: SNo (x2 * y).
Hypothesis H15: SNo (x * y2).
Theorem Conj_mul_SNo_eq_3__10__3: SNo (x2 * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__10__3.
(** Conj_mul_SNo_eq_3__10__14 TMYVjbuHWrAWyzb1kjW8bR8xy7yUtKrbrSq bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__10__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H2: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H3: u :e SNoL x.
Hypothesis H4: v :e SNoL y.
Hypothesis H5: z = u * y + x * v + - (u * v).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (x * v).
Hypothesis H8: SNo (u * v).
Hypothesis H9: x2 :e SNoR x.
Hypothesis H10: y2 :e SNoL y.
Hypothesis H11: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H12: SNo x2.
Hypothesis H13: SNo y2.
Hypothesis H15: SNo (x * y2).
Theorem Conj_mul_SNo_eq_3__10__14: SNo (x2 * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__10__14.
(** Conj_mul_SNo_eq_3__10__15 TMUfct8UDntKCpzcvHRbuu9XigsCnDgrdS2 bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__10__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H2: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H3: u :e SNoL x.
Hypothesis H4: v :e SNoL y.
Hypothesis H5: z = u * y + x * v + - (u * v).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (x * v).
Hypothesis H8: SNo (u * v).
Hypothesis H9: x2 :e SNoR x.
Hypothesis H10: y2 :e SNoL y.
Hypothesis H11: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H12: SNo x2.
Hypothesis H13: SNo y2.
Hypothesis H14: SNo (x2 * y).
Theorem Conj_mul_SNo_eq_3__10__15: SNo (x2 * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__10__15.
(** Conj_mul_SNo_eq_3__12__1 TMYdHaeRkktrsPxk6n7A4woGKqtCA5DbjAv bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__12__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H4: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H5: u :e SNoL x.
Hypothesis H6: v :e SNoL y.
Hypothesis H7: z = u * y + x * v + - (u * v).
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (x * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: x2 :e SNoR x.
Hypothesis H12: y2 :e SNoL y.
Hypothesis H13: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H14: SNo x2.
Hypothesis H15: SNo y2.
Theorem Conj_mul_SNo_eq_3__12__1: SNo (x2 * y) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__12__1.
(** Conj_mul_SNo_eq_3__12__15 TMZiaDRwP1qNiaLb1YJDN4UjSQTtAQty6sN bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__12__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H4: (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H5: u :e SNoL x.
Hypothesis H6: v :e SNoL y.
Hypothesis H7: z = u * y + x * v + - (u * v).
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (x * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: x2 :e SNoR x.
Hypothesis H12: y2 :e SNoL y.
Hypothesis H13: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H14: SNo x2.
Theorem Conj_mul_SNo_eq_3__12__15: SNo (x2 * y) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__12__15.
(** Conj_mul_SNo_eq_3__13__5 TMMbGuWQ45HwJVcLBXKYCyugCCegQ8vWJsG bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__13__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H2: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H3: u :e SNoL x.
Hypothesis H4: v :e SNoL y.
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (x * v).
Hypothesis H8: SNo (u * v).
Hypothesis H9: x2 :e SNoL x.
Hypothesis H10: y2 :e SNoR y.
Hypothesis H11: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H12: SNo x2.
Hypothesis H13: SNo y2.
Hypothesis H14: SNo (x2 * y).
Hypothesis H15: SNo (x * y2).
Theorem Conj_mul_SNo_eq_3__13__5: SNo (x2 * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__13__5.
(** Conj_mul_SNo_eq_3__13__8 TMWkPZpWnKZXabLr71UwwMnLeGYQaQfXdjv bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__13__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H2: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H3: u :e SNoL x.
Hypothesis H4: v :e SNoL y.
Hypothesis H5: z = u * y + x * v + - (u * v).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (x * v).
Hypothesis H9: x2 :e SNoL x.
Hypothesis H10: y2 :e SNoR y.
Hypothesis H11: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H12: SNo x2.
Hypothesis H13: SNo y2.
Hypothesis H14: SNo (x2 * y).
Hypothesis H15: SNo (x * y2).
Theorem Conj_mul_SNo_eq_3__13__8: SNo (x2 * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__13__8.
(** Conj_mul_SNo_eq_3__13__13 TMKFRhjzHfTAFTitp9GfiNhxntNugQfqjcM bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__13__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H2: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H3: u :e SNoL x.
Hypothesis H4: v :e SNoL y.
Hypothesis H5: z = u * y + x * v + - (u * v).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (x * v).
Hypothesis H8: SNo (u * v).
Hypothesis H9: x2 :e SNoL x.
Hypothesis H10: y2 :e SNoR y.
Hypothesis H11: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H12: SNo x2.
Hypothesis H14: SNo (x2 * y).
Hypothesis H15: SNo (x * y2).
Theorem Conj_mul_SNo_eq_3__13__13: SNo (x2 * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__13__13.
(** Conj_mul_SNo_eq_3__13__14 TMMyK8wbLBj3TZtB7tnp3qxCXwX8L8ouRQC bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__13__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H2: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H3: u :e SNoL x.
Hypothesis H4: v :e SNoL y.
Hypothesis H5: z = u * y + x * v + - (u * v).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (x * v).
Hypothesis H8: SNo (u * v).
Hypothesis H9: x2 :e SNoL x.
Hypothesis H10: y2 :e SNoR y.
Hypothesis H11: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H12: SNo x2.
Hypothesis H13: SNo y2.
Hypothesis H15: SNo (x * y2).
Theorem Conj_mul_SNo_eq_3__13__14: SNo (x2 * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__13__14.
(** Conj_mul_SNo_eq_3__14__2 TMRTwNfxynUmbQptUgmLPY6iurQErMBDgz1 bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__14__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo (x * y).
Hypothesis H3: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H4: u :e SNoL x.
Hypothesis H5: v :e SNoL y.
Hypothesis H6: z = u * y + x * v + - (u * v).
Hypothesis H7: SNo (u * y).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (u * v).
Hypothesis H10: x2 :e SNoL x.
Hypothesis H11: y2 :e SNoR y.
Hypothesis H12: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H13: SNo x2.
Hypothesis H14: SNo y2.
Hypothesis H15: SNo (x2 * y).
Theorem Conj_mul_SNo_eq_3__14__2: SNo (x * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__14__2.
(** Conj_mul_SNo_eq_3__14__12 TMVH2x4Ko1vr7fX5i71a7WLXVzpDEmyVn1c bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__14__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo (x * y).
Hypothesis H2: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H3: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H4: u :e SNoL x.
Hypothesis H5: v :e SNoL y.
Hypothesis H6: z = u * y + x * v + - (u * v).
Hypothesis H7: SNo (u * y).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (u * v).
Hypothesis H10: x2 :e SNoL x.
Hypothesis H11: y2 :e SNoR y.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo y2.
Hypothesis H15: SNo (x2 * y).
Theorem Conj_mul_SNo_eq_3__14__12: SNo (x * y2) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__14__12.
(** Conj_mul_SNo_eq_3__15__4 TMLhVonSxp18GuKBNKPG3WDe6RQqQq1oXg8 bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__15__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H5: u :e SNoL x.
Hypothesis H6: v :e SNoL y.
Hypothesis H7: z = u * y + x * v + - (u * v).
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (x * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: x2 :e SNoL x.
Hypothesis H12: y2 :e SNoR y.
Hypothesis H13: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H14: SNo x2.
Hypothesis H15: SNo y2.
Theorem Conj_mul_SNo_eq_3__15__4: SNo (x2 * y) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__15__4.
(** Conj_mul_SNo_eq_3__15__15 TMTcgBRXxjLL51kiyKj3KnerSTbJHq72GKj bounty of about 25 bars **)
Section Conj_mul_SNo_eq_3__15__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL y -> (z2 * y + x * w2) < x * y + z2 * w2)).
Hypothesis H4: (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR y -> (x * y + z2 * w2) < z2 * y + x * w2)).
Hypothesis H5: u :e SNoL x.
Hypothesis H6: v :e SNoL y.
Hypothesis H7: z = u * y + x * v + - (u * v).
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (x * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: x2 :e SNoL x.
Hypothesis H12: y2 :e SNoR y.
Hypothesis H13: w = x2 * y + x * y2 + - (x2 * y2).
Hypothesis H14: SNo x2.
Theorem Conj_mul_SNo_eq_3__15__15: SNo (x2 * y) -> z < w.
Admitted.

End Conj_mul_SNo_eq_3__15__15.
(** Conj_mul_SNo_Lt__8__12 TMUi2N8CmfnNhkR7dEWRmqEzMtgQvLbreXr bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__8__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo z.
Hypothesis H1: SNo (x * y).
Hypothesis H2: SNo (z * y).
Hypothesis H3: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H4: SNo (x * w).
Hypothesis H5: SNo (z * w).
Hypothesis H6: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H7: SNo (z * y + x * w).
Hypothesis H8: SNo (x * y + z * w).
Hypothesis H9: x :e SNoR z.
Hypothesis H10: SNo u.
Hypothesis H11: u :e SNoL y.
Hypothesis H13: SNo (x * u).
Theorem Conj_mul_SNo_Lt__8__12: SNo (z * u) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__8__12.
(** Conj_mul_SNo_Lt__10__5 TMJmsWtTQdmtNAJTrWXUpD5NzyxcqrKaTma bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__10__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo z.
Hypothesis H2: SNo w.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (z * y).
Hypothesis H6: SNo (x * w).
Hypothesis H7: SNo (z * w).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H9: SNo (z * y + x * w).
Hypothesis H10: SNo (x * y + z * w).
Hypothesis H11: x :e SNoR z.
Hypothesis H12: SNo u.
Hypothesis H13: w < u.
Hypothesis H14: SNoLev u :e SNoLev w.
Hypothesis H15: u :e SNoL y.
Theorem Conj_mul_SNo_Lt__10__5: u :e SNoR w -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__10__5.
(** Conj_mul_SNo_Lt__13__5 TMW2oTjFewTeCQwyz5MpBnxT2gGL6FkZxyn bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__13__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo y.
Hypothesis H1: SNo w.
Hypothesis H2: w < y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (z * y).
Hypothesis H6: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR w -> (x * w + u * v) < u * w + x * v)).
Hypothesis H7: SNo (z * w).
Hypothesis H8: z :e SNoL x.
Hypothesis H9: SNoLev y :e SNoLev w.
Theorem Conj_mul_SNo_Lt__13__5: y :e SNoR w -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__13__5.
(** Conj_mul_SNo_Lt__15__6 TMLp5puwZgkm8MWLwQ3479bZy3z7SMHtAPh bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__15__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H4: SNo (z * w).
Hypothesis H5: SNo (z * y + x * w).
Hypothesis H7: z :e SNoL x.
Hypothesis H8: u :e SNoR w.
Hypothesis H9: SNo (x * u).
Hypothesis H10: SNo (z * u).
Hypothesis H11: SNo (z * y + x * u).
Hypothesis H12: SNo (z * w + x * u).
Hypothesis H13: SNo (x * y + z * u).
Hypothesis H14: SNo (x * w + z * u).
Hypothesis H15: (z * y + x * u) < x * y + z * u.
Theorem Conj_mul_SNo_Lt__15__6: (x * w + z * u) < z * w + x * u -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__15__6.
(** Conj_mul_SNo_Lt__18__9 TMWviGyBXZCryZU5DPM4KrvMCFb3FdRNNYj bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__18__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H2: SNo (z * y).
Hypothesis H3: SNo (x * w).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H5: SNo (z * w).
Hypothesis H6: SNo (z * y + x * w).
Hypothesis H7: SNo (x * y + z * w).
Hypothesis H8: z :e SNoL x.
Hypothesis H10: u :e SNoR w.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (z * u).
Hypothesis H13: SNo (z * y + x * u).
Hypothesis H14: SNo (z * w + x * u).
Theorem Conj_mul_SNo_Lt__18__9: SNo (x * y + z * u) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__18__9.
(** Conj_mul_SNo_Lt__19__2 TMUXoNKxu7hQtWawTtRVjrToq3C7wFSNUZG bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__19__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H3: SNo (x * w).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H5: SNo (z * w).
Hypothesis H6: SNo (z * y + x * w).
Hypothesis H7: SNo (x * y + z * w).
Hypothesis H8: z :e SNoL x.
Hypothesis H9: u :e SNoL y.
Hypothesis H10: u :e SNoR w.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (z * u).
Hypothesis H13: SNo (z * y + x * u).
Theorem Conj_mul_SNo_Lt__19__2: SNo (z * w + x * u) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__19__2.
