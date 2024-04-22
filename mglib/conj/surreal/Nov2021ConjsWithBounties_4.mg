(** $I sig/Nov2021ConjPreamble.mgs **)

(** Conj_mul_SNo_assoc_lem2__104__20 TMK6u5DjJQh1yirxpZGirezK2TB3pfkedXk bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__104__20.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo v -> SNo x2 -> SNo (g v x2)).
Hypothesis H1: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g v (x2 + y2) = g v x2 + g v y2).
Hypothesis H2: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g (v + x2) y2 = g v y2 + g x2 y2).
Hypothesis H3: (forall v:set, forall x2:set, SNo v -> SNo x2 -> (forall y2:set, y2 :e SNoL (g v x2) -> (forall P:prop, (forall z2:set, z2 :e SNoL v -> (forall w2:set, w2 :e SNoL x2 -> (y2 + g z2 w2) <= g z2 x2 + g v w2 -> P)) -> (forall z2:set, z2 :e SNoR v -> (forall w2:set, w2 :e SNoR x2 -> (y2 + g z2 w2) <= g z2 x2 + g v w2 -> P)) -> P))).
Hypothesis H4: (forall v:set, forall x2:set, SNo v -> SNo x2 -> (forall y2:set, y2 :e SNoR (g v x2) -> (forall P:prop, (forall z2:set, z2 :e SNoL v -> (forall w2:set, w2 :e SNoR x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> (forall z2:set, z2 :e SNoR v -> (forall w2:set, w2 :e SNoL x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> P))).
Hypothesis H5: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 < v -> z2 < x2 -> (g y2 x2 + g v z2) < g v x2 + g y2 z2).
Hypothesis H6: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 <= v -> z2 <= x2 -> (g y2 x2 + g v z2) <= g v x2 + g y2 z2).
Hypothesis H7: SNo x.
Hypothesis H8: SNo y.
Hypothesis H9: SNo z.
Hypothesis H10: (forall v:set, v :e SNoS_ (SNoLev x) -> g v (g y z) = g (g v y) z).
Hypothesis H11: (forall v:set, v :e SNoS_ (SNoLev y) -> g x (g v z) = g (g x v) z).
Hypothesis H12: (forall v:set, v :e SNoS_ (SNoLev z) -> g x (g y v) = g (g x y) v).
Hypothesis H13: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> g v (g x2 z) = g (g v x2) z)).
Hypothesis H14: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g v (g y x2) = g (g v y) x2)).
Hypothesis H15: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g x (g v x2) = g (g x v) x2)).
Hypothesis H16: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> g v (g x2 y2) = g (g v x2) y2))).
Hypothesis H17: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> P)).
Hypothesis H18: u :e w.
Hypothesis H19: SNo (g x y).
Hypothesis H21: SNo (g (g x y) z).
Theorem Conj_mul_SNo_assoc_lem2__104__20: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, SNo x2 -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> u = g v (g y z) + g x x2 + - (g v x2) -> (g x (g y2 z + g y z2) + g v (x2 + g y2 z2)) <= g v (g y2 z + g y z2) + g x (x2 + g y2 z2) -> (g (g x y + g v y2) z + g (g v y + g x y2) z2) < g (g v y + g x y2) z + g (g x y + g v y2) z2 -> g (g x y) z < u)))) -> g (g x y) z < u.
Admitted.

End Conj_mul_SNo_assoc_lem2__104__20.
(** Conj_mul_SNo_assoc_lem2__105__3 TMPYWVCR1T5YtSVDRtVo4wu6uTCVE1KYosx bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__105__3.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo v -> SNo x2 -> SNo (g v x2)).
Hypothesis H1: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g v (x2 + y2) = g v x2 + g v y2).
Hypothesis H2: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g (v + x2) y2 = g v y2 + g x2 y2).
Hypothesis H4: (forall v:set, forall x2:set, SNo v -> SNo x2 -> (forall y2:set, y2 :e SNoR (g v x2) -> (forall P:prop, (forall z2:set, z2 :e SNoL v -> (forall w2:set, w2 :e SNoR x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> (forall z2:set, z2 :e SNoR v -> (forall w2:set, w2 :e SNoL x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> P))).
Hypothesis H5: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 < v -> z2 < x2 -> (g y2 x2 + g v z2) < g v x2 + g y2 z2).
Hypothesis H6: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 <= v -> z2 <= x2 -> (g y2 x2 + g v z2) <= g v x2 + g y2 z2).
Hypothesis H7: SNo x.
Hypothesis H8: SNo y.
Hypothesis H9: SNo z.
Hypothesis H10: (forall v:set, v :e SNoS_ (SNoLev x) -> g v (g y z) = g (g v y) z).
Hypothesis H11: (forall v:set, v :e SNoS_ (SNoLev y) -> g x (g v z) = g (g x v) z).
Hypothesis H12: (forall v:set, v :e SNoS_ (SNoLev z) -> g x (g y v) = g (g x y) v).
Hypothesis H13: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> g v (g x2 z) = g (g v x2) z)).
Hypothesis H14: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g v (g y x2) = g (g v y) x2)).
Hypothesis H15: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g x (g v x2) = g (g x v) x2)).
Hypothesis H16: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> g v (g x2 y2) = g (g v x2) y2))).
Hypothesis H17: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> P)).
Hypothesis H18: u :e w.
Hypothesis H19: SNo (g x y).
Hypothesis H20: SNo (g y z).
Theorem Conj_mul_SNo_assoc_lem2__105__3: SNo (g (g x y) z) -> g (g x y) z < u.
Admitted.

End Conj_mul_SNo_assoc_lem2__105__3.
(** Conj_mul_SNo_assoc_lem2__105__5 TMYuBvd6eZcAY8qsc2DMHcEB7nrCiXYsEKi bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__105__5.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo v -> SNo x2 -> SNo (g v x2)).
Hypothesis H1: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g v (x2 + y2) = g v x2 + g v y2).
Hypothesis H2: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g (v + x2) y2 = g v y2 + g x2 y2).
Hypothesis H3: (forall v:set, forall x2:set, SNo v -> SNo x2 -> (forall y2:set, y2 :e SNoL (g v x2) -> (forall P:prop, (forall z2:set, z2 :e SNoL v -> (forall w2:set, w2 :e SNoL x2 -> (y2 + g z2 w2) <= g z2 x2 + g v w2 -> P)) -> (forall z2:set, z2 :e SNoR v -> (forall w2:set, w2 :e SNoR x2 -> (y2 + g z2 w2) <= g z2 x2 + g v w2 -> P)) -> P))).
Hypothesis H4: (forall v:set, forall x2:set, SNo v -> SNo x2 -> (forall y2:set, y2 :e SNoR (g v x2) -> (forall P:prop, (forall z2:set, z2 :e SNoL v -> (forall w2:set, w2 :e SNoR x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> (forall z2:set, z2 :e SNoR v -> (forall w2:set, w2 :e SNoL x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> P))).
Hypothesis H6: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 <= v -> z2 <= x2 -> (g y2 x2 + g v z2) <= g v x2 + g y2 z2).
Hypothesis H7: SNo x.
Hypothesis H8: SNo y.
Hypothesis H9: SNo z.
Hypothesis H10: (forall v:set, v :e SNoS_ (SNoLev x) -> g v (g y z) = g (g v y) z).
Hypothesis H11: (forall v:set, v :e SNoS_ (SNoLev y) -> g x (g v z) = g (g x v) z).
Hypothesis H12: (forall v:set, v :e SNoS_ (SNoLev z) -> g x (g y v) = g (g x y) v).
Hypothesis H13: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> g v (g x2 z) = g (g v x2) z)).
Hypothesis H14: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g v (g y x2) = g (g v y) x2)).
Hypothesis H15: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g x (g v x2) = g (g x v) x2)).
Hypothesis H16: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> g v (g x2 y2) = g (g v x2) y2))).
Hypothesis H17: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> P)).
Hypothesis H18: u :e w.
Hypothesis H19: SNo (g x y).
Hypothesis H20: SNo (g y z).
Theorem Conj_mul_SNo_assoc_lem2__105__5: SNo (g (g x y) z) -> g (g x y) z < u.
Admitted.

End Conj_mul_SNo_assoc_lem2__105__5.
(** Conj_mul_SNo_assoc_lem2__105__8 TMWAfofFQMt7amBFC2oFkmZg7hpKA41Jmhi bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__105__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo v -> SNo x2 -> SNo (g v x2)).
Hypothesis H1: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g v (x2 + y2) = g v x2 + g v y2).
Hypothesis H2: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g (v + x2) y2 = g v y2 + g x2 y2).
Hypothesis H3: (forall v:set, forall x2:set, SNo v -> SNo x2 -> (forall y2:set, y2 :e SNoL (g v x2) -> (forall P:prop, (forall z2:set, z2 :e SNoL v -> (forall w2:set, w2 :e SNoL x2 -> (y2 + g z2 w2) <= g z2 x2 + g v w2 -> P)) -> (forall z2:set, z2 :e SNoR v -> (forall w2:set, w2 :e SNoR x2 -> (y2 + g z2 w2) <= g z2 x2 + g v w2 -> P)) -> P))).
Hypothesis H4: (forall v:set, forall x2:set, SNo v -> SNo x2 -> (forall y2:set, y2 :e SNoR (g v x2) -> (forall P:prop, (forall z2:set, z2 :e SNoL v -> (forall w2:set, w2 :e SNoR x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> (forall z2:set, z2 :e SNoR v -> (forall w2:set, w2 :e SNoL x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> P))).
Hypothesis H5: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 < v -> z2 < x2 -> (g y2 x2 + g v z2) < g v x2 + g y2 z2).
Hypothesis H6: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 <= v -> z2 <= x2 -> (g y2 x2 + g v z2) <= g v x2 + g y2 z2).
Hypothesis H7: SNo x.
Hypothesis H9: SNo z.
Hypothesis H10: (forall v:set, v :e SNoS_ (SNoLev x) -> g v (g y z) = g (g v y) z).
Hypothesis H11: (forall v:set, v :e SNoS_ (SNoLev y) -> g x (g v z) = g (g x v) z).
Hypothesis H12: (forall v:set, v :e SNoS_ (SNoLev z) -> g x (g y v) = g (g x y) v).
Hypothesis H13: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> g v (g x2 z) = g (g v x2) z)).
Hypothesis H14: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g v (g y x2) = g (g v y) x2)).
Hypothesis H15: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g x (g v x2) = g (g x v) x2)).
Hypothesis H16: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> g v (g x2 y2) = g (g v x2) y2))).
Hypothesis H17: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> P)).
Hypothesis H18: u :e w.
Hypothesis H19: SNo (g x y).
Hypothesis H20: SNo (g y z).
Theorem Conj_mul_SNo_assoc_lem2__105__8: SNo (g (g x y) z) -> g (g x y) z < u.
Admitted.

End Conj_mul_SNo_assoc_lem2__105__8.
(** Conj_mul_SNo_assoc_lem2__106__8 TMWMdmixDcm5Dz1fmjipp2yRtdXkQnTATBY bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__106__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo v -> SNo x2 -> SNo (g v x2)).
Hypothesis H1: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g v (x2 + y2) = g v x2 + g v y2).
Hypothesis H2: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g (v + x2) y2 = g v y2 + g x2 y2).
Hypothesis H3: (forall v:set, forall x2:set, SNo v -> SNo x2 -> (forall y2:set, y2 :e SNoL (g v x2) -> (forall P:prop, (forall z2:set, z2 :e SNoL v -> (forall w2:set, w2 :e SNoL x2 -> (y2 + g z2 w2) <= g z2 x2 + g v w2 -> P)) -> (forall z2:set, z2 :e SNoR v -> (forall w2:set, w2 :e SNoR x2 -> (y2 + g z2 w2) <= g z2 x2 + g v w2 -> P)) -> P))).
Hypothesis H4: (forall v:set, forall x2:set, SNo v -> SNo x2 -> (forall y2:set, y2 :e SNoR (g v x2) -> (forall P:prop, (forall z2:set, z2 :e SNoL v -> (forall w2:set, w2 :e SNoR x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> (forall z2:set, z2 :e SNoR v -> (forall w2:set, w2 :e SNoL x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> P))).
Hypothesis H5: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 < v -> z2 < x2 -> (g y2 x2 + g v z2) < g v x2 + g y2 z2).
Hypothesis H6: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 <= v -> z2 <= x2 -> (g y2 x2 + g v z2) <= g v x2 + g y2 z2).
Hypothesis H7: SNo x.
Hypothesis H9: SNo z.
Hypothesis H10: (forall v:set, v :e SNoS_ (SNoLev x) -> g v (g y z) = g (g v y) z).
Hypothesis H11: (forall v:set, v :e SNoS_ (SNoLev y) -> g x (g v z) = g (g x v) z).
Hypothesis H12: (forall v:set, v :e SNoS_ (SNoLev z) -> g x (g y v) = g (g x y) v).
Hypothesis H13: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> g v (g x2 z) = g (g v x2) z)).
Hypothesis H14: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g v (g y x2) = g (g v y) x2)).
Hypothesis H15: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g x (g v x2) = g (g x v) x2)).
Hypothesis H16: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> g v (g x2 y2) = g (g v x2) y2))).
Hypothesis H17: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> P)).
Hypothesis H18: u :e w.
Hypothesis H19: SNo (g x y).
Theorem Conj_mul_SNo_assoc_lem2__106__8: SNo (g y z) -> g (g x y) z < u.
Admitted.

End Conj_mul_SNo_assoc_lem2__106__8.
(** Conj_mul_SNo_assoc_lem2__107__3 TMMwe7swEjYDLfswiADW22LntB3yMrmiYBa bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__107__3.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo v -> SNo x2 -> SNo (g v x2)).
Hypothesis H1: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g v (x2 + y2) = g v x2 + g v y2).
Hypothesis H2: (forall v:set, forall x2:set, forall y2:set, SNo v -> SNo x2 -> SNo y2 -> g (v + x2) y2 = g v y2 + g x2 y2).
Hypothesis H4: (forall v:set, forall x2:set, SNo v -> SNo x2 -> (forall y2:set, y2 :e SNoR (g v x2) -> (forall P:prop, (forall z2:set, z2 :e SNoL v -> (forall w2:set, w2 :e SNoR x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> (forall z2:set, z2 :e SNoR v -> (forall w2:set, w2 :e SNoL x2 -> (g z2 x2 + g v w2) <= y2 + g z2 w2 -> P)) -> P))).
Hypothesis H5: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 < v -> z2 < x2 -> (g y2 x2 + g v z2) < g v x2 + g y2 z2).
Hypothesis H6: (forall v:set, forall x2:set, forall y2:set, forall z2:set, SNo v -> SNo x2 -> SNo y2 -> SNo z2 -> y2 <= v -> z2 <= x2 -> (g y2 x2 + g v z2) <= g v x2 + g y2 z2).
Hypothesis H7: SNo x.
Hypothesis H8: SNo y.
Hypothesis H9: SNo z.
Hypothesis H10: (forall v:set, v :e SNoS_ (SNoLev x) -> g v (g y z) = g (g v y) z).
Hypothesis H11: (forall v:set, v :e SNoS_ (SNoLev y) -> g x (g v z) = g (g x v) z).
Hypothesis H12: (forall v:set, v :e SNoS_ (SNoLev z) -> g x (g y v) = g (g x y) v).
Hypothesis H13: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> g v (g x2 z) = g (g v x2) z)).
Hypothesis H14: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g v (g y x2) = g (g v y) x2)).
Hypothesis H15: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g x (g v x2) = g (g x v) x2)).
Hypothesis H16: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> g v (g x2 y2) = g (g v x2) y2))).
Hypothesis H17: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> P)).
Hypothesis H18: u :e w.
Theorem Conj_mul_SNo_assoc_lem2__107__3: SNo (g x y) -> g (g x y) z < u.
Admitted.

End Conj_mul_SNo_assoc_lem2__107__3.
(** Conj_mul_SNo_assoc__1__15 TMYr9xoXoDRbqpZkV5pui5VVJR3DXoy3KPs bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__1__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> x * y * y2 = (x * y) * y2).
Hypothesis H6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> y2 * z2 * z = (y2 * z2) * z)).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H11: SNoCutP w u.
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H13: (forall y2:set, y2 :e u -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H18: (x * y) * z = SNoCut v x2.
Hypothesis H19: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoL (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoL z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoR z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> P))).
Hypothesis H20: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoR (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoR z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoL z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> P))).
Hypothesis H21: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 < y2 -> u2 < z2 -> (z2 * w2 + u2 * y2) < z2 * y2 + u2 * w2).
Hypothesis H22: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 <= y2 -> u2 <= z2 -> (z2 * w2 + u2 * y2) <= z2 * y2 + u2 * w2).
Hypothesis H23: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (y2 * y) * z = y2 * y * z).
Hypothesis H24: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (x * y2) * z = x * y2 * z).
Hypothesis H25: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x * y) * y2 = x * y * y2).
Hypothesis H26: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (z2 * y2) * z = z2 * y2 * z)).
Hypothesis H27: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (z2 * y) * y2 = z2 * y * y2)).
Hypothesis H28: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (x * z2) * y2 = x * z2 * y2)).
Theorem Conj_mul_SNo_assoc__1__15: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev x) -> (w2 * z2) * y2 = w2 * z2 * y2))) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__1__15.
(** Conj_mul_SNo_assoc__1__25 TMciSyPjj9S6v3rpBPVGhU2FWHQyr1vgEn2 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__1__25.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> x * y * y2 = (x * y) * y2).
Hypothesis H6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> y2 * z2 * z = (y2 * z2) * z)).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H11: SNoCutP w u.
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H13: (forall y2:set, y2 :e u -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H15: SNoCutP v x2.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H18: (x * y) * z = SNoCut v x2.
Hypothesis H19: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoL (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoL z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoR z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> P))).
Hypothesis H20: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoR (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoR z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoL z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> P))).
Hypothesis H21: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 < y2 -> u2 < z2 -> (z2 * w2 + u2 * y2) < z2 * y2 + u2 * w2).
Hypothesis H22: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 <= y2 -> u2 <= z2 -> (z2 * w2 + u2 * y2) <= z2 * y2 + u2 * w2).
Hypothesis H23: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (y2 * y) * z = y2 * y * z).
Hypothesis H24: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (x * y2) * z = x * y2 * z).
Hypothesis H26: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (z2 * y2) * z = z2 * y2 * z)).
Hypothesis H27: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (z2 * y) * y2 = z2 * y * y2)).
Hypothesis H28: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (x * z2) * y2 = x * z2 * y2)).
Theorem Conj_mul_SNo_assoc__1__25: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev x) -> (w2 * z2) * y2 = w2 * z2 * y2))) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__1__25.
(** Conj_mul_SNo_assoc__3__5 TMQUgb6TcmJVwmvSxEvVMfXvkNcUbYVdDqM bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__3__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> y2 * z2 * z = (y2 * z2) * z)).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H11: SNoCutP w u.
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H13: (forall y2:set, y2 :e u -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H15: SNoCutP v x2.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H18: (x * y) * z = SNoCut v x2.
Hypothesis H19: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoL (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoL z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoR z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> P))).
Hypothesis H20: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoR (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoR z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoL z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> P))).
Hypothesis H21: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 < y2 -> u2 < z2 -> (z2 * w2 + u2 * y2) < z2 * y2 + u2 * w2).
Hypothesis H22: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 <= y2 -> u2 <= z2 -> (z2 * w2 + u2 * y2) <= z2 * y2 + u2 * w2).
Hypothesis H23: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (y2 * y) * z = y2 * y * z).
Hypothesis H24: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (x * y2) * z = x * y2 * z).
Hypothesis H25: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x * y) * y2 = x * y * y2).
Hypothesis H26: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (z2 * y2) * z = z2 * y2 * z)).
Theorem Conj_mul_SNo_assoc__3__5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (z2 * y) * y2 = z2 * y * y2)) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__3__5.
(** Conj_mul_SNo_assoc__5__18 TMTJHPauSJMxB7bdMQJUnr5s2Cf3dffVG5Y bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__5__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> x * y * y2 = (x * y) * y2).
Hypothesis H6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> y2 * z2 * z = (y2 * z2) * z)).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H11: SNoCutP w u.
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H13: (forall y2:set, y2 :e u -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H15: SNoCutP v x2.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H19: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoL (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoL z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoR z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> P))).
Hypothesis H20: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoR (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoR z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoL z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> P))).
Hypothesis H21: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 < y2 -> u2 < z2 -> (z2 * w2 + u2 * y2) < z2 * y2 + u2 * w2).
Hypothesis H22: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 <= y2 -> u2 <= z2 -> (z2 * w2 + u2 * y2) <= z2 * y2 + u2 * w2).
Hypothesis H23: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (y2 * y) * z = y2 * y * z).
Hypothesis H24: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (x * y2) * z = x * y2 * z).
Theorem Conj_mul_SNo_assoc__5__18: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x * y) * y2 = x * y * y2) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__5__18.
(** Conj_mul_SNo_assoc__5__19 TMNztdDcVGaSPMMX6bKr84ERzSu2b632gx6 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__5__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> x * y * y2 = (x * y) * y2).
Hypothesis H6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> y2 * z2 * z = (y2 * z2) * z)).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H11: SNoCutP w u.
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H13: (forall y2:set, y2 :e u -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H15: SNoCutP v x2.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H18: (x * y) * z = SNoCut v x2.
Hypothesis H20: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoR (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoR z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoL z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> P))).
Hypothesis H21: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 < y2 -> u2 < z2 -> (z2 * w2 + u2 * y2) < z2 * y2 + u2 * w2).
Hypothesis H22: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 <= y2 -> u2 <= z2 -> (z2 * w2 + u2 * y2) <= z2 * y2 + u2 * w2).
Hypothesis H23: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (y2 * y) * z = y2 * y * z).
Hypothesis H24: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (x * y2) * z = x * y2 * z).
Theorem Conj_mul_SNo_assoc__5__19: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x * y) * y2 = x * y * y2) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__5__19.
(** Conj_mul_SNo_assoc__5__23 TMbMicSqa1Uo7gbRjiR5xbf7AUPsvxvfJ1f bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__5__23.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> x * y * y2 = (x * y) * y2).
Hypothesis H6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> y2 * z2 * z = (y2 * z2) * z)).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H11: SNoCutP w u.
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H13: (forall y2:set, y2 :e u -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H15: SNoCutP v x2.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H18: (x * y) * z = SNoCut v x2.
Hypothesis H19: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoL (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoL z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoR z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> P))).
Hypothesis H20: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoR (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoR z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoL z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> P))).
Hypothesis H21: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 < y2 -> u2 < z2 -> (z2 * w2 + u2 * y2) < z2 * y2 + u2 * w2).
Hypothesis H22: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 <= y2 -> u2 <= z2 -> (z2 * w2 + u2 * y2) <= z2 * y2 + u2 * w2).
Hypothesis H24: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (x * y2) * z = x * y2 * z).
Theorem Conj_mul_SNo_assoc__5__23: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x * y) * y2 = x * y * y2) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__5__23.
(** Conj_mul_SNo_assoc__6__20 TMUNaL9yMpQFfhyTtYMgLWL4xc5GGgf2Cud bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__6__20.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> x * y * y2 = (x * y) * y2).
Hypothesis H6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> y2 * z2 * z = (y2 * z2) * z)).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H11: SNoCutP w u.
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H13: (forall y2:set, y2 :e u -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H15: SNoCutP v x2.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H18: (x * y) * z = SNoCut v x2.
Hypothesis H19: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoL (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoL z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoR z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> P))).
Hypothesis H21: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 < y2 -> u2 < z2 -> (z2 * w2 + u2 * y2) < z2 * y2 + u2 * w2).
Hypothesis H22: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 <= y2 -> u2 <= z2 -> (z2 * w2 + u2 * y2) <= z2 * y2 + u2 * w2).
Hypothesis H23: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (y2 * y) * z = y2 * y * z).
Theorem Conj_mul_SNo_assoc__6__20: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (x * y2) * z = x * y2 * z) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__6__20.
(** Conj_mul_SNo_assoc__7__6 TMWH7AsFtkApTcN8EzUYXLVhBhntNeWD3Ky bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__7__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> x * y * y2 = (x * y) * y2).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H11: SNoCutP w u.
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H13: (forall y2:set, y2 :e u -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H15: SNoCutP v x2.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H18: (x * y) * z = SNoCut v x2.
Hypothesis H19: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoL (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoL z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoR z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> P))).
Hypothesis H20: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoR (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoR z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoL z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> P))).
Hypothesis H21: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 < y2 -> u2 < z2 -> (z2 * w2 + u2 * y2) < z2 * y2 + u2 * w2).
Hypothesis H22: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 <= y2 -> u2 <= z2 -> (z2 * w2 + u2 * y2) <= z2 * y2 + u2 * w2).
Theorem Conj_mul_SNo_assoc__7__6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (y2 * y) * z = y2 * y * z) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__7__6.
(** Conj_mul_SNo_assoc__9__0 TMMrsfdC6Ecnmmc13uAWMra4X6T2amXWdz5 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__9__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> x * y * y2 = (x * y) * y2).
Hypothesis H6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> y2 * z2 * z = (y2 * z2) * z)).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H11: SNoCutP w u.
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H13: (forall y2:set, y2 :e u -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H15: SNoCutP v x2.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H18: (x * y) * z = SNoCut v x2.
Hypothesis H19: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoL (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoL z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoR z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> P))).
Hypothesis H20: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoR (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoR z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoL z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> P))).
Theorem Conj_mul_SNo_assoc__9__0: (forall y2:set, forall z2:set, forall w2:set, forall u2:set, SNo y2 -> SNo z2 -> SNo w2 -> SNo u2 -> w2 < y2 -> u2 < z2 -> (z2 * w2 + u2 * y2) < z2 * y2 + u2 * w2) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__9__0.
(** Conj_mul_SNo_assoc__10__13 TMQkYpM9GqnCKrvVJi2ANVvjjpPYJ69YWgB bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__10__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> x * y * y2 = (x * y) * y2).
Hypothesis H6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> y2 * z2 * z = (y2 * z2) * z)).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H11: SNoCutP w u.
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H15: SNoCutP v x2.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H18: (x * y) * z = SNoCut v x2.
Hypothesis H19: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoL (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoL z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoR z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> P))).
Theorem Conj_mul_SNo_assoc__10__13: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoR (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoR z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoL z2 -> (z2 * u2 + v2 * y2) <= w2 + v2 * u2 -> P)) -> P))) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__10__13.
(** Conj_mul_SNo_assoc__11__11 TMRopZCqC2UzTt1mCdi3YVQyXXXjLVBzuPP bounty of about 25 bars **)
Section Conj_mul_SNo_assoc__11__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> y2 * y * z = (y2 * y) * z).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x * y2 * z = (x * y2) * z).
Hypothesis H5: (forall y2:set, y2 :e SNoS_ (SNoLev z) -> x * y * y2 = (x * y) * y2).
Hypothesis H6: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> y2 * z2 * z = (y2 * z2) * z)).
Hypothesis H7: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> y2 * y * z2 = (y2 * y) * z2)).
Hypothesis H8: (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> x * y2 * z2 = (x * y2) * z2)).
Hypothesis H9: (forall y2:set, y2 :e SNoS_ (SNoLev x) -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> y2 * z2 * w2 = (y2 * z2) * w2))).
Hypothesis H10: SNo (x * y).
Hypothesis H12: (forall y2:set, y2 :e w -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H13: (forall y2:set, y2 :e u -> (forall P:prop, (forall z2:set, z2 :e SNoL x -> (forall w2:set, w2 :e SNoR (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR x -> (forall w2:set, w2 :e SNoL (y * z) -> y2 = z2 * y * z + x * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H14: x * y * z = SNoCut w u.
Hypothesis H15: SNoCutP v x2.
Hypothesis H16: (forall y2:set, y2 :e v -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H17: (forall y2:set, y2 :e x2 -> (forall P:prop, (forall z2:set, z2 :e SNoL (x * y) -> (forall w2:set, w2 :e SNoR z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> (forall z2:set, z2 :e SNoR (x * y) -> (forall w2:set, w2 :e SNoL z -> y2 = z2 * z + (x * y) * w2 + - (z2 * w2) -> P)) -> P)).
Hypothesis H18: (x * y) * z = SNoCut v x2.
Theorem Conj_mul_SNo_assoc__11__11: (forall y2:set, forall z2:set, SNo y2 -> SNo z2 -> (forall w2:set, w2 :e SNoL (z2 * y2) -> (forall P:prop, (forall u2:set, u2 :e SNoL y2 -> (forall v2:set, v2 :e SNoL z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> (forall u2:set, u2 :e SNoR y2 -> (forall v2:set, v2 :e SNoR z2 -> (w2 + v2 * u2) <= z2 * u2 + v2 * y2 -> P)) -> P))) -> SNoCut w u = SNoCut v x2.
Admitted.

End Conj_mul_SNo_assoc__11__11.
(** Conj_nonneg_mul_SNo_Le__1__2 TMGjsorauqZGxDnLx5NCzWFx3XxQR3FrwLZ bounty of about 25 bars **)
Section Conj_nonneg_mul_SNo_Le__1__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: Empty <= x.
Hypothesis H3: SNo z.
Hypothesis H4: y <= z.
Hypothesis H5: Empty * z + x * y = x * y.
Theorem Conj_nonneg_mul_SNo_Le__1__2: x * z + Empty * y = x * z -> x * y <= x * z.
Admitted.

End Conj_nonneg_mul_SNo_Le__1__2.
(** Conj_neg_mul_SNo_Lt__1__3 TMQYrmVJstqALQKER1bHkUVBt6XMTuEMYVk bounty of about 25 bars **)
Section Conj_neg_mul_SNo_Lt__1__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: x < Empty.
Hypothesis H2: SNo y.
Hypothesis H4: z < y.
Hypothesis H5: x * y + Empty * z = x * y.
Theorem Conj_neg_mul_SNo_Lt__1__3: Empty * y + x * z = x * z -> x * y < x * z.
Admitted.

End Conj_neg_mul_SNo_Lt__1__3.
(** Conj_neg_mul_SNo_Lt__2__0 TMQuAriBkzHzjXJUFnKvjvGhYrnszCs6Wf1 bounty of about 25 bars **)
Section Conj_neg_mul_SNo_Lt__2__0.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H1: x < Empty.
Hypothesis H2: SNo y.
Hypothesis H3: SNo z.
Hypothesis H4: z < y.
Theorem Conj_neg_mul_SNo_Lt__2__0: x * y + Empty * z = x * y -> x * y < x * z.
Admitted.

End Conj_neg_mul_SNo_Lt__2__0.
(** Conj_SNo_foil_mm__1__1 TMaW8BBqSXjX9KmK5wAmbVfzkxNknuatzyX bounty of about 25 bars **)
Section Conj_SNo_foil_mm__1__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: SNo (- y).
Theorem Conj_SNo_foil_mm__1__1: SNo (- w) -> (x + - y) * (z + - w) = x * z + - (x * w) + - (y * z) + y * w.
Admitted.

End Conj_SNo_foil_mm__1__1.
(** Conj_SNo_foil_mm__2__0 TMaK8SfLjZuPR25H9cpASD1XaMLmrzPeQDc bounty of about 25 bars **)
Section Conj_SNo_foil_mm__2__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Theorem Conj_SNo_foil_mm__2__0: SNo (- y) -> (x + - y) * (z + - w) = x * z + - (x * w) + - (y * z) + y * w.
Admitted.

End Conj_SNo_foil_mm__2__0.
(** Conj_eps_ordsucc_half_add__7__0 TMJb5N2jfvVFzbeYQ6r75deVvFdQFo1Qypx bounty of about 25 bars **)
Section Conj_eps_ordsucc_half_add__7__0.
Variable x:set.
Variable y:set.
Hypothesis H1: x :e omega.
Hypothesis H2: SNo (eps_ (ordsucc x)).
Hypothesis H3: SNo y.
Hypothesis H4: SNoLev y :e ordsucc (ordsucc x).
Hypothesis H5: y < eps_ (ordsucc x).
Theorem Conj_eps_ordsucc_half_add__7__0: y <= Empty -> (y + eps_ (ordsucc x)) < eps_ x /\ (eps_ (ordsucc x) + y) < eps_ x.
Admitted.

End Conj_eps_ordsucc_half_add__7__0.
(** Conj_eps_ordsucc_half_add__7__1 TMW7rp3z3vveRW15DuHC5HQbXg6EiCzmAAW bounty of about 25 bars **)
Section Conj_eps_ordsucc_half_add__7__1.
Variable x:set.
Variable y:set.
Hypothesis H0: nat_p x.
Hypothesis H2: SNo (eps_ (ordsucc x)).
Hypothesis H3: SNo y.
Hypothesis H4: SNoLev y :e ordsucc (ordsucc x).
Hypothesis H5: y < eps_ (ordsucc x).
Theorem Conj_eps_ordsucc_half_add__7__1: y <= Empty -> (y + eps_ (ordsucc x)) < eps_ x /\ (eps_ (ordsucc x) + y) < eps_ x.
Admitted.

End Conj_eps_ordsucc_half_add__7__1.
(** Conj_eps_ordsucc_half_add__11__1 TMahqJLBEpHsK9f9TGcEDFnXXjWDWeTQuhJ bounty of about 25 bars **)
Section Conj_eps_ordsucc_half_add__11__1.
Variable x:set.
Hypothesis H0: nat_p x.
Theorem Conj_eps_ordsucc_half_add__11__1: x :e omega -> eps_ (ordsucc x) + eps_ (ordsucc x) = eps_ x.
Admitted.

End Conj_eps_ordsucc_half_add__11__1.
(** Conj_double_eps_1__1__1 TMVZyUnQoZ91cmJhoJwV56N6UVUMW2JWgPE bounty of about 25 bars **)
Section Conj_double_eps_1__1__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: x + x = y + z.
Theorem Conj_double_eps_1__1__1: SNo (y + z) -> x = eps_ (ordsucc Empty) * (y + z).
Admitted.

End Conj_double_eps_1__1__1.
(** Conj_exp_SNo_1_bd__1__1 TMN8o59sZ5Twx4D5Kz4PctF7qpkiRee7boh bounty of about 25 bars **)
Section Conj_exp_SNo_1_bd__1__1.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H2: nat_p y.
Hypothesis H3: ordsucc Empty <= exp_SNo_nat x y.
Theorem Conj_exp_SNo_1_bd__1__1: SNo (exp_SNo_nat x y) -> ordsucc Empty <= exp_SNo_nat x (ordsucc y).
Admitted.

End Conj_exp_SNo_1_bd__1__1.
(** Conj_mul_SNo_eps_eps_add_SNo__5__0 TMKoaaH7VK9hZvbaEJDT5pusMejBDhJJmaS bounty of about 25 bars **)
Section Conj_mul_SNo_eps_eps_add_SNo__5__0.
Variable x:set.
Variable y:set.
Hypothesis H1: y :e omega.
Hypothesis H2: x + y :e omega.
Hypothesis H3: nat_p (x + y).
Hypothesis H4: SNo (eps_ x).
Theorem Conj_mul_SNo_eps_eps_add_SNo__5__0: SNo (eps_ y) -> eps_ x * eps_ y = eps_ (x + y).
Admitted.

End Conj_mul_SNo_eps_eps_add_SNo__5__0.
(** Conj_mul_SNo_eps_eps_add_SNo__8__0 TMFzVzKiacct23f44X1LXmF5ChpVSdiggCF bounty of about 25 bars **)
Section Conj_mul_SNo_eps_eps_add_SNo__8__0.
Variable x:set.
Variable y:set.
Hypothesis H1: y :e omega.
Theorem Conj_mul_SNo_eps_eps_add_SNo__8__0: x + y :e omega -> eps_ x * eps_ y = eps_ (x + y).
Admitted.

End Conj_mul_SNo_eps_eps_add_SNo__8__0.
(** Conj_SNoS_omega_Lev_equip__9__0 TMG1KMpBBNaaizgKcjtixYkiVWrSygoDhCN bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__9__0.
Variable x:set.
Variable f:(set -> set).
Variable f2:(set -> set).
Variable y:set.
Variable z:set.
Hypothesis H1: (forall w:set, x :e w -> f2 w = f (binintersect w (SNoElts_ x))).
Hypothesis H2: f z = y.
Hypothesis H3: SNoLev z = x.
Hypothesis H4: SNo z.
Hypothesis H5: SNoLev (SNo_extend1 z) = ordsucc x.
Theorem Conj_SNoS_omega_Lev_equip__9__0: x :e SNo_extend1 z -> (exists w:set, w :e Sep (SNoS_ omega) (fun u:set => SNoLev u = ordsucc x) /\ f2 w = y).
Admitted.

End Conj_SNoS_omega_Lev_equip__9__0.
(** Conj_SNoS_omega_Lev_equip__9__1 TMZ43Wjbdf6opM763pZyvVW4PMWiQ9pdxQQ bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__9__1.
Variable x:set.
Variable f:(set -> set).
Variable f2:(set -> set).
Variable y:set.
Variable z:set.
Hypothesis H0: nat_p x.
Hypothesis H2: f z = y.
Hypothesis H3: SNoLev z = x.
Hypothesis H4: SNo z.
Hypothesis H5: SNoLev (SNo_extend1 z) = ordsucc x.
Theorem Conj_SNoS_omega_Lev_equip__9__1: x :e SNo_extend1 z -> (exists w:set, w :e Sep (SNoS_ omega) (fun u:set => SNoLev u = ordsucc x) /\ f2 w = y).
Admitted.

End Conj_SNoS_omega_Lev_equip__9__1.
(** Conj_SNoS_omega_Lev_equip__13__7 TMWUqrVPWYxKfk53cR1PDhFuwKVQETiy8Aq bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__13__7.
Variable x:set.
Variable f:(set -> set).
Variable f2:(set -> set).
Variable y:set.
Hypothesis H0: nat_p x.
Hypothesis H1: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H2: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H3: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H4: (forall z:set, z :e exp_SNo_nat (ordsucc (ordsucc Empty)) x -> (exists w:set, w :e Sep (SNoS_ omega) (fun u:set => SNoLev u = x) /\ f w = z)).
Hypothesis H5: (forall z:set, x :e z -> f2 z = f (binintersect z (SNoElts_ x))).
Hypothesis H6: (forall z:set, nIn x z -> f2 z = exp_SNo_nat (ordsucc (ordsucc Empty)) x + f (binintersect z (SNoElts_ x))).
Theorem Conj_SNoS_omega_Lev_equip__13__7: nat_p y -> (exists z:set, z :e Sep (SNoS_ omega) (fun w:set => SNoLev w = ordsucc x) /\ f2 z = y).
Admitted.

End Conj_SNoS_omega_Lev_equip__13__7.
(** Conj_SNoS_omega_Lev_equip__16__1 TMHRRgFXkDjLdVTJV7gdBgWYzLCBrp6Ehyj bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__16__1.
Variable x:set.
Variable f:(set -> set).
Variable f2:(set -> set).
Variable y:set.
Variable z:set.
Hypothesis H0: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H2: (forall w:set, x :e w -> f2 w = f (binintersect w (SNoElts_ x))).
Hypothesis H3: (forall w:set, nIn x w -> f2 w = exp_SNo_nat (ordsucc (ordsucc Empty)) x + f (binintersect w (SNoElts_ x))).
Hypothesis H4: SNo y.
Hypothesis H5: SNoLev y = ordsucc x.
Hypothesis H6: binintersect y (SNoElts_ x) :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x).
Hypothesis H7: nat_p (f (binintersect y (SNoElts_ x))).
Hypothesis H8: SNo (f (binintersect y (SNoElts_ x))).
Hypothesis H9: f (binintersect y (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Hypothesis H10: SNo z.
Hypothesis H11: SNoLev z = ordsucc x.
Hypothesis H12: binintersect z (SNoElts_ x) :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x).
Hypothesis H13: nat_p (f (binintersect z (SNoElts_ x))).
Hypothesis H14: SNo (f (binintersect z (SNoElts_ x))).
Hypothesis H15: f (binintersect z (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Hypothesis H16: x :e SNoLev y.
Theorem Conj_SNoS_omega_Lev_equip__16__1: x :e SNoLev z -> f2 y = f2 z -> y = z.
Admitted.

End Conj_SNoS_omega_Lev_equip__16__1.
(** Conj_SNoS_omega_Lev_equip__16__4 TMK9XmRHcc5LWNQNgymtMPERAYJ6SLKNqLB bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__16__4.
Variable x:set.
Variable f:(set -> set).
Variable f2:(set -> set).
Variable y:set.
Variable z:set.
Hypothesis H0: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H1: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => SNoLev u = x) -> (forall u:set, u :e Sep (SNoS_ omega) (fun v:set => SNoLev v = x) -> f w = f u -> w = u)).
Hypothesis H2: (forall w:set, x :e w -> f2 w = f (binintersect w (SNoElts_ x))).
Hypothesis H3: (forall w:set, nIn x w -> f2 w = exp_SNo_nat (ordsucc (ordsucc Empty)) x + f (binintersect w (SNoElts_ x))).
Hypothesis H5: SNoLev y = ordsucc x.
Hypothesis H6: binintersect y (SNoElts_ x) :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x).
Hypothesis H7: nat_p (f (binintersect y (SNoElts_ x))).
Hypothesis H8: SNo (f (binintersect y (SNoElts_ x))).
Hypothesis H9: f (binintersect y (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Hypothesis H10: SNo z.
Hypothesis H11: SNoLev z = ordsucc x.
Hypothesis H12: binintersect z (SNoElts_ x) :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x).
Hypothesis H13: nat_p (f (binintersect z (SNoElts_ x))).
Hypothesis H14: SNo (f (binintersect z (SNoElts_ x))).
Hypothesis H15: f (binintersect z (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Hypothesis H16: x :e SNoLev y.
Theorem Conj_SNoS_omega_Lev_equip__16__4: x :e SNoLev z -> f2 y = f2 z -> y = z.
Admitted.

End Conj_SNoS_omega_Lev_equip__16__4.
(** Conj_SNoS_omega_Lev_equip__16__6 TMKmR8LzxLFHc2vi3R6hxPCwXhBiKHXquGw bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__16__6.
Variable x:set.
Variable f:(set -> set).
Variable f2:(set -> set).
Variable y:set.
Variable z:set.
Hypothesis H0: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H1: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => SNoLev u = x) -> (forall u:set, u :e Sep (SNoS_ omega) (fun v:set => SNoLev v = x) -> f w = f u -> w = u)).
Hypothesis H2: (forall w:set, x :e w -> f2 w = f (binintersect w (SNoElts_ x))).
Hypothesis H3: (forall w:set, nIn x w -> f2 w = exp_SNo_nat (ordsucc (ordsucc Empty)) x + f (binintersect w (SNoElts_ x))).
Hypothesis H4: SNo y.
Hypothesis H5: SNoLev y = ordsucc x.
Hypothesis H7: nat_p (f (binintersect y (SNoElts_ x))).
Hypothesis H8: SNo (f (binintersect y (SNoElts_ x))).
Hypothesis H9: f (binintersect y (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Hypothesis H10: SNo z.
Hypothesis H11: SNoLev z = ordsucc x.
Hypothesis H12: binintersect z (SNoElts_ x) :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x).
Hypothesis H13: nat_p (f (binintersect z (SNoElts_ x))).
Hypothesis H14: SNo (f (binintersect z (SNoElts_ x))).
Hypothesis H15: f (binintersect z (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Hypothesis H16: x :e SNoLev y.
Theorem Conj_SNoS_omega_Lev_equip__16__6: x :e SNoLev z -> f2 y = f2 z -> y = z.
Admitted.

End Conj_SNoS_omega_Lev_equip__16__6.
(** Conj_SNoS_omega_Lev_equip__17__14 TMFXYCzERqRqqzAiHctBqYKnhwPEiCRfkRV bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__17__14.
Variable x:set.
Variable f:(set -> set).
Variable f2:(set -> set).
Variable y:set.
Variable z:set.
Hypothesis H0: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H1: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => SNoLev u = x) -> (forall u:set, u :e Sep (SNoS_ omega) (fun v:set => SNoLev v = x) -> f w = f u -> w = u)).
Hypothesis H2: (forall w:set, x :e w -> f2 w = f (binintersect w (SNoElts_ x))).
Hypothesis H3: (forall w:set, nIn x w -> f2 w = exp_SNo_nat (ordsucc (ordsucc Empty)) x + f (binintersect w (SNoElts_ x))).
Hypothesis H4: SNo y.
Hypothesis H5: SNoLev y = ordsucc x.
Hypothesis H6: binintersect y (SNoElts_ x) :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x).
Hypothesis H7: nat_p (f (binintersect y (SNoElts_ x))).
Hypothesis H8: SNo (f (binintersect y (SNoElts_ x))).
Hypothesis H9: f (binintersect y (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Hypothesis H10: SNo z.
Hypothesis H11: SNoLev z = ordsucc x.
Hypothesis H12: binintersect z (SNoElts_ x) :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x).
Hypothesis H13: nat_p (f (binintersect z (SNoElts_ x))).
Hypothesis H15: f (binintersect z (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Theorem Conj_SNoS_omega_Lev_equip__17__14: x :e SNoLev y -> f2 y = f2 z -> y = z.
Admitted.

End Conj_SNoS_omega_Lev_equip__17__14.
(** Conj_SNoS_omega_Lev_equip__18__0 TMTqn1mJ5us4t33BrhY11rQJ9Ufr6SiRkwf bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__18__0.
Variable x:set.
Variable f:(set -> set).
Hypothesis H1: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H2: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H3: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H4: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H5: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H6: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H7: (forall y:set, SNo y -> y < exp_SNo_nat (ordsucc (ordsucc Empty)) x -> (exp_SNo_nat (ordsucc (ordsucc Empty)) x + y) < exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H8: exp_SNo_nat (ordsucc (ordsucc Empty)) x < exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Hypothesis H9: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => SNoLev z = x) -> (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x) -> f y = f z -> y = z)).
Hypothesis H10: (forall y:set, y :e exp_SNo_nat (ordsucc (ordsucc Empty)) x -> (exists z:set, z :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x) /\ f z = y)).
Hypothesis H11: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => SNoLev z = ordsucc x) -> (forall P:prop, (SNo y -> SNoLev y = ordsucc x -> binintersect y (SNoElts_ x) :e Sep (SNoS_ omega) (fun z:set => SNoLev z = x) -> SNo (binintersect y (SNoElts_ x)) -> SNoLev (binintersect y (SNoElts_ x)) = x -> P) -> P)).
Hypothesis H12: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => SNoLev z = ordsucc x) -> (forall P:prop, (nat_p (f (binintersect y (SNoElts_ x))) -> ordinal (f (binintersect y (SNoElts_ x))) -> SNo (f (binintersect y (SNoElts_ x))) -> f (binintersect y (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x -> P) -> P)).
Theorem Conj_SNoS_omega_Lev_equip__18__0: (exists f2:set -> set, (forall y:set, x :e y -> f2 y = f (binintersect y (SNoElts_ x))) /\ (forall y:set, nIn x y -> f2 y = exp_SNo_nat (ordsucc (ordsucc Empty)) x + f (binintersect y (SNoElts_ x)))) -> (exists f2:set -> set, bij (Sep (SNoS_ omega) (fun y:set => SNoLev y = ordsucc x)) (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x) f2).
Admitted.

End Conj_SNoS_omega_Lev_equip__18__0.
(** Conj_SNoS_omega_Lev_equip__18__3 TMFuqnSfwmRA9e6CivrUJRN2ZiuA1zNDFAL bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__18__3.
Variable x:set.
Variable f:(set -> set).
Hypothesis H0: nat_p x.
Hypothesis H1: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H2: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H4: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H5: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H6: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H7: (forall y:set, SNo y -> y < exp_SNo_nat (ordsucc (ordsucc Empty)) x -> (exp_SNo_nat (ordsucc (ordsucc Empty)) x + y) < exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H8: exp_SNo_nat (ordsucc (ordsucc Empty)) x < exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Hypothesis H9: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => SNoLev z = x) -> (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x) -> f y = f z -> y = z)).
Hypothesis H10: (forall y:set, y :e exp_SNo_nat (ordsucc (ordsucc Empty)) x -> (exists z:set, z :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x) /\ f z = y)).
Hypothesis H11: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => SNoLev z = ordsucc x) -> (forall P:prop, (SNo y -> SNoLev y = ordsucc x -> binintersect y (SNoElts_ x) :e Sep (SNoS_ omega) (fun z:set => SNoLev z = x) -> SNo (binintersect y (SNoElts_ x)) -> SNoLev (binintersect y (SNoElts_ x)) = x -> P) -> P)).
Hypothesis H12: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => SNoLev z = ordsucc x) -> (forall P:prop, (nat_p (f (binintersect y (SNoElts_ x))) -> ordinal (f (binintersect y (SNoElts_ x))) -> SNo (f (binintersect y (SNoElts_ x))) -> f (binintersect y (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x -> P) -> P)).
Theorem Conj_SNoS_omega_Lev_equip__18__3: (exists f2:set -> set, (forall y:set, x :e y -> f2 y = f (binintersect y (SNoElts_ x))) /\ (forall y:set, nIn x y -> f2 y = exp_SNo_nat (ordsucc (ordsucc Empty)) x + f (binintersect y (SNoElts_ x)))) -> (exists f2:set -> set, bij (Sep (SNoS_ omega) (fun y:set => SNoLev y = ordsucc x)) (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x) f2).
Admitted.

End Conj_SNoS_omega_Lev_equip__18__3.
(** Conj_SNoS_omega_Lev_equip__18__6 TMb7s34n5EcAcXeNvjtjLjFMEDPVoMYjU13 bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__18__6.
Variable x:set.
Variable f:(set -> set).
Hypothesis H0: nat_p x.
Hypothesis H1: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H2: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H3: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H4: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H5: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H7: (forall y:set, SNo y -> y < exp_SNo_nat (ordsucc (ordsucc Empty)) x -> (exp_SNo_nat (ordsucc (ordsucc Empty)) x + y) < exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H8: exp_SNo_nat (ordsucc (ordsucc Empty)) x < exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x.
Hypothesis H9: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => SNoLev z = x) -> (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x) -> f y = f z -> y = z)).
Hypothesis H10: (forall y:set, y :e exp_SNo_nat (ordsucc (ordsucc Empty)) x -> (exists z:set, z :e Sep (SNoS_ omega) (fun w:set => SNoLev w = x) /\ f z = y)).
Hypothesis H11: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => SNoLev z = ordsucc x) -> (forall P:prop, (SNo y -> SNoLev y = ordsucc x -> binintersect y (SNoElts_ x) :e Sep (SNoS_ omega) (fun z:set => SNoLev z = x) -> SNo (binintersect y (SNoElts_ x)) -> SNoLev (binintersect y (SNoElts_ x)) = x -> P) -> P)).
Hypothesis H12: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => SNoLev z = ordsucc x) -> (forall P:prop, (nat_p (f (binintersect y (SNoElts_ x))) -> ordinal (f (binintersect y (SNoElts_ x))) -> SNo (f (binintersect y (SNoElts_ x))) -> f (binintersect y (SNoElts_ x)) < exp_SNo_nat (ordsucc (ordsucc Empty)) x -> P) -> P)).
Theorem Conj_SNoS_omega_Lev_equip__18__6: (exists f2:set -> set, (forall y:set, x :e y -> f2 y = f (binintersect y (SNoElts_ x))) /\ (forall y:set, nIn x y -> f2 y = exp_SNo_nat (ordsucc (ordsucc Empty)) x + f (binintersect y (SNoElts_ x)))) -> (exists f2:set -> set, bij (Sep (SNoS_ omega) (fun y:set => SNoLev y = ordsucc x)) (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x) f2).
Admitted.

End Conj_SNoS_omega_Lev_equip__18__6.
(** Conj_SNoS_omega_Lev_equip__22__1 TMbCvbPwp2FHpwPLDi6PGgLkykMDv6mpwkf bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__22__1.
Variable x:set.
Hypothesis H0: nat_p x.
Hypothesis H2: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H3: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H4: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H5: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H6: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H7: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Theorem Conj_SNoS_omega_Lev_equip__22__1: (forall y:set, SNo y -> y < exp_SNo_nat (ordsucc (ordsucc Empty)) x -> (exp_SNo_nat (ordsucc (ordsucc Empty)) x + y) < exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x) -> equip (Sep (SNoS_ omega) (fun y:set => SNoLev y = ordsucc x)) (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Admitted.

End Conj_SNoS_omega_Lev_equip__22__1.
(** Conj_SNoS_omega_Lev_equip__22__4 TMX9cVQboUEkonQDqDTa96BnZyBLSe2y3hr bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__22__4.
Variable x:set.
Hypothesis H0: nat_p x.
Hypothesis H1: equip (Sep (SNoS_ omega) (fun y:set => SNoLev y = x)) (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H2: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H3: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H5: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H6: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H7: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Theorem Conj_SNoS_omega_Lev_equip__22__4: (forall y:set, SNo y -> y < exp_SNo_nat (ordsucc (ordsucc Empty)) x -> (exp_SNo_nat (ordsucc (ordsucc Empty)) x + y) < exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x) -> equip (Sep (SNoS_ omega) (fun y:set => SNoLev y = ordsucc x)) (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Admitted.

End Conj_SNoS_omega_Lev_equip__22__4.
(** Conj_SNoS_omega_Lev_equip__24__5 TMGzrd2L5pFtAh1bvZmqPG45HaLvWYfdbMi bounty of about 25 bars **)
Section Conj_SNoS_omega_Lev_equip__24__5.
Variable x:set.
Hypothesis H0: nat_p x.
Hypothesis H1: equip (Sep (SNoS_ omega) (fun y:set => SNoLev y = x)) (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H2: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H3: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Hypothesis H4: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Theorem Conj_SNoS_omega_Lev_equip__24__5: ordinal (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x) -> equip (Sep (SNoS_ omega) (fun y:set => SNoLev y = ordsucc x)) (exp_SNo_nat (ordsucc (ordsucc Empty)) x + exp_SNo_nat (ordsucc (ordsucc Empty)) x).
Admitted.

End Conj_SNoS_omega_Lev_equip__24__5.
(** Conj_int_add_SNo__1__1 TMKXdnndWzphwh27gBanBBbCiKsrkD3NNJS bounty of about 25 bars **)
Section Conj_int_add_SNo__1__1.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e omega.
Hypothesis H2: SNo x.
Theorem Conj_int_add_SNo__1__1: SNo y -> - x + - y :e int.
Admitted.

End Conj_int_add_SNo__1__1.
(** Conj_int_mul_SNo__3__2 TMKLzQZv7tetX9ynJbWSocrRgmXDh9JCEBo bounty of about 25 bars **)
Section Conj_int_mul_SNo__3__2.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e omega.
Hypothesis H1: SNo x.
Theorem Conj_int_mul_SNo__3__2: nat_p y -> (- x) * (- y) :e int.
Admitted.

End Conj_int_mul_SNo__3__2.
(** Conj_int_mul_SNo__10__2 TMT5DAmPEb4avysJVsgfnV7iERVYNbhZHmz bounty of about 25 bars **)
Section Conj_int_mul_SNo__10__2.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e omega.
Hypothesis H1: SNo x.
Hypothesis H3: ordinal y.
Theorem Conj_int_mul_SNo__10__2: SNo y -> x * (- y) :e int.
Admitted.

End Conj_int_mul_SNo__10__2.
(** Conj_SNo_triangle2__2__0 TMVycYNJ7jNg6EL94FLXgfKSZ4XDHoiNVvn bounty of about 25 bars **)
Section Conj_SNo_triangle2__2__0.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo (- y).
Theorem Conj_SNo_triangle2__2__0: SNo (- z) -> abs_SNo (x + - z) <= abs_SNo (x + - y) + abs_SNo (y + - z).
Admitted.

End Conj_SNo_triangle2__2__0.
(** Conj_double_SNo_max_1__1__6 TMZPPjfSoNYFqfCdsNA9tXEqcv7W6qY9vUm bounty of about 25 bars **)
Section Conj_double_SNo_max_1__1__6.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall w:set, w :e SNoL x -> SNo w -> w <= y).
Hypothesis H3: SNoLev y :e SNoLev x.
Hypothesis H4: SNo z.
Hypothesis H5: SNoLev z :e SNoLev y.
Hypothesis H7: z < x.
Theorem Conj_double_SNo_max_1__1__6: z :e SNoL x -> x <= z.
Admitted.

End Conj_double_SNo_max_1__1__6.
(** Conj_double_SNo_max_1__2__2 TMVXxdnLVVAoJGMcYJ7Jzr1zVbL8oRqhwLw bounty of about 25 bars **)
Section Conj_double_SNo_max_1__2__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo z.
Hypothesis H3: x < z.
Hypothesis H4: w :e SNoR z.
Hypothesis H5: (y + w) < x + x.
Hypothesis H6: SNo w.
Hypothesis H7: SNoLev w :e SNoLev z.
Hypothesis H8: z < w.
Theorem Conj_double_SNo_max_1__2__2: (exists u:set, u :e SNoR w /\ y + u = x + x) -> (exists u:set, u :e SNoR z /\ y + u = x + x).
Admitted.

End Conj_double_SNo_max_1__2__2.
(** Conj_double_SNo_min_1__5__1 TMSyUoeoMqqKNLxkEMukT3vhRJnwTb8aeAP bounty of about 25 bars **)
Section Conj_double_SNo_min_1__5__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo z.
Hypothesis H4: z < x.
Hypothesis H5: (x + x) < y + z.
Hypothesis H6: SNo (- x).
Hypothesis H7: SNo (- y).
Hypothesis H8: SNo (- z).
Hypothesis H9: SNo (x + x).
Theorem Conj_double_SNo_min_1__5__1: SNo (y + z) -> (exists w:set, w :e SNoL z /\ y + w = x + x).
Admitted.

End Conj_double_SNo_min_1__5__1.
(** Conj_double_SNo_min_1__5__5 TMdAnCS2pcYxFsvXwBUiWkWREPawhPn472r bounty of about 25 bars **)
Section Conj_double_SNo_min_1__5__5.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo_min_of (SNoR x) y.
Hypothesis H2: SNo y.
Hypothesis H3: SNo z.
Hypothesis H4: z < x.
Hypothesis H6: SNo (- x).
Hypothesis H7: SNo (- y).
Hypothesis H8: SNo (- z).
Hypothesis H9: SNo (x + x).
Theorem Conj_double_SNo_min_1__5__5: SNo (y + z) -> (exists w:set, w :e SNoL z /\ y + w = x + x).
Admitted.

End Conj_double_SNo_min_1__5__5.
(** Conj_double_SNo_min_1__5__6 TMXudoMGdEhm5rdPuCb6JxQ3V1RvK6b3y58 bounty of about 25 bars **)
Section Conj_double_SNo_min_1__5__6.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo_min_of (SNoR x) y.
Hypothesis H2: SNo y.
Hypothesis H3: SNo z.
Hypothesis H4: z < x.
Hypothesis H5: (x + x) < y + z.
Hypothesis H7: SNo (- y).
Hypothesis H8: SNo (- z).
Hypothesis H9: SNo (x + x).
Theorem Conj_double_SNo_min_1__5__6: SNo (y + z) -> (exists w:set, w :e SNoL z /\ y + w = x + x).
Admitted.

End Conj_double_SNo_min_1__5__6.
(** Conj_double_SNo_min_1__5__9 TMbkDCJzS7Y61htx9xAZn22zkqtvqwNqRhh bounty of about 25 bars **)
Section Conj_double_SNo_min_1__5__9.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo_min_of (SNoR x) y.
Hypothesis H2: SNo y.
Hypothesis H3: SNo z.
Hypothesis H4: z < x.
Hypothesis H5: (x + x) < y + z.
Hypothesis H6: SNo (- x).
Hypothesis H7: SNo (- y).
Hypothesis H8: SNo (- z).
Theorem Conj_double_SNo_min_1__5__9: SNo (y + z) -> (exists w:set, w :e SNoL z /\ y + w = x + x).
Admitted.

End Conj_double_SNo_min_1__5__9.
(** Conj_double_SNo_min_1__7__1 TMPqQUwKPm1Pn9YnUN5fkbwQBCGdRbzAk3Y bounty of about 25 bars **)
Section Conj_double_SNo_min_1__7__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo z.
Hypothesis H4: z < x.
Hypothesis H5: (x + x) < y + z.
Hypothesis H6: SNo (- x).
Hypothesis H7: SNo (- y).
Theorem Conj_double_SNo_min_1__7__1: SNo (- z) -> (exists w:set, w :e SNoL z /\ y + w = x + x).
Admitted.

End Conj_double_SNo_min_1__7__1.
(** Conj_finite_max_exists__3__1 TMKFqbw3kax2YeVnPNwjr7GebiYjLjbwXJT bounty of about 25 bars **)
Section Conj_finite_max_exists__3__1.
Variable x:set.
Variable y:set.
Variable f:(set -> set).
Hypothesis H0: (forall z:set, (forall w:set, w :e z -> SNo w) -> equip z (ordsucc x) -> (exists w:set, SNo_max_of z w)).
Hypothesis H2: (forall z:set, z :e ordsucc (ordsucc x) -> f z :e y).
Hypothesis H3: (forall z:set, z :e ordsucc (ordsucc x) -> (forall w:set, w :e ordsucc (ordsucc x) -> f z = f w -> z = w)).
Hypothesis H4: (forall z:set, z :e y -> (exists w:set, w :e ordsucc (ordsucc x) /\ f w = z)).
Hypothesis H5: Subq (Repl (ordsucc x) f) y.
Theorem Conj_finite_max_exists__3__1: equip (Repl (ordsucc x) f) (ordsucc x) -> (exists z:set, SNo_max_of y z).
Admitted.

End Conj_finite_max_exists__3__1.
(** Conj_SNoS_omega_SNoL_max_exists__1__0 TMMwZtwZzq24ogbQh2HpJPu3BXWecQciwYA bounty of about 25 bars **)
Section Conj_SNoS_omega_SNoL_max_exists__1__0.
Variable x:set.
Hypothesis H1: SNoL x <> Empty.
Theorem Conj_SNoS_omega_SNoL_max_exists__1__0: (forall y:set, y :e SNoL x -> SNo y) -> (exists y:set, SNo_max_of (SNoL x) y).
Admitted.

End Conj_SNoS_omega_SNoL_max_exists__1__0.
(** Conj_SNoS_omega_SNoR_min_exists__1__0 TMUvJaTLXjppUiwg1ff7hJFuuqfrnBGEuAo bounty of about 25 bars **)
Section Conj_SNoS_omega_SNoR_min_exists__1__0.
Variable x:set.
Hypothesis H1: SNoR x <> Empty.
Theorem Conj_SNoS_omega_SNoR_min_exists__1__0: (forall y:set, y :e SNoR x -> SNo y) -> (exists y:set, SNo_min_of (SNoR x) y).
Admitted.

End Conj_SNoS_omega_SNoR_min_exists__1__0.
(** Conj_minus_SNo_diadic_rational_p__3__0 TMWSVpsoFVQdr3wEzGzqQmPprFstpFeKZRs bounty of about 25 bars **)
Section Conj_minus_SNo_diadic_rational_p__3__0.
Variable x:set.
Variable y:set.
Theorem Conj_minus_SNo_diadic_rational_p__3__0: SNo (eps_ y) -> (exists z:set, z :e int /\ x = eps_ y * z) -> diadic_rational_p (- x).
Admitted.

End Conj_minus_SNo_diadic_rational_p__3__0.
(** Conj_mul_SNo_diadic_rational_p__1__7 TMZPdyy2iYeBRUmj813vgMVaruTJNRNNUai bounty of about 25 bars **)
Section Conj_mul_SNo_diadic_rational_p__1__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: z :e omega.
Hypothesis H1: SNo (eps_ z).
Hypothesis H2: w :e int.
Hypothesis H3: x = eps_ z * w.
Hypothesis H4: SNo w.
Hypothesis H5: u :e omega.
Hypothesis H6: SNo (eps_ u).
Hypothesis H8: SNo v.
Theorem Conj_mul_SNo_diadic_rational_p__1__7: SNo (eps_ u * v) -> y = eps_ u * v -> (exists x2:set, x2 :e omega /\ (exists y2:set, y2 :e int /\ x * y = eps_ x2 * y2)).
Admitted.

End Conj_mul_SNo_diadic_rational_p__1__7.
(** Conj_mul_SNo_diadic_rational_p__3__2 TMV7CPWxjJBTbrsyZrRPh15spXZb46NKRQ8 bounty of about 25 bars **)
Section Conj_mul_SNo_diadic_rational_p__3__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: z :e omega.
Hypothesis H1: SNo (eps_ z).
Hypothesis H3: x = eps_ z * w.
Hypothesis H4: SNo w.
Hypothesis H5: u :e omega.
Theorem Conj_mul_SNo_diadic_rational_p__3__2: SNo (eps_ u) -> (exists v:set, v :e int /\ y = eps_ u * v) -> diadic_rational_p (x * y).
Admitted.

End Conj_mul_SNo_diadic_rational_p__3__2.
(** Conj_add_SNo_diadic_rational_p__1__8 TMV7au4o5UWBPWULwLsgJgoqFNa7fsVK2PP bounty of about 25 bars **)
Section Conj_add_SNo_diadic_rational_p__1__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: z :e omega.
Hypothesis H1: SNo (eps_ z).
Hypothesis H2: w :e int.
Hypothesis H3: x = eps_ z * w.
Hypothesis H4: u :e omega.
Hypothesis H5: SNo (eps_ u).
Hypothesis H6: v :e int.
Hypothesis H7: y = eps_ u * v.
Hypothesis H9: exp_SNo_nat (ordsucc (ordsucc Empty)) u :e int.
Hypothesis H10: exp_SNo_nat (ordsucc (ordsucc Empty)) u * w :e int.
Hypothesis H11: exp_SNo_nat (ordsucc (ordsucc Empty)) z :e int.
Theorem Conj_add_SNo_diadic_rational_p__1__8: exp_SNo_nat (ordsucc (ordsucc Empty)) z * v :e int -> exp_SNo_nat (ordsucc (ordsucc Empty)) u * w + exp_SNo_nat (ordsucc (ordsucc Empty)) z * v :e int /\ x + y = eps_ (z + u) * (exp_SNo_nat (ordsucc (ordsucc Empty)) u * w + exp_SNo_nat (ordsucc (ordsucc Empty)) z * v).
Admitted.

End Conj_add_SNo_diadic_rational_p__1__8.
(** Conj_add_SNo_diadic_rational_p__1__11 TMF7t8L5f1mERyj3VtKZmbW1k8aSteUSi4c bounty of about 25 bars **)
Section Conj_add_SNo_diadic_rational_p__1__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: z :e omega.
Hypothesis H1: SNo (eps_ z).
Hypothesis H2: w :e int.
Hypothesis H3: x = eps_ z * w.
Hypothesis H4: u :e omega.
Hypothesis H5: SNo (eps_ u).
Hypothesis H6: v :e int.
Hypothesis H7: y = eps_ u * v.
Hypothesis H8: SNo (eps_ u * v).
Hypothesis H9: exp_SNo_nat (ordsucc (ordsucc Empty)) u :e int.
Hypothesis H10: exp_SNo_nat (ordsucc (ordsucc Empty)) u * w :e int.
Theorem Conj_add_SNo_diadic_rational_p__1__11: exp_SNo_nat (ordsucc (ordsucc Empty)) z * v :e int -> exp_SNo_nat (ordsucc (ordsucc Empty)) u * w + exp_SNo_nat (ordsucc (ordsucc Empty)) z * v :e int /\ x + y = eps_ (z + u) * (exp_SNo_nat (ordsucc (ordsucc Empty)) u * w + exp_SNo_nat (ordsucc (ordsucc Empty)) z * v).
Admitted.

End Conj_add_SNo_diadic_rational_p__1__11.
(** Conj_add_SNo_diadic_rational_p__4__0 TMVQZGxMcdDK2HdqW6srTE6PnvWE7RutNY8 bounty of about 25 bars **)
Section Conj_add_SNo_diadic_rational_p__4__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: SNo (eps_ z).
Hypothesis H2: w :e int.
Hypothesis H3: x = eps_ z * w.
Hypothesis H4: u :e omega.
Hypothesis H5: SNo (eps_ u).
Hypothesis H6: v :e int.
Hypothesis H7: y = eps_ u * v.
Hypothesis H8: SNo (eps_ u * v).
Theorem Conj_add_SNo_diadic_rational_p__4__0: exp_SNo_nat (ordsucc (ordsucc Empty)) u :e int -> exp_SNo_nat (ordsucc (ordsucc Empty)) u * w + exp_SNo_nat (ordsucc (ordsucc Empty)) z * v :e int /\ x + y = eps_ (z + u) * (exp_SNo_nat (ordsucc (ordsucc Empty)) u * w + exp_SNo_nat (ordsucc (ordsucc Empty)) z * v).
Admitted.

End Conj_add_SNo_diadic_rational_p__4__0.
(** Conj_add_SNo_diadic_rational_p__4__7 TMJQSBjAjm7vxyCNHT8UK7C3xm6F6X2ZViw bounty of about 25 bars **)
Section Conj_add_SNo_diadic_rational_p__4__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: z :e omega.
Hypothesis H1: SNo (eps_ z).
Hypothesis H2: w :e int.
Hypothesis H3: x = eps_ z * w.
Hypothesis H4: u :e omega.
Hypothesis H5: SNo (eps_ u).
Hypothesis H6: v :e int.
Hypothesis H8: SNo (eps_ u * v).
Theorem Conj_add_SNo_diadic_rational_p__4__7: exp_SNo_nat (ordsucc (ordsucc Empty)) u :e int -> exp_SNo_nat (ordsucc (ordsucc Empty)) u * w + exp_SNo_nat (ordsucc (ordsucc Empty)) z * v :e int /\ x + y = eps_ (z + u) * (exp_SNo_nat (ordsucc (ordsucc Empty)) u * w + exp_SNo_nat (ordsucc (ordsucc Empty)) z * v).
Admitted.

End Conj_add_SNo_diadic_rational_p__4__7.
(** Conj_add_SNo_diadic_rational_p__5__6 TMcSyLcDxLNE2aXkeSJV1cFt1WMD3zE8VRq bounty of about 25 bars **)
Section Conj_add_SNo_diadic_rational_p__5__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: z :e omega.
Hypothesis H1: SNo (eps_ z).
Hypothesis H2: w :e int.
Hypothesis H3: x = eps_ z * w.
Hypothesis H4: u :e omega.
Hypothesis H5: SNo (eps_ u).
Hypothesis H7: y = eps_ u * v.
Hypothesis H8: SNo v.
Theorem Conj_add_SNo_diadic_rational_p__5__6: SNo (eps_ u * v) -> (exists x2:set, x2 :e omega /\ (exists y2:set, y2 :e int /\ x + y = eps_ x2 * y2)).
Admitted.

End Conj_add_SNo_diadic_rational_p__5__6.
(** Conj_add_SNo_diadic_rational_p__5__7 TMLqfYjB4T25CFT6n1vBfEqM7TVqVLGRipj bounty of about 25 bars **)
Section Conj_add_SNo_diadic_rational_p__5__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: z :e omega.
Hypothesis H1: SNo (eps_ z).
Hypothesis H2: w :e int.
Hypothesis H3: x = eps_ z * w.
Hypothesis H4: u :e omega.
Hypothesis H5: SNo (eps_ u).
Hypothesis H6: v :e int.
Hypothesis H8: SNo v.
Theorem Conj_add_SNo_diadic_rational_p__5__7: SNo (eps_ u * v) -> (exists x2:set, x2 :e omega /\ (exists y2:set, y2 :e int /\ x + y = eps_ x2 * y2)).
Admitted.

End Conj_add_SNo_diadic_rational_p__5__7.
(** Conj_add_SNo_diadic_rational_p__7__1 TMH2zbFVvL5Fn9rePTs2NsVfjAQYqPkcdeT bounty of about 25 bars **)
Section Conj_add_SNo_diadic_rational_p__7__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: z :e omega.
Hypothesis H2: w :e int.
Hypothesis H3: x = eps_ z * w.
Hypothesis H4: u :e omega.
Theorem Conj_add_SNo_diadic_rational_p__7__1: SNo (eps_ u) -> (exists v:set, v :e int /\ y = eps_ u * v) -> diadic_rational_p (x + y).
Admitted.

End Conj_add_SNo_diadic_rational_p__7__1.
(** Conj_SNoS_omega_diadic_rational_p_lem__3__1 TMLBMcYi4nnEoz3iCtCGCnSDkvRmMhSJP8W bounty of about 25 bars **)
Section Conj_SNoS_omega_diadic_rational_p_lem__3__1.
Variable x:set.
Variable y:set.
Hypothesis H0: nat_p x.
Hypothesis H2: ~ diadic_rational_p y.
Hypothesis H3: ordinal y.
Theorem Conj_SNoS_omega_diadic_rational_p_lem__3__1: y = x -> (exists z:set, SNo_min_of (SNoR y) z).
Admitted.

End Conj_SNoS_omega_diadic_rational_p_lem__3__1.
(** Conj_SNoS_omega_diadic_rational_p_lem__9__2 TMXzCynKgAxiP9828r6dDAMEsNa733ewRCT bounty of about 25 bars **)
Section Conj_SNoS_omega_diadic_rational_p_lem__9__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: nat_p x.
Hypothesis H1: (forall v:set, v :e x -> (forall x2:set, SNo x2 -> SNoLev x2 = v -> diadic_rational_p x2)).
Hypothesis H3: SNoLev y = x.
Hypothesis H4: ~ diadic_rational_p y.
Hypothesis H5: SNoLev z :e SNoLev y.
Hypothesis H6: SNo w.
Hypothesis H7: diadic_rational_p w.
Hypothesis H8: w + u = y + y.
Hypothesis H9: SNo u.
Hypothesis H10: SNoLev u :e SNoLev z.
Theorem Conj_SNoS_omega_diadic_rational_p_lem__9__2: ~ diadic_rational_p u.
Admitted.

End Conj_SNoS_omega_diadic_rational_p_lem__9__2.
(** Conj_SNoS_omega_diadic_rational_p_lem__10__10 TMYEZA12F1rvpuV3jvJVpv7awmgwB2XXuHt bounty of about 25 bars **)
Section Conj_SNoS_omega_diadic_rational_p_lem__10__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: nat_p x.
Hypothesis H1: (forall u:set, u :e x -> (forall v:set, SNo v -> SNoLev v = u -> diadic_rational_p v)).
Hypothesis H2: SNo y.
Hypothesis H3: SNoLev y = x.
Hypothesis H4: ~ diadic_rational_p y.
Hypothesis H5: SNo_max_of (SNoL y) z.
Hypothesis H6: SNo z.
Hypothesis H7: SNoLev z :e SNoLev y.
Hypothesis H8: z < y.
Hypothesis H9: SNo_min_of (SNoR y) w.
Hypothesis H11: SNoLev w :e SNoLev y.
Hypothesis H12: y < w.
Hypothesis H13: SNo (y + y).
Hypothesis H14: SNo (z + w).
Hypothesis H15: diadic_rational_p z.
Theorem Conj_SNoS_omega_diadic_rational_p_lem__10__10: ~ diadic_rational_p w.
Admitted.

End Conj_SNoS_omega_diadic_rational_p_lem__10__10.
(** Conj_SNoS_omega_diadic_rational_p_lem__10__12 TMUiBGSafg3P5vutrDH7n1TJihAtNuHMe3y bounty of about 25 bars **)
Section Conj_SNoS_omega_diadic_rational_p_lem__10__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: nat_p x.
Hypothesis H1: (forall u:set, u :e x -> (forall v:set, SNo v -> SNoLev v = u -> diadic_rational_p v)).
Hypothesis H2: SNo y.
Hypothesis H3: SNoLev y = x.
Hypothesis H4: ~ diadic_rational_p y.
Hypothesis H5: SNo_max_of (SNoL y) z.
Hypothesis H6: SNo z.
Hypothesis H7: SNoLev z :e SNoLev y.
Hypothesis H8: z < y.
Hypothesis H9: SNo_min_of (SNoR y) w.
Hypothesis H10: SNo w.
Hypothesis H11: SNoLev w :e SNoLev y.
Hypothesis H13: SNo (y + y).
Hypothesis H14: SNo (z + w).
Hypothesis H15: diadic_rational_p z.
Theorem Conj_SNoS_omega_diadic_rational_p_lem__10__12: ~ diadic_rational_p w.
Admitted.

End Conj_SNoS_omega_diadic_rational_p_lem__10__12.
(** Conj_SNoS_omega_diadic_rational_p_lem__11__3 TMWXKUzSL25jh9dJYXM8nsfLs7ZCr8E7kLY bounty of about 25 bars **)
Section Conj_SNoS_omega_diadic_rational_p_lem__11__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: nat_p x.
Hypothesis H1: (forall u:set, u :e x -> (forall v:set, SNo v -> SNoLev v = u -> diadic_rational_p v)).
Hypothesis H2: SNo y.
Hypothesis H4: ~ diadic_rational_p y.
Hypothesis H5: SNo_max_of (SNoL y) z.
Hypothesis H6: SNo z.
Hypothesis H7: SNoLev z :e SNoLev y.
Hypothesis H8: z < y.
Hypothesis H9: SNo_min_of (SNoR y) w.
Hypothesis H10: SNo w.
Hypothesis H11: SNoLev w :e SNoLev y.
Hypothesis H12: y < w.
Hypothesis H13: SNo (y + y).
Hypothesis H14: SNo (z + w).
Theorem Conj_SNoS_omega_diadic_rational_p_lem__11__3: ~ diadic_rational_p z.
Admitted.

End Conj_SNoS_omega_diadic_rational_p_lem__11__3.
(** Conj_SNoS_omega_diadic_rational_p_lem__11__5 TMYDTWoPKKhTi2KKbDQjUw4AAX1HXJFFktq bounty of about 25 bars **)
Section Conj_SNoS_omega_diadic_rational_p_lem__11__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: nat_p x.
Hypothesis H1: (forall u:set, u :e x -> (forall v:set, SNo v -> SNoLev v = u -> diadic_rational_p v)).
Hypothesis H2: SNo y.
Hypothesis H3: SNoLev y = x.
Hypothesis H4: ~ diadic_rational_p y.
Hypothesis H6: SNo z.
Hypothesis H7: SNoLev z :e SNoLev y.
Hypothesis H8: z < y.
Hypothesis H9: SNo_min_of (SNoR y) w.
Hypothesis H10: SNo w.
Hypothesis H11: SNoLev w :e SNoLev y.
Hypothesis H12: y < w.
Hypothesis H13: SNo (y + y).
Hypothesis H14: SNo (z + w).
Theorem Conj_SNoS_omega_diadic_rational_p_lem__11__5: ~ diadic_rational_p z.
Admitted.

End Conj_SNoS_omega_diadic_rational_p_lem__11__5.
(** Conj_SNoS_ordsucc_omega_bdd_above__4__0 TMNgxC5YVMUhEsNkAtGvVTQ22pyheQnVo9p bounty of about 25 bars **)
Section Conj_SNoS_ordsucc_omega_bdd_above__4__0.
Variable x:set.
Variable y:set.
Hypothesis H1: SNo y.
Hypothesis H2: x < y.
Hypothesis H3: SNoLev y :e omega.
Theorem Conj_SNoS_ordsucc_omega_bdd_above__4__0: ordinal (SNoLev y) -> (exists z:set, z :e omega /\ x < z).
Admitted.

End Conj_SNoS_ordsucc_omega_bdd_above__4__0.
(** Conj_SNoS_ordsucc_omega_bdd_drat_intvl__3__0 TMaa94vJggKcEJFWqbFYFKdcrHSdHcZG8uE bounty of about 25 bars **)
Section Conj_SNoS_ordsucc_omega_bdd_drat_intvl__3__0.
Variable x:set.
Variable y:set.
Hypothesis H1: nIn x (SNoS_ omega).
Hypothesis H2: nat_p y.
Hypothesis H3: - y < x -> x < y -> (exists z:set, z :e SNoS_ omega /\ (z < x /\ x < z + ordsucc Empty)).
Hypothesis H4: - (ordsucc y) < x.
Hypothesis H5: x < ordsucc y.
Theorem Conj_SNoS_ordsucc_omega_bdd_drat_intvl__3__0: SNo y -> (exists z:set, z :e SNoS_ omega /\ (z < x /\ x < z + ordsucc Empty)).
Admitted.

End Conj_SNoS_ordsucc_omega_bdd_drat_intvl__3__0.
(** Conj_SNoS_ordsucc_omega_bdd_drat_intvl__5__2 TMFZ1ipbbA3ajjDAfQeAJQr3peiEPMuJTxR bounty of about 25 bars **)
Section Conj_SNoS_ordsucc_omega_bdd_drat_intvl__5__2.
Variable x:set.
Hypothesis H0: x :e SNoS_ (ordsucc omega).
Hypothesis H1: - omega < x.
Hypothesis H3: SNo x.
Hypothesis H4: ~ (forall y:set, y :e omega -> (exists z:set, z :e SNoS_ omega /\ (z < x /\ x < z + eps_ y))).
Hypothesis H5: nIn x (SNoS_ omega).
Theorem Conj_SNoS_ordsucc_omega_bdd_drat_intvl__5__2: ~ (forall y:set, nat_p y -> (exists z:set, z :e SNoS_ omega /\ (z < x /\ x < z + eps_ y))).
Admitted.

End Conj_SNoS_ordsucc_omega_bdd_drat_intvl__5__2.
(** Conj_real_E__3__6 TMe18YcuNkFzjiGrF2jdbxviCg1KLnzATQm bounty of about 25 bars **)
Section Conj_real_E__3__6.
Variable x:set.
Variable P:prop.
Hypothesis H0: SNo x -> SNoLev x :e ordsucc omega -> x :e SNoS_ (ordsucc omega) -> - omega < x -> x < omega -> (forall y:set, y :e SNoS_ omega -> (forall z:set, z :e omega -> abs_SNo (y + - x) < eps_ z) -> y = x) -> (forall y:set, y :e omega -> (exists z:set, z :e SNoS_ omega /\ (z < x /\ x < z + eps_ y))) -> P.
Hypothesis H1: x :e SNoS_ (ordsucc omega).
Hypothesis H2: (forall y:set, y :e SNoS_ omega -> (forall z:set, z :e omega -> abs_SNo (y + - x) < eps_ z) -> y = x).
Hypothesis H3: SNoLev x :e ordsucc omega.
Hypothesis H4: SNo x.
Hypothesis H5: x < omega.
Theorem Conj_real_E__3__6: (forall y:set, y :e omega -> (exists z:set, z :e SNoS_ omega /\ (z < x /\ x < z + eps_ y))) -> P.
Admitted.

End Conj_real_E__3__6.
(** Conj_real_E__4__0 TMYoeUL4MnkVKSXDUUvwyAQhi28mUYMvQNA bounty of about 25 bars **)
Section Conj_real_E__4__0.
Variable x:set.
Variable P:prop.
Hypothesis H1: x :e SNoS_ (ordsucc omega).
Hypothesis H2: x <> - omega.
Hypothesis H3: (forall y:set, y :e SNoS_ omega -> (forall z:set, z :e omega -> abs_SNo (y + - x) < eps_ z) -> y = x).
Hypothesis H4: SNoLev x :e ordsucc omega.
Hypothesis H5: SNo x.
Hypothesis H6: x < omega.
Theorem Conj_real_E__4__0: - omega < x -> P.
Admitted.

End Conj_real_E__4__0.
(** Conj_real_E__4__6 TMMBHs78zrRNyKW3cd7bJkyzvCZ4xFze9N9 bounty of about 25 bars **)
Section Conj_real_E__4__6.
Variable x:set.
Variable P:prop.
Hypothesis H0: SNo x -> SNoLev x :e ordsucc omega -> x :e SNoS_ (ordsucc omega) -> - omega < x -> x < omega -> (forall y:set, y :e SNoS_ omega -> (forall z:set, z :e omega -> abs_SNo (y + - x) < eps_ z) -> y = x) -> (forall y:set, y :e omega -> (exists z:set, z :e SNoS_ omega /\ (z < x /\ x < z + eps_ y))) -> P.
Hypothesis H1: x :e SNoS_ (ordsucc omega).
Hypothesis H2: x <> - omega.
Hypothesis H3: (forall y:set, y :e SNoS_ omega -> (forall z:set, z :e omega -> abs_SNo (y + - x) < eps_ z) -> y = x).
Hypothesis H4: SNoLev x :e ordsucc omega.
Hypothesis H5: SNo x.
Theorem Conj_real_E__4__6: - omega < x -> P.
Admitted.

End Conj_real_E__4__6.
(** Conj_SNoS_omega_real__2__0 TMXFqoGGxtT83bBhWxAzWzHtocSTXsvwuk9 bounty of about 25 bars **)
Section Conj_SNoS_omega_real__2__0.
Variable x:set.
Variable y:set.
Hypothesis H1: y :e SNoS_ omega.
Hypothesis H2: (forall z:set, z :e omega -> abs_SNo (y + - x) < eps_ z).
Hypothesis H3: Empty < y + - x.
Theorem Conj_SNoS_omega_real__2__0: ~ y + - x :e SNoS_ omega.
Admitted.

End Conj_SNoS_omega_real__2__0.
(** Conj_SNoS_omega_real__5__1 TMLbwz9KJVwZGYYgtEDwM3M7xaUNdgpV5Z6 bounty of about 25 bars **)
Section Conj_SNoS_omega_real__5__1.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e SNoS_ omega.
Hypothesis H2: y :e SNoS_ omega.
Hypothesis H3: (forall z:set, z :e omega -> abs_SNo (y + - x) < eps_ z).
Hypothesis H4: SNo y.
Hypothesis H5: Empty < x + - y.
Theorem Conj_SNoS_omega_real__5__1: ~ x + - y :e SNoS_ omega.
Admitted.

End Conj_SNoS_omega_real__5__1.
(** Conj_SNo_prereal_incr_lower_pos__4__6 TMJdQt7Y9beuSxZr6aRpknYi2Z1jHnGSPzL bounty of about 25 bars **)
Section Conj_SNo_prereal_incr_lower_pos__4__6.
Variable x:set.
Variable y:set.
Variable P:prop.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: y :e omega.
Hypothesis H2: (forall u:set, u :e SNoS_ omega -> Empty < u -> u < x -> x < u + eps_ y -> P).
Hypothesis H3: x < z + eps_ y.
Hypothesis H4: SNo z.
Hypothesis H5: z <= Empty.
Hypothesis H7: w :e omega.
Hypothesis H8: eps_ w <= x.
Theorem Conj_SNo_prereal_incr_lower_pos__4__6: SNo (eps_ w) -> x < eps_ w.
Admitted.

End Conj_SNo_prereal_incr_lower_pos__4__6.
(** Conj_SNoCutP_SNoCut_lim__4__4 TMbtyipTzmyeFPY82KXogBudj14dNt3eXNQ bounty of about 25 bars **)
Section Conj_SNoCutP_SNoCut_lim__4__4.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ordinal x.
Hypothesis H1: (forall w:set, w :e x -> ordsucc w :e x).
Hypothesis H2: Subq y (SNoS_ x).
Hypothesis H3: Subq z (SNoS_ x).
Hypothesis H5: (forall w:set, w :e y -> SNoLev w :e x).
Theorem Conj_SNoCutP_SNoCut_lim__4__4: (forall w:set, w :e z -> SNoLev w :e x) -> SNoLev (SNoCut y z) :e ordsucc x.
Admitted.

End Conj_SNoCutP_SNoCut_lim__4__4.
(** Conj_SNo_approx_real__4__12 TMPqS7JkbD2JqeTFSqysXfXdQ46YXcWzDnw bounty of about 25 bars **)
Section Conj_SNo_approx_real__4__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H2: z :e SNoS_ omega.
Hypothesis H3: (forall u:set, u :e omega -> abs_SNo (z + - x) < eps_ u).
Hypothesis H4: SNo z.
Hypothesis H5: SNo (- z).
Hypothesis H6: SNo (x + - z).
Hypothesis H7: w :e omega.
Hypothesis H8: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - (ap y (ordsucc w))) < eps_ v) -> u = ap y (ordsucc w)).
Hypothesis H9: SNo (ap y (ordsucc w)).
Hypothesis H10: z < ap y (ordsucc w).
Hypothesis H11: Empty < ap y (ordsucc w) + - z.
Hypothesis H13: ap y (ordsucc w) < x.
Theorem Conj_SNo_approx_real__4__12: z < x -> ap y w < z.
Admitted.

End Conj_SNo_approx_real__4__12.
(** Conj_SNo_approx_real__9__0 TMbXApEiiZa9o5aMfiQaEauJP71gJVrdqj2 bounty of about 25 bars **)
Section Conj_SNo_approx_real__9__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H1: (forall u:set, u :e omega -> ap y u < x).
Hypothesis H2: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y v < ap y u)).
Hypothesis H3: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H4: z :e SNoS_ omega.
Hypothesis H5: (forall u:set, u :e omega -> abs_SNo (z + - x) < eps_ u).
Hypothesis H6: SNo z.
Hypothesis H7: SNo (- z).
Hypothesis H8: SNo (x + - z).
Hypothesis H9: w :e omega.
Hypothesis H10: z <= ap y w.
Hypothesis H11: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - (ap y (ordsucc w))) < eps_ v) -> u = ap y (ordsucc w)).
Theorem Conj_SNo_approx_real__9__0: SNo (ap y (ordsucc w)) -> ap y w < z.
Admitted.

End Conj_SNo_approx_real__9__0.
(** Conj_SNo_approx_real__9__9 TMWJEMzAVTiFGKkg68ZoAaYLYCDa23XkVQG bounty of about 25 bars **)
Section Conj_SNo_approx_real__9__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e omega -> ap y u < x).
Hypothesis H2: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y v < ap y u)).
Hypothesis H3: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H4: z :e SNoS_ omega.
Hypothesis H5: (forall u:set, u :e omega -> abs_SNo (z + - x) < eps_ u).
Hypothesis H6: SNo z.
Hypothesis H7: SNo (- z).
Hypothesis H8: SNo (x + - z).
Hypothesis H10: z <= ap y w.
Hypothesis H11: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - (ap y (ordsucc w))) < eps_ v) -> u = ap y (ordsucc w)).
Theorem Conj_SNo_approx_real__9__9: SNo (ap y (ordsucc w)) -> ap y w < z.
Admitted.

End Conj_SNo_approx_real__9__9.
(** Conj_SNo_approx_real__10__10 TMcRdM5CBJVSRpd581R1cLb2Q3dopbZ7TnZ bounty of about 25 bars **)
Section Conj_SNo_approx_real__10__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo (- x).
Hypothesis H2: z :e SNoS_ omega.
Hypothesis H3: (forall u:set, u :e omega -> abs_SNo (z + - x) < eps_ u).
Hypothesis H4: SNo z.
Hypothesis H5: SNo (z + - x).
Hypothesis H6: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - (ap y (ordsucc w))) < eps_ v) -> u = ap y (ordsucc w)).
Hypothesis H7: SNo (ap y (ordsucc w)).
Hypothesis H8: ap y (ordsucc w) < z.
Hypothesis H9: Empty < z + - (ap y (ordsucc w)).
Hypothesis H11: x < ap y (ordsucc w).
Hypothesis H12: abs_SNo (z + - x) = z + - x.
Theorem Conj_SNo_approx_real__10__10: z = ap y (ordsucc w) -> z < ap y w.
Admitted.

End Conj_SNo_approx_real__10__10.
(** Conj_SNo_approx_real__12__7 TMK6gp8homc4N8ArrWNNBbXtYzvk4KH5ePC bounty of about 25 bars **)
Section Conj_SNo_approx_real__12__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo (- x).
Hypothesis H2: z :e SNoS_ omega.
Hypothesis H3: (forall u:set, u :e omega -> abs_SNo (z + - x) < eps_ u).
Hypothesis H4: SNo z.
Hypothesis H5: SNo (z + - x).
Hypothesis H6: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - (ap y (ordsucc w))) < eps_ v) -> u = ap y (ordsucc w)).
Hypothesis H8: ap y (ordsucc w) < z.
Hypothesis H9: Empty < z + - (ap y (ordsucc w)).
Hypothesis H10: SNo (z + - (ap y (ordsucc w))).
Hypothesis H11: x < ap y (ordsucc w).
Hypothesis H12: x < z.
Theorem Conj_SNo_approx_real__12__7: Empty < z + - x -> z < ap y w.
Admitted.

End Conj_SNo_approx_real__12__7.
(** Conj_SNo_approx_real__12__9 TMUL1QBL724QNP1qronWW1bmpYBBAxu6p1T bounty of about 25 bars **)
Section Conj_SNo_approx_real__12__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo (- x).
Hypothesis H2: z :e SNoS_ omega.
Hypothesis H3: (forall u:set, u :e omega -> abs_SNo (z + - x) < eps_ u).
Hypothesis H4: SNo z.
Hypothesis H5: SNo (z + - x).
Hypothesis H6: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - (ap y (ordsucc w))) < eps_ v) -> u = ap y (ordsucc w)).
Hypothesis H7: SNo (ap y (ordsucc w)).
Hypothesis H8: ap y (ordsucc w) < z.
Hypothesis H10: SNo (z + - (ap y (ordsucc w))).
Hypothesis H11: x < ap y (ordsucc w).
Hypothesis H12: x < z.
Theorem Conj_SNo_approx_real__12__9: Empty < z + - x -> z < ap y w.
Admitted.

End Conj_SNo_approx_real__12__9.
(** Conj_SNo_approx_real__14__8 TMa7acqvLaZq3E4YiBxxEDY4jDZfPPv2q1B bounty of about 25 bars **)
Section Conj_SNo_approx_real__14__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e omega -> x < ap y u).
Hypothesis H2: SNo (- x).
Hypothesis H3: z :e SNoS_ omega.
Hypothesis H4: (forall u:set, u :e omega -> abs_SNo (z + - x) < eps_ u).
Hypothesis H5: SNo z.
Hypothesis H6: SNo (z + - x).
Hypothesis H7: w :e omega.
Hypothesis H9: SNo (ap y (ordsucc w)).
Hypothesis H10: ap y (ordsucc w) < z.
Hypothesis H11: Empty < z + - (ap y (ordsucc w)).
Hypothesis H12: SNo (z + - (ap y (ordsucc w))).
Theorem Conj_SNo_approx_real__14__8: x < ap y (ordsucc w) -> z < ap y w.
Admitted.

End Conj_SNo_approx_real__14__8.
(** Conj_SNo_approx_real__14__10 TMcBEa1ubBhnXLmDbp3krvHuEu7fQmftYge bounty of about 25 bars **)
Section Conj_SNo_approx_real__14__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e omega -> x < ap y u).
Hypothesis H2: SNo (- x).
Hypothesis H3: z :e SNoS_ omega.
Hypothesis H4: (forall u:set, u :e omega -> abs_SNo (z + - x) < eps_ u).
Hypothesis H5: SNo z.
Hypothesis H6: SNo (z + - x).
Hypothesis H7: w :e omega.
Hypothesis H8: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - (ap y (ordsucc w))) < eps_ v) -> u = ap y (ordsucc w)).
Hypothesis H9: SNo (ap y (ordsucc w)).
Hypothesis H11: Empty < z + - (ap y (ordsucc w)).
Hypothesis H12: SNo (z + - (ap y (ordsucc w))).
Theorem Conj_SNo_approx_real__14__10: x < ap y (ordsucc w) -> z < ap y w.
Admitted.

End Conj_SNo_approx_real__14__10.
(** Conj_SNo_approx_real__18__0 TMJV1dcJwndTioAauemfR7EZFgLbLEQgvJn bounty of about 25 bars **)
Section Conj_SNo_approx_real__18__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H1: (forall u:set, u :e omega -> x < ap y u).
Hypothesis H2: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y u < ap y v)).
Hypothesis H3: SNo (- x).
Hypothesis H4: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H5: z :e SNoS_ omega.
Hypothesis H6: (forall u:set, u :e omega -> abs_SNo (z + - x) < eps_ u).
Hypothesis H7: SNo z.
Hypothesis H8: SNo (z + - x).
Hypothesis H9: w :e omega.
Hypothesis H10: ap y w <= z.
Hypothesis H11: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - (ap y (ordsucc w))) < eps_ v) -> u = ap y (ordsucc w)).
Theorem Conj_SNo_approx_real__18__0: SNo (ap y (ordsucc w)) -> z < ap y w.
Admitted.

End Conj_SNo_approx_real__18__0.
(** Conj_SNo_approx_real__18__8 TMVMMwG9jvsqDv6d9Zzj9y9rNAiwckvtarc bounty of about 25 bars **)
Section Conj_SNo_approx_real__18__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e omega -> x < ap y u).
Hypothesis H2: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y u < ap y v)).
Hypothesis H3: SNo (- x).
Hypothesis H4: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H5: z :e SNoS_ omega.
Hypothesis H6: (forall u:set, u :e omega -> abs_SNo (z + - x) < eps_ u).
Hypothesis H7: SNo z.
Hypothesis H9: w :e omega.
Hypothesis H10: ap y w <= z.
Hypothesis H11: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - (ap y (ordsucc w))) < eps_ v) -> u = ap y (ordsucc w)).
Theorem Conj_SNo_approx_real__18__8: SNo (ap y (ordsucc w)) -> z < ap y w.
Admitted.

End Conj_SNo_approx_real__18__8.
(** Conj_SNo_approx_real__19__13 TMajuAh8BJqhtZB8ApXe4wjvzZsfA6EMj72 bounty of about 25 bars **)
Section Conj_SNo_approx_real__19__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: z :e setexp (SNoS_ omega) omega.
Hypothesis H2: (forall u:set, u :e omega -> x < ap z u).
Hypothesis H3: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap z u < ap z v)).
Hypothesis H4: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H5: SNo (- x).
Hypothesis H6: (forall u:set, u :e omega -> SNo (ap z u)).
Hypothesis H7: (forall u:set, SNo u -> (forall v:set, v :e Repl omega (ap y) -> v < u) -> (forall v:set, v :e Repl omega (ap z) -> u < v) -> Subq (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoLev u) /\ SNoEq_ (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoCut (Repl omega (ap y)) (Repl omega (ap z))) u).
Hypothesis H8: SNoLev x = omega.
Hypothesis H9: w :e SNoS_ omega.
Hypothesis H10: (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u).
Hypothesis H11: SNoLev w :e omega.
Hypothesis H12: SNo w.
Hypothesis H14: (forall u:set, u :e Repl omega (ap y) -> u < w).
Theorem Conj_SNo_approx_real__19__13: (forall u:set, u :e Repl omega (ap z) -> w < u) -> w = x.
Admitted.

End Conj_SNo_approx_real__19__13.
(** Conj_SNo_approx_real__20__16 TMZkg4T1RLwosEcFjgCUMMZNKwFZjbyAaVK bounty of about 25 bars **)
Section Conj_SNo_approx_real__20__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: y :e setexp (SNoS_ omega) omega.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: (forall u:set, u :e omega -> ap y u < x).
Hypothesis H4: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y v < ap y u)).
Hypothesis H5: (forall u:set, u :e omega -> x < ap z u).
Hypothesis H6: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap z u < ap z v)).
Hypothesis H7: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H8: SNo (- x).
Hypothesis H9: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H10: (forall u:set, u :e omega -> SNo (ap z u)).
Hypothesis H11: (forall u:set, SNo u -> (forall v:set, v :e Repl omega (ap y) -> v < u) -> (forall v:set, v :e Repl omega (ap z) -> u < v) -> Subq (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoLev u) /\ SNoEq_ (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoCut (Repl omega (ap y)) (Repl omega (ap z))) u).
Hypothesis H12: SNoLev x = omega.
Hypothesis H13: w :e SNoS_ omega.
Hypothesis H14: (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u).
Hypothesis H15: SNoLev w :e omega.
Hypothesis H17: SNo (- w).
Hypothesis H18: SNo (x + - w).
Hypothesis H19: SNo (w + - x).
Theorem Conj_SNo_approx_real__20__16: (forall u:set, u :e Repl omega (ap y) -> u < w) -> w = x.
Admitted.

End Conj_SNo_approx_real__20__16.
(** Conj_SNo_approx_real__21__1 TMdvyEdxk1oh6DGGmCKEHbfX8bkafMLPXw9 bounty of about 25 bars **)
Section Conj_SNo_approx_real__21__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: (forall u:set, u :e omega -> ap y u < x).
Hypothesis H4: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y v < ap y u)).
Hypothesis H5: (forall u:set, u :e omega -> x < ap z u).
Hypothesis H6: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap z u < ap z v)).
Hypothesis H7: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H8: SNo (- x).
Hypothesis H9: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H10: (forall u:set, u :e omega -> SNo (ap z u)).
Hypothesis H11: (forall u:set, SNo u -> (forall v:set, v :e Repl omega (ap y) -> v < u) -> (forall v:set, v :e Repl omega (ap z) -> u < v) -> Subq (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoLev u) /\ SNoEq_ (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoCut (Repl omega (ap y)) (Repl omega (ap z))) u).
Hypothesis H12: SNoLev x = omega.
Hypothesis H13: w :e SNoS_ omega.
Hypothesis H14: (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u).
Hypothesis H15: SNoLev w :e omega.
Hypothesis H16: SNo w.
Hypothesis H17: SNo (- w).
Hypothesis H18: SNo (x + - w).
Theorem Conj_SNo_approx_real__21__1: SNo (w + - x) -> w = x.
Admitted.

End Conj_SNo_approx_real__21__1.
(** Conj_SNo_approx_real__21__2 TMZW1pgKP5r9GC4dH6YZLPkFRVoi8KjKsJP bounty of about 25 bars **)
Section Conj_SNo_approx_real__21__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: y :e setexp (SNoS_ omega) omega.
Hypothesis H3: (forall u:set, u :e omega -> ap y u < x).
Hypothesis H4: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y v < ap y u)).
Hypothesis H5: (forall u:set, u :e omega -> x < ap z u).
Hypothesis H6: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap z u < ap z v)).
Hypothesis H7: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H8: SNo (- x).
Hypothesis H9: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H10: (forall u:set, u :e omega -> SNo (ap z u)).
Hypothesis H11: (forall u:set, SNo u -> (forall v:set, v :e Repl omega (ap y) -> v < u) -> (forall v:set, v :e Repl omega (ap z) -> u < v) -> Subq (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoLev u) /\ SNoEq_ (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoCut (Repl omega (ap y)) (Repl omega (ap z))) u).
Hypothesis H12: SNoLev x = omega.
Hypothesis H13: w :e SNoS_ omega.
Hypothesis H14: (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u).
Hypothesis H15: SNoLev w :e omega.
Hypothesis H16: SNo w.
Hypothesis H17: SNo (- w).
Hypothesis H18: SNo (x + - w).
Theorem Conj_SNo_approx_real__21__2: SNo (w + - x) -> w = x.
Admitted.

End Conj_SNo_approx_real__21__2.
(** Conj_SNo_approx_real__22__3 TMSJhNkxnEy5fwwk5nfNKVWd18nEJFwsVBm bounty of about 25 bars **)
Section Conj_SNo_approx_real__22__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: y :e setexp (SNoS_ omega) omega.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H4: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y v < ap y u)).
Hypothesis H5: (forall u:set, u :e omega -> x < ap z u).
Hypothesis H6: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap z u < ap z v)).
Hypothesis H7: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H8: SNo (- x).
Hypothesis H9: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H10: (forall u:set, u :e omega -> SNo (ap z u)).
Hypothesis H11: (forall u:set, SNo u -> (forall v:set, v :e Repl omega (ap y) -> v < u) -> (forall v:set, v :e Repl omega (ap z) -> u < v) -> Subq (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoLev u) /\ SNoEq_ (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoCut (Repl omega (ap y)) (Repl omega (ap z))) u).
Hypothesis H12: SNoLev x = omega.
Hypothesis H13: w :e SNoS_ omega.
Hypothesis H14: (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u).
Hypothesis H15: SNoLev w :e omega.
Hypothesis H16: SNo w.
Hypothesis H17: SNo (- w).
Theorem Conj_SNo_approx_real__22__3: SNo (x + - w) -> w = x.
Admitted.

End Conj_SNo_approx_real__22__3.
(** Conj_SNo_approx_real__22__9 TMKHHLPgAtoYdmZD13wKmjxUsMvC8dGCCVp bounty of about 25 bars **)
Section Conj_SNo_approx_real__22__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: y :e setexp (SNoS_ omega) omega.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: (forall u:set, u :e omega -> ap y u < x).
Hypothesis H4: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y v < ap y u)).
Hypothesis H5: (forall u:set, u :e omega -> x < ap z u).
Hypothesis H6: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap z u < ap z v)).
Hypothesis H7: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H8: SNo (- x).
Hypothesis H10: (forall u:set, u :e omega -> SNo (ap z u)).
Hypothesis H11: (forall u:set, SNo u -> (forall v:set, v :e Repl omega (ap y) -> v < u) -> (forall v:set, v :e Repl omega (ap z) -> u < v) -> Subq (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoLev u) /\ SNoEq_ (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoCut (Repl omega (ap y)) (Repl omega (ap z))) u).
Hypothesis H12: SNoLev x = omega.
Hypothesis H13: w :e SNoS_ omega.
Hypothesis H14: (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u).
Hypothesis H15: SNoLev w :e omega.
Hypothesis H16: SNo w.
Hypothesis H17: SNo (- w).
Theorem Conj_SNo_approx_real__22__9: SNo (x + - w) -> w = x.
Admitted.

End Conj_SNo_approx_real__22__9.
(** Conj_SNo_approx_real__23__2 TMcco6JvwnvX2cxjjrXGPkhnk5j2tpwFAuX bounty of about 25 bars **)
Section Conj_SNo_approx_real__23__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: y :e setexp (SNoS_ omega) omega.
Hypothesis H3: (forall u:set, u :e omega -> ap y u < x).
Hypothesis H4: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y v < ap y u)).
Hypothesis H5: (forall u:set, u :e omega -> x < ap z u).
Hypothesis H6: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap z u < ap z v)).
Hypothesis H7: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H8: SNo (- x).
Hypothesis H9: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H10: (forall u:set, u :e omega -> SNo (ap z u)).
Hypothesis H11: (forall u:set, SNo u -> (forall v:set, v :e Repl omega (ap y) -> v < u) -> (forall v:set, v :e Repl omega (ap z) -> u < v) -> Subq (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoLev u) /\ SNoEq_ (SNoLev (SNoCut (Repl omega (ap y)) (Repl omega (ap z)))) (SNoCut (Repl omega (ap y)) (Repl omega (ap z))) u).
Hypothesis H12: SNoLev x = omega.
Hypothesis H13: w :e SNoS_ omega.
Hypothesis H14: (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u).
Hypothesis H15: SNoLev w :e omega.
Hypothesis H16: SNo w.
Theorem Conj_SNo_approx_real__23__2: SNo (- w) -> w = x.
Admitted.

End Conj_SNo_approx_real__23__2.
(** Conj_SNo_approx_real__26__1 TMKyprpZaE3jjjLHjcTEzpwXghbSiYXeWT9 bounty of about 25 bars **)
Section Conj_SNo_approx_real__26__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: (forall w:set, w :e omega -> ap y w < x).
Hypothesis H4: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H5: (forall w:set, w :e omega -> x < ap z w).
Hypothesis H6: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap z w < ap z u)).
Hypothesis H7: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H8: SNo (- x).
Hypothesis H9: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H10: (forall w:set, w :e omega -> SNo (ap z w)).
Theorem Conj_SNo_approx_real__26__1: (forall w:set, w :e omega -> (forall u:set, u :e omega -> ap y w < ap z u)) -> x :e real.
Admitted.

End Conj_SNo_approx_real__26__1.
(** Conj_SNo_approx_real__28__6 TMHbiUhmam383wkNS2DVV7TFtkWVoKasHp4 bounty of about 25 bars **)
Section Conj_SNo_approx_real__28__6.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: y :e setexp (SNoS_ omega) omega.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: (forall w:set, w :e omega -> ap y w < x).
Hypothesis H4: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H5: (forall w:set, w :e omega -> x < ap z w).
Hypothesis H7: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H8: SNo (- x).
Theorem Conj_SNo_approx_real__28__6: (forall w:set, w :e omega -> SNo (ap y w)) -> x :e real.
Admitted.

End Conj_SNo_approx_real__28__6.
(** Conj_SNo_approx_real_rep__1__0 TMPswjThdqLyamR76SpcC6kdeKHkjMeCG8q bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__1__0.
Variable x:set.
Variable y:set.
Hypothesis H1: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - x) < eps_ w) -> z = x).
Hypothesis H2: SNo y.
Hypothesis H3: x < y.
Hypothesis H4: y :e SNoS_ omega.
Hypothesis H5: Empty < y + - x.
Hypothesis H6: ~ (exists z:set, z :e omega /\ (x + eps_ z) <= y).
Theorem Conj_SNo_approx_real_rep__1__0: y <> x.
Admitted.

End Conj_SNo_approx_real_rep__1__0.
(** Conj_SNo_approx_real_rep__1__1 TMLUKQ6pYN7VGx5kXhsLmCsEDg8Fppg9mKf bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__1__1.
Variable x:set.
Variable y:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: x < y.
Hypothesis H4: y :e SNoS_ omega.
Hypothesis H5: Empty < y + - x.
Hypothesis H6: ~ (exists z:set, z :e omega /\ (x + eps_ z) <= y).
Theorem Conj_SNo_approx_real_rep__1__1: y <> x.
Admitted.

End Conj_SNo_approx_real_rep__1__1.
(** Conj_SNo_approx_real_rep__3__0 TMHCAkDxZzUi1rkKiKnR2P4yMtAcv3NDmES bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__3__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H1: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - x) < eps_ v) -> u = x).
Hypothesis H2: (forall u:set, u :e omega -> SNo (ap z u)).
Hypothesis H3: (forall u:set, u :e omega -> (ap z u + - (eps_ u)) < x).
Hypothesis H4: SNo (SNoCut (Repl omega (ap y)) (Repl omega (ap z))).
Hypothesis H5: (forall u:set, u :e omega -> SNoCut (Repl omega (ap y)) (Repl omega (ap z)) < ap z u).
Hypothesis H6: SNo w.
Hypothesis H7: x < w.
Hypothesis H8: w :e SNoS_ omega.
Theorem Conj_SNo_approx_real_rep__3__0: Empty < w + - x -> SNoCut (Repl omega (ap y)) (Repl omega (ap z)) < w.
Admitted.

End Conj_SNo_approx_real_rep__3__0.
(** Conj_SNo_approx_real_rep__6__2 TMZmsUvnGDWMjz4sAcPdhLK7UaGtpZJgpDn bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__6__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - x) < eps_ v) -> u = x).
Hypothesis H3: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap y)) (Repl omega (ap z))).
Hypothesis H5: (forall u:set, u :e omega -> ap y u < SNoCut (Repl omega (ap y)) (Repl omega (ap z))).
Hypothesis H6: SNo w.
Hypothesis H7: w < x.
Hypothesis H8: w :e SNoS_ omega.
Hypothesis H9: Empty < x + - w.
Theorem Conj_SNo_approx_real_rep__6__2: (exists u:set, u :e omega /\ (w + eps_ u) <= x) -> w < SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Admitted.

End Conj_SNo_approx_real_rep__6__2.
(** Conj_SNo_approx_real_rep__6__4 TMPpGQHycudyQ8ukFfoNh1GKVQkBKjKpz4m bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__6__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - x) < eps_ v) -> u = x).
Hypothesis H2: (forall u:set, u :e omega -> ap y u < x /\ x < ap y u + eps_ u /\ (forall v:set, v :e u -> ap y v < ap y u)).
Hypothesis H3: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H5: (forall u:set, u :e omega -> ap y u < SNoCut (Repl omega (ap y)) (Repl omega (ap z))).
Hypothesis H6: SNo w.
Hypothesis H7: w < x.
Hypothesis H8: w :e SNoS_ omega.
Hypothesis H9: Empty < x + - w.
Theorem Conj_SNo_approx_real_rep__6__4: (exists u:set, u :e omega /\ (w + eps_ u) <= x) -> w < SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Admitted.

End Conj_SNo_approx_real_rep__6__4.
(** Conj_SNo_approx_real_rep__7__2 TMHffEj8MiT2BxNpdHqm3u3cD5Ns6RkGGRw bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__7__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - x) < eps_ v) -> u = x).
Hypothesis H3: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap y)) (Repl omega (ap z))).
Hypothesis H5: (forall u:set, u :e omega -> ap y u < SNoCut (Repl omega (ap y)) (Repl omega (ap z))).
Hypothesis H6: SNo w.
Hypothesis H7: w < x.
Hypothesis H8: w :e SNoS_ omega.
Theorem Conj_SNo_approx_real_rep__7__2: Empty < x + - w -> w < SNoCut (Repl omega (ap y)) (Repl omega (ap z)).
Admitted.

End Conj_SNo_approx_real_rep__7__2.
(** Conj_SNo_approx_real_rep__9__9 TMP6JXqsMz2cuVZqivvisGMJYMZ16muRMnS bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__9__9.
Variable x:set.
Variable P:prop.
Variable y:set.
Variable z:set.
Hypothesis H0: x :e real.
Hypothesis H1: (forall w:set, w :e setexp (SNoS_ omega) omega -> (forall u:set, u :e setexp (SNoS_ omega) omega -> (forall v:set, v :e omega -> ap w v < x) -> (forall v:set, v :e omega -> x < ap w v + eps_ v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap w x2 < ap w v)) -> (forall v:set, v :e omega -> (ap u v + - (eps_ v)) < x) -> (forall v:set, v :e omega -> x < ap u v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap u v < ap u x2)) -> SNoCutP (Repl omega (ap w)) (Repl omega (ap u)) -> x = SNoCut (Repl omega (ap w)) (Repl omega (ap u)) -> P)).
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e SNoS_ omega -> (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u) -> w = x).
Hypothesis H4: y :e setexp (SNoS_ omega) omega.
Hypothesis H5: (forall w:set, w :e omega -> ap y w < x /\ x < ap y w + eps_ w /\ (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H6: z :e setexp (SNoS_ omega) omega.
Hypothesis H7: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H8: (forall w:set, w :e omega -> SNo (ap z w)).
Hypothesis H10: (forall w:set, w :e omega -> x < ap y w + eps_ w).
Hypothesis H11: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H12: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x).
Hypothesis H13: (forall w:set, w :e omega -> x < ap z w).
Hypothesis H14: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap z w < ap z u)).
Hypothesis H15: SNoCutP (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H16: SNo (SNoCut (Repl omega (ap y)) (Repl omega (ap z))).
Hypothesis H17: (forall w:set, w :e omega -> ap y w < SNoCut (Repl omega (ap y)) (Repl omega (ap z))).
Hypothesis H18: (forall w:set, w :e omega -> SNoCut (Repl omega (ap y)) (Repl omega (ap z)) < ap z w).
Theorem Conj_SNo_approx_real_rep__9__9: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)) -> P.
Admitted.

End Conj_SNo_approx_real_rep__9__9.
(** Conj_SNo_approx_real_rep__9__10 TMSyd6rEBKTrjHxdqN31rPgSF19hZApgB4m bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__9__10.
Variable x:set.
Variable P:prop.
Variable y:set.
Variable z:set.
Hypothesis H0: x :e real.
Hypothesis H1: (forall w:set, w :e setexp (SNoS_ omega) omega -> (forall u:set, u :e setexp (SNoS_ omega) omega -> (forall v:set, v :e omega -> ap w v < x) -> (forall v:set, v :e omega -> x < ap w v + eps_ v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap w x2 < ap w v)) -> (forall v:set, v :e omega -> (ap u v + - (eps_ v)) < x) -> (forall v:set, v :e omega -> x < ap u v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap u v < ap u x2)) -> SNoCutP (Repl omega (ap w)) (Repl omega (ap u)) -> x = SNoCut (Repl omega (ap w)) (Repl omega (ap u)) -> P)).
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e SNoS_ omega -> (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u) -> w = x).
Hypothesis H4: y :e setexp (SNoS_ omega) omega.
Hypothesis H5: (forall w:set, w :e omega -> ap y w < x /\ x < ap y w + eps_ w /\ (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H6: z :e setexp (SNoS_ omega) omega.
Hypothesis H7: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H8: (forall w:set, w :e omega -> SNo (ap z w)).
Hypothesis H9: (forall w:set, w :e omega -> ap y w < x).
Hypothesis H11: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H12: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x).
Hypothesis H13: (forall w:set, w :e omega -> x < ap z w).
Hypothesis H14: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap z w < ap z u)).
Hypothesis H15: SNoCutP (Repl omega (ap y)) (Repl omega (ap z)).
Hypothesis H16: SNo (SNoCut (Repl omega (ap y)) (Repl omega (ap z))).
Hypothesis H17: (forall w:set, w :e omega -> ap y w < SNoCut (Repl omega (ap y)) (Repl omega (ap z))).
Hypothesis H18: (forall w:set, w :e omega -> SNoCut (Repl omega (ap y)) (Repl omega (ap z)) < ap z w).
Theorem Conj_SNo_approx_real_rep__9__10: x = SNoCut (Repl omega (ap y)) (Repl omega (ap z)) -> P.
Admitted.

End Conj_SNo_approx_real_rep__9__10.
(** Conj_SNo_approx_real_rep__11__2 TMGwyfBiq15RqrJxuD71iMYMRnxgyC1dfU1 bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__11__2.
Variable x:set.
Variable P:prop.
Variable y:set.
Variable z:set.
Hypothesis H0: x :e real.
Hypothesis H1: (forall w:set, w :e setexp (SNoS_ omega) omega -> (forall u:set, u :e setexp (SNoS_ omega) omega -> (forall v:set, v :e omega -> ap w v < x) -> (forall v:set, v :e omega -> x < ap w v + eps_ v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap w x2 < ap w v)) -> (forall v:set, v :e omega -> (ap u v + - (eps_ v)) < x) -> (forall v:set, v :e omega -> x < ap u v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap u v < ap u x2)) -> SNoCutP (Repl omega (ap w)) (Repl omega (ap u)) -> x = SNoCut (Repl omega (ap w)) (Repl omega (ap u)) -> P)).
Hypothesis H3: (forall w:set, w :e SNoS_ omega -> (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u) -> w = x).
Hypothesis H4: y :e setexp (SNoS_ omega) omega.
Hypothesis H5: (forall w:set, w :e omega -> ap y w < x /\ x < ap y w + eps_ w /\ (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H6: z :e setexp (SNoS_ omega) omega.
Hypothesis H7: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x /\ x < ap z w /\ (forall u:set, u :e w -> ap z w < ap z u)).
Hypothesis H8: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H9: (forall w:set, w :e omega -> SNo (ap z w)).
Hypothesis H10: (forall w:set, w :e omega -> ap y w < x).
Hypothesis H11: (forall w:set, w :e omega -> x < ap y w + eps_ w).
Hypothesis H12: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H13: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x).
Hypothesis H14: (forall w:set, w :e omega -> x < ap z w).
Theorem Conj_SNo_approx_real_rep__11__2: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap z w < ap z u)) -> P.
Admitted.

End Conj_SNo_approx_real_rep__11__2.
(** Conj_SNo_approx_real_rep__11__3 TMRS23j1xnPpdb9o7FQ5E2S2uQyZEJGFDxX bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__11__3.
Variable x:set.
Variable P:prop.
Variable y:set.
Variable z:set.
Hypothesis H0: x :e real.
Hypothesis H1: (forall w:set, w :e setexp (SNoS_ omega) omega -> (forall u:set, u :e setexp (SNoS_ omega) omega -> (forall v:set, v :e omega -> ap w v < x) -> (forall v:set, v :e omega -> x < ap w v + eps_ v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap w x2 < ap w v)) -> (forall v:set, v :e omega -> (ap u v + - (eps_ v)) < x) -> (forall v:set, v :e omega -> x < ap u v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap u v < ap u x2)) -> SNoCutP (Repl omega (ap w)) (Repl omega (ap u)) -> x = SNoCut (Repl omega (ap w)) (Repl omega (ap u)) -> P)).
Hypothesis H2: SNo x.
Hypothesis H4: y :e setexp (SNoS_ omega) omega.
Hypothesis H5: (forall w:set, w :e omega -> ap y w < x /\ x < ap y w + eps_ w /\ (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H6: z :e setexp (SNoS_ omega) omega.
Hypothesis H7: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x /\ x < ap z w /\ (forall u:set, u :e w -> ap z w < ap z u)).
Hypothesis H8: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H9: (forall w:set, w :e omega -> SNo (ap z w)).
Hypothesis H10: (forall w:set, w :e omega -> ap y w < x).
Hypothesis H11: (forall w:set, w :e omega -> x < ap y w + eps_ w).
Hypothesis H12: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H13: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x).
Hypothesis H14: (forall w:set, w :e omega -> x < ap z w).
Theorem Conj_SNo_approx_real_rep__11__3: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap z w < ap z u)) -> P.
Admitted.

End Conj_SNo_approx_real_rep__11__3.
(** Conj_SNo_approx_real_rep__14__0 TMdLLekUxFyp1BUUub1FKbb59PQyesDGDRG bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__14__0.
Variable x:set.
Variable P:prop.
Variable y:set.
Variable z:set.
Hypothesis H1: (forall w:set, w :e setexp (SNoS_ omega) omega -> (forall u:set, u :e setexp (SNoS_ omega) omega -> (forall v:set, v :e omega -> ap w v < x) -> (forall v:set, v :e omega -> x < ap w v + eps_ v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap w x2 < ap w v)) -> (forall v:set, v :e omega -> (ap u v + - (eps_ v)) < x) -> (forall v:set, v :e omega -> x < ap u v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap u v < ap u x2)) -> SNoCutP (Repl omega (ap w)) (Repl omega (ap u)) -> x = SNoCut (Repl omega (ap w)) (Repl omega (ap u)) -> P)).
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e SNoS_ omega -> (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u) -> w = x).
Hypothesis H4: y :e setexp (SNoS_ omega) omega.
Hypothesis H5: (forall w:set, w :e omega -> ap y w < x /\ x < ap y w + eps_ w /\ (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H6: z :e setexp (SNoS_ omega) omega.
Hypothesis H7: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x /\ x < ap z w /\ (forall u:set, u :e w -> ap z w < ap z u)).
Hypothesis H8: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H9: (forall w:set, w :e omega -> SNo (ap z w)).
Hypothesis H10: (forall w:set, w :e omega -> ap y w < x).
Hypothesis H11: (forall w:set, w :e omega -> x < ap y w + eps_ w).
Theorem Conj_SNo_approx_real_rep__14__0: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap y u < ap y w)) -> P.
Admitted.

End Conj_SNo_approx_real_rep__14__0.
(** Conj_SNo_approx_real_rep__14__4 TMHd3bk5esoJHwbrBU1dVbhMuvmJNMpvYmh bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__14__4.
Variable x:set.
Variable P:prop.
Variable y:set.
Variable z:set.
Hypothesis H0: x :e real.
Hypothesis H1: (forall w:set, w :e setexp (SNoS_ omega) omega -> (forall u:set, u :e setexp (SNoS_ omega) omega -> (forall v:set, v :e omega -> ap w v < x) -> (forall v:set, v :e omega -> x < ap w v + eps_ v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap w x2 < ap w v)) -> (forall v:set, v :e omega -> (ap u v + - (eps_ v)) < x) -> (forall v:set, v :e omega -> x < ap u v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap u v < ap u x2)) -> SNoCutP (Repl omega (ap w)) (Repl omega (ap u)) -> x = SNoCut (Repl omega (ap w)) (Repl omega (ap u)) -> P)).
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e SNoS_ omega -> (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u) -> w = x).
Hypothesis H5: (forall w:set, w :e omega -> ap y w < x /\ x < ap y w + eps_ w /\ (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H6: z :e setexp (SNoS_ omega) omega.
Hypothesis H7: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x /\ x < ap z w /\ (forall u:set, u :e w -> ap z w < ap z u)).
Hypothesis H8: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H9: (forall w:set, w :e omega -> SNo (ap z w)).
Hypothesis H10: (forall w:set, w :e omega -> ap y w < x).
Hypothesis H11: (forall w:set, w :e omega -> x < ap y w + eps_ w).
Theorem Conj_SNo_approx_real_rep__14__4: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap y u < ap y w)) -> P.
Admitted.

End Conj_SNo_approx_real_rep__14__4.
(** Conj_SNo_approx_real_rep__14__10 TMXG7FzpRXAMVDbi71dZodhfv3HgRvPj2HS bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__14__10.
Variable x:set.
Variable P:prop.
Variable y:set.
Variable z:set.
Hypothesis H0: x :e real.
Hypothesis H1: (forall w:set, w :e setexp (SNoS_ omega) omega -> (forall u:set, u :e setexp (SNoS_ omega) omega -> (forall v:set, v :e omega -> ap w v < x) -> (forall v:set, v :e omega -> x < ap w v + eps_ v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap w x2 < ap w v)) -> (forall v:set, v :e omega -> (ap u v + - (eps_ v)) < x) -> (forall v:set, v :e omega -> x < ap u v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap u v < ap u x2)) -> SNoCutP (Repl omega (ap w)) (Repl omega (ap u)) -> x = SNoCut (Repl omega (ap w)) (Repl omega (ap u)) -> P)).
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e SNoS_ omega -> (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u) -> w = x).
Hypothesis H4: y :e setexp (SNoS_ omega) omega.
Hypothesis H5: (forall w:set, w :e omega -> ap y w < x /\ x < ap y w + eps_ w /\ (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H6: z :e setexp (SNoS_ omega) omega.
Hypothesis H7: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x /\ x < ap z w /\ (forall u:set, u :e w -> ap z w < ap z u)).
Hypothesis H8: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H9: (forall w:set, w :e omega -> SNo (ap z w)).
Hypothesis H11: (forall w:set, w :e omega -> x < ap y w + eps_ w).
Theorem Conj_SNo_approx_real_rep__14__10: (forall w:set, w :e omega -> (forall u:set, u :e w -> ap y u < ap y w)) -> P.
Admitted.

End Conj_SNo_approx_real_rep__14__10.
(** Conj_SNo_approx_real_rep__16__2 TMZC2m1qkeQPJ61k7mqK9SeXH9A98WYVMoD bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__16__2.
Variable x:set.
Variable P:prop.
Variable y:set.
Variable z:set.
Hypothesis H0: x :e real.
Hypothesis H1: (forall w:set, w :e setexp (SNoS_ omega) omega -> (forall u:set, u :e setexp (SNoS_ omega) omega -> (forall v:set, v :e omega -> ap w v < x) -> (forall v:set, v :e omega -> x < ap w v + eps_ v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap w x2 < ap w v)) -> (forall v:set, v :e omega -> (ap u v + - (eps_ v)) < x) -> (forall v:set, v :e omega -> x < ap u v) -> (forall v:set, v :e omega -> (forall x2:set, x2 :e v -> ap u v < ap u x2)) -> SNoCutP (Repl omega (ap w)) (Repl omega (ap u)) -> x = SNoCut (Repl omega (ap w)) (Repl omega (ap u)) -> P)).
Hypothesis H3: (forall w:set, w :e SNoS_ omega -> (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u) -> w = x).
Hypothesis H4: y :e setexp (SNoS_ omega) omega.
Hypothesis H5: (forall w:set, w :e omega -> ap y w < x /\ x < ap y w + eps_ w /\ (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H6: z :e setexp (SNoS_ omega) omega.
Hypothesis H7: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x /\ x < ap z w /\ (forall u:set, u :e w -> ap z w < ap z u)).
Hypothesis H8: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H9: (forall w:set, w :e omega -> SNo (ap z w)).
Theorem Conj_SNo_approx_real_rep__16__2: (forall w:set, w :e omega -> ap y w < x) -> P.
Admitted.

End Conj_SNo_approx_real_rep__16__2.
(** Conj_SNo_approx_real_rep__17__1 TMPJPiemdmEqE19WLTZU7Z8pEfz8s6bFjSc bounty of about 25 bars **)
Section Conj_SNo_approx_real_rep__17__1.
Variable x:set.
Variable P:prop.
Variable y:set.
Variable z:set.
Hypothesis H0: x :e real.
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e SNoS_ omega -> (forall u:set, u :e omega -> abs_SNo (w + - x) < eps_ u) -> w = x).
Hypothesis H4: y :e setexp (SNoS_ omega) omega.
Hypothesis H5: (forall w:set, w :e omega -> ap y w < x /\ x < ap y w + eps_ w /\ (forall u:set, u :e w -> ap y u < ap y w)).
Hypothesis H6: z :e setexp (SNoS_ omega) omega.
Hypothesis H7: (forall w:set, w :e omega -> (ap z w + - (eps_ w)) < x /\ x < ap z w /\ (forall u:set, u :e w -> ap z w < ap z u)).
Hypothesis H8: (forall w:set, w :e omega -> SNo (ap y w)).
Theorem Conj_SNo_approx_real_rep__17__1: (forall w:set, w :e omega -> SNo (ap z w)) -> P.
Admitted.

End Conj_SNo_approx_real_rep__17__1.
(** Conj_real_add_SNo__1__6 TMY8g4rbgXKt846Bb4n2R14nwgb1kh1G566 bounty of about 25 bars **)
Section Conj_real_add_SNo__1__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, v :e omega -> x < ap z v + eps_ v).
Hypothesis H1: (forall v:set, v :e omega -> y < ap w v + eps_ v).
Hypothesis H2: SNo x.
Hypothesis H3: SNo y.
Hypothesis H4: (forall v:set, v :e omega -> SNo (ap z (ordsucc v))).
Hypothesis H5: (forall v:set, v :e omega -> SNo (ap w (ordsucc v))).
Theorem Conj_real_add_SNo__1__6: SNo (eps_ (ordsucc u)) -> (x + y) < (ap z (ordsucc u) + ap w (ordsucc u)) + eps_ (ordsucc u) + eps_ (ordsucc u).
Admitted.

End Conj_real_add_SNo__1__6.
(** Conj_real_add_SNo__2__3 TMFfzj64YGAjMcfvhxia4s9aZiABLUimVYc bounty of about 25 bars **)
Section Conj_real_add_SNo__2__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap x v < ap x u)).
Hypothesis H1: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y v < ap y u)).
Hypothesis H2: (forall u:set, u :e omega -> SNo (ap x (ordsucc u))).
Hypothesis H4: (forall u:set, u :e omega -> ap (Sigma omega (fun v:set => ap x (ordsucc v) + ap y (ordsucc v))) u = ap x (ordsucc u) + ap y (ordsucc u)).
Hypothesis H5: z :e omega.
Hypothesis H6: w :e z.
Theorem Conj_real_add_SNo__2__3: w :e omega -> ap (Sigma omega (fun u:set => ap x (ordsucc u) + ap y (ordsucc u))) w < ap x (ordsucc z) + ap y (ordsucc z).
Admitted.

End Conj_real_add_SNo__2__3.
(** Conj_real_add_SNo__5__5 TMTp7b2uk8a3K12CPsiXeyQrZy98xCtJ2fc bounty of about 25 bars **)
Section Conj_real_add_SNo__5__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap x u < ap x v)).
Hypothesis H1: (forall u:set, u :e omega -> (forall v:set, v :e u -> ap y u < ap y v)).
Hypothesis H2: (forall u:set, u :e omega -> SNo (ap x (ordsucc u))).
Hypothesis H3: (forall u:set, u :e omega -> SNo (ap y (ordsucc u))).
Hypothesis H4: (forall u:set, u :e omega -> ap (Sigma omega (fun v:set => ap x (ordsucc v) + ap y (ordsucc v))) u = ap x (ordsucc u) + ap y (ordsucc u)).
Hypothesis H6: w :e z.
Theorem Conj_real_add_SNo__5__5: w :e omega -> (ap x (ordsucc z) + ap y (ordsucc z)) < ap (Sigma omega (fun u:set => ap x (ordsucc u) + ap y (ordsucc u))) w.
Admitted.

End Conj_real_add_SNo__5__5.
(** Conj_real_add_SNo__6__6 TMPYT7AKTm8ZDRenp4RckJ5dHQamX9YVnYF bounty of about 25 bars **)
Section Conj_real_add_SNo__6__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x + y).
Hypothesis H3: (forall v:set, v :e SNoS_ omega -> (forall x2:set, x2 :e omega -> abs_SNo (v + - y) < eps_ x2) -> v = y).
Hypothesis H4: (forall v:set, v :e omega -> SNo (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v)).
Hypothesis H5: (forall v:set, v :e omega -> (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v + - (eps_ v)) < x + y).
Hypothesis H7: y < u.
Hypothesis H8: u :e SNoS_ omega.
Hypothesis H9: ~ (exists v:set, v :e omega /\ ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v <= x + u).
Hypothesis H10: Empty < u + - y.
Theorem Conj_real_add_SNo__6__6: u <> y.
Admitted.

End Conj_real_add_SNo__6__6.
(** Conj_real_add_SNo__6__10 TMcutPj1p7BEhHoMCU1NxbLogVgoyXigBiv bounty of about 25 bars **)
Section Conj_real_add_SNo__6__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x + y).
Hypothesis H3: (forall v:set, v :e SNoS_ omega -> (forall x2:set, x2 :e omega -> abs_SNo (v + - y) < eps_ x2) -> v = y).
Hypothesis H4: (forall v:set, v :e omega -> SNo (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v)).
Hypothesis H5: (forall v:set, v :e omega -> (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v + - (eps_ v)) < x + y).
Hypothesis H6: SNo u.
Hypothesis H7: y < u.
Hypothesis H8: u :e SNoS_ omega.
Hypothesis H9: ~ (exists v:set, v :e omega /\ ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v <= x + u).
Theorem Conj_real_add_SNo__6__10: u <> y.
Admitted.

End Conj_real_add_SNo__6__10.
(** Conj_real_add_SNo__7__0 TMR6jCcdJ8uZFm4oSbAXDxCCk9SDMNQhv7V bounty of about 25 bars **)
Section Conj_real_add_SNo__7__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x + y).
Hypothesis H3: (forall v:set, v :e SNoS_ omega -> (forall x2:set, x2 :e omega -> abs_SNo (v + - y) < eps_ x2) -> v = y).
Hypothesis H4: (forall v:set, v :e omega -> SNo (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v)).
Hypothesis H5: (forall v:set, v :e omega -> (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v + - (eps_ v)) < x + y).
Hypothesis H6: SNo u.
Hypothesis H7: y < u.
Hypothesis H8: u :e SNoS_ omega.
Hypothesis H9: ~ (exists v:set, v :e omega /\ ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v <= x + u).
Theorem Conj_real_add_SNo__7__0: ~ Empty < u + - y.
Admitted.

End Conj_real_add_SNo__7__0.
(** Conj_real_add_SNo__8__0 TMVRVB6LkKJ6LRUedjjCz3VBX9nnB9NmnKQ bounty of about 25 bars **)
Section Conj_real_add_SNo__8__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x + y).
Hypothesis H3: (forall y2:set, y2 :e SNoS_ omega -> (forall z2:set, z2 :e omega -> abs_SNo (y2 + - y) < eps_ z2) -> y2 = y).
Hypothesis H4: (forall y2:set, y2 :e omega -> SNo (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2)).
Hypothesis H5: (forall y2:set, y2 :e omega -> (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2 + - (eps_ y2)) < x + y).
Hypothesis H6: SNo (SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2)))))).
Hypothesis H7: (forall y2:set, y2 :e Repl omega (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2)))) -> SNoCut (Repl omega (ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))))) (Repl omega (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))))) < y2).
Hypothesis H8: SNo x2.
Hypothesis H9: y < x2.
Hypothesis H10: x2 :e SNoS_ omega.
Theorem Conj_real_add_SNo__8__0: (exists y2:set, y2 :e omega /\ ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2 <= x + x2) -> SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))))) < x + x2.
Admitted.

End Conj_real_add_SNo__8__0.
(** Conj_real_add_SNo__8__6 TMcKdvaQqnTQBDhQ2wbEoJDhrQhXzwXbBEv bounty of about 25 bars **)
Section Conj_real_add_SNo__8__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x + y).
Hypothesis H3: (forall y2:set, y2 :e SNoS_ omega -> (forall z2:set, z2 :e omega -> abs_SNo (y2 + - y) < eps_ z2) -> y2 = y).
Hypothesis H4: (forall y2:set, y2 :e omega -> SNo (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2)).
Hypothesis H5: (forall y2:set, y2 :e omega -> (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2 + - (eps_ y2)) < x + y).
Hypothesis H7: (forall y2:set, y2 :e Repl omega (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2)))) -> SNoCut (Repl omega (ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))))) (Repl omega (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))))) < y2).
Hypothesis H8: SNo x2.
Hypothesis H9: y < x2.
Hypothesis H10: x2 :e SNoS_ omega.
Theorem Conj_real_add_SNo__8__6: (exists y2:set, y2 :e omega /\ ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2 <= x + x2) -> SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))))) < x + x2.
Admitted.

End Conj_real_add_SNo__8__6.
(** Conj_real_add_SNo__9__2 TMNCzjTkDm9KM6EXsMUe1o6HNF1Pq9HQh5K bounty of about 25 bars **)
Section Conj_real_add_SNo__9__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: y :e real.
Hypothesis H1: SNo x.
Hypothesis H3: SNo (x + y).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ omega -> (forall z2:set, z2 :e omega -> abs_SNo (y2 + - y) < eps_ z2) -> y2 = y).
Hypothesis H5: (forall y2:set, y2 :e omega -> SNo (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2)).
Hypothesis H6: (forall y2:set, y2 :e omega -> (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2 + - (eps_ y2)) < x + y).
Hypothesis H7: SNo (SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2)))))).
Hypothesis H8: (forall y2:set, y2 :e Repl omega (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2)))) -> SNoCut (Repl omega (ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))))) (Repl omega (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))))) < y2).
Hypothesis H9: SNo x2.
Hypothesis H10: SNoLev x2 :e SNoLev y.
Hypothesis H11: y < x2.
Theorem Conj_real_add_SNo__9__2: x2 :e SNoS_ omega -> SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))))) < x + x2.
Admitted.

End Conj_real_add_SNo__9__2.
(** Conj_real_add_SNo__10__7 TMUhQBASZxdMD4Z6pq4y6ukZd9yGPz536pF bounty of about 25 bars **)
Section Conj_real_add_SNo__10__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x + y).
Hypothesis H3: (forall v:set, v :e SNoS_ omega -> (forall x2:set, x2 :e omega -> abs_SNo (v + - x) < eps_ x2) -> v = x).
Hypothesis H4: (forall v:set, v :e omega -> SNo (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v)).
Hypothesis H5: (forall v:set, v :e omega -> (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v + - (eps_ v)) < x + y).
Hypothesis H6: SNo u.
Hypothesis H8: u :e SNoS_ omega.
Hypothesis H9: ~ (exists v:set, v :e omega /\ ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v <= u + y).
Hypothesis H10: Empty < u + - x.
Theorem Conj_real_add_SNo__10__7: u <> x.
Admitted.

End Conj_real_add_SNo__10__7.
(** Conj_real_add_SNo__13__2 TMbubgBGQb56FjAFGY6Sk9MsTyEFYBd92f4 bounty of about 25 bars **)
Section Conj_real_add_SNo__13__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: x :e real.
Hypothesis H1: SNo x.
Hypothesis H3: SNo (x + y).
Hypothesis H4: (forall y2:set, y2 :e SNoS_ omega -> (forall z2:set, z2 :e omega -> abs_SNo (y2 + - x) < eps_ z2) -> y2 = x).
Hypothesis H5: (forall y2:set, y2 :e omega -> SNo (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2)).
Hypothesis H6: (forall y2:set, y2 :e omega -> (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2 + - (eps_ y2)) < x + y).
Hypothesis H7: SNo (SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2)))))).
Hypothesis H8: (forall y2:set, y2 :e Repl omega (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2)))) -> SNoCut (Repl omega (ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))))) (Repl omega (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))))) < y2).
Hypothesis H9: SNo x2.
Hypothesis H10: SNoLev x2 :e SNoLev x.
Hypothesis H11: x < x2.
Theorem Conj_real_add_SNo__13__2: x2 :e SNoS_ omega -> SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))))) < x2 + y.
Admitted.

End Conj_real_add_SNo__13__2.
(** Conj_real_add_SNo__13__3 TMJjAfBJR2BCEBpjDvfZJcHAPeoXeYFCGsH bounty of about 25 bars **)
Section Conj_real_add_SNo__13__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: x :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H4: (forall y2:set, y2 :e SNoS_ omega -> (forall z2:set, z2 :e omega -> abs_SNo (y2 + - x) < eps_ z2) -> y2 = x).
Hypothesis H5: (forall y2:set, y2 :e omega -> SNo (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2)).
Hypothesis H6: (forall y2:set, y2 :e omega -> (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2 + - (eps_ y2)) < x + y).
Hypothesis H7: SNo (SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2)))))).
Hypothesis H8: (forall y2:set, y2 :e Repl omega (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2)))) -> SNoCut (Repl omega (ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))))) (Repl omega (ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))))) < y2).
Hypothesis H9: SNo x2.
Hypothesis H10: SNoLev x2 :e SNoLev x.
Hypothesis H11: x < x2.
Theorem Conj_real_add_SNo__13__3: x2 :e SNoS_ omega -> SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))))) < x2 + y.
Admitted.

End Conj_real_add_SNo__13__3.
(** Conj_real_add_SNo__18__2 TMNgBu2JEvCZcB9wgFUetHRjWVnSmsQgvWj bounty of about 25 bars **)
Section Conj_real_add_SNo__18__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall v:set, v :e SNoS_ omega -> (forall x2:set, x2 :e omega -> abs_SNo (v + - x) < eps_ x2) -> v = x).
Hypothesis H4: (forall v:set, v :e omega -> SNo (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v)).
Hypothesis H5: (forall v:set, v :e omega -> (x + y) < ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v + eps_ v).
Hypothesis H6: SNo u.
Hypothesis H7: u < x.
Hypothesis H8: u :e SNoS_ omega.
Hypothesis H9: ~ (exists v:set, v :e omega /\ (u + y) <= ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v).
Hypothesis H10: Empty < x + - u.
Theorem Conj_real_add_SNo__18__2: u <> x.
Admitted.

End Conj_real_add_SNo__18__2.
(** Conj_real_add_SNo__18__6 TMZUF197iJ9oJKmRN5swpsLonb89982xgBh bounty of about 25 bars **)
Section Conj_real_add_SNo__18__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x + y).
Hypothesis H3: (forall v:set, v :e SNoS_ omega -> (forall x2:set, x2 :e omega -> abs_SNo (v + - x) < eps_ x2) -> v = x).
Hypothesis H4: (forall v:set, v :e omega -> SNo (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v)).
Hypothesis H5: (forall v:set, v :e omega -> (x + y) < ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v + eps_ v).
Hypothesis H7: u < x.
Hypothesis H8: u :e SNoS_ omega.
Hypothesis H9: ~ (exists v:set, v :e omega /\ (u + y) <= ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap w (ordsucc x2))) v).
Hypothesis H10: Empty < x + - u.
Theorem Conj_real_add_SNo__18__6: u <> x.
Admitted.

End Conj_real_add_SNo__18__6.
(** Conj_real_add_SNo__22__6 TMMfHY9DHkkQLhfuL385WD4Pd4PNjpGi2py bounty of about 25 bars **)
Section Conj_real_add_SNo__22__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: SNo x.
Hypothesis H3: SNo y.
Hypothesis H4: SNo (x + y).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H7: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2)).
Hypothesis H9: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H10: Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H11: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 < x + y).
Hypothesis H12: (forall x2:set, x2 :e omega -> (x + y) < ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 + eps_ x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))) y2 < ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))) x2)).
Hypothesis H14: (forall x2:set, x2 :e omega -> (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 + - (eps_ x2)) < x + y).
Hypothesis H15: (forall x2:set, x2 :e omega -> (x + y) < ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2).
Hypothesis H16: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) x2 < ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2)).
Hypothesis H17: SNoCutP (Repl omega (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2))))) (Repl omega (ap (Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2))))).
Hypothesis H18: SNo (SNoCut (Repl omega (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2))))) (Repl omega (ap (Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)))))).
Hypothesis H19: (forall x2:set, x2 :e Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2)))) -> x2 < SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2)))))).
Hypothesis H20: (forall x2:set, x2 :e Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2)))) -> SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))))) < x2).
Theorem Conj_real_add_SNo__22__6: x + y = SNoCut (Repl omega (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2))))) (Repl omega (ap (Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2))))) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__22__6.
(** Conj_real_add_SNo__22__8 TMRE8qyWbSNbQhjhtxHrBmNEJWaW3aiz3QQ bounty of about 25 bars **)
Section Conj_real_add_SNo__22__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: SNo x.
Hypothesis H3: SNo y.
Hypothesis H4: SNo (x + y).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H6: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H7: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H9: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H10: Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H11: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 < x + y).
Hypothesis H12: (forall x2:set, x2 :e omega -> (x + y) < ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 + eps_ x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))) y2 < ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))) x2)).
Hypothesis H14: (forall x2:set, x2 :e omega -> (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 + - (eps_ x2)) < x + y).
Hypothesis H15: (forall x2:set, x2 :e omega -> (x + y) < ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2).
Hypothesis H16: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) x2 < ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2)).
Hypothesis H17: SNoCutP (Repl omega (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2))))) (Repl omega (ap (Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2))))).
Hypothesis H18: SNo (SNoCut (Repl omega (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2))))) (Repl omega (ap (Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)))))).
Hypothesis H19: (forall x2:set, x2 :e Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2)))) -> x2 < SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2)))))).
Hypothesis H20: (forall x2:set, x2 :e Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2)))) -> SNoCut (Repl omega (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))))) (Repl omega (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))))) < x2).
Theorem Conj_real_add_SNo__22__8: x + y = SNoCut (Repl omega (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2))))) (Repl omega (ap (Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2))))) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__22__8.
(** Conj_real_add_SNo__23__0 TMHfk5V5QAMcSuyEq9sd48Zx5om76E74M4b bounty of about 25 bars **)
Section Conj_real_add_SNo__23__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: y :e real.
Hypothesis H2: SNo x.
Hypothesis H3: SNo y.
Hypothesis H4: SNo (x + y).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H6: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H7: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2)).
Hypothesis H9: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H10: Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H11: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 < x + y).
Hypothesis H12: (forall x2:set, x2 :e omega -> (x + y) < ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 + eps_ x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))) y2 < ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))) x2)).
Hypothesis H14: (forall x2:set, x2 :e omega -> (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 + - (eps_ x2)) < x + y).
Hypothesis H15: (forall x2:set, x2 :e omega -> (x + y) < ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2).
Hypothesis H16: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) x2 < ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2)).
Theorem Conj_real_add_SNo__23__0: SNoCutP (Repl omega (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2))))) (Repl omega (ap (Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2))))) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__23__0.
(** Conj_real_add_SNo__23__14 TMP8AGa3dn6TjgAXCz4z6sWPX44PJ7TRRdy bounty of about 25 bars **)
Section Conj_real_add_SNo__23__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: SNo x.
Hypothesis H3: SNo y.
Hypothesis H4: SNo (x + y).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H6: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H7: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2)).
Hypothesis H9: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H10: Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H11: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 < x + y).
Hypothesis H12: (forall x2:set, x2 :e omega -> (x + y) < ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 + eps_ x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))) y2 < ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))) x2)).
Hypothesis H15: (forall x2:set, x2 :e omega -> (x + y) < ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2).
Hypothesis H16: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) x2 < ap (Sigma omega (fun z2:set => ap w (ordsucc z2) + ap v (ordsucc z2))) y2)).
Theorem Conj_real_add_SNo__23__14: SNoCutP (Repl omega (ap (Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2))))) (Repl omega (ap (Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2))))) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__23__14.
(** Conj_real_add_SNo__25__18 TMFZ684aFGcC14gyHxsH4mnmS9fddMK7BfV bounty of about 25 bars **)
Section Conj_real_add_SNo__25__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H3: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H4: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H5: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H6: SNo x.
Hypothesis H7: SNo y.
Hypothesis H8: SNo (x + y).
Hypothesis H9: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H10: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H11: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H12: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Hypothesis H13: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)).
Hypothesis H14: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H15: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2)).
Hypothesis H16: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H17: Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H19: (forall x2:set, x2 :e omega -> (x + y) < ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 + eps_ x2).
Hypothesis H20: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))) y2 < ap (Sigma omega (fun z2:set => ap z (ordsucc z2) + ap u (ordsucc z2))) x2)).
Hypothesis H21: (forall x2:set, x2 :e omega -> (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 + - (eps_ x2)) < x + y).
Theorem Conj_real_add_SNo__25__18: (forall x2:set, x2 :e omega -> (x + y) < ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__25__18.
(** Conj_real_add_SNo__29__8 TMat6shLMqqFVM477dyDXw2kK5voMr3tL9z bounty of about 25 bars **)
Section Conj_real_add_SNo__29__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)).
Hypothesis H24: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)).
Hypothesis H25: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H26: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2)).
Hypothesis H27: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H28: Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Theorem Conj_real_add_SNo__29__8: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 < x + y) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__29__8.
(** Conj_real_add_SNo__29__22 TMHG7ebV2M3ohAivbc5fb6xN5HdV12rWTmj bounty of about 25 bars **)
Section Conj_real_add_SNo__29__22.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)).
Hypothesis H24: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)).
Hypothesis H25: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H26: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2)).
Hypothesis H27: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Hypothesis H28: Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Theorem Conj_real_add_SNo__29__22: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 < x + y) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__29__22.
(** Conj_real_add_SNo__30__3 TMPv6ZcMeAauNtjJDDYXdy6WYmh7ae1r7G6 bounty of about 25 bars **)
Section Conj_real_add_SNo__30__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)).
Hypothesis H26: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)).
Hypothesis H27: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H28: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2)).
Hypothesis H29: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Theorem Conj_real_add_SNo__30__3: Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)) :e setexp (SNoS_ omega) omega -> x + y :e real.
Admitted.

End Conj_real_add_SNo__30__3.
(** Conj_real_add_SNo__30__7 TMU8GgMdeAeWc4FaLPrRbCFG5jRWPRw5i52 bounty of about 25 bars **)
Section Conj_real_add_SNo__30__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)).
Hypothesis H26: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)).
Hypothesis H27: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H28: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2)).
Hypothesis H29: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Theorem Conj_real_add_SNo__30__7: Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)) :e setexp (SNoS_ omega) omega -> x + y :e real.
Admitted.

End Conj_real_add_SNo__30__7.
(** Conj_real_add_SNo__30__28 TMY8mPx97j8budqs7BPUDFcPiFvvm8nVBer bounty of about 25 bars **)
Section Conj_real_add_SNo__30__28.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)).
Hypothesis H26: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)).
Hypothesis H27: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H29: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega.
Theorem Conj_real_add_SNo__30__28: Sigma omega (fun x2:set => ap w (ordsucc x2) + ap v (ordsucc x2)) :e setexp (SNoS_ omega) omega -> x + y :e real.
Admitted.

End Conj_real_add_SNo__30__28.
(** Conj_real_add_SNo__31__24 TMcukGxZvH5Gt5hxymjC34kVidJdBSYWzYT bounty of about 25 bars **)
Section Conj_real_add_SNo__31__24.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Hypothesis H26: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Hypothesis H27: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)).
Hypothesis H28: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)).
Hypothesis H29: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Hypothesis H30: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2)).
Theorem Conj_real_add_SNo__31__24: Sigma omega (fun x2:set => ap z (ordsucc x2) + ap u (ordsucc x2)) :e setexp (SNoS_ omega) omega -> x + y :e real.
Admitted.

End Conj_real_add_SNo__31__24.
(** Conj_real_add_SNo__32__17 TMYhmQBdaNCQ5YvMyKYfhaqoyGa4X46LPfK bounty of about 25 bars **)
Section Conj_real_add_SNo__32__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Hypothesis H26: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Hypothesis H27: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)).
Hypothesis H28: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)).
Hypothesis H29: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)).
Theorem Conj_real_add_SNo__32__17: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2)) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__32__17.
(** Conj_real_add_SNo__33__2 TMcV9f1TofHDH1Ap51HwQfmgPRXqyYD9yi6 bounty of about 25 bars **)
Section Conj_real_add_SNo__33__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Hypothesis H26: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Hypothesis H27: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)).
Hypothesis H28: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)).
Theorem Conj_real_add_SNo__33__2: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__33__2.
(** Conj_real_add_SNo__33__11 TMHaXqMyFUrjWzLSLqpjxXMkTkAyLeuZt5K bounty of about 25 bars **)
Section Conj_real_add_SNo__33__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Hypothesis H26: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Hypothesis H27: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)).
Hypothesis H28: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)).
Theorem Conj_real_add_SNo__33__11: (forall x2:set, x2 :e omega -> SNo (ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2)) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__33__11.
(** Conj_real_add_SNo__34__4 TMdKdU8EM1qpbuN9iiQwg6cKoRV25mabNK6 bounty of about 25 bars **)
Section Conj_real_add_SNo__34__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Hypothesis H26: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Hypothesis H27: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)).
Theorem Conj_real_add_SNo__34__4: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap w (ordsucc y2) + ap v (ordsucc y2))) x2 = ap w (ordsucc x2) + ap v (ordsucc x2)) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__34__4.
(** Conj_real_add_SNo__35__11 TMVVp78Q2iManYwP482mjH8hyRNRBzyLpqd bounty of about 25 bars **)
Section Conj_real_add_SNo__35__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Hypothesis H26: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Theorem Conj_real_add_SNo__35__11: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__35__11.
(** Conj_real_add_SNo__35__13 TMRZpkXjbKFxG2xpgu3XgZVmendfUCK8cKC bounty of about 25 bars **)
Section Conj_real_add_SNo__35__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Hypothesis H26: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))).
Theorem Conj_real_add_SNo__35__13: (forall x2:set, x2 :e omega -> ap (Sigma omega (fun y2:set => ap z (ordsucc y2) + ap u (ordsucc y2))) x2 = ap z (ordsucc x2) + ap u (ordsucc x2)) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__35__13.
(** Conj_real_add_SNo__36__12 TMN9Lrb9YoSKjsJvRQAJFtnFgBE2YHWUDvx bounty of about 25 bars **)
Section Conj_real_add_SNo__36__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H15: SNo y.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Theorem Conj_real_add_SNo__36__12: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__36__12.
(** Conj_real_add_SNo__36__15 TMUJHzSboRvs5p3twNn5rWCcUy8HvtzPP8U bounty of about 25 bars **)
Section Conj_real_add_SNo__36__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H9: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H10: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H11: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H14: SNo x.
Hypothesis H16: SNo (x + y).
Hypothesis H17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H20: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Hypothesis H25: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega).
Theorem Conj_real_add_SNo__36__15: (forall x2:set, x2 :e omega -> SNo (ap v (ordsucc x2))) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__36__15.
(** Conj_real_add_SNo__37__9 TMXa8dVQdR2FU851xv7aUWFv4U6fwEq9KDW bounty of about 25 bars **)
Section Conj_real_add_SNo__37__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H3: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H4: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H5: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H6: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H7: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H8: v :e setexp (SNoS_ omega) omega.
Hypothesis H10: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H11: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H12: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H13: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H14: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H15: SNo x.
Hypothesis H16: SNo y.
Hypothesis H17: SNo (x + y).
Hypothesis H18: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H19: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H20: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H21: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H22: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Hypothesis H23: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))).
Hypothesis H24: (forall x2:set, x2 :e omega -> ap w (ordsucc x2) :e SNoS_ omega).
Hypothesis H25: (forall x2:set, x2 :e omega -> SNo (ap w (ordsucc x2))).
Theorem Conj_real_add_SNo__37__9: (forall x2:set, x2 :e omega -> ap v (ordsucc x2) :e SNoS_ omega) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__37__9.
(** Conj_real_add_SNo__40__2 TMYC36yyWQW49XmeDviv565hfZycrUiCJCk bounty of about 25 bars **)
Section Conj_real_add_SNo__40__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H3: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H4: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H5: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H6: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H7: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H8: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H9: v :e setexp (SNoS_ omega) omega.
Hypothesis H10: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H11: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H12: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H13: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H14: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H15: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H16: SNo x.
Hypothesis H17: SNo y.
Hypothesis H18: SNo (x + y).
Hypothesis H19: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H20: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Theorem Conj_real_add_SNo__40__2: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__40__2.
(** Conj_real_add_SNo__40__19 TMZfkmk6NcG8xR5Ud7AWKGjhDQP8iSkvRK1 bounty of about 25 bars **)
Section Conj_real_add_SNo__40__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: w :e setexp (SNoS_ omega) omega.
Hypothesis H3: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H4: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H5: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H6: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H7: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H8: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H9: v :e setexp (SNoS_ omega) omega.
Hypothesis H10: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H11: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H12: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H13: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H14: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H15: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H16: SNo x.
Hypothesis H17: SNo y.
Hypothesis H18: SNo (x + y).
Hypothesis H20: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega).
Theorem Conj_real_add_SNo__40__19: (forall x2:set, x2 :e omega -> SNo (ap u (ordsucc x2))) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__40__19.
(** Conj_real_add_SNo__41__9 TMNyvLxZjov9Rr7KWfZ6VyyLZXXfDxtbfaF bounty of about 25 bars **)
Section Conj_real_add_SNo__41__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: w :e setexp (SNoS_ omega) omega.
Hypothesis H3: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H4: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H5: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H6: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H7: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H8: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H10: v :e setexp (SNoS_ omega) omega.
Hypothesis H11: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H12: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H13: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H14: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H15: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H16: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: SNo x.
Hypothesis H18: SNo y.
Hypothesis H19: SNo (x + y).
Hypothesis H20: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H21: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Hypothesis H22: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega).
Hypothesis H23: (forall x2:set, x2 :e omega -> SNo (ap z (ordsucc x2))).
Theorem Conj_real_add_SNo__41__9: (forall x2:set, x2 :e omega -> ap u (ordsucc x2) :e SNoS_ omega) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__41__9.
(** Conj_real_add_SNo__43__10 TMdcsc7WySVWmkDzvUMW2koxhrFHDWv1peg bounty of about 25 bars **)
Section Conj_real_add_SNo__43__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: w :e setexp (SNoS_ omega) omega.
Hypothesis H4: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H5: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H6: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H7: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H8: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H9: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H11: v :e setexp (SNoS_ omega) omega.
Hypothesis H12: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H13: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H14: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H16: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H17: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H18: SNo x.
Hypothesis H19: SNo y.
Hypothesis H20: SNo (x + y).
Hypothesis H21: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Hypothesis H22: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y).
Theorem Conj_real_add_SNo__43__10: (forall x2:set, x2 :e omega -> ap z (ordsucc x2) :e SNoS_ omega) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__43__10.
(** Conj_real_add_SNo__44__7 TMWLEHzGuRdxrrLLxYp758pqDH36E1hiHuR bounty of about 25 bars **)
Section Conj_real_add_SNo__44__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: w :e setexp (SNoS_ omega) omega.
Hypothesis H4: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H5: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H6: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H8: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H9: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H10: u :e setexp (SNoS_ omega) omega.
Hypothesis H11: v :e setexp (SNoS_ omega) omega.
Hypothesis H12: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H13: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H14: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H16: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H17: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H18: SNo x.
Hypothesis H19: SNo y.
Hypothesis H20: SNo (x + y).
Hypothesis H21: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Theorem Conj_real_add_SNo__44__7: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__44__7.
(** Conj_real_add_SNo__44__17 TMP1pdCmpoHmjLBEhtcJ1qU2476ayGsf6Rg bounty of about 25 bars **)
Section Conj_real_add_SNo__44__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: w :e setexp (SNoS_ omega) omega.
Hypothesis H4: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H5: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H6: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H7: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H8: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H9: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H10: u :e setexp (SNoS_ omega) omega.
Hypothesis H11: v :e setexp (SNoS_ omega) omega.
Hypothesis H12: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H13: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H14: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H16: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H18: SNo x.
Hypothesis H19: SNo y.
Hypothesis H20: SNo (x + y).
Hypothesis H21: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x).
Theorem Conj_real_add_SNo__44__17: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - y) < eps_ y2) -> x2 = y) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__44__17.
(** Conj_real_add_SNo__45__16 TMF6wjz8SL3jYRfAj2p7WabkRVMuVk7UDL2 bounty of about 25 bars **)
Section Conj_real_add_SNo__45__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: w :e setexp (SNoS_ omega) omega.
Hypothesis H4: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H5: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H6: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H7: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H8: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H9: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H10: u :e setexp (SNoS_ omega) omega.
Hypothesis H11: v :e setexp (SNoS_ omega) omega.
Hypothesis H12: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H13: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H14: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H17: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H18: SNo x.
Hypothesis H19: SNo y.
Hypothesis H20: SNo (x + y).
Theorem Conj_real_add_SNo__45__16: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__45__16.
(** Conj_real_add_SNo__45__20 TMQEqcrSDRbzRZhrJ9mp34cWbshw9QNtM25 bounty of about 25 bars **)
Section Conj_real_add_SNo__45__20.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: x :e real.
Hypothesis H1: y :e real.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: w :e setexp (SNoS_ omega) omega.
Hypothesis H4: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H5: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H6: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H7: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H8: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H9: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H10: u :e setexp (SNoS_ omega) omega.
Hypothesis H11: v :e setexp (SNoS_ omega) omega.
Hypothesis H12: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H13: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H14: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H16: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H17: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H18: SNo x.
Hypothesis H19: SNo y.
Theorem Conj_real_add_SNo__45__20: (forall x2:set, x2 :e SNoS_ omega -> (forall y2:set, y2 :e omega -> abs_SNo (x2 + - x) < eps_ y2) -> x2 = x) -> x + y :e real.
Admitted.

End Conj_real_add_SNo__45__20.
(** Conj_real_add_SNo__47__0 TMMkXNLbgNQec4JiiWQcHFeBpec3r7HMBXE bounty of about 25 bars **)

Section Conj_real_add_SNo__47__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: y :e real.
Hypothesis H2: z :e setexp (SNoS_ omega) omega.
Hypothesis H3: w :e setexp (SNoS_ omega) omega.
Hypothesis H4: (forall x2:set, x2 :e omega -> ap z x2 < x).
Hypothesis H5: (forall x2:set, x2 :e omega -> x < ap z x2 + eps_ x2).
Hypothesis H6: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap z y2 < ap z x2)).
Hypothesis H7: (forall x2:set, x2 :e omega -> (ap w x2 + - (eps_ x2)) < x).
Hypothesis H8: (forall x2:set, x2 :e omega -> x < ap w x2).
Hypothesis H9: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap w x2 < ap w y2)).
Hypothesis H10: u :e setexp (SNoS_ omega) omega.
Hypothesis H11: v :e setexp (SNoS_ omega) omega.
Hypothesis H12: (forall x2:set, x2 :e omega -> ap u x2 < y).
Hypothesis H13: (forall x2:set, x2 :e omega -> y < ap u x2 + eps_ x2).
Hypothesis H14: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < y).
Hypothesis H16: (forall x2:set, x2 :e omega -> y < ap v x2).
Hypothesis H17: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H18: SNo x.
Theorem Conj_real_add_SNo__47__0: SNo y -> x + y :e real.
Admitted.

End Conj_real_add_SNo__47__0.
(** Conj_real_mul_SNo_pos__2__2 TMb4ztu1T6aUoRsXHk5bjqZpAzV7JyhzaqD bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__2__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Hypothesis H22: SNo (eps_ (v + x2)).
Hypothesis H23: SNo (eps_ v * eps_ x2).
Theorem Conj_real_mul_SNo_pos__2__2: ~ abs_SNo (z + - (x * y)) < eps_ (v + x2).
Admitted.

End Conj_real_mul_SNo_pos__2__2.
(** Conj_real_mul_SNo_pos__2__11 TMFM8ZbbSYeDy53rtbd5SSEbiDNEnsfz1BS bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__2__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Hypothesis H22: SNo (eps_ (v + x2)).
Hypothesis H23: SNo (eps_ v * eps_ x2).
Theorem Conj_real_mul_SNo_pos__2__11: ~ abs_SNo (z + - (x * y)) < eps_ (v + x2).
Admitted.

End Conj_real_mul_SNo_pos__2__11.
(** Conj_real_mul_SNo_pos__2__21 TMWPj3bQPLDXep6XXWqJnJs6kKq2HvTmJYp bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__2__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Hypothesis H20: SNo (eps_ v).
Hypothesis H22: SNo (eps_ (v + x2)).
Hypothesis H23: SNo (eps_ v * eps_ x2).
Theorem Conj_real_mul_SNo_pos__2__21: ~ abs_SNo (z + - (x * y)) < eps_ (v + x2).
Admitted.

End Conj_real_mul_SNo_pos__2__21.
(** Conj_real_mul_SNo_pos__2__22 TMaBTxesneNG5zLQDtKz7BxTRpPkLow3kRB bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__2__22.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Hypothesis H23: SNo (eps_ v * eps_ x2).
Theorem Conj_real_mul_SNo_pos__2__22: ~ abs_SNo (z + - (x * y)) < eps_ (v + x2).
Admitted.

End Conj_real_mul_SNo_pos__2__22.
(** Conj_real_mul_SNo_pos__4__10 TMLyZM9FMgRqhmRP4eGmH9Xp3X9gL6oQp73 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__4__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Hypothesis H22: v + x2 :e omega.
Theorem Conj_real_mul_SNo_pos__4__10: ~ SNo (eps_ (v + x2)).
Admitted.

End Conj_real_mul_SNo_pos__4__10.
(** Conj_real_mul_SNo_pos__5__1 TMGh3q8JL8T1Pe71mKC1zsxP6Q6ErhB1hyW bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__5__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Theorem Conj_real_mul_SNo_pos__5__1: ~ v + x2 :e omega.
Admitted.

End Conj_real_mul_SNo_pos__5__1.
(** Conj_real_mul_SNo_pos__5__5 TMbBxx9inTYvuet9seEqFKtvL67jbravsAQ bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__5__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Theorem Conj_real_mul_SNo_pos__5__5: ~ v + x2 :e omega.
Admitted.

End Conj_real_mul_SNo_pos__5__5.
(** Conj_real_mul_SNo_pos__5__21 TMUWSJ3sGfREd4hHR7JHvr2FLLQ8x7HhdNP bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__5__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Hypothesis H20: SNo (eps_ v).
Theorem Conj_real_mul_SNo_pos__5__21: ~ v + x2 :e omega.
Admitted.

End Conj_real_mul_SNo_pos__5__21.
(** Conj_real_mul_SNo_pos__6__13 TMVFDSCjDVngrWZ8ybhbRjcLwaZ6RWAfYd4 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__6__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Hypothesis H20: SNo (eps_ v).
Theorem Conj_real_mul_SNo_pos__6__13: ~ SNo (eps_ x2).
Admitted.

End Conj_real_mul_SNo_pos__6__13.
(** Conj_real_mul_SNo_pos__7__0 TMGPW4R8amVWgLbbWSAXsr5RuxxYEMR1M4o bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__7__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Theorem Conj_real_mul_SNo_pos__7__0: ~ SNo (eps_ v).
Admitted.

End Conj_real_mul_SNo_pos__7__0.
(** Conj_real_mul_SNo_pos__7__5 TMTgXSvTiZRooyMMizKBB4tvfP2vTL1yTc1 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__7__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (y + - u).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= y + - u.
Theorem Conj_real_mul_SNo_pos__7__5: ~ SNo (eps_ v).
Admitted.

End Conj_real_mul_SNo_pos__7__5.
(** Conj_real_mul_SNo_pos__8__14 TMZ6hiRV6xT2hvHLa2FfnWjQp3eq7oiai5Z bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__8__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoR x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - x -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoL y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= y + - v -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: x * y < z.
Hypothesis H9: w :e SNoR x.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (w * y + x * u) <= z + w * u.
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (w * u).
Hypothesis H17: SNo (- (w * u)).
Hypothesis H18: SNo (w + - x).
Theorem Conj_real_mul_SNo_pos__8__14: ~ SNo (y + - u).
Admitted.

End Conj_real_mul_SNo_pos__8__14.
(** Conj_real_mul_SNo_pos__10__3 TMJk2xTp8Z1gdjk25uUkbgYSN6hzymi3HZF bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__10__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H4: (forall v:set, v :e SNoR x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - x -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoL y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= y + - v -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: x * y < z.
Hypothesis H9: w :e SNoR x.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (w * y + x * u) <= z + w * u.
Hypothesis H14: SNo (w * y).
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (w * u).
Theorem Conj_real_mul_SNo_pos__10__3: ~ SNo (- (w * u)).
Admitted.

End Conj_real_mul_SNo_pos__10__3.
(** Conj_real_mul_SNo_pos__10__12 TMZZUwten3tHmhroqv8p7yhinoi8xZn6rkY bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__10__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoR x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - x -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoL y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= y + - v -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: x * y < z.
Hypothesis H9: w :e SNoR x.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: SNo w.
Hypothesis H13: (w * y + x * u) <= z + w * u.
Hypothesis H14: SNo (w * y).
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (w * u).
Theorem Conj_real_mul_SNo_pos__10__12: ~ SNo (- (w * u)).
Admitted.

End Conj_real_mul_SNo_pos__10__12.
(** Conj_real_mul_SNo_pos__14__9 TMY1tpSZgY6XRiPYNoCJDRCtn3mCZgeL7Nj bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__14__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: SNo z.
Hypothesis H5: x * y < z.
Hypothesis H6: SNo w.
Hypothesis H7: SNo u.
Hypothesis H8: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (x * u).
Hypothesis H11: SNo (w * u).
Hypothesis H12: SNo (- (w * u)).
Hypothesis H13: SNo (x + - w).
Hypothesis H14: SNo (u + - y).
Hypothesis H15: v :e omega.
Hypothesis H16: eps_ v <= x + - w.
Hypothesis H17: x2 :e omega.
Hypothesis H18: eps_ x2 <= u + - y.
Hypothesis H19: SNo (eps_ v).
Hypothesis H20: SNo (eps_ x2).
Hypothesis H21: SNo (eps_ (v + x2)).
Hypothesis H22: SNo (eps_ v * eps_ x2).
Hypothesis H23: abs_SNo (z + - (x * y)) < eps_ (v + x2).
Theorem Conj_real_mul_SNo_pos__14__9: ~ eps_ (v + x2) <= abs_SNo (z + - (x * y)).
Admitted.

End Conj_real_mul_SNo_pos__14__9.
(** Conj_real_mul_SNo_pos__15__5 TMVTHJvz3E8kP8Q8KC7KS6ESFKnWLyXf8pQ bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__15__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (x + - w).
Hypothesis H15: SNo (u + - y).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= x + - w.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= u + - y.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Hypothesis H22: SNo (eps_ (v + x2)).
Hypothesis H23: SNo (eps_ v * eps_ x2).
Theorem Conj_real_mul_SNo_pos__15__5: ~ abs_SNo (z + - (x * y)) < eps_ (v + x2).
Admitted.

End Conj_real_mul_SNo_pos__15__5.
(** Conj_real_mul_SNo_pos__15__11 TMY8rTwN7TPhJTjrC5UDuE1yZ1JxjaoScer bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__15__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (x + - w).
Hypothesis H15: SNo (u + - y).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= x + - w.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= u + - y.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Hypothesis H22: SNo (eps_ (v + x2)).
Hypothesis H23: SNo (eps_ v * eps_ x2).
Theorem Conj_real_mul_SNo_pos__15__11: ~ abs_SNo (z + - (x * y)) < eps_ (v + x2).
Admitted.

End Conj_real_mul_SNo_pos__15__11.
(** Conj_real_mul_SNo_pos__15__12 TMRJ5fZJJiUNMLJxr7fEuPgWwF7yJ8sGoay bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__15__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (x + - w).
Hypothesis H15: SNo (u + - y).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= x + - w.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= u + - y.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Hypothesis H22: SNo (eps_ (v + x2)).
Hypothesis H23: SNo (eps_ v * eps_ x2).
Theorem Conj_real_mul_SNo_pos__15__12: ~ abs_SNo (z + - (x * y)) < eps_ (v + x2).
Admitted.

End Conj_real_mul_SNo_pos__15__12.
(** Conj_real_mul_SNo_pos__17__10 TMTvNDCJynJbCyvB5gSCXQozGi1wJQNoZJK bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__17__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (x + - w).
Hypothesis H15: SNo (u + - y).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= x + - w.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= u + - y.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Hypothesis H22: v + x2 :e omega.
Theorem Conj_real_mul_SNo_pos__17__10: ~ SNo (eps_ (v + x2)).
Admitted.

End Conj_real_mul_SNo_pos__17__10.
(** Conj_real_mul_SNo_pos__18__5 TMJg9eWN7w96gpt7G9geW9bvV926d8YF8bt bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__18__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (x + - w).
Hypothesis H15: SNo (u + - y).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= x + - w.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= u + - y.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Theorem Conj_real_mul_SNo_pos__18__5: ~ v + x2 :e omega.
Admitted.

End Conj_real_mul_SNo_pos__18__5.
(** Conj_real_mul_SNo_pos__18__21 TMdwoJGHjwa3Tpbb9Spo6kG2FoSpZEb1D8b bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__18__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: x * y < z.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (w * y + x * u) <= z + w * u.
Hypothesis H10: SNo (w * y).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (w * u).
Hypothesis H13: SNo (- (w * u)).
Hypothesis H14: SNo (x + - w).
Hypothesis H15: SNo (u + - y).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= x + - w.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= u + - y.
Hypothesis H20: SNo (eps_ v).
Theorem Conj_real_mul_SNo_pos__18__21: ~ v + x2 :e omega.
Admitted.

End Conj_real_mul_SNo_pos__18__21.
(** Conj_real_mul_SNo_pos__21__1 TMU8Uj3WpVgm1oRxdn2aZCqXW87rKBhF7VJ bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__21__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= x + - v -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoR y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - y -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: x * y < z.
Hypothesis H9: w :e SNoL x.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (w * y + x * u) <= z + w * u.
Hypothesis H14: SNo (w * y).
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (w * u).
Hypothesis H17: SNo (- (w * u)).
Hypothesis H18: SNo (x + - w).
Theorem Conj_real_mul_SNo_pos__21__1: ~ SNo (u + - y).
Admitted.

End Conj_real_mul_SNo_pos__21__1.
(** Conj_real_mul_SNo_pos__21__2 TMJc1UE2We1XxAP1ChnE1hzVLoKxmC1ZqLm bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__21__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= x + - v -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoR y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - y -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: x * y < z.
Hypothesis H9: w :e SNoL x.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (w * y + x * u) <= z + w * u.
Hypothesis H14: SNo (w * y).
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (w * u).
Hypothesis H17: SNo (- (w * u)).
Hypothesis H18: SNo (x + - w).
Theorem Conj_real_mul_SNo_pos__21__2: ~ SNo (u + - y).
Admitted.

End Conj_real_mul_SNo_pos__21__2.
(** Conj_real_mul_SNo_pos__25__1 TMHqD2hPSYEnFQ1Uoe1fbZwJmPxZNMJX869 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__25__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= x + - v -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoR y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - y -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: x * y < z.
Hypothesis H9: w :e SNoL x.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (w * y + x * u) <= z + w * u.
Hypothesis H14: SNo (w * y).
Hypothesis H15: SNo (x * u).
Theorem Conj_real_mul_SNo_pos__25__1: ~ SNo (- (x * u)).
Admitted.

End Conj_real_mul_SNo_pos__25__1.
(** Conj_real_mul_SNo_pos__29__9 TMdAwAJr93jDFZPDQTVqKbs76b8CwaYUmbk bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__29__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo z.
Hypothesis H4: z < x * y.
Hypothesis H5: SNo w.
Hypothesis H6: SNo u.
Hypothesis H7: (z + w * u) <= w * y + x * u.
Hypothesis H8: SNo (w * u).
Hypothesis H10: SNo (- (x * u)).
Hypothesis H11: SNo (w * y).
Hypothesis H12: SNo (- (w * y)).
Hypothesis H13: SNo (w + - x).
Hypothesis H14: SNo (u + - y).
Hypothesis H15: v :e omega.
Hypothesis H16: eps_ v <= w + - x.
Hypothesis H17: x2 :e omega.
Hypothesis H18: eps_ x2 <= u + - y.
Hypothesis H19: SNo (eps_ v).
Hypothesis H20: SNo (eps_ x2).
Hypothesis H21: SNo (eps_ (v + x2)).
Hypothesis H22: SNo (eps_ v * eps_ x2).
Hypothesis H23: abs_SNo (z + - (x * y)) < eps_ (v + x2).
Theorem Conj_real_mul_SNo_pos__29__9: ~ eps_ (v + x2) <= abs_SNo (z + - (x * y)).
Admitted.

End Conj_real_mul_SNo_pos__29__9.
(** Conj_real_mul_SNo_pos__30__12 TMbVKHnebTA6auFRf2Lj3UvPJVBMgVkSFus bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__30__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H4: SNo z.
Hypothesis H5: z < x * y.
Hypothesis H6: SNo w.
Hypothesis H7: SNo u.
Hypothesis H8: (z + w * u) <= w * y + x * u.
Hypothesis H9: SNo (w * u).
Hypothesis H10: SNo (x * u).
Hypothesis H11: SNo (- (x * u)).
Hypothesis H13: SNo (- (w * y)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (u + - y).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= u + - y.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Hypothesis H22: SNo (eps_ (v + x2)).
Hypothesis H23: SNo (eps_ v * eps_ x2).
Theorem Conj_real_mul_SNo_pos__30__12: ~ abs_SNo (z + - (x * y)) < eps_ (v + x2).
Admitted.

End Conj_real_mul_SNo_pos__30__12.
(** Conj_real_mul_SNo_pos__30__15 TMGNvxnvGL2gNd6LPmhtDjstjLZmWk8RDRM bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__30__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H4: SNo z.
Hypothesis H5: z < x * y.
Hypothesis H6: SNo w.
Hypothesis H7: SNo u.
Hypothesis H8: (z + w * u) <= w * y + x * u.
Hypothesis H9: SNo (w * u).
Hypothesis H10: SNo (x * u).
Hypothesis H11: SNo (- (x * u)).
Hypothesis H12: SNo (w * y).
Hypothesis H13: SNo (- (w * y)).
Hypothesis H14: SNo (w + - x).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= u + - y.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Hypothesis H22: SNo (eps_ (v + x2)).
Hypothesis H23: SNo (eps_ v * eps_ x2).
Theorem Conj_real_mul_SNo_pos__30__15: ~ abs_SNo (z + - (x * y)) < eps_ (v + x2).
Admitted.

End Conj_real_mul_SNo_pos__30__15.
(** Conj_real_mul_SNo_pos__33__1 TMGxdnezSHvuVpEkkijxJP1AqL4SD42CZZA bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__33__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H4: SNo z.
Hypothesis H5: z < x * y.
Hypothesis H6: SNo w.
Hypothesis H7: SNo u.
Hypothesis H8: (z + w * u) <= w * y + x * u.
Hypothesis H9: SNo (w * u).
Hypothesis H10: SNo (x * u).
Hypothesis H11: SNo (- (x * u)).
Hypothesis H12: SNo (w * y).
Hypothesis H13: SNo (- (w * y)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (u + - y).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= u + - y.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Theorem Conj_real_mul_SNo_pos__33__1: ~ v + x2 :e omega.
Admitted.

End Conj_real_mul_SNo_pos__33__1.
(** Conj_real_mul_SNo_pos__33__18 TMbsMfp8uUjr35AURGbebxrLstwB8Qy8vbb bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__33__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H4: SNo z.
Hypothesis H5: z < x * y.
Hypothesis H6: SNo w.
Hypothesis H7: SNo u.
Hypothesis H8: (z + w * u) <= w * y + x * u.
Hypothesis H9: SNo (w * u).
Hypothesis H10: SNo (x * u).
Hypothesis H11: SNo (- (x * u)).
Hypothesis H12: SNo (w * y).
Hypothesis H13: SNo (- (w * y)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (u + - y).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H19: eps_ x2 <= u + - y.
Hypothesis H20: SNo (eps_ v).
Hypothesis H21: SNo (eps_ x2).
Theorem Conj_real_mul_SNo_pos__33__18: ~ v + x2 :e omega.
Admitted.

End Conj_real_mul_SNo_pos__33__18.
(** Conj_real_mul_SNo_pos__35__9 TMHX3c35GpCLQaC7FnwyH1dYAryEk5DHK7E bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__35__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H4: SNo z.
Hypothesis H5: z < x * y.
Hypothesis H6: SNo w.
Hypothesis H7: SNo u.
Hypothesis H8: (z + w * u) <= w * y + x * u.
Hypothesis H10: SNo (x * u).
Hypothesis H11: SNo (- (x * u)).
Hypothesis H12: SNo (w * y).
Hypothesis H13: SNo (- (w * y)).
Hypothesis H14: SNo (w + - x).
Hypothesis H15: SNo (u + - y).
Hypothesis H16: v :e omega.
Hypothesis H17: eps_ v <= w + - x.
Hypothesis H18: x2 :e omega.
Hypothesis H19: eps_ x2 <= u + - y.
Theorem Conj_real_mul_SNo_pos__35__9: ~ SNo (eps_ v).
Admitted.

End Conj_real_mul_SNo_pos__35__9.
(** Conj_real_mul_SNo_pos__36__0 TMUbRVYkPzwZB7HBhn899BWwEEBYw4oMAsD bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__36__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall v:set, v :e SNoR x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - x -> P) -> P)).
Hypothesis H4: (forall v:set, v :e SNoR y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - y -> P) -> P)).
Hypothesis H5: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H6: SNo z.
Hypothesis H7: z < x * y.
Hypothesis H8: w :e SNoR x.
Hypothesis H9: u :e SNoR y.
Hypothesis H10: SNo w.
Hypothesis H11: SNo u.
Hypothesis H12: (z + w * u) <= w * y + x * u.
Hypothesis H13: SNo (w * u).
Hypothesis H14: SNo (x * u).
Hypothesis H15: SNo (- (x * u)).
Hypothesis H16: SNo (w * y).
Hypothesis H17: SNo (- (w * y)).
Hypothesis H18: SNo (w + - x).
Theorem Conj_real_mul_SNo_pos__36__0: ~ SNo (u + - y).
Admitted.

End Conj_real_mul_SNo_pos__36__0.
(** Conj_real_mul_SNo_pos__39__9 TMHLqNZ98TqtpoUAp3NgQd55oe9zJzHAcWJ bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__39__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall v:set, v :e SNoR x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - x -> P) -> P)).
Hypothesis H4: (forall v:set, v :e SNoR y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - y -> P) -> P)).
Hypothesis H5: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H6: SNo z.
Hypothesis H7: z < x * y.
Hypothesis H8: w :e SNoR x.
Hypothesis H10: SNo w.
Hypothesis H11: SNo u.
Hypothesis H12: (z + w * u) <= w * y + x * u.
Hypothesis H13: SNo (w * u).
Hypothesis H14: SNo (x * u).
Hypothesis H15: SNo (- (x * u)).
Theorem Conj_real_mul_SNo_pos__39__9: ~ SNo (w * y).
Admitted.

End Conj_real_mul_SNo_pos__39__9.
(** Conj_real_mul_SNo_pos__39__12 TMTreUTv1VUcD9KsjMsDSa6TeFNnNraYgSZ bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__39__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall v:set, v :e SNoR x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - x -> P) -> P)).
Hypothesis H4: (forall v:set, v :e SNoR y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - y -> P) -> P)).
Hypothesis H5: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H6: SNo z.
Hypothesis H7: z < x * y.
Hypothesis H8: w :e SNoR x.
Hypothesis H9: u :e SNoR y.
Hypothesis H10: SNo w.
Hypothesis H11: SNo u.
Hypothesis H13: SNo (w * u).
Hypothesis H14: SNo (x * u).
Hypothesis H15: SNo (- (x * u)).
Theorem Conj_real_mul_SNo_pos__39__12: ~ SNo (w * y).
Admitted.

End Conj_real_mul_SNo_pos__39__12.
(** Conj_real_mul_SNo_pos__41__1 TMZhhNJ4CPyemyKZQA28mCyT6Jq4LN5FBzn bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__41__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall v:set, v :e SNoR x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - x -> P) -> P)).
Hypothesis H4: (forall v:set, v :e SNoR y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - y -> P) -> P)).
Hypothesis H5: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H6: SNo z.
Hypothesis H7: z < x * y.
Hypothesis H8: w :e SNoR x.
Hypothesis H9: u :e SNoR y.
Hypothesis H10: SNo w.
Hypothesis H11: SNo u.
Hypothesis H12: (z + w * u) <= w * y + x * u.
Hypothesis H13: SNo (w * u).
Theorem Conj_real_mul_SNo_pos__41__1: ~ SNo (x * u).
Admitted.

End Conj_real_mul_SNo_pos__41__1.
(** Conj_real_mul_SNo_pos__42__3 TMdDayLHAHaYYYkgCRwvjvF5qVtCVZUuVEh bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__42__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H4: (forall v:set, v :e SNoR y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= v + - y -> P) -> P)).
Hypothesis H5: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H6: SNo z.
Hypothesis H7: z < x * y.
Hypothesis H8: w :e SNoR x.
Hypothesis H9: u :e SNoR y.
Hypothesis H10: SNo w.
Hypothesis H11: SNo u.
Hypothesis H12: (z + w * u) <= w * y + x * u.
Theorem Conj_real_mul_SNo_pos__42__3: ~ SNo (w * u).
Admitted.

End Conj_real_mul_SNo_pos__42__3.
(** Conj_real_mul_SNo_pos__45__5 TMMaH8G3p6NukY7R89XeVXfbrVfp3FVEJt5 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__45__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H6: z < x * y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (z + w * u) <= w * y + x * u.
Hypothesis H10: SNo (w * u).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (- (x * u)).
Hypothesis H13: SNo (w * y).
Hypothesis H14: SNo (- (w * y)).
Hypothesis H15: SNo (x + - w).
Hypothesis H16: SNo (y + - u).
Hypothesis H17: v :e omega.
Hypothesis H18: eps_ v <= x + - w.
Hypothesis H19: x2 :e omega.
Hypothesis H20: eps_ x2 <= y + - u.
Hypothesis H21: SNo (eps_ v).
Hypothesis H22: SNo (eps_ x2).
Hypothesis H23: SNo (eps_ (v + x2)).
Theorem Conj_real_mul_SNo_pos__45__5: ~ SNo (eps_ v * eps_ x2).
Admitted.

End Conj_real_mul_SNo_pos__45__5.
(** Conj_real_mul_SNo_pos__45__14 TMWep4wb7N1D7DUhDbEUqQPLpt46uVxFQw3 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__45__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: z < x * y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (z + w * u) <= w * y + x * u.
Hypothesis H10: SNo (w * u).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (- (x * u)).
Hypothesis H13: SNo (w * y).
Hypothesis H15: SNo (x + - w).
Hypothesis H16: SNo (y + - u).
Hypothesis H17: v :e omega.
Hypothesis H18: eps_ v <= x + - w.
Hypothesis H19: x2 :e omega.
Hypothesis H20: eps_ x2 <= y + - u.
Hypothesis H21: SNo (eps_ v).
Hypothesis H22: SNo (eps_ x2).
Hypothesis H23: SNo (eps_ (v + x2)).
Theorem Conj_real_mul_SNo_pos__45__14: ~ SNo (eps_ v * eps_ x2).
Admitted.

End Conj_real_mul_SNo_pos__45__14.
(** Conj_real_mul_SNo_pos__46__12 TMZuHFCgKcUJSppYycU4VP78mJhFFbTpLcx bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__46__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: z < x * y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (z + w * u) <= w * y + x * u.
Hypothesis H10: SNo (w * u).
Hypothesis H11: SNo (x * u).
Hypothesis H13: SNo (w * y).
Hypothesis H14: SNo (- (w * y)).
Hypothesis H15: SNo (x + - w).
Hypothesis H16: SNo (y + - u).
Hypothesis H17: v :e omega.
Hypothesis H18: eps_ v <= x + - w.
Hypothesis H19: x2 :e omega.
Hypothesis H20: eps_ x2 <= y + - u.
Hypothesis H21: SNo (eps_ v).
Hypothesis H22: SNo (eps_ x2).
Hypothesis H23: v + x2 :e omega.
Theorem Conj_real_mul_SNo_pos__46__12: ~ SNo (eps_ (v + x2)).
Admitted.

End Conj_real_mul_SNo_pos__46__12.
(** Conj_real_mul_SNo_pos__46__18 TMJPiMxCDJjw17ncKHMwSA17aWfa48YmMRj bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__46__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: z < x * y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (z + w * u) <= w * y + x * u.
Hypothesis H10: SNo (w * u).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (- (x * u)).
Hypothesis H13: SNo (w * y).
Hypothesis H14: SNo (- (w * y)).
Hypothesis H15: SNo (x + - w).
Hypothesis H16: SNo (y + - u).
Hypothesis H17: v :e omega.
Hypothesis H19: x2 :e omega.
Hypothesis H20: eps_ x2 <= y + - u.
Hypothesis H21: SNo (eps_ v).
Hypothesis H22: SNo (eps_ x2).
Hypothesis H23: v + x2 :e omega.
Theorem Conj_real_mul_SNo_pos__46__18: ~ SNo (eps_ (v + x2)).
Admitted.

End Conj_real_mul_SNo_pos__46__18.
(** Conj_real_mul_SNo_pos__47__21 TMF4BGCGTDo4ybAmR83Rh17t22KHayVxJLF bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__47__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: z < x * y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (z + w * u) <= w * y + x * u.
Hypothesis H10: SNo (w * u).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (- (x * u)).
Hypothesis H13: SNo (w * y).
Hypothesis H14: SNo (- (w * y)).
Hypothesis H15: SNo (x + - w).
Hypothesis H16: SNo (y + - u).
Hypothesis H17: v :e omega.
Hypothesis H18: eps_ v <= x + - w.
Hypothesis H19: x2 :e omega.
Hypothesis H20: eps_ x2 <= y + - u.
Hypothesis H22: SNo (eps_ x2).
Theorem Conj_real_mul_SNo_pos__47__21: ~ v + x2 :e omega.
Admitted.

End Conj_real_mul_SNo_pos__47__21.
(** Conj_real_mul_SNo_pos__48__19 TMHKL3W3kSwv2zQzL6LBPqMqE9TTEvmQT4s bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__48__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall y2:set, y2 :e omega -> abs_SNo (z + - (x * y)) < eps_ y2).
Hypothesis H5: SNo z.
Hypothesis H6: z < x * y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (z + w * u) <= w * y + x * u.
Hypothesis H10: SNo (w * u).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (- (x * u)).
Hypothesis H13: SNo (w * y).
Hypothesis H14: SNo (- (w * y)).
Hypothesis H15: SNo (x + - w).
Hypothesis H16: SNo (y + - u).
Hypothesis H17: v :e omega.
Hypothesis H18: eps_ v <= x + - w.
Hypothesis H20: eps_ x2 <= y + - u.
Hypothesis H21: SNo (eps_ v).
Theorem Conj_real_mul_SNo_pos__48__19: ~ SNo (eps_ x2).
Admitted.

End Conj_real_mul_SNo_pos__48__19.
(** Conj_real_mul_SNo_pos__49__4 TMazLgmxWH8mpmhuJVNJmzcz5TQsep9nKML bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__49__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H5: SNo z.
Hypothesis H6: z < x * y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: (z + w * u) <= w * y + x * u.
Hypothesis H10: SNo (w * u).
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (- (x * u)).
Hypothesis H13: SNo (w * y).
Hypothesis H14: SNo (- (w * y)).
Hypothesis H15: SNo (x + - w).
Hypothesis H16: SNo (y + - u).
Hypothesis H17: v :e omega.
Hypothesis H18: eps_ v <= x + - w.
Hypothesis H19: x2 :e omega.
Hypothesis H20: eps_ x2 <= y + - u.
Theorem Conj_real_mul_SNo_pos__49__4: ~ SNo (eps_ v).
Admitted.

End Conj_real_mul_SNo_pos__49__4.
(** Conj_real_mul_SNo_pos__51__2 TMRrqoM1xmaAyz5ZFS9fPi5BxkBCJVW1xyq bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__51__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= x + - v -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoL y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= y + - v -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: z < x * y.
Hypothesis H9: w :e SNoL x.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (z + w * u) <= w * y + x * u.
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (- (x * u)).
Hypothesis H17: SNo (w * y).
Hypothesis H18: SNo (- (w * y)).
Theorem Conj_real_mul_SNo_pos__51__2: ~ SNo (x + - w).
Admitted.

End Conj_real_mul_SNo_pos__51__2.
(** Conj_real_mul_SNo_pos__53__0 TMTyQfX87omZgNybwLvYDM8iv3BP9Mh22Hb bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__53__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= x + - v -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoL y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= y + - v -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: z < x * y.
Hypothesis H9: w :e SNoL x.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (z + w * u) <= w * y + x * u.
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (- (x * u)).
Theorem Conj_real_mul_SNo_pos__53__0: ~ SNo (w * y).
Admitted.

End Conj_real_mul_SNo_pos__53__0.
(** Conj_real_mul_SNo_pos__53__1 TMV8HpqwnwPFwSRSkS2exHSL7CzFnnFbyZ1 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__53__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= x + - v -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoL y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= y + - v -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: z < x * y.
Hypothesis H9: w :e SNoL x.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (z + w * u) <= w * y + x * u.
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (- (x * u)).
Theorem Conj_real_mul_SNo_pos__53__1: ~ SNo (w * y).
Admitted.

End Conj_real_mul_SNo_pos__53__1.
(** Conj_real_mul_SNo_pos__53__6 TMYWJyBvBrce5b1A7qcPWzwJ2GQy3mkZLwu bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__53__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= x + - v -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoL y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= y + - v -> P) -> P)).
Hypothesis H7: SNo z.
Hypothesis H8: z < x * y.
Hypothesis H9: w :e SNoL x.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (z + w * u) <= w * y + x * u.
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (- (x * u)).
Theorem Conj_real_mul_SNo_pos__53__6: ~ SNo (w * y).
Admitted.

End Conj_real_mul_SNo_pos__53__6.
(** Conj_real_mul_SNo_pos__53__10 TMHe6xEbMBdoEsuj6Seoa1spVSD9ZMTHY6j bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__53__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= x + - v -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoL y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= y + - v -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: z < x * y.
Hypothesis H9: w :e SNoL x.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (z + w * u) <= w * y + x * u.
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (- (x * u)).
Theorem Conj_real_mul_SNo_pos__53__10: ~ SNo (w * y).
Admitted.

End Conj_real_mul_SNo_pos__53__10.
(** Conj_real_mul_SNo_pos__53__14 TMbdwAdYDWWmJuvDFzwMcWaHB8bFSad1jkZ bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__53__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= x + - v -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoL y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= y + - v -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H8: z < x * y.
Hypothesis H9: w :e SNoL x.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (z + w * u) <= w * y + x * u.
Hypothesis H15: SNo (x * u).
Hypothesis H16: SNo (- (x * u)).
Theorem Conj_real_mul_SNo_pos__53__14: ~ SNo (w * y).
Admitted.

End Conj_real_mul_SNo_pos__53__14.
(** Conj_real_mul_SNo_pos__55__8 TMPwgSrgY9Am1YHBSzfx7vkTYjjkZpSGdBT bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__55__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= x + - v -> P) -> P)).
Hypothesis H5: (forall v:set, v :e SNoL y -> (forall P:prop, (forall x2:set, x2 :e omega -> eps_ x2 <= y + - v -> P) -> P)).
Hypothesis H6: (forall v:set, v :e omega -> abs_SNo (z + - (x * y)) < eps_ v).
Hypothesis H7: SNo z.
Hypothesis H9: w :e SNoL x.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: SNo w.
Hypothesis H12: SNo u.
Hypothesis H13: (z + w * u) <= w * y + x * u.
Hypothesis H14: SNo (w * u).
Theorem Conj_real_mul_SNo_pos__55__8: ~ SNo (x * u).
Admitted.

End Conj_real_mul_SNo_pos__55__8.
(** Conj_real_mul_SNo_pos__59__5 TMYfp2kyiAPo757NqpD5pCy2rsEs8kj6uTQ bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__59__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: z :e omega.
Hypothesis H3: eps_ z * x < ordsucc Empty.
Hypothesis H4: eps_ z * y < ordsucc Empty.
Hypothesis H6: w + ordsucc Empty :e omega.
Hypothesis H7: w + ordsucc (ordsucc Empty) :e omega.
Hypothesis H8: u < x.
Hypothesis H9: SNo u.
Hypothesis H10: v < y.
Hypothesis H11: SNo v.
Hypothesis H12: SNo (eps_ z).
Hypothesis H13: SNo (eps_ (w + ordsucc Empty)).
Hypothesis H14: SNo (eps_ (w + ordsucc (ordsucc Empty))).
Theorem Conj_real_mul_SNo_pos__59__5: SNo (eps_ z * eps_ (w + ordsucc (ordsucc Empty))) -> (u * eps_ z * eps_ (w + ordsucc (ordsucc Empty)) + (eps_ z * eps_ (w + ordsucc (ordsucc Empty))) * v + (eps_ z * eps_ (w + ordsucc (ordsucc Empty))) * eps_ z * eps_ (w + ordsucc (ordsucc Empty))) < (eps_ (w + ordsucc (ordsucc Empty)) + eps_ (w + ordsucc (ordsucc Empty))) + eps_ (w + ordsucc Empty).
Admitted.

End Conj_real_mul_SNo_pos__59__5.
(** Conj_real_mul_SNo_pos__69__21 TMLDKfg1JN8GzHWn9mxuLFpxTXYK2nwHBkL bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__69__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H6: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= v + - x.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Hypothesis H16: y2 + z2 :e omega.
Hypothesis H17: SNo (eps_ (y2 + z2)).
Hypothesis H18: SNo (- (eps_ (y2 + z2))).
Hypothesis H19: SNo (ap w (y2 + z2)).
Hypothesis H20: SNo (v * y).
Hypothesis H22: SNo (- (v * x2)).
Theorem Conj_real_mul_SNo_pos__69__21: SNo (v * y + x * x2 + - (v * x2)) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__69__21.
(** Conj_real_mul_SNo_pos__70__1 TMKFSRJdZG6awGoWoPHYrM3BncrHz8YTmoY bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__70__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H6: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= v + - x.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Hypothesis H16: y2 + z2 :e omega.
Hypothesis H17: SNo (eps_ (y2 + z2)).
Hypothesis H18: SNo (- (eps_ (y2 + z2))).
Hypothesis H19: SNo (ap w (y2 + z2)).
Hypothesis H20: SNo (v * y).
Hypothesis H21: SNo (x * x2).
Hypothesis H22: SNo (v * x2).
Theorem Conj_real_mul_SNo_pos__70__1: SNo (- (v * x2)) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__70__1.
(** Conj_real_mul_SNo_pos__71__3 TMRCGac7r8fiPRwFyjA14mZXXeyi1zdb3PB bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__71__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H6: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= v + - x.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Hypothesis H16: y2 + z2 :e omega.
Hypothesis H17: SNo (eps_ (y2 + z2)).
Hypothesis H18: SNo (- (eps_ (y2 + z2))).
Hypothesis H19: SNo (ap w (y2 + z2)).
Hypothesis H20: SNo (v * y).
Hypothesis H21: SNo (x * x2).
Theorem Conj_real_mul_SNo_pos__71__3: SNo (v * x2) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__71__3.
(** Conj_real_mul_SNo_pos__71__18 TMH9XTxLMp36aJmahrECEPGyxCpdSe6tYqT bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__71__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H6: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= v + - x.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Hypothesis H16: y2 + z2 :e omega.
Hypothesis H17: SNo (eps_ (y2 + z2)).
Hypothesis H19: SNo (ap w (y2 + z2)).
Hypothesis H20: SNo (v * y).
Hypothesis H21: SNo (x * x2).
Theorem Conj_real_mul_SNo_pos__71__18: SNo (v * x2) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__71__18.
(** Conj_real_mul_SNo_pos__72__9 TMV4RUascwakY88yKdVtRf1zgxEQaH3Vf95 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__72__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H6: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Hypothesis H16: y2 + z2 :e omega.
Hypothesis H17: SNo (eps_ (y2 + z2)).
Hypothesis H18: SNo (- (eps_ (y2 + z2))).
Hypothesis H19: SNo (ap w (y2 + z2)).
Hypothesis H20: SNo (v * y).
Theorem Conj_real_mul_SNo_pos__72__9: SNo (x * x2) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__72__9.
(** Conj_real_mul_SNo_pos__72__13 TMKUcikKKxN15rMiQnLxKPeWqHEjqy3AAz4 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__72__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H6: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= v + - x.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Hypothesis H16: y2 + z2 :e omega.
Hypothesis H17: SNo (eps_ (y2 + z2)).
Hypothesis H18: SNo (- (eps_ (y2 + z2))).
Hypothesis H19: SNo (ap w (y2 + z2)).
Hypothesis H20: SNo (v * y).
Theorem Conj_real_mul_SNo_pos__72__13: SNo (x * x2) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__72__13.
(** Conj_real_mul_SNo_pos__73__16 TMavqhXhJZxKGNTaBveHCj3LU5rGaC1ehom bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__73__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H6: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= v + - x.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Hypothesis H17: SNo (eps_ (y2 + z2)).
Hypothesis H18: SNo (- (eps_ (y2 + z2))).
Hypothesis H19: SNo (ap w (y2 + z2)).
Theorem Conj_real_mul_SNo_pos__73__16: SNo (v * y) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__73__16.
(** Conj_real_mul_SNo_pos__76__16 TMUvELkFgMHCSvioerw59HAU4nU2kKZAxNS bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__76__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall w2:set, w2 :e omega -> SNo (ap w w2)).
Hypothesis H5: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H7: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H8: u = v * y + x * x2 + - (v * x2).
Hypothesis H9: y2 :e omega.
Hypothesis H10: eps_ y2 <= v + - x.
Hypothesis H11: z2 :e omega.
Hypothesis H12: eps_ z2 <= y + - x2.
Hypothesis H13: SNo v.
Hypothesis H14: SNo x2.
Hypothesis H15: SNo (eps_ y2).
Hypothesis H17: y2 + z2 :e omega.
Theorem Conj_real_mul_SNo_pos__76__16: SNo (eps_ (y2 + z2)) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__76__16.
(** Conj_real_mul_SNo_pos__77__10 TMP7spghSWDhmBudt8MhBRRP58HbokNfGwd bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__77__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall w2:set, w2 :e omega -> SNo (ap w w2)).
Hypothesis H5: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H7: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H8: u = v * y + x * x2 + - (v * x2).
Hypothesis H9: y2 :e omega.
Hypothesis H11: z2 :e omega.
Hypothesis H12: eps_ z2 <= y + - x2.
Hypothesis H13: SNo v.
Hypothesis H14: SNo x2.
Hypothesis H15: SNo (eps_ y2).
Hypothesis H16: SNo (eps_ z2).
Theorem Conj_real_mul_SNo_pos__77__10: y2 + z2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__77__10.
(** Conj_real_mul_SNo_pos__84__2 TMYaoVDtuKAyxHHR5vbiDH8NvLiSPNcsriK bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__84__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H6: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= x + - v.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= x2 + - y.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Hypothesis H16: y2 + z2 :e omega.
Hypothesis H17: SNo (eps_ (y2 + z2)).
Hypothesis H18: SNo (- (eps_ (y2 + z2))).
Hypothesis H19: SNo (ap w (y2 + z2)).
Theorem Conj_real_mul_SNo_pos__84__2: SNo (v * y) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__84__2.
(** Conj_real_mul_SNo_pos__85__6 TMMT46Q6jcs4CzRLXZGgdpoxmrVM5bPdM7A bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__85__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall w2:set, w2 :e omega -> SNo (ap w w2)).
Hypothesis H5: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H7: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H8: u = v * y + x * x2 + - (v * x2).
Hypothesis H9: y2 :e omega.
Hypothesis H10: eps_ y2 <= x + - v.
Hypothesis H11: z2 :e omega.
Hypothesis H12: eps_ z2 <= x2 + - y.
Hypothesis H13: SNo v.
Hypothesis H14: SNo x2.
Hypothesis H15: SNo (eps_ y2).
Hypothesis H16: SNo (eps_ z2).
Hypothesis H17: y2 + z2 :e omega.
Hypothesis H18: SNo (eps_ (y2 + z2)).
Hypothesis H19: SNo (- (eps_ (y2 + z2))).
Theorem Conj_real_mul_SNo_pos__85__6: SNo (ap w (y2 + z2)) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__85__6.
(** Conj_real_mul_SNo_pos__85__14 TMWdzBZ64sitNpnkdBGJJJPf7zRkVQH3AWM bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__85__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall w2:set, w2 :e omega -> SNo (ap w w2)).
Hypothesis H5: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H7: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H8: u = v * y + x * x2 + - (v * x2).
Hypothesis H9: y2 :e omega.
Hypothesis H10: eps_ y2 <= x + - v.
Hypothesis H11: z2 :e omega.
Hypothesis H12: eps_ z2 <= x2 + - y.
Hypothesis H13: SNo v.
Hypothesis H15: SNo (eps_ y2).
Hypothesis H16: SNo (eps_ z2).
Hypothesis H17: y2 + z2 :e omega.
Hypothesis H18: SNo (eps_ (y2 + z2)).
Hypothesis H19: SNo (- (eps_ (y2 + z2))).
Theorem Conj_real_mul_SNo_pos__85__14: SNo (ap w (y2 + z2)) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__85__14.
(** Conj_real_mul_SNo_pos__85__19 TMUXjYoxk8YmZQodrkRoJZ9wDduJgayZTrD bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__85__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall w2:set, w2 :e omega -> SNo (ap w w2)).
Hypothesis H5: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H7: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H8: u = v * y + x * x2 + - (v * x2).
Hypothesis H9: y2 :e omega.
Hypothesis H10: eps_ y2 <= x + - v.
Hypothesis H11: z2 :e omega.
Hypothesis H12: eps_ z2 <= x2 + - y.
Hypothesis H13: SNo v.
Hypothesis H14: SNo x2.
Hypothesis H15: SNo (eps_ y2).
Hypothesis H16: SNo (eps_ z2).
Hypothesis H17: y2 + z2 :e omega.
Hypothesis H18: SNo (eps_ (y2 + z2)).
Theorem Conj_real_mul_SNo_pos__85__19: SNo (ap w (y2 + z2)) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__85__19.
(** Conj_real_mul_SNo_pos__86__4 TMNyw3HmEqwWf7fEoWNCgzrsamFfPV2Sqy8 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__86__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H5: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H7: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H8: u = v * y + x * x2 + - (v * x2).
Hypothesis H9: y2 :e omega.
Hypothesis H10: eps_ y2 <= x + - v.
Hypothesis H11: z2 :e omega.
Hypothesis H12: eps_ z2 <= x2 + - y.
Hypothesis H13: SNo v.
Hypothesis H14: SNo x2.
Hypothesis H15: SNo (eps_ y2).
Hypothesis H16: SNo (eps_ z2).
Hypothesis H17: y2 + z2 :e omega.
Hypothesis H18: SNo (eps_ (y2 + z2)).
Theorem Conj_real_mul_SNo_pos__86__4: SNo (- (eps_ (y2 + z2))) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__86__4.
(** Conj_real_mul_SNo_pos__86__18 TMdSBk7x2HshTHBCnLsRavjer91rHjqXLSg bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__86__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall w2:set, w2 :e omega -> SNo (ap w w2)).
Hypothesis H5: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H7: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H8: u = v * y + x * x2 + - (v * x2).
Hypothesis H9: y2 :e omega.
Hypothesis H10: eps_ y2 <= x + - v.
Hypothesis H11: z2 :e omega.
Hypothesis H12: eps_ z2 <= x2 + - y.
Hypothesis H13: SNo v.
Hypothesis H14: SNo x2.
Hypothesis H15: SNo (eps_ y2).
Hypothesis H16: SNo (eps_ z2).
Hypothesis H17: y2 + z2 :e omega.
Theorem Conj_real_mul_SNo_pos__86__18: SNo (- (eps_ (y2 + z2))) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__86__18.
(** Conj_real_mul_SNo_pos__87__14 TMLrgfFoPgJS9Pnupz55Z2qw5zScDM4P4Ps bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__87__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall w2:set, w2 :e omega -> SNo (ap w w2)).
Hypothesis H5: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H7: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H8: u = v * y + x * x2 + - (v * x2).
Hypothesis H9: y2 :e omega.
Hypothesis H10: eps_ y2 <= x + - v.
Hypothesis H11: z2 :e omega.
Hypothesis H12: eps_ z2 <= x2 + - y.
Hypothesis H13: SNo v.
Hypothesis H15: SNo (eps_ y2).
Hypothesis H16: SNo (eps_ z2).
Hypothesis H17: y2 + z2 :e omega.
Theorem Conj_real_mul_SNo_pos__87__14: SNo (eps_ (y2 + z2)) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__87__14.
(** Conj_real_mul_SNo_pos__88__10 TMF62MDyp1m1NKt3LjpM27aipbovhL1NfmY bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__88__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall w2:set, w2 :e omega -> SNo (ap w w2)).
Hypothesis H5: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H7: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H8: u = v * y + x * x2 + - (v * x2).
Hypothesis H9: y2 :e omega.
Hypothesis H11: z2 :e omega.
Hypothesis H12: eps_ z2 <= x2 + - y.
Hypothesis H13: SNo v.
Hypothesis H14: SNo x2.
Hypothesis H15: SNo (eps_ y2).
Hypothesis H16: SNo (eps_ z2).
Theorem Conj_real_mul_SNo_pos__88__10: y2 + z2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__88__10.
(** Conj_real_mul_SNo_pos__90__14 TMbudEvWFMNHLGb8uRp7rAVcxjE2G7XbRLq bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__90__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (- (x * y)).
Hypothesis H4: (forall w2:set, w2 :e omega -> SNo (ap w w2)).
Hypothesis H5: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < ap w w2).
Hypothesis H7: (forall w2:set, w2 :e omega -> (ap w w2 + - (eps_ w2)) < x * y).
Hypothesis H8: u = v * y + x * x2 + - (v * x2).
Hypothesis H9: y2 :e omega.
Hypothesis H10: eps_ y2 <= x + - v.
Hypothesis H11: z2 :e omega.
Hypothesis H12: eps_ z2 <= x2 + - y.
Hypothesis H13: SNo v.
Theorem Conj_real_mul_SNo_pos__90__14: SNo (eps_ y2) -> SNoCut (Repl omega (ap z)) (Repl omega (ap w)) < u.
Admitted.

End Conj_real_mul_SNo_pos__90__14.
(** Conj_real_mul_SNo_pos__93__1 TMMNuwvWGseTceibVcc5PYNTszjHsSkAKGp bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__93__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H4: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H6: u = v * y + x * x2 + - (v * x2).
Hypothesis H7: y2 :e omega.
Hypothesis H8: eps_ y2 <= v + - x.
Hypothesis H9: z2 :e omega.
Hypothesis H10: eps_ z2 <= x2 + - y.
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (eps_ y2).
Hypothesis H14: SNo (eps_ z2).
Hypothesis H15: y2 + z2 :e omega.
Hypothesis H16: SNo (eps_ (y2 + z2)).
Hypothesis H17: SNo (ap z (y2 + z2)).
Hypothesis H18: SNo (v * y).
Hypothesis H19: SNo (x * x2).
Theorem Conj_real_mul_SNo_pos__93__1: SNo (v * x2) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__93__1.
(** Conj_real_mul_SNo_pos__93__16 TMRo6vy1XXhLQfqwtP4pijfyb9abm8kmUd5 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__93__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H4: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H6: u = v * y + x * x2 + - (v * x2).
Hypothesis H7: y2 :e omega.
Hypothesis H8: eps_ y2 <= v + - x.
Hypothesis H9: z2 :e omega.
Hypothesis H10: eps_ z2 <= x2 + - y.
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (eps_ y2).
Hypothesis H14: SNo (eps_ z2).
Hypothesis H15: y2 + z2 :e omega.
Hypothesis H17: SNo (ap z (y2 + z2)).
Hypothesis H18: SNo (v * y).
Hypothesis H19: SNo (x * x2).
Theorem Conj_real_mul_SNo_pos__93__16: SNo (v * x2) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__93__16.
(** Conj_real_mul_SNo_pos__94__6 TMbgTCgYKSERHSQs7YuweXcpMN1N1LbrkZz bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__94__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H4: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H7: y2 :e omega.
Hypothesis H8: eps_ y2 <= v + - x.
Hypothesis H9: z2 :e omega.
Hypothesis H10: eps_ z2 <= x2 + - y.
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (eps_ y2).
Hypothesis H14: SNo (eps_ z2).
Hypothesis H15: y2 + z2 :e omega.
Hypothesis H16: SNo (eps_ (y2 + z2)).
Hypothesis H17: SNo (ap z (y2 + z2)).
Hypothesis H18: SNo (v * y).
Theorem Conj_real_mul_SNo_pos__94__6: SNo (x * x2) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__94__6.
(** Conj_real_mul_SNo_pos__94__7 TMX1hBM2erXLDPuyfnHYdtDLGXX5yTPik7G bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__94__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H4: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H6: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: eps_ y2 <= v + - x.
Hypothesis H9: z2 :e omega.
Hypothesis H10: eps_ z2 <= x2 + - y.
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (eps_ y2).
Hypothesis H14: SNo (eps_ z2).
Hypothesis H15: y2 + z2 :e omega.
Hypothesis H16: SNo (eps_ (y2 + z2)).
Hypothesis H17: SNo (ap z (y2 + z2)).
Hypothesis H18: SNo (v * y).
Theorem Conj_real_mul_SNo_pos__94__7: SNo (x * x2) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__94__7.
(** Conj_real_mul_SNo_pos__95__14 TMPz8f46YXM6m3SqrdpjdANzGLmRD2ccRtH bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__95__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H4: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H6: u = v * y + x * x2 + - (v * x2).
Hypothesis H7: y2 :e omega.
Hypothesis H8: eps_ y2 <= v + - x.
Hypothesis H9: z2 :e omega.
Hypothesis H10: eps_ z2 <= x2 + - y.
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (eps_ y2).
Hypothesis H15: y2 + z2 :e omega.
Hypothesis H16: SNo (eps_ (y2 + z2)).
Hypothesis H17: SNo (ap z (y2 + z2)).
Theorem Conj_real_mul_SNo_pos__95__14: SNo (v * y) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__95__14.
(** Conj_real_mul_SNo_pos__100__9 TMPSTEx3vtjUBY15NtokfywDSJbGNdNDHqo bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__100__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall w2:set, w2 :e omega -> SNo (ap z w2)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= x2 + - y.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Theorem Conj_real_mul_SNo_pos__100__9: SNo (eps_ y2) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__100__9.
(** Conj_real_mul_SNo_pos__100__13 TMGywPDTVZsCpNgmTZKcUAScjC6e3qJ3fnc bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__100__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall w2:set, w2 :e omega -> SNo (ap z w2)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= v + - x.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= x2 + - y.
Hypothesis H12: SNo v.
Theorem Conj_real_mul_SNo_pos__100__13: SNo (eps_ y2) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__100__13.
(** Conj_real_mul_SNo_pos__101__1 TMLeS97XXykwEmtZ6mGUKsmAYVeZ6weoQco bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__101__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H4: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H6: u = v * y + x * x2 + - (v * x2).
Hypothesis H7: y2 :e omega.
Hypothesis H8: eps_ y2 <= x + - v.
Hypothesis H9: z2 :e omega.
Hypothesis H10: eps_ z2 <= y + - x2.
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (eps_ y2).
Hypothesis H14: SNo (eps_ z2).
Hypothesis H15: y2 + z2 :e omega.
Hypothesis H16: SNo (eps_ (y2 + z2)).
Hypothesis H17: SNo (ap z (y2 + z2)).
Hypothesis H18: SNo (v * y).
Hypothesis H19: SNo (x * x2).
Hypothesis H20: SNo (- (v * x2)).
Theorem Conj_real_mul_SNo_pos__101__1: SNo (v * y + x * x2 + - (v * x2)) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__101__1.
(** Conj_real_mul_SNo_pos__101__20 TMMbmK2RVyBo3LH5MrTdFiQ485b4986p29S bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__101__20.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H4: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H6: u = v * y + x * x2 + - (v * x2).
Hypothesis H7: y2 :e omega.
Hypothesis H8: eps_ y2 <= x + - v.
Hypothesis H9: z2 :e omega.
Hypothesis H10: eps_ z2 <= y + - x2.
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (eps_ y2).
Hypothesis H14: SNo (eps_ z2).
Hypothesis H15: y2 + z2 :e omega.
Hypothesis H16: SNo (eps_ (y2 + z2)).
Hypothesis H17: SNo (ap z (y2 + z2)).
Hypothesis H18: SNo (v * y).
Hypothesis H19: SNo (x * x2).
Theorem Conj_real_mul_SNo_pos__101__20: SNo (v * y + x * x2 + - (v * x2)) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__101__20.
(** Conj_real_mul_SNo_pos__104__4 TMP8NEigTJwwkZDiNpJqy4DqWUqo9ELxy9N bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__104__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H6: u = v * y + x * x2 + - (v * x2).
Hypothesis H7: y2 :e omega.
Hypothesis H8: eps_ y2 <= x + - v.
Hypothesis H9: z2 :e omega.
Hypothesis H10: eps_ z2 <= y + - x2.
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (eps_ y2).
Hypothesis H14: SNo (eps_ z2).
Hypothesis H15: y2 + z2 :e omega.
Hypothesis H16: SNo (eps_ (y2 + z2)).
Hypothesis H17: SNo (ap z (y2 + z2)).
Hypothesis H18: SNo (v * y).
Theorem Conj_real_mul_SNo_pos__104__4: SNo (x * x2) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__104__4.
(** Conj_real_mul_SNo_pos__105__6 TMQLicaHDBE8BFp4NK5G6zJ9etv5dy8ndyH bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__105__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H4: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H7: y2 :e omega.
Hypothesis H8: eps_ y2 <= x + - v.
Hypothesis H9: z2 :e omega.
Hypothesis H10: eps_ z2 <= y + - x2.
Hypothesis H11: SNo v.
Hypothesis H12: SNo x2.
Hypothesis H13: SNo (eps_ y2).
Hypothesis H14: SNo (eps_ z2).
Hypothesis H15: y2 + z2 :e omega.
Hypothesis H16: SNo (eps_ (y2 + z2)).
Hypothesis H17: SNo (ap z (y2 + z2)).
Theorem Conj_real_mul_SNo_pos__105__6: SNo (v * y) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__105__6.
(** Conj_real_mul_SNo_pos__106__17 TMbMLeidfTMuiPd34tmK9QmnsMoXhdNpDPe bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__106__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall w2:set, w2 :e omega -> SNo (ap z w2)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= x + - v.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Hypothesis H16: y2 + z2 :e omega.
Theorem Conj_real_mul_SNo_pos__106__17: SNo (ap z (y2 + z2)) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__106__17.
(** Conj_real_mul_SNo_pos__107__16 TMMx8VRrAt4HzBnaKYjQCL6SMsruuCpUeLT bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__107__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall w2:set, w2 :e omega -> SNo (ap z w2)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= x + - v.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Theorem Conj_real_mul_SNo_pos__107__16: SNo (eps_ (y2 + z2)) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__107__16.
(** Conj_real_mul_SNo_pos__108__6 TMM5toNWPBBZSzZ7iamMVJoohpLoNNbKT4E bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__108__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall w2:set, w2 :e omega -> SNo (ap z w2)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= x + - v.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Theorem Conj_real_mul_SNo_pos__108__6: y2 + z2 :e omega -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__108__6.
(** Conj_real_mul_SNo_pos__108__11 TMPR34o5X3U7h6suDWD1unFoVouhasQFHoP bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__108__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: (forall w2:set, w2 :e omega -> SNo (ap z w2)).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= x + - v.
Hypothesis H10: z2 :e omega.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Hypothesis H15: SNo (eps_ z2).
Theorem Conj_real_mul_SNo_pos__108__11: y2 + z2 :e omega -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__108__11.
(** Conj_real_mul_SNo_pos__109__3 TMFyecQjJ8sdb9a8tSQTcWxkPj33XtVwQZ3 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__109__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Variable z2:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H4: SNo (SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H5: (forall w2:set, w2 :e omega -> ap z w2 < SNoCut (Repl omega (ap z)) (Repl omega (ap w))).
Hypothesis H6: (forall w2:set, w2 :e omega -> x * y < ap z w2 + eps_ w2).
Hypothesis H7: u = v * y + x * x2 + - (v * x2).
Hypothesis H8: y2 :e omega.
Hypothesis H9: eps_ y2 <= x + - v.
Hypothesis H10: z2 :e omega.
Hypothesis H11: eps_ z2 <= y + - x2.
Hypothesis H12: SNo v.
Hypothesis H13: SNo x2.
Hypothesis H14: SNo (eps_ y2).
Theorem Conj_real_mul_SNo_pos__109__3: SNo (eps_ z2) -> u < SNoCut (Repl omega (ap z)) (Repl omega (ap w)).
Admitted.

End Conj_real_mul_SNo_pos__109__3.
(** Conj_real_mul_SNo_pos__111__23 TMUyZuNkPQJbLAyEgpPPdTBz9WPYU6YJFQi bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__111__23.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: v :e setexp (SNoS_ omega) omega.
Hypothesis H15: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H16: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H18: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Hypothesis H19: SNoCutP (Repl omega (ap u)) (Repl omega (ap v)).
Hypothesis H20: SNo (SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H21: (forall x2:set, x2 :e omega -> ap u x2 < SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H22: (forall x2:set, x2 :e omega -> SNoCut (Repl omega (ap u)) (Repl omega (ap v)) < ap v x2).
Hypothesis H24: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H25: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y).
Hypothesis H26: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Theorem Conj_real_mul_SNo_pos__111__23: x * y <> SNoCut (Repl omega (ap u)) (Repl omega (ap v)).
Admitted.

End Conj_real_mul_SNo_pos__111__23.
(** Conj_real_mul_SNo_pos__112__11 TMX2HaetPie6ZpHwoVVmuanNJHBv7TbmcXo bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__112__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: v :e setexp (SNoS_ omega) omega.
Hypothesis H15: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H16: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H19: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Hypothesis H20: SNoCutP (Repl omega (ap u)) (Repl omega (ap v)).
Hypothesis H21: SNo (SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H22: (forall x2:set, x2 :e omega -> ap u x2 < SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H23: (forall x2:set, x2 :e omega -> SNoCut (Repl omega (ap u)) (Repl omega (ap v)) < ap v x2).
Hypothesis H24: (forall x2:set, x2 :e omega -> x * y < ap u x2 + eps_ x2).
Hypothesis H25: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H26: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y).
Theorem Conj_real_mul_SNo_pos__112__11: ~ (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Admitted.

End Conj_real_mul_SNo_pos__112__11.
(** Conj_real_mul_SNo_pos__112__22 TMWSSwAqXy5XqUzCwkGp4CgvBjtyoNU6pxi bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__112__22.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: v :e setexp (SNoS_ omega) omega.
Hypothesis H15: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H16: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H19: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Hypothesis H20: SNoCutP (Repl omega (ap u)) (Repl omega (ap v)).
Hypothesis H21: SNo (SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H23: (forall x2:set, x2 :e omega -> SNoCut (Repl omega (ap u)) (Repl omega (ap v)) < ap v x2).
Hypothesis H24: (forall x2:set, x2 :e omega -> x * y < ap u x2 + eps_ x2).
Hypothesis H25: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H26: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y).
Theorem Conj_real_mul_SNo_pos__112__22: ~ (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Admitted.

End Conj_real_mul_SNo_pos__112__22.
(** Conj_real_mul_SNo_pos__113__6 TMcTCm79ELB739kanE9hTnqu3YKGSECxqm6 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__113__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: v :e setexp (SNoS_ omega) omega.
Hypothesis H15: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H16: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H19: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Hypothesis H20: SNoCutP (Repl omega (ap u)) (Repl omega (ap v)).
Hypothesis H21: SNo (SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H22: (forall x2:set, x2 :e omega -> ap u x2 < SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H23: (forall x2:set, x2 :e omega -> SNoCut (Repl omega (ap u)) (Repl omega (ap v)) < ap v x2).
Hypothesis H24: (forall x2:set, x2 :e omega -> x * y < ap u x2 + eps_ x2).
Hypothesis H25: (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Theorem Conj_real_mul_SNo_pos__113__6: ~ (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y).
Admitted.

End Conj_real_mul_SNo_pos__113__6.
(** Conj_real_mul_SNo_pos__114__6 TMVRFeBQhjzdKomgrnvSS3iwN1MctH1Pjgk bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__114__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: (forall x2:set, x2 :e omega -> ap u x2 < x * y /\ x * y < ap u x2 + eps_ x2 /\ (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: v :e setexp (SNoS_ omega) omega.
Hypothesis H16: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H20: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Hypothesis H21: SNoCutP (Repl omega (ap u)) (Repl omega (ap v)).
Hypothesis H22: SNo (SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap u x2 < SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNoCut (Repl omega (ap u)) (Repl omega (ap v)) < ap v x2).
Hypothesis H25: (forall x2:set, x2 :e omega -> x * y < ap u x2 + eps_ x2).
Theorem Conj_real_mul_SNo_pos__114__6: ~ (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Admitted.

End Conj_real_mul_SNo_pos__114__6.
(** Conj_real_mul_SNo_pos__114__21 TMEonVXa2cMo835BTYV884Rt5YdxnuYp1Mv bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__114__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: (forall x2:set, x2 :e omega -> ap u x2 < x * y /\ x * y < ap u x2 + eps_ x2 /\ (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: v :e setexp (SNoS_ omega) omega.
Hypothesis H16: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H20: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Hypothesis H22: SNo (SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap u x2 < SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNoCut (Repl omega (ap u)) (Repl omega (ap v)) < ap v x2).
Hypothesis H25: (forall x2:set, x2 :e omega -> x * y < ap u x2 + eps_ x2).
Theorem Conj_real_mul_SNo_pos__114__21: ~ (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Admitted.

End Conj_real_mul_SNo_pos__114__21.
(** Conj_real_mul_SNo_pos__114__25 TMLijcXx5rgBoVx7vcQLai5nJ2fa8xnkmbZ bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__114__25.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: (forall x2:set, x2 :e omega -> ap u x2 < x * y /\ x * y < ap u x2 + eps_ x2 /\ (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: v :e setexp (SNoS_ omega) omega.
Hypothesis H16: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H20: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Hypothesis H21: SNoCutP (Repl omega (ap u)) (Repl omega (ap v)).
Hypothesis H22: SNo (SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap u x2 < SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNoCut (Repl omega (ap u)) (Repl omega (ap v)) < ap v x2).
Theorem Conj_real_mul_SNo_pos__114__25: ~ (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Admitted.

End Conj_real_mul_SNo_pos__114__25.
(** Conj_real_mul_SNo_pos__115__11 TMLq6VCy3gfhjaj9j7PcL141BCrbndUpCxc bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__115__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: (forall x2:set, x2 :e omega -> ap u x2 < x * y /\ x * y < ap u x2 + eps_ x2 /\ (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: v :e setexp (SNoS_ omega) omega.
Hypothesis H16: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H20: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Hypothesis H21: SNoCutP (Repl omega (ap u)) (Repl omega (ap v)).
Hypothesis H22: SNo (SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap u x2 < SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNoCut (Repl omega (ap u)) (Repl omega (ap v)) < ap v x2).
Theorem Conj_real_mul_SNo_pos__115__11: ~ (forall x2:set, x2 :e omega -> x * y < ap u x2 + eps_ x2).
Admitted.

End Conj_real_mul_SNo_pos__115__11.
(** Conj_real_mul_SNo_pos__115__21 TMJagLpgWeRdeipF5jne5tuzY5f4qRiBGJ3 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__115__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: (forall x2:set, x2 :e omega -> ap u x2 < x * y /\ x * y < ap u x2 + eps_ x2 /\ (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: v :e setexp (SNoS_ omega) omega.
Hypothesis H16: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H20: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Hypothesis H22: SNo (SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H23: (forall x2:set, x2 :e omega -> ap u x2 < SNoCut (Repl omega (ap u)) (Repl omega (ap v))).
Hypothesis H24: (forall x2:set, x2 :e omega -> SNoCut (Repl omega (ap u)) (Repl omega (ap v)) < ap v x2).
Theorem Conj_real_mul_SNo_pos__115__21: ~ (forall x2:set, x2 :e omega -> x * y < ap u x2 + eps_ x2).
Admitted.

End Conj_real_mul_SNo_pos__115__21.
(** Conj_real_mul_SNo_pos__116__0 TMWLgpD24AqoEUGfa1kfgrRZg7UzT5ssvzA bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__116__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: (forall x2:set, x2 :e omega -> ap u x2 < x * y /\ x * y < ap u x2 + eps_ x2 /\ (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: v :e setexp (SNoS_ omega) omega.
Hypothesis H16: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H20: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Theorem Conj_real_mul_SNo_pos__116__0: ~ (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e omega -> ap u x2 < ap v y2)).
Admitted.

End Conj_real_mul_SNo_pos__116__0.
(** Conj_real_mul_SNo_pos__116__5 TMQW1q6rqbDTqAyefnGkcRYpuqZpCgascYs bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__116__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: (forall x2:set, x2 :e omega -> ap u x2 < x * y /\ x * y < ap u x2 + eps_ x2 /\ (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: v :e setexp (SNoS_ omega) omega.
Hypothesis H16: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Hypothesis H20: (forall x2:set, x2 :e omega -> x * y < ap v x2).
Theorem Conj_real_mul_SNo_pos__116__5: ~ (forall x2:set, x2 :e omega -> (forall y2:set, y2 :e omega -> ap u x2 < ap v y2)).
Admitted.

End Conj_real_mul_SNo_pos__116__5.
(** Conj_real_mul_SNo_pos__117__0 TMVXXT3ELwQTZq5ayKEGjUzaKdmxLH8YbV1 bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__117__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: (forall x2:set, x2 :e omega -> ap u x2 < x * y /\ x * y < ap u x2 + eps_ x2 /\ (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: v :e setexp (SNoS_ omega) omega.
Hypothesis H16: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Theorem Conj_real_mul_SNo_pos__117__0: ~ (forall x2:set, x2 :e omega -> x * y < ap v x2).
Admitted.

End Conj_real_mul_SNo_pos__117__0.
(** Conj_real_mul_SNo_pos__117__15 TMZoNHtsQScAkXRUB74sAfGbsNZCkqC9eRY bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__117__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: (forall x2:set, x2 :e omega -> ap u x2 < x * y /\ x * y < ap u x2 + eps_ x2 /\ (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H16: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Hypothesis H18: (forall x2:set, x2 :e omega -> SNo (ap v x2)).
Hypothesis H19: (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Theorem Conj_real_mul_SNo_pos__117__15: ~ (forall x2:set, x2 :e omega -> x * y < ap v x2).
Admitted.

End Conj_real_mul_SNo_pos__117__15.
(** Conj_real_mul_SNo_pos__118__18 TMdEAgnLyH1pY7FMoKQ6j2XUeKksZr1zxYz bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__118__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: ~ x * y :e real.
Hypothesis H1: SNo x.
Hypothesis H2: SNo y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: SNo (- (x * y)).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x + - x2 -> P) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoR x -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - x -> P) -> P)).
Hypothesis H7: (forall x2:set, x2 :e SNoL y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= y + - x2 -> P) -> P)).
Hypothesis H8: (forall x2:set, x2 :e SNoR y -> (forall P:prop, (forall y2:set, y2 :e omega -> eps_ y2 <= x2 + - y -> P) -> P)).
Hypothesis H9: SNoCutP z w.
Hypothesis H10: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H11: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: x * y = SNoCut z w.
Hypothesis H13: u :e setexp (SNoS_ omega) omega.
Hypothesis H14: (forall x2:set, x2 :e omega -> ap u x2 < x * y /\ x * y < ap u x2 + eps_ x2 /\ (forall y2:set, y2 :e x2 -> ap u y2 < ap u x2)).
Hypothesis H15: v :e setexp (SNoS_ omega) omega.
Hypothesis H16: (forall x2:set, x2 :e omega -> (ap v x2 + - (eps_ x2)) < x * y /\ x * y < ap v x2 /\ (forall y2:set, y2 :e x2 -> ap v x2 < ap v y2)).
Hypothesis H17: (forall x2:set, x2 :e omega -> SNo (ap u x2)).
Theorem Conj_real_mul_SNo_pos__118__18: ~ (forall x2:set, x2 :e omega -> ap u x2 < x * y).
Admitted.

End Conj_real_mul_SNo_pos__118__18.
(** Conj_real_mul_SNo_pos__123__21 TMTCSz5NCrQuzQJSN975pypcTqBqoqAP2Kr bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__123__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: Empty < x.
Hypothesis H1: Empty < y.
Hypothesis H2: ~ x * y :e real.
Hypothesis H3: SNo x.
Hypothesis H4: x :e SNoS_ (ordsucc omega).
Hypothesis H5: x < omega.
Hypothesis H6: SNo y.
Hypothesis H7: y :e SNoS_ (ordsucc omega).
Hypothesis H8: y < omega.
Hypothesis H9: (forall u:set, u :e omega -> (forall P:prop, (forall v:set, v :e SNoS_ omega -> Empty < v -> v < x -> x < v + eps_ u -> P) -> P)).
Hypothesis H10: (forall u:set, u :e omega -> (forall P:prop, (forall v:set, v :e SNoS_ omega -> Empty < v -> v < y -> y < v + eps_ u -> P) -> P)).
Hypothesis H11: SNo (x * y).
Hypothesis H12: SNo (- (x * y)).
Hypothesis H13: (forall u:set, SNo u -> SNoLev u :e omega -> SNoLev u :e SNoLev (x * y)).
Hypothesis H14: (forall u:set, u :e SNoL x -> (forall P:prop, (forall v:set, v :e omega -> eps_ v <= x + - u -> P) -> P)).
Hypothesis H15: (forall u:set, u :e SNoR x -> (forall P:prop, (forall v:set, v :e omega -> eps_ v <= u + - x -> P) -> P)).
Hypothesis H16: (forall u:set, u :e SNoL y -> (forall P:prop, (forall v:set, v :e omega -> eps_ v <= y + - u -> P) -> P)).
Hypothesis H17: (forall u:set, u :e SNoR y -> (forall P:prop, (forall v:set, v :e omega -> eps_ v <= u + - y -> P) -> P)).
Hypothesis H18: SNoCutP z w.
Hypothesis H19: (forall u:set, u :e z -> (forall P:prop, (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> u = v * y + x * x2 + - (v * x2) -> P)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoR y -> u = v * y + x * x2 + - (v * x2) -> P)) -> P)).
Hypothesis H20: (forall u:set, u :e w -> (forall P:prop, (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR y -> u = v * y + x * x2 + - (v * x2) -> P)) -> (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoL y -> u = v * y + x * x2 + - (v * x2) -> P)) -> P)).
Theorem Conj_real_mul_SNo_pos__123__21: ~ (forall u:set, u :e SNoS_ omega -> (forall v:set, v :e omega -> abs_SNo (u + - (x * y)) < eps_ v) -> u = x * y).
Admitted.

End Conj_real_mul_SNo_pos__123__21.
(** Conj_real_mul_SNo_pos__127__3 TMYNkZb3QP4bEZayAUe4ZNhandvPjKMtd5g bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__127__3.
Variable x:set.
Variable y:set.
Hypothesis H0: Empty < x.
Hypothesis H1: Empty < y.
Hypothesis H2: ~ x * y :e real.
Hypothesis H4: x :e SNoS_ (ordsucc omega).
Hypothesis H5: x < omega.
Hypothesis H6: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - x) < eps_ w) -> z = x).
Hypothesis H7: SNo y.
Hypothesis H8: y :e SNoS_ (ordsucc omega).
Hypothesis H9: y < omega.
Hypothesis H10: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - y) < eps_ w) -> z = y).
Hypothesis H11: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < x -> x < w + eps_ z -> P) -> P)).
Hypothesis H12: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < y -> y < w + eps_ z -> P) -> P)).
Hypothesis H13: SNo (x * y).
Hypothesis H14: SNo (- (x * y)).
Hypothesis H15: (forall z:set, SNo z -> SNoLev z :e omega -> SNoLev z :e SNoLev (x * y)).
Hypothesis H16: Subq (SNoL x) (SNoS_ omega).
Hypothesis H17: Subq (SNoR x) (SNoS_ omega).
Hypothesis H18: Subq (SNoL y) (SNoS_ omega).
Hypothesis H19: Subq (SNoR y) (SNoS_ omega).
Theorem Conj_real_mul_SNo_pos__127__3: ~ (forall z:set, z :e SNoL x -> (forall P:prop, (forall w:set, w :e omega -> eps_ w <= x + - z -> P) -> P)).
Admitted.

End Conj_real_mul_SNo_pos__127__3.
(** Conj_real_mul_SNo_pos__129__4 TMQTB8232tywc8kYk8Pg4whEct1TpnX5Tje bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__129__4.
Variable x:set.
Variable y:set.
Hypothesis H0: Empty < x.
Hypothesis H1: Empty < y.
Hypothesis H2: ~ x * y :e real.
Hypothesis H3: SNo x.
Hypothesis H5: x < omega.
Hypothesis H6: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - x) < eps_ w) -> z = x).
Hypothesis H7: SNo y.
Hypothesis H8: SNoLev y :e ordsucc omega.
Hypothesis H9: y :e SNoS_ (ordsucc omega).
Hypothesis H10: y < omega.
Hypothesis H11: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - y) < eps_ w) -> z = y).
Hypothesis H12: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < x -> x < w + eps_ z -> P) -> P)).
Hypothesis H13: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < y -> y < w + eps_ z -> P) -> P)).
Hypothesis H14: SNo (x * y).
Hypothesis H15: SNo (- (x * y)).
Hypothesis H16: (forall z:set, SNo z -> SNoLev z :e omega -> SNoLev z :e SNoLev (x * y)).
Hypothesis H17: Subq (SNoL x) (SNoS_ omega).
Hypothesis H18: Subq (SNoR x) (SNoS_ omega).
Theorem Conj_real_mul_SNo_pos__129__4: ~ Subq (SNoL y) (SNoS_ omega).
Admitted.

End Conj_real_mul_SNo_pos__129__4.
(** Conj_real_mul_SNo_pos__130__0 TMRRwPzS6KKfBzsw5XaoSKd8ao7ZN7Z2HFN bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__130__0.
Variable x:set.
Variable y:set.
Hypothesis H1: Empty < y.
Hypothesis H2: ~ x * y :e real.
Hypothesis H3: SNo x.
Hypothesis H4: SNoLev x :e ordsucc omega.
Hypothesis H5: x :e SNoS_ (ordsucc omega).
Hypothesis H6: x < omega.
Hypothesis H7: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - x) < eps_ w) -> z = x).
Hypothesis H8: SNo y.
Hypothesis H9: SNoLev y :e ordsucc omega.
Hypothesis H10: y :e SNoS_ (ordsucc omega).
Hypothesis H11: y < omega.
Hypothesis H12: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - y) < eps_ w) -> z = y).
Hypothesis H13: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < x -> x < w + eps_ z -> P) -> P)).
Hypothesis H14: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < y -> y < w + eps_ z -> P) -> P)).
Hypothesis H15: SNo (x * y).
Hypothesis H16: SNo (- (x * y)).
Hypothesis H17: (forall z:set, SNo z -> SNoLev z :e omega -> SNoLev z :e SNoLev (x * y)).
Hypothesis H18: Subq (SNoL x) (SNoS_ omega).
Theorem Conj_real_mul_SNo_pos__130__0: ~ Subq (SNoR x) (SNoS_ omega).
Admitted.

End Conj_real_mul_SNo_pos__130__0.
(** Conj_real_mul_SNo_pos__132__4 TMPEKF2qMeDC3XrA3wWyAvwFdzZTHJEV73F bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__132__4.
Variable x:set.
Variable y:set.
Hypothesis H0: Empty < x.
Hypothesis H1: Empty < y.
Hypothesis H2: ~ x * y :e real.
Hypothesis H3: SNo x.
Hypothesis H5: x :e SNoS_ (ordsucc omega).
Hypothesis H6: x < omega.
Hypothesis H7: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - x) < eps_ w) -> z = x).
Hypothesis H8: SNo y.
Hypothesis H9: SNoLev y :e ordsucc omega.
Hypothesis H10: y :e SNoS_ (ordsucc omega).
Hypothesis H11: y < omega.
Hypothesis H12: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - y) < eps_ w) -> z = y).
Hypothesis H13: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < x -> x < w + eps_ z -> P) -> P)).
Hypothesis H14: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < y -> y < w + eps_ z -> P) -> P)).
Hypothesis H15: SNo (x * y).
Hypothesis H16: SNo (- (x * y)).
Hypothesis H17: nIn (SNoLev (x * y)) omega.
Theorem Conj_real_mul_SNo_pos__132__4: ~ (forall z:set, SNo z -> SNoLev z :e omega -> SNoLev z :e SNoLev (x * y)).
Admitted.

End Conj_real_mul_SNo_pos__132__4.
(** Conj_real_mul_SNo_pos__133__12 TMFdfgHoVkM7aZUJZJ9pGVAiMiQdyGgJHdz bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__133__12.
Variable x:set.
Variable y:set.
Hypothesis H0: Empty < x.
Hypothesis H1: Empty < y.
Hypothesis H2: ~ x * y :e real.
Hypothesis H3: SNo x.
Hypothesis H4: SNoLev x :e ordsucc omega.
Hypothesis H5: x :e SNoS_ (ordsucc omega).
Hypothesis H6: x < omega.
Hypothesis H7: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - x) < eps_ w) -> z = x).
Hypothesis H8: SNo y.
Hypothesis H9: SNoLev y :e ordsucc omega.
Hypothesis H10: y :e SNoS_ (ordsucc omega).
Hypothesis H11: y < omega.
Hypothesis H13: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < x -> x < w + eps_ z -> P) -> P)).
Hypothesis H14: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < y -> y < w + eps_ z -> P) -> P)).
Hypothesis H15: SNo (x * y).
Hypothesis H16: SNo (- (x * y)).
Theorem Conj_real_mul_SNo_pos__133__12: ~ nIn (SNoLev (x * y)) omega.
Admitted.

End Conj_real_mul_SNo_pos__133__12.
(** Conj_real_mul_SNo_pos__135__10 TMJyD52P98j7bD8o1aoVGQbrBp35vzHcoWt bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__135__10.
Variable x:set.
Variable y:set.
Hypothesis H0: Empty < x.
Hypothesis H1: Empty < y.
Hypothesis H2: ~ x * y :e real.
Hypothesis H3: SNo x.
Hypothesis H4: SNoLev x :e ordsucc omega.
Hypothesis H5: x :e SNoS_ (ordsucc omega).
Hypothesis H6: x < omega.
Hypothesis H7: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - x) < eps_ w) -> z = x).
Hypothesis H8: SNo y.
Hypothesis H9: SNoLev y :e ordsucc omega.
Hypothesis H11: y < omega.
Hypothesis H12: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - y) < eps_ w) -> z = y).
Hypothesis H13: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < x -> x < w + eps_ z -> P) -> P)).
Hypothesis H14: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < y -> y < w + eps_ z -> P) -> P)).
Theorem Conj_real_mul_SNo_pos__135__10: ~ SNo (x * y).
Admitted.

End Conj_real_mul_SNo_pos__135__10.
(** Conj_real_mul_SNo_pos__136__12 TMS5PZE3TZPN4ND1ujYfpfUWCYedEWQFXeq bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__136__12.
Variable x:set.
Variable y:set.
Hypothesis H0: Empty < x.
Hypothesis H1: Empty < y.
Hypothesis H2: ~ x * y :e real.
Hypothesis H3: SNo x.
Hypothesis H4: SNoLev x :e ordsucc omega.
Hypothesis H5: x :e SNoS_ (ordsucc omega).
Hypothesis H6: x < omega.
Hypothesis H7: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - x) < eps_ w) -> z = x).
Hypothesis H8: SNo y.
Hypothesis H9: SNoLev y :e ordsucc omega.
Hypothesis H10: y :e SNoS_ (ordsucc omega).
Hypothesis H11: y < omega.
Hypothesis H13: (forall z:set, z :e omega -> (exists w:set, w :e SNoS_ omega /\ (w < y /\ y < w + eps_ z))).
Hypothesis H14: (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < x -> x < w + eps_ z -> P) -> P)).
Theorem Conj_real_mul_SNo_pos__136__12: ~ (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < y -> y < w + eps_ z -> P) -> P)).
Admitted.

End Conj_real_mul_SNo_pos__136__12.
(** Conj_real_mul_SNo_pos__137__4 TMbbdYEKJCjEjJTwRC5ytepJEaBK8R6mgxW bounty of about 25 bars **)
Section Conj_real_mul_SNo_pos__137__4.
Variable x:set.
Variable y:set.
Hypothesis H0: Empty < x.
Hypothesis H1: Empty < y.
Hypothesis H2: ~ x * y :e real.
Hypothesis H3: SNo x.
Hypothesis H5: x :e SNoS_ (ordsucc omega).
Hypothesis H6: x < omega.
Hypothesis H7: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - x) < eps_ w) -> z = x).
Hypothesis H8: (forall z:set, z :e omega -> (exists w:set, w :e SNoS_ omega /\ (w < x /\ x < w + eps_ z))).
Hypothesis H9: SNo y.
Hypothesis H10: SNoLev y :e ordsucc omega.
Hypothesis H11: y :e SNoS_ (ordsucc omega).
Hypothesis H12: y < omega.
Hypothesis H13: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - y) < eps_ w) -> z = y).
Hypothesis H14: (forall z:set, z :e omega -> (exists w:set, w :e SNoS_ omega /\ (w < y /\ y < w + eps_ z))).
Theorem Conj_real_mul_SNo_pos__137__4: ~ (forall z:set, z :e omega -> (forall P:prop, (forall w:set, w :e SNoS_ omega -> Empty < w -> w < x -> x < w + eps_ z -> P) -> P)).
Admitted.

End Conj_real_mul_SNo_pos__137__4.
(** Conj_abs_SNo_intvl_bd__1__1 TMaPQSoyBWSFwADtt1AdDWQ33syELGW1SDa bounty of about 25 bars **)
Section Conj_abs_SNo_intvl_bd__1__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: y < x + z.
Hypothesis H4: Empty <= y + - x.
Theorem Conj_abs_SNo_intvl_bd__1__1: abs_SNo (y + - x) = y + - x -> abs_SNo (y + - x) < z.
Admitted.

End Conj_abs_SNo_intvl_bd__1__1.
(** Conj_pos_small_real_recip_ex__6__9 TMPFhGY4vjtoJ52pG4WQyXYdYaHUNp5YYGB bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__6__9.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: x < ordsucc Empty.
Hypothesis H1: SNo x.
Hypothesis H2: SNo (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H3: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u) -> SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u)) < w).
Hypothesis H4: y :e SNoS_ omega.
Hypothesis H5: (forall w:set, w :e omega -> abs_SNo (y + - (SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u)))) < eps_ w).
Hypothesis H6: SNo y.
Hypothesis H7: SNo (x * y).
Hypothesis H8: SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < y.
Hypothesis H10: ordsucc Empty <= x * y + - (eps_ z).
Theorem Conj_pos_small_real_recip_ex__6__9: ~ SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < y + - (eps_ z).
Admitted.

End Conj_pos_small_real_recip_ex__6__9.
(** Conj_pos_small_real_recip_ex__8__0 TMRvBrLEdB8cJdjdMEKvs4LRugzKhp57Mof bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__8__0.
Variable x:set.
Variable y:set.
Hypothesis H1: ~ (exists z:set, z :e real /\ x * z = ordsucc Empty).
Hypothesis H2: SNo x.
Hypothesis H3: SNo (SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H4: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty) -> z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H5: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w) -> SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z).
Hypothesis H6: y :e SNoS_ omega.
Hypothesis H7: (forall z:set, z :e omega -> abs_SNo (y + - (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ z).
Hypothesis H8: SNo y.
Hypothesis H9: y :e real.
Hypothesis H10: SNo (x * y).
Hypothesis H11: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - (x * y)) < eps_ w) -> z = x * y).
Hypothesis H12: x * y < ordsucc Empty -> (exists z:set, z :e omega /\ (x * y + eps_ z) <= ordsucc Empty).
Theorem Conj_pos_small_real_recip_ex__8__0: (ordsucc Empty < x * y -> (exists z:set, z :e omega /\ ordsucc Empty <= x * y + - (eps_ z))) -> y = SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)).
Admitted.

End Conj_pos_small_real_recip_ex__8__0.
(** Conj_pos_small_real_recip_ex__9__3 TMUC6SVsJ4pj4b6h72e8rth32dqURg96cm2 bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__9__3.
Variable x:set.
Variable y:set.
Hypothesis H0: x < ordsucc Empty.
Hypothesis H1: ~ (exists z:set, z :e real /\ x * z = ordsucc Empty).
Hypothesis H2: SNo x.
Hypothesis H4: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty) -> z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H5: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w) -> SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z).
Hypothesis H6: y :e SNoS_ omega.
Hypothesis H7: (forall z:set, z :e omega -> abs_SNo (y + - (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ z).
Hypothesis H8: SNo y.
Hypothesis H9: y :e real.
Hypothesis H10: SNo (x * y).
Hypothesis H11: (forall z:set, z :e SNoS_ omega -> (forall w:set, w :e omega -> abs_SNo (z + - (x * y)) < eps_ w) -> z = x * y).
Hypothesis H12: SNo (- (x * y)).
Theorem Conj_pos_small_real_recip_ex__9__3: (x * y < ordsucc Empty -> (exists z:set, z :e omega /\ (x * y + eps_ z) <= ordsucc Empty)) -> y = SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)).
Admitted.

End Conj_pos_small_real_recip_ex__9__3.
(** Conj_pos_small_real_recip_ex__11__1 TMMyT9UihYiCAz1imqwARNcY4xDFPpK2wyS bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__11__1.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e real.
Hypothesis H2: ~ (exists z:set, z :e real /\ x * z = ordsucc Empty).
Hypothesis H3: SNo x.
Hypothesis H4: SNo (SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H5: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty) -> z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H6: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w) -> SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z).
Hypothesis H7: y :e SNoS_ omega.
Hypothesis H8: (forall z:set, z :e omega -> abs_SNo (y + - (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ z).
Hypothesis H9: SNo y.
Hypothesis H10: y :e real.
Theorem Conj_pos_small_real_recip_ex__11__1: x * y :e real -> y = SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)).
Admitted.

End Conj_pos_small_real_recip_ex__11__1.
(** Conj_pos_small_real_recip_ex__11__2 TMbRkHPN6tCX8U7x1vPQss3jfzXWm36frrA bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__11__2.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e real.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H3: SNo x.
Hypothesis H4: SNo (SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H5: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty) -> z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H6: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w) -> SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z).
Hypothesis H7: y :e SNoS_ omega.
Hypothesis H8: (forall z:set, z :e omega -> abs_SNo (y + - (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ z).
Hypothesis H9: SNo y.
Hypothesis H10: y :e real.
Theorem Conj_pos_small_real_recip_ex__11__2: x * y :e real -> y = SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)).
Admitted.

End Conj_pos_small_real_recip_ex__11__2.
(** Conj_pos_small_real_recip_ex__11__7 TMYt1mpvVAUNeAz8K7uEQ76yn4oCL36RLiq bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__11__7.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e real.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H2: ~ (exists z:set, z :e real /\ x * z = ordsucc Empty).
Hypothesis H3: SNo x.
Hypothesis H4: SNo (SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H5: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty) -> z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H6: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w) -> SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z).
Hypothesis H8: (forall z:set, z :e omega -> abs_SNo (y + - (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ z).
Hypothesis H9: SNo y.
Hypothesis H10: y :e real.
Theorem Conj_pos_small_real_recip_ex__11__7: x * y :e real -> y = SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)).
Admitted.

End Conj_pos_small_real_recip_ex__11__7.
(** Conj_pos_small_real_recip_ex__12__0 TMXejCpXMA14xRhTB1xfqy7GqeQ7ZCfa8e2 bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__12__0.
Variable x:set.
Variable y:set.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H2: ~ (exists z:set, z :e real /\ x * z = ordsucc Empty).
Hypothesis H3: SNo x.
Hypothesis H4: SNo (SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H5: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty) -> z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H6: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w) -> SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z).
Hypothesis H7: y :e SNoS_ omega.
Hypothesis H8: (forall z:set, z :e omega -> abs_SNo (y + - (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ z).
Hypothesis H9: SNo y.
Theorem Conj_pos_small_real_recip_ex__12__0: y :e real -> y = SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)).
Admitted.

End Conj_pos_small_real_recip_ex__12__0.
(** Conj_pos_small_real_recip_ex__12__9 TMXF87PV4nDSoWX5w445ySm7xNHY8nkjPmQ bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__12__9.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e real.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H2: ~ (exists z:set, z :e real /\ x * z = ordsucc Empty).
Hypothesis H3: SNo x.
Hypothesis H4: SNo (SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H5: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty) -> z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H6: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w) -> SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z).
Hypothesis H7: y :e SNoS_ omega.
Hypothesis H8: (forall z:set, z :e omega -> abs_SNo (y + - (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ z).
Theorem Conj_pos_small_real_recip_ex__12__9: y :e real -> y = SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)).
Admitted.

End Conj_pos_small_real_recip_ex__12__9.
(** Conj_pos_small_real_recip_ex__13__3 TMSQsSq5kKeYas4A4JPvzs9EYjsG9MwRL84 bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__13__3.
Variable x:set.
Variable y:set.
Hypothesis H0: Empty < x.
Hypothesis H1: SNo x.
Hypothesis H2: SNo (SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H4: y :e omega.
Hypothesis H5: eps_ y <= x.
Hypothesis H6: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) y).
Hypothesis H7: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) y).
Theorem Conj_pos_small_real_recip_ex__13__3: exp_SNo_nat (ordsucc (ordsucc Empty)) y + ordsucc Empty :e omega -> SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)) < omega.
Admitted.

End Conj_pos_small_real_recip_ex__13__3.
(** Conj_pos_small_real_recip_ex__17__1 TMMPDKY5xGhBSK9UB7QuJueypeCtTpDLhtB bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__17__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: Empty < x.
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty) -> w < SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u))).
Hypothesis H4: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u) -> SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u)) < w).
Hypothesis H5: SNo (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H6: SNo (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H7: SNo (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H8: y :e omega.
Hypothesis H9: z :e SNoS_ omega.
Hypothesis H10: z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)).
Hypothesis H11: SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z + eps_ (ordsucc y).
Hypothesis H12: SNo z.
Hypothesis H13: SNo (x * z).
Hypothesis H14: SNo (eps_ (ordsucc y)).
Hypothesis H15: SNo (x * eps_ (ordsucc y)).
Hypothesis H16: SNo (z + eps_ (ordsucc y)).
Hypothesis H17: SNo (ordsucc Empty + - (x * z)).
Hypothesis H18: SNo (x * z + - (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))).
Theorem Conj_pos_small_real_recip_ex__17__1: x * (z + eps_ (ordsucc y)) < x * z + eps_ (ordsucc y) -> abs_SNo (ordsucc Empty + - (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ y.
Admitted.

End Conj_pos_small_real_recip_ex__17__1.
(** Conj_pos_small_real_recip_ex__17__6 TMXPsjo4XsgfoQhfLGUwyNDDTMxGWk6pU8Z bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__17__6.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: Empty < x.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty) -> w < SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u))).
Hypothesis H4: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u) -> SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u)) < w).
Hypothesis H5: SNo (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H7: SNo (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H8: y :e omega.
Hypothesis H9: z :e SNoS_ omega.
Hypothesis H10: z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)).
Hypothesis H11: SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z + eps_ (ordsucc y).
Hypothesis H12: SNo z.
Hypothesis H13: SNo (x * z).
Hypothesis H14: SNo (eps_ (ordsucc y)).
Hypothesis H15: SNo (x * eps_ (ordsucc y)).
Hypothesis H16: SNo (z + eps_ (ordsucc y)).
Hypothesis H17: SNo (ordsucc Empty + - (x * z)).
Hypothesis H18: SNo (x * z + - (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))).
Theorem Conj_pos_small_real_recip_ex__17__6: x * (z + eps_ (ordsucc y)) < x * z + eps_ (ordsucc y) -> abs_SNo (ordsucc Empty + - (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ y.
Admitted.

End Conj_pos_small_real_recip_ex__17__6.
(** Conj_pos_small_real_recip_ex__17__7 TMXPsjo4XsgfoQhfLGUwyNDDTMxGWk6pU8Z bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__17__7.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: Empty < x.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty) -> w < SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u))).
Hypothesis H4: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u) -> SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u)) < w).
Hypothesis H5: SNo (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H6: SNo (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H8: y :e omega.
Hypothesis H9: z :e SNoS_ omega.
Hypothesis H10: z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)).
Hypothesis H11: SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z + eps_ (ordsucc y).
Hypothesis H12: SNo z.
Hypothesis H13: SNo (x * z).
Hypothesis H14: SNo (eps_ (ordsucc y)).
Hypothesis H15: SNo (x * eps_ (ordsucc y)).
Hypothesis H16: SNo (z + eps_ (ordsucc y)).
Hypothesis H17: SNo (ordsucc Empty + - (x * z)).
Hypothesis H18: SNo (x * z + - (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))).
Theorem Conj_pos_small_real_recip_ex__17__7: x * (z + eps_ (ordsucc y)) < x * z + eps_ (ordsucc y) -> abs_SNo (ordsucc Empty + - (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ y.
Admitted.

End Conj_pos_small_real_recip_ex__17__7.
(** Conj_pos_small_real_recip_ex__18__8 TMNhPY5S2ATU9ibFKSrWbMMCjJU9SLEJ3DT bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__18__8.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: Empty < x.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty) -> w < SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u))).
Hypothesis H4: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u) -> SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u)) < w).
Hypothesis H5: SNo (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H6: SNo (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H7: SNo (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H9: z :e SNoS_ omega.
Hypothesis H10: z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)).
Hypothesis H11: SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z + eps_ (ordsucc y).
Hypothesis H12: SNo z.
Hypothesis H13: SNo (x * z).
Hypothesis H14: SNo (eps_ (ordsucc y)).
Hypothesis H15: SNo (x * eps_ (ordsucc y)).
Hypothesis H16: SNo (z + eps_ (ordsucc y)).
Hypothesis H17: SNo (ordsucc Empty + - (x * z)).
Theorem Conj_pos_small_real_recip_ex__18__8: SNo (x * z + - (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) -> abs_SNo (ordsucc Empty + - (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ y.
Admitted.

End Conj_pos_small_real_recip_ex__18__8.
(** Conj_pos_small_real_recip_ex__19__2 TMU9digWpqJEjvHUH9hcZETHWnhbveFMXYv bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__19__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: Empty < x.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H3: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty) -> w < SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u))).
Hypothesis H4: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u) -> SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u)) < w).
Hypothesis H5: SNo (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H6: SNo (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H7: SNo (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H8: y :e omega.
Hypothesis H9: z :e SNoS_ omega.
Hypothesis H10: z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)).
Hypothesis H11: SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z + eps_ (ordsucc y).
Hypothesis H12: SNo z.
Hypothesis H13: SNo (x * z).
Hypothesis H14: SNo (eps_ (ordsucc y)).
Hypothesis H15: SNo (x * eps_ (ordsucc y)).
Hypothesis H16: SNo (z + eps_ (ordsucc y)).
Theorem Conj_pos_small_real_recip_ex__19__2: SNo (ordsucc Empty + - (x * z)) -> abs_SNo (ordsucc Empty + - (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ y.
Admitted.

End Conj_pos_small_real_recip_ex__19__2.
(** Conj_pos_small_real_recip_ex__23__0 TMX7GHFNnh4sXd8mZC6EALQPWCbn5Sq8xHg bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__23__0.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H2: SNo x.
Hypothesis H3: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty) -> w < SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u))).
Hypothesis H4: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u) -> SNoCut (Sep (SNoS_ omega) (fun u:set => x * u < ordsucc Empty)) (Sep (SNoS_ omega) (fun u:set => ordsucc Empty < x * u)) < w).
Hypothesis H5: SNo (SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H6: SNo (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H7: SNo (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w))).
Hypothesis H8: y :e omega.
Hypothesis H9: z :e SNoS_ omega.
Hypothesis H10: z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)).
Hypothesis H11: SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z + eps_ (ordsucc y).
Hypothesis H12: SNo z.
Theorem Conj_pos_small_real_recip_ex__23__0: SNo (x * z) -> abs_SNo (ordsucc Empty + - (x * SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)))) < eps_ y.
Admitted.

End Conj_pos_small_real_recip_ex__23__0.
(** Conj_pos_small_real_recip_ex__24__3 TMZHcw7XtrAH23Q4QiyN9KZuUR2MDo2wHtp bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__24__3.
Variable x:set.
Hypothesis H0: Empty < x.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H2: ~ (exists y:set, y :e real /\ x * y = ordsucc Empty).
Hypothesis H4: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty) -> y < SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H5: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z) -> SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)) < y).
Hypothesis H6: SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y)) :e real.
Hypothesis H7: SNo (SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y))).
Hypothesis H8: (forall y:set, y :e omega -> (exists z:set, z :e SNoS_ omega /\ (z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) /\ SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z + eps_ y))).
Hypothesis H9: x * SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y)) :e real.
Theorem Conj_pos_small_real_recip_ex__24__3: ~ SNo (x * SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y))).
Admitted.

End Conj_pos_small_real_recip_ex__24__3.
(** Conj_pos_small_real_recip_ex__24__8 TMPWakYUV4PUbKqaTyBdMCjwNLuAF2WEcQh bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__24__8.
Variable x:set.
Hypothesis H0: Empty < x.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H2: ~ (exists y:set, y :e real /\ x * y = ordsucc Empty).
Hypothesis H3: SNo x.
Hypothesis H4: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty) -> y < SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H5: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z) -> SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)) < y).
Hypothesis H6: SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y)) :e real.
Hypothesis H7: SNo (SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y))).
Hypothesis H9: x * SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y)) :e real.
Theorem Conj_pos_small_real_recip_ex__24__8: ~ SNo (x * SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y))).
Admitted.

End Conj_pos_small_real_recip_ex__24__8.
(** Conj_pos_small_real_recip_ex__24__9 TMX5TjYbGMH25Z4fZpjthbpdd6dwTmDfzFT bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__24__9.
Variable x:set.
Hypothesis H0: Empty < x.
Hypothesis H1: x < ordsucc Empty.
Hypothesis H2: ~ (exists y:set, y :e real /\ x * y = ordsucc Empty).
Hypothesis H3: SNo x.
Hypothesis H4: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty) -> y < SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H5: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z) -> SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)) < y).
Hypothesis H6: SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y)) :e real.
Hypothesis H7: SNo (SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y))).
Hypothesis H8: (forall y:set, y :e omega -> (exists z:set, z :e SNoS_ omega /\ (z < SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) /\ SNoCut (Sep (SNoS_ omega) (fun w:set => x * w < ordsucc Empty)) (Sep (SNoS_ omega) (fun w:set => ordsucc Empty < x * w)) < z + eps_ y))).
Theorem Conj_pos_small_real_recip_ex__24__9: ~ SNo (x * SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y))).
Admitted.

End Conj_pos_small_real_recip_ex__24__9.
(** Conj_pos_small_real_recip_ex__26__3 TMZAVZB6SwcbSPJRUG28LRHBFF6LQ1SwZz1 bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__26__3.
Variable x:set.
Hypothesis H0: x :e real.
Hypothesis H1: Empty < x.
Hypothesis H2: x < ordsucc Empty.
Hypothesis H4: SNo x.
Hypothesis H5: (forall y:set, y :e SNoS_ omega -> (forall z:set, z :e omega -> abs_SNo (y + - x) < eps_ z) -> y = x).
Hypothesis H6: SNo (SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y))).
Hypothesis H7: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty) -> y < SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z))).
Hypothesis H8: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z) -> SNoCut (Sep (SNoS_ omega) (fun z:set => x * z < ordsucc Empty)) (Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z)) < y).
Hypothesis H9: SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y)) :e SNoS_ (ordsucc omega).
Theorem Conj_pos_small_real_recip_ex__26__3: ~ SNoCut (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y)) :e real.
Admitted.

End Conj_pos_small_real_recip_ex__26__3.
(** Conj_pos_small_real_recip_ex__28__6 TMWkBcL9rtKJG7Skoz4xgqiWb2fQLfW49ez bounty of about 25 bars **)
Section Conj_pos_small_real_recip_ex__28__6.
Variable x:set.
Hypothesis H0: x :e real.
Hypothesis H1: Empty < x.
Hypothesis H2: x < ordsucc Empty.
Hypothesis H3: ~ (exists y:set, y :e real /\ x * y = ordsucc Empty).
Hypothesis H4: SNo x.
Hypothesis H5: (forall y:set, y :e SNoS_ omega -> (forall z:set, z :e omega -> abs_SNo (y + - x) < eps_ z) -> y = x).
Hypothesis H7: (forall y:set, y :e Sep (SNoS_ omega) (fun z:set => ordsucc Empty < x * z) -> (forall P:prop, (SNo y -> SNoLev y :e omega -> ordsucc Empty < x * y -> P) -> P)).
Theorem Conj_pos_small_real_recip_ex__28__6: ~ SNoCutP (Sep (SNoS_ omega) (fun y:set => x * y < ordsucc Empty)) (Sep (SNoS_ omega) (fun y:set => ordsucc Empty < x * y)).
Admitted.

End Conj_pos_small_real_recip_ex__28__6.
(** Conj_pos_real_recip_ex__1__3 TMYxfzWP3TyvFGP5mgke3usKuW1W2dYceXn bounty of about 25 bars **)
Section Conj_pos_real_recip_ex__1__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: y :e omega.
Hypothesis H2: z :e real.
Theorem Conj_pos_real_recip_ex__1__3: SNo (eps_ y) -> (exists w:set, w :e real /\ x * w = ordsucc Empty).
Admitted.

End Conj_pos_real_recip_ex__1__3.
(** Conj_pos_real_recip_ex__2__4 TMHduHoFc1HwuDUrnuvnEh1t2XvbuPBKnfg bounty of about 25 bars **)
Section Conj_pos_real_recip_ex__2__4.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e real.
Hypothesis H1: Empty < x.
Hypothesis H2: SNo x.
Hypothesis H3: y :e omega.
Hypothesis H5: eps_ y :e real.
Theorem Conj_pos_real_recip_ex__2__4: Empty < eps_ y * x -> (exists z:set, z :e real /\ x * z = ordsucc Empty).
Admitted.

End Conj_pos_real_recip_ex__2__4.
(** Conj_real_Archimedean__2__3 TMZ22KSEEWvE1jsZxsfmtuBURBgnGUx8TPh bounty of about 25 bars **)
Section Conj_real_Archimedean__2__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo (exp_SNo_nat (ordsucc (ordsucc Empty)) y).
Hypothesis H2: ordsucc Empty <= exp_SNo_nat (ordsucc (ordsucc Empty)) y * x.
Hypothesis H4: SNo z.
Theorem Conj_real_Archimedean__2__3: Empty <= z -> z * ordsucc Empty <= z * exp_SNo_nat (ordsucc (ordsucc Empty)) y * x.
Admitted.

End Conj_real_Archimedean__2__3.
(** Conj_real_Archimedean__8__2 TMHtre3BvKpSrkGACbgJDx89321ys2Q2ymN bounty of about 25 bars **)
Section Conj_real_Archimedean__8__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: y :e real.
Hypothesis H1: SNo x.
Hypothesis H3: eps_ z <= x.
Theorem Conj_real_Archimedean__8__2: nat_p (exp_SNo_nat (ordsucc (ordsucc Empty)) z) -> (exists w:set, w :e omega /\ y <= w * x).
Admitted.

End Conj_real_Archimedean__8__2.
(** Conj_real_complete1__3__1 TMHYkQPEwgBGgMwub78UEBPqwSGWyuy8qK6 bounty of about 25 bars **)
Section Conj_real_complete1__3__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e omega -> ap x u <= ap y u /\ ap x u <= ap x (ordsucc u) /\ ap y (ordsucc u) <= ap y u).
Hypothesis H2: (forall u:set, u :e z -> ap x u <= ap x z).
Hypothesis H3: w :e ordsucc z.
Hypothesis H4: z :e omega.
Theorem Conj_real_complete1__3__1: ordsucc z :e omega -> ap x w <= ap x (ordsucc z).
Admitted.

End Conj_real_complete1__3__1.
(** Conj_real_complete1__3__3 TMTP39b7t9hBLGCVUgKEhEwYFGg9Ugy4vfF bounty of about 25 bars **)
Section Conj_real_complete1__3__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e omega -> ap x u <= ap y u /\ ap x u <= ap x (ordsucc u) /\ ap y (ordsucc u) <= ap y u).
Hypothesis H1: (forall u:set, u :e omega -> SNo (ap x u)).
Hypothesis H2: (forall u:set, u :e z -> ap x u <= ap x z).
Hypothesis H4: z :e omega.
Theorem Conj_real_complete1__3__3: ordsucc z :e omega -> ap x w <= ap x (ordsucc z).
Admitted.

End Conj_real_complete1__3__3.
(** Conj_real_complete1__4__3 TMTdUussKNkA6rwhnezaxmLyw9kt9yom4vH bounty of about 25 bars **)
Section Conj_real_complete1__4__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e omega -> ap x u <= ap y u /\ ap x u <= ap x (ordsucc u) /\ ap y (ordsucc u) <= ap y u).
Hypothesis H1: (forall u:set, u :e omega -> SNo (ap x u)).
Hypothesis H2: nat_p z.
Hypothesis H4: w :e ordsucc z.
Theorem Conj_real_complete1__4__3: z :e omega -> ap x w <= ap x (ordsucc z).
Admitted.

End Conj_real_complete1__4__3.
(** Conj_real_complete1__9__1 TMLsAQBkCCJTxwoGjtCzWefeKmuV12qcAYs bounty of about 25 bars **)
Section Conj_real_complete1__9__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: (forall u:set, u :e omega -> ap x u <= ap y u /\ ap x u <= ap x (ordsucc u) /\ ap y (ordsucc u) <= ap y u).
Hypothesis H2: (forall u:set, u :e omega -> SNo (ap y u)).
Hypothesis H3: (forall u:set, nat_p u -> (forall v:set, v :e u -> ap x v <= ap x u)).
Hypothesis H4: (forall u:set, nat_p u -> (forall v:set, v :e u -> ap y u <= ap y v)).
Hypothesis H5: z :e omega.
Hypothesis H6: w :e omega.
Hypothesis H7: nat_p z.
Hypothesis H8: nat_p w.
Theorem Conj_real_complete1__9__1: ap x z <= ap y z -> ap x z <= ap y w.
Admitted.

End Conj_real_complete1__9__1.
(** Conj_real_complete1__12__0 TMMSiP4yJQCTTuknYDALik3YjGSFMxFzFeR bounty of about 25 bars **)
Section Conj_real_complete1__12__0.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H1: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H2: SNo (SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w))).
Hypothesis H3: (forall w:set, SNo w -> (forall u:set, u :e Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ v < ap x x2) -> u < w) -> (forall u:set, u :e Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ ap y x2 < v) -> w < u) -> Subq (SNoLev (SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)))) (SNoLev w) /\ SNoEq_ (SNoLev (SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)))) (SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u))) w).
Hypothesis H4: (forall w:set, w :e omega -> ap x w <= SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)) /\ SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)) <= ap y w).
Hypothesis H5: z :e SNoS_ omega.
Hypothesis H6: ~ (z :e Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u) \/ z :e Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)).
Hypothesis H7: SNoLev z :e omega.
Hypothesis H8: ordinal (SNoLev z).
Hypothesis H9: SNo z.
Hypothesis H10: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v) -> w < z).
Theorem Conj_real_complete1__12__0: ~ (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u) -> z < w).
Admitted.

End Conj_real_complete1__12__0.
(** Conj_real_complete1__12__2 TMQDih3V9NmyYNj6zh1PL2niw62w8n1C2Cs bounty of about 25 bars **)
Section Conj_real_complete1__12__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ~ (exists w:set, w :e real /\ (forall u:set, u :e omega -> ap x u <= w /\ w <= ap y u)).
Hypothesis H1: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H3: (forall w:set, SNo w -> (forall u:set, u :e Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ v < ap x x2) -> u < w) -> (forall u:set, u :e Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ ap y x2 < v) -> w < u) -> Subq (SNoLev (SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)))) (SNoLev w) /\ SNoEq_ (SNoLev (SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)))) (SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u))) w).
Hypothesis H4: (forall w:set, w :e omega -> ap x w <= SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)) /\ SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)) <= ap y w).
Hypothesis H5: z :e SNoS_ omega.
Hypothesis H6: ~ (z :e Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u) \/ z :e Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)).
Hypothesis H7: SNoLev z :e omega.
Hypothesis H8: ordinal (SNoLev z).
Hypothesis H9: SNo z.
Hypothesis H10: (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v) -> w < z).
Theorem Conj_real_complete1__12__2: ~ (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u) -> z < w).
Admitted.

End Conj_real_complete1__12__2.
(** Conj_real_complete1__13__7 TMSzrrfisUb6ZZ9opJymXNtpxQ7bC7h1RmT bounty of about 25 bars **)
Section Conj_real_complete1__13__7.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: ~ (exists w:set, w :e real /\ (forall u:set, u :e omega -> ap x u <= w /\ w <= ap y u)).
Hypothesis H1: (forall w:set, w :e omega -> SNo (ap x w)).
Hypothesis H2: (forall w:set, w :e omega -> SNo (ap y w)).
Hypothesis H3: SNo (SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w))).
Hypothesis H4: (forall w:set, SNo w -> (forall u:set, u :e Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ v < ap x x2) -> u < w) -> (forall u:set, u :e Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ ap y x2 < v) -> w < u) -> Subq (SNoLev (SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)))) (SNoLev w) /\ SNoEq_ (SNoLev (SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)))) (SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u))) w).
Hypothesis H5: (forall w:set, w :e omega -> ap x w <= SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)) /\ SNoCut (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v)) (Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u)) <= ap y w).
Hypothesis H6: z :e SNoS_ omega.
Hypothesis H8: SNoLev z :e omega.
Hypothesis H9: ordinal (SNoLev z).
Hypothesis H10: SNo z.
Theorem Conj_real_complete1__13__7: ~ (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v) -> w < z).
Admitted.

End Conj_real_complete1__13__7.
(** Conj_real_complete1__14__5 TMVsfdvd4ET23WBhN2akt6MDBS2hvAKukPP bounty of about 25 bars **)
Section Conj_real_complete1__14__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, v :e omega -> SNo (ap y v)).
Hypothesis H1: SNo (SNoCut (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ v < ap x x2)) (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ ap y x2 < v))).
Hypothesis H2: (forall v:set, v :e omega -> abs_SNo (z + - (SNoCut (Sep (SNoS_ omega) (fun x2:set => exists y2:set, y2 :e omega /\ x2 < ap x y2)) (Sep (SNoS_ omega) (fun x2:set => exists y2:set, y2 :e omega /\ ap y y2 < x2)))) < eps_ v).
Hypothesis H3: SNo z.
Hypothesis H4: w :e omega.
Hypothesis H6: u :e omega.
Hypothesis H7: Empty < z + - (ap y w).
Hypothesis H8: SNoCut (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ v < ap x x2)) (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ ap y x2 < v)) <= ap y w.
Theorem Conj_real_complete1__14__5: Empty < z + - (SNoCut (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ v < ap x x2)) (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ ap y x2 < v))) -> abs_SNo (z + - (ap y w)) < eps_ u.
Admitted.

End Conj_real_complete1__14__5.
(** Conj_real_complete1__15__6 TMdW3M8me4jck3p1HzyEF7sB1VQYNsooomR bounty of about 25 bars **)
Section Conj_real_complete1__15__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, v :e omega -> SNo (ap y v)).
Hypothesis H1: SNo (SNoCut (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ v < ap x x2)) (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ ap y x2 < v))).
Hypothesis H2: (forall v:set, v :e omega -> SNoCut (Sep (SNoS_ omega) (fun x2:set => exists y2:set, y2 :e omega /\ x2 < ap x y2)) (Sep (SNoS_ omega) (fun x2:set => exists y2:set, y2 :e omega /\ ap y y2 < x2)) <= ap y v).
Hypothesis H3: (forall v:set, v :e omega -> abs_SNo (z + - (SNoCut (Sep (SNoS_ omega) (fun x2:set => exists y2:set, y2 :e omega /\ x2 < ap x y2)) (Sep (SNoS_ omega) (fun x2:set => exists y2:set, y2 :e omega /\ ap y y2 < x2)))) < eps_ v).
Hypothesis H4: SNo z.
Hypothesis H5: w :e omega.
Hypothesis H7: u :e omega.
Hypothesis H8: Empty < z + - (ap y w).
Theorem Conj_real_complete1__15__6: SNoCut (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ v < ap x x2)) (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ ap y x2 < v)) <= ap y w -> abs_SNo (z + - (ap y w)) < eps_ u.
Admitted.

End Conj_real_complete1__15__6.
(** Conj_real_complete1__20__7 TMTous61Px84n5jVyrkxN13CSWJsz1ioskB bounty of about 25 bars **)
Section Conj_real_complete1__20__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, v :e omega -> SNo (ap x v)).
Hypothesis H1: SNo (SNoCut (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ v < ap x x2)) (Sep (SNoS_ omega) (fun v:set => exists x2:set, x2 :e omega /\ ap y x2 < v))).
Hypothesis H2: (forall v:set, v :e omega -> ap x v <= SNoCut (Sep (SNoS_ omega) (fun x2:set => exists y2:set, y2 :e omega /\ x2 < ap x y2)) (Sep (SNoS_ omega) (fun x2:set => exists y2:set, y2 :e omega /\ ap y y2 < x2))).
Hypothesis H3: (forall v:set, v :e omega -> abs_SNo (z + - (SNoCut (Sep (SNoS_ omega) (fun x2:set => exists y2:set, y2 :e omega /\ x2 < ap x y2)) (Sep (SNoS_ omega) (fun x2:set => exists y2:set, y2 :e omega /\ ap y y2 < x2)))) < eps_ v).
Hypothesis H4: SNo z.
Hypothesis H5: w :e omega.
Hypothesis H6: z < ap x w.
Theorem Conj_real_complete1__20__7: Empty < ap x w + - z -> abs_SNo (z + - (ap x w)) < eps_ u.
Admitted.

End Conj_real_complete1__20__7.
(** Conj_real_complete1__25__7 TMPVaLP5LsFCgAEccyv1DMAQTtsK2YnG9nS bounty of about 25 bars **)
Section Conj_real_complete1__25__7.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e setexp real omega.
Hypothesis H1: y :e setexp real omega.
Hypothesis H2: ~ (exists z:set, z :e real /\ (forall w:set, w :e omega -> ap x w <= z /\ z <= ap y w)).
Hypothesis H3: (forall z:set, z :e omega -> SNo (ap x z)).
Hypothesis H4: (forall z:set, z :e omega -> SNo (ap y z)).
Hypothesis H5: Subq (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ z < ap x w)) (SNoS_ omega).
Hypothesis H6: Subq (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ ap y w < z)) (SNoS_ omega).
Hypothesis H8: SNo (SNoCut (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ z < ap x w)) (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ ap y w < z))).
Hypothesis H9: (forall z:set, SNo z -> (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v) -> w < z) -> (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u) -> z < w) -> Subq (SNoLev (SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)))) (SNoLev z) /\ SNoEq_ (SNoLev (SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)))) (SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w))) z).
Hypothesis H10: (forall z:set, z :e omega -> ap x z <= SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w))).
Hypothesis H11: (forall z:set, z :e omega -> SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)) <= ap y z).
Theorem Conj_real_complete1__25__7: ~ (forall z:set, z :e omega -> ap x z <= SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)) /\ SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)) <= ap y z).
Admitted.

End Conj_real_complete1__25__7.
(** Conj_real_complete1__26__11 TMKB3eGR57KrnConpMuX3dqK973krYn4LVU bounty of about 25 bars **)
Section Conj_real_complete1__26__11.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e setexp real omega.
Hypothesis H1: y :e setexp real omega.
Hypothesis H2: ~ (exists z:set, z :e real /\ (forall w:set, w :e omega -> ap x w <= z /\ z <= ap y w)).
Hypothesis H3: (forall z:set, z :e omega -> SNo (ap x z)).
Hypothesis H4: (forall z:set, z :e omega -> SNo (ap y z)).
Hypothesis H5: (forall z:set, z :e omega -> (forall w:set, w :e omega -> ap x z <= ap y w)).
Hypothesis H6: Subq (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ z < ap x w)) (SNoS_ omega).
Hypothesis H7: Subq (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ ap y w < z)) (SNoS_ omega).
Hypothesis H8: SNoCutP (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ z < ap x w)) (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ ap y w < z)).
Hypothesis H9: SNo (SNoCut (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ z < ap x w)) (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ ap y w < z))).
Hypothesis H10: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w) -> SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)) < z).
Hypothesis H12: (forall z:set, z :e omega -> ap x z <= SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w))).
Theorem Conj_real_complete1__26__11: ~ (forall z:set, z :e omega -> SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)) <= ap y z).
Admitted.

End Conj_real_complete1__26__11.
(** Conj_real_complete1__27__11 TMdxSfFcq3FdqmSNeoLt7E3REakvYwcepxA bounty of about 25 bars **)
Section Conj_real_complete1__27__11.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e setexp real omega.
Hypothesis H1: y :e setexp real omega.
Hypothesis H2: ~ (exists z:set, z :e real /\ (forall w:set, w :e omega -> ap x w <= z /\ z <= ap y w)).
Hypothesis H3: (forall z:set, z :e omega -> SNo (ap x z)).
Hypothesis H4: (forall z:set, z :e omega -> SNo (ap y z)).
Hypothesis H5: (forall z:set, z :e omega -> (forall w:set, w :e omega -> ap x z <= ap y w)).
Hypothesis H6: Subq (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ z < ap x w)) (SNoS_ omega).
Hypothesis H7: Subq (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ ap y w < z)) (SNoS_ omega).
Hypothesis H8: SNoCutP (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ z < ap x w)) (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ ap y w < z)).
Hypothesis H9: SNo (SNoCut (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ z < ap x w)) (Sep (SNoS_ omega) (fun z:set => exists w:set, w :e omega /\ ap y w < z))).
Hypothesis H10: (forall z:set, z :e Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u) -> z < SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w))).
Hypothesis H12: (forall z:set, SNo z -> (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ u < ap x v) -> w < z) -> (forall w:set, w :e Sep (SNoS_ omega) (fun u:set => exists v:set, v :e omega /\ ap y v < u) -> z < w) -> Subq (SNoLev (SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)))) (SNoLev z) /\ SNoEq_ (SNoLev (SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w)))) (SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w))) z).
Theorem Conj_real_complete1__27__11: ~ (forall z:set, z :e omega -> ap x z <= SNoCut (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ w < ap x u)) (Sep (SNoS_ omega) (fun w:set => exists u:set, u :e omega /\ ap y u < w))).
Admitted.

End Conj_real_complete1__27__11.
(** Conj_real_complete1__31__1 TMbqvnFNHXeaZjHK6c7WjL8VdnvXcYkau4M bounty of about 25 bars **)
Section Conj_real_complete1__31__1.
Variable x:set.
Variable y:set.
Hypothesis H0: x :e setexp real omega.
Hypothesis H2: (forall z:set, z :e omega -> ap x z <= ap y z /\ ap x z <= ap x (ordsucc z) /\ ap y (ordsucc z) <= ap y z).
Hypothesis H3: ~ (exists z:set, z :e real /\ (forall w:set, w :e omega -> ap x w <= z /\ z <= ap y w)).
Hypothesis H4: (forall z:set, z :e omega -> SNo (ap x z)).
Hypothesis H5: (forall z:set, z :e omega -> SNo (ap y z)).
Hypothesis H6: (forall z:set, nat_p z -> (forall w:set, w :e z -> ap x w <= ap x z)).
Hypothesis H7: (forall z:set, nat_p z -> (forall w:set, w :e z -> ap y z <= ap y w)).
Theorem Conj_real_complete1__31__1: ~ (forall z:set, z :e omega -> (forall w:set, w :e omega -> ap x z <= ap y w)).
Admitted.

End Conj_real_complete1__31__1.
(** Conj_ctagged_notin_SNo__3__0 TMWyfVXUfbVzc7ZDWZFZYv2ibcna3c7cihA bounty of about 25 bars **)
Section Conj_ctagged_notin_SNo__3__0.
Variable x:set.
Variable y:set.
Hypothesis H1: ordinal (SNoLev x).
Hypothesis H2: Subq x (SNoElts_ (SNoLev x)).
Theorem Conj_ctagged_notin_SNo__3__0: ~ SetAdjoin y (Sing (ordsucc (ordsucc Empty))) :e binunion (SNoLev x) (Repl (SNoLev x) (fun z:set => SetAdjoin z (Sing (ordsucc Empty)))).
Admitted.

End Conj_ctagged_notin_SNo__3__0.
(** Conj_ctagged_eqE_Subq__1__1 TMTfP8MMHDXqkkgbohA8fMfmHKxpg55HEbL bounty of about 25 bars **)
Section Conj_ctagged_eqE_Subq__1__1.
Variable x:set.
Variable y:set.
Hypothesis H0: Sing (ordsucc (ordsucc Empty)) :e x.
Hypothesis H2: ordinal y.
Theorem Conj_ctagged_eqE_Subq__1__1: ~ Sing (ordsucc (ordsucc Empty)) :e SetAdjoin y (Sing (ordsucc Empty)).
Admitted.

End Conj_ctagged_eqE_Subq__1__1.
(** Conj_ctagged_eqE_Subq__2__3 TMHXXjw8cG92xF9SogmGhUZzP7F4VrnCjj9 bounty of about 25 bars **)
Section Conj_ctagged_eqE_Subq__2__3.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: Sing (ordsucc (ordsucc Empty)) :e y.
Hypothesis H1: ordinal (SNoLev x).
Hypothesis H2: z :e SNoLev x.
Theorem Conj_ctagged_eqE_Subq__2__3: ~ ordinal z.
Admitted.

End Conj_ctagged_eqE_Subq__2__3.
(** Conj_ctagged_eqE_Subq__5__2 TMPjtiRn3YTJppVfNqxCxUQRtvMHvSPjTuJ bounty of about 25 bars **)
Section Conj_ctagged_eqE_Subq__5__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: y :e x.
Hypothesis H3: z :e Sing (Sing (ordsucc (ordsucc Empty))).
Theorem Conj_ctagged_eqE_Subq__5__2: z <> Sing (ordsucc (ordsucc Empty)).
Admitted.

End Conj_ctagged_eqE_Subq__5__2.
(** Conj_SNo_pair_prop_1_Subq__1__0 TMFWVR9bMV7faSWpjCcRWUHVwFqA8xNAxvK bounty of about 25 bars **)
Section Conj_SNo_pair_prop_1_Subq__1__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H1: SNo_pair x y = SNo_pair z w.
Hypothesis H2: u :e x.
Theorem Conj_SNo_pair_prop_1_Subq__1__0: u :e SNo_pair z w -> u :e z.
Admitted.

End Conj_SNo_pair_prop_1_Subq__1__0.
(** Conj_add_CSNo_minus_CSNo_rinv__1__1 TMGvMPu6FNJFNzzxkUsrD8j7o5dvBWLqayu bounty of about 25 bars **)
Section Conj_add_CSNo_minus_CSNo_rinv__1__1.
Variable x:set.
Hypothesis H0: CSNo x.
Theorem Conj_add_CSNo_minus_CSNo_rinv__1__1: SNo (- (CSNo_Im x)) -> SNo_pair (CSNo_Re x + CSNo_Re (SNo_pair (- (CSNo_Re x)) (- (CSNo_Im x)))) (CSNo_Im x + CSNo_Im (SNo_pair (- (CSNo_Re x)) (- (CSNo_Im x)))) = Empty.
Admitted.

End Conj_add_CSNo_minus_CSNo_rinv__1__1.
(** Conj_add_CSNo_com__1__2 TMJR3mdFNNJgxoneGne75ELM1mva7cdPb4H bounty of about 25 bars **)
Section Conj_add_CSNo_com__1__2.
Variable x:set.
Variable y:set.
Hypothesis H0: CSNo x.
Hypothesis H1: CSNo y.
Theorem Conj_add_CSNo_com__1__2: CSNo (add_CSNo y x) -> add_CSNo x y = add_CSNo y x.
Admitted.

End Conj_add_CSNo_com__1__2.
(** Conj_add_CSNo_assoc__2__4 TMMeS8ujRWaUQhLZd9Z2BYTSkkL7jZnKZbt bounty of about 25 bars **)
Section Conj_add_CSNo_assoc__2__4.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: CSNo x.
Hypothesis H1: CSNo y.
Hypothesis H2: CSNo z.
Hypothesis H3: CSNo (add_CSNo y z).
Theorem Conj_add_CSNo_assoc__2__4: CSNo (add_CSNo x (add_CSNo y z)) -> add_CSNo x (add_CSNo y z) = add_CSNo (add_CSNo x y) z.
Admitted.

End Conj_add_CSNo_assoc__2__4.
(** Conj_mul_CSNo_assoc__2__8 TMKfXsHxyzeYigzgFi6jQKquTV161zM4ThW bounty of about 25 bars **)
Section Conj_mul_CSNo_assoc__2__8.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: CSNo x.
Hypothesis H1: CSNo y.
Hypothesis H2: CSNo z.
Hypothesis H3: CSNo (mul_CSNo y z).
Hypothesis H4: CSNo (mul_CSNo x y).
Hypothesis H5: CSNo (mul_CSNo x (mul_CSNo y z)).
Hypothesis H6: CSNo (mul_CSNo (mul_CSNo x y) z).
Hypothesis H7: SNo (CSNo_Re x).
Hypothesis H9: SNo (CSNo_Re z).
Hypothesis H10: SNo (CSNo_Im x).
Theorem Conj_mul_CSNo_assoc__2__8: SNo (CSNo_Im y) -> mul_CSNo x (mul_CSNo y z) = mul_CSNo (mul_CSNo x y) z.
Admitted.

End Conj_mul_CSNo_assoc__2__8.
(** Conj_mul_CSNo_assoc__3__1 TMXhHMj7FhJXndiqL2TkBP8x79MN8HpkMwc bounty of about 25 bars **)
Section Conj_mul_CSNo_assoc__3__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: CSNo x.
Hypothesis H2: CSNo z.
Hypothesis H3: CSNo (mul_CSNo y z).
Hypothesis H4: CSNo (mul_CSNo x y).
Hypothesis H5: CSNo (mul_CSNo x (mul_CSNo y z)).
Hypothesis H6: CSNo (mul_CSNo (mul_CSNo x y) z).
Hypothesis H7: SNo (CSNo_Re x).
Hypothesis H8: SNo (CSNo_Re y).
Hypothesis H9: SNo (CSNo_Re z).
Theorem Conj_mul_CSNo_assoc__3__1: SNo (CSNo_Im x) -> mul_CSNo x (mul_CSNo y z) = mul_CSNo (mul_CSNo x y) z.
Admitted.

End Conj_mul_CSNo_assoc__3__1.
(** Conj_mul_CSNo_assoc__4__6 TMNpWNxQPQr62KPRcmVDoUdw8J8m8YjXpqh bounty of about 25 bars **)
Section Conj_mul_CSNo_assoc__4__6.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: CSNo x.
Hypothesis H1: CSNo y.
Hypothesis H2: CSNo z.
Hypothesis H3: CSNo (mul_CSNo y z).
Hypothesis H4: CSNo (mul_CSNo x y).
Hypothesis H5: CSNo (mul_CSNo x (mul_CSNo y z)).
Hypothesis H7: SNo (CSNo_Re x).
Hypothesis H8: SNo (CSNo_Re y).
Theorem Conj_mul_CSNo_assoc__4__6: SNo (CSNo_Re z) -> mul_CSNo x (mul_CSNo y z) = mul_CSNo (mul_CSNo x y) z.
Admitted.

End Conj_mul_CSNo_assoc__4__6.
(** Conj_mul_CSNo_distrL__2__0 TMb4GJkZzkgg5ZLTZQf1qd98F95hEErVQvQ bounty of about 25 bars **)
Section Conj_mul_CSNo_distrL__2__0.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H1: CSNo y.
Hypothesis H2: CSNo z.
Hypothesis H3: CSNo (add_CSNo y z).
Hypothesis H4: CSNo (mul_CSNo x y).
Hypothesis H5: CSNo (mul_CSNo x z).
Hypothesis H6: CSNo (mul_CSNo x (add_CSNo y z)).
Hypothesis H7: CSNo (add_CSNo (mul_CSNo x y) (mul_CSNo x z)).
Hypothesis H8: SNo (CSNo_Re x).
Hypothesis H9: SNo (CSNo_Re y).
Hypothesis H10: SNo (CSNo_Re z).
Hypothesis H11: SNo (CSNo_Im x).
Theorem Conj_mul_CSNo_distrL__2__0: SNo (CSNo_Im y) -> mul_CSNo x (add_CSNo y z) = add_CSNo (mul_CSNo x y) (mul_CSNo x z).
Admitted.

End Conj_mul_CSNo_distrL__2__0.
(** Conj_CSNo_relative_recip__5__2 TMX8WVqJ1byoEumpMvwXnXEXSESYsRiwKad bounty of about 25 bars **)
Section Conj_CSNo_relative_recip__5__2.
Variable x:set.
Variable y:set.
Hypothesis H0: CSNo x.
Hypothesis H1: SNo y.
Hypothesis H3: SNo (CSNo_Re x).
Hypothesis H4: SNo (CSNo_Im x).
Hypothesis H5: SNo (y * CSNo_Re x).
Hypothesis H6: CSNo (y * CSNo_Re x).
Hypothesis H7: SNo (y * CSNo_Im x).
Hypothesis H8: CSNo (y * CSNo_Im x).
Theorem Conj_CSNo_relative_recip__5__2: CSNo (mul_CSNo Complex_i (y * CSNo_Im x)) -> mul_CSNo x (add_CSNo (y * CSNo_Re x) (minus_CSNo (mul_CSNo Complex_i (y * CSNo_Im x)))) = ordsucc Empty.
Admitted.

End Conj_CSNo_relative_recip__5__2.
(** Conj_nonzero_complex_recip_ex__2__4 TMHDEdxPXwPMBssSQ7ddwei6EedB6BucqEs bounty of about 25 bars **)
Section Conj_nonzero_complex_recip_ex__2__4.
Variable x:set.
Hypothesis H0: x :e complex.
Hypothesis H1: x <> Empty.
Hypothesis H2: CSNo_Re x :e real.
Hypothesis H3: CSNo_Im x :e real.
Hypothesis H5: SNo (CSNo_Im x * CSNo_Im x).
Hypothesis H6: CSNo_Re x * CSNo_Re x + CSNo_Im x * CSNo_Im x :e real.
Theorem Conj_nonzero_complex_recip_ex__2__4: SNo (CSNo_Re x * CSNo_Re x + CSNo_Im x * CSNo_Im x) -> (exists y:set, y :e complex /\ mul_CSNo x y = ordsucc Empty).
Admitted.

End Conj_nonzero_complex_recip_ex__2__4.
