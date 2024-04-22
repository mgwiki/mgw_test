(** $I sig/Nov2021ConjPreamble.mgs **)

(** Conj_mul_SNo_assoc_lem1__26__21 TMXrPhiBRCMz9pTqLHTdFycxb5uuBkvWMqy bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__26__21.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g x y + g u x2).
Theorem Conj_mul_SNo_assoc_lem1__26__21: SNo (g (g x y + g u x2) y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__26__21.
(** Conj_mul_SNo_assoc_lem1__27__27 TMFNE4P28v5aLvucyhNssEyDR7eCevs2fbv bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__27__27.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Hypothesis H30: SNo (g x y + g u x2).
Theorem Conj_mul_SNo_assoc_lem1__27__27: SNo (g (g u y + g x x2) y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__27__27.
(** Conj_mul_SNo_assoc_lem1__27__30 TMc2qDZ6zjzAU41rNAxu6v3fWbTz5vShdYw bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__27__30.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Theorem Conj_mul_SNo_assoc_lem1__27__30: SNo (g (g u y + g x x2) y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__27__30.
(** Conj_mul_SNo_assoc_lem1__28__4 TMMd41ujZEZfsW5b4MA3xE9JD6akW8DZWAb bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__28__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Hypothesis H30: SNo (g x y + g u x2).
Theorem Conj_mul_SNo_assoc_lem1__28__4: SNo (g (g x y + g u x2) z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__28__4.
(** Conj_mul_SNo_assoc_lem1__28__7 TMN5iEjnyUjoaC7uGHCujZGWddhzeiEw83b bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__28__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Hypothesis H30: SNo (g x y + g u x2).
Theorem Conj_mul_SNo_assoc_lem1__28__7: SNo (g (g x y + g u x2) z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__28__7.
(** Conj_mul_SNo_assoc_lem1__28__8 TMYvEA2jPfddvxXzaWsFTu95aLfxfu9HWBP bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__28__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Hypothesis H30: SNo (g x y + g u x2).
Theorem Conj_mul_SNo_assoc_lem1__28__8: SNo (g (g x y + g u x2) z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__28__8.
(** Conj_mul_SNo_assoc_lem1__28__22 TMJLzJr7G23kN3w4TvLnjHtRYYWvaoic7rM bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__28__22.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Hypothesis H30: SNo (g x y + g u x2).
Theorem Conj_mul_SNo_assoc_lem1__28__22: SNo (g (g x y + g u x2) z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__28__22.
(** Conj_mul_SNo_assoc_lem1__28__27 TMVAsQkVN74SrKoSGEubBkY4jhhnAQvay1G bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__28__27.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Hypothesis H30: SNo (g x y + g u x2).
Theorem Conj_mul_SNo_assoc_lem1__28__27: SNo (g (g x y + g u x2) z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__28__27.
(** Conj_mul_SNo_assoc_lem1__28__30 TMHqLodnGtn2oxrfGJWwZqPvnMeB6JQGN3C bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__28__30.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Theorem Conj_mul_SNo_assoc_lem1__28__30: SNo (g (g x y + g u x2) z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__28__30.
(** Conj_mul_SNo_assoc_lem1__29__14 TMcM49sfyRXJRnVHWkvE9fSGi7dEfsi1uVG bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__29__14.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Hypothesis H30: SNo (g x y + g u x2).
Theorem Conj_mul_SNo_assoc_lem1__29__14: SNo (g (g u y + g x x2) z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__29__14.
(** Conj_mul_SNo_assoc_lem1__30__0 TMNGrNGThR2sRz5fAYgLgERdrGtb8zHm3Xb bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__30__0.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Theorem Conj_mul_SNo_assoc_lem1__30__0: SNo (g x y + g u x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__30__0.
(** Conj_mul_SNo_assoc_lem1__30__4 TMUM1CXXxs8NNsypD9rA7cH7sSeXUtgLTqA bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__30__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Hypothesis H29: SNo (g u y + g x x2).
Theorem Conj_mul_SNo_assoc_lem1__30__4: SNo (g x y + g u x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__30__4.
(** Conj_mul_SNo_assoc_lem1__31__23 TMbXkZ56N1Wt4Li9th5L6HA7L52eCaYi12o bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__31__23.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__31__23: SNo (g u y + g x x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__31__23.
(** Conj_mul_SNo_assoc_lem1__31__27 TMHv5eedM5n1yicCqCV1zWEMX5woZ2TwW3i bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__31__27.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g x (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__31__27: SNo (g u y + g x x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__31__27.
(** Conj_mul_SNo_assoc_lem1__33__4 TMRofdExL1eRr8aSTg75nkNZbTjBQKyAq9t bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__33__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g x (v + g x2 y2)).
Hypothesis H27: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g u (g x2 y2)).
Hypothesis H29: SNo (g u (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__33__4: SNo (g u v + g u (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__33__4.
(** Conj_mul_SNo_assoc_lem1__33__24 TMUEt815xSG2ZBSPJRPj4WijAreRFYxtxSd bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__33__24.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g x (v + g x2 y2)).
Hypothesis H27: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g u (g x2 y2)).
Hypothesis H29: SNo (g u (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__33__24: SNo (g u v + g u (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__33__24.
(** Conj_mul_SNo_assoc_lem1__34__8 TMFVSBaPwqEiT2qMf9A4kHkr95DvR5nnR6p bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__34__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g x (v + g x2 y2)).
Hypothesis H27: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__34__8: SNo (g u (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__34__8.
(** Conj_mul_SNo_assoc_lem1__34__9 TMdg9DgeQbMXuEuKEArSbktjRv4vX5u9LSF bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__34__9.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g x (v + g x2 y2)).
Hypothesis H27: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__34__9: SNo (g u (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__34__9.
(** Conj_mul_SNo_assoc_lem1__35__4 TMR3PewmRSCvFUF6dNJjVVpKMVgmGgUCjTv bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__35__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Hypothesis H27: SNo (g x (v + g x2 y2)).
Hypothesis H28: SNo (g u (v + g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__35__4: SNo (g u (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__35__4.
(** Conj_mul_SNo_assoc_lem1__36__3 TMVHi8WazMbsjErVzhwp8Y9Vy3Wnxor3hqV bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__36__3.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Hypothesis H27: SNo (g x (v + g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__36__3: SNo (g u (v + g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__36__3.
(** Conj_mul_SNo_assoc_lem1__36__11 TMFQaYLFPCE2DXPVx5wXCnQDLNuzjoLzvre bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__36__11.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Hypothesis H27: SNo (g x (v + g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__36__11: SNo (g u (v + g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__36__11.
(** Conj_mul_SNo_assoc_lem1__36__23 TMa9TLnUkpUaf3g9PCKPFgteDzSKJcJQJdb bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__36__23.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Hypothesis H27: SNo (g x (v + g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__36__23: SNo (g u (v + g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__36__23.
(** Conj_mul_SNo_assoc_lem1__36__27 TMXm3oEE8WuitCqXwMMsoJar9mKvcg7PUGg bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__36__27.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem1__36__27: SNo (g u (v + g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__36__27.
(** Conj_mul_SNo_assoc_lem1__37__11 TMWAK1YiutPPtwaEHc8jUqMBob1RHvnvANu bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__37__11.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem1__37__11: SNo (g x (v + g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__37__11.
(** Conj_mul_SNo_assoc_lem1__38__11 TMQa9c82UPAFid5doSiewo6VTcXqJHGLjvp bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__38__11.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem1__38__11: SNo (v + g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__38__11.
(** Conj_mul_SNo_assoc_lem1__38__13 TMPKkBV5dLPNpNPmUwuMny9sgzLU2bev2VN bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__38__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem1__38__13: SNo (v + g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__38__13.
(** Conj_mul_SNo_assoc_lem1__40__19 TMQURrqTZ6oakmdwtmTDeD8zanuR2fgTYzK bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__40__19.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z).
Hypothesis H25: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem1__40__19: SNo (g x2 z + g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__40__19.
(** Conj_mul_SNo_assoc_lem1__40__25 TMTJjwjowoSyPq2g11anjQqxBe9UKx44qKh bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__40__25.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem1__40__25: SNo (g x2 z + g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__40__25.
(** Conj_mul_SNo_assoc_lem1__41__17 TMd9LpRX8gAnDacQVm9cH4mazv6L8ZYgPWd bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__41__17.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem1__41__17: SNo (g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__41__17.
(** Conj_mul_SNo_assoc_lem1__43__3 TMLuxqALyfEYoy11UpMfpZKejHLCds3ZHzB bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__43__3.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem1__43__3: SNo (g x x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__43__3.
(** Conj_mul_SNo_assoc_lem1__43__6 TMK913J4oFuZMfBVFUpEnsC3idSWGxyauUx bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__43__6.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem1__43__6: SNo (g x x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__43__6.
(** Conj_mul_SNo_assoc_lem1__43__19 TMR12FQzUEso6WDMABMSebV8XBA2NUA7ubd bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__43__19.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem1__43__19: SNo (g x x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__43__19.
(** Conj_mul_SNo_assoc_lem1__46__0 TMLrdp434475c5f4HSZnrVnbVMuop74Hemb bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__46__0.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H7: u :e SNoR x.
Hypothesis H8: w = g u (g y z) + g x v + - (g u v).
Hypothesis H9: SNo u.
Hypothesis H10: x < u.
Hypothesis H11: SNo v.
Hypothesis H12: x2 :e SNoL y.
Hypothesis H13: y2 :e SNoR z.
Hypothesis H14: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H15: SNo x2.
Hypothesis H16: x2 < y.
Hypothesis H17: SNo y2.
Hypothesis H18: z < y2.
Hypothesis H19: SNo (g x2 z + g y y2).
Hypothesis H20: SNo (v + g x2 y2).
Hypothesis H21: SNo (g x (v + g x2 y2)).
Hypothesis H22: SNo (g u (v + g x2 y2)).
Hypothesis H23: SNo (g u (g x2 z + g y y2)).
Hypothesis H24: SNo (g x (g x2 z + g y y2)).
Hypothesis H25: SNo (g u y + g x x2).
Hypothesis H26: SNo (g x y + g u x2).
Hypothesis H27: SNo (g (g u y + g x x2) z).
Hypothesis H28: SNo (g (g x y + g u x2) z).
Hypothesis H29: SNo (g (g u y + g x x2) y2).
Theorem Conj_mul_SNo_assoc_lem1__46__0: SNo (g (g x y + g u x2) y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__46__0.
(** Conj_mul_SNo_assoc_lem1__47__5 TMaXoKJCyF4UPnYAAPK5CKv71aAvjxMQjE9 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__47__5.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H7: u :e SNoR x.
Hypothesis H8: w = g u (g y z) + g x v + - (g u v).
Hypothesis H9: SNo u.
Hypothesis H10: x < u.
Hypothesis H11: SNo v.
Hypothesis H12: x2 :e SNoL y.
Hypothesis H13: y2 :e SNoR z.
Hypothesis H14: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H15: SNo x2.
Hypothesis H16: x2 < y.
Hypothesis H17: SNo y2.
Hypothesis H18: z < y2.
Hypothesis H19: SNo (g x2 z + g y y2).
Hypothesis H20: SNo (v + g x2 y2).
Hypothesis H21: SNo (g x (v + g x2 y2)).
Hypothesis H22: SNo (g u (v + g x2 y2)).
Hypothesis H23: SNo (g u (g x2 z + g y y2)).
Hypothesis H24: SNo (g x (g x2 z + g y y2)).
Hypothesis H25: SNo (g u y + g x x2).
Hypothesis H26: SNo (g x y + g u x2).
Hypothesis H27: SNo (g (g u y + g x x2) z).
Hypothesis H28: SNo (g (g x y + g u x2) z).
Theorem Conj_mul_SNo_assoc_lem1__47__5: SNo (g (g u y + g x x2) y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__47__5.
(** Conj_mul_SNo_assoc_lem1__48__1 TMFV4jNtq97tZkzqQ6wSz3TMyjiRKSv6u4G bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__48__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H7: u :e SNoR x.
Hypothesis H8: w = g u (g y z) + g x v + - (g u v).
Hypothesis H9: SNo u.
Hypothesis H10: x < u.
Hypothesis H11: SNo v.
Hypothesis H12: x2 :e SNoL y.
Hypothesis H13: y2 :e SNoR z.
Hypothesis H14: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H15: SNo x2.
Hypothesis H16: x2 < y.
Hypothesis H17: SNo y2.
Hypothesis H18: z < y2.
Hypothesis H19: SNo (g x2 z + g y y2).
Hypothesis H20: SNo (v + g x2 y2).
Hypothesis H21: SNo (g x (v + g x2 y2)).
Hypothesis H22: SNo (g u (v + g x2 y2)).
Hypothesis H23: SNo (g u (g x2 z + g y y2)).
Hypothesis H24: SNo (g x (g x2 z + g y y2)).
Hypothesis H25: SNo (g u y + g x x2).
Hypothesis H26: SNo (g x y + g u x2).
Hypothesis H27: SNo (g (g u y + g x x2) z).
Theorem Conj_mul_SNo_assoc_lem1__48__1: SNo (g (g x y + g u x2) z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__48__1.
(** Conj_mul_SNo_assoc_lem1__48__22 TMNSWLXRZ6wC9d5ogaSiuFsapX7M3qNDu5H bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__48__22.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H7: u :e SNoR x.
Hypothesis H8: w = g u (g y z) + g x v + - (g u v).
Hypothesis H9: SNo u.
Hypothesis H10: x < u.
Hypothesis H11: SNo v.
Hypothesis H12: x2 :e SNoL y.
Hypothesis H13: y2 :e SNoR z.
Hypothesis H14: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H15: SNo x2.
Hypothesis H16: x2 < y.
Hypothesis H17: SNo y2.
Hypothesis H18: z < y2.
Hypothesis H19: SNo (g x2 z + g y y2).
Hypothesis H20: SNo (v + g x2 y2).
Hypothesis H21: SNo (g x (v + g x2 y2)).
Hypothesis H23: SNo (g u (g x2 z + g y y2)).
Hypothesis H24: SNo (g x (g x2 z + g y y2)).
Hypothesis H25: SNo (g u y + g x x2).
Hypothesis H26: SNo (g x y + g u x2).
Hypothesis H27: SNo (g (g u y + g x x2) z).
Theorem Conj_mul_SNo_assoc_lem1__48__22: SNo (g (g x y + g u x2) z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__48__22.
(** Conj_mul_SNo_assoc_lem1__50__11 TMNNjV6TSwfi7Uhy2et3mbD98DHCiXvFUDc bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__50__11.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u x2).
Hypothesis H21: SNo (g x2 z + g y y2).
Hypothesis H22: SNo (v + g x2 y2).
Hypothesis H23: SNo (g x (v + g x2 y2)).
Hypothesis H24: SNo (g u (v + g x2 y2)).
Hypothesis H25: SNo (g u (g x2 z + g y y2)).
Hypothesis H26: SNo (g x (g x2 z + g y y2)).
Hypothesis H27: SNo (g u y + g x x2).
Theorem Conj_mul_SNo_assoc_lem1__50__11: SNo (g x y + g u x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__50__11.
(** Conj_mul_SNo_assoc_lem1__52__3 TMTSHJyN58HYTk3dU1hKDXB56j3A3r4u7ww bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__52__3.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__52__3: SNo (g x (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__52__3.
(** Conj_mul_SNo_assoc_lem1__52__10 TMUkHcaUW7PQRPSy1hihi9jYuSnBvSjBERq bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__52__10.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__52__10: SNo (g x (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__52__10.
(** Conj_mul_SNo_assoc_lem1__52__25 TMd11PPv8pwxY588eVpd2qqHhqbzkBQWpLP bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__52__25.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__52__25: SNo (g x (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__52__25.
(** Conj_mul_SNo_assoc_lem1__53__6 TMMCn2CEmYTwJMx2Jqx1QGJ2wMDm1fZpb9w bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__53__6.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g x (v + g x2 y2)).
Hypothesis H27: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g u (g x2 y2)).
Hypothesis H29: SNo (g u (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__53__6: SNo (g u v + g u (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__53__6.
(** Conj_mul_SNo_assoc_lem1__53__23 TMcf7WjNgDsKWb4xNurDQukYakpBiFNJZ4Q bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__53__23.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g x (v + g x2 y2)).
Hypothesis H27: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g u (g x2 y2)).
Hypothesis H29: SNo (g u (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__53__23: SNo (g u v + g u (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__53__23.
(** Conj_mul_SNo_assoc_lem1__54__13 TMNZsnirKwo5MDU3KNRDDdjWqNMB7ViT3UY bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__54__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g x (v + g x2 y2)).
Hypothesis H27: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__54__13: SNo (g u (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__54__13.
(** Conj_mul_SNo_assoc_lem1__54__20 TMFm628uzXFmwooviQJocSN9HbPcXXwTycV bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__54__20.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g x (v + g x2 y2)).
Hypothesis H27: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__54__20: SNo (g u (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__54__20.
(** Conj_mul_SNo_assoc_lem1__54__23 TMFAoeDS77TbJETtBx6uZnXYbtkG5AQq9co bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__54__23.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g x (v + g x2 y2)).
Hypothesis H27: SNo (g u (v + g x2 y2)).
Hypothesis H28: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__54__23: SNo (g u (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__54__23.
(** Conj_mul_SNo_assoc_lem1__55__8 TMY97FH4aEH3MJdcwKPCe3EUjRi6yWb3ARr bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__55__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Hypothesis H27: SNo (g x (v + g x2 y2)).
Hypothesis H28: SNo (g u (v + g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__55__8: SNo (g u (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__55__8.
(** Conj_mul_SNo_assoc_lem1__57__15 TMYooweT4sD7pdHQ9WknUBGhp2Hi7G7xCna bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__57__15.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem1__57__15: SNo (g x (v + g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__57__15.
(** Conj_mul_SNo_assoc_lem1__58__7 TMMs5P2LPAVPbzUJ5PM1QBLvb4rtViLVcqf bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__58__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem1__58__7: SNo (v + g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__58__7.
(** Conj_mul_SNo_assoc_lem1__58__9 TMQCreWjs9eNHcMUpDz1FMJTNoy46Uvh8pn bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__58__9.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem1__58__9: SNo (v + g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__58__9.
(** Conj_mul_SNo_assoc_lem1__59__2 TMdsZQFQYzyGLWi3q9pW6XxdjBwwyEXgK5H bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__59__2.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem1__59__2: SNo (g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__59__2.
(** Conj_mul_SNo_assoc_lem1__59__7 TMX4a9RBjchAk1uecsvqfCF8noiP8SLCQ47 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__59__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem1__59__7: SNo (g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__59__7.
(** Conj_mul_SNo_assoc_lem1__59__18 TMKQ72JH5rsStrBMabaJSTKUT9pnKX7kmGG bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__59__18.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem1__59__18: SNo (g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__59__18.
(** Conj_mul_SNo_assoc_lem1__60__6 TMJGoV9fwNVUkCJ6jWKk7y1ySe64VpFa5o1 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__60__6.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z).
Hypothesis H25: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem1__60__6: SNo (g x2 z + g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__60__6.
(** Conj_mul_SNo_assoc_lem1__61__1 TMYuMAGqyLDRQwD2RkYaXDx7YU1bV7oYLwS bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__61__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem1__61__1: SNo (g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__61__1.
(** Conj_mul_SNo_assoc_lem1__62__1 TMdbjiJWGBKVfrYRUnYogyWkoiGrEP2Wy3h bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__62__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Theorem Conj_mul_SNo_assoc_lem1__62__1: SNo (g x2 z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__62__1.
(** Conj_mul_SNo_assoc_lem1__64__15 TMU4qnYzNx3ctpsSEGQUfmNx8BjbpMgRMZw bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__64__15.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Theorem Conj_mul_SNo_assoc_lem1__64__15: SNo (g u x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__64__15.
(** Conj_mul_SNo_assoc_lem1__65__9 TMZmg43T6HkDTgV7q7c1ncG1BgtUzAJFKp4 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__65__9.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Theorem Conj_mul_SNo_assoc_lem1__65__9: SNo (g u y) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__65__9.
(** Conj_mul_SNo_assoc_lem1__67__4 TMd4NQmfKUVFBqSj4WV3Mbr7dhjNuT3GGwD bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__67__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> SNo (g x2 y2)).
Hypothesis H1: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> (forall z2:set, z2 :e SNoR (g x2 y2) -> (forall P:prop, (forall w2:set, w2 :e SNoL x2 -> (forall u2:set, u2 :e SNoR y2 -> (g w2 y2 + g x2 u2) <= z2 + g w2 u2 -> P)) -> (forall w2:set, w2 :e SNoR x2 -> (forall u2:set, u2 :e SNoL y2 -> (g w2 y2 + g x2 u2) <= z2 + g w2 u2 -> P)) -> P))).
Hypothesis H2: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 < x2 -> w2 < y2 -> (g z2 y2 + g x2 w2) < g x2 y2 + g z2 w2).
Hypothesis H3: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 <= x2 -> w2 <= y2 -> (g z2 y2 + g x2 w2) <= g x2 y2 + g z2 w2).
Hypothesis H5: SNo y.
Hypothesis H6: SNo z.
Hypothesis H7: SNo (g x y).
Hypothesis H8: SNo (g y z).
Hypothesis H9: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> w = g x2 (g y z) + g x y2 + - (g x2 y2) -> (g x2 (g z2 z + g y w2) + g x (y2 + g z2 w2)) <= g x (g z2 z + g y w2) + g x2 (y2 + g z2 w2) -> (g (g x2 y + g x z2) z + g (g x y + g x2 z2) w2) < g (g x y + g x2 z2) z + g (g x2 y + g x z2) w2 -> w < g (g x y) z)))).
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoR (g y z).
Hypothesis H12: w = g u (g y z) + g x v + - (g u v).
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Theorem Conj_mul_SNo_assoc_lem1__67__4: SNo v -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__67__4.
(** Conj_mul_SNo_assoc_lem1__70__6 TMF3YyEvqxapK1tnoU5jE6ShQBJE5gLGMs9 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__70__6.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> SNo (g x2 y2)).
Hypothesis H1: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 < x2 -> w2 < y2 -> (g z2 y2 + g x2 w2) < g x2 y2 + g z2 w2).
Hypothesis H2: SNo x.
Hypothesis H3: SNo y.
Hypothesis H4: SNo z.
Hypothesis H5: SNo (g x y).
Hypothesis H7: w < x.
Hypothesis H8: SNo u.
Hypothesis H9: y < u.
Hypothesis H10: SNo v.
Hypothesis H11: z < v.
Hypothesis H12: SNo (g w y).
Hypothesis H13: SNo (g w u).
Hypothesis H14: SNo (g x u).
Hypothesis H15: SNo (g w y + g x u).
Hypothesis H16: SNo (g x y + g w u).
Hypothesis H17: SNo (g (g w y + g x u) z).
Theorem Conj_mul_SNo_assoc_lem1__70__6: SNo (g (g x y + g w u) z) -> (g (g w y + g x u) z + g (g x y + g w u) v) < g (g x y + g w u) z + g (g w y + g x u) v.
Admitted.

End Conj_mul_SNo_assoc_lem1__70__6.
(** Conj_mul_SNo_assoc_lem1__72__7 TMVVbpN8Znfv5eVBZcx6X36kdbwHXQWXwSW bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__72__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> SNo (g x2 y2)).
Hypothesis H1: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 < x2 -> w2 < y2 -> (g z2 y2 + g x2 w2) < g x2 y2 + g z2 w2).
Hypothesis H2: SNo x.
Hypothesis H3: SNo y.
Hypothesis H4: SNo z.
Hypothesis H5: SNo (g x y).
Hypothesis H6: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: y < u.
Hypothesis H10: SNo v.
Hypothesis H11: z < v.
Hypothesis H12: SNo (g w y).
Hypothesis H13: SNo (g w u).
Hypothesis H14: SNo (g x u).
Hypothesis H15: SNo (g w y + g x u).
Theorem Conj_mul_SNo_assoc_lem1__72__7: SNo (g x y + g w u) -> (g (g w y + g x u) z + g (g x y + g w u) v) < g (g x y + g w u) z + g (g w y + g x u) v.
Admitted.

End Conj_mul_SNo_assoc_lem1__72__7.
(** Conj_mul_SNo_assoc_lem1__73__3 TMVctcy7QXVv7RjLNdSMNsBamUoWzgvxfnZ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__73__3.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> SNo (g x2 y2)).
Hypothesis H1: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 < x2 -> w2 < y2 -> (g z2 y2 + g x2 w2) < g x2 y2 + g z2 w2).
Hypothesis H2: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: SNo (g x y).
Hypothesis H6: SNo w.
Hypothesis H7: w < x.
Hypothesis H8: SNo u.
Hypothesis H9: y < u.
Hypothesis H10: SNo v.
Hypothesis H11: z < v.
Hypothesis H12: SNo (g w y).
Hypothesis H13: SNo (g w u).
Hypothesis H14: SNo (g x u).
Theorem Conj_mul_SNo_assoc_lem1__73__3: SNo (g w y + g x u) -> (g (g w y + g x u) z + g (g x y + g w u) v) < g (g x y + g w u) z + g (g w y + g x u) v.
Admitted.

End Conj_mul_SNo_assoc_lem1__73__3.
(** Conj_mul_SNo_assoc_lem1__74__8 TMWqB49vbQvsj2f7md8HYQMsNnbVKTm2mT7 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__74__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem1__74__8: SNo (v + g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__74__8.
(** Conj_mul_SNo_assoc_lem1__75__0 TMcYCj9DzpNQET3JEv8NqJ6eCebrA5Jxroo bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__75__0.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem1__75__0: SNo (g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__75__0.
(** Conj_mul_SNo_assoc_lem1__75__9 TMaKCqHAaxswiceUCBSMLmVCu4V9dTD5n8b bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__75__9.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem1__75__9: SNo (g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__75__9.
(** Conj_mul_SNo_assoc_lem1__76__10 TMcJ22hn8BFMdLtvmvJUJjh6tiv21P6hMu4 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__76__10.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z).
Hypothesis H24: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem1__76__10: SNo (g x2 z + g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__76__10.
(** Conj_mul_SNo_assoc_lem1__77__7 TMVH516dhQQD1Do5jcyRFkVPrUT9pj4qWoL bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__77__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem1__77__7: SNo (g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__77__7.
(** Conj_mul_SNo_assoc_lem1__77__13 TMHSB8oGCmkSCxSv7TEm2tmh9oDM82PRcAD bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__77__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem1__77__13: SNo (g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__77__13.
(** Conj_mul_SNo_assoc_lem1__77__19 TMUUyTNqprRnkiseku7ZpRcxgMbqB1VY2Jm bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__77__19.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem1__77__19: SNo (g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__77__19.
(** Conj_mul_SNo_assoc_lem1__79__14 TMKwh8VuBBQKsdxR4re3WCZgANyJeXaFEoT bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__79__14.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem1__79__14: SNo (g x x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__79__14.
(** Conj_mul_SNo_assoc_lem1__80__7 TMPF9zKzRmofAZYWAWTMTVb8wAio5BtHsrn bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__80__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Theorem Conj_mul_SNo_assoc_lem1__80__7: SNo (g u x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__80__7.
(** Conj_mul_SNo_assoc_lem1__81__0 TMFqFQLd6tEodASQJUpQ2DtkpzFXn63A9Jf bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__81__0.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Theorem Conj_mul_SNo_assoc_lem1__81__0: SNo (g u y) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__81__0.
(** Conj_mul_SNo_assoc_lem1__82__1 TMbY5TmQQ2mQK2Ew57sgVa7Ayfxqy1xhJn2 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__82__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g x2 z + g y y2).
Hypothesis H21: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem1__82__1: SNo (v + g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__82__1.
(** Conj_mul_SNo_assoc_lem1__82__14 TMMyipcVyjQYKpAW4AvtC1p5qLhemnfNxc8 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__82__14.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g x2 z + g y y2).
Hypothesis H21: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem1__82__14: SNo (v + g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__82__14.
(** Conj_mul_SNo_assoc_lem1__83__9 TMF9BEKoUTvRvTUhwS99wDwGnqjCzMYa9dS bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__83__9.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem1__83__9: SNo (g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__83__9.
(** Conj_mul_SNo_assoc_lem1__83__13 TMXvHNrm6F4MRxLAdhrrDLnWUVxKdch4csz bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__83__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem1__83__13: SNo (g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__83__13.
(** Conj_mul_SNo_assoc_lem1__84__13 TMX9UtZdV3QoGbnPiYnY3yEudYoyrwQoE7B bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__84__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g x2 z).
Hypothesis H21: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem1__84__13: SNo (g x2 z + g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__84__13.
(** Conj_mul_SNo_assoc_lem1__84__20 TMTyrKic9auo6BaW2S2irVcxxfCBngdwxQA bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__84__20.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H21: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem1__84__20: SNo (g x2 z + g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__84__20.
(** Conj_mul_SNo_assoc_lem1__85__0 TMcXh6VKA18L7nFmbZPEPVNSkVSmVoZ1pC6 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__85__0.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem1__85__0: SNo (g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__85__0.
(** Conj_mul_SNo_assoc_lem1__85__3 TMGfu3w7GguSuHAD8JKrBVt5bodpAqWCxh6 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__85__3.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2)) <= g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2) -> (g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2) < g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2 -> w < g (g x y) z)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem1__85__3: SNo (g y y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__85__3.
(** Conj_mul_SNo_assoc_lem1__87__3 TMQ4BtqbMNJVoC8EzDTMZY4r26U93EAgLkN bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__87__3.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> SNo (g x2 y2)).
Hypothesis H1: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> (forall z2:set, z2 :e SNoL (g x2 y2) -> (forall P:prop, (forall w2:set, w2 :e SNoL x2 -> (forall u2:set, u2 :e SNoL y2 -> (z2 + g w2 u2) <= g w2 y2 + g x2 u2 -> P)) -> (forall w2:set, w2 :e SNoR x2 -> (forall u2:set, u2 :e SNoR y2 -> (z2 + g w2 u2) <= g w2 y2 + g x2 u2 -> P)) -> P))).
Hypothesis H2: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 < x2 -> w2 < y2 -> (g z2 y2 + g x2 w2) < g x2 y2 + g z2 w2).
Hypothesis H4: SNo x.
Hypothesis H5: SNo y.
Hypothesis H6: SNo z.
Hypothesis H7: SNo (g x y).
Hypothesis H8: SNo (g y z).
Hypothesis H9: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> w = g x2 (g y z) + g x y2 + - (g x2 y2) -> (g x2 (g z2 z + g y w2) + g x (y2 + g z2 w2)) <= g x (g z2 z + g y w2) + g x2 (y2 + g z2 w2) -> (g (g x2 y + g x z2) z + g (g x y + g x2 z2) w2) < g (g x y + g x2 z2) z + g (g x2 y + g x z2) w2 -> w < g (g x y) z)))).
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL (g y z).
Hypothesis H12: w = g u (g y z) + g x v + - (g u v).
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Theorem Conj_mul_SNo_assoc_lem1__87__3: SNo v -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__87__3.
(** Conj_mul_SNo_assoc_lem1__87__9 TMTYCi7aJmAK4zSSDJy6BAhpHSQDM8ZLWKF bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__87__9.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> SNo (g x2 y2)).
Hypothesis H1: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> (forall z2:set, z2 :e SNoL (g x2 y2) -> (forall P:prop, (forall w2:set, w2 :e SNoL x2 -> (forall u2:set, u2 :e SNoL y2 -> (z2 + g w2 u2) <= g w2 y2 + g x2 u2 -> P)) -> (forall w2:set, w2 :e SNoR x2 -> (forall u2:set, u2 :e SNoR y2 -> (z2 + g w2 u2) <= g w2 y2 + g x2 u2 -> P)) -> P))).
Hypothesis H2: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 < x2 -> w2 < y2 -> (g z2 y2 + g x2 w2) < g x2 y2 + g z2 w2).
Hypothesis H3: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 <= x2 -> w2 <= y2 -> (g z2 y2 + g x2 w2) <= g x2 y2 + g z2 w2).
Hypothesis H4: SNo x.
Hypothesis H5: SNo y.
Hypothesis H6: SNo z.
Hypothesis H7: SNo (g x y).
Hypothesis H8: SNo (g y z).
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL (g y z).
Hypothesis H12: w = g u (g y z) + g x v + - (g u v).
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Theorem Conj_mul_SNo_assoc_lem1__87__9: SNo v -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__87__9.
(** Conj_mul_SNo_assoc_lem1__88__0 TMN81AjjFnmX7vQedvtvdPPrptR266tV4y9 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__88__0.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
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
Hypothesis H17: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> P)).
Hypothesis H18: u :e w.
Hypothesis H19: SNo (g x y).
Hypothesis H20: SNo (g y z).
Hypothesis H21: SNo (g (g x y) z).
Theorem Conj_mul_SNo_assoc_lem1__88__0: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, SNo x2 -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> u = g v (g y z) + g x x2 + - (g v x2) -> (g v (g y2 z + g y z2) + g x (x2 + g y2 z2)) <= g x (g y2 z + g y z2) + g v (x2 + g y2 z2) -> (g (g v y + g x y2) z + g (g x y + g v y2) z2) < g (g x y + g v y2) z + g (g v y + g x y2) z2 -> u < g (g x y) z)))) -> u < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__88__0.
(** Conj_mul_SNo_assoc_lem1__88__17 TMPdvfVshkMrPSnNUccB14SnAorP2zSHNof bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__88__17.
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
Hypothesis H18: u :e w.
Hypothesis H19: SNo (g x y).
Hypothesis H20: SNo (g y z).
Hypothesis H21: SNo (g (g x y) z).
Theorem Conj_mul_SNo_assoc_lem1__88__17: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, SNo x2 -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> (forall z2:set, z2 :e SNoS_ (SNoLev z) -> u = g v (g y z) + g x x2 + - (g v x2) -> (g v (g y2 z + g y z2) + g x (x2 + g y2 z2)) <= g x (g y2 z + g y z2) + g v (x2 + g y2 z2) -> (g (g v y + g x y2) z + g (g x y + g v y2) z2) < g (g x y + g v y2) z + g (g v y + g x y2) z2 -> u < g (g x y) z)))) -> u < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__88__17.
(** Conj_mul_SNo_assoc_lem1__89__7 TMLtSG3ZqsAVP6Fhe5qtQjVjmiiEYF64pmi bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__89__7.
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
Hypothesis H8: SNo y.
Hypothesis H9: SNo z.
Hypothesis H10: (forall v:set, v :e SNoS_ (SNoLev x) -> g v (g y z) = g (g v y) z).
Hypothesis H11: (forall v:set, v :e SNoS_ (SNoLev y) -> g x (g v z) = g (g x v) z).
Hypothesis H12: (forall v:set, v :e SNoS_ (SNoLev z) -> g x (g y v) = g (g x y) v).
Hypothesis H13: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> g v (g x2 z) = g (g v x2) z)).
Hypothesis H14: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g v (g y x2) = g (g v y) x2)).
Hypothesis H15: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> g x (g v x2) = g (g x v) x2)).
Hypothesis H16: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> g v (g x2 y2) = g (g v x2) y2))).
Hypothesis H17: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> P)).
Hypothesis H18: u :e w.
Hypothesis H19: SNo (g x y).
Hypothesis H20: SNo (g y z).
Theorem Conj_mul_SNo_assoc_lem1__89__7: SNo (g (g x y) z) -> u < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__89__7.
(** Conj_mul_SNo_assoc_lem1__91__1 TMaWzbxr85bGNhgcJWDLDDPPVoznmgT7iVV bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__91__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: (forall v:set, forall x2:set, SNo v -> SNo x2 -> SNo (g v x2)).
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
Hypothesis H17: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR (g y z) -> v = g x2 (g y z) + g x y2 + - (g x2 y2) -> P)) -> P)).
Hypothesis H18: u :e w.
Theorem Conj_mul_SNo_assoc_lem1__91__1: SNo (g x y) -> u < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__91__1.
(** Conj_mul_SNo_assoc_lem2__2__20 TMSwHCde2s2cGgmYiBwLN4PZgoewLCghYrW bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__2__20.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H2: SNo x.
Hypothesis H3: SNo z.
Hypothesis H4: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H11: SNo (g x y).
Hypothesis H12: SNo (g (g x y) z).
Hypothesis H13: u :e SNoS_ (SNoLev x).
Hypothesis H14: SNo v.
Hypothesis H15: x2 :e SNoS_ (SNoLev y).
Hypothesis H16: y2 :e SNoS_ (SNoLev z).
Hypothesis H17: w = g u (g y z) + g x v + - (g u v).
Hypothesis H18: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H19: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo y2.
Hypothesis H22: SNo (g u (g y z)).
Hypothesis H23: SNo (g x v).
Hypothesis H24: SNo (g x x2).
Hypothesis H25: SNo (g u v).
Hypothesis H26: SNo (g u x2).
Hypothesis H27: SNo (g u y).
Hypothesis H28: SNo (g x2 z).
Hypothesis H29: SNo (g y y2).
Hypothesis H30: SNo (g u (g x2 z)).
Hypothesis H31: SNo (g u (g y y2)).
Hypothesis H32: SNo (g x2 y2).
Hypothesis H33: SNo (g x (g x2 y2)).
Hypothesis H34: SNo (g x (g x2 z)).
Hypothesis H35: SNo (g x (g y y2)).
Hypothesis H36: SNo (g u (g y z) + g x v).
Hypothesis H37: SNo (g (g x y) z + g u v).
Hypothesis H38: SNo (g u (g x2 y2)).
Hypothesis H39: SNo (g u (v + g x2 y2)).
Hypothesis H40: SNo (g u (g x2 z + g y y2)).
Hypothesis H41: SNo (g u v + g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__2__20: SNo (g u (g y z) + g x (g x2 z) + g x (g y y2) + g u v + g u (g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__2__20.
(** Conj_mul_SNo_assoc_lem2__2__23 TMG1J753bNykGjs7ZzPeyqmASGa5XSnvmk7 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__2__23.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H2: SNo x.
Hypothesis H3: SNo z.
Hypothesis H4: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H11: SNo (g x y).
Hypothesis H12: SNo (g (g x y) z).
Hypothesis H13: u :e SNoS_ (SNoLev x).
Hypothesis H14: SNo v.
Hypothesis H15: x2 :e SNoS_ (SNoLev y).
Hypothesis H16: y2 :e SNoS_ (SNoLev z).
Hypothesis H17: w = g u (g y z) + g x v + - (g u v).
Hypothesis H18: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H19: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H20: SNo u.
Hypothesis H21: SNo y2.
Hypothesis H22: SNo (g u (g y z)).
Hypothesis H24: SNo (g x x2).
Hypothesis H25: SNo (g u v).
Hypothesis H26: SNo (g u x2).
Hypothesis H27: SNo (g u y).
Hypothesis H28: SNo (g x2 z).
Hypothesis H29: SNo (g y y2).
Hypothesis H30: SNo (g u (g x2 z)).
Hypothesis H31: SNo (g u (g y y2)).
Hypothesis H32: SNo (g x2 y2).
Hypothesis H33: SNo (g x (g x2 y2)).
Hypothesis H34: SNo (g x (g x2 z)).
Hypothesis H35: SNo (g x (g y y2)).
Hypothesis H36: SNo (g u (g y z) + g x v).
Hypothesis H37: SNo (g (g x y) z + g u v).
Hypothesis H38: SNo (g u (g x2 y2)).
Hypothesis H39: SNo (g u (v + g x2 y2)).
Hypothesis H40: SNo (g u (g x2 z + g y y2)).
Hypothesis H41: SNo (g u v + g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__2__23: SNo (g u (g y z) + g x (g x2 z) + g x (g y y2) + g u v + g u (g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__2__23.
(** Conj_mul_SNo_assoc_lem2__3__25 TMP3m1PPxL5FFxzi7p6ZzzGvPiQ93TbKtwk bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__3__25.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H2: SNo x.
Hypothesis H3: SNo z.
Hypothesis H4: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H11: SNo (g x y).
Hypothesis H12: SNo (g (g x y) z).
Hypothesis H13: u :e SNoS_ (SNoLev x).
Hypothesis H14: SNo v.
Hypothesis H15: x2 :e SNoS_ (SNoLev y).
Hypothesis H16: y2 :e SNoS_ (SNoLev z).
Hypothesis H17: w = g u (g y z) + g x v + - (g u v).
Hypothesis H18: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H19: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H20: SNo u.
Hypothesis H21: SNo y2.
Hypothesis H22: SNo (g u (g y z)).
Hypothesis H23: SNo (g x v).
Hypothesis H24: SNo (g x x2).
Hypothesis H26: SNo (g u x2).
Hypothesis H27: SNo (g u y).
Hypothesis H28: SNo (g x2 z).
Hypothesis H29: SNo (g y y2).
Hypothesis H30: SNo (g u (g x2 z)).
Hypothesis H31: SNo (g u (g y y2)).
Hypothesis H32: SNo (g x2 y2).
Hypothesis H33: SNo (g x (g x2 y2)).
Hypothesis H34: SNo (g x (g x2 z)).
Hypothesis H35: SNo (g x (g y y2)).
Hypothesis H36: SNo (g u (g y z) + g x v).
Hypothesis H37: SNo (g (g x y) z + g u v).
Hypothesis H38: SNo (g u (g x2 y2)).
Hypothesis H39: SNo (g u (v + g x2 y2)).
Hypothesis H40: SNo (g u (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem2__3__25: SNo (g u v + g u (g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__3__25.
(** Conj_mul_SNo_assoc_lem2__4__11 TMdgd4Dg6cWbJKBEaS3RDUih6WQjnddSEDL bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__4__11.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Hypothesis H40: SNo (g u (v + g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__4__11: SNo (g u (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__4__11.
(** Conj_mul_SNo_assoc_lem2__4__14 TMWDgPg88ywaHDLkv8Ws3GZ2xzGg3ro6oZ9 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__4__14.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Hypothesis H40: SNo (g u (v + g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__4__14: SNo (g u (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__4__14.
(** Conj_mul_SNo_assoc_lem2__5__6 TMNJvMdMhPm2esaH1eMT4ywWKugZw7LZz1V bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__5__6.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Hypothesis H40: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__5__6: SNo (g u (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__5__6.
(** Conj_mul_SNo_assoc_lem2__5__26 TMRHyve96Qn8z611tU37yLXB7v32eGdLgeh bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__5__26.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Hypothesis H40: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__5__26: SNo (g u (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__5__26.
(** Conj_mul_SNo_assoc_lem2__6__10 TMPsBVfeCa5SCbL24iYLBgwxxq4ZKWnGW99 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__6__10.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__6__10: SNo (v + g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__6__10.
(** Conj_mul_SNo_assoc_lem2__6__13 TMbd3bvgQ5FEve2rcGjxc7aSBpU89432Naj bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__6__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__6__13: SNo (v + g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__6__13.
(** Conj_mul_SNo_assoc_lem2__6__14 TMSQasZkSP4JYBpdLYG2EYmtu6sr4CscZ5S bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__6__14.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__6__14: SNo (v + g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__6__14.
(** Conj_mul_SNo_assoc_lem2__6__15 TMXbWqshkjogDbpga18Dc3oECUhNCLTwkFr bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__6__15.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__6__15: SNo (v + g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__6__15.
(** Conj_mul_SNo_assoc_lem2__6__29 TMTehYaDEgN7LhqeV8mwysLmgBRBtMugkRq bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__6__29.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__6__29: SNo (v + g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__6__29.
(** Conj_mul_SNo_assoc_lem2__6__30 TMVEzVkwtfqJBG3RDSw4769wqboegLah2b7 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__6__30.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__6__30: SNo (v + g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__6__30.
(** Conj_mul_SNo_assoc_lem2__7__13 TMLqkAa6cjByos2FXsvZTDVTpx7egYirX5y bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__7__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Theorem Conj_mul_SNo_assoc_lem2__7__13: SNo (g u (g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__7__13.
(** Conj_mul_SNo_assoc_lem2__7__16 TMKuedjg9Q81PeJnogSNmjtaPvGjX4P2AN3 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__7__16.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Theorem Conj_mul_SNo_assoc_lem2__7__16: SNo (g u (g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__7__16.
(** Conj_mul_SNo_assoc_lem2__8__2 TMav2ZHtL5RVmHpP7g2smWHsXiqdvQn4W3J bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__8__2.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Theorem Conj_mul_SNo_assoc_lem2__8__2: SNo (g (g x y) z + g u v) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__8__2.
(** Conj_mul_SNo_assoc_lem2__8__6 TMJSUSkeGyWWnMyy3FybfAzpUU6BhwGn3Zb bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__8__6.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Theorem Conj_mul_SNo_assoc_lem2__8__6: SNo (g (g x y) z + g u v) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__8__6.
(** Conj_mul_SNo_assoc_lem2__9__6 TMaV2waWALe6Zytp4XSayWHxSDNLe8z7xme bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__9__6.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Theorem Conj_mul_SNo_assoc_lem2__9__6: SNo (g u (g y z) + g x v) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__9__6.
(** Conj_mul_SNo_assoc_lem2__9__21 TMT4SdZqdAMZx6BKPuLhvToyKHvhu1eJsDD bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__9__21.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Theorem Conj_mul_SNo_assoc_lem2__9__21: SNo (g u (g y z) + g x v) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__9__21.
(** Conj_mul_SNo_assoc_lem2__10__9 TMGsi1FDPE6fZuLDFSKAeURsuvUrm7ndu25 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__10__9.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Theorem Conj_mul_SNo_assoc_lem2__10__9: SNo (g x (g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__10__9.
(** Conj_mul_SNo_assoc_lem2__11__1 TMTveihSiFsnGtaqFJJmw6SZ8gQRMUU3PeZ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__11__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__11__1: SNo (g x (g x2 z)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__11__1.
(** Conj_mul_SNo_assoc_lem2__11__19 TMTSX1tmosHsmCsQ4v9PawTTjvH9ogiEzR2 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__11__19.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H31: SNo (g u (g x2 z)).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Hypothesis H34: SNo (g x (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__11__19: SNo (g x (g x2 z)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__11__19.
(** Conj_mul_SNo_assoc_lem2__12__31 TMRKA8Gfj8o5Lh9jbByM4iTetvYEcWJ3NFG bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__12__31.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
Hypothesis H27: SNo (g u x2).
Hypothesis H28: SNo (g u y).
Hypothesis H29: SNo (g x2 z).
Hypothesis H30: SNo (g y y2).
Hypothesis H32: SNo (g u (g y y2)).
Hypothesis H33: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__12__31: SNo (g x (g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__12__31.
(** Conj_mul_SNo_assoc_lem2__13__8 TMWkPGkTiPDRxDJUSiLm1ZX5LYbZhKtDSLw bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__13__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNo y2.
Hypothesis H24: SNo (g u (g y z)).
Hypothesis H25: SNo (g x v).
Hypothesis H26: SNo (g x x2).
Hypothesis H27: SNo (g u v).
Hypothesis H28: SNo (g u x2).
Hypothesis H29: SNo (g u y).
Hypothesis H30: SNo (g x2 z).
Hypothesis H31: SNo (g y y2).
Hypothesis H32: SNo (g u (g x2 z)).
Hypothesis H33: SNo (g u (g y y2)).
Theorem Conj_mul_SNo_assoc_lem2__13__8: SNo (g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__13__8.
(** Conj_mul_SNo_assoc_lem2__14__5 TMFDfGZNgvY7GVmvqc1Zyn2QVqfjMUAdr6W bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__14__5.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNo y2.
Hypothesis H24: SNo (g u (g y z)).
Hypothesis H25: SNo (g x v).
Hypothesis H26: SNo (g x x2).
Hypothesis H27: SNo (g u v).
Hypothesis H28: SNo (g u x2).
Hypothesis H29: SNo (g u y).
Hypothesis H30: SNo (g x2 z).
Hypothesis H31: SNo (g y y2).
Hypothesis H32: SNo (g u (g x2 z)).
Theorem Conj_mul_SNo_assoc_lem2__14__5: SNo (g u (g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__14__5.
(** Conj_mul_SNo_assoc_lem2__14__29 TMcaPoRJV7xALRquuc4fvzKSPFk6Taqkwm5 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__14__29.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNo y2.
Hypothesis H24: SNo (g u (g y z)).
Hypothesis H25: SNo (g x v).
Hypothesis H26: SNo (g x x2).
Hypothesis H27: SNo (g u v).
Hypothesis H28: SNo (g u x2).
Hypothesis H30: SNo (g x2 z).
Hypothesis H31: SNo (g y y2).
Hypothesis H32: SNo (g u (g x2 z)).
Theorem Conj_mul_SNo_assoc_lem2__14__29: SNo (g u (g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__14__29.
(** Conj_mul_SNo_assoc_lem2__15__1 TMEnubJbuBU5CAKZN7nK1VDXT4xzTWdoWpm bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__15__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNo y2.
Hypothesis H24: SNo (g u (g y z)).
Hypothesis H25: SNo (g x v).
Hypothesis H26: SNo (g x x2).
Hypothesis H27: SNo (g u v).
Hypothesis H28: SNo (g u x2).
Hypothesis H29: SNo (g u y).
Hypothesis H30: SNo (g x2 z).
Hypothesis H31: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem2__15__1: SNo (g u (g x2 z)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__15__1.
(** Conj_mul_SNo_assoc_lem2__15__27 TMRjvQf8C9ihFkoM9LQY2abJ51zKaggcRJV bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__15__27.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNo y2.
Hypothesis H24: SNo (g u (g y z)).
Hypothesis H25: SNo (g x v).
Hypothesis H26: SNo (g x x2).
Hypothesis H28: SNo (g u x2).
Hypothesis H29: SNo (g u y).
Hypothesis H30: SNo (g x2 z).
Hypothesis H31: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem2__15__27: SNo (g u (g x2 z)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__15__27.
(** Conj_mul_SNo_assoc_lem2__15__29 TMTB4dxGBwZyxW5iqnwtzL6MhKPx3NmtZPJ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__15__29.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo z.
Hypothesis H5: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H12: SNo (g x y).
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H20: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNo y2.
Hypothesis H24: SNo (g u (g y z)).
Hypothesis H25: SNo (g x v).
Hypothesis H26: SNo (g x x2).
Hypothesis H27: SNo (g u v).
Hypothesis H28: SNo (g u x2).
Hypothesis H30: SNo (g x2 z).
Hypothesis H31: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem2__15__29: SNo (g u (g x2 z)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__15__29.
(** Conj_mul_SNo_assoc_lem2__18__13 TMSbJEdibeqbZk8B7cPRrvMibL5A1in8nnp bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__18__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H12: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H14: SNo (g (g x y) z).
Hypothesis H15: u :e SNoS_ (SNoLev x).
Hypothesis H16: SNo v.
Hypothesis H17: x2 :e SNoS_ (SNoLev y).
Hypothesis H18: y2 :e SNoS_ (SNoLev z).
Hypothesis H19: w = g u (g y z) + g x v + - (g u v).
Hypothesis H20: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H21: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Hypothesis H28: SNo (g u v).
Hypothesis H29: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem2__18__13: SNo (g u y) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__18__13.
(** Conj_mul_SNo_assoc_lem2__18__18 TMRhSfNXEsoJZUM4C3Z73uop8S9LmHBqBim bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__18__18.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H12: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H13: SNo (g x y).
Hypothesis H14: SNo (g (g x y) z).
Hypothesis H15: u :e SNoS_ (SNoLev x).
Hypothesis H16: SNo v.
Hypothesis H17: x2 :e SNoS_ (SNoLev y).
Hypothesis H19: w = g u (g y z) + g x v + - (g u v).
Hypothesis H20: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H21: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Hypothesis H28: SNo (g u v).
Hypothesis H29: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem2__18__18: SNo (g u y) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__18__18.
(** Conj_mul_SNo_assoc_lem2__19__8 TMPAiERC5n5Hf5zKrUYxbkJYCEKRk9qzXcG bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__19__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H12: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H13: SNo (g x y).
Hypothesis H14: SNo (g (g x y) z).
Hypothesis H15: u :e SNoS_ (SNoLev x).
Hypothesis H16: SNo v.
Hypothesis H17: x2 :e SNoS_ (SNoLev y).
Hypothesis H18: y2 :e SNoS_ (SNoLev z).
Hypothesis H19: w = g u (g y z) + g x v + - (g u v).
Hypothesis H20: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H21: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Hypothesis H28: SNo (g u v).
Theorem Conj_mul_SNo_assoc_lem2__19__8: SNo (g u x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__19__8.
(** Conj_mul_SNo_assoc_lem2__19__11 TMdPtmSG5J2dYTm8Dc17zeXGj9vMgRUDCpY bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__19__11.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H12: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H13: SNo (g x y).
Hypothesis H14: SNo (g (g x y) z).
Hypothesis H15: u :e SNoS_ (SNoLev x).
Hypothesis H16: SNo v.
Hypothesis H17: x2 :e SNoS_ (SNoLev y).
Hypothesis H18: y2 :e SNoS_ (SNoLev z).
Hypothesis H19: w = g u (g y z) + g x v + - (g u v).
Hypothesis H20: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H21: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Hypothesis H28: SNo (g u v).
Theorem Conj_mul_SNo_assoc_lem2__19__11: SNo (g u x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__19__11.
(** Conj_mul_SNo_assoc_lem2__21__8 TMSdGUZPXx5KF7bD7satVPWQhyKc7gxQFNq bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__21__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H12: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H13: SNo (g x y).
Hypothesis H14: SNo (g (g x y) z).
Hypothesis H15: u :e SNoS_ (SNoLev x).
Hypothesis H16: SNo v.
Hypothesis H17: x2 :e SNoS_ (SNoLev y).
Hypothesis H18: y2 :e SNoS_ (SNoLev z).
Hypothesis H19: w = g u (g y z) + g x v + - (g u v).
Hypothesis H20: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H21: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Theorem Conj_mul_SNo_assoc_lem2__21__8: SNo (g x x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__21__8.
(** Conj_mul_SNo_assoc_lem2__22__22 TMPLALSpJNjQHmDL4NFiTP7R21jpZzEMRX1 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__22__22.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H12: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H13: SNo (g x y).
Hypothesis H14: SNo (g (g x y) z).
Hypothesis H15: u :e SNoS_ (SNoLev x).
Hypothesis H16: SNo v.
Hypothesis H17: x2 :e SNoS_ (SNoLev y).
Hypothesis H18: y2 :e SNoS_ (SNoLev z).
Hypothesis H19: w = g u (g y z) + g x v + - (g u v).
Hypothesis H20: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H21: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Theorem Conj_mul_SNo_assoc_lem2__22__22: SNo (g x v) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__22__22.
(** Conj_mul_SNo_assoc_lem2__23__13 TMGzC8yB5kEaE8wYXh2nFEKULRt6zJmER5i bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__23__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H12: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H14: SNo (g y z).
Hypothesis H15: SNo (g (g x y) z).
Hypothesis H16: u :e SNoS_ (SNoLev x).
Hypothesis H17: SNo v.
Hypothesis H18: x2 :e SNoS_ (SNoLev y).
Hypothesis H19: y2 :e SNoS_ (SNoLev z).
Hypothesis H20: w = g u (g y z) + g x v + - (g u v).
Hypothesis H21: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H22: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H23: SNo u.
Hypothesis H24: SNo x2.
Hypothesis H25: SNo y2.
Theorem Conj_mul_SNo_assoc_lem2__23__13: SNo (g u (g y z)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__23__13.
(** Conj_mul_SNo_assoc_lem2__23__23 TMZS7pvNKGLAzG1DCi5HJpjPY9xMgRTndSF bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__23__23.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g z2 (w2 + u2) = g z2 w2 + g z2 u2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, SNo z2 -> SNo w2 -> SNo u2 -> g (z2 + w2) u2 = g z2 u2 + g w2 u2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> g z2 (g y z) = g (g z2 y) z).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> g x (g z2 z) = g (g x z2) z).
Hypothesis H8: (forall z2:set, z2 :e SNoS_ (SNoLev z) -> g x (g y z2) = g (g x y) z2).
Hypothesis H9: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> g z2 (g w2 z) = g (g z2 w2) z)).
Hypothesis H10: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g z2 (g y w2) = g (g z2 y) w2)).
Hypothesis H11: (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> g x (g z2 w2) = g (g x z2) w2)).
Hypothesis H12: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, w2 :e SNoS_ (SNoLev y) -> (forall u2:set, u2 :e SNoS_ (SNoLev z) -> g z2 (g w2 u2) = g (g z2 w2) u2))).
Hypothesis H13: SNo (g x y).
Hypothesis H14: SNo (g y z).
Hypothesis H15: SNo (g (g x y) z).
Hypothesis H16: u :e SNoS_ (SNoLev x).
Hypothesis H17: SNo v.
Hypothesis H18: x2 :e SNoS_ (SNoLev y).
Hypothesis H19: y2 :e SNoS_ (SNoLev z).
Hypothesis H20: w = g u (g y z) + g x v + - (g u v).
Hypothesis H21: (g x (g x2 z + g y y2) + g u (v + g x2 y2)) <= g u (g x2 z + g y y2) + g x (v + g x2 y2).
Hypothesis H22: (g (g x y + g u x2) z + g (g u y + g x x2) y2) < g (g u y + g x x2) z + g (g x y + g u x2) y2.
Hypothesis H24: SNo x2.
Hypothesis H25: SNo y2.
Theorem Conj_mul_SNo_assoc_lem2__23__23: SNo (g u (g y z)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__23__23.
(** Conj_mul_SNo_assoc_lem2__24__1 TMN1TZQea8oMprwHKLLtA8Fj69vA3WjDGCD bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__24__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> SNo (g x2 y2)).
Hypothesis H2: SNo x.
Hypothesis H3: SNo y.
Hypothesis H4: SNo z.
Hypothesis H5: SNo (g x y).
Hypothesis H6: SNo w.
Hypothesis H7: x < w.
Hypothesis H8: SNo u.
Hypothesis H9: y < u.
Hypothesis H10: SNo v.
Hypothesis H11: z < v.
Hypothesis H12: SNo (g w y).
Hypothesis H13: SNo (g w u).
Hypothesis H14: SNo (g x u).
Hypothesis H15: SNo (g (g w y + g x u) z).
Hypothesis H16: SNo (g (g x y + g w u) z).
Hypothesis H17: SNo (g (g w y + g x u) v).
Hypothesis H18: SNo (g (g x y + g w u) v).
Hypothesis H19: SNo (g w y + g x u).
Theorem Conj_mul_SNo_assoc_lem2__24__1: SNo (g x y + g w u) -> (g (g x y + g w u) z + g (g w y + g x u) v) < g (g w y + g x u) z + g (g x y + g w u) v.
Admitted.

End Conj_mul_SNo_assoc_lem2__24__1.
(** Conj_mul_SNo_assoc_lem2__25__14 TMQYM7NwQtJHgtiFTXYDjtAHnRkN6VEDxSW bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__25__14.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> SNo (g x2 y2)).
Hypothesis H1: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 < x2 -> w2 < y2 -> (g z2 y2 + g x2 w2) < g x2 y2 + g z2 w2).
Hypothesis H2: SNo x.
Hypothesis H3: SNo y.
Hypothesis H4: SNo z.
Hypothesis H5: SNo (g x y).
Hypothesis H6: SNo w.
Hypothesis H7: x < w.
Hypothesis H8: SNo u.
Hypothesis H9: y < u.
Hypothesis H10: SNo v.
Hypothesis H11: z < v.
Hypothesis H12: SNo (g w y).
Hypothesis H13: SNo (g w u).
Hypothesis H15: SNo (g (g w y + g x u) z).
Hypothesis H16: SNo (g (g x y + g w u) z).
Hypothesis H17: SNo (g (g w y + g x u) v).
Hypothesis H18: SNo (g (g x y + g w u) v).
Theorem Conj_mul_SNo_assoc_lem2__25__14: SNo (g w y + g x u) -> (g (g x y + g w u) z + g (g w y + g x u) v) < g (g w y + g x u) z + g (g x y + g w u) v.
Admitted.

End Conj_mul_SNo_assoc_lem2__25__14.
(** Conj_mul_SNo_assoc_lem2__28__17 TMS7QnHzYwthVFEwwZ2oHnBaxVAVysPQ5XW bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__28__17.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g u y + g x x2).
Hypothesis H26: SNo (g x y + g u x2).
Hypothesis H27: SNo (g (g u y + g x x2) z).
Theorem Conj_mul_SNo_assoc_lem2__28__17: SNo (g (g x y + g u x2) z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__28__17.
(** Conj_mul_SNo_assoc_lem2__31__23 TMaswt3VQfgAP8iLwNQf3SddDJMfXKuq9jE bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__31__23.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H24: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__31__23: SNo (g u y + g x x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__31__23.
(** Conj_mul_SNo_assoc_lem2__32__4 TMTUL9hvCGi16XsBkqVAzMAGyLmHNXjcHfk bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__32__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__32__4: SNo (g x (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__32__4.
(** Conj_mul_SNo_assoc_lem2__32__6 TMVUeBHCw5rfBG6Nf4qV3BQUp9gWJnd6KwA bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__32__6.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__32__6: SNo (g x (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__32__6.
(** Conj_mul_SNo_assoc_lem2__32__11 TMYfwfTdbFtNh5e1TEeEXUSYfFCjAs72MGW bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__32__11.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__32__11: SNo (g x (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__32__11.
(** Conj_mul_SNo_assoc_lem2__32__21 TMK6mYMC2St2bcXgkUfHaZuPW38AXvVigcQ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__32__21.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g u y).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__32__21: SNo (g x (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__32__21.
(** Conj_mul_SNo_assoc_lem2__33__1 TMcCgYG3nv7wt2sXCfKPqGbyB1XZDRRQw6Z bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__33__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__33__1: SNo (g u v + g u (g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__33__1.
(** Conj_mul_SNo_assoc_lem2__34__7 TMM2rvruYoGsNTRc2KH1P2nHUFBL5Mda1ZZ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__34__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__34__7: SNo (g u (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__34__7.
(** Conj_mul_SNo_assoc_lem2__36__5 TMKNXY6wqnYGPwAVaELvA3rrUhCLKyu2EFg bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__36__5.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__36__5: SNo (g u (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__36__5.
(** Conj_mul_SNo_assoc_lem2__36__10 TMYjpptZ1Kj2oLphKLafKJpYBXBfP9rBPcx bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__36__10.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__36__10: SNo (g u (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__36__10.
(** Conj_mul_SNo_assoc_lem2__37__9 TMdeLPLPwDrFwU3RbWN3jfBwHswZCpjEQDZ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__37__9.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__37__9: SNo (g x (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__37__9.
(** Conj_mul_SNo_assoc_lem2__37__12 TMNryvsbv5fFpSkCs1auQHeYpVHWWHpHhdC bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__37__12.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__37__12: SNo (g x (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__37__12.
(** Conj_mul_SNo_assoc_lem2__37__14 TMGs5bsCzmo4wNE1QdfyoxjsJPcUcezEaMX bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__37__14.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__37__14: SNo (g x (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__37__14.
(** Conj_mul_SNo_assoc_lem2__39__13 TMNC1VHTJQsNSPKeN389Mcbj6H3V2wfkoF4 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__39__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem2__39__13: SNo (g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__39__13.
(** Conj_mul_SNo_assoc_lem2__40__4 TMb6a9MwoRRTArjL1znmzoSZHREhbRHj9Lo bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__40__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z).
Hypothesis H25: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem2__40__4: SNo (g x2 z + g y y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__40__4.
(** Conj_mul_SNo_assoc_lem2__40__14 TMHqvQzY4vjQQMo2kF1DN8JZhCa5nHZ98W9 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__40__14.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z).
Hypothesis H25: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem2__40__14: SNo (g x2 z + g y y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__40__14.
(** Conj_mul_SNo_assoc_lem2__42__4 TMWaixchB1EoAuxtMZyCM8h4swsxiDand6m bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__42__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Theorem Conj_mul_SNo_assoc_lem2__42__4: SNo (g x2 z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__42__4.
(** Conj_mul_SNo_assoc_lem2__42__15 TMYoHo4haydzNdVTLYhr2PP71XFV6f7zJia bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__42__15.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Theorem Conj_mul_SNo_assoc_lem2__42__15: SNo (g x2 z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__42__15.
(** Conj_mul_SNo_assoc_lem2__42__18 TMW4eLZAbFu5ejikBcoUuYLMU3As4Zh62VS bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__42__18.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Theorem Conj_mul_SNo_assoc_lem2__42__18: SNo (g x2 z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__42__18.
(** Conj_mul_SNo_assoc_lem2__45__4 TMKdP4SL5ucMoESxPitXVtX2ALgUWHuyNfL bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__45__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H15: y2 :e SNoR z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Theorem Conj_mul_SNo_assoc_lem2__45__4: SNo (g u y) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__45__4.
(** Conj_mul_SNo_assoc_lem2__45__15 TMTikR4XceorDfdtQiHETfDdabKsUUPvtVy bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__45__15.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoR y.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: y < x2.
Hypothesis H19: SNo y2.
Hypothesis H20: z < y2.
Theorem Conj_mul_SNo_assoc_lem2__45__15: SNo (g u y) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__45__15.
(** Conj_mul_SNo_assoc_lem2__48__14 TMT3nUxzqDef7tfkgrUPSGgMb2ixybp6r6U bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__48__14.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H7: u :e SNoR x.
Hypothesis H8: w = g u (g y z) + g x v + - (g u v).
Hypothesis H9: SNo u.
Hypothesis H10: x < u.
Hypothesis H11: SNo v.
Hypothesis H12: x2 :e SNoL y.
Hypothesis H13: y2 :e SNoL z.
Hypothesis H15: SNo x2.
Hypothesis H16: x2 < y.
Hypothesis H17: SNo y2.
Hypothesis H18: y2 < z.
Hypothesis H19: SNo (g x2 z + g y y2).
Hypothesis H20: SNo (v + g x2 y2).
Hypothesis H21: SNo (g u y + g x x2).
Hypothesis H22: SNo (g x y + g u x2).
Theorem Conj_mul_SNo_assoc_lem2__48__14: SNo (g (g x y + g u x2) z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__48__14.
(** Conj_mul_SNo_assoc_lem2__48__21 TMMG8gnjS3XAQXfWgCnazW7AkzsvR4uqHKf bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__48__21.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H7: u :e SNoR x.
Hypothesis H8: w = g u (g y z) + g x v + - (g u v).
Hypothesis H9: SNo u.
Hypothesis H10: x < u.
Hypothesis H11: SNo v.
Hypothesis H12: x2 :e SNoL y.
Hypothesis H13: y2 :e SNoL z.
Hypothesis H14: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H15: SNo x2.
Hypothesis H16: x2 < y.
Hypothesis H17: SNo y2.
Hypothesis H18: y2 < z.
Hypothesis H19: SNo (g x2 z + g y y2).
Hypothesis H20: SNo (v + g x2 y2).
Hypothesis H22: SNo (g x y + g u x2).
Theorem Conj_mul_SNo_assoc_lem2__48__21: SNo (g (g x y + g u x2) z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__48__21.
(** Conj_mul_SNo_assoc_lem2__50__1 TMR9dqsch3YvE3fTz13KSmSGTddFonY238r bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__50__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u x2).
Hypothesis H21: SNo (g x2 z + g y y2).
Hypothesis H22: SNo (v + g x2 y2).
Hypothesis H23: SNo (g u y + g x x2).
Theorem Conj_mul_SNo_assoc_lem2__50__1: SNo (g x y + g u x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__50__1.
(** Conj_mul_SNo_assoc_lem2__50__2 TMWXFjWUL1SKTfJEyohLEaaCkjkSSa2VZSZ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__50__2.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u x2).
Hypothesis H21: SNo (g x2 z + g y y2).
Hypothesis H22: SNo (v + g x2 y2).
Hypothesis H23: SNo (g u y + g x x2).
Theorem Conj_mul_SNo_assoc_lem2__50__2: SNo (g x y + g u x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__50__2.
(** Conj_mul_SNo_assoc_lem2__51__12 TMFHLmKnnfKs1D3E6NyWmmWRaZYNxf5Gfcw bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__51__12.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__51__12: SNo (g u y + g x x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__51__12.
(** Conj_mul_SNo_assoc_lem2__51__15 TMQHV9L2FKs5b2X4EeX1xboocv4thgkmLHx bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__51__15.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__51__15: SNo (g u y + g x x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__51__15.
(** Conj_mul_SNo_assoc_lem2__52__12 TMZbKWyWifTHPMaSivPiEPtwfYMUrTPqcTL bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__52__12.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__52__12: SNo (g x (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__52__12.
(** Conj_mul_SNo_assoc_lem2__53__6 TMcBPERf69M1tWrG1ru9KxKcaaKUTL15Rf9 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__53__6.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__53__6: SNo (g u v + g u (g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__53__6.
(** Conj_mul_SNo_assoc_lem2__53__18 TMMMviAFZ4dJ423MZrq7U5TYpiHh8teJZrq bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__53__18.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__53__18: SNo (g u v + g u (g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__53__18.
(** Conj_mul_SNo_assoc_lem2__54__10 TMKDAAdxAjZFsnpWNqph7UBxBfXqJRq8vHf bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__54__10.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__54__10: SNo (g u (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__54__10.
(** Conj_mul_SNo_assoc_lem2__57__11 TMQdNjtjCmVVxgeAwdQ242WWkn7SG6zFt1A bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__57__11.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__57__11: SNo (g x (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__57__11.
(** Conj_mul_SNo_assoc_lem2__57__18 TMdeaupC9Jes2pmEFaJHftNLt2N6ivEbMfu bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__57__18.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Hypothesis H26: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__57__18: SNo (g x (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__57__18.
(** Conj_mul_SNo_assoc_lem2__58__3 TMKLqfPLWB6RGNvuGUYLVsanWVM8j9PY7ij bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__58__3.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Hypothesis H25: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__58__3: SNo (v + g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__58__3.
(** Conj_mul_SNo_assoc_lem2__59__19 TMF1G8GFaQpLFVC51BLDZNtsA3SvTuw4C7V bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__59__19.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem2__59__19: SNo (g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__59__19.
(** Conj_mul_SNo_assoc_lem2__60__9 TMRAzdzCAgW3Dd25Lz6eN9ZHC3TLy6SrZPU bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__60__9.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z).
Hypothesis H25: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem2__60__9: SNo (g x2 z + g y y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__60__9.
(** Conj_mul_SNo_assoc_lem2__60__20 TMQsuQgfVu1W87P8ZJZt8vr8shcutXVGACx bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__60__20.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Hypothesis H24: SNo (g x2 z).
Hypothesis H25: SNo (g y y2).
Theorem Conj_mul_SNo_assoc_lem2__60__20: SNo (g x2 z + g y y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__60__20.
(** Conj_mul_SNo_assoc_lem2__62__21 TMdYqkDR1gnzUoaagccMDFBfiBkdqHz725X bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__62__21.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H22: SNo (g u x2).
Hypothesis H23: SNo (g x x2).
Theorem Conj_mul_SNo_assoc_lem2__62__21: SNo (g x2 z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__62__21.
(** Conj_mul_SNo_assoc_lem2__63__4 TMZrMdAMJxccKMmWwq8Tf2PjEd1t3PTPneh bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__63__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem2__63__4: SNo (g x x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__63__4.
(** Conj_mul_SNo_assoc_lem2__63__5 TMLxbz6cJ1ydgsj4KDLcfgmWCtRbsM7G6cf bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__63__5.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Hypothesis H22: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem2__63__5: SNo (g x x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__63__5.
(** Conj_mul_SNo_assoc_lem2__64__4 TMWEe4j6FD7anaRNuDY88CfdHkG9mZtWMeU bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__64__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoR x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: x < u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: x2 :e SNoL y.
Hypothesis H15: y2 :e SNoL z.
Hypothesis H16: (v + g x2 y2) <= g x2 z + g y y2.
Hypothesis H17: SNo x2.
Hypothesis H18: x2 < y.
Hypothesis H19: SNo y2.
Hypothesis H20: y2 < z.
Hypothesis H21: SNo (g u y).
Theorem Conj_mul_SNo_assoc_lem2__64__4: SNo (g u x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__64__4.
(** Conj_mul_SNo_assoc_lem2__66__10 TMNjyCWGVtHZxe5RXRaboKnJBQq2mEi3aGr bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__66__10.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> SNo (g x2 y2)).
Hypothesis H1: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> (forall z2:set, z2 :e SNoL (g x2 y2) -> (forall P:prop, (forall w2:set, w2 :e SNoL x2 -> (forall u2:set, u2 :e SNoL y2 -> (z2 + g w2 u2) <= g w2 y2 + g x2 u2 -> P)) -> (forall w2:set, w2 :e SNoR x2 -> (forall u2:set, u2 :e SNoR y2 -> (z2 + g w2 u2) <= g w2 y2 + g x2 u2 -> P)) -> P))).
Hypothesis H2: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 < x2 -> w2 < y2 -> (g z2 y2 + g x2 w2) < g x2 y2 + g z2 w2).
Hypothesis H3: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 <= x2 -> w2 <= y2 -> (g z2 y2 + g x2 w2) <= g x2 y2 + g z2 w2).
Hypothesis H4: SNo x.
Hypothesis H5: SNo y.
Hypothesis H6: SNo z.
Hypothesis H7: SNo (g x y).
Hypothesis H8: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> w = g x2 (g y z) + g x y2 + - (g x2 y2) -> (g x (g z2 z + g y w2) + g x2 (y2 + g z2 w2)) <= g x2 (g z2 z + g y w2) + g x (y2 + g z2 w2) -> (g (g x y + g x2 z2) z + g (g x2 y + g x z2) w2) < g (g x2 y + g x z2) z + g (g x y + g x2 z2) w2 -> g (g x y) z < w)))).
Hypothesis H9: u :e SNoR x.
Hypothesis H11: w = g u (g y z) + g x v + - (g u v).
Hypothesis H12: SNo u.
Hypothesis H13: x < u.
Hypothesis H14: SNo v.
Theorem Conj_mul_SNo_assoc_lem2__66__10: SNo (g u v) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__66__10.
(** Conj_mul_SNo_assoc_lem2__71__8 TMUia5NQQZn5Cv6LDEDti2qfsbYZ9MJQiqP bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__71__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g u (v + g x2 y2)).
Hypothesis H26: SNo (g u (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem2__71__8: SNo (g x (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__71__8.
(** Conj_mul_SNo_assoc_lem2__72__20 TMF4BUCpvuMHoGCdWRB93SwdFMUk5MSEiEN bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__72__20.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g u (v + g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__72__20: SNo (g u (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__72__20.
(** Conj_mul_SNo_assoc_lem2__73__7 TMVRFVxgNYAFtVbcFAr9LAwtaHhGgjw1rfQ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__73__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__73__7: SNo (g u (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__73__7.
(** Conj_mul_SNo_assoc_lem2__73__10 TMN4m6Vn2ZqKBY1DaWq3DUNK1aUgTXznV2E bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__73__10.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__73__10: SNo (g u (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__73__10.
(** Conj_mul_SNo_assoc_lem2__74__16 TMFpDLWvYyv1SHGThwBjdMe7nTT8c3DHYgm bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__74__16.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__74__16: SNo (v + g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__74__16.
(** Conj_mul_SNo_assoc_lem2__75__7 TMMorLf3eqGHEzELmJyJsoFgGtg87n5F76V bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__75__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem2__75__7: SNo (g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__75__7.
(** Conj_mul_SNo_assoc_lem2__75__19 TMchhuUvq6awkL2mN7LoeSWVi6FF4Y3SVg1 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__75__19.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem2__75__19: SNo (g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__75__19.
(** Conj_mul_SNo_assoc_lem2__77__18 TMUMAy59dAPD9HP7pRVgCbiDvr5HL8zYYtz bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__77__18.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem2__77__18: SNo (g y y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__77__18.
(** Conj_mul_SNo_assoc_lem2__79__17 TMdRrSrTCeg1aBJ1SK9CAT3ffoWHUhNNRUa bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__79__17.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem2__79__17: SNo (g x x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__79__17.
(** Conj_mul_SNo_assoc_lem2__79__19 TMa4hApiuyiLbznCpqgq76oCUPSeaoupGSj bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__79__19.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H20: SNo (g u y).
Hypothesis H21: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem2__79__19: SNo (g x x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__79__19.
(** Conj_mul_SNo_assoc_lem2__80__11 TMGxXVew6ifmMvWXt4SU9PvcPMzfFWArYri bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__80__11.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Hypothesis H19: y2 < z.
Hypothesis H20: SNo (g u y).
Theorem Conj_mul_SNo_assoc_lem2__80__11: SNo (g u x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__80__11.
(** Conj_mul_SNo_assoc_lem2__81__19 TMTVcGt5Jks2ECokwC99x99ouDacQAZWhk8 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__81__19.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoR y.
Hypothesis H14: y2 :e SNoL z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: y < x2.
Hypothesis H18: SNo y2.
Theorem Conj_mul_SNo_assoc_lem2__81__19: SNo (g u y) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__81__19.
(** Conj_mul_SNo_assoc_lem2__82__13 TMLTkDaEidxHX7pTvG74zaRz2pqUWdtuM99 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__82__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g x2 z + g y y2).
Hypothesis H21: SNo (v + g x2 y2).
Hypothesis H22: SNo (g x (v + g x2 y2)).
Hypothesis H23: SNo (g u (v + g x2 y2)).
Hypothesis H24: SNo (g u (g x2 z + g y y2)).
Hypothesis H25: SNo (g x (g x2 z + g y y2)).
Hypothesis H26: SNo (g u y + g x x2).
Hypothesis H27: SNo (g (g x y + g u x2) z).
Hypothesis H28: SNo (g (g u y + g x x2) z).
Hypothesis H29: SNo (g (g x y + g u x2) y2).
Theorem Conj_mul_SNo_assoc_lem2__82__13: SNo (g (g u y + g x x2) y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__82__13.
(** Conj_mul_SNo_assoc_lem2__83__29 TMW5TTAGgQ7cixwS3g8HL9pR5xo1RxRbE21 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__83__29.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g x2 z + g y y2).
Hypothesis H21: SNo (v + g x2 y2).
Hypothesis H22: SNo (g x (v + g x2 y2)).
Hypothesis H23: SNo (g u (v + g x2 y2)).
Hypothesis H24: SNo (g u (g x2 z + g y y2)).
Hypothesis H25: SNo (g x (g x2 z + g y y2)).
Hypothesis H26: SNo (g u y + g x x2).
Hypothesis H27: SNo (g (g x y + g u x2) z).
Hypothesis H28: SNo (g (g u y + g x x2) z).
Theorem Conj_mul_SNo_assoc_lem2__83__29: SNo (g (g x y + g u x2) y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__83__29.
(** Conj_mul_SNo_assoc_lem2__84__12 TMFodmi4xxS7aGL6CfBbmtkPpeUhqgEjby8 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__84__12.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g x2 z + g y y2).
Hypothesis H21: SNo (v + g x2 y2).
Hypothesis H22: SNo (g x (v + g x2 y2)).
Hypothesis H23: SNo (g u (v + g x2 y2)).
Hypothesis H24: SNo (g u (g x2 z + g y y2)).
Hypothesis H25: SNo (g x (g x2 z + g y y2)).
Hypothesis H26: SNo (g u y + g x x2).
Hypothesis H27: SNo (g (g x y + g u x2) z).
Hypothesis H28: SNo (g (g u y + g x x2) z).
Theorem Conj_mul_SNo_assoc_lem2__84__12: SNo (g x y + g u x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__84__12.
(** Conj_mul_SNo_assoc_lem2__84__14 TMQY4T3ubJfhftBv9ViH96G4KYSEWsCieLH bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__84__14.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g x2 z + g y y2).
Hypothesis H21: SNo (v + g x2 y2).
Hypothesis H22: SNo (g x (v + g x2 y2)).
Hypothesis H23: SNo (g u (v + g x2 y2)).
Hypothesis H24: SNo (g u (g x2 z + g y y2)).
Hypothesis H25: SNo (g x (g x2 z + g y y2)).
Hypothesis H26: SNo (g u y + g x x2).
Hypothesis H27: SNo (g (g x y + g u x2) z).
Hypothesis H28: SNo (g (g u y + g x x2) z).
Theorem Conj_mul_SNo_assoc_lem2__84__14: SNo (g x y + g u x2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__84__14.
(** Conj_mul_SNo_assoc_lem2__86__1 TMbtP3vCJ1MBrpjDbBZsnQyASGZqSeMueqC bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__86__1.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g x2 z + g y y2).
Hypothesis H21: SNo (v + g x2 y2).
Hypothesis H22: SNo (g x (v + g x2 y2)).
Hypothesis H23: SNo (g u (v + g x2 y2)).
Hypothesis H24: SNo (g u (g x2 z + g y y2)).
Hypothesis H25: SNo (g x (g x2 z + g y y2)).
Hypothesis H26: SNo (g x y + g u x2).
Hypothesis H27: SNo (g u y + g x x2).
Theorem Conj_mul_SNo_assoc_lem2__86__1: SNo (g (g x y + g u x2) z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__86__1.
(** Conj_mul_SNo_assoc_lem2__86__26 TMcvDyNzPQM4UuPfpLtJ2gJnaYhUKLhWokY bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__86__26.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: x2 :e SNoL y.
Hypothesis H14: y2 :e SNoR z.
Hypothesis H15: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H16: SNo x2.
Hypothesis H17: x2 < y.
Hypothesis H18: SNo y2.
Hypothesis H19: z < y2.
Hypothesis H20: SNo (g x2 z + g y y2).
Hypothesis H21: SNo (v + g x2 y2).
Hypothesis H22: SNo (g x (v + g x2 y2)).
Hypothesis H23: SNo (g u (v + g x2 y2)).
Hypothesis H24: SNo (g u (g x2 z + g y y2)).
Hypothesis H25: SNo (g x (g x2 z + g y y2)).
Hypothesis H27: SNo (g u y + g x x2).
Theorem Conj_mul_SNo_assoc_lem2__86__26: SNo (g (g x y + g u x2) z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__86__26.
(** Conj_mul_SNo_assoc_lem2__91__7 TMakxsvUDJMgbHQUTUbQeaem1Md2B2Xrfio bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__91__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (v + g x2 y2).
Hypothesis H25: SNo (g x (v + g x2 y2)).
Hypothesis H26: SNo (g u (v + g x2 y2)).
Hypothesis H27: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__91__7: SNo (g u (g x2 z + g y y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__91__7.
(** Conj_mul_SNo_assoc_lem2__93__22 TMJaxFd1ija3gF4PD7gSpeAscbPBNgHF6Mz bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__93__22.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (g x2 y2).
Hypothesis H25: SNo (v + g x2 y2).
Hypothesis H26: SNo (g x (v + g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem2__93__22: SNo (g u (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__93__22.
(** Conj_mul_SNo_assoc_lem2__94__7 TMHF55wZpTug6AbxH1Y8GFb88AfQ3itcx6N bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__94__7.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (g x2 y2).
Hypothesis H25: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__94__7: SNo (g x (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__94__7.
(** Conj_mul_SNo_assoc_lem2__94__13 TMVnpiXyAyCcbtPj5bkfTyxRiQwHtjy9Fyv bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__94__13.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (g x2 y2).
Hypothesis H25: SNo (v + g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__94__13: SNo (g x (v + g x2 y2)) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__94__13.
(** Conj_mul_SNo_assoc_lem2__95__2 TMUvij3kfTp9mS4idDBvEUhXmvZdBPHd6Fz bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__95__2.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__95__2: SNo (v + g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__95__2.
(** Conj_mul_SNo_assoc_lem2__95__8 TMRYeijPBdhiw71G2ubNa29GehSKppYYzZQ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__95__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Hypothesis H24: SNo (g x2 y2).
Theorem Conj_mul_SNo_assoc_lem2__95__8: SNo (v + g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__95__8.
(** Conj_mul_SNo_assoc_lem2__96__20 TMJxri3fAstdKePrGbv4qLDKFHLrWXhKXZJ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__96__20.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z + g y y2).
Theorem Conj_mul_SNo_assoc_lem2__96__20: SNo (g x2 y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__96__20.
(** Conj_mul_SNo_assoc_lem2__97__24 TMN9nXAUDGdWiUJ5xNUzJW1oDfrPSx2zC9q bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__97__24.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem2__97__24: SNo (g x2 z + g y y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__97__24.
(** Conj_mul_SNo_assoc_lem2__98__8 TMKeoxuV4Rw6QfdQd1E5KuoKx9QtFnJNfEW bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__98__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem2__98__8: SNo (g y y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__98__8.
(** Conj_mul_SNo_assoc_lem2__98__11 TMKbVDX8fgnRgqHnjiv1ustdKyctyGNDj87 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__98__11.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem2__98__11: SNo (g y y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__98__11.
(** Conj_mul_SNo_assoc_lem2__98__16 TMJU3C4xLSttVHjJ6ncmvAzf7BSuNbPXEuB bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__98__16.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Hypothesis H23: SNo (g x2 z).
Theorem Conj_mul_SNo_assoc_lem2__98__16: SNo (g y y2) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__98__16.
(** Conj_mul_SNo_assoc_lem2__99__3 TMXv9o9WGT7KPrmUVv24TQB9qKGu8VWoJih bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__99__3.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Theorem Conj_mul_SNo_assoc_lem2__99__3: SNo (g x2 z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__99__3.
(** Conj_mul_SNo_assoc_lem2__99__8 TMHKWPxWcaPS7jnCyrj6dsZAFFm4JYkuHPr bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__99__8.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
Hypothesis H0: (forall z2:set, forall w2:set, SNo z2 -> SNo w2 -> SNo (g z2 w2)).
Hypothesis H1: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 < z2 -> v2 < w2 -> (g u2 w2 + g z2 v2) < g z2 w2 + g u2 v2).
Hypothesis H2: (forall z2:set, forall w2:set, forall u2:set, forall v2:set, SNo z2 -> SNo w2 -> SNo u2 -> SNo v2 -> u2 <= z2 -> v2 <= w2 -> (g u2 w2 + g z2 v2) <= g z2 w2 + g u2 v2).
Hypothesis H3: SNo x.
Hypothesis H4: SNo y.
Hypothesis H5: SNo z.
Hypothesis H6: SNo (g x y).
Hypothesis H7: (forall z2:set, z2 :e SNoS_ (SNoLev x) -> (forall w2:set, SNo w2 -> (forall u2:set, u2 :e SNoS_ (SNoLev y) -> (forall v2:set, v2 :e SNoS_ (SNoLev z) -> w = g z2 (g y z) + g x w2 + - (g z2 w2) -> (g x (g u2 z + g y v2) + g z2 (w2 + g u2 v2)) <= g z2 (g u2 z + g y v2) + g x (w2 + g u2 v2) -> (g (g x y + g z2 u2) z + g (g z2 y + g x u2) v2) < g (g z2 y + g x u2) z + g (g x y + g z2 u2) v2 -> g (g x y) z < w)))).
Hypothesis H9: w = g u (g y z) + g x v + - (g u v).
Hypothesis H10: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (g u v).
Hypothesis H14: SNo (g u y).
Hypothesis H15: x2 :e SNoL y.
Hypothesis H16: y2 :e SNoR z.
Hypothesis H17: (g x2 z + g y y2) <= v + g x2 y2.
Hypothesis H18: SNo x2.
Hypothesis H19: x2 < y.
Hypothesis H20: SNo y2.
Hypothesis H21: z < y2.
Hypothesis H22: SNo (g x x2).
Theorem Conj_mul_SNo_assoc_lem2__99__8: SNo (g x2 z) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__99__8.
(** Conj_mul_SNo_assoc_lem2__101__4 TMc2SsF2ShVXAbGTuHuu7yxMqnUS24H358Y bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem2__101__4.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> SNo (g x2 y2)).
Hypothesis H1: (forall x2:set, forall y2:set, SNo x2 -> SNo y2 -> (forall z2:set, z2 :e SNoR (g x2 y2) -> (forall P:prop, (forall w2:set, w2 :e SNoL x2 -> (forall u2:set, u2 :e SNoR y2 -> (g w2 y2 + g x2 u2) <= z2 + g w2 u2 -> P)) -> (forall w2:set, w2 :e SNoR x2 -> (forall u2:set, u2 :e SNoL y2 -> (g w2 y2 + g x2 u2) <= z2 + g w2 u2 -> P)) -> P))).
Hypothesis H2: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 < x2 -> w2 < y2 -> (g z2 y2 + g x2 w2) < g x2 y2 + g z2 w2).
Hypothesis H3: (forall x2:set, forall y2:set, forall z2:set, forall w2:set, SNo x2 -> SNo y2 -> SNo z2 -> SNo w2 -> z2 <= x2 -> w2 <= y2 -> (g z2 y2 + g x2 w2) <= g x2 y2 + g z2 w2).
Hypothesis H5: SNo y.
Hypothesis H6: SNo z.
Hypothesis H7: SNo (g x y).
Hypothesis H8: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, SNo y2 -> (forall z2:set, z2 :e SNoS_ (SNoLev y) -> (forall w2:set, w2 :e SNoS_ (SNoLev z) -> w = g x2 (g y z) + g x y2 + - (g x2 y2) -> (g x (g z2 z + g y w2) + g x2 (y2 + g z2 w2)) <= g x2 (g z2 z + g y w2) + g x (y2 + g z2 w2) -> (g (g x y + g x2 z2) z + g (g x2 y + g x z2) w2) < g (g x2 y + g x z2) z + g (g x y + g x2 z2) w2 -> g (g x y) z < w)))).
Hypothesis H9: u :e SNoL x.
Hypothesis H10: v :e SNoR (g y z).
Hypothesis H11: w = g u (g y z) + g x v + - (g u v).
Hypothesis H12: SNo u.
Hypothesis H13: u < x.
Hypothesis H14: SNo v.
Hypothesis H15: SNo (g u v).
Theorem Conj_mul_SNo_assoc_lem2__101__4: SNo (g u y) -> g (g x y) z < w.
Admitted.

End Conj_mul_SNo_assoc_lem2__101__4.
