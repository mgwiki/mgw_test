(** $I sig/OEISPreamble.mgs **)

(** Bounty 1 PFG TMLamgpmmLktCkXfzUSgfnZApbScHKB1v9y **)
Section A192796.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix < 490 := SNoLt.
Infix <= 490 := SNoLe.
Variable F0:set -> set -> set.
Hypothesis HF0: forall x0 :e int, forall x1 :e int, F0 x0 x1 :e int.
Variable F1:set -> set.
Hypothesis HF1: forall x0 :e int, F1 x0 :e int.
Variable G1:set.
Hypothesis HG1: G1 :e int.
Variable H1:set -> set.
Hypothesis HH1: forall x0 :e int, H1 x0 :e int.
Variable U1:set -> set -> set.
Hypothesis HU1: forall x0 :e int, forall x1 :e int, U1 x0 x1 :e int.
Variable V1:set -> set.
Hypothesis HV1: forall x0 :e int, V1 x0 :e int.
Variable G0:set -> set.
Hypothesis HG0: forall x0 :e int, G0 x0 :e int.
Variable H0:set.
Hypothesis HH0: H0 :e int.
Variable U0:set -> set -> set.
Hypothesis HU0: forall x0 :e int, forall x1 :e int, U0 x0 x1 :e int.
Variable V0:set -> set.
Hypothesis HV0: forall x0 :e int, V0 x0 :e int.
Variable SMALL:set -> set.
Hypothesis HSMALL: forall x0 :e int, SMALL x0 :e int.
Variable F2:set -> set.
Hypothesis HF2: forall x0 :e int, F2 x0 :e int.
Variable G2:set.
Hypothesis HG2: G2 :e int.
Variable H2:set -> set.
Hypothesis HH2: forall x0 :e int, H2 x0 :e int.
Variable U2:set -> set -> set.
Hypothesis HU2: forall x0 :e int, forall x1 :e int, U2 x0 x1 :e int.
Variable V2:set -> set.
Hypothesis HV2: forall x0 :e int, V2 x0 :e int.
Variable FAST:set -> set.
Hypothesis HFAST: forall x0 :e int, FAST x0 :e int.
Hypothesis H1: (forall X :e int, (forall Y :e int, ((F0 X Y) = (X + Y)))).
Hypothesis H2: (forall X :e int, ((F1 X) = (1 + (X + X)))).
Hypothesis H3: (G1 = 2).
Hypothesis H4: (forall X :e int, ((H1 X) = X)).
Hypothesis H5: (forall X :e int, (forall Y :e int, ((U1 X Y) = (if (X <= 0) then Y else (F1 (U1 (X + - 1) Y)))))).
Hypothesis H6: (forall X :e int, ((V1 X) = (U1 G1 (H1 X)))).
Hypothesis H7: (forall X :e int, ((G0 X) = (V1 X))).
Hypothesis H8: (H0 = 0).
Hypothesis H9: (forall X :e int, (forall Y :e int, ((U0 X Y) = (if (X <= 0) then Y else (F0 (U0 (X + - 1) Y) X))))).
Hypothesis H10: (forall X :e int, ((V0 X) = (U0 (G0 X) H0))).
Hypothesis H11: (forall X :e int, ((SMALL X) = ((V0 X) * X))).
Hypothesis H12: (forall X :e int, ((F2 X) = ((2 * (X * X)) + - X))).
Hypothesis H13: (G2 = 1).
Hypothesis H14: (forall X :e int, ((H2 X) = (2 + (X + X)))).
Hypothesis H15: (forall X :e int, (forall Y :e int, ((U2 X Y) = (if (X <= 0) then Y else (F2 (U2 (X + - 1) Y)))))).
Hypothesis H16: (forall X :e int, ((V2 X) = (U2 G2 (H2 X)))).
Hypothesis H17: (forall X :e int, ((FAST X) = ((V2 X) * X))).
Theorem A192796: (forall N :e int, ((0 <= N) -> ((SMALL N) = (FAST N)))).
Admitted.
End A192796.