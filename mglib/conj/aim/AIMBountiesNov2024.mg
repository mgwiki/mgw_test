(** $I sig/PfgEAug2022Preamble.mgs **)

Section AIM.

Variable X:set.
Variable m b s:set -> set -> set.
Variable e:set.
Variable K:set -> set -> set.
Variable a:set -> set -> set -> set.
Variable T:set -> set -> set.
Variable L R:set -> set -> set -> set.

Hypothesis He: e :e X.
Hypothesis Hm: forall x y :e X, m x y :e X.
Hypothesis Hs: forall x y :e X, s x y :e X.
Hypothesis Hb: forall x y :e X, b x y :e X.
Hypothesis HKdef: forall x y :e X, K x y = b (m y x) (m x y).
Hypothesis HK: forall x y :e X, K x y :e X.
Hypothesis Hadef: forall x y z :e X, a x y z = b (m x (m y z)) (m (m x y) z).
Hypothesis Ha: forall x y z :e X, a x y z :e X.
Hypothesis HTdef: forall u x :e X, T u x = b x (m u x).
Hypothesis HT: forall u x :e X, T u x :e X.
Hypothesis HLdef: forall u x y :e X, L u x y = b (m y x) (m y (m x u)).
Hypothesis HL: forall u x y :e X, L u x y :e X.
Hypothesis HRdef: forall u x y :e X, R u x y = s (m (m u x) y) (m x y).
Hypothesis HR: forall u x y :e X, R u x y :e X.
Hypothesis HeL: forall x :e X, m e x = x.
Hypothesis HeR: forall x :e X, m x e = x.
Hypothesis Hbm: forall x y :e X, b x (m x y) = y.
Hypothesis Hmb: forall x y :e X, m x (b x y) = y.
Hypothesis Hsm: forall x y :e X, s (m x y) y = x.
Hypothesis Hms: forall x y :e X, m (s x y) y = x.
Hypothesis HTT: forall u x y :e X, T (T u x) y = T (T u y) x.
Hypothesis HTL: forall u x y z :e X, T (L u x y) z = L (T u z) x y.
Hypothesis HTR: forall u x y z :e X, T (R u x y) z = R (T u z) x y.
Hypothesis HLR: forall u x y z w :e X, L (R u x y) z w = R (L u z w) x y.
Hypothesis HLL: forall u x y z w :e X, L (L u x y) z w = L (L u z w) x y.
Hypothesis HRR: forall u x y z w :e X, R (R u x y) z w = R (R u z w) x y.

Theorem aK1: forall x y z u :e X, a (K x y) z u = e.
Admitted.

Theorem aa1: forall x y z u w :e X, a (a x y z) u w = e.
Admitted.

Theorem com__aa1: (forall x y :e X, m x y = m y x)
 -> forall x y z u w :e X, a (a x y z) u w = e.
Admitted.

Theorem middle_Bol__aa1: (forall x y z :e X, m x (b (m y z) x) = m (s x z) (b y x))
 -> forall x y z u w :e X, a (a x y z) u w = e.
Admitted.

Theorem KK_Kcom__aa1: (forall x y z :e X, K (K x y) z = e)
 -> (forall x y :e X, K x y = K y x)
 -> forall x y z u w :e X, a (a x y z) u w = e.
Admitted.

Theorem T1dist__aa1: (forall x y z :e X, m (T x y) (T z y) = T (m x z) y)
 -> forall x y z u w :e X, a (a x y z) u w = e.
Admitted.

Theorem nil3_24: forall x y z u w v5 v6 :e X, a (a (a x y z) u w) v5 v6 = e.
Admitted.

Theorem com__nil3_24: (forall x y :e X, m x y = m y x)
 -> forall x y z u w v5 v6 :e X, a (a (a x y z) u w) v5 v6 = e.
Admitted.

Theorem aa1_45: forall x y z u w :e X, a (a x y z) u w = a (a x y z) w u.
Admitted.

Theorem nil3_24__aa1: (forall x y z u w v5 v6 :e X, a (a (a x y z) u w) v5 v6 = e)
  -> forall x y z u w :e X, a (a x y z) u w = e.
Admitted.

End AIM.
