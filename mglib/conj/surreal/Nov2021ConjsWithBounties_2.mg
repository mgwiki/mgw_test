(** $I sig/Nov2021ConjPreamble.mgs **)

(** Conj_mul_SNo_Lt__23__10 TMSJzQCLFKAzZP39iMF3SeiYqfkQEMGroHm bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__23__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo z.
Hypothesis H2: SNo w.
Hypothesis H3: SNo (x * y).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H5: SNo (z * y).
Hypothesis H6: SNo (x * w).
Hypothesis H7: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H8: SNo (z * w).
Hypothesis H9: SNo (z * y + x * w).
Hypothesis H11: z :e SNoL x.
Hypothesis H12: SNo u.
Hypothesis H13: w < u.
Hypothesis H14: SNoLev u :e SNoLev w.
Hypothesis H15: u :e SNoL y.
Theorem Conj_mul_SNo_Lt__23__10: u :e SNoR w -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__23__10.
(** Conj_mul_SNo_Lt__24__6 TMM5B3jeWUhr9Y2AMqqvCKXtF7M5rCSGXGB bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__24__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: SNo (x * y).
Hypothesis H5: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (x * w).
Hypothesis H8: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H9: SNo (z * w).
Hypothesis H10: SNo (z * y + x * w).
Hypothesis H11: SNo (x * y + z * w).
Hypothesis H12: z :e SNoL x.
Hypothesis H13: SNo u.
Hypothesis H14: w < u.
Hypothesis H15: u < y.
Hypothesis H16: SNoLev u :e SNoLev w.
Hypothesis H17: SNoLev u :e SNoLev y.
Theorem Conj_mul_SNo_Lt__24__6: u :e SNoL y -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__24__6.
(** Conj_mul_SNo_Lt__24__9 TMR6L3XCy7nHCdGqXLydM6J2cu2xvTcaEvE bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__24__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: SNo (x * y).
Hypothesis H5: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H6: SNo (z * y).
Hypothesis H7: SNo (x * w).
Hypothesis H8: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H10: SNo (z * y + x * w).
Hypothesis H11: SNo (x * y + z * w).
Hypothesis H12: z :e SNoL x.
Hypothesis H13: SNo u.
Hypothesis H14: w < u.
Hypothesis H15: u < y.
Hypothesis H16: SNoLev u :e SNoLev w.
Hypothesis H17: SNoLev u :e SNoLev y.
Theorem Conj_mul_SNo_Lt__24__9: u :e SNoL y -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__24__9.
(** Conj_mul_SNo_Lt__26__4 TMSh2aLEUxhrMRD3zK47Wk536jTYnEgofS4 bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__26__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H5: SNo (z * y + x * w).
Hypothesis H6: SNo (x * y + z * w).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (u * w).
Hypothesis H10: SNo (z * w + u * y).
Hypothesis H11: SNo (u * w + x * y).
Hypothesis H12: SNo (x * w + u * y).
Hypothesis H13: SNo (u * w + z * y).
Hypothesis H14: y :e SNoR w.
Hypothesis H15: (x * w + u * y) < u * w + x * y.
Theorem Conj_mul_SNo_Lt__26__4: (u * w + z * y) < z * w + u * y -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__26__4.
(** Conj_mul_SNo_Lt__27__13 TMWDCi488kgJBFgbimVVes2Si3XcVHjwmyV bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__27__13.
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
Hypothesis H5: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H6: SNo (z * y + x * w).
Hypothesis H7: SNo (x * y + z * w).
Hypothesis H8: u :e SNoL x.
Hypothesis H9: u :e SNoR z.
Hypothesis H10: SNo (u * y).
Hypothesis H11: SNo (u * w).
Hypothesis H12: SNo (z * w + u * y).
Hypothesis H14: SNo (x * w + u * y).
Hypothesis H15: SNo (u * w + z * y).
Hypothesis H16: y :e SNoR w.
Theorem Conj_mul_SNo_Lt__27__13: (x * w + u * y) < u * w + x * y -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__27__13.
(** Conj_mul_SNo_Lt__29__0 TMTA4dcGiWCpsNH7JKXsHZSxv7KQxCw912S bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__29__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H1: SNo (z * y).
Hypothesis H2: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H3: SNo (x * w).
Hypothesis H4: SNo (z * w).
Hypothesis H5: SNo (z * y + x * w).
Hypothesis H6: SNo (x * y + z * w).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (u * w).
Hypothesis H10: SNo (u * y + x * w).
Hypothesis H11: SNo (u * y + z * w).
Hypothesis H12: SNo (x * y + u * w).
Hypothesis H13: SNo (z * y + u * w).
Hypothesis H14: w :e SNoL y.
Hypothesis H15: (u * y + x * w) < x * y + u * w.
Theorem Conj_mul_SNo_Lt__29__0: (z * y + u * w) < u * y + z * w -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__29__0.
(** Conj_mul_SNo_Lt__29__6 TMWhvRjMoLy1WfwXqsJnxWVp2rUh7U6UWtY bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__29__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H3: SNo (x * w).
Hypothesis H4: SNo (z * w).
Hypothesis H5: SNo (z * y + x * w).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (u * w).
Hypothesis H10: SNo (u * y + x * w).
Hypothesis H11: SNo (u * y + z * w).
Hypothesis H12: SNo (x * y + u * w).
Hypothesis H13: SNo (z * y + u * w).
Hypothesis H14: w :e SNoL y.
Hypothesis H15: (u * y + x * w) < x * y + u * w.
Theorem Conj_mul_SNo_Lt__29__6: (z * y + u * w) < u * y + z * w -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__29__6.
(** Conj_mul_SNo_Lt__29__10 TMKCfb9ckE56MyrzjUBFqG6zkWFq4k7tXKE bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__29__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H3: SNo (x * w).
Hypothesis H4: SNo (z * w).
Hypothesis H5: SNo (z * y + x * w).
Hypothesis H6: SNo (x * y + z * w).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (u * w).
Hypothesis H11: SNo (u * y + z * w).
Hypothesis H12: SNo (x * y + u * w).
Hypothesis H13: SNo (z * y + u * w).
Hypothesis H14: w :e SNoL y.
Hypothesis H15: (u * y + x * w) < x * y + u * w.
Theorem Conj_mul_SNo_Lt__29__10: (z * y + u * w) < u * y + z * w -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__29__10.
(** Conj_mul_SNo_Lt__31__9 TMH5Grq7zsnjYv26ZDa8JowokvgfSzbBM6g bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__31__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo y.
Hypothesis H1: SNo w.
Hypothesis H2: w < y.
Hypothesis H3: SNo (x * y).
Hypothesis H4: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H5: SNo (z * y).
Hypothesis H6: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H7: SNo (x * w).
Hypothesis H8: SNo (z * w).
Hypothesis H10: SNo (x * y + z * w).
Hypothesis H11: u :e SNoL x.
Hypothesis H12: u :e SNoR z.
Hypothesis H13: SNo (u * y).
Hypothesis H14: SNo (u * w).
Hypothesis H15: SNo (u * y + x * w).
Hypothesis H16: SNo (u * y + z * w).
Hypothesis H17: SNo (x * y + u * w).
Hypothesis H18: SNo (z * y + u * w).
Hypothesis H19: SNoLev w :e SNoLev y.
Theorem Conj_mul_SNo_Lt__31__9: w :e SNoL y -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__31__9.
(** Conj_mul_SNo_Lt__32__13 TML5bFhRXz3dvDHaDREG312xhDsUeajvaPE bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__32__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Hypothesis H16: SNo (u * y + z * v).
Hypothesis H17: SNo (u * w + x * v).
Hypothesis H18: SNo (z * y + u * v).
Hypothesis H19: SNo (x * w + u * v).
Hypothesis H20: SNo (u * w + z * v).
Hypothesis H21: SNo (u * y + x * v).
Hypothesis H22: SNo (x * y + u * v).
Theorem Conj_mul_SNo_Lt__32__13: SNo (z * w + u * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__32__13.
(** Conj_mul_SNo_Lt__33__2 TMHSmdzHtuLUHZGW6ztqu8vyfVuQq5WVEDR bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__33__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Hypothesis H16: SNo (u * y + z * v).
Hypothesis H17: SNo (u * w + x * v).
Hypothesis H18: SNo (z * y + u * v).
Hypothesis H19: SNo (x * w + u * v).
Hypothesis H20: SNo (u * w + z * v).
Hypothesis H21: SNo (u * y + x * v).
Theorem Conj_mul_SNo_Lt__33__2: SNo (x * y + u * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__33__2.
(** Conj_mul_SNo_Lt__33__21 TMYzh6zx9rAk9HCGP926gPZqUq8g7rmcKhC bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__33__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Hypothesis H16: SNo (u * y + z * v).
Hypothesis H17: SNo (u * w + x * v).
Hypothesis H18: SNo (z * y + u * v).
Hypothesis H19: SNo (x * w + u * v).
Hypothesis H20: SNo (u * w + z * v).
Theorem Conj_mul_SNo_Lt__33__21: SNo (x * y + u * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__33__21.
(** Conj_mul_SNo_Lt__34__7 TMYJt5rndtZh7Rk1pKGYha7EXJ7yzy66wt3 bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__34__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Hypothesis H16: SNo (u * y + z * v).
Hypothesis H17: SNo (u * w + x * v).
Hypothesis H18: SNo (z * y + u * v).
Hypothesis H19: SNo (x * w + u * v).
Hypothesis H20: SNo (u * w + z * v).
Theorem Conj_mul_SNo_Lt__34__7: SNo (u * y + x * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__34__7.
(** Conj_mul_SNo_Lt__35__7 TMJX18vHwEUsfnF9mNsDK9rbPzvoCZWqtu3 bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__35__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Hypothesis H16: SNo (u * y + z * v).
Hypothesis H17: SNo (u * w + x * v).
Hypothesis H18: SNo (z * y + u * v).
Hypothesis H19: SNo (x * w + u * v).
Hypothesis H20: SNo (u * w + z * v).
Theorem Conj_mul_SNo_Lt__35__7: SNo (x * y + x * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__35__7.
(** Conj_mul_SNo_Lt__35__18 TMK8wovVNU9kS2PZdgF6BhTCbUZPzycbTzX bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__35__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Hypothesis H16: SNo (u * y + z * v).
Hypothesis H17: SNo (u * w + x * v).
Hypothesis H19: SNo (x * w + u * v).
Hypothesis H20: SNo (u * w + z * v).
Theorem Conj_mul_SNo_Lt__35__18: SNo (x * y + x * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__35__18.
(** Conj_mul_SNo_Lt__36__19 TMPGm6jKX5nLrSVYy17sf1nwYupMDqETvxB bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__36__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Hypothesis H16: SNo (u * y + z * v).
Hypothesis H17: SNo (u * w + x * v).
Hypothesis H18: SNo (z * y + u * v).
Theorem Conj_mul_SNo_Lt__36__19: SNo (u * w + z * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__36__19.
(** Conj_mul_SNo_Lt__37__3 TMdd9s7BtiTMUjxLWLTJp2846TJHzXRToHF bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__37__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Hypothesis H16: SNo (u * y + z * v).
Hypothesis H17: SNo (u * w + x * v).
Hypothesis H18: SNo (z * y + u * v).
Theorem Conj_mul_SNo_Lt__37__3: SNo (x * w + u * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__37__3.
(** Conj_mul_SNo_Lt__37__17 TMKxcFTVDGQoSDERxzXeqPSauXeZHy9CvHp bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__37__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Hypothesis H16: SNo (u * y + z * v).
Hypothesis H18: SNo (z * y + u * v).
Theorem Conj_mul_SNo_Lt__37__17: SNo (x * w + u * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__37__17.
(** Conj_mul_SNo_Lt__38__15 TMTwLsdnjqoLgpRJp2v1VacStBVAPrEGyy3 bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__38__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H16: SNo (u * y + z * v).
Hypothesis H17: SNo (u * w + x * v).
Theorem Conj_mul_SNo_Lt__38__15: SNo (z * y + u * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__38__15.
(** Conj_mul_SNo_Lt__39__12 TMctgCSrCEZVM5vFET34N5JSrUnmWBYgtew bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__39__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Hypothesis H16: SNo (u * y + z * v).
Theorem Conj_mul_SNo_Lt__39__12: SNo (u * w + x * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__39__12.
(** Conj_mul_SNo_Lt__40__13 TMbqwNM7jKX6BcQkodHxxQjRfX5NfsgQ5yG bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__40__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Hypothesis H15: SNo (u * v + u * v).
Theorem Conj_mul_SNo_Lt__40__13: SNo (u * y + z * v) -> ((z * y + x * w) + u * v + u * v) < (x * y + z * w) + u * v + u * v.
Admitted.

End Conj_mul_SNo_Lt__40__13.
(** Conj_mul_SNo_Lt__41__1 TMKm2eAorisw6JeUukkBJNer9GGzwAtMP5G bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__41__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H2: SNo (x * w).
Hypothesis H3: SNo (z * w).
Hypothesis H4: SNo (z * y + x * w).
Hypothesis H5: SNo (x * y + z * w).
Hypothesis H6: SNo (u * y).
Hypothesis H7: SNo (u * w).
Hypothesis H8: SNo (x * v).
Hypothesis H9: SNo (z * v).
Hypothesis H10: SNo (u * v).
Hypothesis H11: (u * y + x * v) < x * y + u * v.
Hypothesis H12: (u * w + z * v) < z * w + u * v.
Hypothesis H13: (x * w + u * v) < u * w + x * v.
Hypothesis H14: (z * y + u * v) < u * y + z * v.
Theorem Conj_mul_SNo_Lt__41__1: SNo (u * v + u * v) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__41__1.
(** Conj_mul_SNo_Lt__42__12 TMaV8cE235TovDCH811xBw5neyptMNXQMFH bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__42__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoL y -> (z * y + x2 * y2) < x2 * y + z * y2)).
Hypothesis H3: SNo (x * w).
Hypothesis H4: SNo (z * w).
Hypothesis H5: SNo (z * y + x * w).
Hypothesis H6: SNo (x * y + z * w).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo (u * y).
Hypothesis H9: SNo (u * w).
Hypothesis H10: v :e SNoL y.
Hypothesis H11: SNo (x * v).
Hypothesis H13: SNo (u * v).
Hypothesis H14: (u * y + x * v) < x * y + u * v.
Hypothesis H15: (u * w + z * v) < z * w + u * v.
Hypothesis H16: (x * w + u * v) < u * w + x * v.
Theorem Conj_mul_SNo_Lt__42__12: (z * y + u * v) < u * y + z * v -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__42__12.
(** Conj_mul_SNo_Lt__44__1 TMarWgHWHQkTmPy73tiKhaP9gxa2Ko2J5oq bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__44__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H2: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoL y -> (z * y + x2 * y2) < x2 * y + z * y2)).
Hypothesis H3: SNo (x * w).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR w -> (x * w + x2 * y2) < x2 * w + x * y2)).
Hypothesis H5: SNo (z * w).
Hypothesis H6: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoR w -> (x2 * w + z * y2) < z * w + x2 * y2)).
Hypothesis H7: SNo (z * y + x * w).
Hypothesis H8: SNo (x * y + z * w).
Hypothesis H9: u :e SNoL x.
Hypothesis H10: u :e SNoR z.
Hypothesis H11: SNo (u * y).
Hypothesis H12: SNo (u * w).
Hypothesis H13: v :e SNoL y.
Hypothesis H14: v :e SNoR w.
Hypothesis H15: SNo (x * v).
Hypothesis H16: SNo (z * v).
Hypothesis H17: SNo (u * v).
Hypothesis H18: (u * y + x * v) < x * y + u * v.
Theorem Conj_mul_SNo_Lt__44__1: (u * w + z * v) < z * w + u * v -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__44__1.
(** Conj_mul_SNo_Lt__44__18 TMNmBfTK1kGpyEDdYvSXzy4b6eRqVLTpsCB bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__44__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo (x * y).
Hypothesis H1: SNo (z * y).
Hypothesis H2: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoL y -> (z * y + x2 * y2) < x2 * y + z * y2)).
Hypothesis H3: SNo (x * w).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR w -> (x * w + x2 * y2) < x2 * w + x * y2)).
Hypothesis H5: SNo (z * w).
Hypothesis H6: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoR w -> (x2 * w + z * y2) < z * w + x2 * y2)).
Hypothesis H7: SNo (z * y + x * w).
Hypothesis H8: SNo (x * y + z * w).
Hypothesis H9: u :e SNoL x.
Hypothesis H10: u :e SNoR z.
Hypothesis H11: SNo (u * y).
Hypothesis H12: SNo (u * w).
Hypothesis H13: v :e SNoL y.
Hypothesis H14: v :e SNoR w.
Hypothesis H15: SNo (x * v).
Hypothesis H16: SNo (z * v).
Hypothesis H17: SNo (u * v).
Theorem Conj_mul_SNo_Lt__44__18: (u * w + z * v) < z * w + u * v -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__44__18.
(** Conj_mul_SNo_Lt__48__2 TMWcibTE18PVDvGppPKzfoSnT4jy1GXTFUh bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__48__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL y -> (x2 * y + x * y2) < x * y + x2 * y2)).
Hypothesis H4: SNo (z * y).
Hypothesis H5: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoL y -> (z * y + x2 * y2) < x2 * y + z * y2)).
Hypothesis H6: SNo (x * w).
Hypothesis H7: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR w -> (x * w + x2 * y2) < x2 * w + x * y2)).
Hypothesis H8: SNo (z * w).
Hypothesis H9: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoR w -> (x2 * w + z * y2) < z * w + x2 * y2)).
Hypothesis H10: SNo (z * y + x * w).
Hypothesis H11: SNo (x * y + z * w).
Hypothesis H12: SNo u.
Hypothesis H13: u :e SNoL x.
Hypothesis H14: u :e SNoR z.
Hypothesis H15: SNo (u * y).
Hypothesis H16: SNo (u * w).
Hypothesis H17: SNo v.
Hypothesis H18: v :e SNoL y.
Hypothesis H19: v :e SNoR w.
Theorem Conj_mul_SNo_Lt__48__2: SNo (x * v) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__48__2.
(** Conj_mul_SNo_Lt__49__1 TML7tpJgU7asx354ehoVs16fvzJQRox2c4p bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__49__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo w.
Hypothesis H3: SNo (x * y).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL y -> (x2 * y + x * y2) < x * y + x2 * y2)).
Hypothesis H5: SNo (z * y).
Hypothesis H6: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoL y -> (z * y + x2 * y2) < x2 * y + z * y2)).
Hypothesis H7: SNo (x * w).
Hypothesis H8: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR w -> (x * w + x2 * y2) < x2 * w + x * y2)).
Hypothesis H9: SNo (z * w).
Hypothesis H10: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoR w -> (x2 * w + z * y2) < z * w + x2 * y2)).
Hypothesis H11: SNo (z * y + x * w).
Hypothesis H12: SNo (x * y + z * w).
Hypothesis H13: SNo u.
Hypothesis H14: u :e SNoL x.
Hypothesis H15: u :e SNoR z.
Hypothesis H16: SNo (u * y).
Hypothesis H17: SNo (u * w).
Hypothesis H18: SNo v.
Hypothesis H19: w < v.
Hypothesis H20: SNoLev v :e SNoLev w.
Hypothesis H21: v :e SNoL y.
Theorem Conj_mul_SNo_Lt__49__1: v :e SNoR w -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__49__1.
(** Conj_mul_SNo_Lt__49__12 TMMcV8MoX6xsdnu5dKdZ1TjjTet849b8Lgv bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__49__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo z.
Hypothesis H2: SNo w.
Hypothesis H3: SNo (x * y).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL y -> (x2 * y + x * y2) < x * y + x2 * y2)).
Hypothesis H5: SNo (z * y).
Hypothesis H6: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoL y -> (z * y + x2 * y2) < x2 * y + z * y2)).
Hypothesis H7: SNo (x * w).
Hypothesis H8: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR w -> (x * w + x2 * y2) < x2 * w + x * y2)).
Hypothesis H9: SNo (z * w).
Hypothesis H10: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoR w -> (x2 * w + z * y2) < z * w + x2 * y2)).
Hypothesis H11: SNo (z * y + x * w).
Hypothesis H13: SNo u.
Hypothesis H14: u :e SNoL x.
Hypothesis H15: u :e SNoR z.
Hypothesis H16: SNo (u * y).
Hypothesis H17: SNo (u * w).
Hypothesis H18: SNo v.
Hypothesis H19: w < v.
Hypothesis H20: SNoLev v :e SNoLev w.
Hypothesis H21: v :e SNoL y.
Theorem Conj_mul_SNo_Lt__49__12: v :e SNoR w -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__49__12.
(** Conj_mul_SNo_Lt__49__20 TMWXERb8eMLqk8KUUcmNcXrFHE9UKRtaEeS bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__49__20.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo z.
Hypothesis H2: SNo w.
Hypothesis H3: SNo (x * y).
Hypothesis H4: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL y -> (x2 * y + x * y2) < x * y + x2 * y2)).
Hypothesis H5: SNo (z * y).
Hypothesis H6: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoL y -> (z * y + x2 * y2) < x2 * y + z * y2)).
Hypothesis H7: SNo (x * w).
Hypothesis H8: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR w -> (x * w + x2 * y2) < x2 * w + x * y2)).
Hypothesis H9: SNo (z * w).
Hypothesis H10: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoR w -> (x2 * w + z * y2) < z * w + x2 * y2)).
Hypothesis H11: SNo (z * y + x * w).
Hypothesis H12: SNo (x * y + z * w).
Hypothesis H13: SNo u.
Hypothesis H14: u :e SNoL x.
Hypothesis H15: u :e SNoR z.
Hypothesis H16: SNo (u * y).
Hypothesis H17: SNo (u * w).
Hypothesis H18: SNo v.
Hypothesis H19: w < v.
Hypothesis H21: v :e SNoL y.
Theorem Conj_mul_SNo_Lt__49__20: v :e SNoR w -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__49__20.
(** Conj_mul_SNo_Lt__50__16 TMH9BPEh4SpP41578uqDdQa1YkUvb4kREoT bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__50__16.
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
Hypothesis H4: SNo (x * y).
Hypothesis H5: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL y -> (x2 * y + x * y2) < x * y + x2 * y2)).
Hypothesis H6: SNo (z * y).
Hypothesis H7: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoL y -> (z * y + x2 * y2) < x2 * y + z * y2)).
Hypothesis H8: SNo (x * w).
Hypothesis H9: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR w -> (x * w + x2 * y2) < x2 * w + x * y2)).
Hypothesis H10: SNo (z * w).
Hypothesis H11: (forall x2:set, x2 :e SNoR z -> (forall y2:set, y2 :e SNoR w -> (x2 * w + z * y2) < z * w + x2 * y2)).
Hypothesis H12: SNo (z * y + x * w).
Hypothesis H13: SNo (x * y + z * w).
Hypothesis H14: SNo u.
Hypothesis H15: u :e SNoL x.
Hypothesis H17: SNo (u * y).
Hypothesis H18: SNo (u * w).
Hypothesis H19: SNo v.
Hypothesis H20: w < v.
Hypothesis H21: v < y.
Hypothesis H22: SNoLev v :e SNoLev w.
Hypothesis H23: SNoLev v :e SNoLev y.
Theorem Conj_mul_SNo_Lt__50__16: v :e SNoL y -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__50__16.
(** Conj_mul_SNo_Lt__52__23 TMKr37tuCDts2pzu2unAyMSL81ffCtuaTXh bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__52__23.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Hypothesis H17: u :e SNoR z.
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (u * w).
Hypothesis H20: SNo (u * y + x * w).
Hypothesis H21: SNo (u * y + z * w).
Hypothesis H22: SNo (x * y + u * w).
Hypothesis H24: SNo (z * w + u * y).
Hypothesis H25: SNo (u * w + x * y).
Theorem Conj_mul_SNo_Lt__52__23: SNo (x * w + u * y) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__52__23.
(** Conj_mul_SNo_Lt__53__23 TMSJjwr8ysXu9yGDAUBsonpGRxKVocKuQLs bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__53__23.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Hypothesis H17: u :e SNoR z.
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (u * w).
Hypothesis H20: SNo (u * y + x * w).
Hypothesis H21: SNo (u * y + z * w).
Hypothesis H22: SNo (x * y + u * w).
Hypothesis H24: SNo (z * w + u * y).
Theorem Conj_mul_SNo_Lt__53__23: SNo (u * w + x * y) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__53__23.
(** Conj_mul_SNo_Lt__53__24 TMFPWZbUopHc3TdQ1J2Bes4zduTDY1dy6VZ bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__53__24.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Hypothesis H17: u :e SNoR z.
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (u * w).
Hypothesis H20: SNo (u * y + x * w).
Hypothesis H21: SNo (u * y + z * w).
Hypothesis H22: SNo (x * y + u * w).
Hypothesis H23: SNo (z * y + u * w).
Theorem Conj_mul_SNo_Lt__53__24: SNo (u * w + x * y) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__53__24.
(** Conj_mul_SNo_Lt__54__4 TMWq1y2gqkj9p9nmSYM5VHHb35BLt2KU4xj bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__54__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Hypothesis H17: u :e SNoR z.
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (u * w).
Hypothesis H20: SNo (u * y + x * w).
Hypothesis H21: SNo (u * y + z * w).
Hypothesis H22: SNo (x * y + u * w).
Hypothesis H23: SNo (z * y + u * w).
Theorem Conj_mul_SNo_Lt__54__4: SNo (z * w + u * y) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__54__4.
(** Conj_mul_SNo_Lt__54__22 TMbr6WaR47XVgTBQE5PtkpyBBQHX7tY2GRZ bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__54__22.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Hypothesis H17: u :e SNoR z.
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (u * w).
Hypothesis H20: SNo (u * y + x * w).
Hypothesis H21: SNo (u * y + z * w).
Hypothesis H23: SNo (z * y + u * w).
Theorem Conj_mul_SNo_Lt__54__22: SNo (z * w + u * y) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__54__22.
(** Conj_mul_SNo_Lt__55__12 TMVLCUjfHPDRPpXfFmXJhzCxQ8KWvLxD4o4 bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__55__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Hypothesis H17: u :e SNoR z.
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (u * w).
Hypothesis H20: SNo (u * y + x * w).
Hypothesis H21: SNo (u * y + z * w).
Hypothesis H22: SNo (x * y + u * w).
Theorem Conj_mul_SNo_Lt__55__12: SNo (z * y + u * w) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__55__12.
(** Conj_mul_SNo_Lt__55__22 TMUq9F9LLC4ufGCxfaE4goViRAVx1BpDKn1 bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__55__22.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Hypothesis H17: u :e SNoR z.
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (u * w).
Hypothesis H20: SNo (u * y + x * w).
Hypothesis H21: SNo (u * y + z * w).
Theorem Conj_mul_SNo_Lt__55__22: SNo (z * y + u * w) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__55__22.
(** Conj_mul_SNo_Lt__57__1 TMUK2hs55DdmS5maVfUxrqBQAM19SLs5jZQ bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__57__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Hypothesis H17: u :e SNoR z.
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (u * w).
Hypothesis H20: SNo (u * y + x * w).
Theorem Conj_mul_SNo_Lt__57__1: SNo (u * y + z * w) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__57__1.
(** Conj_mul_SNo_Lt__57__6 TMHzHyhJY1ERtyzVEHaaWKKsJpYDCuomeVe bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__57__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Hypothesis H17: u :e SNoR z.
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (u * w).
Hypothesis H20: SNo (u * y + x * w).
Theorem Conj_mul_SNo_Lt__57__6: SNo (u * y + z * w) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__57__6.
(** Conj_mul_SNo_Lt__57__11 TMThs7inNhfhqiohqCLqCkPeEHEfYnHdNgv bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__57__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Hypothesis H17: u :e SNoR z.
Hypothesis H18: SNo (u * y).
Hypothesis H19: SNo (u * w).
Hypothesis H20: SNo (u * y + x * w).
Theorem Conj_mul_SNo_Lt__57__11: SNo (u * y + z * w) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__57__11.
(** Conj_mul_SNo_Lt__60__17 TMPBsLcpDzeBMiXX9YTdTEPQ76fkF2YTpkT bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__60__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H14: SNo (x * y + z * w).
Hypothesis H15: SNo u.
Hypothesis H16: u :e SNoL x.
Theorem Conj_mul_SNo_Lt__60__17: SNo (u * y) -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__60__17.
(** Conj_mul_SNo_Lt__61__14 TMQLYAVwfyjCuH6gKovkR8B34Sm7pz5hYXf bounty of about 25 bars **)
Section Conj_mul_SNo_Lt__61__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: SNo w.
Hypothesis H4: w < y.
Hypothesis H5: SNo (x * y).
Hypothesis H6: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> (v * y + x * x2) < x * y + v * x2)).
Hypothesis H7: SNo (z * y).
Hypothesis H8: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoL y -> (z * y + v * x2) < v * y + z * x2)).
Hypothesis H9: SNo (x * w).
Hypothesis H10: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoR w -> (x * w + v * x2) < v * w + x * x2)).
Hypothesis H11: SNo (z * w).
Hypothesis H12: (forall v:set, v :e SNoR z -> (forall x2:set, x2 :e SNoR w -> (v * w + z * x2) < z * w + v * x2)).
Hypothesis H13: SNo (z * y + x * w).
Hypothesis H15: SNo u.
Hypothesis H16: z < u.
Hypothesis H17: SNoLev u :e SNoLev z.
Hypothesis H18: u :e SNoL x.
Theorem Conj_mul_SNo_Lt__61__14: u :e SNoR z -> (z * y + x * w) < x * y + z * w.
Admitted.

End Conj_mul_SNo_Lt__61__14.
(** Conj_mul_SNo_SNoL_interpolate__2__2 TMVAo5ZWMvLqFc9jZqdA3Sn5sTkpaRo1qQP bounty of about 25 bars **)
Section Conj_mul_SNo_SNoL_interpolate__2__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR y -> (x2 * y + x * y2) < z + x2 * y2)).
Hypothesis H4: SNo w.
Hypothesis H5: z < w.
Hypothesis H6: u :e SNoR x.
Hypothesis H7: v :e SNoR y.
Hypothesis H8: (w + u * v) <= u * y + x * v.
Hypothesis H9: SNo u.
Hypothesis H10: SNo v.
Hypothesis H11: SNo (u * v).
Theorem Conj_mul_SNo_SNoL_interpolate__2__2: (w + u * v) < z + u * v -> x * y < w.
Admitted.

End Conj_mul_SNo_SNoL_interpolate__2__2.
(** Conj_mul_SNo_SNoL_interpolate__3__1 TMXKNrjQJLhZVPesgSKot4VkdvEf1VcGtis bounty of about 25 bars **)
Section Conj_mul_SNo_SNoL_interpolate__3__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR y -> (x2 * y + x * y2) < z + x2 * y2)).
Hypothesis H4: SNo w.
Hypothesis H5: z < w.
Hypothesis H6: u :e SNoR x.
Hypothesis H7: v :e SNoR y.
Hypothesis H8: (w + u * v) <= u * y + x * v.
Hypothesis H9: SNo u.
Hypothesis H10: SNo v.
Theorem Conj_mul_SNo_SNoL_interpolate__3__1: SNo (u * v) -> x * y < w.
Admitted.

End Conj_mul_SNo_SNoL_interpolate__3__1.
(** Conj_mul_SNo_SNoL_interpolate__3__2 TMHTnDXkxhmMZHqcTRkaPapaxQ6tAWz1kFC bounty of about 25 bars **)
Section Conj_mul_SNo_SNoL_interpolate__3__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR y -> (x2 * y + x * y2) < z + x2 * y2)).
Hypothesis H4: SNo w.
Hypothesis H5: z < w.
Hypothesis H6: u :e SNoR x.
Hypothesis H7: v :e SNoR y.
Hypothesis H8: (w + u * v) <= u * y + x * v.
Hypothesis H9: SNo u.
Hypothesis H10: SNo v.
Theorem Conj_mul_SNo_SNoL_interpolate__3__2: SNo (u * v) -> x * y < w.
Admitted.

End Conj_mul_SNo_SNoL_interpolate__3__2.
(** Conj_mul_SNo_SNoL_interpolate__3__5 TMTHJ61q2mNUAPwUh9k478498hw3C9rZfAH bounty of about 25 bars **)
Section Conj_mul_SNo_SNoL_interpolate__3__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR y -> (x2 * y + x * y2) < z + x2 * y2)).
Hypothesis H4: SNo w.
Hypothesis H6: u :e SNoR x.
Hypothesis H7: v :e SNoR y.
Hypothesis H8: (w + u * v) <= u * y + x * v.
Hypothesis H9: SNo u.
Hypothesis H10: SNo v.
Theorem Conj_mul_SNo_SNoL_interpolate__3__5: SNo (u * v) -> x * y < w.
Admitted.

End Conj_mul_SNo_SNoL_interpolate__3__5.
(** Conj_mul_SNo_SNoL_interpolate__5__9 TMcAaTaV3H6diAjXiBbRqoCxFZTknJNeJ3F bounty of about 25 bars **)
Section Conj_mul_SNo_SNoL_interpolate__5__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL y -> (x2 * y + x * y2) < z + x2 * y2)).
Hypothesis H4: SNo w.
Hypothesis H5: z < w.
Hypothesis H6: u :e SNoL x.
Hypothesis H7: v :e SNoL y.
Hypothesis H8: (w + u * v) <= u * y + x * v.
Hypothesis H10: SNo v.
Hypothesis H11: SNo (u * v).
Theorem Conj_mul_SNo_SNoL_interpolate__5__9: (w + u * v) < z + u * v -> x * y < w.
Admitted.

End Conj_mul_SNo_SNoL_interpolate__5__9.
(** Conj_mul_SNo_SNoL_interpolate__7__3 TMYThaUfhYWi7j8ULQjaP3WuFToo399mUmJ bounty of about 25 bars **)
Section Conj_mul_SNo_SNoL_interpolate__7__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H4: (forall u:set, u :e SNoS_ (SNoLev z) -> SNoLev u :e SNoLev (x * y) -> u < x * y -> (exists v:set, v :e SNoL x /\ (exists x2:set, x2 :e SNoL y /\ (u + v * x2) <= v * y + x * x2)) \/ (exists v:set, v :e SNoR x /\ (exists x2:set, x2 :e SNoR y /\ (u + v * x2) <= v * y + x * x2))).
Hypothesis H5: SNoLev z :e SNoLev (x * y).
Hypothesis H6: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoL y -> (u * y + x * v) < z + u * v)).
Hypothesis H7: (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoR y -> (u * y + x * v) < z + u * v)).
Hypothesis H8: SNo w.
Hypothesis H9: SNoLev w :e SNoLev z.
Hypothesis H10: z < w.
Hypothesis H11: w < x * y.
Theorem Conj_mul_SNo_SNoL_interpolate__7__3: (exists u:set, u :e SNoL x /\ (exists v:set, v :e SNoL y /\ (w + u * v) <= u * y + x * v)) \/ (exists u:set, u :e SNoR x /\ (exists v:set, v :e SNoR y /\ (w + u * v) <= u * y + x * v)) -> x * y < w.
Admitted.

End Conj_mul_SNo_SNoL_interpolate__7__3.
(** Conj_mul_SNo_SNoL_interpolate__8__1 TMMLhZJbXGaEPxjZrJHX6DXHPi4oJMypbSW bounty of about 25 bars **)
Section Conj_mul_SNo_SNoL_interpolate__8__1.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo z.
Hypothesis H4: (forall w:set, w :e SNoS_ (SNoLev z) -> SNoLev w :e SNoLev (x * y) -> w < x * y -> (exists u:set, u :e SNoL x /\ (exists v:set, v :e SNoL y /\ (w + u * v) <= u * y + x * v)) \/ (exists u:set, u :e SNoR x /\ (exists v:set, v :e SNoR y /\ (w + u * v) <= u * y + x * v))).
Hypothesis H5: SNoLev z :e SNoLev (x * y).
Hypothesis H6: z < x * y.
Hypothesis H7: ~ ((exists w:set, w :e SNoL x /\ (exists u:set, u :e SNoL y /\ (z + w * u) <= w * y + x * u)) \/ (exists w:set, w :e SNoR x /\ (exists u:set, u :e SNoR y /\ (z + w * u) <= w * y + x * u))).
Hypothesis H8: (forall w:set, w :e SNoL x -> (forall u:set, u :e SNoL y -> (w * y + x * u) < z + w * u)).
Theorem Conj_mul_SNo_SNoL_interpolate__8__1: ~ (forall w:set, w :e SNoR x -> (forall u:set, u :e SNoR y -> (w * y + x * u) < z + w * u)).
Admitted.

End Conj_mul_SNo_SNoL_interpolate__8__1.
(** Conj_mul_SNo_SNoL_interpolate__9__4 TMYRPdKdbZhUiknHS6qmv9PKXmDTFut2jz3 bounty of about 25 bars **)
Section Conj_mul_SNo_SNoL_interpolate__9__4.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H3: SNo z.
Hypothesis H5: SNoLev z :e SNoLev (x * y).
Hypothesis H6: z < x * y.
Hypothesis H7: ~ ((exists w:set, w :e SNoL x /\ (exists u:set, u :e SNoL y /\ (z + w * u) <= w * y + x * u)) \/ (exists w:set, w :e SNoR x /\ (exists u:set, u :e SNoR y /\ (z + w * u) <= w * y + x * u))).
Theorem Conj_mul_SNo_SNoL_interpolate__9__4: ~ (forall w:set, w :e SNoL x -> (forall u:set, u :e SNoL y -> (w * y + x * u) < z + w * u)).
Admitted.

End Conj_mul_SNo_SNoL_interpolate__9__4.
(** Conj_mul_SNo_SNoL_interpolate__11__0 TMYpZAftBM1Y86VtuXn7zSxUkXbrXf5LFrL bounty of about 25 bars **)
Section Conj_mul_SNo_SNoL_interpolate__11__0.
Variable x:set.
Variable y:set.
Hypothesis H1: SNo y.
Theorem Conj_mul_SNo_SNoL_interpolate__11__0: SNo (x * y) -> (forall z:set, z :e SNoL (x * y) -> (exists w:set, w :e SNoL x /\ (exists u:set, u :e SNoL y /\ (z + w * u) <= w * y + x * u)) \/ (exists w:set, w :e SNoR x /\ (exists u:set, u :e SNoR y /\ (z + w * u) <= w * y + x * u))).
Admitted.

End Conj_mul_SNo_SNoL_interpolate__11__0.
(** Conj_mul_SNo_SNoR_interpolate__1__3 TMTW3d62qPEXJRDbjEhWrPo2VjqLBnT9wyH bounty of about 25 bars **)
Section Conj_mul_SNo_SNoR_interpolate__1__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo z.
Hypothesis H1: SNo w.
Hypothesis H2: w < z.
Hypothesis H4: (z + u * v) < w + u * v.
Theorem Conj_mul_SNo_SNoR_interpolate__1__3: z < w -> w < x * y.
Admitted.

End Conj_mul_SNo_SNoR_interpolate__1__3.
(** Conj_mul_SNo_SNoR_interpolate__3__1 TMGJ7YT7JCpjHMUNfiMFirSniXjTzj58jCE bounty of about 25 bars **)
Section Conj_mul_SNo_SNoR_interpolate__3__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL y -> (z + x2 * y2) < x2 * y + x * y2)).
Hypothesis H4: SNo w.
Hypothesis H5: w < z.
Hypothesis H6: u :e SNoR x.
Hypothesis H7: v :e SNoL y.
Hypothesis H8: (u * y + x * v) <= w + u * v.
Hypothesis H9: SNo u.
Hypothesis H10: SNo v.
Theorem Conj_mul_SNo_SNoR_interpolate__3__1: SNo (u * v) -> w < x * y.
Admitted.

End Conj_mul_SNo_SNoR_interpolate__3__1.
(** Conj_mul_SNo_SNoR_interpolate__3__8 TMKCe66ZKMpabiCDcttkP56VezaV4ytgTai bounty of about 25 bars **)
Section Conj_mul_SNo_SNoR_interpolate__3__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL y -> (z + x2 * y2) < x2 * y + x * y2)).
Hypothesis H4: SNo w.
Hypothesis H5: w < z.
Hypothesis H6: u :e SNoR x.
Hypothesis H7: v :e SNoL y.
Hypothesis H9: SNo u.
Hypothesis H10: SNo v.
Theorem Conj_mul_SNo_SNoR_interpolate__3__8: SNo (u * v) -> w < x * y.
Admitted.

End Conj_mul_SNo_SNoR_interpolate__3__8.
(** Conj_mul_SNo_SNoR_interpolate__4__3 TMTW3d62qPEXJRDbjEhWrPo2VjqLBnT9wyH bounty of about 25 bars **)
Section Conj_mul_SNo_SNoR_interpolate__4__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo z.
Hypothesis H1: SNo w.
Hypothesis H2: w < z.
Hypothesis H4: (z + u * v) < w + u * v.
Theorem Conj_mul_SNo_SNoR_interpolate__4__3: z < w -> w < x * y.
Admitted.

End Conj_mul_SNo_SNoR_interpolate__4__3.
(** Conj_mul_SNo_SNoR_interpolate__6__4 TMSdXhaLYDDfeQTgWG5cbwWGmaGMp1ZvAL4 bounty of about 25 bars **)
Section Conj_mul_SNo_SNoR_interpolate__6__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR y -> (z + x2 * y2) < x2 * y + x * y2)).
Hypothesis H5: w < z.
Hypothesis H6: u :e SNoL x.
Hypothesis H7: v :e SNoR y.
Hypothesis H8: (u * y + x * v) <= w + u * v.
Hypothesis H9: SNo u.
Hypothesis H10: SNo v.
Theorem Conj_mul_SNo_SNoR_interpolate__6__4: SNo (u * v) -> w < x * y.
Admitted.

End Conj_mul_SNo_SNoR_interpolate__6__4.
(** Conj_mul_SNo_SNoR_interpolate__7__3 TMXVhXyGsXGLDb8MGn2yuenoebtuYChchYH bounty of about 25 bars **)
Section Conj_mul_SNo_SNoR_interpolate__7__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo (x * y).
Hypothesis H4: (forall u:set, u :e SNoS_ (SNoLev z) -> SNoLev u :e SNoLev (x * y) -> x * y < u -> (exists v:set, v :e SNoL x /\ (exists x2:set, x2 :e SNoR y /\ (v * y + x * x2) <= u + v * x2)) \/ (exists v:set, v :e SNoR x /\ (exists x2:set, x2 :e SNoL y /\ (v * y + x * x2) <= u + v * x2))).
Hypothesis H5: SNoLev z :e SNoLev (x * y).
Hypothesis H6: (forall u:set, u :e SNoL x -> (forall v:set, v :e SNoR y -> (z + u * v) < u * y + x * v)).
Hypothesis H7: (forall u:set, u :e SNoR x -> (forall v:set, v :e SNoL y -> (z + u * v) < u * y + x * v)).
Hypothesis H8: SNo w.
Hypothesis H9: SNoLev w :e SNoLev z.
Hypothesis H10: w < z.
Hypothesis H11: x * y < w.
Theorem Conj_mul_SNo_SNoR_interpolate__7__3: (exists u:set, u :e SNoL x /\ (exists v:set, v :e SNoR y /\ (u * y + x * v) <= w + u * v)) \/ (exists u:set, u :e SNoR x /\ (exists v:set, v :e SNoL y /\ (u * y + x * v) <= w + u * v)) -> w < x * y.
Admitted.

End Conj_mul_SNo_SNoR_interpolate__7__3.
(** Conj_mul_SNo_SNoR_interpolate__8__2 TMZeuFaoPT4P9adgbZz1UNoxhEq4Pa3WfzE bounty of about 25 bars **)
Section Conj_mul_SNo_SNoR_interpolate__8__2.
Variable x:set.
Variable y:set.
Variable z:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: SNo z.
Hypothesis H4: (forall w:set, w :e SNoS_ (SNoLev z) -> SNoLev w :e SNoLev (x * y) -> x * y < w -> (exists u:set, u :e SNoL x /\ (exists v:set, v :e SNoR y /\ (u * y + x * v) <= w + u * v)) \/ (exists u:set, u :e SNoR x /\ (exists v:set, v :e SNoL y /\ (u * y + x * v) <= w + u * v))).
Hypothesis H5: SNoLev z :e SNoLev (x * y).
Hypothesis H6: x * y < z.
Hypothesis H7: ~ ((exists w:set, w :e SNoL x /\ (exists u:set, u :e SNoR y /\ (w * y + x * u) <= z + w * u)) \/ (exists w:set, w :e SNoR x /\ (exists u:set, u :e SNoL y /\ (w * y + x * u) <= z + w * u))).
Hypothesis H8: (forall w:set, w :e SNoL x -> (forall u:set, u :e SNoR y -> (z + w * u) < w * y + x * u)).
Theorem Conj_mul_SNo_SNoR_interpolate__8__2: ~ (forall w:set, w :e SNoR x -> (forall u:set, u :e SNoL y -> (z + w * u) < w * y + x * u)).
Admitted.

End Conj_mul_SNo_SNoR_interpolate__8__2.
(** Conj_mul_SNo_oneR__3__0 TMFB5yf5a9bzsSVSHhCx8mPBPvPQkR4AvXY bounty of about 25 bars **)
Section Conj_mul_SNo_oneR__3__0.
Variable x:set.
Variable y:set.
Hypothesis H1: (forall z:set, z :e SNoL x -> (forall w:set, w :e SNoL (ordsucc Empty) -> (z * ordsucc Empty + x * w) < x * ordsucc Empty + z * w)).
Hypothesis H2: Empty :e SNoL (ordsucc Empty).
Hypothesis H3: y :e SNoL x.
Hypothesis H4: SNo y.
Hypothesis H5: y * ordsucc Empty + x * Empty = y.
Theorem Conj_mul_SNo_oneR__3__0: x * ordsucc Empty + y * Empty = x * ordsucc Empty -> y < x * ordsucc Empty.
Admitted.

End Conj_mul_SNo_oneR__3__0.
(** Conj_mul_SNo_com__1__0 TMMWSnpFz5mJNhwYF4osH1UqKFrztVXEe9V bounty of about 25 bars **)
Section Conj_mul_SNo_com__1__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: SNo y.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> x2 * y = y * x2).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> x * x2 = x2 * x).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x2 * y2 = y2 * x2)).
Hypothesis H5: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR y -> x2 * y + x * y2 + - (x2 * y2) :e w)).
Hypothesis H7: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL y -> x2 * y + x * y2 + - (x2 * y2) :e w)).
Hypothesis H8: (forall x2:set, x2 :e v -> (forall P:prop, (forall y2:set, y2 :e SNoL y -> (forall z2:set, z2 :e SNoR x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR y -> (forall z2:set, z2 :e SNoL x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H9: (forall x2:set, x2 :e SNoL y -> (forall y2:set, y2 :e SNoR x -> x2 * x + y * y2 + - (x2 * y2) :e v)).
Hypothesis H10: (forall x2:set, x2 :e SNoR y -> (forall y2:set, y2 :e SNoL x -> x2 * x + y * y2 + - (x2 * y2) :e v)).
Hypothesis H11: z = u.
Theorem Conj_mul_SNo_com__1__0: w = v -> SNoCut z w = SNoCut u v.
Admitted.

End Conj_mul_SNo_com__1__0.
(** Conj_mul_SNo_com__2__5 TMQBn2Vmh5519uKLgvALG1RLir74uKm6kNN bounty of about 25 bars **)
Section Conj_mul_SNo_com__2__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> x2 * y = y * x2).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> x * x2 = x2 * x).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x2 * y2 = y2 * x2)).
Hypothesis H6: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL y -> x2 * y + x * y2 + - (x2 * y2) :e z)).
Hypothesis H7: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR y -> x2 * y + x * y2 + - (x2 * y2) :e z)).
Hypothesis H8: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H9: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR y -> x2 * y + x * y2 + - (x2 * y2) :e w)).
Hypothesis H10: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL y -> x2 * y + x * y2 + - (x2 * y2) :e w)).
Hypothesis H11: (forall x2:set, x2 :e u -> (forall P:prop, (forall y2:set, y2 :e SNoL y -> (forall z2:set, z2 :e SNoL x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR y -> (forall z2:set, z2 :e SNoR x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: (forall x2:set, x2 :e SNoL y -> (forall y2:set, y2 :e SNoL x -> x2 * x + y * y2 + - (x2 * y2) :e u)).
Hypothesis H13: (forall x2:set, x2 :e SNoR y -> (forall y2:set, y2 :e SNoR x -> x2 * x + y * y2 + - (x2 * y2) :e u)).
Hypothesis H14: (forall x2:set, x2 :e v -> (forall P:prop, (forall y2:set, y2 :e SNoL y -> (forall z2:set, z2 :e SNoR x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR y -> (forall z2:set, z2 :e SNoL x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H15: (forall x2:set, x2 :e SNoL y -> (forall y2:set, y2 :e SNoR x -> x2 * x + y * y2 + - (x2 * y2) :e v)).
Hypothesis H16: (forall x2:set, x2 :e SNoR y -> (forall y2:set, y2 :e SNoL x -> x2 * x + y * y2 + - (x2 * y2) :e v)).
Theorem Conj_mul_SNo_com__2__5: z = u -> SNoCut z w = SNoCut u v.
Admitted.

End Conj_mul_SNo_com__2__5.
(** Conj_mul_SNo_com__2__9 TMXzBz7GFYvBMLPG62PoH8ymNGTBA1uUE5b bounty of about 25 bars **)
Section Conj_mul_SNo_com__2__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> x2 * y = y * x2).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> x * x2 = x2 * x).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x2 * y2 = y2 * x2)).
Hypothesis H5: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL y -> x2 * y + x * y2 + - (x2 * y2) :e z)).
Hypothesis H7: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR y -> x2 * y + x * y2 + - (x2 * y2) :e z)).
Hypothesis H8: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H10: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL y -> x2 * y + x * y2 + - (x2 * y2) :e w)).
Hypothesis H11: (forall x2:set, x2 :e u -> (forall P:prop, (forall y2:set, y2 :e SNoL y -> (forall z2:set, z2 :e SNoL x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR y -> (forall z2:set, z2 :e SNoR x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: (forall x2:set, x2 :e SNoL y -> (forall y2:set, y2 :e SNoL x -> x2 * x + y * y2 + - (x2 * y2) :e u)).
Hypothesis H13: (forall x2:set, x2 :e SNoR y -> (forall y2:set, y2 :e SNoR x -> x2 * x + y * y2 + - (x2 * y2) :e u)).
Hypothesis H14: (forall x2:set, x2 :e v -> (forall P:prop, (forall y2:set, y2 :e SNoL y -> (forall z2:set, z2 :e SNoR x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR y -> (forall z2:set, z2 :e SNoL x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H15: (forall x2:set, x2 :e SNoL y -> (forall y2:set, y2 :e SNoR x -> x2 * x + y * y2 + - (x2 * y2) :e v)).
Hypothesis H16: (forall x2:set, x2 :e SNoR y -> (forall y2:set, y2 :e SNoL x -> x2 * x + y * y2 + - (x2 * y2) :e v)).
Theorem Conj_mul_SNo_com__2__9: z = u -> SNoCut z w = SNoCut u v.
Admitted.

End Conj_mul_SNo_com__2__9.
(** Conj_mul_SNo_com__2__11 TMUdwb2A7HxFGAMvBzeMdz85SUezBqpZWx3 bounty of about 25 bars **)
Section Conj_mul_SNo_com__2__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> x2 * y = y * x2).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> x * x2 = x2 * x).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x2 * y2 = y2 * x2)).
Hypothesis H5: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL y -> x2 * y + x * y2 + - (x2 * y2) :e z)).
Hypothesis H7: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR y -> x2 * y + x * y2 + - (x2 * y2) :e z)).
Hypothesis H8: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H9: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR y -> x2 * y + x * y2 + - (x2 * y2) :e w)).
Hypothesis H10: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL y -> x2 * y + x * y2 + - (x2 * y2) :e w)).
Hypothesis H12: (forall x2:set, x2 :e SNoL y -> (forall y2:set, y2 :e SNoL x -> x2 * x + y * y2 + - (x2 * y2) :e u)).
Hypothesis H13: (forall x2:set, x2 :e SNoR y -> (forall y2:set, y2 :e SNoR x -> x2 * x + y * y2 + - (x2 * y2) :e u)).
Hypothesis H14: (forall x2:set, x2 :e v -> (forall P:prop, (forall y2:set, y2 :e SNoL y -> (forall z2:set, z2 :e SNoR x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR y -> (forall z2:set, z2 :e SNoL x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H15: (forall x2:set, x2 :e SNoL y -> (forall y2:set, y2 :e SNoR x -> x2 * x + y * y2 + - (x2 * y2) :e v)).
Hypothesis H16: (forall x2:set, x2 :e SNoR y -> (forall y2:set, y2 :e SNoL x -> x2 * x + y * y2 + - (x2 * y2) :e v)).
Theorem Conj_mul_SNo_com__2__11: z = u -> SNoCut z w = SNoCut u v.
Admitted.

End Conj_mul_SNo_com__2__11.
(** Conj_mul_SNo_com__2__14 TMW92VQFJRVgNVRwkSTXVPYCVu56UJc1hDA bounty of about 25 bars **)
Section Conj_mul_SNo_com__2__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> x2 * y = y * x2).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> x * x2 = x2 * x).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> x2 * y2 = y2 * x2)).
Hypothesis H5: (forall x2:set, x2 :e z -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H6: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoL y -> x2 * y + x * y2 + - (x2 * y2) :e z)).
Hypothesis H7: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoR y -> x2 * y + x * y2 + - (x2 * y2) :e z)).
Hypothesis H8: (forall x2:set, x2 :e w -> (forall P:prop, (forall y2:set, y2 :e SNoL x -> (forall z2:set, z2 :e SNoR y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR x -> (forall z2:set, z2 :e SNoL y -> x2 = y2 * y + x * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H9: (forall x2:set, x2 :e SNoL x -> (forall y2:set, y2 :e SNoR y -> x2 * y + x * y2 + - (x2 * y2) :e w)).
Hypothesis H10: (forall x2:set, x2 :e SNoR x -> (forall y2:set, y2 :e SNoL y -> x2 * y + x * y2 + - (x2 * y2) :e w)).
Hypothesis H11: (forall x2:set, x2 :e u -> (forall P:prop, (forall y2:set, y2 :e SNoL y -> (forall z2:set, z2 :e SNoL x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> (forall y2:set, y2 :e SNoR y -> (forall z2:set, z2 :e SNoR x -> x2 = y2 * x + y * z2 + - (y2 * z2) -> P)) -> P)).
Hypothesis H12: (forall x2:set, x2 :e SNoL y -> (forall y2:set, y2 :e SNoL x -> x2 * x + y * y2 + - (x2 * y2) :e u)).
Hypothesis H13: (forall x2:set, x2 :e SNoR y -> (forall y2:set, y2 :e SNoR x -> x2 * x + y * y2 + - (x2 * y2) :e u)).
Hypothesis H15: (forall x2:set, x2 :e SNoL y -> (forall y2:set, y2 :e SNoR x -> x2 * x + y * y2 + - (x2 * y2) :e v)).
Hypothesis H16: (forall x2:set, x2 :e SNoR y -> (forall y2:set, y2 :e SNoL x -> x2 * x + y * y2 + - (x2 * y2) :e v)).
Theorem Conj_mul_SNo_com__2__14: z = u -> SNoCut z w = SNoCut u v.
Admitted.

End Conj_mul_SNo_com__2__14.
(** Conj_mul_SNo_minus_distrL__2__12 TMEuc4utY3sCFs4zY5edG8aHEUqzqmWAkNW bounty of about 25 bars **)
Section Conj_mul_SNo_minus_distrL__2__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> - x2 * y = - (x2 * y)).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> - x * x2 = - (x * x2)).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> - x2 * y2 = - (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoL (- x) -> (forall y2:set, y2 :e SNoR y -> x2 * y + - x * y2 + - (x2 * y2) :e z)).
Hypothesis H6: u :e SNoR x.
Hypothesis H7: v :e SNoR y.
Hypothesis H8: w = u * y + x * v + - (u * v).
Hypothesis H9: SNo u.
Hypothesis H10: SNoLev u :e SNoLev x.
Hypothesis H11: x < u.
Hypothesis H13: SNo (- u).
Theorem Conj_mul_SNo_minus_distrL__2__12: - u :e SNoL (- x) -> - w :e z.
Admitted.

End Conj_mul_SNo_minus_distrL__2__12.
(** Conj_mul_SNo_minus_distrL__4__7 TMMZ866TgcntfrQnfcE1aV3fQRbFoZxXnXL bounty of about 25 bars **)
Section Conj_mul_SNo_minus_distrL__4__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> - x2 * y = - (x2 * y)).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> - x * x2 = - (x * x2)).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> - x2 * y2 = - (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR (- x) -> (forall y2:set, y2 :e SNoL y -> x2 * y + - x * y2 + - (x2 * y2) :e z)).
Hypothesis H6: u :e SNoL x.
Hypothesis H8: w = u * y + x * v + - (u * v).
Hypothesis H9: SNo u.
Hypothesis H10: SNo v.
Hypothesis H11: - u :e SNoR (- x).
Theorem Conj_mul_SNo_minus_distrL__4__7: - w = - u * y + - x * v + - (- u * v) -> - w :e z.
Admitted.

End Conj_mul_SNo_minus_distrL__4__7.
(** Conj_mul_SNo_minus_distrL__5__1 TMYB24ggbKYc7vT31MvKD1avEN6jGZGsgbp bounty of about 25 bars **)
Section Conj_mul_SNo_minus_distrL__5__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> - x2 * y = - (x2 * y)).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> - x * x2 = - (x * x2)).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> - x2 * y2 = - (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR (- x) -> (forall y2:set, y2 :e SNoL y -> x2 * y + - x * y2 + - (x2 * y2) :e z)).
Hypothesis H6: u :e SNoL x.
Hypothesis H7: v :e SNoL y.
Hypothesis H8: w = u * y + x * v + - (u * v).
Hypothesis H9: SNo u.
Hypothesis H10: SNoLev u :e SNoLev x.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Hypothesis H13: SNo (- u).
Theorem Conj_mul_SNo_minus_distrL__5__1: - u :e SNoR (- x) -> - w :e z.
Admitted.

End Conj_mul_SNo_minus_distrL__5__1.
(** Conj_mul_SNo_minus_distrL__9__0 TMcb5AsUczGPnddJ5Rugfq8T6dxRuzhKKs5 bounty of about 25 bars **)
Section Conj_mul_SNo_minus_distrL__9__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H1: SNo y.
Hypothesis H2: (forall v:set, v :e SNoS_ (SNoLev x) -> - v * y = - (v * y)).
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev y) -> - x * v = - (x * v)).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> - v * x2 = - (v * x2))).
Hypothesis H5: (forall v:set, v :e SNoL x -> (forall x2:set, x2 :e SNoL y -> v * y + x * x2 + - (v * x2) :e z)).
Hypothesis H6: u :e SNoL y.
Hypothesis H7: SNo w.
Hypothesis H8: SNoLev w :e SNoLev (- x).
Hypothesis H9: - x < w.
Hypothesis H10: SNo u.
Theorem Conj_mul_SNo_minus_distrL__9__0: SNo (- w) -> w * y + - x * u + - (w * u) :e Repl z minus_SNo.
Admitted.

End Conj_mul_SNo_minus_distrL__9__0.
(** Conj_mul_SNo_minus_distrL__15__11 TMKFZcuy6dZKmXM9DjVgWxfjLXrBwU8toPP bounty of about 25 bars **)
Section Conj_mul_SNo_minus_distrL__15__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> - x2 * y = - (x2 * y)).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> - x * x2 = - (x * x2)).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> - x2 * y2 = - (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoL (- x) -> (forall y2:set, y2 :e SNoL y -> x2 * y + - x * y2 + - (x2 * y2) :e z)).
Hypothesis H6: u :e SNoR x.
Hypothesis H7: v :e SNoL y.
Hypothesis H8: w = u * y + x * v + - (u * v).
Hypothesis H9: SNo u.
Hypothesis H10: SNoLev u :e SNoLev x.
Hypothesis H12: SNo v.
Theorem Conj_mul_SNo_minus_distrL__15__11: SNo (- u) -> - w :e z.
Admitted.

End Conj_mul_SNo_minus_distrL__15__11.
(** Conj_mul_SNo_minus_distrL__18__8 TMQxAaFM64wyeSLR7B2RG8MhUvJvhfuGpFS bounty of about 25 bars **)
Section Conj_mul_SNo_minus_distrL__18__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> - x2 * y = - (x2 * y)).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> - x * x2 = - (x * x2)).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> - x2 * y2 = - (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR (- x) -> (forall y2:set, y2 :e SNoR y -> x2 * y + - x * y2 + - (x2 * y2) :e z)).
Hypothesis H6: u :e SNoL x.
Hypothesis H7: v :e SNoR y.
Hypothesis H9: SNo u.
Hypothesis H10: SNoLev u :e SNoLev x.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Theorem Conj_mul_SNo_minus_distrL__18__8: SNo (- u) -> - w :e z.
Admitted.

End Conj_mul_SNo_minus_distrL__18__8.
(** Conj_mul_SNo_minus_distrL__18__10 TMKAHt92bfoRAcp3VWJ2TLjVhUgbaxYBJaX bounty of about 25 bars **)
Section Conj_mul_SNo_minus_distrL__18__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> - x2 * y = - (x2 * y)).
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> - x * x2 = - (x * x2)).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev y) -> - x2 * y2 = - (x2 * y2))).
Hypothesis H5: (forall x2:set, x2 :e SNoR (- x) -> (forall y2:set, y2 :e SNoR y -> x2 * y + - x * y2 + - (x2 * y2) :e z)).
Hypothesis H6: u :e SNoL x.
Hypothesis H7: v :e SNoR y.
Hypothesis H8: w = u * y + x * v + - (u * v).
Hypothesis H9: SNo u.
Hypothesis H11: u < x.
Hypothesis H12: SNo v.
Theorem Conj_mul_SNo_minus_distrL__18__10: SNo (- u) -> - w :e z.
Admitted.

End Conj_mul_SNo_minus_distrL__18__10.
(** Conj_mul_SNo_minus_distrL__19__5 TMbMyDKcru4qMnGZodvvSAUZMssyJhm5Tqf bounty of about 25 bars **)
Section Conj_mul_SNo_minus_distrL__19__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall v:set, v :e SNoS_ (SNoLev x) -> - v * y = - (v * y)).
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev y) -> - x * v = - (x * v)).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> - v * x2 = - (v * x2))).
Hypothesis H6: u :e SNoR y.
Hypothesis H7: SNo w.
Hypothesis H8: SNo u.
Hypothesis H9: SNo (- w).
Hypothesis H10: - w :e SNoL x.
Theorem Conj_mul_SNo_minus_distrL__19__5: w * y + - x * u + - (w * u) = - (- w * y + x * u + - (- w * u)) -> w * y + - x * u + - (w * u) :e Repl z minus_SNo.
Admitted.

End Conj_mul_SNo_minus_distrL__19__5.
(** Conj_mul_SNo_minus_distrL__22__7 TMH8okuPDoASFJE1vY5pm2ws9K5VsGbvkbJ bounty of about 25 bars **)
Section Conj_mul_SNo_minus_distrL__22__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: (forall v:set, v :e SNoS_ (SNoLev x) -> - v * y = - (v * y)).
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev y) -> - x * v = - (x * v)).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev y) -> - v * x2 = - (v * x2))).
Hypothesis H5: (forall v:set, v :e SNoR x -> (forall x2:set, x2 :e SNoL y -> v * y + x * x2 + - (v * x2) :e z)).
Hypothesis H6: u :e SNoL y.
Hypothesis H8: SNo u.
Hypothesis H9: SNo (- w).
Hypothesis H10: - w :e SNoR x.
Theorem Conj_mul_SNo_minus_distrL__22__7: w * y + - x * u + - (w * u) = - (- w * y + x * u + - (- w * u)) -> w * y + - x * u + - (w * u) :e Repl z minus_SNo.
Admitted.

End Conj_mul_SNo_minus_distrL__22__7.
(** Conj_mul_SNo_minus_distrL__26__0 TMNdi4TQGs861uU8DhP7Da8HDTnpKXc8CZv bounty of about 25 bars **)
Section Conj_mul_SNo_minus_distrL__26__0.
Variable x:set.
Variable y:set.
Hypothesis H1: SNo y.
Hypothesis H2: (forall z:set, z :e SNoS_ (SNoLev x) -> - z * y = - (z * y)).
Hypothesis H3: (forall z:set, z :e SNoS_ (SNoLev y) -> - x * z = - (x * z)).
Hypothesis H4: (forall z:set, z :e SNoS_ (SNoLev x) -> (forall w:set, w :e SNoS_ (SNoLev y) -> - z * w = - (z * w))).
Theorem Conj_mul_SNo_minus_distrL__26__0: SNo (- x) -> - x * y = - (x * y).
Admitted.

End Conj_mul_SNo_minus_distrL__26__0.
(** Conj_mul_SNo_distrR__1__23 TMU94X5sAr9MxqwdNdm78WufsjbLhU6Cdjt bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__1__23.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H24: SNo (w + x * z).
Hypothesis H25: SNo (u * v + x * v).
Theorem Conj_mul_SNo_distrR__1__23: SNo (u * z + x * v) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__1__23.
(** Conj_mul_SNo_distrR__2__24 TMazBgPHPKjJzQA3vqJioPNAgeisrBBs99q bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__2__24.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Theorem Conj_mul_SNo_distrR__2__24: SNo (u * v + x * v) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__2__24.
(** Conj_mul_SNo_distrR__6__9 TMNSZr3oLFcDZDhoLhoTNCbFXyrUmHn8Gjb bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__6__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Theorem Conj_mul_SNo_distrR__6__9: SNo (u * z) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__6__9.
(** Conj_mul_SNo_distrR__6__16 TMLF1gTdLcJZPkJ1EbpYUrhXPfzyCF5hLD6 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__6__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Theorem Conj_mul_SNo_distrR__6__16: SNo (u * z) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__6__16.
(** Conj_mul_SNo_distrR__6__19 TMdxxHpALSLaGmxwazURBagYrm8Wg6Du7Yb bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__6__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H20: SNo ((x + y) * v).
Theorem Conj_mul_SNo_distrR__6__19: SNo (u * z) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__6__19.
(** Conj_mul_SNo_distrR__6__20 TMLLNWir96k4Kmo3V5RG9qHaPs6p4VpTM94 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__6__20.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Theorem Conj_mul_SNo_distrR__6__20: SNo (u * z) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__6__20.
(** Conj_mul_SNo_distrR__10__4 TMVSjGET2zA9sdLvsn5y86PffrT8JuvbfDN bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__10__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Theorem Conj_mul_SNo_distrR__10__4: SNo (u * v) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__10__4.
(** Conj_mul_SNo_distrR__13__1 TMTEhWgawfBdy8XFKt6VMfc7apPZs2QEu7h bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__13__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Theorem Conj_mul_SNo_distrR__13__1: SNo (y * v) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__13__1.
(** Conj_mul_SNo_distrR__14__14 TMUq3koYdevu92BHQdKyTBrY49UCyUowryc bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__14__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Theorem Conj_mul_SNo_distrR__14__14: SNo (x * v) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__14__14.
(** Conj_mul_SNo_distrR__15__1 TMGGJsJaGiRqTZ6wifDKMkdsnqS3WZbin1Q bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__15__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Theorem Conj_mul_SNo_distrR__15__1: SNo (u * z) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__15__1.
(** Conj_mul_SNo_distrR__16__5 TMXFv64KLyKReDZqYSUDqEygAh9yGBYAes4 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__16__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Theorem Conj_mul_SNo_distrR__16__5: SNo ((x + y) * v) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__16__5.
(** Conj_mul_SNo_distrR__16__14 TMbHYN5Jyo2XmG5ayyk39C3mLQ5yx4SnMrt bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__16__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Theorem Conj_mul_SNo_distrR__16__14: SNo ((x + y) * v) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__16__14.
(** Conj_mul_SNo_distrR__17__1 TMPuETwoonChvvNss6d9kC6fwcTSjz7ypHe bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__17__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Theorem Conj_mul_SNo_distrR__17__1: SNo (w + u * v) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__17__1.
(** Conj_mul_SNo_distrR__17__2 TMdLKZsNUGogTgW6KRAyLXttmcRqbKHwvE7 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__17__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Theorem Conj_mul_SNo_distrR__17__2: SNo (w + u * v) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__17__2.
(** Conj_mul_SNo_distrR__17__11 TMVze8iNfeViJfn7XUDSgPbCFnLZoiPXyzt bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__17__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H12: (u * z + y * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Theorem Conj_mul_SNo_distrR__17__11: SNo (w + u * v) -> (x + y) * z < w + x * z.
Admitted.

End Conj_mul_SNo_distrR__17__11.
(** Conj_mul_SNo_distrR__20__1 TMdYru46QWaaihpFFYaDqdod8143ZaBkFhY bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__20__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + y * z).
Theorem Conj_mul_SNo_distrR__20__1: SNo (u * v + y * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__20__1.
(** Conj_mul_SNo_distrR__20__2 TMLRWDXYDhEao3t4zgcFWBKsNTmeQUPTCYp bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__20__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + y * z).
Theorem Conj_mul_SNo_distrR__20__2: SNo (u * v + y * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__20__2.
(** Conj_mul_SNo_distrR__20__6 TMXQrkec7a2mNMJsBS6wbQz7s35Y21L1PUv bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__20__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + y * z).
Theorem Conj_mul_SNo_distrR__20__6: SNo (u * v + y * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__20__6.
(** Conj_mul_SNo_distrR__20__20 TMTgvx3t4CMs73L8K3uzWULzs6SS4HYMWCy bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__20__20.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + y * z).
Theorem Conj_mul_SNo_distrR__20__20: SNo (u * v + y * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__20__20.
(** Conj_mul_SNo_distrR__25__5 TMHjsjSLG3qcx6wNuMp7VRxUdWLqpmYjoYV bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__25__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Theorem Conj_mul_SNo_distrR__25__5: SNo ((x + y) * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__25__5.
(** Conj_mul_SNo_distrR__27__13 TMJBVG5EHRU5e6vemxeuy2J8D5bHuxYobns bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__27__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Theorem Conj_mul_SNo_distrR__27__13: SNo (u + y) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__27__13.
(** Conj_mul_SNo_distrR__27__16 TMb3G8kqeGB5A4xTUwNvQtAsyhpDPi3Z7Va bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__27__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H17: SNo (u * v).
Theorem Conj_mul_SNo_distrR__27__16: SNo (u + y) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__27__16.
(** Conj_mul_SNo_distrR__29__11 TMQsqQRVLYSr2WFnLC5ASCoxyckBKaMzWQC bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__29__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + y * z).
Hypothesis H25: SNo (u * v + y * v).
Theorem Conj_mul_SNo_distrR__29__11: SNo (u * z + x * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__29__11.
(** Conj_mul_SNo_distrR__30__18 TMK2jdeA3NkuqpWLuEZFmRPtpKycPqS79mL bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__30__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + y * z).
Theorem Conj_mul_SNo_distrR__30__18: SNo (u * v + y * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__30__18.
(** Conj_mul_SNo_distrR__31__15 TMLPm7nvQmkx7oyDa8wbSdqZToJpQaT2VUo bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__31__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Theorem Conj_mul_SNo_distrR__31__15: SNo (w + y * z) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__31__15.
(** Conj_mul_SNo_distrR__31__19 TMUNHnKt24Q6oTQFXL3RDHCupi4sJZD1MwG bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__31__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Theorem Conj_mul_SNo_distrR__31__19: SNo (w + y * z) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__31__19.
(** Conj_mul_SNo_distrR__32__11 TMNRNpskpRrbKUGfXvaTQsZKjyqsxogtBuP bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__32__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Theorem Conj_mul_SNo_distrR__32__11: SNo (y * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__32__11.
(** Conj_mul_SNo_distrR__32__14 TMRfuofqd6iKhka1dWPu3pU7P1bkiE3pQNL bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__32__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Theorem Conj_mul_SNo_distrR__32__14: SNo (y * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__32__14.
(** Conj_mul_SNo_distrR__32__16 TMReDWJ14kaVXeicSxzY37Tv1r4vQ4VERa7 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__32__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Theorem Conj_mul_SNo_distrR__32__16: SNo (y * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__32__16.
(** Conj_mul_SNo_distrR__32__22 TMKqvFAR6LgY8ChXr3EykqYgMKehVFoSAG4 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__32__22.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Theorem Conj_mul_SNo_distrR__32__22: SNo (y * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__32__22.
(** Conj_mul_SNo_distrR__33__1 TMYCzbanTRopFqWvkPR1SC6UgRwXDcAv3WX bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__33__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Theorem Conj_mul_SNo_distrR__33__1: SNo (x * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__33__1.
(** Conj_mul_SNo_distrR__33__10 TMUb2jKZW6uy4A84fu72PmAsbpEco692EgM bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__33__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Theorem Conj_mul_SNo_distrR__33__10: SNo (x * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__33__10.
(** Conj_mul_SNo_distrR__33__11 TMWM3tmXyTq2VqGo2nuvKKqwaViUMeFpfcH bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__33__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Theorem Conj_mul_SNo_distrR__33__11: SNo (x * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__33__11.
(** Conj_mul_SNo_distrR__34__15 TMbuqEmUYukwC6DNGFGx2BiyFoXmdneaFda bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__34__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Theorem Conj_mul_SNo_distrR__34__15: SNo (u * z) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__34__15.
(** Conj_mul_SNo_distrR__35__17 TMRYkZvQTioECxVCcJCbkbeF2GpbtG2pQ5g bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__35__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Theorem Conj_mul_SNo_distrR__35__17: SNo ((x + y) * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__35__17.
(** Conj_mul_SNo_distrR__36__16 TMdYXjeNRGtQVG4koBEXz4mu1iWomVAQ1jC bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__36__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (u * z + x * v) <= w + u * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Theorem Conj_mul_SNo_distrR__36__16: SNo (w + u * v) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__36__16.
(** Conj_mul_SNo_distrR__37__12 TMdvk5o3ry4bBYeevH9yHHVot9tnzYbgVn2 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__37__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoR z.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Theorem Conj_mul_SNo_distrR__37__12: SNo (u + y) -> (x + y) * z < w + y * z.
Admitted.

End Conj_mul_SNo_distrR__37__12.
(** Conj_mul_SNo_distrR__39__5 TMR3nD8zMeFFXiKFfhBkF6jm1hsSYepHH8y bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__39__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + x * z).
Hypothesis H25: SNo (u * v + x * v).
Theorem Conj_mul_SNo_distrR__39__5: SNo (u * z + x * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__39__5.
(** Conj_mul_SNo_distrR__40__1 TMQUCDYK85o3twi18wq9L4DgUKi6gZtcPFC bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__40__1.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + x * z).
Theorem Conj_mul_SNo_distrR__40__1: SNo (u * v + x * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__40__1.
(** Conj_mul_SNo_distrR__40__24 TMS113RJw2iS1i5P74KVdgMNtYan1Ctuefb bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__40__24.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Theorem Conj_mul_SNo_distrR__40__24: SNo (u * v + x * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__40__24.
(** Conj_mul_SNo_distrR__41__10 TMZSG48dCkEuxXB7kbpaTTkfrJ6v9Tzwwf6 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__41__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Theorem Conj_mul_SNo_distrR__41__10: SNo (w + x * z) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__41__10.
(** Conj_mul_SNo_distrR__41__14 TMP6fgSW1qTQHd72h7CoGo9ofvcUCXpgxT8 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__41__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Theorem Conj_mul_SNo_distrR__41__14: SNo (w + x * z) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__41__14.
(** Conj_mul_SNo_distrR__42__19 TMLKqQ65FXqBmdoWQZ9DgixHHUSAswkCeF4 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__42__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Theorem Conj_mul_SNo_distrR__42__19: SNo (y * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__42__19.
(** Conj_mul_SNo_distrR__44__4 TMWGfq1LbAeFx4bHjLqm8ZoG7pBgJ5V3C3U bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__44__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Theorem Conj_mul_SNo_distrR__44__4: SNo (u * z) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__44__4.
(** Conj_mul_SNo_distrR__45__16 TMHLPJx6ynfxXTkzoWH5ofFdiHmgsPVqsbW bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__45__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Theorem Conj_mul_SNo_distrR__45__16: SNo ((x + y) * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__45__16.
(** Conj_mul_SNo_distrR__47__17 TMUyuaVyLYpWZ59z93sbXEMjs98kpWpanp7 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__47__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Theorem Conj_mul_SNo_distrR__47__17: SNo (x + u) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__47__17.
(** Conj_mul_SNo_distrR__48__11 TMaz44LnE1pb9RaEGi5AGLx4g1WG1f1bptq bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__48__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Theorem Conj_mul_SNo_distrR__48__11: SNo (u * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__48__11.
(** Conj_mul_SNo_distrR__48__15 TMU4ADx8d4eAtmHruNTko9Anu4MrwNHFJpJ bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__48__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR y.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: y < u.
Hypothesis H16: z < v.
Theorem Conj_mul_SNo_distrR__48__15: SNo (u * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__48__15.
(** Conj_mul_SNo_distrR__49__2 TMTZVPBF5BsrRLPKKBJc3dLpAvUitc2kwpP bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__49__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + x * z).
Theorem Conj_mul_SNo_distrR__49__2: SNo (u * v + x * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__49__2.
(** Conj_mul_SNo_distrR__52__2 TMKdWbsrJMU2vPPzCWXTApXppKARV7Gt41R bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__52__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Theorem Conj_mul_SNo_distrR__52__2: SNo (x * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__52__2.
(** Conj_mul_SNo_distrR__52__9 TMPnsZYKio5eknaCWc5sX8S74DsM9etm4gw bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__52__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Theorem Conj_mul_SNo_distrR__52__9: SNo (x * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__52__9.
(** Conj_mul_SNo_distrR__52__13 TMWAuogoqYeNYe8ePKXTF4LnMBFCnR1FLyY bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__52__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Theorem Conj_mul_SNo_distrR__52__13: SNo (x * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__52__13.
(** Conj_mul_SNo_distrR__52__19 TMH7wgEZFjYczdFvAs18ukb8d9fewfFrnbu bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__52__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Theorem Conj_mul_SNo_distrR__52__19: SNo (x * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__52__19.
(** Conj_mul_SNo_distrR__52__21 TMVjuCjVmizyaEigPLu548NFq3eRivbhoyA bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__52__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Theorem Conj_mul_SNo_distrR__52__21: SNo (x * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__52__21.
(** Conj_mul_SNo_distrR__53__19 TMd77WxRGj57fcLRo7Y4VnN2wJ9VieG9fgp bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__53__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (x + u).
Hypothesis H20: SNo ((x + y) * v).
Theorem Conj_mul_SNo_distrR__53__19: SNo (u * z) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__53__19.
(** Conj_mul_SNo_distrR__56__5 TMWNj5NmkZjvpuQVcHCKriFEUNdBjUs21Pi bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__56__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Theorem Conj_mul_SNo_distrR__56__5: SNo (x + u) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__56__5.
(** Conj_mul_SNo_distrR__56__15 TMNftAcP2idEbztxAk7iNGPiwNKpKjBEgUA bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__56__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Theorem Conj_mul_SNo_distrR__56__15: SNo (x + u) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__56__15.
(** Conj_mul_SNo_distrR__57__7 TMWMo5S4S8uA1Xa94wAmho8QYLMQfGa6B11 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__57__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL y.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + y * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < y.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Theorem Conj_mul_SNo_distrR__57__7: SNo (u * v) -> (w + x * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__57__7.
(** Conj_mul_SNo_distrR__58__19 TMGmFgPdFVZjvtefrPUoLPyy22zcyMf92Co bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__58__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + y * z).
Theorem Conj_mul_SNo_distrR__58__19: SNo (u * v + y * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__58__19.
(** Conj_mul_SNo_distrR__60__18 TMcF7xxLge6MoZsEJSwT7UVmBTX3GSaMVv9 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__60__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Theorem Conj_mul_SNo_distrR__60__18: SNo (y * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__60__18.
(** Conj_mul_SNo_distrR__61__21 TMdTGbgS4zY9qMjAkJnny7Kr8AtS28Se6UQ bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__61__21.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Theorem Conj_mul_SNo_distrR__61__21: SNo (x * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__61__21.
(** Conj_mul_SNo_distrR__63__2 TMW6MBPjUnTqFXsPGtfWJDU57Nc6qMuKgww bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__63__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Theorem Conj_mul_SNo_distrR__63__2: SNo ((x + y) * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__63__2.
(** Conj_mul_SNo_distrR__64__17 TMRzoL3Y9GrmMz2XoGinfT43U4ZMX4Q1n9H bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__64__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoR x.
Hypothesis H11: v :e SNoR z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: x < u.
Hypothesis H15: SNo v.
Hypothesis H16: z < v.
Hypothesis H18: SNo (u + y).
Theorem Conj_mul_SNo_distrR__64__17: SNo (w + u * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__64__17.
(** Conj_mul_SNo_distrR__67__6 TMKwPK1NSKTXSxa7P25qsYB1E4QvXkDxWdx bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__67__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + y * z).
Hypothesis H25: SNo (u * v + y * v).
Theorem Conj_mul_SNo_distrR__67__6: SNo (u * z + x * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__67__6.
(** Conj_mul_SNo_distrR__67__23 TMUHGWg6EDJfHSmJCUtPgpQogEQWeZ4vYgJ bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__67__23.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H24: SNo (w + y * z).
Hypothesis H25: SNo (u * v + y * v).
Theorem Conj_mul_SNo_distrR__67__23: SNo (u * z + x * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__67__23.
(** Conj_mul_SNo_distrR__68__11 TMdn7oyQpfHuXPmUTHiRmP4yinV5WrvXEEy bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__68__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + y * z).
Theorem Conj_mul_SNo_distrR__68__11: SNo (u * v + y * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__68__11.
(** Conj_mul_SNo_distrR__68__13 TMJtgS4CUtwWszuK7bu6TJrMqQAQRyJB8J7 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__68__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Hypothesis H24: SNo (w + y * z).
Theorem Conj_mul_SNo_distrR__68__13: SNo (u * v + y * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__68__13.
(** Conj_mul_SNo_distrR__69__4 TMbPgDJvxqmUnqd3yJGY5Fz6Q9SUUijkwE9 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__69__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Theorem Conj_mul_SNo_distrR__69__4: SNo (w + y * z) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__69__4.
(** Conj_mul_SNo_distrR__69__8 TMTis28vThZDvEsUqvr9uVLaW9X6o5a9o45 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__69__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Hypothesis H23: SNo (y * v).
Theorem Conj_mul_SNo_distrR__69__8: SNo (w + y * z) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__69__8.
(** Conj_mul_SNo_distrR__70__19 TMR8eFinNYkj2hZx9erM3aK81RvujHiRvCu bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__70__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Theorem Conj_mul_SNo_distrR__70__19: SNo (y * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__70__19.
(** Conj_mul_SNo_distrR__70__20 TMJpqoHR8tBDSavGk9sD6458zGvBEjWadCa bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__70__20.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H21: SNo (u * z).
Hypothesis H22: SNo (x * v).
Theorem Conj_mul_SNo_distrR__70__20: SNo (y * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__70__20.
(** Conj_mul_SNo_distrR__71__13 TMXnnCKVRhppcUsZGLjAjc6m3y19kqViVrG bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__71__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Hypothesis H19: SNo (w + u * v).
Hypothesis H20: SNo ((x + y) * v).
Hypothesis H21: SNo (u * z).
Theorem Conj_mul_SNo_distrR__71__13: SNo (x * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__71__13.
(** Conj_mul_SNo_distrR__73__19 TMRCkYVw8S41KhsMLC4Wq8bHrBLU3rrK7Ht bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__73__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Theorem Conj_mul_SNo_distrR__73__19: SNo ((x + y) * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__73__19.
(** Conj_mul_SNo_distrR__74__5 TMUPB9pzygmuQUd64T2mbg9We8K7Sx8S84r bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__74__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Hypothesis H18: SNo (u + y).
Theorem Conj_mul_SNo_distrR__74__5: SNo (w + u * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__74__5.
(** Conj_mul_SNo_distrR__75__5 TMTkW6kKiGcqjymbaJ4m2zpKnt97V3XRjj5 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__75__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H12: (w + u * v) <= u * z + x * v.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Hypothesis H17: SNo (u * v).
Theorem Conj_mul_SNo_distrR__75__5: SNo (u + y) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__75__5.
(** Conj_mul_SNo_distrR__76__12 TMYAEiux2ftJmL7dYKfKyomf2jQH1YeQ5M9 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__76__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + y) * x2 = x * x2 + y * x2).
Hypothesis H5: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H6: SNo (x + y).
Hypothesis H7: SNo ((x + y) * z).
Hypothesis H8: SNo (y * z).
Hypothesis H9: SNo w.
Hypothesis H10: u :e SNoL x.
Hypothesis H11: v :e SNoL z.
Hypothesis H13: SNo u.
Hypothesis H14: u < x.
Hypothesis H15: SNo v.
Hypothesis H16: v < z.
Theorem Conj_mul_SNo_distrR__76__12: SNo (u * v) -> (w + y * z) < (x + y) * z.
Admitted.

End Conj_mul_SNo_distrR__76__12.
(** Conj_mul_SNo_distrR__77__2 TMdugbRqF1AudSCUMjJidHjDUPf77W8phGT bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__77__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR y.
Hypothesis H18: (x + v) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: y < v.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__77__2: SNo (x + v) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__77__2.
(** Conj_mul_SNo_distrR__77__13 TMWkauJuAqaYcbJRnnZxFpaneBQ73EunD8T bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__77__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR y.
Hypothesis H18: (x + v) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: y < v.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__77__13: SNo (x + v) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__77__13.
(** Conj_mul_SNo_distrR__78__18 TMVLi79f5ooai9sgjMPsN3EdCczK5LExmT7 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__78__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR y.
Hypothesis H19: SNo v.
Hypothesis H20: y < v.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__78__18: SNo (v * z) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__78__18.
(** Conj_mul_SNo_distrR__80__0 TMR57Nz5WAEUXE817U3ugbZ9v8kRLbVgnEH bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__80__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__80__0: SNo (v + y) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__80__0.
(** Conj_mul_SNo_distrR__80__7 TMT8JVYbXfJ92euamdyePXNdrjYuu9gqm4z bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__80__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__80__7: SNo (v + y) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__80__7.
(** Conj_mul_SNo_distrR__80__13 TMJ7u36B2TPRL7SyeEphjUU4sA5AmYomqG1 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__80__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__80__13: SNo (v + y) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__80__13.
(** Conj_mul_SNo_distrR__80__16 TMGgbV6t1hxLQCKqyRuWqRAx58k3ngxZifK bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__80__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__80__16: SNo (v + y) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__80__16.
(** Conj_mul_SNo_distrR__81__7 TMY3Cs5bDWCjKrHiSaH5ii4RqFKFQ2VyHvh bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__81__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__81__7: SNo (v * z) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__81__7.
(** Conj_mul_SNo_distrR__81__9 TMNaP1cQ9ixnsnbZvwm1g5yFAY7SaNddXc5 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__81__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__81__9: SNo (v * z) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__81__9.
(** Conj_mul_SNo_distrR__81__10 TMShdL6GozWZ1axGsoLsssjmXpiE7nbxhnQ bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__81__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__81__10: SNo (v * z) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__81__10.
(** Conj_mul_SNo_distrR__81__19 TMJh7xa5c7G9F29UBVvcWDGrnT43zspkkHL bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__81__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__81__19: SNo (v * z) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__81__19.
(** Conj_mul_SNo_distrR__82__13 TMbmp3VPbw8DP8kVyEkDGEWq37HxkvmKF7v bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__82__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Theorem Conj_mul_SNo_distrR__82__13: SNo (v * u) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__82__13.
(** Conj_mul_SNo_distrR__83__8 TMGvJMkcjaxY8pSmEjav1UrPSUHkPV9CHrp bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__83__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoR (x + y).
Hypothesis H12: u :e SNoL z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H15: u < z.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Hypothesis H20: SNo (w * u).
Hypothesis H21: SNo (w * z + x * u + y * u).
Theorem Conj_mul_SNo_distrR__83__8: SNo (x * z + y * z + w * u) -> (x * z + y * z) < w * z + (x + y) * u + - (w * u).
Admitted.

End Conj_mul_SNo_distrR__83__8.
(** Conj_mul_SNo_distrR__85__18 TMPU9rb2gCEPYzveAHTBZntzdbVWWGxPREr bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__85__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoR (x + y).
Hypothesis H12: u :e SNoL z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H15: u < z.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H19: SNo ((x + y) * u).
Theorem Conj_mul_SNo_distrR__85__18: SNo (w * u) -> (x * z + y * z) < w * z + (x + y) * u + - (w * u).
Admitted.

End Conj_mul_SNo_distrR__85__18.
(** Conj_mul_SNo_distrR__90__15 TMVZSi6EwpMF7T395XzsM67rQ2ufThh2r4E bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__90__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoR (x + y).
Hypothesis H13: u :e SNoL z.
Hypothesis H14: SNo w.
Hypothesis H16: u < z.
Theorem Conj_mul_SNo_distrR__90__15: SNo (x * u) -> (x * z + y * z) < w * z + (x + y) * u + - (w * u).
Admitted.

End Conj_mul_SNo_distrR__90__15.
(** Conj_mul_SNo_distrR__92__5 TMZJ3ghx23sYEWD8VhXCqKwaY6PXbhLzC4N bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__92__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoL y.
Hypothesis H18: w <= x + v.
Hypothesis H19: SNo v.
Hypothesis H20: v < y.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__92__5: SNo (v * z) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__92__5.
(** Conj_mul_SNo_distrR__92__16 TMYd1RPzXPRBXSo7U5KAEoDNf1UdDXteTnq bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__92__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H17: v :e SNoL y.
Hypothesis H18: w <= x + v.
Hypothesis H19: SNo v.
Hypothesis H20: v < y.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__92__16: SNo (v * z) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__92__16.
(** Conj_mul_SNo_distrR__93__0 TMV3sKQA4Sh62SQtRQFqUh2RYFXKpksXJdv bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__93__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoL y.
Hypothesis H18: w <= x + v.
Hypothesis H19: SNo v.
Hypothesis H20: v < y.
Theorem Conj_mul_SNo_distrR__93__0: SNo (v * u) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__93__0.
(** Conj_mul_SNo_distrR__94__0 TMW5J1p6ri2h3XpxHqA7qdGhqoN4rd1Wmyx bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__94__0.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoL x.
Hypothesis H18: w <= v + y.
Hypothesis H19: SNo v.
Hypothesis H20: v < x.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__94__0: SNo (v + y) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__94__0.
(** Conj_mul_SNo_distrR__94__22 TMGVpJbjSZw11rfp9Q8v3zkAbYkVECD3HjL bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__94__22.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoL x.
Hypothesis H18: w <= v + y.
Hypothesis H19: SNo v.
Hypothesis H20: v < x.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__94__22: SNo (v + y) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__94__22.
(** Conj_mul_SNo_distrR__95__12 TMTjcbr4qgJB2j2bzwH3jJDPw7HLTc5kjzi bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__95__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoL x.
Hypothesis H18: w <= v + y.
Hypothesis H19: SNo v.
Hypothesis H20: v < x.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__95__12: SNo (v * z) -> (x * z + y * z + w * u) < w * z + x * u + y * u.
Admitted.

End Conj_mul_SNo_distrR__95__12.
(** Conj_mul_SNo_distrR__97__18 TMYJy1GcCAhUHPjV5HDcGoCAwdrxkaMjvcm bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__97__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoL (x + y).
Hypothesis H12: u :e SNoR z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H15: z < u.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H19: SNo ((x + y) * u).
Hypothesis H20: SNo (w * u).
Hypothesis H21: SNo (w * z + x * u + y * u).
Theorem Conj_mul_SNo_distrR__97__18: SNo (x * z + y * z + w * u) -> (x * z + y * z) < w * z + (x + y) * u + - (w * u).
Admitted.

End Conj_mul_SNo_distrR__97__18.
(** Conj_mul_SNo_distrR__98__10 TMT8cWBkCkTEcypsJn99yRjGXYLVgeCN3Cn bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__98__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H11: w :e SNoL (x + y).
Hypothesis H12: u :e SNoR z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H15: z < u.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Hypothesis H20: SNo (w * u).
Theorem Conj_mul_SNo_distrR__98__10: SNo (w * z + x * u + y * u) -> (x * z + y * z) < w * z + (x + y) * u + - (w * u).
Admitted.

End Conj_mul_SNo_distrR__98__10.
(** Conj_mul_SNo_distrR__100__6 TMYakRNoEJbjsTqCp4RqMrptQvBkJwwJpf1 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__100__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoL (x + y).
Hypothesis H12: u :e SNoR z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H15: z < u.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Theorem Conj_mul_SNo_distrR__100__6: SNo (x * u + y * u) -> (x * z + y * z) < w * z + (x + y) * u + - (w * u).
Admitted.

End Conj_mul_SNo_distrR__100__6.
(** Conj_mul_SNo_distrR__100__13 TMaqP72VD68s2zKHcaCDzWNCPhxoeC5Ukct bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__100__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoL (x + y).
Hypothesis H12: u :e SNoR z.
Hypothesis H14: SNo u.
Hypothesis H15: z < u.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Theorem Conj_mul_SNo_distrR__100__13: SNo (x * u + y * u) -> (x * z + y * z) < w * z + (x + y) * u + - (w * u).
Admitted.

End Conj_mul_SNo_distrR__100__13.
(** Conj_mul_SNo_distrR__101__14 TMH8JteUWPM6shMFTW2Db98abzc3HtqCKnr bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__101__14.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoL (x + y).
Hypothesis H13: u :e SNoR z.
Hypothesis H15: SNo u.
Hypothesis H16: z < u.
Hypothesis H17: SNo (x * u).
Hypothesis H18: SNo (y * u).
Hypothesis H19: SNo (w * z).
Theorem Conj_mul_SNo_distrR__101__14: SNo ((x + y) * u) -> (x * z + y * z) < w * z + (x + y) * u + - (w * u).
Admitted.

End Conj_mul_SNo_distrR__101__14.
(** Conj_mul_SNo_distrR__104__2 TMRrzkzxBWvj9eKcFmJAryE4BHsoL9JWxZ3 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__104__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoL (x + y).
Hypothesis H13: u :e SNoR z.
Hypothesis H14: SNo w.
Hypothesis H15: SNo u.
Hypothesis H16: z < u.
Theorem Conj_mul_SNo_distrR__104__2: SNo (x * u) -> (x * z + y * z) < w * z + (x + y) * u + - (w * u).
Admitted.

End Conj_mul_SNo_distrR__104__2.
(** Conj_mul_SNo_distrR__105__19 TMKSAH3dGmGsGNcFrm78y4Ft8chzCFwgCjN bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__105__19.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR y.
Hypothesis H18: (x + v) <= w.
Hypothesis H20: y < v.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__105__19: SNo (x + v) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__105__19.
(** Conj_mul_SNo_distrR__107__18 TMKmKcNTBSArFcrocLmff7btcAhdN8iBE8e bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__107__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR y.
Hypothesis H19: SNo v.
Hypothesis H20: y < v.
Theorem Conj_mul_SNo_distrR__107__18: SNo (v * u) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__107__18.
(** Conj_mul_SNo_distrR__108__2 TMbxGoSFTWK8QHKDvsfq6e7TMu7eKLQpbpb bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__108__2.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__108__2: SNo (v + y) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__108__2.
(** Conj_mul_SNo_distrR__108__9 TMct4mbr4YRkQEBrCxTtpC9uLWg5k3AkBst bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__108__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__108__9: SNo (v + y) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__108__9.
(** Conj_mul_SNo_distrR__109__8 TMR29mPKBrRdXxvXXa2ABtwUAtyYCgtQuKg bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__109__8.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__109__8: SNo (v * z) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__109__8.
(** Conj_mul_SNo_distrR__109__18 TMarrrQcBPDY9ANwKErTgSQcuXFFPeGPYyR bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__109__18.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__109__18: SNo (v * z) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__109__18.
(** Conj_mul_SNo_distrR__110__16 TMT3SmXYNFrPGLCpf1JXtoh6fuYCoBBXhsj bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__110__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoR z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: z < u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H17: v :e SNoR x.
Hypothesis H18: (v + y) <= w.
Hypothesis H19: SNo v.
Hypothesis H20: x < v.
Theorem Conj_mul_SNo_distrR__110__16: SNo (v * u) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__110__16.
(** Conj_mul_SNo_distrR__111__6 TMKA4QnGbrP8ewmTp7yjZAd8eBK4rMndEKH bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__111__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoR (x + y).
Hypothesis H12: u :e SNoR z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H15: z < u.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Hypothesis H20: SNo (w * u).
Hypothesis H21: SNo (w * z + x * u + y * u).
Theorem Conj_mul_SNo_distrR__111__6: SNo (x * z + y * z + w * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__111__6.
(** Conj_mul_SNo_distrR__112__16 TMTsYSd29QRVRacBeoKmMi44fv9bZkqsqt5 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__112__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoR (x + y).
Hypothesis H12: u :e SNoR z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H15: z < u.
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Hypothesis H20: SNo (w * u).
Theorem Conj_mul_SNo_distrR__112__16: SNo (w * z + x * u + y * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__112__16.
(** Conj_mul_SNo_distrR__115__15 TMdr8fpa33fDW9E7px4bSFN6qQGct1NccZR bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__115__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoR (x + y).
Hypothesis H13: u :e SNoR z.
Hypothesis H14: SNo w.
Hypothesis H16: z < u.
Hypothesis H17: SNo (x * u).
Hypothesis H18: SNo (y * u).
Hypothesis H19: SNo (w * z).
Theorem Conj_mul_SNo_distrR__115__15: SNo ((x + y) * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__115__15.
(** Conj_mul_SNo_distrR__116__7 TMN7czdKeDMPFj3NnG9p73uF2fTNWbJtajp bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__116__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoR (x + y).
Hypothesis H13: u :e SNoR z.
Hypothesis H14: SNo w.
Hypothesis H15: SNo u.
Hypothesis H16: z < u.
Hypothesis H17: SNo (x * u).
Hypothesis H18: SNo (y * u).
Theorem Conj_mul_SNo_distrR__116__7: SNo (w * z) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__116__7.
(** Conj_mul_SNo_distrR__116__15 TMKyhHdRiSpxLyfSq3VUGSMRfSwctKQycDi bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__116__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoR (x + y).
Hypothesis H13: u :e SNoR z.
Hypothesis H14: SNo w.
Hypothesis H16: z < u.
Hypothesis H17: SNo (x * u).
Hypothesis H18: SNo (y * u).
Theorem Conj_mul_SNo_distrR__116__15: SNo (w * z) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__116__15.
(** Conj_mul_SNo_distrR__117__12 TMUEPZtJ8VRUMpL7GBoiZDjMtTJZq1k5edf bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__117__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H13: u :e SNoR z.
Hypothesis H14: SNo w.
Hypothesis H15: SNo u.
Hypothesis H16: z < u.
Hypothesis H17: SNo (x * u).
Theorem Conj_mul_SNo_distrR__117__12: SNo (y * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__117__12.
(** Conj_mul_SNo_distrR__118__12 TMErf8zaukDoYseiSjUgjpyqPn9NCEmjXGK bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__118__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H13: u :e SNoR z.
Hypothesis H14: SNo w.
Hypothesis H15: SNo u.
Hypothesis H16: z < u.
Theorem Conj_mul_SNo_distrR__118__12: SNo (x * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__118__12.
(** Conj_mul_SNo_distrR__119__9 TMVSquwN6wmCxEKjoGQgbEGZgucA73LggWW bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__119__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoL y.
Hypothesis H18: w <= x + v.
Hypothesis H19: SNo v.
Hypothesis H20: v < y.
Hypothesis H21: SNo (v * u).
Hypothesis H22: SNo (v * z).
Theorem Conj_mul_SNo_distrR__119__9: SNo (x + v) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__119__9.
(** Conj_mul_SNo_distrR__120__16 TMSuPWeJog6BvBemPtjpDyM3kJsRxpDJrpo bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__120__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (x + x2) * z = x * z + x2 * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H17: v :e SNoL y.
Hypothesis H18: w <= x + v.
Hypothesis H19: SNo v.
Hypothesis H20: v < y.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__120__16: SNo (v * z) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__120__16.
(** Conj_mul_SNo_distrR__121__3 TMVzGEdKhSYAVyKfTJN9ubZcnnifuK6XCxX bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__121__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev y) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x + x2) * y2 = x * y2 + x2 * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H10: u < z.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoL y.
Hypothesis H18: w <= x + v.
Hypothesis H19: SNo v.
Hypothesis H20: v < y.
Theorem Conj_mul_SNo_distrR__121__3: SNo (v * u) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__121__3.
(** Conj_mul_SNo_distrR__123__10 TMHb1ZGudXqMwXcWmR5PPAcJwWxTt7GX8K6 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__123__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (x2 + y) * z = x2 * z + y * z).
Hypothesis H4: (forall x2:set, x2 :e SNoS_ (SNoLev x) -> (forall y2:set, y2 :e SNoS_ (SNoLev z) -> (x2 + y) * y2 = x2 * y2 + y * y2)).
Hypothesis H5: SNo (x * z).
Hypothesis H6: SNo (y * z).
Hypothesis H7: u :e SNoL z.
Hypothesis H8: SNo w.
Hypothesis H9: SNo u.
Hypothesis H11: SNo (x * u).
Hypothesis H12: SNo (y * u).
Hypothesis H13: SNo (w * z).
Hypothesis H14: SNo (w * u).
Hypothesis H15: SNo (w * z + x * u + y * u).
Hypothesis H16: SNo (x * z + y * z + w * u).
Hypothesis H17: v :e SNoL x.
Hypothesis H18: w <= v + y.
Hypothesis H19: SNo v.
Hypothesis H20: v < x.
Hypothesis H21: SNo (v * u).
Theorem Conj_mul_SNo_distrR__123__10: SNo (v * z) -> (w * z + x * u + y * u) < x * z + y * z + w * u.
Admitted.

End Conj_mul_SNo_distrR__123__10.
(** Conj_mul_SNo_distrR__125__15 TMG6Ed7CNp5CtxzisUGSLKRzaAg8jb8PHsA bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__125__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoL (x + y).
Hypothesis H12: u :e SNoL z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Hypothesis H20: SNo (w * u).
Hypothesis H21: SNo (w * z + x * u + y * u).
Theorem Conj_mul_SNo_distrR__125__15: SNo (x * z + y * z + w * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__125__15.
(** Conj_mul_SNo_distrR__126__9 TMS9ZBnEU5zJXypDnr55dyZj2vQoNMPXJ12 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__126__9.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoL (x + y).
Hypothesis H12: u :e SNoL z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H15: u < z.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Hypothesis H20: SNo (w * u).
Theorem Conj_mul_SNo_distrR__126__9: SNo (w * z + x * u + y * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__126__9.
(** Conj_mul_SNo_distrR__126__11 TMQQ5TytRWd5jQx4kwLCNYzJX3XtGoNx838 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__126__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H12: u :e SNoL z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H15: u < z.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Hypothesis H20: SNo (w * u).
Theorem Conj_mul_SNo_distrR__126__11: SNo (w * z + x * u + y * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__126__11.
(** Conj_mul_SNo_distrR__127__7 TMFRFLNCAwByM8QsRVEQ8hBkoSgiMXU6uRX bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__127__7.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoL (x + y).
Hypothesis H12: u :e SNoL z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H15: u < z.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Theorem Conj_mul_SNo_distrR__127__7: SNo (w * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__127__7.
(** Conj_mul_SNo_distrR__128__15 TMdio434wQ2X1DSMfMBLroMwX78BTLPX4xb bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__128__15.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x * z).
Hypothesis H9: SNo (y * z).
Hypothesis H10: SNo (x * z + y * z).
Hypothesis H11: w :e SNoL (x + y).
Hypothesis H12: u :e SNoL z.
Hypothesis H13: SNo w.
Hypothesis H14: SNo u.
Hypothesis H16: SNo (x * u).
Hypothesis H17: SNo (y * u).
Hypothesis H18: SNo (w * z).
Hypothesis H19: SNo ((x + y) * u).
Theorem Conj_mul_SNo_distrR__128__15: SNo (x * u + y * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__128__15.
(** Conj_mul_SNo_distrR__129__10 TMbCVvbWdvQuvVDWx1pmoiYFB9xdSpfTUAu bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__129__10.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoL (x + y).
Hypothesis H13: u :e SNoL z.
Hypothesis H14: SNo w.
Hypothesis H15: SNo u.
Hypothesis H16: u < z.
Hypothesis H17: SNo (x * u).
Hypothesis H18: SNo (y * u).
Hypothesis H19: SNo (w * z).
Theorem Conj_mul_SNo_distrR__129__10: SNo ((x + y) * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__129__10.
(** Conj_mul_SNo_distrR__130__13 TMFqsC1YdjeodiemfS8aTPvwvqXBma6DZjj bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__130__13.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoL (x + y).
Hypothesis H14: SNo w.
Hypothesis H15: SNo u.
Hypothesis H16: u < z.
Hypothesis H17: SNo (x * u).
Hypothesis H18: SNo (y * u).
Theorem Conj_mul_SNo_distrR__130__13: SNo (w * z) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__130__13.
(** Conj_mul_SNo_distrR__131__12 TMbk48qRYLWf1AtxikXuWdBGhZnFdyeikbT bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__131__12.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H13: u :e SNoL z.
Hypothesis H14: SNo w.
Hypothesis H15: SNo u.
Hypothesis H16: u < z.
Hypothesis H17: SNo (x * u).
Theorem Conj_mul_SNo_distrR__131__12: SNo (y * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__131__12.
(** Conj_mul_SNo_distrR__131__17 TMXVxFvrAEo8u5qotzvuZkF3E1zE7NX9eqh bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__131__17.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoL (x + y).
Hypothesis H13: u :e SNoL z.
Hypothesis H14: SNo w.
Hypothesis H15: SNo u.
Hypothesis H16: u < z.
Theorem Conj_mul_SNo_distrR__131__17: SNo (y * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__131__17.
(** Conj_mul_SNo_distrR__132__4 TMYoVokjyoKoJZZoXWnadx6zKwz8jh3B98L bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__132__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoL (x + y).
Hypothesis H13: u :e SNoL z.
Hypothesis H14: SNo w.
Hypothesis H15: SNo u.
Hypothesis H16: u < z.
Theorem Conj_mul_SNo_distrR__132__4: SNo (x * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__132__4.
(** Conj_mul_SNo_distrR__132__16 TMV6XTChegLQBsFFGLeXpn9qjfcsuYrvDJA bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__132__16.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNo (x + y).
Hypothesis H9: SNo (x * z).
Hypothesis H10: SNo (y * z).
Hypothesis H11: SNo (x * z + y * z).
Hypothesis H12: w :e SNoL (x + y).
Hypothesis H13: u :e SNoL z.
Hypothesis H14: SNo w.
Hypothesis H15: SNo u.
Theorem Conj_mul_SNo_distrR__132__16: SNo (x * u) -> (w * z + (x + y) * u + - (w * u)) < x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__132__16.
(** Conj_mul_SNo_distrR__133__11 TML7HZcZ7JwBWG2K9ezf3QaNvpogEzhkBTX bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__133__11.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNoCutP w u.
Hypothesis H9: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H10: (forall v:set, v :e u -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H12: SNo (x + y).
Hypothesis H13: SNo ((x + y) * z).
Hypothesis H14: SNo (x * z).
Hypothesis H15: SNo (y * z).
Hypothesis H16: SNo (x * z + y * z).
Theorem Conj_mul_SNo_distrR__133__11: x * z + y * z = SNoCut (binunion (Repl (SNoL (x * z)) (fun v:set => v + y * z)) (Repl (SNoL (y * z)) (add_SNo (x * z)))) (binunion (Repl (SNoR (x * z)) (fun v:set => v + y * z)) (Repl (SNoR (y * z)) (add_SNo (x * z)))) -> (x + y) * z = x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__133__11.
(** Conj_mul_SNo_distrR__135__6 TMUdLTNFkPPLEBZomZJEP1p5q1yPFnJUrCD bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__135__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNoCutP w u.
Hypothesis H9: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H10: (forall v:set, v :e u -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H11: (x + y) * z = SNoCut w u.
Hypothesis H12: SNo (x + y).
Hypothesis H13: SNo ((x + y) * z).
Hypothesis H14: SNo (x * z).
Theorem Conj_mul_SNo_distrR__135__6: SNo (y * z) -> (x + y) * z = x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__135__6.
(** Conj_mul_SNo_distrR__136__5 TMSnYvLozqEjEtvJrXtGzfQjDkyd1f5Vs7W bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__136__5.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNoCutP w u.
Hypothesis H9: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H10: (forall v:set, v :e u -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H11: (x + y) * z = SNoCut w u.
Hypothesis H12: SNo (x + y).
Hypothesis H13: SNo ((x + y) * z).
Theorem Conj_mul_SNo_distrR__136__5: SNo (x * z) -> (x + y) * z = x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__136__5.
(** Conj_mul_SNo_distrR__137__3 TMczyWUXwud5rYRj376zaqvmmeCKZRMfCj4 bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__137__3.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNoCutP w u.
Hypothesis H9: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H10: (forall v:set, v :e u -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H11: (x + y) * z = SNoCut w u.
Hypothesis H12: SNo (x + y).
Theorem Conj_mul_SNo_distrR__137__3: SNo ((x + y) * z) -> (x + y) * z = x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__137__3.
(** Conj_mul_SNo_distrR__137__4 TMdgaUgt6mi2ReHtWvwJifq4ETmGwGbiY7b bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__137__4.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H6: (forall v:set, v :e SNoS_ (SNoLev x) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (v + y) * x2 = v * x2 + y * x2)).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNoCutP w u.
Hypothesis H9: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H10: (forall v:set, v :e u -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H11: (x + y) * z = SNoCut w u.
Hypothesis H12: SNo (x + y).
Theorem Conj_mul_SNo_distrR__137__4: SNo ((x + y) * z) -> (x + y) * z = x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__137__4.
(** Conj_mul_SNo_distrR__138__6 TMQdquZdAwnr9iL7hp3Cv2QXzBuKjSyKXRN bounty of about 25 bars **)
Section Conj_mul_SNo_distrR__138__6.
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Hypothesis H0: SNo x.
Hypothesis H1: SNo y.
Hypothesis H2: SNo z.
Hypothesis H3: (forall v:set, v :e SNoS_ (SNoLev x) -> (v + y) * z = v * z + y * z).
Hypothesis H4: (forall v:set, v :e SNoS_ (SNoLev y) -> (x + v) * z = x * z + v * z).
Hypothesis H5: (forall v:set, v :e SNoS_ (SNoLev z) -> (x + y) * v = x * v + y * v).
Hypothesis H7: (forall v:set, v :e SNoS_ (SNoLev y) -> (forall x2:set, x2 :e SNoS_ (SNoLev z) -> (x + v) * x2 = x * x2 + v * x2)).
Hypothesis H8: SNoCutP w u.
Hypothesis H9: (forall v:set, v :e w -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H10: (forall v:set, v :e u -> (forall P:prop, (forall x2:set, x2 :e SNoL (x + y) -> (forall y2:set, y2 :e SNoR z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> (forall x2:set, x2 :e SNoR (x + y) -> (forall y2:set, y2 :e SNoL z -> v = x2 * z + (x + y) * y2 + - (x2 * y2) -> P)) -> P)).
Hypothesis H11: (x + y) * z = SNoCut w u.
Theorem Conj_mul_SNo_distrR__138__6: SNo (x + y) -> (x + y) * z = x * z + y * z.
Admitted.

End Conj_mul_SNo_distrR__138__6.
(** Conj_mul_SNo_assoc_lem1__1__7 TMKnnoPW6hcBe3TD7vdUN6JmCK4pKEW7jMc bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__1__7.
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
Hypothesis H18: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H19: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H20: SNo u.
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
Hypothesis H41: SNo (g u (g y z) + g x (g x2 z) + g x (g y y2) + g u v + g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__1__7: SNo (g u (g x2 z) + g u (g y y2) + g x (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__1__7.
(** Conj_mul_SNo_assoc_lem1__1__33 TMZ2dwQaMb41nvs4kPygdgDzVBerbqzWcPV bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__1__33.
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
Hypothesis H18: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H19: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H20: SNo u.
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
Hypothesis H34: SNo (g x (g x2 z)).
Hypothesis H35: SNo (g x (g y y2)).
Hypothesis H36: SNo (g u (g y z) + g x v).
Hypothesis H37: SNo (g (g x y) z + g u v).
Hypothesis H38: SNo (g u (g x2 y2)).
Hypothesis H39: SNo (g u (v + g x2 y2)).
Hypothesis H40: SNo (g u (g x2 z + g y y2)).
Hypothesis H41: SNo (g u (g y z) + g x (g x2 z) + g x (g y y2) + g u v + g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__1__33: SNo (g u (g x2 z) + g u (g y y2) + g x (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__1__33.
(** Conj_mul_SNo_assoc_lem1__2__27 TMMYbjBBEyXjofdffuhoRfHHJBgAska7jJo bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__2__27.
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
Hypothesis H18: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H19: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H20: SNo u.
Hypothesis H21: SNo y2.
Hypothesis H22: SNo (g u (g y z)).
Hypothesis H23: SNo (g x v).
Hypothesis H24: SNo (g x x2).
Hypothesis H25: SNo (g u v).
Hypothesis H26: SNo (g u x2).
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
Theorem Conj_mul_SNo_assoc_lem1__2__27: SNo (g u (g y z) + g x (g x2 z) + g x (g y y2) + g u v + g u (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__2__27.
(** Conj_mul_SNo_assoc_lem1__3__17 TMN4vHLkZcrXP7tS5GZpmPUBoN4YsEqLyv5 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__3__17.
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
Hypothesis H18: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H19: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H20: SNo u.
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
Theorem Conj_mul_SNo_assoc_lem1__3__17: SNo (g u v + g u (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__3__17.
(** Conj_mul_SNo_assoc_lem1__3__38 TMSqYdGmrpnSAebNhRfhF9U1NUTqAvCAwLC bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__3__38.
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
Hypothesis H18: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H19: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H20: SNo u.
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
Hypothesis H39: SNo (g u (v + g x2 y2)).
Hypothesis H40: SNo (g u (g x2 z + g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__3__38: SNo (g u v + g u (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__3__38.
(** Conj_mul_SNo_assoc_lem1__4__1 TMXcAqsTEE1hgtGAT5HjrtMKvK2iNpueWPH bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__4__1.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__4__1: SNo (g u (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__4__1.
(** Conj_mul_SNo_assoc_lem1__4__8 TMHqeR25A8wfCNzLRzDFcNrBmLVdymZjKmd bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__4__8.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__4__8: SNo (g u (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__4__8.
(** Conj_mul_SNo_assoc_lem1__4__18 TMSNQ9v7jdToPn2XowpMzAZxtuxyWQU35tL bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__4__18.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__4__18: SNo (g u (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__4__18.
(** Conj_mul_SNo_assoc_lem1__4__27 TMRivtAg1Hpj5g8vE8JBaLWPNZ5M99bCppQ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__4__27.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo y2.
Hypothesis H23: SNo (g u (g y z)).
Hypothesis H24: SNo (g x v).
Hypothesis H25: SNo (g x x2).
Hypothesis H26: SNo (g u v).
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
Theorem Conj_mul_SNo_assoc_lem1__4__27: SNo (g u (g x2 z + g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__4__27.
(** Conj_mul_SNo_assoc_lem1__6__15 TMMKp1bkq5dDyp14ALeW9ahjHFkKUqM2nvs bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__6__15.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__6__15: SNo (v + g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__6__15.
(** Conj_mul_SNo_assoc_lem1__6__31 TMPXcW5uzUy7EqAgtSNhTECT8qPW2egc1Ur bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__6__31.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Hypothesis H34: SNo (g x (g x2 y2)).
Hypothesis H35: SNo (g x (g x2 z)).
Hypothesis H36: SNo (g x (g y y2)).
Hypothesis H37: SNo (g u (g y z) + g x v).
Hypothesis H38: SNo (g (g x y) z + g u v).
Hypothesis H39: SNo (g u (g x2 y2)).
Theorem Conj_mul_SNo_assoc_lem1__6__31: SNo (v + g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__6__31.
(** Conj_mul_SNo_assoc_lem1__6__39 TMTWYzUV5UDpy1hKuhnZarfTwo7KBRde5wJ bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__6__39.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__6__39: SNo (v + g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__6__39.
(** Conj_mul_SNo_assoc_lem1__9__22 TML5UvhA1EB19XK4JVreoGD2HLShnGjvJ1L bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__9__22.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H21: SNo u.
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
Theorem Conj_mul_SNo_assoc_lem1__9__22: SNo (g u (g y z) + g x v) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__9__22.
(** Conj_mul_SNo_assoc_lem1__10__14 TMciT5MQuzNPVkBa3VvEFY6mhkvQM44PZuM bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__10__14.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__10__14: SNo (g x (g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__10__14.
(** Conj_mul_SNo_assoc_lem1__10__16 TMQQUwReS53D6Ao3Pua1pAeLJXeWQanM8Uf bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__10__16.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__10__16: SNo (g x (g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__10__16.
(** Conj_mul_SNo_assoc_lem1__10__19 TMRVGx7eJ9f36S1ZzNyy8Y1R5BCct4CBbU6 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__10__19.
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
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__10__19: SNo (g x (g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__10__19.
(** Conj_mul_SNo_assoc_lem1__10__26 TMWFSt8CQsyePtHHgC3w6gXt9FkTq72zq6n bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__10__26.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__10__26: SNo (g x (g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__10__26.
(** Conj_mul_SNo_assoc_lem1__12__2 TMZo1YdifN3e5enp4ydBHys7i9ghGmkcy3N bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__12__2.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__12__2: SNo (g x (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__12__2.
(** Conj_mul_SNo_assoc_lem1__12__16 TMPXwsxij2gSSDac57YbY16Wika8rQ18gTL bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__12__16.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__12__16: SNo (g x (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__12__16.
(** Conj_mul_SNo_assoc_lem1__12__17 TMVnHxQQNK4PGT3sHgK5wJFtaB6LWs1aEWx bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__12__17.
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
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__12__17: SNo (g x (g x2 y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__12__17.
(** Conj_mul_SNo_assoc_lem1__13__6 TMMq2w8qWm3wmZmQdsNFjkpwHhP7uU6Vc8V bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__13__6.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__13__6: SNo (g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__13__6.
(** Conj_mul_SNo_assoc_lem1__13__12 TMa3hMPDPyKTYUenuDmjD9MyWFLydGTRNaD bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__13__12.
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
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__13__12: SNo (g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__13__12.
(** Conj_mul_SNo_assoc_lem1__13__26 TMZ1iaAArizmmL56DcJgDa6t1M26M8Bgzmi bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__13__26.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H21: SNo u.
Hypothesis H22: SNo x2.
Hypothesis H23: SNo y2.
Hypothesis H24: SNo (g u (g y z)).
Hypothesis H25: SNo (g x v).
Hypothesis H27: SNo (g u v).
Hypothesis H28: SNo (g u x2).
Hypothesis H29: SNo (g u y).
Hypothesis H30: SNo (g x2 z).
Hypothesis H31: SNo (g y y2).
Hypothesis H32: SNo (g u (g x2 z)).
Hypothesis H33: SNo (g u (g y y2)).
Theorem Conj_mul_SNo_assoc_lem1__13__26: SNo (g x2 y2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__13__26.
(** Conj_mul_SNo_assoc_lem1__14__12 TMTrG48ZSckWqGvwCzWNNEhyG34pswmW1KS bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__14__12.
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
Hypothesis H13: SNo (g (g x y) z).
Hypothesis H14: u :e SNoS_ (SNoLev x).
Hypothesis H15: SNo v.
Hypothesis H16: x2 :e SNoS_ (SNoLev y).
Hypothesis H17: y2 :e SNoS_ (SNoLev z).
Hypothesis H18: w = g u (g y z) + g x v + - (g u v).
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__14__12: SNo (g u (g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__14__12.
(** Conj_mul_SNo_assoc_lem1__14__21 TMFpz8ZrD1CgD8aTy4QqkjTACqbqDxvi3AN bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__14__21.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__14__21: SNo (g u (g y y2)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__14__21.
(** Conj_mul_SNo_assoc_lem1__15__6 TMHEBdM2iQR8sxxGuChA4vnQ52YjKV8QT9x bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__15__6.
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
Hypothesis H19: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H20: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
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
Theorem Conj_mul_SNo_assoc_lem1__15__6: SNo (g u (g x2 z)) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__15__6.
(** Conj_mul_SNo_assoc_lem1__17__0 TMWedQg5CTC7ex2qFLyh3WZun2S5CvtZppW bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__17__0.
Variable g:(set -> (set -> set)).
Variable x:set.
Variable y:set.
Variable z:set.
Variable w:set.
Variable u:set.
Variable v:set.
Variable x2:set.
Variable y2:set.
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
Hypothesis H20: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H21: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Hypothesis H28: SNo (g u v).
Hypothesis H29: SNo (g u x2).
Hypothesis H30: SNo (g u y).
Theorem Conj_mul_SNo_assoc_lem1__17__0: SNo (g x2 z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__17__0.
(** Conj_mul_SNo_assoc_lem1__17__2 TMW4cHKhGeVSoDs8o9MKboxwjgkF7HcmLKi bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__17__2.
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
Hypothesis H20: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H21: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Hypothesis H28: SNo (g u v).
Hypothesis H29: SNo (g u x2).
Hypothesis H30: SNo (g u y).
Theorem Conj_mul_SNo_assoc_lem1__17__2: SNo (g x2 z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__17__2.
(** Conj_mul_SNo_assoc_lem1__17__14 TMWJwMJWR15yeki7TxMRQhNDYjo5YENFH1V bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__17__14.
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
Hypothesis H15: u :e SNoS_ (SNoLev x).
Hypothesis H16: SNo v.
Hypothesis H17: x2 :e SNoS_ (SNoLev y).
Hypothesis H18: y2 :e SNoS_ (SNoLev z).
Hypothesis H19: w = g u (g y z) + g x v + - (g u v).
Hypothesis H20: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H21: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Hypothesis H28: SNo (g u v).
Hypothesis H29: SNo (g u x2).
Hypothesis H30: SNo (g u y).
Theorem Conj_mul_SNo_assoc_lem1__17__14: SNo (g x2 z) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__17__14.
(** Conj_mul_SNo_assoc_lem1__18__24 TMYPtSgqDEFm4NbTPaDe1sr88v4ZMUEHije bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__18__24.
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
Hypothesis H20: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H21: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Hypothesis H28: SNo (g u v).
Hypothesis H29: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem1__18__24: SNo (g u y) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__18__24.
(** Conj_mul_SNo_assoc_lem1__18__27 TMR3Xczm7LHwMZp8fFPDwDaHkeHYkCdxsPP bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__18__27.
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
Hypothesis H20: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H21: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H28: SNo (g u v).
Hypothesis H29: SNo (g u x2).
Theorem Conj_mul_SNo_assoc_lem1__18__27: SNo (g u y) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__18__27.
(** Conj_mul_SNo_assoc_lem1__19__13 TMbQw1uPYngB8ZEjaNZREXfTr4Aj8YNm2My bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__19__13.
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
Hypothesis H20: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H21: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Hypothesis H28: SNo (g u v).
Theorem Conj_mul_SNo_assoc_lem1__19__13: SNo (g u x2) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__19__13.
(** Conj_mul_SNo_assoc_lem1__20__5 TMUY5RTGyX3sZPo9pFK7rSa4VY51kTP6vm5 bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__20__5.
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
Hypothesis H20: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H21: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Theorem Conj_mul_SNo_assoc_lem1__20__5: SNo (g u v) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__20__5.
(** Conj_mul_SNo_assoc_lem1__20__23 TMc5P4U3d4PGbJGEDfdS6UC3svi4KFgbvsS bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__20__23.
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
Hypothesis H20: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H21: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H22: SNo u.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Hypothesis H26: SNo (g x v).
Hypothesis H27: SNo (g x x2).
Theorem Conj_mul_SNo_assoc_lem1__20__23: SNo (g u v) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__20__23.
(** Conj_mul_SNo_assoc_lem1__22__14 TMRXTNTyEoHqgUsZCWbvERiFkvDA8pfrZ5S bounty of about 25 bars **)
Section Conj_mul_SNo_assoc_lem1__22__14.
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
Hypothesis H15: u :e SNoS_ (SNoLev x).
Hypothesis H16: SNo v.
Hypothesis H17: x2 :e SNoS_ (SNoLev y).
Hypothesis H18: y2 :e SNoS_ (SNoLev z).
Hypothesis H19: w = g u (g y z) + g x v + - (g u v).
Hypothesis H20: (g u (g x2 z + g y y2) + g x (v + g x2 y2)) <= g x (g x2 z + g y y2) + g u (v + g x2 y2).
Hypothesis H21: (g (g u y + g x x2) z + g (g x y + g u x2) y2) < g (g x y + g u x2) z + g (g u y + g x x2) y2.
Hypothesis H22: SNo u.
Hypothesis H23: SNo x2.
Hypothesis H24: SNo y2.
Hypothesis H25: SNo (g u (g y z)).
Theorem Conj_mul_SNo_assoc_lem1__22__14: SNo (g x v) -> w < g (g x y) z.
Admitted.

End Conj_mul_SNo_assoc_lem1__22__14.
