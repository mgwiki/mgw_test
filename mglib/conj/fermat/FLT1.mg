(** $I sig/FLTPreamble1.mgs **)

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix ^ 342 right := exp_SNo_nat.
(* Unicode <= "2264" *)
Infix < 490 := SNoLt.
Infix <= 490 := SNoLe.

Theorem FermatsLastTheorem: forall n :e int, 2 < n -> forall x y z :e int, x ^ n + y ^ n = z ^ n -> x = 0 \/ y = 0 \/ z = 0.
Admitted.

Theorem FermatsLastTheorem3: forall x y z :e int, x ^ 3 + y ^ 3 = z ^ 3 -> x = 0 \/ y = 0 \/ z = 0.
Admitted.

Theorem FermatsLastTheorem4: forall x y z :e int, x ^ 4 + y ^ 4 = z ^ 4 -> x = 0 \/ y = 0 \/ z = 0.
Admitted.

Theorem FermatsLastTheoremReduction:
    (forall x y z :e int, x ^ 3 + y ^ 3 = z ^ 3 -> x = 0 \/ y = 0 \/ z = 0)
 -> (forall x y z :e int, x ^ 4 + y ^ 4 = z ^ 4 -> x = 0 \/ y = 0 \/ z = 0)
 -> (forall p, prime_nat p -> 5 <= p -> forall x y z :e int, x ^ p + y ^ p = z ^ p -> x = 0 \/ y = 0 \/ z = 0)
 -> (forall n :e int, 2 < n -> forall x y z :e int, x ^ n + y ^ n = z ^ n -> x = 0 \/ y = 0 \/ z = 0).
 Admitted.
 
