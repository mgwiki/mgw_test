Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
End Eq.
Infix = 502 := eq.

Section Ex.
Variable A:SType.
Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.
End Ex.
(* Unicode exists "2203" *)
Binder+ exists , := ex.

(* Parameter Eps_i "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" *)
Parameter Eps_i : (set->prop)->set.

Parameter Empty : set.

(* Parameter ordsucc "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "65d8837d7b0172ae830bed36c8407fcd41b7d875033d2284eb2df245b42295a6" *)
Parameter ordsucc : set -> set.

Notation Nat Empty ordsucc.

(* Parameter nat_p "25c483dc8509e17d4b6cf67c5b94c2b3f3902a45c3c34582da3e29ab1dc633ab" "458be3a74fef41541068991d6ed4034dc3b5e637179369954ba21f6dff4448e4" *)
Parameter nat_p : set -> prop.

(* Parameter add_nat "e4d45122168d3fb3f5723ffffe4d368988a1be62792f272e949c6728cec97865" "afa8ae66d018824f39cfa44fb10fe583334a7b9375ac09f92d622a4833578d1a" *)
Parameter add_nat : set -> set -> set.
Infix + 360 right := add_nat.

(* Parameter TwoRamseyProp "aab220c89625a268d769430a9bd1c5242495f378775d11b8e61bd9148d917e80" "c5d86cf97e40aa1fd6c7b0939b0974f704b1c792393b364c520e0e4558842cf6" *)
Parameter TwoRamseyProp : set -> set -> set -> prop.

Axiom TwoRamseyProp_2 : forall n, TwoRamseyProp 2 n n.

Axiom TwoRamseyProp_3_4_9 : TwoRamseyProp 3 4 9.

Axiom nat_4 : nat_p 4.
Axiom nat_8 : nat_p 8.

Axiom add_nat_8_4 : 8 + 4 = 12.

Axiom TwoRamseyProp_bd : forall r s m n,
    nat_p m -> nat_p n
 -> TwoRamseyProp (ordsucc r) s (ordsucc m)
 -> TwoRamseyProp r (ordsucc s) (ordsucc n)
 -> TwoRamseyProp (ordsucc r) (ordsucc s) (ordsucc (ordsucc (m + n))).

Theorem TwoRamseyProp_3_5_14 : TwoRamseyProp 3 5 14.
prove TwoRamseyProp (ordsucc 2) (ordsucc 4) (ordsucc (ordsucc 12)).
rewrite <- add_nat_8_4.
prove TwoRamseyProp (ordsucc 2) (ordsucc 4) (ordsucc (ordsucc (8 + 4))).
apply TwoRamseyProp_bd 2 4 8 4 nat_8 nat_4.
- prove TwoRamseyProp (ordsucc 2) 4 (ordsucc 8).
  prove TwoRamseyProp 3 4 9.
  exact TwoRamseyProp_3_4_9.
- prove TwoRamseyProp 2 (ordsucc 4) (ordsucc 4).
  prove TwoRamseyProp 2 5 5.
  exact TwoRamseyProp_2 5.
Qed.
