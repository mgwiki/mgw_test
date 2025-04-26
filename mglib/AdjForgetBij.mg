Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.

Axiom FalseE : False -> forall p:prop, p.

Definition not : prop -> prop := fun A:prop => A -> False.

(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.

Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.

(* Unicode /\ "2227" *)
Infix /\ 780 left := and.

Axiom andI : forall (A B : prop), A -> B -> A /\ B.

Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.

(* Unicode \/ "2228" *)
Infix \/ 785 left := or.

Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
Definition neq : A->A->prop := fun x y:A => ~ eq x y.
End Eq.

Infix = 502 := eq.
(* Unicode <> "2260" *)
Infix <> 502 := neq.

Section Ex.
Variable A:SType.
Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.
End Ex.

Axiom prop_ext_2 : forall p q:prop, (p -> q) -> (q -> p) -> p = q.

Parameter In:set->set->prop.

Definition Subq : set -> set -> prop := fun A B => forall x :e A, x :e B.

(* Unicode exists "2203" *)
Binder+ exists , := ex; and.

Definition nIn : set->set->prop :=
fun x X => ~In x X.

(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.

Parameter Empty : set.

Axiom EmptyE : forall x:set, x /:e Empty.

(* Parameter Sing "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" "bd01a809e97149be7e091bf7cbb44e0c2084c018911c24e159f585455d8e6bd0" *)
Parameter Sing : set -> set.
Notation SetEnum1 Sing.

Axiom SingE : forall x y:set, y :e {x} -> y = x. 

(* Parameter ordsucc "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "65d8837d7b0172ae830bed36c8407fcd41b7d875033d2284eb2df245b42295a6" *)
Parameter ordsucc : set->set.

Notation Nat Empty ordsucc.

Axiom neq_ordsucc_0 : forall a:set, ordsucc a <> 0.
Axiom eq_1_Sing0 : 1 = {0}.

(* Parameter nat_p "25c483dc8509e17d4b6cf67c5b94c2b3f3902a45c3c34582da3e29ab1dc633ab" "458be3a74fef41541068991d6ed4034dc3b5e637179369954ba21f6dff4448e4" *)
Parameter nat_p : set->prop.

Axiom nat_0 : nat_p 0.
Axiom nat_1 : nat_p 1.
Axiom nat_inv : forall n, nat_p n -> n = 0 \/ exists x, nat_p x /\ n = ordsucc x.

(* Parameter omega "39cdf86d83c7136517f803d29d0c748ea45a274ccbf9b8488f9cda3e21f4b47c" "6fc30ac8f2153537e397b9ff2d9c981f80c151a73f96cf9d56ae2ee27dfd1eb2" *)
Parameter omega:set.

Axiom omega_nat_p : forall n :e omega, nat_p n.
Axiom nat_p_omega : forall n:set, nat_p n -> n :e omega.
Axiom omega_ordsucc : forall n :e omega, ordsucc n :e omega.

(* Parameter nat_primrec "9161ec45669e68b6f032fc9d4d59e7cf0b3f5f860baeb243e29e767a69d600b1" "3be1c5f3e403e02caebeaf6a2b30d019be74b996581a62908316c01702a459df" *)
Parameter nat_primrec : set -> (set -> set -> set) -> set -> set.

(* Parameter If_i "8c8f550868df4fdc93407b979afa60092db4b1bb96087bc3c2f17fadf3f35cbf" "b8ff52f838d0ff97beb955ee0b26fad79602e1529f8a2854bda0ecd4193a8a3c" *)
Parameter If_i : prop->set->set->set.

Notation IfThenElse If_i.

Axiom If_i_0 : forall p:prop, forall x y:set,
~ p -> (if p then x else y) = y.

Axiom If_i_1 : forall p:prop, forall x y:set,
p -> (if p then x else y) = x.

(* Parameter lam "93592da87a6f2da9f7eb0fbd449e0dc4730682572e0685b6a799ae16c236dcae" "8acbb2b5de4ab265344d713b111d82b0048c8a4bf732a67ad35f1054a4eb4642" *)
Parameter lam : set -> (set -> set) -> set.

Definition setprod : set->set->set := fun X Y:set => lam X (fun _ => Y).

(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.

(* Parameter ap "58c1782da006f2fb2849c53d5d8425049fad551eb4f8025055d260f0c9e1fe40" "c7aaa670ef9b6f678b8cf10b13b2571e4dc1e6fde061d1f641a5fa6c30c09d46" *)
Parameter ap : set -> set -> set.

Notation SetImplicitOp ap.
Notation SetLam lam.

Axiom beta : forall X:set, forall F:set -> set, forall x:set, x :e X -> (fun x :e X => F x) x = F x.

Definition lam_id : set -> set := fun X => lam X (fun x => x).

Definition lam_comp : set -> set -> set -> set :=
 fun X g f => lam X (fun x : set => g (f x)).

Definition struct_id : set -> set := fun X => lam_id (X 0).

Definition struct_comp : set -> set -> set -> set -> set -> set := fun X Y Z f g => lam_comp (X 0) f g.

Axiom lam_ext: forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> (fun x :e X => F x) = (fun x :e X => G x).

(* Parameter Pi "8ab5fa18b3cb4b4b313a431cc37bdd987f036cc47f175379215f69af5977eb3b" "40f1c38f975e69e2ae664b3395551df5820b0ba6a93a228eba771fc2a4551293" *)
Parameter Pi : set -> (set -> set) -> set.

(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

Axiom lam_Pi : forall X:set, forall Y:set -> set, forall F:set -> set,
 (forall x :e X, F x :e Y x) -> (fun x :e X => F x) :e (Pi_ x :e X, Y x).
Axiom ap_Pi : forall X:set, forall Y:set -> set, forall f:set, forall x:set, f :e (Pi_ x :e X, Y x) -> x :e X -> f x :e Y x.

Definition setexp : set->set->set := fun Y X:set => Pi_ x :e X, Y.

(* Superscript :^: *)
Infix :^: 430 left := setexp.

Definition HomSet : set -> set -> set -> prop := fun X Y f => f :e Y :^: X.

Definition bij : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall u v :e X, f u = f v -> u = v)
  /\
  (forall w :e Y, exists u :e X, f u = w).

Axiom bijI : forall X Y, forall f:set -> set,
    (forall u :e X, f u :e Y)
 -> (forall u v :e X, f u = f v -> u = v)
 -> (forall w :e Y, exists u :e X, f u = w)
 -> bij X Y f.

Axiom bijE : forall X Y, forall f:set -> set,
    bij X Y f
 -> forall p:prop,
      ((forall u :e X, f u :e Y)
    -> (forall u v :e X, f u = f v -> u = v)
    -> (forall w :e Y, exists u :e X, f u = w)
    -> p)
   -> p.

(* Parameter inv "e1e47685e70397861382a17f4ecc47d07cdab63beca11b1d0c6d2985d3e2d38b" "896fa967e973688effc566a01c68f328848acd8b37e857ad23e133fdd4a50463" *)
Parameter inv : set -> (set -> set) -> set -> set.

Axiom surj_rinv : forall X Y, forall f:set->set, (forall w :e Y, exists u :e X, f u = w) -> forall y :e Y, inv X f y :e X /\ f (inv X f y) = y.

Axiom inj_linv : forall X, forall f:set->set, (forall u v :e X, f u = f v -> u = v) -> forall x :e X, inv X f (f x) = x.

Axiom bij_inv : forall X Y, forall f:set->set, bij X Y f -> bij Y X (inv X f).

Axiom ap0_lam : forall X:set, forall Y:set -> set, forall z:set, z :e (fun x :e X => Y x) -> (z 0) :e X.

Axiom ap1_lam : forall X:set, forall Y:set -> set, forall z:set, z :e (fun x :e X => Y x) -> (z 1) :e (Y (z 0)).

Axiom tuple_2_inj : forall x y w z:set, (x,y) = (w,z) -> x = w /\ y = z.
Axiom tuple_2_setprod : forall X:set, forall Y:set, forall x :e X, forall y :e Y, (x,y) :e X :*: Y.
Axiom tuple_lam_eta : forall X:set, forall Y:set -> set, forall z :e (fun x :e X => Y x), (z 0,z 1) = z.

Section Tuples.

Variable x0 x1: set.
Axiom tuple_2_0_eq: (x0,x1) 0 = x0.

Axiom tuple_2_1_eq: (x0,x1) 1 = x1.

End Tuples.

(* Parameter ordinal "dab6e51db9653e58783a3fde73d4f2dc2637891208c92c998709e8795ba4326f" "ee28d96500ca4c012f9306ed26fad3b20524e7a89f9ac3210c88be4e6a7aed23" *)
Parameter ordinal : set->prop.

Axiom ordinal_Empty : ordinal Empty.
Axiom nat_p_ordinal : forall n:set, nat_p n -> ordinal n.
Axiom ordinal_ordsucc : forall alpha:set, ordinal alpha -> ordinal (ordsucc alpha).

(* Parameter SNo "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" "11faa7a742daf8e4f9aaf08e90b175467e22d0e6ad3ed089af1be90cfc17314b" *)
Parameter SNo : set -> prop.

(* Parameter SNoLt "0d574978cbb344ec3744139d5c1d0d90336d38f956e09a904d230c4fa06b30d1" "46e7ed0ee512360f08f5e5f9fc40a934ff27cfd0c79d3c2384e6fb16d461bd95" *)
Parameter SNoLt : set -> set -> prop.
(* Parameter SNoLe "09cdd0b9af76352f6b30bf3c4bca346eaa03d280255f13afb2e73fe8329098b6" "ddf7d378c4df6fcdf73e416f8d4c08965e38e50abe1463a0312048d3dd7ac7e9" *)
Parameter SNoLe : set -> set -> prop.
(* Parameter minus_SNo "6d39c64862ac40c95c6f5e4ed5f02bb019279bfb0cda8c9bbe0e1b813b1e876c" "268a6c1da15b8fe97d37be85147bc7767b27098cdae193faac127195e8824808" *)
Parameter minus_SNo : set -> set.
(* Parameter add_SNo "29b9b279a7a5b776b777d842e678a4acaf3b85b17a0223605e4cc68025e9b2a7" "127d043261bd13d57aaeb99e7d2c02cae2bd0698c0d689b03e69f1ac89b3c2c6" *)
Parameter add_SNo : set -> set -> set.

Infix < 490 := SNoLt.
Infix <= 490 := SNoLe.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.

Axiom SNoLt_irref : forall x, ~(x < x).
Axiom SNoLt_tra : forall x y z, SNo x -> SNo y -> SNo z -> x < y -> y < z -> x < z.

Axiom SNoLeE : forall x y, SNo x -> SNo y -> x <= y -> x < y \/ x = y.

Axiom SNo_0 : SNo 0.
Axiom SNo_1 : SNo 1.

Axiom SNoLt_0_1 : 0 < 1.

Axiom SNo_minus_SNo : forall x, SNo x -> SNo (- x).
Axiom SNo_add_SNo : forall x y, SNo x -> SNo y -> SNo (x + y).

Axiom minus_SNo_0 : - 0 = 0.
Axiom minus_SNo_invol : forall x, SNo x -> - - x = x.
Axiom add_SNo_0R : forall x, SNo x -> x + 0 = x.
Axiom add_SNo_com : forall x y, SNo x -> SNo y -> x + y = y + x.
Axiom add_SNo_Lt2 : forall x y z, SNo x -> SNo y -> SNo z -> y < z -> x + y < x + z.
Axiom add_SNo_Lt2_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y < x + z -> y < z.

Axiom add_SNo_cancel_L : forall x y z, SNo x -> SNo y -> SNo z -> x + y = x + z -> y = z.

Axiom add_SNo_cancel_R : forall x y z, SNo x -> SNo y -> SNo z -> x + y = z + y -> x = z.

Axiom add_SNo_minus_SNo_rinv : forall x, SNo x -> x + -x = 0.
Axiom minus_add_SNo_distr : forall x y, SNo x -> SNo y -> -(x+y) = (-x) + (-y).

Axiom add_SNo_minus_SNo_prop2 : forall x y, SNo x -> SNo y -> x + - x + y = y.

Axiom add_SNo_minus_R2' : forall x y, SNo x -> SNo y -> (x + - y) + y = x.

Axiom minus_SNo_Lt_contra : forall x y, SNo x -> SNo y -> x < y -> - y < - x.
Axiom minus_SNo_Lt_contra3 : forall x y, SNo x -> SNo y -> -x < -y -> y < x.

Axiom ordinal_SNo : forall alpha, ordinal alpha -> SNo alpha.
Axiom ordinal_SNoLt_In : forall alpha beta, ordinal alpha -> ordinal beta -> alpha < beta -> alpha :e beta.

Axiom ordinal_ordsucc_SNo_eq : forall alpha, ordinal alpha -> ordsucc alpha = 1 + alpha.

(* Parameter int "f7cd39d139f71b389f61d3cf639bf341d01dac1be60ad65b40ee3aa5218e0043" "90ee851305d1ba4b80424ec6e2760ebabb1fd3e399fcb5c6b5c814d898138c16" *)
Parameter int : set.

Axiom nat_p_int : forall n, nat_p n -> n :e int.
Axiom int_SNo : forall x :e int, SNo x.
Axiom Subq_omega_int : omega c= int.
Axiom int_minus_SNo: forall x :e int, - x :e int.
Axiom int_add_SNo: forall x y :e int, x + y :e int.

(* Parameter pack_u "9575c80a2655d3953184d74d13bd5860d4f415acbfc25d279378b4036579af65" "119d13725af3373dd508f147836c2eff5ff5acf92a1074ad6c114b181ea8a933" *)
Parameter pack_u : set -> (set -> set) -> set.

(* Parameter unpack_u_i "4e62ce5c996f13a11eb05d8dbff98e7acceaca2d3b3a570bea862ad74b79f4df" "111dc52d4fe7026b5a4da1edbfb7867d219362a0e5da0682d7a644a362d95997" *)
Parameter unpack_u_i : set -> (set -> (set -> set) -> set) -> set.

Axiom unpack_u_i_eq : forall Phi:set -> (set -> set) -> set,
  forall X, forall F:set -> set,
  (forall F':set -> set, (forall x :e X, F x = F' x) -> Phi X F' = Phi X F)
  ->
  unpack_u_i (pack_u X F) Phi = Phi X F.

(* Parameter unpack_u_o "22baf0455fa7619b6958e5bd762f4085bae580997860844329722650209d24bf" "eb32c2161bb5020efad8203cd45aa4738a4908823619b55963cc2fd1f9830098" *)
Parameter unpack_u_o : set -> (set -> (set -> set) -> prop) -> prop.

Axiom unpack_u_o_eq : forall Phi:set -> (set -> set) -> prop,
  forall X, forall F:set -> set,
  (forall F':set -> set, (forall x :e X, F x = F' x) -> Phi X F' = Phi X F)
  ->
  unpack_u_o (pack_u X F) Phi = Phi X F.

Axiom pack_u_0_eq2 : forall X, forall F:set -> set, X = pack_u X F 0.

Definition struct_u : set -> prop := fun S => forall q:set -> prop, (forall X, forall F:set -> set, (forall x :e X, F x :e X) -> q (pack_u X F)) -> q S.

Axiom pack_struct_u_I: forall X, forall F:set -> set, (forall x :e X, F x :e X) -> struct_u (pack_u X F).

(* Parameter Hom_struct_u "96edb4f2610efd412654278db08e16550670a674fc2dc2b8ce6e73dcc46bbeab" "9579111144263dda4d1a69686bd1cd9e0ef4ffaecf2b279cf431d0a9e36f67ab" *)
Parameter Hom_struct_u : set -> set -> set -> prop.

Axiom Hom_struct_u_pack :
 forall X Y, forall opX opY:set -> set,
 forall f,
    (Hom_struct_u (pack_u X opX) (pack_u Y opY) f)
  = (f :e Y :^: X /\ (forall x :e X, f (opX x) = opY (f x))).

Definition struct_u_bij : set -> prop
 := fun X => struct_u X /\ unpack_u_o X (fun X' h => bij X' X' (fun x => h x)).

(* Parameter MetaCat "9b2dee6442140d530f300f187f315d389cfa416a087e15c1677d3bf02f85f063" "fd9743c836fc84a35eca7120bf513d8be118e8eff433fbcc8ca5369662cda164" *)
Parameter MetaCat : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> prop.

Axiom MetaCatSet : MetaCat (fun _ => True) HomSet (fun X => lam_id X) (fun X Y Z g f => lam_comp X g f).
Axiom MetaCat_struct_u_bij: MetaCat struct_u_bij Hom_struct_u struct_id struct_comp.

(* Parameter MetaFunctor "3f1821f85d08e8012e699b09efeb0773942fcc2adacfea48bc8f23b31eb6673d" "f35b679c6bab1e6cf0fdcf922094790594854b8da194ab1c6b10991183d51c1a" *)
Parameter MetaFunctor : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> prop.

Axiom MetaFunctor_I :
 forall C0 : set -> prop, forall C1 : set -> set -> set -> prop,
  forall idC : set -> set, forall compC : set -> set -> set -> set -> set -> set,
 forall D0 : set -> prop, forall D1 : set -> set -> set -> prop,
  forall idD : set -> set, forall compD : set -> set -> set -> set -> set -> set,
 forall F0 : set -> set, forall F1 : set -> set -> set -> set,
     (forall X, C0 X -> D0 (F0 X))
  -> (forall X Y f, C0 X -> C0 Y -> C1 X Y f -> D1 (F0 X) (F0 Y) (F1 X Y f))
  -> (forall X, C0 X -> F1 X X (idC X) = idD (F0 X))
  -> (forall X Y Z f g, C0 X -> C0 Y -> C0 Z -> C1 X Y f -> C1 Y Z g
       -> F1 X Z (compC X Y Z g f) = compD (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f))
  -> MetaFunctor C0 C1 idC compC D0 D1 idD compD F0 F1.

Axiom MetaCat_struct_u_bij_Forgetful: MetaFunctor struct_u_bij Hom_struct_u
          struct_id struct_comp
          (fun _ => True) HomSet
          (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
          (fun X => X 0) (fun X Y f => f).

(* Parameter MetaFunctor_strict "dd69f4b569545c4beb1b440df404a181508406955eb862b17b28cf09de44afcf" "8085cf0170b86729cab30e095b013215757a3930981428ca9b33ed00255b3e5b" *)
Parameter MetaFunctor_strict : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> prop.

Axiom MetaFunctor_strict_I :
 forall C0 : set -> prop, forall C1 : set -> set -> set -> prop,
  forall idC : set -> set, forall compC : set -> set -> set -> set -> set -> set,
 forall D0 : set -> prop, forall D1 : set -> set -> set -> prop,
  forall idD : set -> set, forall compD : set -> set -> set -> set -> set -> set,
 forall F0 : set -> set, forall F1 : set -> set -> set -> set,
      MetaCat C0 C1 idC compC
   -> MetaCat D0 D1 idD compD
   -> MetaFunctor C0 C1 idC compC D0 D1 idD compD F0 F1
   -> MetaFunctor_strict C0 C1 idC compC D0 D1 idD compD F0 F1.

(* Parameter MetaNatTrans "8a2958081ef9384f7ae14223d1b2eae8a7b40e054a6e8404700b3282c5cc73fc" "cf0ad1ee32827718afb13bd3eaf6f0a23dac224e237a5287cf6770bed71314d0" *)
Parameter MetaNatTrans : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> (set -> set) -> prop.

Axiom MetaNatTrans_I :
  forall C0 : set -> prop, forall C1 : set -> set -> set -> prop,
   forall idC : set -> set, forall compC : set -> set -> set -> set -> set -> set,
  forall D0 : set -> prop, forall D1 : set -> set -> set -> prop,
   forall idD : set -> set, forall compD : set -> set -> set -> set -> set -> set,
  forall F0 : set -> set, forall F1 : set -> set -> set -> set,
  forall G0 : set -> set, forall G1 : set -> set -> set -> set,
  forall eta : set -> set,
      (forall X, C0 X -> D1 (F0 X) (G0 X) (eta X))
   -> (forall X Y f, C0 X -> C0 Y -> C1 X Y f
         -> compD (F0 X) (G0 X) (G0 Y) (G1 X Y f) (eta X) = compD (F0 X) (F0 Y) (G0 Y) (eta Y) (F1 X Y f))
   -> MetaNatTrans C0 C1 idC compC D0 D1 idD compD F0 F1 G0 G1 eta.

(* Parameter MetaAdjunction "cecdcdbb34d99cbd63719b23fce489fa60013beaacbc82f82b45e1606f0d1426" "e8b6c46a7320708ff26c3ecf5b9d4028cd895a2df98bc04c5a259452e7b00b34" *)
Parameter MetaAdjunction : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> (set -> set) -> (set -> set) -> prop.

Axiom MetaAdjunction_I :
  forall C0 : set -> prop, forall C1 : set -> set -> set -> prop,
   forall idC : set -> set, forall compC : set -> set -> set -> set -> set -> set,
  forall D0 : set -> prop, forall D1 : set -> set -> set -> prop,
   forall idD : set -> set, forall compD : set -> set -> set -> set -> set -> set,
  forall F0 : set -> set, forall F1 : set -> set -> set -> set,
  forall G0 : set -> set, forall G1 : set -> set -> set -> set,
  forall eta eps : set -> set,
      (forall X, C0 X -> compD (F0 X) (F0 (G0 (F0 X))) (F0 X) (eps (F0 X)) (F1 X (G0 (F0 X)) (eta X)) = idD (F0 X))
   -> (forall Y, D0 Y -> compC (G0 Y) (G0 (F0 (G0 Y))) (G0 Y) (G1 (F0 (G0 Y)) Y (eps Y)) (eta (G0 Y)) = idC (G0 Y))
   -> MetaAdjunction C0 C1 idC compC D0 D1 idD compD F0 F1 G0 G1 eta eps.

(* Parameter MetaAdjunction_strict "be3dc11d683b255bfbd9127adb3c6087d074a17cb0e31c91d602b5ae49893e97" "c8ed7d3ad63a4a29ebc88ac0ccb02bfd5f4c0141eebc8a7a349ed7115a3a3eb9" *)
Parameter MetaAdjunction_strict : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> (set -> set) -> (set -> set) -> prop.
 
Axiom MetaAdjunction_strict_I :
  forall C0 : set -> prop, forall C1 : set -> set -> set -> prop,
   forall idC : set -> set, forall compC : set -> set -> set -> set -> set -> set,
  forall D0 : set -> prop, forall D1 : set -> set -> set -> prop,
   forall idD : set -> set, forall compD : set -> set -> set -> set -> set -> set,
  forall F0 : set -> set, forall F1 : set -> set -> set -> set,
  forall G0 : set -> set, forall G1 : set -> set -> set -> set,
  forall eta eps : set -> set,
      MetaFunctor_strict C0 C1 idC compC D0 D1 idD compD F0 F1
   -> MetaFunctor D0 D1 idD compD C0 C1 idC compC G0 G1
   -> MetaNatTrans C0 C1 idC compC C0 C1 idC compC (fun X : set => X) (fun X Y f : set => f) (fun X : set => G0 (F0 X)) (fun X Y f : set => G1 (F0 X) (F0 Y) (F1 X Y f)) eta
   -> MetaNatTrans D0 D1 idD compD D0 D1 idD compD (fun A : set => F0 (G0 A)) (fun A B h : set => F1 (G0 A) (G0 B) (G1 A B h)) (fun A : set => A) (fun A B h : set => h) eps
   -> MetaAdjunction C0 C1 idC compC D0 D1 idD compD F0 F1 G0 G1 eta eps
   -> MetaAdjunction_strict C0 C1 idC compC D0 D1 idD compD F0 F1 G0 G1 eta eps.

Definition omega_iterate : set -> (set -> set) -> set -> set :=
  fun n h x => nat_primrec x (fun _ r => h r) n.

Axiom omega_iterate_0: forall h:set -> set, forall x, omega_iterate 0 h x = x.

Axiom omega_iterate_S_out: forall n :e omega, forall h:set -> set, forall x, omega_iterate (ordsucc n) h x = h (omega_iterate n h x).

Axiom omega_iterate_In: forall X, forall x :e X,
    forall h:set -> set, (forall x :e X, h x :e X)
 -> forall n, nat_p n -> omega_iterate n h x :e X.

Axiom omega_iterate_ext: forall X, forall x :e X,
    forall h h':set -> set, (forall x :e X, h x :e X) -> (forall x :e X, h x = h' x)
 -> forall n, nat_p n -> omega_iterate n h x = omega_iterate n h' x.

Axiom omega_iterate_comm : forall X, forall x :e X,
    forall h k:set -> set, (forall x :e X, h x :e X)
 -> forall f:set -> set, (forall x :e X, f (h x) = k (f x))
 -> forall n, nat_p n -> f (omega_iterate n h x) = omega_iterate n k (f x).

Axiom omega_iterate_pair_count1 : forall x,
  forall n, nat_p n -> omega_iterate n (fun u => (ordsucc (u 0),u 1)) (0,x) = (n,x).

Axiom omega_iterate_pair_countback1 : forall x,
  forall n, nat_p n -> omega_iterate n (fun u => (u 0 + - 1,u 1)) (0,x) = (- n,x).

Definition MetaCat_struct_u_forgetfree_eta: set -> set
 := fun X => fun x :e X => (0,x).

Axiom int_neg_or_nonneg: forall x :e int,
 forall p:prop,
     (x < 0 -> - x :e omega -> p)
  -> (0 <= x -> ~(x < 0) -> x :e omega -> p)
  -> p.

Definition MetaCat_struct_u_bij_free0: set -> set
 := fun X => pack_u (int :*: X) (fun u => (u 0 + 1,u 1)).

Definition MetaCat_struct_u_bij_free1: set -> set -> set -> set
 := fun X Y h => fun u :e int :*: X => (u 0,h (u 1)).

Definition MetaCat_struct_u_bij_forgetfree_eps: set -> set
 := fun A => unpack_u_i A (fun X h => fun u :e int :*: X => if u 0 < 0 then omega_iterate (- (u 0)) (inv X h) (u 1) else omega_iterate (u 0) h (u 1)).

Theorem MetaCat_struct_u_bij_forgetfree:
  MetaAdjunction_strict
       (fun _ => True) HomSet
       (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
       struct_u_bij Hom_struct_u struct_id struct_comp
       MetaCat_struct_u_bij_free0
       MetaCat_struct_u_bij_free1
       (fun X => X 0) (fun X Y f => f)
       MetaCat_struct_u_forgetfree_eta
       MetaCat_struct_u_bij_forgetfree_eps.
set F0 : set -> set := fun X => pack_u (int :*: X) (fun u => (u 0 + 1,u 1)).
set F1 : set -> set -> set -> set := fun X Y h => fun u :e int :*: X => (u 0,h (u 1)).
set eta : set -> set := fun X => fun x :e X => (0,x).
set epsPhi : set -> (set -> set) -> set := fun X h => fun u :e int :*: X => if u 0 < 0 then omega_iterate (- (u 0)) (inv X h) (u 1) else omega_iterate (u 0) h (u 1).
set eps : set -> set := fun A => unpack_u_i A epsPhi.
(** F X is omega x X with injection (n,x) |-> (ordsucc n,x) **)
(** eta_X : X -> U (F X) by eta_X x = (0,x) **)
(** eps_A : F (U A) -> A where A = (X,h) by eps_A (n,x) = h^n x **)
prove MetaAdjunction_strict
       (fun _ => True) HomSet
       (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
       struct_u_bij Hom_struct_u struct_id struct_comp
       F0 F1
       (fun X => X 0) (fun X Y f => f)
       eta eps.
claim L1: forall X, forall u :e int :*: X, (u 0 + 1,u 1) :e int :*: X.
{ let X u. assume Hu.
  apply tuple_2_setprod int X.
  - prove u 0 + 1 :e int.
    apply int_add_SNo.
    + exact ap0_lam int (fun _ => X) u Hu.
    + exact nat_p_int 1 nat_1.
  - prove u 1 :e X.
    exact ap1_lam int (fun _ => X) u Hu.
}
claim L1b: forall X, bij (int :*: X) (int :*: X) (fun u => (u 0 + 1,u 1)).
{ let X. apply bijI.
  - exact L1 X.
  - let u. assume Hu. let v. assume Hv.
    assume H1: (u 0 + 1,u 1) = (v 0 + 1,v 1).
    prove u = v.
    apply tuple_2_inj (u 0 + 1) (u 1) (v 0 + 1) (v 1) H1.
    assume H2: u 0 + 1 = v 0 + 1.
    assume H3: u 1 = v 1.
    rewrite <- tuple_lam_eta int (fun _ => X) u Hu.
    rewrite <- tuple_lam_eta int (fun _ => X) v Hv.
    prove (u 0,u 1) = (v 0,v 1).
    claim Lu0: u 0 :e int.
    { exact ap0_lam int (fun _ => X) u Hu. }
    claim Lv0: v 0 :e int.
    { exact ap0_lam int (fun _ => X) v Hv. }
    rewrite add_SNo_cancel_R (u 0) 1 (v 0) (int_SNo (u 0) Lu0) SNo_1 (int_SNo (v 0) Lv0) H2.
    rewrite H3.
    reflexivity.
  - let w. assume Hw: w :e int :*: X.
    prove exists u :e int :*: X, (u 0 + 1,u 1) = w.
    claim Lw0: w 0 :e int.
    { exact ap0_lam int (fun _ => X) w Hw. }
    claim Lw1: w 1 :e X.
    { exact ap1_lam int (fun _ => X) w Hw. }
    witness (w 0 + - 1,w 1).
    apply andI.
    + prove (w 0 + - 1,w 1) :e int :*: X.
      apply tuple_2_setprod int X.
      * { prove w 0 + - 1 :e int.
	  apply int_add_SNo.
	  - exact Lw0.
	  - apply int_minus_SNo. apply nat_p_int. exact nat_1.
        }
      * prove w 1 :e X. exact Lw1.
    + rewrite tuple_2_0_eq. rewrite tuple_2_1_eq.
      prove ((w 0 + - 1) + 1,w 1) = w.
      rewrite add_SNo_minus_R2' (w 0) 1 (int_SNo (w 0) Lw0) SNo_1.
      prove (w 0,w 1) = w.
      exact tuple_lam_eta int (fun _ => X) w Hw.
} 
claim Letabeta: forall X, forall x :e X, eta X x = (0,x).
{ let X x. assume Hx. exact beta X (fun x => (0,x)) x Hx. }
set Phi : set -> (set -> set) -> prop := fun X' h => bij X' X' (fun x => h x).
claim LPhi1: forall X, forall h:set -> set,
   forall h':set -> set, (forall x :e X, h x = h' x) ->
      Phi X h -> Phi X h'.
{ let X h h'. assume Hhh'.
  assume Hh: bij X X h.
  apply bijE X X h Hh.
  assume Hh1 Hh2 Hh3.
  prove bij X X h'.
  apply bijI.
  - let x. assume Hx. prove h' x :e X.
    rewrite <- Hhh' x Hx.
    exact Hh1 x Hx.
  - let x. assume Hx. let y. assume Hy.
    prove h' x = h' y -> x = y.
    rewrite <- Hhh' x Hx.
    rewrite <- Hhh' y Hy.
    exact Hh2 x Hx y Hy.
  - let z. assume Hz: z :e X.
    prove exists x :e X, h' x = z.
    apply Hh3 z Hz.
    let x. assume H. apply H.
    assume Hx: x :e X.
    assume Hxz: h x = z.
    witness x. apply andI.
    + exact Hx.
    + prove h' x = z.
      rewrite <- Hhh' x Hx.
      exact Hxz.
}
claim L2: forall X, forall h:set -> set,
   forall h':set -> set, (forall x :e X, h x = h' x) ->
      (Phi X h') = (Phi X h).
{ let X h. let h'. assume Hhh'.
  apply prop_ext_2.
  - assume H1: Phi X h'.
    apply LPhi1 X h' h.
    + let x. assume Hx. symmetry. exact Hhh' x Hx.
    + exact H1.
  - exact LPhi1 X h h' Hhh'.
}
claim L3: forall X, forall h:set -> set, (forall x :e X, h x :e X) -> forall u :e omega :*: X, omega_iterate (u 0) h (u 1) :e X.
{ let X h. assume Hh. let u. assume Hu.
  exact omega_iterate_In X (u 1) (ap1_lam omega (fun _ => X) u Hu) h Hh (u 0) (omega_nat_p (u 0) (ap0_lam omega (fun _ => X) u Hu)).
}
claim L4: forall X, forall h:set -> set, bij X X h ->
   forall h':set -> set, (forall x :e X, h x = h' x) ->
      (epsPhi X h') = (epsPhi X h).
{ let X h. assume Hh. let h'. assume Hhh'.
  claim Lih: bij X X (inv X h).
  { exact bij_inv X X h Hh. }
  apply bijE X X h Hh.
  assume Hh1 Hh2 Hh3.
  apply bijE X X (inv X h) Lih.
  assume Hih1 Hih2 Hih3.
  claim Lh': bij X X h'.
  { exact LPhi1 X h h' Hhh' Hh. }
  apply bijE X X h' Lh'.
  assume Hh'1 Hh'2 Hh'3.
  claim Lih': bij X X (inv X h').
  { exact bij_inv X X h' Lh'. }
  apply bijE X X (inv X h') Lih'.
  assume Hih'1 Hih'2 Hih'3.
  prove (fun u :e int :*: X => if u 0 < 0 then omega_iterate (- (u 0)) (inv X h') (u 1) else omega_iterate (u 0) h' (u 1))
      = (fun u :e int :*: X => if u 0 < 0 then omega_iterate (- (u 0)) (inv X h) (u 1) else omega_iterate (u 0) h (u 1)).
  apply lam_ext.
  let u. assume Hu.
  symmetry.
  prove (if u 0 < 0 then omega_iterate (- (u 0)) (inv X h) (u 1) else omega_iterate (u 0) h (u 1))
      = (if u 0 < 0 then omega_iterate (- (u 0)) (inv X h') (u 1) else omega_iterate (u 0) h' (u 1)).
  claim Lu0: u 0 :e int.
  { exact ap0_lam int (fun _ => X) u Hu. }
  apply int_neg_or_nonneg (u 0) Lu0.
  - assume H1: u 0 < 0.
    assume H2: - u 0 :e omega.
    rewrite If_i_1 (u 0 < 0) (omega_iterate (- (u 0)) (inv X h) (u 1)) (omega_iterate (u 0) h (u 1)) H1.
    rewrite If_i_1 (u 0 < 0) (omega_iterate (- (u 0)) (inv X h') (u 1)) (omega_iterate (u 0) h' (u 1)) H1.
    prove omega_iterate (- (u 0)) (inv X h) (u 1)
        = omega_iterate (- (u 0)) (inv X h') (u 1).
    claim Lihih': forall x :e X, inv X h x = inv X h' x.
    { let x. assume Hx.
      prove inv X h x = inv X h' x.
      apply Hh2.
      - prove inv X h x :e X.
        exact Hih1 x Hx.
      - prove inv X h' x :e X.
        exact Hih'1 x Hx.
      - prove h (inv X h x) = h (inv X h' x).
        transitivity x, h' (inv X h' x).
	+ prove h (inv X h x) = x.
	  apply surj_rinv X X h Hh3 x Hx.
	  assume _ H. exact H.
	+ prove x = h' (inv X h' x).
	  symmetry.
	  apply surj_rinv X X h' Hh'3 x Hx.
	  assume _ H. exact H.
	+ prove h' (inv X h' x) = h (inv X h' x).
	  symmetry.
	  apply Hhh'.
	  prove inv X h' x :e X.
          exact Hih'1 x Hx.
    }
    exact omega_iterate_ext X (u 1) (ap1_lam int (fun _ => X) u Hu) (inv X h) (inv X h') Hih1 Lihih' (- u 0) (omega_nat_p (- u 0) H2).
  - assume H1: 0 <= u 0.
    assume H2: ~(u 0 < 0).
    assume H3: u 0 :e omega.
    rewrite If_i_0 (u 0 < 0) (omega_iterate (- (u 0)) (inv X h) (u 1)) (omega_iterate (u 0) h (u 1)) H2.
    rewrite If_i_0 (u 0 < 0) (omega_iterate (- (u 0)) (inv X h') (u 1)) (omega_iterate (u 0) h' (u 1)) H2.
    prove omega_iterate (u 0) h (u 1)
        = omega_iterate (u 0) h' (u 1).
    exact omega_iterate_ext X (u 1) (ap1_lam int (fun _ => X) u Hu) h h' Hh1 Hhh' (u 0) (omega_nat_p (u 0) H3).
}
claim Lepseq: forall X, forall h:set -> set, bij X X h
 -> eps (pack_u X h) = epsPhi X h.
{ let X h. assume Hh. exact unpack_u_i_eq epsPhi X h (L4 X h Hh). }
claim Lepsbetaint: forall X, forall h:set -> set, bij X X h
 -> forall n :e int, forall x :e X, eps (pack_u X h) (n,x) = if n < 0 then omega_iterate (- n) (inv X h) x else omega_iterate n h x.
{ let X h. assume Hh. let n. assume Hn. let x. assume Hx.
  prove eps (pack_u X h) (n,x) = if n < 0 then omega_iterate (- n) (inv X h) x else omega_iterate n h x.
  transitivity epsPhi X h (n,x),
               if (n,x) 0 < 0 then omega_iterate (- ((n,x) 0)) (inv X h) ((n,x) 1) else omega_iterate ((n,x) 0) h ((n,x) 1).
  - f_equal. exact Lepseq X h Hh.
  - exact beta (int :*: X) (fun u => if u 0 < 0 then omega_iterate (- (u 0)) (inv X h) (u 1) else omega_iterate (u 0) h (u 1)) (n,x) (tuple_2_setprod int X n Hn x Hx).
  - rewrite tuple_2_0_eq.
    rewrite tuple_2_1_eq.
    reflexivity.
}
claim Lepsbetanonneg: forall X, forall h:set -> set, bij X X h
 -> forall n :e omega, forall x :e X, eps (pack_u X h) (n,x) = omega_iterate n h x.
{ let X h. assume Hh. let n. assume Hn. let x. assume Hx.
  prove eps (pack_u X h) (n,x) = omega_iterate n h x.
  transitivity if n < 0 then omega_iterate (- n) (inv X h) x else omega_iterate n h x.
  - exact Lepsbetaint X h Hh n (Subq_omega_int n Hn) x Hx.
  - apply If_i_0.
    prove ~(n < 0).
    assume H1: n < 0.
    apply EmptyE n.
    prove n :e 0.
    exact ordinal_SNoLt_In n 0 (nat_p_ordinal n (omega_nat_p n Hn)) ordinal_Empty H1.
}
claim Lepsbetaneg: forall X, forall h:set -> set, bij X X h
 -> forall n :e int, n < 0 -> forall x :e X, eps (pack_u X h) (n,x) = omega_iterate (- n) (inv X h) x.
{ let X h. assume Hh. let n. assume Hn Hnneg. let x. assume Hx.
  prove eps (pack_u X h) (n,x) = omega_iterate (- n) (inv X h) x.
  transitivity if n < 0 then omega_iterate (- n) (inv X h) x else omega_iterate n h x.
  - exact Lepsbetaint X h Hh n Hn x Hx.
  - apply If_i_1. exact Hnneg.
}
claim LepsIn: forall X, forall h:set -> set, bij X X h
 -> forall n :e int, forall x :e X, eps (pack_u X h) (n,x) :e X.
{ let X h. assume Hh. let n. assume Hn. let x. assume Hx.
  apply bijE X X h Hh.
  assume Hh1 Hh2 Hh3.
  claim Lih: bij X X (inv X h).
  { exact bij_inv X X h Hh. }
  apply bijE X X (inv X h) Lih.
  assume Hih1 Hih2 Hih3.
  apply int_neg_or_nonneg n Hn.
  - assume H1: n < 0.
    assume H2: - n :e omega.
    prove eps (pack_u X h) (n,x) :e X.
    claim LepsIn1: omega_iterate (- n) (inv X h) x :e X.
    { exact omega_iterate_In X x Hx (inv X h) Hih1 (- n) (omega_nat_p (- n) H2). }
    exact Lepsbetaneg X h Hh n Hn H1 x Hx (fun _ v => v :e X) LepsIn1.
  - assume H1: 0 <= n.
    assume H2: ~(n < 0).
    assume H3: n :e omega.
    claim LepsIn2: omega_iterate n h x :e X.
    { exact omega_iterate_In X x Hx h Hh1 n (omega_nat_p n H3). }
    exact Lepsbetanonneg X h Hh n H3 x Hx (fun _ v => v :e X) LepsIn2.
}
claim LepsInP: forall X, forall h:set -> set, bij X X h
 -> forall u :e int :*: X, eps (pack_u X h) u :e X.
{ let X h. assume Hh. let u. assume Hu.
  rewrite <- tuple_lam_eta int (fun _ => X) u Hu.
  exact LepsIn X h Hh (u 0) (ap0_lam int (fun _ => X) u Hu)
                      (u 1) (ap1_lam int (fun _ => X) u Hu).
}
apply MetaAdjunction_strict_I.
- prove MetaFunctor_strict (fun _ => True) HomSet
          (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
          struct_u_bij Hom_struct_u struct_id struct_comp
          F0 F1.
  apply MetaFunctor_strict_I.
  + prove MetaCat (fun _ => True) HomSet (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g)).
    exact MetaCatSet.
  + prove MetaCat struct_u_bij Hom_struct_u struct_id struct_comp.
    exact MetaCat_struct_u_bij.
  + prove MetaFunctor (fun _ => True) HomSet
          (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
          struct_u_bij Hom_struct_u struct_id struct_comp
          F0 F1.
    apply MetaFunctor_I.
    * { let X. assume HX.
        prove struct_u_bij (F0 X).
        prove struct_u (F0 X) /\ unpack_u_o (F0 X) (fun X' h => bij X' X' h).
	apply andI.
	- prove struct_u (pack_u (int :*: X) (fun u => (u 0 + 1,u 1))).
          apply pack_struct_u_I.
          prove forall u :e int :*: X, (u 0 + 1,u 1) :e int :*: X.
          exact L1 X.
	- prove unpack_u_o (F0 X) (fun X' h => bij X' X' h).
	  claim L5: forall G:set -> set, (forall u :e int :*: X, (u 0 + 1,u 1) = G u) -> (Phi (int :*: X) G) = (Phi (int :*: X) (fun u => (u 0 + 1,u 1))).
	  { exact L2 (int :*: X) (fun u => (u 0 + 1,u 1)). }
	  prove unpack_u_o (pack_u (int :*: X) (fun u => (u 0 + 1,u 1))) (fun X' h => bij X' X' h).
	  rewrite unpack_u_o_eq Phi (int :*: X) (fun u => (u 0 + 1,u 1)) L5.
	  prove bij (int :*: X) (int :*: X) (fun u => (u 0 + 1,u 1)).
	  exact L1b X.
      }
    * { let X Y f. assume HX HY Hf.
        prove Hom_struct_u (F0 X) (F0 Y) (F1 X Y f).
        prove Hom_struct_u (pack_u (int :*: X) (fun u => (u 0 + 1,u 1)))
                           (pack_u (int :*: Y) (fun u => (u 0 + 1,u 1)))
                           (fun u :e int :*: X => (u 0,f (u 1))).
        rewrite Hom_struct_u_pack.
	apply andI.
	- prove (fun u :e int :*: X => (u 0,f (u 1))) :e (int :*: Y) :^: (int :*: X).
	  prove (fun u :e int :*: X => (u 0,f (u 1))) :e Pi_ x :e int :*: X, int :*: Y.
	  apply lam_Pi.
	  let u. assume Hu: u :e int :*: X.
	  prove (u 0,f (u 1)) :e int :*: Y.
	  prove (u 0,f (u 1)) :e int :*: Y.
	  apply tuple_2_setprod int Y (u 0) (ap0_lam int (fun _ => X) u Hu) (f (u 1)).
	  prove f (u 1) :e Y.
	  apply ap_Pi X (fun _ => Y) f (u 1) Hf.
	  prove u 1 :e X.
	  exact ap1_lam int (fun _ => X) u Hu.
	- let u. assume Hu: u :e int :*: X.
	  prove (fun u :e int :*: X => (u 0,f (u 1))) (u 0 + 1,u 1)
	      = (((fun u :e int :*: X => (u 0,f (u 1))) u 0 + 1),((fun u :e int :*: X => (u 0,f (u 1))) u 1)).
	  rewrite beta (int :*: X) (fun u => (u 0,f (u 1))) (u 0 + 1,u 1) (L1 X u Hu).
	  rewrite tuple_2_0_eq.
	  rewrite tuple_2_1_eq.
	  prove (u 0 + 1,f (u 1))
	      = ((fun u :e int :*: X => (u 0,f (u 1))) u 0 + 1,((fun u :e int :*: X => (u 0,f (u 1))) u 1)).
	  rewrite beta (int :*: X) (fun u => (u 0,f (u 1))) u Hu.
	  rewrite tuple_2_0_eq.
	  rewrite tuple_2_1_eq.
	  reflexivity.
      }
    * { let X. assume HX.
        prove F1 X X (lam_id X) = struct_id (F0 X).
	prove F1 X X (lam_id X)
	    = (fun u :e pack_u (int :*: X) (fun u => (u 0 + 1,u 1)) 0 => u).
	prove (fun u :e int :*: X => (u 0,lam_id X (u 1)))
	    = (fun u :e pack_u (int :*: X) (fun u => (u 0 + 1,u 1)) 0 => u).
	rewrite <- pack_u_0_eq2.
        apply lam_ext.
	let u. assume Hu: u :e int :*: X.
	prove (u 0,lam_id X (u 1)) = u.
	prove (u 0,(fun x :e X => x) (u 1)) = u.
	rewrite beta X (fun x => x) (u 1) (ap1_lam int (fun _ => X) u Hu).
	prove (u 0,u 1) = u.
	exact tuple_lam_eta int (fun _ => X) u Hu.
      }
    * { let X Y Z f g. assume HX HY HZ Hf Hg.
        prove F1 X Z (lam_comp X g f) = struct_comp (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f).
	prove (fun u :e int :*: X => (u 0,lam_comp X g f (u 1)))
	    = lam_comp (pack_u (int :*: X) (fun u => (u 0 + 1,u 1)) 0) (F1 Y Z g) (F1 X Y f).
	rewrite <- pack_u_0_eq2.
	prove (fun u :e int :*: X => (u 0,lam_comp X g f (u 1)))
	    = (fun u :e int :*: X => (F1 Y Z g (F1 X Y f u))).
	apply lam_ext.
	let u. assume Hu.
	prove (u 0,lam_comp X g f (u 1))
	    = F1 Y Z g (F1 X Y f u).
	prove (u 0,lam_comp X g f (u 1))
	    = F1 Y Z g ((fun u :e int :*: X => (u 0,f (u 1))) u).
	rewrite beta (int :*: X) (fun u => (u 0,f (u 1))) u Hu.
	prove (u 0,lam_comp X g f (u 1))
	    = F1 Y Z g (u 0,f (u 1)).
	claim LufY: (u 0,f (u 1)) :e int :*: Y.
	{ apply tuple_2_setprod int Y.
	  - exact ap0_lam int (fun _ => X) u Hu.
	  - exact ap_Pi X (fun _ => Y) f (u 1) Hf (ap1_lam int (fun _ => X) u Hu).
	}
	prove (u 0,lam_comp X g f (u 1))
	    = (fun v :e int :*: Y => (v 0,g (v 1))) (u 0,f (u 1)).
	rewrite beta (int :*: Y) (fun v => (v 0,g (v 1))) (u 0,f (u 1)) LufY.
	rewrite tuple_2_0_eq.
	rewrite tuple_2_1_eq.
	prove (u 0,lam_comp X g f (u 1))
	    = (u 0,g (f (u 1))).
	prove (u 0,((fun x :e X => g (f x)) (u 1)))
	    = (u 0,g (f (u 1))).
	rewrite beta X (fun x => g (f x)) (u 1) (ap1_lam int (fun _ => X) u Hu).
	reflexivity.
      }
- prove MetaFunctor struct_u_bij Hom_struct_u struct_id struct_comp
                    (fun _ => True) HomSet (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
		    (fun X => X 0) (fun X Y f => f).
  exact MetaCat_struct_u_bij_Forgetful.
- prove MetaNatTrans (fun _ => True) HomSet (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
                     (fun _ => True) HomSet (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
		     (fun X => X) (fun X Y f => f) (fun X => F0 X 0) (fun X Y f => F1 X Y f) eta.
  apply MetaNatTrans_I.
  + let X. assume _. prove HomSet X (F0 X 0) (eta X).
    prove eta X :e pack_u (int :*: X) (fun u => (u 0 + 1,u 1)) 0 :^: X.
    rewrite <- pack_u_0_eq2.
    prove eta X :e (int :*: X) :^: X.
    prove (fun x :e X => (0,x)) :e Pi_ x :e X, int :*: X.
    apply lam_Pi.
    let x. assume Hx: x :e X.
    prove (0,x) :e int :*: X.
    apply tuple_2_setprod.
    * exact nat_p_int 0 nat_0.
    * exact Hx.
  + let X Y f. assume _ _. assume Hf: HomSet X Y f.
    prove lam_comp X (F1 X Y f) (eta X) = lam_comp X (eta Y) f.
    prove (fun x :e X => F1 X Y f (eta X x)) = (fun x :e X => eta Y (f x)).
    apply lam_ext.
    let x. assume Hx: x :e X.
    prove F1 X Y f (eta X x) = eta Y (f x).
    transitivity F1 X Y f (0,x),
                 (0,f x).
    * f_equal. exact Letabeta X x Hx.
    * prove (fun u :e int :*: X => (u 0,f (u 1))) (0,x) = (0,f x).
      rewrite beta (int :*: X) (fun u => (u 0,f (u 1))) (0,x) (tuple_2_setprod int X 0 (nat_p_int 0 nat_0) x Hx).
      rewrite tuple_2_0_eq.
      rewrite tuple_2_1_eq.
      reflexivity.
    * symmetry. exact Letabeta Y (f x) (ap_Pi X (fun _ => Y) f x Hf Hx).
- prove MetaNatTrans struct_u_bij Hom_struct_u struct_id struct_comp
                     struct_u_bij Hom_struct_u struct_id struct_comp
                     (fun Y => F0 (Y 0)) (fun X Y g => F1 (X 0) (Y 0) g) (fun Y => Y) (fun X Y g => g) eps.
  apply MetaNatTrans_I.
  + let A. assume HA. prove Hom_struct_u (F0 (A 0)) A (eps A).
    apply HA. assume HAs. apply HAs.
    let X h.
    assume Hh: forall x :e X, h x :e X.
    prove unpack_u_o (pack_u X h) Phi
       -> Hom_struct_u (F0 (pack_u X h 0)) (pack_u X h) (eps (pack_u X h)).
    rewrite <- pack_u_0_eq2.
    prove unpack_u_o (pack_u X h) Phi
       -> Hom_struct_u (pack_u (int :*: X) (fun u => (u 0 + 1,u 1))) (pack_u X h) (eps (pack_u X h)).
    rewrite unpack_u_o_eq Phi X h (L2 X h).
    assume Hh2: bij X X h.
    apply bijE X X h Hh2.
    assume Hh2a Hh2b Hh2c.
    claim Lih: bij X X (inv X h).
    { exact bij_inv X X h Hh2. }
    apply bijE X X (inv X h) Lih.
    assume Hih1 Hih2 Hih3.
    rewrite Hom_struct_u_pack.
    apply andI.
    * { prove eps (pack_u X h) :e X :^: (int :*: X).
        claim L6: (fun u :e int :*: X => if u 0 < 0 then omega_iterate (- (u 0)) (inv X h) (u 1) else omega_iterate (u 0) h (u 1)) :e Pi_ u :e int :*: X, X.
	{ apply lam_Pi.
          let u. assume Hu: u :e int :*: X.
	  prove (if u 0 < 0 then omega_iterate (- (u 0)) (inv X h) (u 1) else omega_iterate (u 0) h (u 1)) :e X.
          claim Lu0: u 0 :e int.
          { exact ap0_lam int (fun _ => X) u Hu. }
          claim Lu1: u 1 :e X.
	  { exact ap1_lam int (fun _ => X) u Hu. }
	  apply int_neg_or_nonneg (u 0) Lu0.
	  - assume H1: u 0 < 0.
	    assume H2: - u 0 :e omega.
	    rewrite If_i_1 (u 0 < 0) (omega_iterate (- (u 0)) (inv X h) (u 1)) (omega_iterate (u 0) h (u 1)) H1.
            prove omega_iterate (- (u 0)) (inv X h) (u 1) :e X.
	    exact omega_iterate_In X (u 1) Lu1 (inv X h) Hih1 (- (u 0)) (omega_nat_p (- (u 0)) H2).
          - assume H1: 0 <= u 0.
	    assume H2: ~(u 0 < 0).
	    assume H3: u 0 :e omega.
	    rewrite If_i_0 (u 0 < 0) (omega_iterate (- (u 0)) (inv X h) (u 1)) (omega_iterate (u 0) h (u 1)) H2.
	    prove omega_iterate (u 0) h (u 1) :e X.
	    exact omega_iterate_In X (u 1) Lu1 h Hh2a (u 0) (omega_nat_p (u 0) H3).
	}
        exact Lepseq X h Hh2 (fun _ u => u :e X :^: (int :*: X)) L6.
      }
    * { prove forall u :e int :*: X, eps (pack_u X h) (u 0 + 1,u 1) = h (eps (pack_u X h) u).
        let u. assume Hu: u :e int :*: X.
	claim Lu0: u 0 :e int.
	{ exact ap0_lam int (fun _ => X) u Hu. }
	claim Lu1: u 1 :e X.
	{ exact ap1_lam int (fun _ => X) u Hu. }
	claim LSu0: u 0 + 1 :e int.
	{ exact int_add_SNo (u 0) Lu0 1 (nat_p_int 1 nat_1). }
        claim Lu0S: SNo (u 0).
        { exact int_SNo (u 0) Lu0. }
	prove eps (pack_u X h) (u 0 + 1,u 1) = h (eps (pack_u X h) u).
	transitivity if u 0 + 1 < 0 then omega_iterate (- (u 0 + 1)) (inv X h) (u 1) else omega_iterate (u 0 + 1) h (u 1).
	- exact Lepsbetaint X h Hh2 (u 0 + 1) LSu0 (u 1) Lu1.
	- prove (if u 0 + 1 < 0 then omega_iterate (- (u 0 + 1)) (inv X h) (u 1) else omega_iterate (u 0 + 1) h (u 1)) = h (eps (pack_u X h) u).
	  apply int_neg_or_nonneg (u 0 + 1) LSu0.
	  + assume H1: u 0 + 1 < 0.
	    assume H2: - (u 0 + 1) :e omega.
	    rewrite If_i_1 (u 0 + 1 < 0) (omega_iterate (- (u 0 + 1)) (inv X h) (u 1)) (omega_iterate (u 0 + 1) h (u 1)) H1.
	    prove omega_iterate (- (u 0 + 1)) (inv X h) (u 1) = h (eps (pack_u X h) u).
	    apply Hih2.
	    * prove omega_iterate (- (u 0 + 1)) (inv X h) (u 1) :e X.
	      apply omega_iterate_In X (u 1) Lu1 (inv X h) Hih1 (- (u 0 + 1)).
	      prove nat_p (- (u 0 + 1)).
	      exact omega_nat_p (- (u 0 + 1)) H2.
	    * prove h (eps (pack_u X h) u) :e X.
	      apply Hh.
	      prove eps (pack_u X h) u :e X.
              rewrite <- tuple_lam_eta int (fun _ => X) u Hu.
	      exact LepsIn X h Hh2 (u 0) Lu0 (u 1) Lu1.
	    * { prove inv X h (omega_iterate (- (u 0 + 1)) (inv X h) (u 1))
	            = inv X h (h (eps (pack_u X h) u)).
		transitivity omega_iterate (- u 0) (inv X h) (u 1),
		             eps (pack_u X h) u.
		- prove inv X h (omega_iterate (- (u 0 + 1)) (inv X h) (u 1)) = omega_iterate (- u 0) (inv X h) (u 1).
		  rewrite <- omega_iterate_S_out (- (u 0 + 1)) H2.
		  prove omega_iterate (ordsucc (- (u 0 + 1))) (inv X h) (u 1) = omega_iterate (- u 0) (inv X h) (u 1).
		  rewrite ordinal_ordsucc_SNo_eq (- (u 0 + 1)) (nat_p_ordinal (- (u 0 + 1)) (omega_nat_p (- (u 0 + 1)) H2)).
		  prove omega_iterate (1 + - (u 0 + 1)) (inv X h) (u 1) = omega_iterate (- u 0) (inv X h) (u 1).
		  rewrite add_SNo_com (u 0) 1 (int_SNo (u 0) Lu0) SNo_1.
		  rewrite minus_add_SNo_distr 1 (u 0) SNo_1 (int_SNo (u 0) Lu0).
		  prove omega_iterate (1 + - 1 + - u 0) (inv X h) (u 1) = omega_iterate (- u 0) (inv X h) (u 1).
		  rewrite add_SNo_minus_SNo_prop2 1 (- u 0) SNo_1 (SNo_minus_SNo (u 0) (int_SNo (u 0) Lu0)).
		  reflexivity.
		- prove omega_iterate (- u 0) (inv X h) (u 1) = eps (pack_u X h) u.
		  symmetry.
		  rewrite <- tuple_lam_eta int (fun _ => X) u Hu at 1.
		  prove eps (pack_u X h) (u 0,u 1) = omega_iterate (- u 0) (inv X h) (u 1).
		  claim Lu0neg: u 0 < 0.
		  { apply SNoLt_tra (u 0) (u 0 + 1) 0 Lu0S (SNo_add_SNo (u 0) 1 Lu0S SNo_1) SNo_0.
		    - prove u 0 < u 0 + 1.
		      rewrite <- add_SNo_0R (u 0) Lu0S at 1.
		      apply add_SNo_Lt2 (u 0) 0 1 Lu0S SNo_0 SNo_1.
		      prove 0 < 1.
		      exact SNoLt_0_1.
		    - prove u 0 + 1 < 0. exact H1.
		  }
		  exact Lepsbetaneg X h Hh2 (u 0) Lu0 Lu0neg (u 1) Lu1.
		- prove eps (pack_u X h) u = inv X h (h (eps (pack_u X h) u)).
		  symmetry.
		  exact inj_linv X h Hh2b (eps (pack_u X h) u) (LepsInP X h Hh2 u Hu).
	      }
	  + assume H1: 0 <= u 0 + 1.
	    assume H2: ~(u 0 + 1 < 0).
	    assume H3: u 0 + 1 :e omega.
	    rewrite If_i_0 (u 0 + 1 < 0) (omega_iterate (- (u 0 + 1)) (inv X h) (u 1)) (omega_iterate (u 0 + 1) h (u 1)) H2.
	    prove omega_iterate (u 0 + 1) h (u 1) = h (eps (pack_u X h) u).
	    apply SNoLeE 0 (u 0 + 1) SNo_0 (int_SNo (u 0 + 1) LSu0) H1.
	    * { assume H4: 0 < u 0 + 1.
	        claim Lu0n: u 0 :e omega.
		{ apply int_neg_or_nonneg (u 0) Lu0.
		  - assume H5: u 0 < 0.
		    assume H6: - u 0 :e omega.
		    prove False.
		    claim Lmu0pos: 0 < - u 0.
		    { rewrite <- minus_SNo_0 at 1.
		      apply minus_SNo_Lt_contra (u 0) 0 Lu0S SNo_0.
		      prove u 0 < 0.
		      exact H5.
		    }
		    apply nat_inv (- u 0) (omega_nat_p (- u 0) H6).
		    + assume H7: - u 0 = 0.
		      apply SNoLt_irref 0.
		      prove 0 < 0.
		      rewrite <- H7 at 2.
		      exact Lmu0pos.
		    + assume H. apply H.
		      let n. assume H. apply H.
		      assume Hn: nat_p n.
		      assume H7: - u 0 = ordsucc n.
		      apply neq_ordsucc_0 n.
		      prove ordsucc n = 0.
		      apply SingE.
		      prove ordsucc n :e {0}.
		      rewrite <- eq_1_Sing0.
		      prove ordsucc n :e 1.
		      apply ordinal_SNoLt_In (ordsucc n) 1 (ordinal_ordsucc n (nat_p_ordinal n Hn)) (nat_p_ordinal 1 nat_1).
		      prove ordsucc n < 1.
		      rewrite <- H7.
		      prove - u 0 < 1.
		      apply add_SNo_Lt2_cancel (u 0) (- u 0) 1 Lu0S (SNo_minus_SNo (u 0) Lu0S) SNo_1.
		      prove u 0 + - u 0 < u 0 + 1.
		      rewrite add_SNo_minus_SNo_rinv (u 0) Lu0S.
		      exact H4.
		  - assume _ _ H5. exact H5.
		}
	        claim Lu0o: ordinal (u 0).
	        { exact nat_p_ordinal (u 0) (omega_nat_p (u 0) Lu0n). }
	        prove omega_iterate (u 0 + 1) h (u 1) = h (eps (pack_u X h) u).
	        rewrite add_SNo_com (u 0) 1 (int_SNo (u 0) Lu0) SNo_1.
	        prove omega_iterate (1 + u 0) h (u 1) = h (eps (pack_u X h) u).
	        rewrite <- ordinal_ordsucc_SNo_eq (u 0) Lu0o.
	        prove omega_iterate (ordsucc (u 0)) h (u 1) = h (eps (pack_u X h) u).
	        transitivity h (omega_iterate (u 0) h (u 1)).
		- exact omega_iterate_S_out (u 0) Lu0n h (u 1).
		- f_equal.
                  prove omega_iterate (u 0) h (u 1) = eps (pack_u X h) u.
	          symmetry.
	          rewrite <- tuple_lam_eta int (fun _ => X) u Hu at 1.
	          prove eps (pack_u X h) (u 0,u 1) = omega_iterate (u 0) h (u 1).
	          exact Lepsbetanonneg X h Hh2 (u 0) Lu0n (u 1) Lu1.
	      }
	    * { assume H4: 0 = u 0 + 1.
                prove omega_iterate (u 0 + 1) h (u 1) = h (eps (pack_u X h) u).
	        rewrite <- H4.
	        rewrite omega_iterate_0.
	        prove u 1 = h (eps (pack_u X h) u).
		apply surj_rinv X X h Hh2c (u 1) Lu1.
		assume _.
		assume H5: h (inv X h (u 1)) = u 1.
		rewrite <- H5.
		prove h (inv X h (u 1)) = h (eps (pack_u X h) u).
		f_equal.
		prove inv X h (u 1) = eps (pack_u X h) u.
                claim Lmu01: - u 0 = 1.
		{ apply add_SNo_cancel_L (u 0) (- u 0) 1 Lu0S (SNo_minus_SNo (u 0) Lu0S) SNo_1.
		  prove u 0 + - u 0 = u 0 + 1.
		  rewrite add_SNo_minus_SNo_rinv (u 0) Lu0S.
		  exact H4.
		}
		transitivity omega_iterate (- u 0) (inv X h) (u 1).
		- prove inv X h (u 1) = omega_iterate (- u 0) (inv X h) (u 1).
		  rewrite Lmu01.
		  symmetry.
		  rewrite omega_iterate_S_out 0 (nat_p_omega 0 nat_0).
		  f_equal.
		  apply omega_iterate_0.
		- prove omega_iterate (- u 0) (inv X h) (u 1) = eps (pack_u X h) u.
		  claim Lu0neg: u 0 < 0.
		  { apply minus_SNo_Lt_contra3 0 (u 0) SNo_0 Lu0S.
		    prove - 0 < - u 0.
		    rewrite Lmu01.
		    rewrite minus_SNo_0.
		    prove 0 < 1.
		    exact SNoLt_0_1.
		  }
		  symmetry.
		  rewrite <- tuple_lam_eta int (fun _ => X) u Hu at 1.
                  exact Lepsbetaneg X h Hh2 (u 0) Lu0 Lu0neg (u 1) Lu1.
	      }
      }
  + let A B f. assume HA HB.
    prove Hom_struct_u A B f
       -> lam_comp (F0 (A 0) 0) f (eps A)
        = lam_comp (F0 (A 0) 0) (eps B) (F1 (A 0) (B 0) f).
    apply HA. assume HAs. apply HAs.
    let X h.
    assume Hh: forall x :e X, h x :e X.
    prove unpack_u_o (pack_u X h) Phi
       -> Hom_struct_u (pack_u X h) B f
       -> lam_comp (F0 (pack_u X h 0) 0) f (eps (pack_u X h))
        = lam_comp (F0 (pack_u X h 0) 0) (eps B) (F1 (pack_u X h 0) (B 0) f).
    rewrite <- pack_u_0_eq2.
    rewrite unpack_u_o_eq Phi X h (L2 X h).
    assume Hh2: bij X X h.
    apply bijE X X h Hh2.
    assume Hh2a Hh2b Hh2c.
    prove Hom_struct_u (pack_u X h) B f
       -> lam_comp (F0 X 0) f (eps (pack_u X h))
        = lam_comp (F0 X 0) (eps B) (F1 X (B 0) f).
    apply HB. assume HBs. apply HBs.
    let Y k.
    assume Hk: forall y :e Y, k y :e Y.
    prove unpack_u_o (pack_u Y k) Phi
       -> Hom_struct_u (pack_u X h) (pack_u Y k) f
       -> lam_comp (F0 X 0) f (eps (pack_u X h))
        = lam_comp (F0 X 0) (eps (pack_u Y k)) (F1 X (pack_u Y k 0) f).
    rewrite unpack_u_o_eq Phi Y k (L2 Y k).
    assume Hk2: bij Y Y k.
    apply bijE Y Y k Hk2.
    assume Hk2a Hk2b Hk2c.
    rewrite Hom_struct_u_pack X Y h k f.
    assume Hf. apply Hf.
    assume Hf1: f :e Y :^: X.
    assume Hf2: forall x :e X, f (h x) = k (f x).
    rewrite <- pack_u_0_eq2.
    prove lam_comp (F0 X 0) f (eps (pack_u X h))
        = lam_comp (F0 X 0) (eps (pack_u Y k)) (F1 X Y f).
    prove lam_comp (pack_u (int :*: X) (fun u => (u 0 + 1,u 1)) 0) f (eps (pack_u X h))
        = lam_comp (pack_u (int :*: X) (fun u => (u 0 + 1,u 1)) 0) (eps (pack_u Y k)) (F1 X Y f).
    rewrite <- pack_u_0_eq2.
    prove lam_comp (int :*: X) f (eps (pack_u X h))
        = lam_comp (int :*: X) (eps (pack_u Y k)) (F1 X Y f).
    prove (fun u :e int :*: X => f (eps (pack_u X h) u))
        = (fun u :e int :*: X => eps (pack_u Y k) (F1 X Y f u)).
    apply lam_ext.
    let u. assume Hu: u :e int :*: X.
    claim Lu0: u 0 :e int.
    { exact ap0_lam int (fun _ => X) u Hu. }
    claim Lu1: u 1 :e X.
    { exact ap1_lam int (fun _ => X) u Hu. }
    claim Lih: bij X X (inv X h).
    { exact bij_inv X X h Hh2. }
    apply bijE X X (inv X h) Lih.
    assume Hih1 Hih2 Hih3.
    claim Lik: bij Y Y (inv Y k).
    { exact bij_inv Y Y k Hk2. }
    apply bijE Y Y (inv Y k) Lik.
    assume Hik1 Hik2 Hik3.
    prove f (eps (pack_u X h) u) = eps (pack_u Y k) (F1 X Y f u).
    prove f (eps (pack_u X h) u) = eps (pack_u Y k) ((fun u :e int :*: X => (u 0,f (u 1))) u).
    rewrite beta (int :*: X) (fun u => (u 0,f (u 1))) u Hu.
    prove f (eps (pack_u X h) u) = eps (pack_u Y k) (u 0,f (u 1)).
    transitivity f (if u 0 < 0 then omega_iterate (- u 0) (inv X h) (u 1) else omega_iterate (u 0) h (u 1)),
                 if u 0 < 0 then omega_iterate (- u 0) (inv Y k) (f (u 1)) else omega_iterate (u 0) k (f (u 1)).
    * f_equal.
      prove eps (pack_u X h) u = if u 0 < 0 then omega_iterate (- u 0) (inv X h) (u 1) else omega_iterate (u 0) h (u 1).
      rewrite <- tuple_lam_eta int (fun _ => X) u Hu at 1.
      exact Lepsbetaint X h Hh2 (u 0) Lu0 (u 1) Lu1.
    * { prove f (if u 0 < 0 then omega_iterate (- u 0) (inv X h) (u 1) else omega_iterate (u 0) h (u 1))
            = (if u 0 < 0 then omega_iterate (- u 0) (inv Y k) (f (u 1)) else omega_iterate (u 0) k (f (u 1))).
        apply int_neg_or_nonneg (u 0) Lu0.
        - assume H1: u 0 < 0.
	  assume H2: - u 0 :e omega.
	  rewrite If_i_1 (u 0 < 0) (omega_iterate (- u 0) (inv X h) (u 1)) (omega_iterate (u 0) h (u 1)) H1.
	  rewrite If_i_1 (u 0 < 0) (omega_iterate (- u 0) (inv Y k) (f (u 1))) (omega_iterate (u 0) k (f (u 1))) H1.
	  prove f (omega_iterate (- u 0) (inv X h) (u 1))
              = omega_iterate (- u 0) (inv Y k) (f (u 1)).
          (** omega_iterate_comm but with inverses of h and k **)
	  claim Lf: forall x :e X, f (inv X h x) = inv Y k (f x).
	  { let x. assume Hx.
	    apply Hk2b.
	    - prove f (inv X h x) :e Y.
	      apply ap_Pi X (fun _ => Y) f (inv X h x) Hf1.
	      prove inv X h x :e X.
	      exact Hih1 x Hx.
	    - prove inv Y k (f x) :e Y.
	      apply Hik1.
	      prove f x :e Y.
	      exact ap_Pi X (fun _ => Y) f x Hf1 Hx.
	    - prove k (f (inv X h x)) = k (inv Y k (f x)).
	      transitivity f (h (inv X h x)), f x.
	      + prove k (f (inv X h x)) = f (h (inv X h x)).
	        symmetry.
		exact Hf2 (inv X h x) (Hih1 x Hx).
	      + prove f (h (inv X h x)) = f x.
	        f_equal.
		apply surj_rinv X X h Hh2c x Hx.
		assume _ H. exact H.
	      + prove f x = k (inv Y k (f x)).
	        symmetry.
		apply surj_rinv Y Y k Hk2c (f x) (ap_Pi X (fun _ => Y) f x Hf1 Hx).
		assume _ H. exact H.
	  }
  	  exact omega_iterate_comm X (u 1) Lu1 (inv X h) (inv Y k) Hih1 (fun x => f x) Lf (- u 0) (omega_nat_p (- u 0) H2).
        - assume H1: 0 <= u 0.
	  assume H2: ~(u 0 < 0).
	  assume H3: u 0 :e omega.
	  rewrite If_i_0 (u 0 < 0) (omega_iterate (- u 0) (inv X h) (u 1)) (omega_iterate (u 0) h (u 1)) H2.
	  rewrite If_i_0 (u 0 < 0) (omega_iterate (- u 0) (inv Y k) (f (u 1))) (omega_iterate (u 0) k (f (u 1))) H2.
          prove f (omega_iterate (u 0) h (u 1))
              = omega_iterate (u 0) k (f (u 1)).
	  exact omega_iterate_comm X (u 1) Lu1 h k Hh (fun x => f x) Hf2 (u 0) (omega_nat_p (u 0) H3).
      }
    * symmetry. exact Lepsbetaint Y k Hk2 (u 0) Lu0 (f (u 1)) (ap_Pi X (fun _ => Y) f (u 1) Hf1 Lu1).
- prove MetaAdjunction
         (fun _ => True) HomSet
         (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
         struct_u_bij Hom_struct_u struct_id struct_comp
         F0 F1 (fun X => X 0) (fun X Y f => f) eta eps.
  apply MetaAdjunction_I.
  + let X. assume _.
    prove struct_comp (F0 X) (F0 (F0 X 0)) (F0 X) (eps (F0 X)) (F1 X (F0 X 0) (eta X))
        = struct_id (F0 X).
    prove lam_comp (F0 X 0) (eps (F0 X)) (F1 X (F0 X 0) (eta X))
        = lam_id (F0 X 0).
    prove lam_comp (pack_u (int :*: X) (fun u => (u 0 + 1,u 1)) 0) (eps (F0 X)) (F1 X (pack_u (int :*: X) (fun u => (u 0 + 1,u 1)) 0) (eta X))
        = lam_id (pack_u (int :*: X) (fun u => (u 0 + 1,u 1)) 0).
    rewrite <- pack_u_0_eq2.
    prove lam_comp (int :*: X) (eps (F0 X)) (F1 X (int :*: X) (eta X))
        = lam_id (int :*: X).
    prove (fun u :e int :*: X => eps (F0 X) (F1 X (int :*: X) (eta X) u))
        = (fun u :e int :*: X => u).
    apply lam_ext.
    let u. assume Hu: u :e int :*: X.
    claim Lu0: u 0 :e int.
    { exact ap0_lam int (fun _ => X) u Hu. }
    claim Lu1: u 1 :e X.
    { exact ap1_lam int (fun _ => X) u Hu. }
    prove eps (F0 X) (F1 X (int :*: X) (eta X) u) = u.
    prove eps (F0 X) ((fun u :e int :*: X => (u 0,eta X (u 1))) u) = u.
    transitivity eps (F0 X) (u 0,(0,u 1)),
                 if u 0 < 0 then omega_iterate (- u 0) (inv (int :*: X) (fun u => (u 0 + 1,u 1))) (0,u 1) else omega_iterate (u 0) (fun u => (u 0 + 1,u 1)) (0,u 1),
		 (u 0,u 1).
    * { f_equal.
        transitivity (u 0,eta X (u 1)).
        - exact beta (int :*: X) (fun u => (u 0,eta X (u 1))) u Hu.
        - prove (u 0,eta X (u 1)) = (u 0,(0,u 1)).
          exact Letabeta X (u 1) Lu1 (fun _ v => (u 0,v) = (u 0,(0,u 1))) (fun q H => H).
      }
    * prove eps (F0 X) (u 0,(0,u 1)) = if u 0 < 0 then omega_iterate (- u 0) (inv (int :*: X) (fun u => (u 0 + 1,u 1))) (0,u 1) else omega_iterate (u 0) (fun u => (u 0 + 1,u 1)) (0,u 1).
      prove eps (pack_u (int :*: X) (fun u => (u 0 + 1,u 1))) (u 0,(0,u 1)) = if u 0 < 0 then omega_iterate (- u 0) (inv (int :*: X) (fun u => (u 0 + 1,u 1))) (0,u 1) else omega_iterate (u 0) (fun u => (u 0 + 1,u 1)) (0,u 1).
      apply Lepsbetaint (int :*: X) (fun u => (u 0 + 1,u 1)) (L1b X)
                        (u 0) Lu0
		        (0,u 1)
		        (tuple_2_setprod int X 0 (nat_p_int 0 nat_0) (u 1) Lu1).
    * { prove (if u 0 < 0 then omega_iterate (- u 0) (inv (int :*: X) (fun u => (u 0 + 1,u 1))) (0,u 1) else omega_iterate (u 0) (fun u => (u 0 + 1,u 1)) (0,u 1)) = (u 0,u 1).
        apply int_neg_or_nonneg (u 0) Lu0.
        - assume H1: u 0 < 0.
          assume H2: - u 0 :e omega.
	  rewrite If_i_1 (u 0 < 0) (omega_iterate (- u 0) (inv (int :*: X) (fun u => (u 0 + 1,u 1))) (0,u 1)) (omega_iterate (u 0) (fun u => (u 0 + 1,u 1)) (0,u 1)) H1.
          prove omega_iterate (- u 0) (inv (int :*: X) (fun u => (u 0 + 1,u 1))) (0,u 1) = (u 0,u 1).
	  transitivity omega_iterate (- u 0) (fun u => (u 0 + - 1,u 1)) (0,u 1).
	  + symmetry.
	    claim L7: forall u :e int :*: X, (u 0 + - 1,u 1) :e int :*: X.
	    { let u. assume Hu.
	      claim Lu0: u 0 :e int.
              { exact ap0_lam int (fun _ => X) u Hu. }
              claim Lu1: u 1 :e X.
              { exact ap1_lam int (fun _ => X) u Hu. }
	      apply tuple_2_setprod.
	      - prove u 0 + - 1 :e int.
	        apply int_add_SNo.
                + exact Lu0.
                + prove - 1 :e int.
                  apply int_minus_SNo.
                  exact nat_p_int 1 nat_1.
              - prove u 1 :e X. exact Lu1.
	    }
	    apply omega_iterate_ext (int :*: X) (0,u 1) (tuple_2_setprod int X 0 (nat_p_int 0 nat_0) (u 1) Lu1) (fun u => (u 0 + - 1,u 1)) (inv (int :*: X) (fun u => (u 0 + 1,u 1))).
	    * exact L7.
	    * { prove forall u :e int :*: X, (u 0 + - 1,u 1) = inv (int :*: X) (fun u => (u 0 + 1,u 1)) u.
	        let u. assume Hu.
	        claim Lu0: u 0 :e int.
                { exact ap0_lam int (fun _ => X) u Hu. }
                claim Lu1: u 1 :e X.
                { exact ap1_lam int (fun _ => X) u Hu. }
		set g : set -> set := fun u => (u 0 + 1,u 1).
		prove (u 0 + - 1,u 1) = inv (int :*: X) g u.
		apply bijE (int :*: X) (int :*: X) g (L1b X).
		assume _ H3 H4.
		apply H3.
		- prove (u 0 + - 1,u 1) :e int :*: X.
		  exact L7 u Hu.
		- prove inv (int :*: X) g u :e int :*: X.
		  apply bijE (int :*: X) (int :*: X) (inv (int :*: X) g) (bij_inv (int :*: X) (int :*: X) g (L1b X)).
		  assume H5 _ _.
		  exact H5 u Hu.
		- prove ((u 0 + - 1,u 1) 0 + 1,(u 0 + - 1,u 1) 1)
		      = g (inv (int :*: X) g u).
		  rewrite tuple_2_0_eq.
		  rewrite tuple_2_1_eq.
		  prove ((u 0 + - 1) + 1,u 1) = g (inv (int :*: X) g u).
		  rewrite add_SNo_minus_R2' (u 0) 1 (int_SNo (u 0) Lu0) SNo_1.
		  prove (u 0,u 1) = g (inv (int :*: X) g u).
		  rewrite tuple_lam_eta int (fun _ => X) u Hu.
		  prove u = g (inv (int :*: X) g u).
		  symmetry.
		  apply surj_rinv (int :*: X) (int :*: X) g H4 u Hu.
		  assume _ H5.
		  exact H5.
	      }
	    * prove nat_p (- u 0). exact omega_nat_p (- u 0) H2.
	  + prove omega_iterate (- u 0) (fun u => (u 0 + - 1,u 1)) (0,u 1) = (u 0,u 1).
	    rewrite omega_iterate_pair_countback1 (u 1) (- u 0) (omega_nat_p (- u 0) H2).
	    prove (- - u 0,u 1) = (u 0,u 1).
	    rewrite minus_SNo_invol (u 0) (int_SNo (u 0) Lu0).
	    reflexivity.
        - assume H1: 0 <= u 0.
	  assume H2: ~(u 0 < 0).
	  assume H3: u 0 :e omega.
	  rewrite If_i_0 (u 0 < 0) (omega_iterate (- u 0) (inv (int :*: X) (fun u => (u 0 + 1,u 1))) (0,u 1)) (omega_iterate (u 0) (fun u => (u 0 + 1,u 1)) (0,u 1)) H2.
	  prove omega_iterate (u 0) (fun u => (u 0 + 1,u 1)) (0,u 1) = (u 0,u 1).
	  transitivity omega_iterate (u 0) (fun u => (ordsucc (u 0),u 1)) (0,u 1).
	  + prove omega_iterate (u 0) (fun u => (u 0 + 1,u 1)) (0,u 1)
	        = omega_iterate (u 0) (fun u => (ordsucc (u 0),u 1)) (0,u 1).
            symmetry.
	    apply omega_iterate_ext (omega :*: X) (0,u 1) (tuple_2_setprod omega X 0 (nat_p_omega 0 nat_0) (u 1) Lu1) (fun u => (ordsucc (u 0),u 1)) (fun u => (u 0 + 1,u 1)).
	    * { prove forall u :e omega :*: X, (ordsucc (u 0),u 1) :e omega :*: X.
	        let u. assume Hu. apply tuple_2_setprod omega X.
		- prove ordsucc (u 0) :e omega.
                  apply omega_ordsucc.
                  exact ap0_lam omega (fun _ => X) u Hu.
                - prove u 1 :e X.
                  exact ap1_lam omega (fun _ => X) u Hu.
	      }
	    * prove forall u :e omega :*: X, (ordsucc (u 0),u 1) = (u 0 + 1,u 1).
	      let u. assume Hu.
	      claim Lu0o: ordinal (u 0).
	      { exact nat_p_ordinal (u 0) (omega_nat_p (u 0) (ap0_lam omega (fun _ => X) u Hu)). }
	      rewrite ordinal_ordsucc_SNo_eq (u 0) Lu0o.
	      prove (1 + u 0,u 1) = (u 0 + 1,u 1).
	      rewrite add_SNo_com 1 (u 0) SNo_1 (ordinal_SNo (u 0) Lu0o).
	      reflexivity.
	    * prove nat_p (u 0). exact omega_nat_p (u 0) H3.
	  + exact omega_iterate_pair_count1 (u 1) (u 0) (omega_nat_p (u 0) H3).
     }
   * prove (u 0,u 1) = u.
     exact tuple_lam_eta int (fun _ => X) u Hu.
  + let A. assume HA. apply HA. assume HAs. apply HAs.
    let X h.
    assume Hh: forall x :e X, h x :e X.
    prove unpack_u_o (pack_u X h) Phi
       -> lam_comp (pack_u X h 0) (eps (pack_u X h)) (eta (pack_u X h 0)) = lam_id (pack_u X h 0).
    rewrite <- pack_u_0_eq2.
    rewrite unpack_u_o_eq Phi X h (L2 X h).
    assume Hh2: bij X X h.
    prove (fun x :e X => eps (pack_u X h) (eta X x)) = (fun x :e X => x).
    apply lam_ext.
    let x. assume Hx: x :e X.
    prove eps (pack_u X h) (eta X x) = x.
    transitivity eps (pack_u X h) (0,x),
                 omega_iterate 0 h x.
    * f_equal. exact Letabeta X x Hx.
    * prove eps (pack_u X h) (0,x) = omega_iterate 0 h x.
      exact Lepsbetanonneg X h Hh2 0 (nat_p_omega 0 nat_0) x Hx.
    * prove omega_iterate 0 h x = x.
      apply omega_iterate_0.
Qed.

(** bounty 750 **)
Proposition MetaCat_struct_u_bij_left_adjoint_forgetful:
  exists F0:set -> set,
  exists F1:set -> set -> set -> set,
  exists eta eps:set -> set,
  MetaAdjunction_strict
       (fun _ => True) HomSet
       (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
       struct_u_bij Hom_struct_u struct_id struct_comp
       F0 F1 (fun X => X 0) (fun X Y f => f) eta eps.
set F0 : set -> set := fun X => pack_u (int :*: X) (fun u => (u 0 + 1,u 1)).
set F1 : set -> set -> set -> set := fun X Y h => fun u :e int :*: X => (u 0,h (u 1)).
set eta : set -> set := fun X => fun x :e X => (0,x).
set epsPhi : set -> (set -> set) -> set := fun X h => fun u :e int :*: X => if u 0 < 0 then omega_iterate (- (u 0)) (inv X h) (u 1) else omega_iterate (u 0) h (u 1).
set eps : set -> set := fun A => unpack_u_i A epsPhi.
witness F0. witness F1. witness eta. witness eps.
exact MetaCat_struct_u_bij_forgetfree.
Qed.

