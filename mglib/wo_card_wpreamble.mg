(** Preamble Begin **)
(* Parameter Eps_i "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" *)
Parameter Eps_i : (set->prop)->set.

Axiom Eps_i_ax : forall P:set->prop, forall x:set, P x -> P (Eps_i P).

Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.

Definition not : prop -> prop := fun A:prop => A -> False.

(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.

Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.

(* Unicode /\ "2227" *)
Infix /\ 780 left := and.

Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.

(* Unicode \/ "2228" *)
Infix \/ 785 left := or.

Definition iff : prop -> prop -> prop := fun A B:prop => and (A -> B) (B -> A).

(* Unicode <-> "2194" *)
Infix <-> 805 := iff.

Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
Definition neq : A->A->prop := fun x y:A => ~ eq x y.
End Eq.

Infix = 502 := eq.
(* Unicode <> "2260" *)
Infix <> 502 := neq.

Section FE.
Variable A B : SType.
Axiom func_ext : forall f g : A -> B , (forall x : A , f x = g x) -> f = g.
End FE.

Section Ex.
Variable A:SType.
Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.
End Ex.

(* Unicode exists "2203" *)
Binder+ exists , := ex.

Axiom prop_ext : forall p q:prop, iff p q -> p = q.

Parameter In:set->set->prop.

Definition Subq : set -> set -> prop := fun A B => forall x :e A, x :e B.

Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.

Axiom In_ind : forall P:set->prop, (forall X:set, (forall x :e X, P x) -> P X) -> forall X:set, P X.

Binder+ exists , := ex; and.

Parameter Empty : set.
Axiom EmptyAx : ~exists x:set, x :e Empty.

(* Unicode Union "22C3" *)
Parameter Union : set->set.

Axiom UnionEq : forall X x, x :e Union X <-> exists Y, x :e Y /\ Y :e X.

(* Unicode Power "1D4AB" *)
Parameter Power : set->set.

Axiom PowerEq : forall X Y:set, Y :e Power X <-> Y c= X.

Parameter Repl : set -> (set -> set) -> set.
Notation Repl Repl.

Axiom ReplEq : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} <-> exists x :e A, y = F x.

Definition TransSet : set->prop := fun U:set => forall x :e U, x c= U.

Definition Union_closed : set->prop := fun U:set => forall X:set, X :e U -> Union X :e U.
Definition Power_closed : set->prop := fun U:set => forall X:set, X :e U -> Power X :e U.
Definition Repl_closed : set->prop := fun U:set => forall X:set, X :e U -> forall F:set->set,
   (forall x:set, x :e X -> F x :e U) -> {F x|x :e X} :e U.
Definition ZF_closed : set->prop := fun U:set =>
   Union_closed U
/\ Power_closed U
/\ Repl_closed U.

Parameter UnivOf : set->set.

Axiom UnivOf_In : forall N:set, N :e UnivOf N.

Axiom UnivOf_TransSet : forall N:set, TransSet (UnivOf N).

Axiom UnivOf_ZF_closed : forall N:set, ZF_closed (UnivOf N).

Axiom UnivOf_Min : forall N U:set, N :e U
  -> TransSet U
  -> ZF_closed U
  -> UnivOf N c= U.

Axiom FalseE : False -> forall p:prop, p.

Axiom TrueI : True.

Axiom notI : forall A:prop, (A -> False) -> ~A.

Axiom notE : forall A:prop, ~A -> A -> False.

Axiom andI : forall (A B : prop), A -> B -> A /\ B.

Axiom andEL : forall (A B : prop), A /\ B -> A.

Axiom andER : forall (A B : prop), A /\ B -> B.

Axiom orIL : forall (A B : prop), A -> A \/ B.

Axiom orIR : forall (A B : prop), B -> A \/ B.

Axiom orE : forall (A B C:prop), (A -> C) -> (B -> C) -> A \/ B -> C.

Section PropN.

Variable P1 P2 P3:prop.

Axiom and3I : P1 -> P2 -> P3 -> P1 /\ P2 /\ P3.
Axiom and3E : P1 /\ P2 /\ P3 -> (forall p:prop, (P1 -> P2 -> P3 -> p) -> p).
Axiom or3I1 : P1 -> P1 \/ P2 \/ P3.
Axiom or3I2 : P2 -> P1 \/ P2 \/ P3.
Axiom or3I3 : P3 -> P1 \/ P2 \/ P3.

End PropN.

Axiom iffI : forall A B:prop, (A -> B) -> (B -> A) -> (A <-> B).
Axiom iffEL : forall A B:prop, (A <-> B) -> A -> B.
Axiom iffER : forall A B:prop, (A <-> B) -> B -> A.
Axiom iff_ref : forall A:prop, A <-> A.

Axiom neq_i_sym: forall x y, x <> y -> y <> x.

Definition nIn : set->set->prop :=
fun x X => ~In x X.

(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.

Axiom Eps_i_ex : forall P:set -> prop, (exists x, P x) -> P (Eps_i P).

Axiom pred_ext : forall P Q:set -> prop, (forall x, P x <-> Q x) -> P = Q.
Axiom prop_ext_2 : forall p q:prop, (p -> q) -> (q -> p) -> p = q.
Axiom pred_ext_2 : forall P Q:set -> prop, P c= Q -> Q c= P -> P = Q.

Axiom Subq_ref : forall X:set, X c= X.
Axiom Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
Axiom Subq_contra : forall X Y z:set, X c= Y -> z /:e Y -> z /:e X.

Axiom EmptyE : forall x:set, x /:e Empty.
Axiom Subq_Empty : forall X:set, Empty c= X.
Axiom Empty_Subq_eq : forall X:set, X c= Empty -> X = Empty.
Axiom Empty_eq : forall X:set, (forall x, x /:e X) -> X = Empty.

Axiom UnionI : forall X x Y:set, x :e Y -> Y :e X -> x :e Union X.
Axiom UnionE : forall X x:set, x :e Union X -> exists Y:set, x :e Y /\ Y :e X.
Axiom UnionE_impred : forall X x:set, x :e Union X -> forall p:prop, (forall Y:set, x :e Y -> Y :e X -> p) -> p.

Axiom Union_Empty : Union Empty = Empty.

Axiom PowerI : forall X Y:set, Y c= X -> Y :e Power X.
Axiom PowerE : forall X Y:set, Y :e Power X -> Y c= X.
Axiom Power_Subq : forall X Y:set, X c= Y -> Power X c= Power Y.
Axiom Empty_In_Power : forall X:set, Empty :e Power X.
Axiom Self_In_Power : forall X:set, X :e Power X.

Axiom Union_Power_Subq : forall X:set, Union (Power X) c= X.

Axiom xm : forall P:prop, P \/ ~P.
Axiom dneg : forall P:prop, ~~P -> P.

Axiom ReplI : forall A:set, forall F:set->set, forall x:set, x :e A -> F x :e {F x|x :e A}.

Axiom ReplE : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> exists x :e A, y = F x.

Axiom ReplE_impred : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> forall p:prop, (forall x:set, x :e A -> y = F x -> p) -> p.

Axiom Repl_Empty : forall F:set -> set, {F x|x :e Empty} = Empty.

Axiom ReplEq_ext_sub : forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> {F x|x :e X} c= {G x|x :e X}.

Axiom ReplEq_ext : forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> {F x|x :e X} = {G x|x :e X}.

(* Parameter If_i "8c8f550868df4fdc93407b979afa60092db4b1bb96087bc3c2f17fadf3f35cbf" "b8ff52f838d0ff97beb955ee0b26fad79602e1529f8a2854bda0ecd4193a8a3c" *)
Parameter If_i : prop->set->set->set.

Notation IfThenElse If_i.

Axiom If_i_correct : forall p:prop, forall x y:set,
p /\ (if p then x else y) = x \/ ~p /\ (if p then x else y) = y.

Axiom If_i_0 : forall p:prop, forall x y:set,
~ p -> (if p then x else y) = y.

Axiom If_i_1 : forall p:prop, forall x y:set,
p -> (if p then x else y) = x.

Axiom If_i_or : forall p:prop, forall x y:set, (if p then x else y) = x \/ (if p then x else y) = y.

Axiom If_i_eta : forall p:prop, forall x:set, (if p then x else x) = x.

(* Parameter UPair "80aea0a41bb8a47c7340fe8af33487887119c29240a470e920d3f6642b91990d" "74243828e4e6c9c0b467551f19c2ddaebf843f72e2437cc2dea41d079a31107f" *)
Parameter UPair : set->set->set.

Notation SetEnum2 UPair.

Axiom UPairE :
forall x y z:set, x :e {y,z} -> x = y \/ x = z.

Axiom UPairI1 : forall y z:set, y :e {y,z}.

Axiom UPairI2 : forall y z:set, z :e {y,z}.

Axiom UPair_com : forall x y:set, {x,y} = {y,x}.

(* Parameter Sing "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" "bd01a809e97149be7e091bf7cbb44e0c2084c018911c24e159f585455d8e6bd0" *)
Parameter Sing : set -> set.
Notation SetEnum1 Sing.

Axiom SingI : forall x:set, x :e {x}. 
Axiom SingE : forall x y:set, y :e {x} -> y = x. 

(* Parameter binunion "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" "5e1ac4ac93257583d0e9e17d6d048ff7c0d6ccc1a69875b2a505a2d4da305784" *)
Parameter binunion : set -> set -> set.

(* Unicode :\/: "222a" *)
Infix :\/: 345 left := binunion.

Axiom binunionI1 : forall X Y z:set, z :e X -> z :e X :\/: Y.

Axiom binunionI2 : forall X Y z:set, z :e Y -> z :e X :\/: Y.

Axiom binunionE : forall X Y z:set, z :e X :\/: Y -> z :e X \/ z :e Y.

Definition SetAdjoin : set->set->set := fun X y => X :\/: {y}.

Notation SetEnum Empty Sing UPair SetAdjoin.

(* Parameter ReplSep "f627d20f1b21063483a5b96e4e2704bac09415a75fed6806a2587ce257f1f2fd" "ec807b205da3293041239ff9552e2912636525180ddecb3a2b285b91b53f70d8" *)
Parameter ReplSep : set->(set->prop)->(set->set)->set.
Notation ReplSep ReplSep.

Axiom ReplSepI: forall X:set, forall P:set->prop, forall F:set->set, forall x:set, x :e X -> P x -> F x :e {F x|x :e X, P x}.

Axiom ReplSepE:forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> exists x:set, x :e X /\ P x /\ y = F x.

Axiom ReplSepE_impred: forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> forall p:prop, (forall x :e X, P x -> y = F x -> p) -> p.

Axiom In_irref : forall x, x /:e x.

(* Parameter ordsucc "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "65d8837d7b0172ae830bed36c8407fcd41b7d875033d2284eb2df245b42295a6" *)
Parameter ordsucc : set->set.

Axiom ordsuccI1 : forall x:set, x c= ordsucc x.
Axiom ordsuccI2 : forall x:set, x :e ordsucc x.
Axiom ordsuccE : forall x y:set, y :e ordsucc x -> y :e x \/ y = x.

Notation Nat Empty ordsucc.

Axiom neq_0_ordsucc : forall a:set, 0 <> ordsucc a.
Axiom neq_ordsucc_0 : forall a:set, ordsucc a <> 0.

Axiom ordsucc_inj : forall a b:set, ordsucc a = ordsucc b -> a = b.
Axiom ordsucc_inj_contra : forall a b:set, a <> b -> ordsucc a <> ordsucc b.

Axiom ZF_closed_I : forall U,
 Union_closed U ->
 Power_closed U ->
 Repl_closed U ->
 ZF_closed U.

Axiom ZF_closed_E : forall U, ZF_closed U ->
 forall p:prop,
 (Union_closed U ->
  Power_closed U ->
  Repl_closed U -> p)
 -> p.

Axiom ZF_Union_closed : forall U, ZF_closed U ->
  forall X :e U, Union X :e U.

Axiom ZF_Power_closed : forall U, ZF_closed U ->
  forall X :e U, Power X :e U.

Axiom ZF_Repl_closed : forall U, ZF_closed U ->
  forall X :e U, forall F:set->set, (forall x :e X, F x :e U) -> {F x|x:eX} :e U.

Axiom ZF_UPair_closed : forall U, ZF_closed U ->
  forall x y :e U, {x,y} :e U.

Axiom ZF_Sing_closed : forall U, ZF_closed U ->
  forall x :e U, {x} :e U.

Axiom ZF_binunion_closed : forall U, ZF_closed U ->
  forall X Y :e U, (X :\/: Y) :e U.

Axiom ZF_ordsucc_closed : forall U, ZF_closed U ->
  forall x :e U, ordsucc x :e U.

Definition ordinal : set->prop := fun (alpha:set) => TransSet alpha /\ forall beta :e alpha, TransSet beta.

Axiom ordinal_TransSet : forall alpha:set, ordinal alpha -> TransSet alpha.

Axiom ordinal_In_TransSet : forall alpha:set, ordinal alpha -> forall beta :e alpha, TransSet beta.

Axiom ordinal_Empty : ordinal Empty.

Axiom ordinal_Hered : forall alpha:set, ordinal alpha -> forall beta :e alpha, ordinal beta.

Axiom TransSet_ordsucc : forall X:set, TransSet X -> TransSet (ordsucc X).

Axiom ordinal_ordsucc : forall alpha:set, ordinal alpha -> ordinal (ordsucc alpha).

Axiom ordinal_1 : ordinal 1.

Axiom ordinal_2 : ordinal 2.

Axiom TransSet_ordsucc_In_Subq : forall X:set, TransSet X -> forall x :e X, ordsucc x c= X.

Axiom ordinal_ordsucc_In_Subq : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta c= alpha.

Axiom ordinal_trichotomy_or : forall alpha beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.

Axiom ordinal_In_Or_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha :e beta \/ beta c= alpha.

Definition inj : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall u v :e X, f u = f v -> u = v).

Definition surj : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall w :e Y, exists u :e X, f u = w).

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

Axiom bij_comp : forall X Y Z:set, forall f g:set->set, bij X Y f -> bij Y Z g -> bij X Z (fun x => g (f x)).

Axiom bij_id : forall X, bij X X (fun x => x).

Axiom bij_inj : forall X Y, forall f:set -> set, bij X Y f -> inj X Y f.

Axiom bij_surj : forall X Y, forall f:set -> set, bij X Y f -> surj X Y f.

Axiom inj_surj_bij : forall X Y, forall f:set -> set, inj X Y f -> surj X Y f -> bij X Y f.

Axiom surj_inv_inj : forall X Y, forall f:set -> set, (forall y :e Y, exists x :e X, f x = y) -> inj Y X (inv X f).

Definition atleastp : set -> set -> prop
 := fun X Y : set => exists f : set -> set, inj X Y f.

Definition equip : set -> set -> prop
 := fun X Y : set => exists f : set -> set, bij X Y f.

Axiom equip_ref : forall X, equip X X.
Axiom equip_sym : forall X Y, equip X Y -> equip Y X.
Axiom equip_tra : forall X Y Z, equip X Y -> equip Y Z -> equip X Z.

Axiom SchroederBernstein: forall A B, forall f g:set -> set, inj A B f -> inj B A g -> equip A B.

Axiom f_eq_i : forall f:set -> set, forall x y, x = y -> f x = f y.
Axiom f_eq_i_i : forall f:set -> set -> set, forall x y z w, x = y -> z = w -> f x z = f y w.
Axiom eq_i_tra : forall x y z, x = y -> y = z -> x = z.

Section EpsilonRec_i.

Variable F:set -> (set -> set) -> set.

(* Parameter In_rec_i "f97da687c51f5a332ff57562bd465232bc70c9165b0afe0a54e6440fc4962a9f" "fac413e747a57408ad38b3855d3cde8673f86206e95ccdadff2b5babaf0c219e" *)
Parameter In_rec_i : set -> set.

Hypothesis Fr:forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.

Axiom In_rec_i_eq : forall X:set, In_rec_i X = F X In_rec_i.

End EpsilonRec_i.

Definition bigintersect := fun (D:(set->prop)->prop) (x:set) => forall P:set->prop, D P -> P x.

Definition reflexive : (set->set->prop)->prop := fun R => forall x:set, R x x.
Definition irreflexive : (set->set->prop)->prop := fun R => forall x:set, ~R x x.
Definition symmetric : (set->set->prop)->prop := fun R => forall x y:set, R x y -> R y x.
Definition antisymmetric : (set->set->prop)->prop := fun R => forall x y:set, R x y -> R y x -> x = y.
Definition transitive : (set->set->prop)->prop := fun R => forall x y z:set, R x y -> R y z -> R x z.
Definition eqreln : (set->set->prop)->prop := fun R => reflexive R /\ symmetric R /\ transitive R.
Definition per : (set->set->prop)->prop := fun R => symmetric R /\ transitive R.
Definition linear : (set->set->prop)->prop := fun R => forall x y:set, R x y \/ R y x.
Definition trichotomous_or : (set->set->prop)->prop := fun R => forall x y:set, R x y \/ x = y \/ R y x.
Definition partialorder : (set->set->prop)->prop := fun R => reflexive R /\ antisymmetric R /\ transitive R.
Definition totalorder : (set->set->prop)->prop := fun R => partialorder R /\ linear R.
Definition strictpartialorder : (set->set->prop)->prop := fun R => irreflexive R /\ transitive R.
Definition stricttotalorder : (set->set->prop)->prop := fun R => strictpartialorder R /\ trichotomous_or R.

Axiom partialorder_strictpartialorder : forall R:set->set->prop,
  partialorder R -> strictpartialorder (fun x y => R x y /\ x <> y).

Axiom least_ordinal_ex : forall p:set -> prop, (exists alpha, ordinal alpha /\ p alpha) -> exists alpha, ordinal alpha /\ p alpha /\ forall beta :e alpha, ~p beta.

Axiom ordinal_trichotomy_or_impred : forall alpha beta, ordinal alpha -> ordinal beta -> forall p:prop, (alpha :e beta -> p) -> (alpha = beta -> p) -> (beta :e alpha -> p) -> p.

(** Preamble End **)

(** Three helper results **)
Theorem injI : forall X Y, forall f:set -> set, (forall x :e X, f x :e Y) -> (forall x z :e X, f x = f z -> x = z) -> inj X Y f.
let X Y f. assume H1 H2.
prove (forall x :e X, f x :e Y) /\ (forall x z :e X, f x = f z -> x = z).
apply andI.
- exact H1.
- exact H2.
Qed.

Theorem Subq_atleastp : forall X Y, X c= Y -> atleastp X Y.
let X Y.
assume H1: X c= Y.
set f : set -> set := fun x => x.
prove exists f:set->set, inj X Y f.
witness f. apply injI.
- exact H1.
- let x. assume Hx: x :e X.
  let x'. assume Hx': x' :e X.
  assume H2: x = x'.
  exact H2.
Qed.

Theorem atleastp_antisym_equip: forall A B, atleastp A B -> atleastp B A -> equip A B.
let A B.
assume H1: atleastp A B.
assume H2: atleastp B A.
apply H1.
let f. assume Hf: inj A B f.
apply H2.
let g. assume Hg: inj B A g.
exact SchroederBernstein A B f g Hf Hg.
Qed.

(** Zermelo Well Ordering Theorem **)
Section Zermelo1908.

Binder some , := Eps_i.

Let prime := fun (p:set -> prop) (x:set) => p x /\ x <> some x:set, p x.

Postfix ' 200 := prime.

Let C : (set -> prop) -> prop := fun p:set -> prop =>
  forall Q:(set -> prop) -> prop,
       (forall p:set->prop, Q p -> Q (p '))
    -> (forall D:(set->prop)->prop, D c= Q -> Q (bigintersect D))
    -> Q p.

Lemma C_prime : forall p:set->prop, C p -> C (p ').
let p.
assume H1: C p.
let Q.
assume H2: forall p:set->prop, Q p -> Q (p ').
assume H3: forall D:(set->prop)->prop, D c= Q -> Q (bigintersect D).
prove Q (p ').
apply H2.
prove Q p.
exact (H1 Q H2 H3).
Qed.

Lemma C_int : forall D:(set->prop)->prop, D c= C -> C (bigintersect D).
let D.
assume H1: D c= C.
let Q.
assume H2: forall p:set->prop, Q p -> Q (p ').
assume H3: forall D:(set->prop)->prop, D c= Q -> Q (bigintersect D).
prove Q (bigintersect D).
apply H3.
prove D c= Q.
let p.
assume H4:D p.
prove Q p.
exact (H1 p H4 Q H2 H3).
Qed.

Lemma C_ind : forall Q:(set->prop)->prop,
       (forall p:set->prop, C p -> Q p -> Q (p '))
    -> (forall D:(set->prop)->prop, D c= C -> D c= Q -> Q (bigintersect D))
    -> C c= Q.
let Q.
assume H1: forall p:set->prop, C p -> Q p -> Q (p ').
assume H2: forall D:(set->prop)->prop, D c= C -> D c= Q -> Q (bigintersect D).
let p.
assume H3: C p.
claim L1:C p /\ Q p.
{
  apply H3.
  - prove forall q:set->prop, C q /\ Q q -> C (q ') /\ Q (q ').
    let q. assume H4: C q /\ Q q. apply H4. assume H5: C q. assume H6: Q q. apply andI.
    + prove (C (q ')). apply (C_prime q). exact H5.
    + prove (Q (q ')). exact (H1 q H5 H6).
  - prove forall D:(set->prop)->prop, (forall q:set->prop, D q -> C q /\ Q q) -> C (bigintersect D) /\ Q (bigintersect D).
    let D. assume H4: (forall q:set->prop, D q -> C q /\ Q q). apply andI.
    + prove (C (bigintersect D)). apply (C_int D). let q. assume H5. apply (H4 q H5). assume H6 _. exact H6.
    + prove (Q (bigintersect D)). apply (H2 D).
      * prove (D c= C). let q. assume H5. apply (H4 q H5). assume H6 _. exact H6.
      * prove (D c= Q). let q. assume H5. apply (H4 q H5). assume _ H6. exact H6.
}
apply L1.
assume _.
assume H4:Q p.
exact H4.
Qed.

Section Cp.

Variable p:set->prop.

Lemma C_lin : C p -> forall q:set->prop, C q -> q c= p \/ p c= q.
assume Hp:C p.
prove ((fun p:set->prop => forall q:set->prop, C q -> q c= p \/ p c= q) p).
apply (Hp (fun p => forall q:set->prop, C q -> q c= p \/ p c= q)).
- let p. 
  assume IHp: forall q:set->prop, C q -> q c= p \/ p c= q.
  prove forall q:set->prop, C q -> q c= p ' \/ p ' c= q.
  prove forall q:set->prop, C q -> (fun q:set->prop => q c= p ' \/ p ' c= q) q.
  apply (C_ind (fun q => q c= p ' \/ p ' c= q)).
  + let q.
    assume Hq:C q.
    assume IHq: q c= p ' \/ p ' c= q.
    prove q ' c= p ' \/ p ' c= q '.
    apply IHq.
    * assume IHq1: q c= p '. apply orIL. prove q ' c= p '.
      let x.
      assume H1: q x /\ x <> some x:set, q x.
      prove p ' x. apply IHq1.
      prove q x.
      exact (andEL (q x) (x <> some x:set, q x) H1).
    * { assume IHq2: p ' c= q.
        apply (IHp (q ') (C_prime q Hq)).
	- assume IHp1: q ' c= p.
          apply (xm (p ' (some x:set, q x))).
          + assume H2: p ' (some x:set, q x).
            apply (xm (q ' (some x:set, p x))).
            * { assume H3: q ' (some x:set, p x).
                claim L1: (some x:set, p x) <> (some x:set, q x).
                {
                   exact (andER (q (some x:set, p x)) ((some x:set, p x) <> (some x:set, q x)) H3).
		}
                claim L2: p <> q.
                {
                   assume H4: p = q. apply L1. rewrite <- H4. reflexivity.
                }
                apply L2.
                prove p = q.
		apply pred_ext. let x. apply iffI.
		- assume H4: p x.
                  prove q x.
		  apply (xm (x = some x:set, p x)).
		  + assume H5: x = some x:set, p x. rewrite H5. exact (andEL (q (some x:set, p x)) ((some x:set, p x) <> (some x:set, q x)) H3).
		  + assume H5: x <> some x:set, p x. apply IHq2. exact (andI (p x) (x <> (some x:set, p x)) H4 H5).
		- assume H4: q x.
                  prove p x.
		  apply (xm (x = some x:set, q x)).
		  + assume H5: x = some x:set, q x. rewrite H5. exact (andEL (p (some x:set, q x)) ((some x:set, q x) <> (some x:set, p x)) H2).
		  + assume H5: x <> some x:set, q x. apply IHp1. exact (andI (q x) (x <> (some x:set, q x)) H4 H5).
              }
            * { assume H3: ~ q ' (some x:set, p x).
                apply orIL. prove q ' c= p '.
                let x.
   	        assume H4: q ' x.
	        prove p x /\ x <> some x:set, p x.
                apply andI.
	        - apply IHp1. exact H4.
	        - assume H5: x = some x:set, p x. apply H3. rewrite <- H5. exact H4.
              }
          + assume H2: ~ p ' (some x:set, q x).
            apply orIR. prove p ' c= q '.
            let x.
	    assume H3: p ' x.
	    prove q x /\ x <> some x:set, q x.
            apply andI.
	    * apply IHq2. exact H3.
	    * assume H4: x = some x:set, q x. apply H2. rewrite <- H4. exact H3.
	- assume IHp2: p c= q '.
          apply orIR. prove p ' c= q '.
          let x.
          assume H2: p x /\ x <> some x:set, p x.
          prove q ' x. apply IHp2. exact (andEL (p x) (x <> some x:set, p x) H2).
      }
  + let E.
    assume HE: forall q:set->prop, E q -> C q.
    assume IHE: forall q:set->prop, E q -> q c= p ' \/ p ' c= q.
    prove bigintersect E c= p ' \/ p ' c= bigintersect E.
    apply (xm (exists q:set->prop, E q /\ q c= p ')).
    * assume H1: exists q:set->prop, E q /\ q c= p '.
      apply orIL.
      prove bigintersect E c= p '.
      apply H1. let q. assume H2: E q /\ q c= p '. apply H2.
      assume H3: E q.
      assume H4: q c= p '.
      let x. assume H5: bigintersect E x. prove p ' x. apply H4. prove q x. exact (H5 q H3).
    * { assume H1: ~exists q:set->prop, E q /\ q c= p '.
        apply orIR.
        prove p ' c= bigintersect E.
        let x. assume H2: p ' x. let q. assume H3: E q. prove q x.
        apply (IHE q H3).
        - assume IHE1: q c= p '. apply H1. witness q. exact (andI (E q) (q c= p ') H3 IHE1).
        - assume IHE2: p ' c= q. exact (IHE2 x H2).
      }
- let D.
  assume IHD: forall p:set->prop, D p -> forall q:set->prop, C q -> q c= p \/ p c= q.
  prove forall q:set->prop, C q -> q c= bigintersect D \/ bigintersect D c= q.
  let q. assume Hq:C q.
  apply (xm (exists p:set->prop, D p /\ p c= q)).
  + assume H1: exists p:set->prop, D p /\ p c= q.
    apply orIR.
    prove bigintersect D c= q.
    apply H1. let p. assume H2: D p /\ p c= q. apply H2.
    assume H3: D p.
    assume H4: p c= q.
    let x. assume H5: bigintersect D x. prove q x. apply H4. prove p x. exact (H5 p H3).
  + assume H1: ~exists p:set->prop, D p /\ p c= q.
    apply orIL.
    prove q c= bigintersect D.
    let x. assume H2: q x. let p. assume H3: D p. prove p x.
    apply (IHD p H3 q Hq).
    * assume IHD1: q c= p. exact (IHD1 x H2).
    * assume IHD2: p c= q. apply H1. witness p. exact (andI (D p) (p c= q) H3 IHD2).
Qed.

End Cp.

Lemma C_Eps : forall p:set->prop, C p -> forall q:set->prop, C q -> q (some x:set, p x) -> p c= q.
let p. assume Hp:C p. let q. assume Hq: C q. assume H1: q (some x:set, p x).
apply (C_lin (p ') (C_prime p Hp) q Hq).
- assume H2: q c= p '.
  claim L1: p ' (some x:set, p x).
  {
    apply H2. exact H1.
  }
  claim L2:((some x:set, p x) <> (some x:set, p x)).
  {
    exact (andER (p (some x:set, p x)) ((some x:set, p x) <> (some x:set, p x)) L1).
  }
  apply L2. reflexivity.
- assume H2: p ' c= q.
  prove p c= q.
  let x. assume H3: p x.
  prove q x.
  apply (xm (x = some x:set, p x)).
  + assume H4: x = some x:set, p x. rewrite H4. exact H1.
  + assume H4: x <> some x:set, p x. apply H2. prove (p x /\ x <> some x:set, p x). apply andI.
    * exact H3.
    * exact H4.
Qed.

Let clos := fun (p:set -> prop) => bigintersect (fun q => C q /\ p c= q).

Section closp.

Variable p:set->prop.

Lemma C_clos : C (clos p).
prove (C (bigintersect (fun q:set->prop => C q /\ p c= q))).
apply (C_int (fun q:set->prop => C q /\ p c= q)).
prove (fun q:set->prop => C q /\ p c= q) c= C.
let q. assume H1: C q /\ p c= q. exact (andEL (C q) (p c= q) H1).
Qed.

Lemma clos_subq : forall x:set, p x -> clos p x.
let x. assume H1: p x. let q. assume H2: C q /\ p c= q. prove q x.
exact (andER (C q) (p c= q) H2 x H1).
Qed.

Lemma clos_Eps : (exists x:set, p x) -> p (some x:set, clos p x).
assume H1. apply dneg. assume H2: ~p (some x:set, clos p x).
set q := (clos p) '.
claim L1: ~ q (some x:set, clos p x).
{
  assume H3: clos p (some x:set, clos p x) /\ (some x:set, clos p x) <> (some x:set, clos p x).
  apply (andER (clos p (some x:set, clos p x)) ((some x:set, clos p x) <> (some x:set, clos p x)) H3).
  reflexivity.
}
claim L2: C q.
{
  prove C ((clos p) ').
  apply (C_prime (clos p)).
  prove C (clos p).
  apply C_clos.
}
claim L3: p c= q.
{
  let x. assume H3: p x.
  prove (clos p x /\ x <> some x:set, clos p x). apply andI.
  - exact (clos_subq x H3).
  - assume H4: x = some x:set, clos p x.
    apply H2.
    prove p (some x:set, clos p x).
    rewrite <- H4. exact H3.
}
claim L4: clos p c= q.
{
  let x. assume H3: clos p x.
  exact (H3 q (andI (C q) (p c= q) L2 L3)).
}
claim L5: exists x:set, clos p x.
{
  apply H1.
  let x. assume H3: p x.
  prove exists x:set, clos p x.
  witness x.
  prove clos p x.
  apply (clos_subq x).
  prove p x.
  exact H3.
}
claim L6: clos p (some x:set, clos p x).
{
  exact (Eps_i_ex (clos p) L5).
}
exact (L1 (L4 (some x:set, clos p x) L6)).
Qed.

End closp.

Definition ZermeloWO := fun (a:set) => clos (fun x => x = a).

Let R := ZermeloWO.

Infix <= 490 := R.

Lemma CR : forall a:set, C (R a).
let a. exact (C_clos (fun x => x = a)).
Qed.

Lemma R_ref : reflexive R.
let a.
prove (a <= a).
prove clos (fun x => x = a) a.
apply (clos_subq (fun x => x = a) a).
prove a = a.
reflexivity.
Qed.

Lemma R_Eps : forall a:set, (some x:set, R a x) = a.
let a.
claim L1: exists x:set, x = a.
{
  witness a.
  reflexivity.
}
exact (clos_Eps (fun x => x = a) L1).
Qed.

Lemma R_lin : linear R.
let a b.
prove a <= b \/ b <= a.
apply (C_lin (R a) (CR a) (R b) (CR b)).
- assume H1: R b c= R a.
  apply orIL.
  prove R a b.
  apply (H1 b).
  exact (R_ref b).
- assume H1: R a c= R b.
  apply orIR.
  prove R b a.
  apply (H1 a).
  exact (R_ref a).
Qed.

Lemma R_tra : transitive R.
let a b c. assume H1: a <= b. assume H2: b <= c.
prove clos (fun x => x = a) c.
let p. assume H3: C p /\ (fun x:set => x = a) c= p.
prove p c.
claim L1: (fun x:set => x = b) c= p.
{
  let x. assume H4: x = b.
  prove p x.
  rewrite H4.
  prove p b.
  exact (H1 p H3).
}
claim L2: C p /\ (fun x:set => x = b) c= p.
{
  apply andI.
  - exact (andEL (C p) ((fun x:set => x = a) c= p) H3).
  - exact L1.
}
exact (H2 p L2).
Qed.

Lemma R_antisym : antisymmetric R.
let a b. assume H1: a <= b. assume H2: b <= a.
prove a = b.
rewrite <- (R_Eps a).
rewrite <- (R_Eps b).
prove (some x:set, R a x) = (some x:set, R b x).
claim L1: R a = R b.
{
  apply pred_ext. let c. apply iffI.
  - assume H3:R a c. prove R b c. exact (R_tra b a c H2 H3).
  - assume H3:R b c. prove R a c. exact (R_tra a b c H1 H3).
}
rewrite L1.
reflexivity.
Qed.

Lemma R_partialorder : partialorder R.
prove reflexive R /\ antisymmetric R /\ transitive R.
apply and3I.
- exact R_ref.
- exact R_antisym.
- exact R_tra.
Qed.

Lemma R_totalorder : totalorder R.
prove partialorder R /\ linear R.
apply andI.
- exact R_partialorder.
- exact R_lin.
Qed.

Lemma R_wo : forall p:set->prop, (exists x:set, p x) -> exists x:set, p x /\ forall y:set, p y -> x <= y.
let p. assume H1: exists x:set, p x.
set z := some x:set, clos p x.
witness z. apply andI.
- prove p z.
  exact (clos_Eps p H1).
- prove forall y:set, p y -> z <= y.
  let y. assume H2: p y.
  prove (clos (fun x:set => x = z) y).
  let q. assume H3: C q /\ (fun x:set => x = z) c= q.
  apply H3. assume H4: C q. assume H5: (fun x:set => x = z) c= q.
  claim L1: q z.
  {
    exact (H5 z (fun r H => H)).
  }
  claim L2: clos p c= q.
  {
    exact (C_Eps (clos p) (C_clos p) q H4 L1).
  }
  prove q y.
  apply L2.
  prove clos p y.
  exact (clos_subq p y H2).
Qed.

Definition ZermeloWOstrict := fun (a b:set) => R a b /\ a <> b.
Let lt := ZermeloWOstrict.

Infix < 490 := lt.

Lemma lt_trich : trichotomous_or lt.
let a b.
prove (a < b \/ a = b \/ b < a).
apply (xm (a = b)).
- assume H1: a = b. apply or3I2. exact H1.
- assume H1: a <> b.
  apply (R_lin a b).
  + assume H2: a <= b. apply or3I1. prove a <= b /\ a <> b. apply andI.
    * exact H2.
    * exact H1.
  + assume H2: b <= a. apply or3I3. prove b <= a /\ b <> a. apply andI.
    * exact H2.
    * apply neq_i_sym. exact H1.
Qed.

Lemma lt_stricttotalorder : stricttotalorder lt.
prove strictpartialorder lt /\ trichotomous_or lt.
apply andI.
- prove strictpartialorder (fun a b => R a b /\ a <> b).
  apply (partialorder_strictpartialorder R).
  prove partialorder R.
  exact R_partialorder.
- exact lt_trich.
Qed.

Lemma lt_wo : forall (p:set -> prop), (exists x:set, p x) -> exists x:set, p x /\ forall y:set, p y /\ y <> x -> x < y.
let p. assume H1.
apply (R_wo p H1).
let x. assume H1: p x /\ forall y:set, p y -> x <= y.
apply H1. assume H2 H3.
witness x. apply andI.
- exact H2.
- let y. assume H4. apply H4. assume H5 H6.
  prove x <= y /\ x <> y.
  apply andI.
  + exact (H3 y H5).
  + apply neq_i_sym. exact H6.
Qed.

Theorem Zermelo_WO : exists r : set -> set -> prop,
    totalorder r
 /\ (forall p:set->prop, (exists x:set, p x) -> exists x:set, p x /\ forall y:set, p y -> r x y).
witness R.
apply andI.
- exact R_totalorder.
- exact R_wo.
Qed.

Theorem Zermelo_WO_strict : exists r : set -> set -> prop,
    stricttotalorder r
 /\ (forall p:set->prop, (exists x:set, p x) -> exists x:set, p x /\ forall y:set, p y /\ y <> x -> r x y).
witness lt. apply andI.
- exact lt_stricttotalorder.
- exact lt_wo.
Qed.

Definition ordinals_into_set : set -> set -> set
 := fun X =>
      In_rec_i (fun alpha f => some x, x :e X /\ (forall beta :e alpha, f beta < x) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y)).

Theorem ordinals_into_set_eq: forall X alpha,
   ordinals_into_set X alpha
 = some x, x :e X /\ (forall beta :e alpha, ordinals_into_set X beta < x) /\ (forall y :e X, (forall beta :e alpha, ordinals_into_set X beta < y) -> x < y \/ x = y).
let X.
set Phi : set -> (set -> set) -> set := fun alpha f => some x, x :e X /\ (forall beta :e alpha, f beta < x) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y).
set f : set -> set := ordinals_into_set X.
set f' : set -> set := fun alpha => Phi alpha f.
claim L1: forall alpha, forall g h:set -> set, (forall beta :e alpha, g beta = h beta) -> Phi alpha g = Phi alpha h.
{ let alpha g h.
  assume H1: forall beta :e alpha, g beta = h beta.
  prove (some x, x :e X /\ (forall beta :e alpha, g beta < x) /\ (forall y :e X, (forall beta :e alpha, g beta < y) -> x < y \/ x = y))
      = (some x, x :e X /\ (forall beta :e alpha, h beta < x) /\ (forall y :e X, (forall beta :e alpha, h beta < y) -> x < y \/ x = y)).
  claim L1a: (fun x:set => x :e X /\ (forall beta :e alpha, g beta < x) /\ (forall y :e X, (forall beta :e alpha, g beta < y) -> x < y \/ x = y))
           = (fun x:set => x :e X /\ (forall beta :e alpha, h beta < x) /\ (forall y :e X, (forall beta :e alpha, h beta < y) -> x < y \/ x = y)).
  { apply pred_ext.
    let x.
    apply iffI.
    - assume H2abc. apply H2abc. assume H2ab H2c. apply H2ab. assume H2a H2b.
      prove x :e X /\ (forall beta :e alpha, h beta < x) /\ (forall y :e X, (forall beta :e alpha, h beta < y) -> x < y \/ x = y).
      apply and3I.
      + exact H2a.
      + prove forall beta :e alpha, h beta < x.
        let beta. assume Hb.
	rewrite <- H1 beta Hb.
	exact H2b beta Hb.
      + prove forall y :e X, (forall beta :e alpha, h beta < y) -> x < y \/ x = y.
        let y. assume Hy.
	assume H3: forall beta :e alpha, h beta < y.
	prove x < y \/ x = y.
	apply H2c y Hy.
	let beta. assume Hb.
	rewrite H1 beta Hb.
	exact H3 beta Hb.
    - assume H2abc. apply H2abc. assume H2ab H2c. apply H2ab. assume H2a H2b.
      prove x :e X /\ (forall beta :e alpha, g beta < x) /\ (forall y :e X, (forall beta :e alpha, g beta < y) -> x < y \/ x = y).
      apply and3I.
      + exact H2a.
      + prove forall beta :e alpha, g beta < x.
        let beta. assume Hb.
	rewrite H1 beta Hb.
	exact H2b beta Hb.
      + prove forall y :e X, (forall beta :e alpha, g beta < y) -> x < y \/ x = y.
        let y. assume Hy.
	assume H3: forall beta :e alpha, g beta < y.
	prove x < y \/ x = y.
	apply H2c y Hy.
	let beta. assume Hb.
	rewrite <- H1 beta Hb.
	exact H3 beta Hb.
  }
  exact L1a (fun u v => (some x, x :e X /\ (forall beta :e alpha, g beta < x) /\ (forall y :e X, (forall beta :e alpha, g beta < y) -> x < y \/ x = y)) = Eps_i u) (fun q H => H).
}
prove forall alpha, f alpha = f' alpha.
exact In_rec_i_eq Phi L1.
Qed.

Theorem ordinals_into_set_props: forall X alpha, ordinal alpha ->
    (exists x :e X, forall beta :e alpha, ordinals_into_set X beta < x)
 -> ordinals_into_set X alpha :e X
 /\ (forall beta :e alpha, ordinals_into_set X beta < ordinals_into_set X alpha)
 /\ (forall y :e X, (forall beta :e alpha, ordinals_into_set X beta < y) -> ordinals_into_set X alpha < y \/ ordinals_into_set X alpha = y).
let X alpha.
assume Ha1: ordinal alpha.
assume Ha2: exists x :e X, forall beta :e alpha, ordinals_into_set X beta < x.
set Phi : set -> (set -> set) -> set := fun alpha f => some x, x :e X /\ (forall beta :e alpha, f beta < x) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y).
set f : set -> set := ordinals_into_set X.
set f' : set -> set := fun alpha => Phi alpha f.
set p : set -> prop := fun x => x :e X /\ forall beta :e alpha, f beta < x.
apply lt_wo p Ha2.
let x. assume H. apply H. assume H1.
apply H1.
assume Hx1: x :e X.
assume Hx2: forall beta :e alpha, f beta < x.
assume Hx3: forall y, p y /\ y <> x -> x < y.
claim L1: exists x, x :e X /\ (forall beta :e alpha, f beta < x) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y).
{ witness x. apply and3I.
  - exact Hx1.
  - exact Hx2.
  - let y.
    assume Hy1: y :e X.
    assume Hy2: forall beta :e alpha, f beta < y.
    prove x < y \/ x = y.
    apply xm (y = x).
    + assume Hyx: y = x. apply orIR. symmetry. exact Hyx.
    + assume Hyx: y <> x. apply orIL.
      prove x < y.
      apply Hx3.
      prove p y /\ y <> x.
      apply andI.
      * { prove p y.
          prove y :e X /\ forall beta :e alpha, f beta < y.
	  apply andI.
	  - exact Hy1.
	  - exact Hy2.
	}
      * exact Hyx.
}
rewrite ordinals_into_set_eq X alpha.
prove f' alpha :e X /\ (forall beta :e alpha, f beta < f' alpha) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> f' alpha < y \/ f' alpha = y).
exact Eps_i_ex (fun x => x :e X /\ (forall beta :e alpha, f beta < x) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y)) L1.
Qed.

Theorem ordinals_into_set_uniq: forall X alpha, ordinal alpha ->
 forall x :e X,
      (forall beta :e alpha, ordinals_into_set X beta < x)
   -> (forall y :e X, (forall beta :e alpha, ordinals_into_set X beta < y) -> x < y \/ x = y)
   -> ordinals_into_set X alpha = x.
let X alpha.
assume Ha: ordinal alpha.
set Phi : set -> (set -> set) -> set := fun alpha f => some x, x :e X /\ (forall beta :e alpha, f beta < x) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y).
set f : set -> set := ordinals_into_set X.
let x.
assume Hx1: x :e X.
assume Hx2: forall beta :e alpha, f beta < x.
assume Hx3: forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y.
prove f alpha = x.
claim L1: exists x :e X, forall beta :e alpha, f beta < x.
{ witness x. apply andI.
  - exact Hx1.
  - exact Hx2.
}
apply ordinals_into_set_props X alpha Ha L1. assume H. apply H.
assume H1: f alpha :e X.
assume H2: forall beta :e alpha, f beta < f alpha.
assume H3: forall y :e X, (forall beta :e alpha, f beta < y) -> f alpha < y \/ f alpha = y.
apply lt_stricttotalorder.
assume Hspo Htrich.
apply Hspo.
assume Hirref Htra.
apply H3 x Hx1 Hx2.
- assume H4: f alpha < x.
  apply Hx3 (f alpha) H1 H2.
  + assume H5: x < f alpha.
    prove False.
    apply Hirref x.
    prove x < x.
    exact Htra x (f alpha) x H5 H4.
  + assume H5: x = f alpha.
    symmetry.
    exact H5.
- assume H4: f alpha = x.
  exact H4.
Qed.

Definition set_into_ordinals : set -> set -> set := fun X x => some alpha,    ordinal alpha
 /\ ordinals_into_set X alpha = x
 /\ forall beta :e alpha, ordinals_into_set X beta <> x.

Theorem set_into_ordinals_prop: forall X, forall x :e X,
    (exists alpha, ordinal alpha /\ ordinals_into_set X alpha = x)
 -> ordinal (set_into_ordinals X x)
 /\ ordinals_into_set X (set_into_ordinals X x) = x
 /\ forall beta :e set_into_ordinals X x, ordinals_into_set X beta <> x.
let X x. assume Hx: x :e X.
set Phi : set -> (set -> set) -> set := fun alpha f => some x, x :e X /\ (forall beta :e alpha, f beta < x) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y).
set f : set -> set := ordinals_into_set X.
set g : set -> set := fun x => some alpha, ordinal alpha /\ f alpha = x /\ forall beta :e alpha, f beta <> x.
assume H1: exists alpha, ordinal alpha /\ f alpha = x.
claim L1: exists alpha, ordinal alpha /\ f alpha = x /\ forall beta :e alpha, f beta <> x.
{ exact least_ordinal_ex (fun alpha => f alpha = x) H1. }
prove ordinal (g x) /\ f (g x) = x /\ forall beta :e g x, f beta <> x.
exact Eps_i_ex (fun alpha => ordinal alpha /\ f alpha = x /\ forall beta :e alpha, f beta <> x) L1.
Qed.

Theorem set_into_ordinals_ordinals_into_set_prop1: forall X,
 forall alpha, ordinal alpha
  -> ordinals_into_set X alpha :e X
  -> (forall beta :e alpha, ordinals_into_set X beta < ordinals_into_set X alpha)
  -> (forall x :e X, (forall beta :e alpha, ordinals_into_set X beta < x) -> ordinals_into_set X alpha < x \/ ordinals_into_set X alpha = x)
  -> set_into_ordinals X (ordinals_into_set X alpha) = alpha.
let X.
set Phi : set -> (set -> set) -> set := fun alpha f => some x, x :e X /\ (forall beta :e alpha, f beta < x) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y).
set f : set -> set := ordinals_into_set X.
set g : set -> set := fun x => some alpha, ordinal alpha /\ f alpha = x /\ forall beta :e alpha, f beta <> x.
let alpha.
assume Ha: ordinal alpha.
assume H1: f alpha :e X.
assume H2: forall beta :e alpha, f beta < f alpha.
assume H3: forall x :e X, (forall beta :e alpha, f beta < x) -> f alpha < x \/ f alpha = x.
prove g (f alpha) = alpha.
claim L1: exists beta, ordinal beta /\ f beta = f alpha.
{ witness alpha. apply andI.
  - exact Ha.
  - reflexivity.
}
apply lt_stricttotalorder.
assume Hspo Htrich.
apply Hspo.
assume Hirref Htra.
apply set_into_ordinals_prop X (f alpha) H1 L1.
assume H. apply H.
assume H4: ordinal (g (f alpha)).
assume H5: f (g (f alpha)) = f alpha.
assume H6: forall beta :e g (f alpha), f beta <> f alpha.
apply ordinal_trichotomy_or_impred (g (f alpha)) alpha H4 Ha.
- assume H7: g (f alpha) :e alpha.
  apply Hirref (f alpha).
  prove f alpha < f alpha.
  rewrite <- H5 at 1.
  prove f (g (f alpha)) < f alpha.
  exact H2 (g (f alpha)) H7.
- assume H7: g (f alpha) = alpha. exact H7.
- assume H7: alpha :e g (f alpha).
  apply H6 alpha H7. reflexivity.
Qed.

Theorem ordinals_into_set_set_into_ordinals_prop2: forall X, forall x :e X,
    (exists alpha, ordinal alpha /\ ordinals_into_set X alpha = x)
 /\ (forall beta :e set_into_ordinals X x, ordinals_into_set X beta < x).
let X. apply dneg.
set Phi : set -> (set -> set) -> set := fun alpha f => some x, x :e X /\ (forall beta :e alpha, f beta < x) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y).
set f : set -> set := ordinals_into_set X.
set g : set -> set := fun x => some alpha, ordinal alpha /\ f alpha = x /\ forall beta :e alpha, f beta <> x.
set p : set -> prop := fun x =>
           x :e X
	/\ ~((exists alpha, ordinal alpha /\ f alpha = x)
          /\ (forall beta :e g x, f beta < x)).
assume HC: ~(forall x :e X,
             (exists alpha, ordinal alpha /\ f alpha = x)
          /\ (forall beta :e g x, f beta < x)).
claim L1: exists x, p x.
{ apply dneg.
  assume HC': ~exists x, p x.
  apply HC.
  let x. assume Hx. apply dneg.
  assume HC''.
  apply HC'.
  witness x.
  prove x :e X
     /\ ~((exists alpha, ordinal alpha /\ f alpha = x)
       /\ (forall beta :e g x, f beta < x)).
  apply andI.
  - exact Hx.
  - exact HC''.
}
apply lt_wo p L1.
let x. assume H. apply H. assume H1. apply H1.
assume Hx1: x :e X.
assume Hx2: ~((exists alpha, ordinal alpha /\ f alpha = x)
          /\ (forall beta :e g x, f beta < x)).
assume Hx3: forall y, p y /\ y <> x -> x < y.
apply lt_stricttotalorder.
assume H_lt_strictpartialorder H_lt_trich.
apply H_lt_strictpartialorder.
assume H_lt_irref H_lt_trans.
claim LIH: forall y, y :e X -> y < x ->
      (exists alpha, ordinal alpha /\ f alpha = y)
   /\ (forall beta :e g y, f beta < y).
{ let y. assume HyX Hyx.
  apply dneg.
  assume HC': ~((exists alpha, ordinal alpha /\ f alpha = y)
             /\ (forall beta :e g y, f beta < y)).
  claim LC': p y.
  { prove y :e X
       /\ ~((exists alpha, ordinal alpha /\ f alpha = y)
         /\ (forall beta :e g y, f beta < y)).
    apply andI.
    - exact HyX.
    - exact HC'.
  }
  claim Lynx: y <> x.
  { assume H1: y = x. apply H_lt_irref y.
    prove y < y.
    rewrite H1 at 2.
    exact Hyx.
  }
  apply H_lt_irref y.
  prove y < y.
  apply H_lt_trans y x y Hyx.
  prove x < y.
  apply Hx3 y.
  apply andI.
  - exact LC'.
  - exact Lynx.
}
claim LIH1: forall y, y :e X -> y < x ->
       exists alpha, ordinal alpha /\ f alpha = y.
{ let y. assume HyX Hyx.
  apply LIH y HyX Hyx.
  assume H _. exact H.
}
claim LIH2: forall y, y :e X -> y < x ->
       forall beta :e g y, f beta < y.
{ let y. assume HyX Hyx.
  apply LIH y HyX Hyx.
  assume _ H. exact H.
}
set alpha := {g y|y :e X, y < x}.
claim L1: forall y :e X, y < x ->
                ordinal (g y)
             /\ f (g y) = y
	     /\ forall beta :e g y, f beta <> y.
{ let y. assume HyX Hyx.
  exact set_into_ordinals_prop X y HyX (LIH1 y HyX Hyx).
}
claim L2: ordinal alpha.
{ prove TransSet alpha /\ forall beta :e alpha, TransSet beta.
  apply andI.
  - let beta. assume Hb: beta :e alpha.
    let gamma. assume Hc: gamma :e beta.
    apply ReplSepE_impred X (fun y => y < x) g beta Hb.
    let y. assume HyX: y :e X. assume Hyx: y < x.
    assume Hbetagy: beta = g y.
    prove gamma :e alpha.
    apply L1 y HyX Hyx.
    prove ordinal (g y) /\ f (g y) = y
       -> (forall delta :e g y, f delta <> y)
       -> gamma :e alpha.
    rewrite <- Hbetagy.
    assume H. apply H.
    assume Hbetaord: ordinal beta.
    assume Hfbetay: f beta = y.
    assume Hfbetaleast: forall delta :e beta, f delta <> y.
    claim Lgammagy: gamma :e g y.
    { rewrite <- Hbetagy. exact Hc. }
    claim Lfgammay: f gamma < y.
    { exact LIH2 y HyX Hyx gamma Lgammagy. }
    claim Lgammaord: ordinal gamma.
    { exact ordinal_Hered beta Hbetaord gamma Hc. }
    claim Lgammaub: exists z :e X, forall delta :e gamma, f delta < z.
    { witness y. apply andI.
      - exact HyX.
      - let delta. assume Hd: delta :e gamma.
        prove f delta < y.
	apply LIH2 y HyX Hyx delta.
	prove delta :e g y.
	rewrite <- Hbetagy.
	apply Hbetaord.
	assume Hbetatrans _.
	exact Hbetatrans gamma Hc delta Hd.
    }
    apply ordinals_into_set_props X gamma Lgammaord Lgammaub.
    assume H. apply H.
    assume HfgammaX: f gamma :e X.
    assume Hfgammaub: forall delta :e gamma, f delta < f gamma.
    assume Hfgammalub: forall z :e X, (forall delta :e gamma, f delta < z) -> f gamma < z \/ f gamma = z.
    claim Lgfgamma: g (f gamma) = gamma.
    { apply set_into_ordinals_ordinals_into_set_prop1 X gamma.
      - prove ordinal gamma. exact Lgammaord.
      - prove f gamma :e X.
        exact HfgammaX.
      - prove forall delta :e gamma, f delta < f gamma.
        exact Hfgammaub.
      - prove forall z :e X, (forall delta :e gamma, f delta < z) -> f gamma < z \/ f gamma = z.
        exact Hfgammalub.
    }
    prove gamma :e alpha.
    rewrite <- Lgfgamma.
    prove g (f gamma) :e alpha.
    claim Lfgammax: f gamma < x.
    { exact H_lt_trans (f gamma) y x Lfgammay Hyx. }
    exact ReplSepI X (fun y => y < x) g (f gamma) HfgammaX Lfgammax.
  - let beta. assume Hb: beta :e alpha.
    apply ReplSepE_impred X (fun y => y < x) g beta Hb.
    let y. assume HyX: y :e X. assume Hyx: y < x.
    assume Hbetagy: beta = g y.
    rewrite Hbetagy.
    prove TransSet (g y).
    apply L1 y HyX Hyx.
    assume H _. apply H.
    assume H1: ordinal (g y).
    assume _.
    apply H1.
    assume H2: TransSet (g y).
    assume _.
    exact H2.
}
claim L3: f alpha = x.
{ apply ordinals_into_set_uniq X alpha L2 x Hx1.
  - prove forall beta :e alpha, f beta < x.
    let beta. assume Hb: beta :e alpha.
    apply ReplSepE_impred X (fun y => y < x) g beta Hb.
    let y. assume HyX: y :e X. assume Hyx: y < x.
    assume Hbetagy: beta = g y.
    apply L1 y HyX Hyx.
    prove ordinal (g y) /\ f (g y) = y
       -> (forall delta :e g y, f delta <> y)
       -> f beta < x.
    rewrite <- Hbetagy.
    assume H. apply H.
    assume Hbetaord: ordinal beta.
    assume Hfbetay: f beta = y.
    assume Hfbetaleast: forall delta :e beta, f delta <> y.
    prove f beta < x.
    rewrite Hfbetay. exact Hyx.
  - prove forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y.
    let y. assume HyX.
    assume Hy2: forall beta :e alpha, f beta < y.
    prove x < y \/ x = y.
    apply H_lt_trich x y.
    - assume H. exact H.
    - assume Hyx: y < x. prove False.
      claim Lgyalpha: g y :e alpha.
      { exact ReplSepI X (fun y => y < x) g y HyX Hyx. }
      apply L1 y HyX Hyx. assume H. apply H.
      assume Hgyord: ordinal (g y).
      assume Hfgy: f (g y) = y.
      assume Hfgyleast: forall delta :e g y, f delta <> y.
      apply H_lt_irref y.
      prove y < y.
      rewrite <- Hfgy at 1.
      exact Hy2 (g y) Lgyalpha.
}
claim L4: exists alpha, ordinal alpha /\ f alpha = x.
{ witness alpha. apply andI.
  + exact L2.
  + exact L3.
}
apply Hx2. apply andI.
- prove exists alpha, ordinal alpha /\ f alpha = x.
  exact L4.
- prove forall beta :e g x, f beta < x.
  apply set_into_ordinals_prop X x Hx1 L4.
  assume H. apply H.
  assume Hgxord: ordinal (g x).
  assume Hfgx: f (g x) = x.
  assume Hgxleast: forall beta :e g x, f beta <> x.
  claim Lgxalpha: g x = alpha.
  { apply ordinal_trichotomy_or_impred (g x) alpha Hgxord L2.
    - assume H1: g x :e alpha. prove False.
      apply ReplSepE_impred X (fun y => y < x) g (g x) H1.
      let y. assume HyX: y :e X. assume Hyx: y < x.
      assume Hgxgy: g x = g y.
      apply L1 y HyX Hyx. assume H. apply H.
      assume Hgyord: ordinal (g y).
      assume Hfgy: f (g y) = y.
      assume Hfgyleast: forall delta :e g y, f delta <> y.
      claim Lxy: x = y.
      { rewrite <- Hfgx. rewrite <- Hfgy.
        prove f (g x) = f (g y).
	f_equal.
	exact Hgxgy.
      }
      apply H_lt_irref x.
      prove x < x.
      rewrite Lxy at 1.
      exact Hyx.
    - assume H1: g x = alpha. exact H1.
    - assume H1: alpha :e g x. prove False.
      apply Hgxleast alpha H1.
      prove f alpha = x.
      exact L3.
  }
  rewrite Lgxalpha.
  let beta. assume Hb: beta :e alpha.
  prove f beta < x.
  apply ReplSepE_impred X (fun y => y < x) g beta Hb.
  let y. assume HyX: y :e X. assume Hyx: y < x.
  assume Hbetagy: beta = g y.
  apply L1 y HyX Hyx. assume H. apply H.
  assume Hgyord: ordinal (g y).
  assume Hfgy: f (g y) = y.
  assume Hfgyleast: forall delta :e g y, f delta <> y.
  prove f beta < x.
  rewrite Hbetagy.
  prove f (g y) < x.
  rewrite Hfgy.
  prove y < x.
  exact Hyx.
Qed.

Theorem set_equip_ord: forall X, exists alpha, ordinal alpha /\ equip alpha X.
let X.
set Phi : set -> (set -> set) -> set := fun alpha f => some x, x :e X /\ (forall beta :e alpha, f beta < x) /\ (forall y :e X, (forall beta :e alpha, f beta < y) -> x < y \/ x = y).
set f : set -> set := ordinals_into_set X.
set f' : set -> set := fun alpha => Phi alpha f.
set g : set -> set := fun x => some alpha, ordinal alpha /\ f alpha = x /\ forall beta :e alpha, f beta <> x.
set alpha := {g x|x :e X}.
apply lt_stricttotalorder.
assume H_lt_strictpartialorder H_lt_trich.
apply H_lt_strictpartialorder.
assume H_lt_irref H_lt_trans.
claim L1: forall x :e X,
                ordinal (g x)
             /\ f (g x) = x
	     /\ forall beta :e g x, f beta <> x.
{ let x. assume Hx.
  apply ordinals_into_set_set_into_ordinals_prop2 X x Hx.
  assume H1: exists alpha, ordinal alpha /\ f alpha = x.
  assume H2: forall beta :e g x, f beta < x.
  exact set_into_ordinals_prop X x Hx H1.
}
claim L2: ordinal alpha.
{ prove TransSet alpha /\ forall beta :e alpha, TransSet beta.
  apply andI.
  - let beta. assume Hb: beta :e alpha.
    let gamma. assume Hc: gamma :e beta.
    apply ReplE_impred X g beta Hb.
    let x. assume Hx: x :e X.
    assume Hbetagx: beta = g x.
    prove gamma :e alpha.
    apply ordinals_into_set_set_into_ordinals_prop2 X x Hx.
    assume H1: exists delta, ordinal delta /\ f delta = x.
    rewrite <- Hbetagx.
    assume H2: forall delta :e beta, f delta < x.
    apply L1 x Hx.
    prove ordinal (g x) /\ f (g x) = x
       -> (forall delta :e g x, f delta <> x)
       -> gamma :e alpha.
    rewrite <- Hbetagx.
    assume H. apply H.
    assume Hbetaord: ordinal beta.
    assume Hfbetax: f beta = x.
    assume Hfbetaleast: forall delta :e beta, f delta <> x.
    apply Hbetaord.
    assume Hbetatra: TransSet beta.
    assume _.
    claim Lgammagx: gamma :e g x.
    { rewrite <- Hbetagx. exact Hc. }
    claim Lfgammax: f gamma < x.
    { exact H2 gamma Hc. }
    claim Lgammaord: ordinal gamma.
    { exact ordinal_Hered beta Hbetaord gamma Hc. }
    claim Lgammaub: exists z :e X, forall delta :e gamma, f delta < z.
    { witness x. apply andI.
      - exact Hx.
      - let delta. assume Hd: delta :e gamma.
        prove f delta < x.
	apply H2 delta.
	prove delta :e beta.
	exact Hbetatra gamma Hc delta Hd.
    }
    apply ordinals_into_set_props X gamma Lgammaord Lgammaub.
    assume H. apply H.
    assume HfgammaX: f gamma :e X.
    assume Hfgammaub: forall delta :e gamma, f delta < f gamma.
    assume Hfgammalub: forall z :e X, (forall delta :e gamma, f delta < z) -> f gamma < z \/ f gamma = z.
    claim Lgfgamma: g (f gamma) = gamma.
    { apply set_into_ordinals_ordinals_into_set_prop1 X gamma.
      - prove ordinal gamma. exact Lgammaord.
      - prove f gamma :e X.
        exact HfgammaX.
      - prove forall delta :e gamma, f delta < f gamma.
        exact Hfgammaub.
      - prove forall z :e X, (forall delta :e gamma, f delta < z) -> f gamma < z \/ f gamma = z.
        exact Hfgammalub.
    }
    prove gamma :e alpha.
    rewrite <- Lgfgamma.
    prove g (f gamma) :e alpha.
    exact ReplI X g (f gamma) HfgammaX.
  - let beta. assume Hb: beta :e alpha.
    apply ReplE_impred X g beta Hb.
    let x. assume Hx: x :e X.
    assume Hbetagx: beta = g x.
    rewrite Hbetagx.
    prove TransSet (g x).
    apply L1 x Hx.
    assume H _. apply H.
    assume H1: ordinal (g x).
    assume _.
    apply H1.
    assume H2: TransSet (g x).
    assume _.
    exact H2.
}
witness alpha. apply andI.
- exact L2.
- prove equip alpha X.
  prove exists f:set -> set, bij alpha X f.
  witness f.
  prove bij alpha X f.
  apply bijI alpha X f.
  + prove forall beta :e alpha, f beta :e X.
    let beta. assume Hb: beta :e alpha.
    apply ReplE_impred X g beta Hb.
    let x. assume Hx: x :e X.
    assume Hbetagx: beta = g x.
    rewrite Hbetagx.
    prove f (g x) :e X.
    apply L1 x Hx. assume H _. apply H.
    assume _.
    assume Hfgx: f (g x) = x.
    rewrite Hfgx.
    exact Hx.
  + prove forall beta gamma :e alpha, f beta = f gamma -> beta = gamma.
    let beta. assume Hb: beta :e alpha.
    let gamma. assume Hc: gamma :e alpha.
    apply ReplE_impred X g beta Hb.
    let x. assume Hx: x :e X.
    assume Hbetagx: beta = g x.
    apply ReplE_impred X g gamma Hc.
    let y. assume Hy: y :e X.
    assume Hgammagy: gamma = g y.
    rewrite Hbetagx.
    rewrite Hgammagy.
    prove f (g x) = f (g y) -> g x = g y.
    apply L1 x Hx. assume H _. apply H.
    assume _.
    assume Hfgx: f (g x) = x.
    rewrite Hfgx.
    apply L1 y Hy. assume H _. apply H.
    assume _.
    assume Hfgy: f (g y) = y.
    rewrite Hfgy.
    assume Hxy: x = y.
    prove g x = g y.
    f_equal.
    exact Hxy.
  + prove forall x :e X, exists beta :e alpha, f beta = x.
    let x. assume Hx: x :e X.
    apply L1 x Hx. assume H _. apply H.
    assume H1: ordinal (g x).
    assume H2: f (g x) = x.
    witness (g x). apply andI.
    * prove g x :e alpha.
      exact ReplI X g x Hx.
    * exact H2.
Qed.

End Zermelo1908.

(** Cardinality **)
Section Cardinality.

Binder some , := Eps_i.

Definition card : set -> set := fun X =>
  some alpha, ordinal alpha /\ equip alpha X
      /\ forall beta, ordinal beta /\ equip beta X -> alpha c= beta.

Definition cardinal : set -> prop := fun alpha =>
    ordinal alpha
 /\ forall beta :e alpha, ~atleastp alpha beta.

Theorem card_ex: forall X,
  exists alpha, ordinal alpha /\ equip alpha X
      /\ forall beta, ordinal beta /\ equip beta X -> alpha c= beta.
let X.
claim L1: exists alpha, ordinal alpha /\ equip alpha X.
{ exact set_equip_ord X. }
apply least_ordinal_ex (fun alpha => equip alpha X) L1.
let alpha. assume H. apply H. assume H. apply H.
assume H1: ordinal alpha.
assume H2: equip alpha X.
assume H3: forall beta :e alpha, ~equip beta X.
witness alpha. apply and3I.
- exact H1.
- exact H2.
- let beta. assume H. apply H.
  assume H4: ordinal beta.
  assume H5: equip beta X.
  prove alpha c= beta.
  apply ordinal_In_Or_Subq beta alpha H4 H1.
  + assume H6: beta :e alpha. prove False.
    apply H3 beta H6.
    prove equip beta X.
    exact H5.
  + assume H6: alpha c= beta. exact H6.
Qed.

Theorem card_prop: forall X,
    ordinal (card X) /\ equip (card X) X
 /\ forall beta, ordinal beta /\ equip beta X -> card X c= beta.
let X.
exact Eps_i_ex
        (fun alpha => ordinal alpha /\ equip alpha X
          /\ forall beta, ordinal beta /\ equip beta X -> alpha c= beta)
	(card_ex X).
Qed.

Theorem card_cardinal: forall X, cardinal (card X).
let X.
apply card_prop X. assume H. apply H.
assume H1: ordinal (card X).
assume H2: equip (card X) X.
assume H3: forall beta, ordinal beta /\ equip beta X -> card X c= beta.
prove ordinal (card X) /\ forall beta :e card X, ~atleastp (card X) beta.
apply andI.
- exact H1.
- let beta. assume Hb: beta :e card X.
  assume H4: atleastp (card X) beta.
  prove False.
  claim L1: ordinal beta /\ equip beta X.
  { apply andI.
    - exact ordinal_Hered (card X) H1 beta Hb.
    - prove equip beta X.
      apply equip_tra beta (card X) X.
      + prove equip beta (card X).
        apply atleastp_antisym_equip.
	* prove atleastp beta (card X).
	  apply Subq_atleastp.
	  prove beta c= card X.
	  apply H1.
	  assume H5: TransSet (card X).
	  assume _.
	  exact H5 beta Hb.
        * exact H4.
      + prove equip (card X) X.
        exact H2.
  }
  apply In_irref beta.
  prove beta :e beta.
  exact H3 beta L1 beta Hb.
Qed.

End Cardinality.
