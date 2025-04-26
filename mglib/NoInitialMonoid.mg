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

Parameter In:set->set->prop.

(* Unicode exists "2203" *)
Binder+ exists , := ex; and.

Parameter Empty : set.

(* Parameter ordsucc "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "65d8837d7b0172ae830bed36c8407fcd41b7d875033d2284eb2df245b42295a6" *)
Parameter ordsucc : set->set.

Notation Nat Empty ordsucc.

Axiom neq_0_1 : 0 <> 1.
Axiom In_0_2 : 0 :e 2.
Axiom In_1_2 : 1 :e 2.

(* Parameter nat_p "25c483dc8509e17d4b6cf67c5b94c2b3f3902a45c3c34582da3e29ab1dc633ab" "458be3a74fef41541068991d6ed4034dc3b5e637179369954ba21f6dff4448e4" *)
Parameter nat_p : set->prop.

Axiom nat_2 : nat_p 2.
Axiom nat_p_trans : forall n, nat_p n -> forall m :e n, nat_p m.

Axiom cases_2: forall i :e 2, forall p:set->prop, p 0 -> p 1 -> p i.

(* Parameter omega "39cdf86d83c7136517f803d29d0c748ea45a274ccbf9b8488f9cda3e21f4b47c" "6fc30ac8f2153537e397b9ff2d9c981f80c151a73f96cf9d56ae2ee27dfd1eb2" *)
Parameter omega:set.

Axiom nat_p_omega : forall n:set, nat_p n -> n :e omega.

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

(* Parameter Pi "8ab5fa18b3cb4b4b313a431cc37bdd987f036cc47f175379215f69af5977eb3b" "40f1c38f975e69e2ae664b3395551df5820b0ba6a93a228eba771fc2a4551293" *)
Parameter Pi : set -> (set -> set) -> set.

(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

Axiom lam_Pi : forall X:set, forall Y:set -> set, forall F:set -> set,
 (forall x :e X, F x :e Y x) -> (fun x :e X => F x) :e (Pi_ x :e X, Y x).
Definition setexp : set->set->set := fun Y X:set => Pi_ x :e X, Y.

(* Superscript :^: *)
Infix :^: 430 left := setexp.

Definition HomSet : set -> set -> set -> prop := fun X Y f => f :e Y :^: X.

(* Parameter SNo "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" "11faa7a742daf8e4f9aaf08e90b175467e22d0e6ad3ed089af1be90cfc17314b" *)
Parameter SNo : set -> prop.

(* Parameter mul_SNo "f56bf39b8eea93d7f63da529dedb477ae1ab1255c645c47d8915623f364f2d6b" "48d05483e628cb37379dd5d279684d471d85c642fe63533c3ad520b84b18df9d" *)
Parameter mul_SNo : set -> set -> set.

Infix * 355 right := mul_SNo.

Axiom omega_SNo: forall n :e omega, SNo n.

Axiom SNo_0 : SNo 0.
Axiom SNo_1 : SNo 1.

Axiom mul_SNo_zeroL : forall x, SNo x -> 0 * x = 0.
Axiom mul_SNo_oneL : forall x, SNo x -> 1 * x = x.
Axiom mul_SNo_oneR : forall x, SNo x -> x * 1 = x.

Axiom mul_SNo_assoc : forall x y z, SNo x -> SNo y -> SNo z -> x * (y * z) = (x * y) * z.

Section Initial.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Definition initial_p: set -> (set -> set) -> prop
 := fun Y h => Obj Y
     /\ forall X:set, Obj X
         -> Hom Y X (h X)
         /\ forall h':set, Hom Y X h' -> h' = h X.

End Initial.

(* Parameter pack_b "e007d96601771e291e9083ce21b5e97703bce4ff5257fec59b7ed3dbb05b5319" "855387af88aad68b5f942a3a97029fcd79fe0a4e781cdf546d058297f8a483ce" *)
Parameter pack_b : set -> (set -> set -> set) -> set.

Definition struct_b : set -> prop := fun S => forall q:set -> prop, (forall X:set, forall F:set -> set -> set, (forall x y :e X, F x y :e X) -> q (pack_b X F)) -> q S.

Axiom pack_struct_b_I: forall X, forall F:set -> set -> set, (forall x y :e X, F x y :e X) -> struct_b (pack_b X F).

(* Parameter unpack_b_o "0fa2c67750f22ef718feacbb3375b43caa7129d02200572180f9cfe7abf54cec" "0601c1c35ff2c84ae36acdecfae98d553546d98a227f007481baf6b962cc1dc8" *)
Parameter unpack_b_o : set -> (set -> (set -> set -> set) -> prop) -> prop.

Axiom unpack_b_o_eq : forall Phi:set -> (set -> set -> set) -> prop,
  forall X, forall F:set -> set -> set,
  (forall F':set -> set -> set, (forall x y :e X, F x y = F' x y) -> Phi X F' = Phi X F)
  ->
  unpack_b_o (pack_b X F) Phi = Phi X F.

(* Parameter Hom_struct_b "a84fd92c3d7f64da963df3dac4615300170cb17ff896ccef2f8dd00066ec3d02" "e815783558526a66c8f279c485040d57663745bc5f9348b1ebc671af74c2a305" *)
Parameter Hom_struct_b : set -> set -> set -> prop.

Axiom Hom_struct_b_pack :
 forall X Y, forall opX opY:set -> set -> set,
 forall f,
    (Hom_struct_b (pack_b X opX) (pack_b Y opY) f)
  = (f :e Y :^: X /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))).

Definition struct_b_monoid : set -> prop
 := fun X => struct_b X
     /\ unpack_b_o X
          (fun X' op => 
                (forall x y z :e X', op (op x y) z = op x (op y z)) 
	     /\ (exists e :e X', forall x :e X', op x e = x /\ op e x = x)).

(* Parameter MetaAdjunction_strict "be3dc11d683b255bfbd9127adb3c6087d074a17cb0e31c91d602b5ae49893e97" "c8ed7d3ad63a4a29ebc88ac0ccb02bfd5f4c0141eebc8a7a349ed7115a3a3eb9" *)
(* Parameter MetaCat "9b2dee6442140d530f300f187f315d389cfa416a087e15c1677d3bf02f85f063" "fd9743c836fc84a35eca7120bf513d8be118e8eff433fbcc8ca5369662cda164" *)
Parameter MetaCat : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> prop.

Axiom MetaCatSet_initial : exists Y:set, exists uniqa:set -> set,
  initial_p (fun _ => True) HomSet (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) Y uniqa.

Parameter MetaAdjunction_strict : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> (set -> set) -> (set -> set) -> prop.

Axiom LeftAdjointsPreserveInitial:
  forall Obj : set -> prop,
  forall x1 : set -> set -> set -> prop,
  forall Id : set -> set,
  forall Comp : set -> set -> set -> set -> set -> set,
  forall Obj' : set -> prop,
  forall Hom' : set -> set -> set -> prop,
  forall Id' : set -> set,
  forall Comp' : set -> set -> set -> set -> set -> set,
  forall F0 : set -> set,
  forall F1 : set -> set -> set -> set,
  forall G0 : set -> set,
  forall G1 : set -> set -> set -> set,
  forall eta eps : set -> set,
      MetaAdjunction_strict Obj x1 Id Comp Obj' Hom' Id' Comp' F0 F1 G0 G1 eta eps
   -> forall Init, forall uniq : set -> set,
        initial_p Obj x1 Id Comp Init uniq
     -> exists uniq' : set -> set,
         initial_p Obj' Hom' Id' Comp' (F0 Init) uniq'.

Axiom struct_b_monoid_Phi: forall X, forall F:set -> set -> set, (forall x y :e X, F x y :e X) ->
  forall F':set -> set -> set, (forall x y :e X, F x y = F' x y) ->
      ((forall x y z :e X, F' (F' x y) z = F' x (F' y z)) 
    /\ (exists e :e X, forall x :e X, F' x e = x /\ F' e x = x))
    = ((forall x y z :e X, F (F x y) z = F x (F y z)) 
    /\ (exists e :e X, forall x :e X, F x e = x /\ F e x = x)).

(** Bounty 25 **)
Proposition MetaCat_struct_b_monoid_initial_neg:
 ~exists Y:set, exists uniqa:set -> set,
  initial_p struct_b_monoid Hom_struct_b struct_id struct_comp Y uniqa.
set Obj := struct_b_monoid.
set Hom := Hom_struct_b.
set id := struct_id.
set comp := struct_comp.
set Phi : set -> (set -> set -> set) -> prop
    := fun X' op => 
                (forall x y z :e X', op (op x y) z = op x (op y z)) 
	     /\ (exists e :e X', forall x :e X', op x e = x /\ op e x = x).
claim LPhi1: forall X, forall F:set -> set -> set, (forall x y :e X, F x y :e X) ->
  forall F':set -> set -> set, (forall x y :e X, F x y = F' x y) -> Phi X F' = Phi X F.
{ exact struct_b_monoid_Phi. }
assume H. apply H.
let Y. assume H. apply H.
let uniqa.
assume H1: initial_p struct_b_monoid Hom_struct_b struct_id struct_comp Y uniqa.
apply H1.
assume HY: Obj Y.
apply HY.
assume HYs.
apply HYs.
let V q. assume Hq.
rewrite unpack_b_o_eq Phi V q (LPhi1 V q Hq).
assume HVq: Phi V q.
assume H2: forall X:set, Obj X
            -> Hom (pack_b V q) X (uniqa X)
            /\ forall h':set, Hom (pack_b V q) X h' -> h' = uniqa X.
set M2 := pack_b 2 mul_SNo.
claim L2SNo: forall x :e 2, SNo x.
{ let x. assume Hx. exact omega_SNo x (nat_p_omega x (nat_p_trans 2 nat_2 x Hx)). }
claim L1: Obj M2.
{ prove struct_b M2 /\ unpack_b_o M2 Phi.
  claim L1a: forall x y :e 2, x * y :e 2.
  { let x. assume Hx. let y. assume Hy.
    claim Ly: SNo y.
    { exact L2SNo y Hy. }
    apply cases_2 x Hx.
    - prove 0 * y :e 2.
      rewrite mul_SNo_zeroL y Ly.
      exact In_0_2.
    - prove 1 * y :e 2.
      rewrite mul_SNo_oneL y Ly.
      exact Hy.
  }
  apply andI.
  - apply pack_struct_b_I. exact L1a.
  - rewrite unpack_b_o_eq Phi 2 mul_SNo (LPhi1 2 mul_SNo L1a).
    apply andI.
    + let x. assume Hx. let y. assume Hy. let z. assume Hz.
      prove (x * y) * z = x * (y * z).
      symmetry.
      exact mul_SNo_assoc x y z (L2SNo x Hx) (L2SNo y Hy) (L2SNo z Hz).
    + witness 1. apply andI.
      * exact In_1_2.
      * { let x. assume Hx.
          claim Lx: SNo x.
	  { exact L2SNo x Hx. }
          apply andI.
          - prove x * 1 = x.
	    exact mul_SNo_oneR x Lx.
	  - prove 1 * x = x.
	    exact mul_SNo_oneL x Lx.
	}
}
apply H2 M2 L1.
rewrite Hom_struct_b_pack. assume H. apply H.
assume H3: uniqa M2 :e 2 :^: V.
assume H4: forall x y :e V, uniqa M2 (q x y) = uniqa M2 x * uniqa M2 y.
assume H4: forall h':set, Hom (pack_b V q) M2 h' -> h' = uniqa M2.
set f := fun x :e V => 0.
set g := fun x :e V => 1.
claim L2: Hom (pack_b V q) M2 f.
{ rewrite Hom_struct_b_pack.
  apply andI.
  - prove f :e 2 :^: V.
    prove (fun x :e V => 0) :e Pi_ x :e V, 2.
    apply lam_Pi.
    let x. assume Hx.
    exact In_0_2.
  - prove forall x y :e V, f (q x y) = f x * f y.
    let x. assume Hx. let y. assume Hy.
    rewrite beta V (fun _ => 0) (q x y) (Hq x Hx y Hy).
    rewrite beta V (fun _ => 0) x Hx.
    rewrite beta V (fun _ => 0) y Hy.
    prove 0 = 0 * 0.
    symmetry.
    exact mul_SNo_zeroL 0 SNo_0.
}
claim L3: Hom (pack_b V q) M2 g.
{ rewrite Hom_struct_b_pack.
  apply andI.
  - prove g :e 2 :^: V.
    prove (fun x :e V => 1) :e Pi_ x :e V, 2.
    apply lam_Pi.
    let x. assume Hx.
    exact In_1_2.
  - prove forall x y :e V, g (q x y) = g x * g y.
    let x. assume Hx. let y. assume Hy.
    rewrite beta V (fun _ => 1) (q x y) (Hq x Hx y Hy).
    rewrite beta V (fun _ => 1) x Hx.
    rewrite beta V (fun _ => 1) y Hy.
    prove 1 = 1 * 1.
    symmetry.
    exact mul_SNo_oneL 1 SNo_1.
}
prove False.
apply HVq.
assume HA: forall x y z :e V, q (q x y) z = q x (q y z).
assume H. apply H.
let e. assume H. apply H.
assume He: e :e V.
assume _.
apply neq_0_1.
prove 0 = 1.
transitivity f e, uniqa M2 e, g e.
- prove 0 = f e.
  symmetry.
  exact beta V (fun _ => 0) e He.
- prove f e = uniqa M2 e.
  f_equal.
  exact H4 f L2.
- prove uniqa M2 e = g e.
  f_equal.
  symmetry.
  exact H4 g L3.
- prove g e = 1.
  exact beta V (fun _ => 1) e He.
Qed.

(** Bounty 750 **)
Proposition MetaCat_struct_b_monoid_left_adjoint_forgetful_neg:
 ~exists F0:set -> set,
  exists F1:set -> set -> set -> set,
  exists eta eps:set -> set,
  MetaAdjunction_strict
       (fun _ => True) HomSet
       (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
       struct_b_monoid Hom_struct_b struct_id struct_comp
       F0 F1 (fun X => X 0) (fun X Y f => f) eta eps.
assume H. apply H.
let F0. assume H. apply H.
let F1. assume H. apply H.
let eta. assume H. apply H.
let eps.
assume H1: MetaAdjunction_strict
             (fun _ => True) HomSet
             (fun X => (lam_id X)) (fun X Y Z f g => (lam_comp X f g))
             struct_b_monoid Hom_struct_b struct_id struct_comp
             F0 F1 (fun X => X 0) (fun X Y f => f) eta eps.
apply MetaCatSet_initial.
let Init. assume H. apply H.
let uniq.
assume H2: initial_p (fun _ => True) HomSet (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) Init uniq.
apply MetaCat_struct_b_monoid_initial_neg.
witness F0 Init.
exact LeftAdjointsPreserveInitial
        (fun _ => True) HomSet (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x)))
        struct_b_monoid Hom_struct_b struct_id struct_comp
	F0 F1 (fun X => X 0) (fun X Y f => f) eta eps H1
	Init uniq H2.
Qed.
