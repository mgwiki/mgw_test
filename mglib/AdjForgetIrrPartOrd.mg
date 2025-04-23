Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.

Definition not : prop -> prop := fun A:prop => A -> False.

(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.

Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.

(* Unicode /\ "2227" *)
Infix /\ 780 left := and.

Axiom andI: forall A B : prop, A -> B -> A /\ B.

Definition iff : prop -> prop -> prop := fun A B:prop => (A -> B) /\ (B -> A).

(* Unicode <-> "2194" *)
Infix <-> 805 := iff.

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

Parameter In:set->set->prop.
Parameter Empty : set.

(* Parameter lam "93592da87a6f2da9f7eb0fbd449e0dc4730682572e0685b6a799ae16c236dcae" "8acbb2b5de4ab265344d713b111d82b0048c8a4bf732a67ad35f1054a4eb4642" *)
Parameter lam : set -> (set -> set) -> set.

Definition lam_id : set -> set := fun X => lam X (fun x => x).

(* Parameter ap "58c1782da006f2fb2849c53d5d8425049fad551eb4f8025055d260f0c9e1fe40" "c7aaa670ef9b6f678b8cf10b13b2571e4dc1e6fde061d1f641a5fa6c30c09d46" *)
Parameter ap : set -> set -> set.
Notation SetImplicitOp ap.

Definition lam_comp : set -> set -> set -> set :=
 fun X g f => lam X (fun x : set => g (f x)).

(* Parameter Pi "8ab5fa18b3cb4b4b313a431cc37bdd987f036cc47f175379215f69af5977eb3b" "40f1c38f975e69e2ae664b3395551df5820b0ba6a93a228eba771fc2a4551293" *)
Parameter Pi : set -> (set -> set) -> set.

(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

Definition setexp : set->set->set := fun Y X:set => Pi_ x :e X, Y.

(* Superscript :^: *)
Infix :^: 430 left := setexp.

Definition HomSet : set -> set -> set -> prop := fun X Y f => f :e Y :^: X.

Axiom lam_id_exp_In : forall X, lam_id X :e X :^: X.
Axiom lam_comp_id_R : forall X Y f, f :e Y :^: X -> lam_comp X f (lam_id X) = f.
Axiom lam_comp_id_L : forall X Y f, f :e Y :^: X -> lam_comp X (lam_id Y) f = f.

(* Parameter ordsucc "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "65d8837d7b0172ae830bed36c8407fcd41b7d875033d2284eb2df245b42295a6" *)
Parameter ordsucc : set -> set.
Notation Nat Empty ordsucc.

Definition struct_id : set -> set := fun A : set => lam_id (A 0).

Definition struct_comp : set -> set -> set -> set -> set -> set :=
 fun A B C : set => lam_comp (A 0).

(* Parameter pack_r "39d80099e1b48aed4548f424ae4f1ff25b2d595828aff4b3a5abe232ca0348b5" "217a7f92acc207b15961c90039aa929f0bd5d9212f66ce5595c3af1dd8b9737e" *)
Parameter pack_r : set -> (set -> set -> prop) -> set.

Definition struct_r : set -> prop :=
 fun S => forall q:set -> prop,
                 (forall X:set, forall R:set -> set -> prop, q (pack_r X R))
              -> q S.

Axiom pack_r_0_eq2 : forall X, forall R : set -> set -> prop, X = pack_r X R 0.

(* Parameter BinRelnHom "352304ebb6c77dbc4e2a952e767857a98538e43de1c35fb4bcd6c99fca02ae7e" "acf0f04c6a55a143e3ed8404c0fa6b09b323d938c83532f081b47091e31c4eb3" *)
Parameter BinRelnHom : set -> set -> set -> prop.

Axiom BinRelnHom_eq : forall X Y, forall R Q : set -> set -> prop, forall h,
  BinRelnHom (pack_r X R) (pack_r Y Q) h = (h :e Y :^: X /\ forall x y :e X, R x y -> Q (h x) (h y)).

(* Parameter IrrPartOrd "71ade8643726a6e7f38cc8ef90bf356e854b17e60a87a5799b556e53a948c155" "64673bc8a8882720c2818d2bf776ca95f2a94e00547422df4e502e2c1ea48675" *)
Parameter IrrPartOrd : set -> prop.

Axiom IrrPartOrd_I : forall X, forall R : set -> set -> prop,
     (forall x :e X, ~R x x)
  -> (forall x y z :e X, R x y -> R y z -> R x z)
  -> IrrPartOrd (pack_r X R).

Axiom IrrPartOrd_E :
  forall A, IrrPartOrd A ->
  forall q : set -> prop,
      (forall X, forall R : set -> set -> prop,
           (forall x :e X, ~R x x)
        -> (forall x y z :e X, R x y -> R y z -> R x z)
        -> q (pack_r X R))
   -> q A.

(* Parameter MetaCat "9b2dee6442140d530f300f187f315d389cfa416a087e15c1677d3bf02f85f063" "fd9743c836fc84a35eca7120bf513d8be118e8eff433fbcc8ca5369662cda164" *)
Parameter MetaCat : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> prop.

Axiom MetaCat_Set : MetaCat (fun _ => True) HomSet lam_id (fun X _ _ => lam_comp X).

Axiom MetaCat_IrrPartOrd : MetaCat IrrPartOrd BinRelnHom struct_id struct_comp.

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

Axiom MetaFunctor_IrrPartOrd_forgetful : MetaFunctor IrrPartOrd BinRelnHom struct_id struct_comp (fun _ => True) HomSet lam_id (fun X _ _ => lam_comp X) (fun A => ap A 0) (fun X Y f => f).

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

Theorem MetaCat_struct_r_partialord_left_adjoint_forgetful : exists F0 : set -> set, exists F1 : set -> set -> set -> set, exists eta : set -> set, exists eps : set -> set, MetaAdjunction_strict (fun X : set => True) HomSet lam_id (fun X Y Z : set => lam_comp X) IrrPartOrd BinRelnHom struct_id struct_comp F0 F1 (fun A : set => A 0) (fun A B f : set => f) eta eps.
set F0 := fun X : set => pack_r X (fun _ _ => False).
set F1 := fun X Y f : set => f.
set eta := fun X : set => lam_id X.
set eps := fun A : set => lam_id (A 0).
witness F0. witness F1. witness eta. witness eps.
prove MetaAdjunction_strict (fun X : set => True) HomSet lam_id (fun X Y Z : set => lam_comp X) IrrPartOrd BinRelnHom struct_id struct_comp F0 F1 (fun A : set => A 0) (fun A B f : set => f) eta eps.
claim L1: forall X, X = F0 X 0.
{ let X. exact pack_r_0_eq2 X (fun _ _ => False). }
claim L2: forall X Y f, HomSet X Y f -> BinRelnHom (F0 X) (F0 Y) f.
{ let X Y f.
  assume H1: f :e Y :^: X.
  prove BinRelnHom (F0 X) (F0 Y) f.
  prove BinRelnHom (pack_r X (fun _ _ => False)) (pack_r Y (fun _ _ => False)) f.
  rewrite BinRelnHom_eq. apply andI.
  - prove f :e Y :^: X. exact H1.
  - let x. assume Hx. let x'. assume Hx'.
    assume H2: False.
    exact H2.
}
claim L3: forall X, forall R:set -> set -> prop, eps (pack_r X R) = lam_id X.
{ let X R.
  prove lam_id (pack_r X R 0) = lam_id X.
  rewrite <- pack_r_0_eq2 X R.
  reflexivity.
}
apply MetaAdjunction_strict_I.
- prove MetaFunctor_strict (fun X : set => True) HomSet lam_id (fun X Y Z : set => lam_comp X) IrrPartOrd BinRelnHom struct_id struct_comp F0 F1.
  apply MetaFunctor_strict_I.
  + prove MetaCat (fun X : set => True) HomSet lam_id (fun X Y Z : set => lam_comp X).
    exact MetaCat_Set.
  + prove MetaCat IrrPartOrd BinRelnHom struct_id struct_comp.
    exact MetaCat_IrrPartOrd.
  + prove MetaFunctor (fun X : set => True) HomSet lam_id (fun X Y Z : set => lam_comp X) IrrPartOrd BinRelnHom struct_id struct_comp F0 F1.
    apply MetaFunctor_I.
    * { let X. assume _.
        prove IrrPartOrd (F0 X).
        prove IrrPartOrd (pack_r X (fun _ _ => False)).
        apply IrrPartOrd_I.
	- let x. assume Hx: x :e X. assume Hxx: False. exact Hxx.
	- let x. assume Hx. let y. assume Hy. let z. assume Hz.
	  assume Hxy: False.
	  prove False.
	  exact Hxy.
      }
    * let X Y f. assume _ _.
      assume Hf: HomSet X Y f.
      prove BinRelnHom (F0 X) (F0 Y) (F1 X Y f).
      exact L2 X Y f Hf.
    * let X. assume _.
      prove F1 X X (lam_id X) = struct_id (F0 X).
      prove lam_id X = lam_id (F0 X 0).
      rewrite <- L1.
      reflexivity.
    * let X Y Z f g. assume _ _ _.
      assume Hf: f :e Y :^: X.
      assume Hg: g :e Z :^: Y.
      prove F1 X Z (lam_comp X g f) = struct_comp (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f).
      prove lam_comp X g f = struct_comp (F0 X) (F0 Y) (F0 Z) g f.
      prove lam_comp X g f = lam_comp (F0 X 0) g f.
      rewrite <- L1.
      reflexivity.
- prove MetaFunctor IrrPartOrd BinRelnHom struct_id struct_comp (fun X : set => True) HomSet lam_id (fun X Y Z : set => lam_comp X) (fun A : set => A 0) (fun A B f : set => f).
  exact MetaFunctor_IrrPartOrd_forgetful.
- prove MetaNatTrans (fun X : set => True) HomSet lam_id (fun X Y Z : set => lam_comp X) (fun X : set => True) HomSet lam_id (fun X Y Z : set => lam_comp X) (fun X : set => X) (fun X Y f : set => f) (fun X : set => F0 X 0) (fun X Y f : set => F1 X Y f) eta.
  apply MetaNatTrans_I.
  + let X. assume _.
    prove HomSet X (F0 X 0) (eta X).
    rewrite <- L1.
    prove HomSet X X (lam_id X).
    prove lam_id X :e X :^: X.
    exact lam_id_exp_In X.
  + let X Y f. assume _ _.
    assume Hf: HomSet X Y f.
    prove lam_comp X f (eta X) = lam_comp X (eta Y) f.
    prove lam_comp X f (lam_id X) = lam_comp X (lam_id Y) f.
    rewrite lam_comp_id_L X Y f Hf.
    prove lam_comp X f (lam_id X) = f.
    exact lam_comp_id_R X Y f Hf.
- prove MetaNatTrans IrrPartOrd BinRelnHom struct_id struct_comp IrrPartOrd BinRelnHom struct_id struct_comp (fun A : set => F0 (A 0)) (fun A B h : set => h) (fun A : set => A) (fun A B h : set => h) eps.
  apply MetaNatTrans_I.
  + let A. assume HA: IrrPartOrd A.
    prove BinRelnHom (F0 (A 0)) A (eps A).
    apply IrrPartOrd_E A HA.
    let X R.
    assume HRirr: forall x :e X, ~R x x.
    assume HRtra: forall x y z :e X, R x y -> R y z -> R x z.
    prove BinRelnHom (F0 (pack_r X R 0)) (pack_r X R) (eps (pack_r X R)).
    rewrite <- pack_r_0_eq2.
    prove BinRelnHom (pack_r X (fun _ _ => False)) (pack_r X R) (eps (pack_r X R)).
    rewrite BinRelnHom_eq.
    apply andI.
    * prove eps (pack_r X R) :e X :^: X.
      rewrite L3.
      prove lam_id X :e X :^: X.
      exact lam_id_exp_In X.
    * let x. assume Hx. let y. assume Hy.
      assume Hxy: False.
      prove False.
      exact Hxy.
  + let A B h.
    assume HA: IrrPartOrd A.
    assume HB: IrrPartOrd B.
    prove BinRelnHom A B h
       -> struct_comp (F0 (A 0)) A B h (eps A) = struct_comp (F0 (A 0)) (F0 (B 0)) B (eps B) h.
    apply IrrPartOrd_E A HA.
    let X R.
    assume HRirr: forall x :e X, ~R x x.
    assume HRtra: forall x y z :e X, R x y -> R y z -> R x z.
    prove BinRelnHom (pack_r X R) B h
       -> struct_comp (F0 (pack_r X R 0)) (pack_r X R) B h (eps (pack_r X R)) = struct_comp (F0 (pack_r X R 0)) (F0 (B 0)) B (eps B) h.
    rewrite <- pack_r_0_eq2.
    prove BinRelnHom (pack_r X R) B h
       -> struct_comp (F0 X) (pack_r X R) B h (eps (pack_r X R)) = struct_comp (F0 X) (F0 (B 0)) B (eps B) h.
    apply IrrPartOrd_E B HB.
    let Y Q.
    assume HQirr: forall x :e Y, ~Q x x.
    assume HQtra: forall x y z :e Y, Q x y -> Q y z -> Q x z.
    prove BinRelnHom (pack_r X R) (pack_r Y Q) h
       -> struct_comp (F0 X) (pack_r X R) (pack_r Y Q) h (eps (pack_r X R)) = struct_comp (F0 X) (F0 (pack_r Y Q 0)) (pack_r Y Q) (eps (pack_r Y Q)) h.
    rewrite BinRelnHom_eq.
    assume Hh. apply Hh.
    assume Hh1: h :e Y :^: X.
    assume Hh2: forall x y :e X, R x y -> Q (h x) (h y).
    prove lam_comp (F0 X 0) h (eps (pack_r X R)) = lam_comp (F0 X 0) (eps (pack_r Y Q)) h.
    rewrite <- L1.
    prove lam_comp X h (eps (pack_r X R)) = lam_comp X (eps (pack_r Y Q)) h.
    rewrite L3. rewrite L3.
    prove lam_comp X h (lam_id X) = lam_comp X (lam_id Y) h.
    rewrite lam_comp_id_L X Y h Hh1.
    exact lam_comp_id_R X Y h Hh1.
- prove MetaAdjunction (fun X : set => True) HomSet lam_id (fun X Y Z : set => lam_comp X) IrrPartOrd BinRelnHom struct_id struct_comp F0 F1 (fun A : set => A 0) (fun A B f : set => f) eta eps.
  claim L4: forall X, lam_comp X (lam_id X) (lam_id X) = lam_id X.
  { let X. apply lam_comp_id_L.
    prove lam_id X :e X :^: X.
    exact lam_id_exp_In X.
  }
  apply MetaAdjunction_I.
  + let X. assume _.
    prove struct_comp (F0 X) (F0 (F0 X 0)) (F0 X) (eps (F0 X)) (F1 X (F0 X 0) (eta X))
        = struct_id (F0 X).
    prove lam_comp (F0 X 0) (eps (F0 X)) (eta X)
        = lam_id (F0 X 0).
    prove lam_comp (F0 X 0) (lam_id (F0 X 0)) (eta X)
        = lam_id (F0 X 0).
    rewrite <- L1.
    prove lam_comp X (lam_id X) (lam_id X) = lam_id X.
    exact L4 X.
  + let A. assume HA.
    prove lam_comp (A 0) (eps A) (eta (A 0)) = lam_id (A 0).
    apply IrrPartOrd_E A HA.
    let X R.
    assume HRirr: forall x :e X, ~R x x.
    assume HRtra: forall x y z :e X, R x y -> R y z -> R x z.
    prove lam_comp (pack_r X R 0) (eps (pack_r X R)) (eta (pack_r X R 0)) = lam_id (pack_r X R 0).
    rewrite <- pack_r_0_eq2 X R.
    prove lam_comp X (eps (pack_r X R)) (eta X) = lam_id X.
    rewrite L3.
    prove lam_comp X (lam_id X) (lam_id X) = lam_id X.
    exact L4 X.
Qed.
