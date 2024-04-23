(** $I sig/PfgEJul2021Preamble6.mgs **)

Section MetaCat.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Definition idT : prop := forall X:set, Obj X -> Hom X X (id X).
Definition compT : prop :=
 forall X Y Z:set, forall f g:set,
 Obj X -> Obj Y -> Obj Z
 ->
 Hom X Y f -> Hom Y Z g
 ->
 Hom X Z (comp X Y Z g f).

Definition idL : prop :=
 forall X Y:set, forall f:set,
 Obj X -> Obj Y -> Hom X Y f -> comp X X Y f (id X) = f.

Definition idR : prop :=
 forall X Y:set, forall f:set,
 Obj X -> Obj Y -> Hom X Y f -> comp X Y Y (id Y) f = f.

Definition compAssoc : prop :=
 forall X Y Z W:set, forall f g h:set,
 Obj X -> Obj Y -> Obj Z -> Obj W
 ->
 Hom X Y f -> Hom Y Z g -> Hom Z W h
 ->
 comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f).

Definition MetaCat : prop := (idT /\ compT) /\ (idL /\ idR) /\ compAssoc.

Theorem MetaCat_I :
    idT -> compT
 -> (forall X Y:set, forall f:set, Obj X -> Obj Y -> Hom X Y f -> comp X X Y f (id X) = f)
 -> (forall X Y:set, forall f:set, Obj X -> Obj Y -> Hom X Y f -> comp X Y Y (id Y) f = f)
 -> (forall X Y Z W:set, forall f g h:set, Obj X -> Obj Y -> Obj Z -> Obj W
 -> Hom X Y f -> Hom Y Z g -> Hom Z W h
 -> comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f))
 -> MetaCat.
assume H1 H2 H3 H4 H5.
prove (idT /\ compT) /\ (idL /\ idR) /\ compAssoc.
apply and3I.
- apply andI.
  + exact H1.
  + exact H2.
- apply andI.
  + exact H3.
  + exact H4.
- exact H5.
Qed.

Theorem MetaCat_E : MetaCat ->
 forall p:prop,
    (idT -> compT
         -> (forall X Y:set, forall f:set, Obj X -> Obj Y -> Hom X Y f -> comp X X Y f (id X) = f)
         -> (forall X Y:set, forall f:set, Obj X -> Obj Y -> Hom X Y f -> comp X Y Y (id Y) f = f)
         -> (forall X Y Z W:set, forall f g h:set, Obj X -> Obj Y -> Obj Z -> Obj W
	 -> Hom X Y f -> Hom Y Z g -> Hom Z W h
	 -> comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f))
         -> p)
  -> p.
assume HC. let p. assume Hp.
apply HC. assume H14 H5. apply H14. assume H12 H34.
apply H12. assume H1 H2.
apply H34. assume H3 H4.
exact Hp H1 H2 H3 H4 H5.
Qed.

End MetaCat.

Section MetaCatOp.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Theorem MetaCatOp :
 MetaCat Obj Hom id comp
 ->
 MetaCat Obj (fun X Y => Hom Y X) id (fun X Y Z f g => comp Z Y X g f).
assume HC. apply MetaCat_E Obj Hom id comp HC.
assume HC1: forall X:set, Obj X -> Hom X X (id X).
assume HC2: forall X Y Z:set, forall f g:set,
 Obj X -> Obj Y -> Obj Z ->
 Hom X Y f -> Hom Y Z g -> Hom X Z (comp X Y Z g f).
assume HC3: forall X Y:set, forall f:set,
 Obj X -> Obj Y -> Hom X Y f -> comp X X Y f (id X) = f.
assume HC4: forall X Y:set, forall f:set,
 Obj X -> Obj Y -> Hom X Y f -> comp X Y Y (id Y) f = f.
assume HC5: forall X Y Z W:set, forall f g h:set,
 Obj X -> Obj Y -> Obj Z -> Obj W ->
 Hom X Y f -> Hom Y Z g -> Hom Z W h ->
 comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f).
apply MetaCat_I.
- exact HC1.
- let X Y Z f g. assume HX HY HZ Hf Hg.
  exact HC2 Z Y X g f HZ HY HX Hg Hf.
- let X Y f. assume HX HY Hf.
  exact HC4 Y X f HY HX Hf.
- let X Y f. assume HX HY Hf.
  exact HC3 Y X f HY HX Hf.
- let X Y Z W f g h. assume HX HY HZ HW Hf Hg Hh.
  prove comp W Y X f (comp W Z Y g h) = comp W Z X (comp Z Y X f g) h.
  symmetry.
  exact HC5 W Z Y X h g f HW HZ HY HX Hh Hg Hf.
Qed.

End MetaCatOp.

Section LimsCoLims.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Definition monic: set -> set -> set -> prop
 := fun X Y f =>
       Obj X /\ Obj Y /\ Hom X Y f
    /\ forall Z:set, Obj Z ->
       forall g h:set, Hom Z X g -> Hom Z X h
       ->
           comp Z X Y f g = comp Z X Y f h
        -> g = h.

Definition terminal_p: set -> (set -> set) -> prop
 := fun Y h => Obj Y
     /\ forall X:set, Obj X
         -> Hom X Y (h X)
         /\ forall h':set, Hom X Y h' -> h' = h X.

Definition initial_p: set -> (set -> set) -> prop
 := fun Y h => Obj Y
     /\ forall X:set, Obj X
         -> Hom Y X (h X)
         /\ forall h':set, Hom Y X h' -> h' = h X.

Definition product_p : set -> set -> set -> set -> set -> (set -> set -> set -> set) -> prop
  := fun X Y Z pi0 pi1 pair =>
         Obj X
      /\ Obj Y
      /\ Obj Z
      /\ Hom Z X pi0
      /\ Hom Z Y pi1
      /\ forall W:set, Obj W -> forall h k:set, Hom W X h -> Hom W Y k
      ->
                 Hom W Z (pair W h k)
              /\ comp W Z X pi0 (pair W h k) = h
              /\ comp W Z Y pi1 (pair W h k) = k
              /\ forall u:set, Hom W Z u
                  -> comp W Z X pi0 u = h
                  -> comp W Z Y pi1 u = k
                  -> u = pair W h k.

Definition product_constr_p : (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> prop :=
  fun prod pi0 pi1 pair =>
    forall X Y:set, Obj X -> Obj Y
    -> product_p X Y (prod X Y) (pi0 X Y) (pi1 X Y) (pair X Y).

Definition coproduct_p : set -> set -> set -> set -> set -> (set -> set -> set -> set) -> prop
  := fun X Y Z i0 i1 comb =>
         Obj X
      /\ Obj Y
      /\ Obj Z
      /\ Hom X Z i0
      /\ Hom Y Z i1
      /\ forall W:set, Obj W -> forall h k:set, Hom X W h -> Hom Y W k
      ->
                 Hom Z W (comb W h k)
              /\ comp X Z W (comb W h k) i0 = h
              /\ comp Y Z W (comb W h k) i1 = k
              /\ forall hk:set, Hom Z W hk
                  -> comp X Z W hk i0 = h
                  -> comp Y Z W hk i1 = k
                  -> hk = comb W h k.

Definition coproduct_constr_p : (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> prop :=
  fun coprod i0 i1 copair =>
    forall X Y:set, Obj X -> Obj Y
    -> coproduct_p X Y (coprod X Y) (i0 X Y) (i1 X Y) (copair X Y).

Definition equalizer_p : set -> set -> set -> set -> set -> set -> (set -> set -> set) -> prop
  := fun X Y f g Q q fac =>
         Obj X
      /\ Obj Y
      /\ Hom X Y f
      /\ Hom X Y g
      /\ Obj Q
      /\ Hom Q X q
      /\ comp Q X Y f q = comp Q X Y g q 
      /\ forall W:set, Obj W -> forall h:set, Hom W X h -> comp W X Y f h = comp W X Y g h
      ->
                 Hom W Q (fac W h)
              /\ comp W Q X q (fac W h) = h
              /\ forall u:set, Hom W Q u
                  -> comp W Q X q u = h
                  -> u = fac W h.

Definition equalizer_constr_p : (set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set) -> prop :=
  fun quot canonmap fac =>
    forall X Y:set, Obj X -> Obj Y -> forall f g:set, Hom X Y f -> Hom X Y g
    -> equalizer_p X Y f g (quot X Y f g) (canonmap X Y f g) (fac X Y f g).

Definition coequalizer_p : set -> set -> set -> set -> set -> set -> (set -> set -> set) -> prop
  := fun X Y f g Q q fac =>
         Obj X
      /\ Obj Y
      /\ Hom X Y f
      /\ Hom X Y g
      /\ Obj Q
      /\ Hom Y Q q
      /\ comp X Y Q q f = comp X Y Q q g 
      /\ forall W:set, Obj W -> forall h:set, Hom Y W h -> comp X Y W h f = comp X Y W h g
      	 ->
                 Hom Q W (fac W h)
              /\ comp Y Q W (fac W h) q = h
              /\ forall u:set, Hom Q W u
                  -> comp Y Q W u q = h
                  -> u = fac W h.

Definition coequalizer_constr_p : (set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set) -> prop :=
  fun quot canonmap fac =>
    forall X Y:set, Obj X -> Obj Y -> forall f g:set, Hom X Y f -> Hom X Y g
    -> coequalizer_p X Y f g (quot X Y f g) (canonmap X Y f g) (fac X Y f g).

Definition pullback_p : set -> set -> set -> set -> set -> set -> set -> set -> (set -> set -> set -> set) -> prop
  := fun X Y Z f g P pi0 pi1 pair =>
         Obj X
      /\ Obj Y
      /\ Obj Z
      /\ Hom X Z f
      /\ Hom Y Z g
      /\ Obj P
      /\ Hom P X pi0
      /\ Hom P Y pi1
      /\ comp P X Z f pi0 = comp P Y Z g pi1 
      /\ forall W:set, Obj W ->
         forall h:set, Hom W X h ->
         forall k:set, Hom W Y k
	 ->
                 comp W X Z f h = comp W Y Z g k
		 ->
                 Hom W P (pair W h k)
              /\ comp W P X pi0 (pair W h k) = h
              /\ comp W P Y pi1 (pair W h k) = k
              /\ forall u:set, Hom W P u
                  -> comp W P X pi0 u = h
                  -> comp W P Y pi1 u = k
                  -> u = pair W h k.

Definition pullback_constr_p : (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set -> set -> set) -> prop :=
  fun pb pi0 pi1 pair =>
    forall X Y Z:set, Obj X -> Obj Y -> Obj Z ->
    forall f g:set, Hom X Z f -> Hom Y Z g
    ->
       pullback_p X Y Z f g (pb X Y Z f g) (pi0 X Y Z f g) (pi1 X Y Z f g) (pair X Y Z f g).

Definition pushout_p : set -> set -> set -> set -> set -> set -> set -> set -> (set -> set -> set -> set) -> prop
  := fun X Y Z f g P i0 i1 copair =>
         Obj X
      /\ Obj Y
      /\ Obj Z
      /\ Hom Z X f
      /\ Hom Z Y g
      /\ Obj P
      /\ Hom X P i0
      /\ Hom Y P i1
      /\ comp Z X P i0 f = comp Z Y P i1 g 
      /\ forall W:set, Obj W ->
         forall h:set, Hom X W h ->
         forall k:set, Hom Y W k
	 ->
                 comp Z X W h f = comp Z Y W k g
		 ->
                 Hom P W (copair W h k)
              /\ comp X P W (copair W h k) i0 = h
              /\ comp Y P W (copair W h k) i1 = k
              /\ forall u:set, Hom P W u
                  -> comp X P W u i0 = h
                  -> comp Y P W u i1 = k
                  -> u = copair W h k.

Definition pushout_constr_p : (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set -> set -> set) -> prop :=
  fun po i0 i1 copair =>
    forall X Y Z:set, Obj X -> Obj Y -> Obj Z ->
    forall f g:set, Hom Z X f -> Hom Z Y g
    ->
       pushout_p X Y Z f g (po X Y Z f g) (i0 X Y Z f g) (i1 X Y Z f g) (copair X Y Z f g).

Definition exponent_p: (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> set -> set -> set -> set -> (set -> set -> set) -> prop
 := fun prod pi0 pi1 pair X Y Z a lm =>
       Obj X /\ Obj Y /\ Obj Z /\ Hom (prod Z X) Y a
    /\ forall W:set, Obj W -> forall f:set, Hom (prod W X) Y f
        -> Hom W Z (lm W f)
        /\ comp (prod W X) (prod Z X) Y a
	        (pair Z X (prod W X) (comp (prod W X) W Z (lm W f) (pi0 W X)) (pi1 W X)) = f
        /\ forall g:set, Hom W Z g
            -> comp (prod W X) (prod Z X) Y a
                    (pair Z X (prod W X) (comp (prod W X) W Z g (pi0 W X)) (pi1 W X)) = f
            -> g = lm W f.

Definition product_exponent_constr_p: (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set -> set -> set) -> prop
 := fun prod pi0 pi1 pair exp a lm =>
        product_constr_p prod pi0 pi1 pair
     /\ forall X Y:set, Obj X -> Obj Y
         -> exponent_p prod pi0 pi1 pair X Y (exp X Y) (a X Y) (lm X Y).

Definition subobject_classifier_p: set -> (set -> set) -> set -> set -> (set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set) -> prop
 := fun one uniqa Omega tru ch constr_p =>
        terminal_p one uniqa
     /\ Obj Omega 
     /\ Hom one Omega tru
     /\ forall X Y:set, forall m:set, monic X Y m
         -> Hom Y Omega (ch X Y m)
         /\ pullback_p one Y Omega tru (ch X Y m) X (uniqa X) m (constr_p X Y m).

Definition nno_p: set -> (set -> set) -> set -> set -> set -> (set -> set -> set -> set) -> prop
 := fun one uniqa N zer suc rec =>
        terminal_p one uniqa
     /\ Obj N
     /\ Hom one N zer
     /\ Hom N N suc
     /\ forall X:set, forall x:set, forall f:set,
            Obj X -> Hom one X x -> Hom X X f
         -> Hom N X (rec X x f)
         /\ comp one N X (rec X x f) zer = x
         /\ comp N N X (rec X x f) suc = comp N X X f (rec X x f)
         /\ forall u:set, Hom N X u
             -> comp one N X u zer = x
             -> comp N N X u suc = comp N X X f u
             -> u = rec X x f.

End LimsCoLims.

Section LimsCoLims2.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Theorem product_coproduct_Op:
  forall X Y Z:set, forall pi0 pi1:set, forall pair:set -> set -> set -> set,
     product_p Obj Hom id comp X Y Z pi0 pi1 pair
  -> coproduct_p Obj (fun X Y => Hom Y X) id
     (fun X Y Z f g => comp Z Y X g f) X Y Z pi0 pi1 pair.
let X Y Z pi0 pi1 pair.
assume H1. exact H1.
Qed.

Theorem product_coproduct_constr_Op:
  forall prod:set -> set -> set, forall pi0 pi1:set -> set -> set, forall pair:set -> set -> set -> set -> set -> set,
     product_constr_p Obj Hom id comp prod pi0 pi1 pair
  -> coproduct_constr_p Obj (fun X Y => Hom Y X) id
       (fun X Y Z f g => comp Z Y X g f) prod pi0 pi1 pair.
let prod pi0 pi1 pair.
assume H1. exact H1.
Qed.

Theorem coproduct_product_Op:
  forall X Y Z:set, forall i0 i1:set, forall copair:set -> set -> set -> set,
     coproduct_p Obj Hom id comp X Y Z i0 i1 copair
  -> product_p Obj (fun X Y => Hom Y X) id
             (fun X Y Z f g => comp Z Y X g f) X Y Z i0 i1 copair.
let X Y Z i0 i1 copair.
assume H1. exact H1.
Qed.

Theorem coproduct_product_constr_Op:
  forall coprod:set -> set -> set, forall i0 i1:set -> set -> set, forall copair:set -> set -> set -> set -> set -> set,
     coproduct_constr_p Obj Hom id comp coprod i0 i1 copair
  -> product_constr_p Obj (fun X Y => Hom Y X) id
         (fun X Y Z f g => comp Z Y X g f) coprod i0 i1 copair.
let coprod i0 i1 copair.
assume H1. exact H1.
Qed.

Theorem equalizer_coequalizer_Op:
  forall X Y:set, forall f g:set, forall Q:set, forall q:set, forall fac:set -> set -> set,
     equalizer_p Obj Hom id comp X Y f g Q q fac
  -> coequalizer_p Obj (fun X Y => Hom Y X) id
         (fun X Y Z f g => comp Z Y X g f) Y X f g Q q fac.
let X Y f g Q q fac.
assume HE.
apply HE. assume HE. apply HE. assume HE.
apply HE. assume HE. apply HE. assume HE.
apply HE. assume HE. apply HE. assume HE. apply HE.
assume HE1: Obj X.
assume HE2: Obj Y.
assume HE3: Hom X Y f.
assume HE4: Hom X Y g.
assume HE5: Obj Q.
assume HE6: Hom Q X q.
assume HE7: comp Q X Y f q = comp Q X Y g q.
assume HE8: forall W:set, Obj W -> forall h:set, Hom W X h -> comp W X Y f h = comp W X Y g h ->
                 Hom W Q (fac W h)
              /\ comp W Q X q (fac W h) = h
              /\ forall u:set, Hom W Q u
                  -> comp W Q X q u = h
                  -> u = fac W h.
prove Obj Y
   /\ Obj X
   /\ Hom X Y f
   /\ Hom X Y g
   /\ Obj Q
   /\ Hom Q X q
   /\ comp Q X Y f q = comp Q X Y g q
   /\ forall W:set, Obj W -> forall h:set, Hom W X h -> comp W X Y f h = comp W X Y g h ->
              Hom W Q (fac W h)
           /\ comp W Q X q (fac W h) = h
           /\ forall u:set, Hom W Q u
               -> comp W Q X q u = h
               -> u = fac W h.
apply and8I.
- exact HE2.
- exact HE1.
- exact HE3.
- exact HE4.
- exact HE5.
- exact HE6.
- exact HE7.
- exact HE8.
Qed.

Theorem equalizer_coequalizer_constr_Op:
  forall quot:set -> set -> set -> set -> set,
  forall canonmap: set -> set -> set -> set -> set,
  forall fac: set -> set -> set -> set -> set -> set -> set,
     equalizer_constr_p Obj Hom id comp quot canonmap fac
  -> coequalizer_constr_p Obj (fun X Y => Hom Y X) id
        (fun X Y Z f g => comp Z Y X g f) (fun X Y f g => quot Y X f g)
	(fun X Y f g => canonmap Y X f g) (fun X Y f g => fac Y X f g).
let quot canonmap fac.
assume HE.
let X Y. assume HX HY.
let f g. assume Hf Hg.
exact equalizer_coequalizer_Op Y X f g (quot Y X f g) (canonmap Y X f g) (fac Y X f g) (HE Y X HY HX f g Hf Hg).
Qed.

Theorem coequalizer_equalizer_Op:
  forall X Y:set, forall f g:set, forall Q:set, forall q:set, forall fac:set -> set -> set,
     coequalizer_p Obj Hom id comp X Y f g Q q fac
  -> equalizer_p Obj (fun X Y => Hom Y X) id
        (fun X Y Z f g => comp Z Y X g f) Y X f g Q q fac.
let X Y f g Q q fac.
assume HE.
apply HE. assume HE. apply HE. assume HE.
apply HE. assume HE. apply HE. assume HE.
apply HE. assume HE. apply HE. assume HE. apply HE.
assume HE1: Obj X.
assume HE2: Obj Y.
assume HE3: Hom X Y f.
assume HE4: Hom X Y g.
assume HE5: Obj Q.
assume HE6: Hom Y Q q.
assume HE7: comp X Y Q q f = comp X Y Q q g.
assume HE8: forall W:set, Obj W -> forall h:set, Hom Y W h -> comp X Y W h f = comp X Y W h g ->
                 Hom Q W (fac W h)
              /\ comp Y Q W (fac W h) q = h
              /\ forall u:set, Hom Q W u
                  -> comp Y Q W u q = h
                  -> u = fac W h.
prove Obj Y
   /\ Obj X
   /\ Hom X Y f
   /\ Hom X Y g
   /\ Obj Q
   /\ Hom Y Q q
   /\ comp X Y Q q f = comp X Y Q q g
   /\ forall W:set, Obj W -> forall h:set, Hom Y W h -> comp X Y W h f = comp X Y W h g ->
                 Hom Q W (fac W h)
              /\ comp Y Q W (fac W h) q = h
              /\ forall u:set, Hom Q W u
                  -> comp Y Q W u q = h
                  -> u = fac W h.
apply and8I.
- exact HE2.
- exact HE1.
- exact HE3.
- exact HE4.
- exact HE5.
- exact HE6.
- exact HE7.
- exact HE8.
Qed.

Theorem coequalizer_equalizer_constr_Op:
  forall quot:set -> set -> set -> set -> set,
  forall canonmap: set -> set -> set -> set -> set,
  forall fac: set -> set -> set -> set -> set -> set -> set,
     coequalizer_constr_p Obj Hom id comp quot canonmap fac
  -> equalizer_constr_p Obj (fun X Y => Hom Y X) id
          (fun X Y Z f g => comp Z Y X g f) (fun X Y f g => quot Y X f g)
	  (fun X Y f g => canonmap Y X f g) (fun X Y f g => fac Y X f g).
let quot canonmap fac.
assume HE.
let X Y. assume HX HY.
let f g. assume Hf Hg.
exact coequalizer_equalizer_Op Y X f g (quot Y X f g) (canonmap Y X f g) (fac Y X f g) (HE Y X HY HX f g Hf Hg).
Qed.

Theorem pullback_pushout_Op:
  forall X Y Z:set, forall f g:set, forall P:set, forall pi0 pi1:set, forall pair:set -> set -> set -> set,
     pullback_p Obj Hom id comp X Y Z f g P pi0 pi1 pair
  -> pushout_p Obj (fun X Y => Hom Y X) id
          (fun X Y Z f g => comp Z Y X g f) X Y Z f g P pi0 pi1 pair.
let X Y Z f g P pi0 pi1 pair.
assume HP. exact HP.
Qed.

Theorem pullback_pushout_constr_Op:
  forall pb:set -> set -> set -> set -> set -> set, forall pi0 pi1:set -> set -> set -> set -> set -> set,
  forall pair:set -> set -> set -> set -> set -> set -> set -> set -> set,
     pullback_constr_p Obj Hom id comp pb pi0 pi1 pair
  -> pushout_constr_p Obj (fun X Y => Hom Y X) id
          (fun X Y Z f g => comp Z Y X g f) pb pi0 pi1 pair.
let pb pi0 pi1 pair.
assume HP. exact HP.
Qed.

Theorem pushout_pullback_Op:
  forall X Y Z:set, forall f g:set, forall P:set, forall i0 i1:set, forall copair:set -> set -> set -> set,
     pushout_p Obj Hom id comp X Y Z f g P i0 i1 copair
  -> pullback_p Obj (fun X Y => Hom Y X) id
         (fun X Y Z f g => comp Z Y X g f) X Y Z f g P i0 i1 copair.
let X Y Z f g P i0 i1 copair.
assume HP. exact HP.
Qed.

Theorem pushout_pullback_constr_Op:
  forall po:set -> set -> set -> set -> set -> set, forall i0 i1:set -> set -> set -> set -> set -> set,
  forall copair:set -> set -> set -> set -> set -> set -> set -> set -> set,
     pushout_constr_p Obj Hom id comp po i0 i1 copair
  -> pullback_constr_p Obj (fun X Y => Hom Y X) id
        (fun X Y Z f g => comp Z Y X g f) po i0 i1 copair.
let po i0 i1 copair.
assume HP. exact HP.
Qed.

Theorem product_equalizer_pullback_constr:
  MetaCat Obj Hom id comp ->
  forall quot:set -> set -> set -> set -> set,
  forall canonmap:set -> set -> set -> set -> set,
  forall fac:set -> set -> set -> set -> set -> set -> set,
  equalizer_constr_p Obj Hom id comp quot canonmap fac
  ->
  forall prod:set -> set -> set,
  forall pi0:set -> set -> set,
  forall pi1:set -> set -> set,
  forall pair:set -> set -> set -> set -> set -> set,
  product_constr_p Obj Hom id comp prod pi0 pi1 pair
  ->
  pullback_constr_p Obj Hom id comp
    (fun X Y Z f g => quot (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y)))
    (fun X Y Z f g => comp (quot (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y))) (prod X Y) X (pi0 X Y) (canonmap (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y))))
    (fun X Y Z f g => comp (quot (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y))) (prod X Y) Y (pi1 X Y) (canonmap (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y))))
    (fun X Y Z f g W h k => fac (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y)) W (pair X Y W h k)).
assume HC. apply MetaCat_E Obj Hom id comp HC.
assume HC1: forall X:set, Obj X -> Hom X X (id X).
assume HC2: forall X Y Z:set, forall f g:set,
 Obj X -> Obj Y -> Obj Z ->
 Hom X Y f -> Hom Y Z g -> Hom X Z (comp X Y Z g f).
assume HC3: forall X Y:set, forall f:set,
 Obj X -> Obj Y -> Hom X Y f -> comp X X Y f (id X) = f.
assume HC4: forall X Y:set, forall f:set,
 Obj X -> Obj Y -> Hom X Y f -> comp X Y Y (id Y) f = f.
assume HC5: forall X Y Z W:set, forall f g h:set,
 Obj X -> Obj Y -> Obj Z -> Obj W ->
 Hom X Y f -> Hom Y Z g -> Hom Z W h ->
 comp X Y W (comp Y Z W h g) f = comp X Z W h (comp X Y Z g f).
let quot canonmap fac.
assume HE: equalizer_constr_p Obj Hom id comp quot canonmap fac.
let prod pi0 pi1 pair.
assume HP: product_constr_p Obj Hom id comp prod pi0 pi1 pair.
let X Y Z.
assume HX: Obj X.
assume HY: Obj Y.
assume HZ: Obj Z.
let f g.
assume Hf: Hom X Z f.
assume Hg: Hom Y Z g.
set pi0f := comp (prod X Y) X Z f (pi0 X Y).
set pi1g := comp (prod X Y) Y Z g (pi1 X Y).
set P := quot (prod X Y) Z pi0f pi1g.
set pi0P := comp P (prod X Y) X (pi0 X Y) (canonmap (prod X Y) Z pi0f pi1g).
set pi1P := comp P (prod X Y) Y (pi1 X Y) (canonmap (prod X Y) Z pi0f pi1g).
set pairP := (fun W:set => fun h k:set => fac (prod X Y) Z pi0f pi1g W (pair X Y W h k)).
apply HP X Y HX HY. assume HP1.
apply HP1. assume HP1. apply HP1. assume HP1.
apply HP1. assume HP1. apply HP1.
assume _ _.
assume HP1: Obj (prod X Y).
assume HP2: Hom (prod X Y) X (pi0 X Y).
assume HP3: Hom (prod X Y) Y (pi1 X Y).
assume HP4: forall W:set, Obj W -> forall h k:set, Hom W X h -> Hom W Y k ->
                 Hom W (prod X Y) (pair X Y W h k)
              /\ comp W (prod X Y) X (pi0 X Y) (pair X Y W h k) = h
              /\ comp W (prod X Y) Y (pi1 X Y) (pair X Y W h k) = k
              /\ forall u:set, Hom W (prod X Y) u
                  -> comp W (prod X Y) X (pi0 X Y) u = h
                  -> comp W (prod X Y) Y (pi1 X Y) u = k
                  -> u = pair X Y W h k.
claim Lpi0f: Hom (prod X Y) Z pi0f.
{ exact HC2 (prod X Y) X Z (pi0 X Y) f HP1 HX HZ HP2 Hf. }
claim Lpi1g: Hom (prod X Y) Z pi1g.
{ exact HC2 (prod X Y) Y Z (pi1 X Y) g HP1 HY HZ HP3 Hg. }
apply HE (prod X Y) Z HP1 HZ pi0f pi1g Lpi0f Lpi1g.
assume HE1.
apply HE1. assume HE1. apply HE1. assume HE1.
apply HE1. assume HE1. apply HE1. assume HE1. apply HE1. assume HE1.
apply HE1.
assume _ _ _ _.
assume HE1: Obj P.
assume HE2: Hom P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g).
assume HE3: comp P (prod X Y) Z pi0f (canonmap (prod X Y) Z pi0f pi1g) = comp P (prod X Y) Z pi1g (canonmap (prod X Y) Z pi0f pi1g).
assume HE4: forall W:set, Obj W -> forall h:set, Hom W (prod X Y) h -> comp W (prod X Y) Z pi0f h = comp W (prod X Y) Z pi1g h ->
                 Hom W P (fac (prod X Y) Z pi0f pi1g W h)
              /\ comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) (fac (prod X Y) Z pi0f pi1g W h) = h
              /\ forall u:set, Hom W P u
                  -> comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) u = h
                  -> u = fac (prod X Y) Z pi0f pi1g W h.
claim Lpi0P: Hom P X pi0P.
{ exact HC2 P (prod X Y) X (canonmap (prod X Y) Z pi0f pi1g) (pi0 X Y) HE1 HP1 HX HE2 HP2. }
claim Lpi1P: Hom P Y pi1P.
{ exact HC2 P (prod X Y) Y (canonmap (prod X Y) Z pi0f pi1g) (pi1 X Y) HE1 HP1 HY HE2 HP3. }
prove pullback_p Obj Hom id comp X Y Z f g P pi0P pi1P pairP.
prove Obj X
   /\ Obj Y
   /\ Obj Z
   /\ Hom X Z f
   /\ Hom Y Z g
   /\ Obj P
   /\ Hom P X pi0P
   /\ Hom P Y pi1P
   /\ comp P X Z f pi0P = comp P Y Z g pi1P
   /\ forall W:set, Obj W ->
      forall h:set, Hom W X h ->
      forall k:set, Hom W Y k ->
              comp W X Z f h = comp W Y Z g k ->
              Hom W P (pairP W h k)
           /\ comp W P X pi0P (pairP W h k) = h
           /\ comp W P Y pi1P (pairP W h k) = k
           /\ forall u:set, Hom W P u
               -> comp W P X pi0P u = h
               -> comp W P Y pi1P u = k
               -> u = pairP W h k.
apply and10I.
- exact HX.
- exact HY.
- exact HZ.
- exact Hf.
- exact Hg.
- prove Obj P. exact HE1.
- prove Hom P X pi0P. exact Lpi0P.
- prove Hom P Y pi1P. exact Lpi1P.
- prove comp P X Z f pi0P = comp P Y Z g pi1P.
  prove comp P X Z f (comp P (prod X Y) X (pi0 X Y) (canonmap (prod X Y) Z pi0f pi1g))
      = comp P Y Z g (comp P (prod X Y) Y (pi1 X Y) (canonmap (prod X Y) Z pi0f pi1g)).
  transitivity comp P (prod X Y) Z pi0f (canonmap (prod X Y) Z pi0f pi1g),
               comp P (prod X Y) Z pi1g (canonmap (prod X Y) Z pi0f pi1g).
  + symmetry. apply HC5.
    * exact HE1.
    * exact HP1.
    * exact HX.
    * exact HZ.
    * exact HE2.
    * exact HP2.
    * exact Hf.
  + prove comp P (prod X Y) Z pi0f (canonmap (prod X Y) Z pi0f pi1g)
        = comp P (prod X Y) Z pi1g (canonmap (prod X Y) Z pi0f pi1g).
    exact HE3.
  + apply HC5.
    * exact HE1.
    * exact HP1.
    * exact HY.
    * exact HZ.
    * exact HE2.
    * exact HP3.
    * exact Hg.
- let W. assume HW: Obj W.
  let h. assume Hh: Hom W X h.
  let k. assume Hk: Hom W Y k.
  assume Hhk: comp W X Z f h = comp W Y Z g k.
  apply HP4 W HW h k Hh Hk.
  assume HP4a. apply HP4a. assume HP4a. apply HP4a.
  assume HP4a: Hom W (prod X Y) (pair X Y W h k).
  assume HP4b: comp W (prod X Y) X (pi0 X Y) (pair X Y W h k) = h.
  assume HP4c: comp W (prod X Y) Y (pi1 X Y) (pair X Y W h k) = k.
  assume HP4d: forall u:set, Hom W (prod X Y) u
                  -> comp W (prod X Y) X (pi0 X Y) u = h
                  -> comp W (prod X Y) Y (pi1 X Y) u = k
                  -> u = pair X Y W h k.
  claim LP1: comp W (prod X Y) Z pi0f (pair X Y W h k) = comp W (prod X Y) Z pi1g (pair X Y W h k).
  { transitivity comp W X Z f (comp W (prod X Y) X (pi0 X Y) (pair X Y W h k)),
                 comp W Y Z g (comp W (prod X Y) Y (pi1 X Y) (pair X Y W h k)).
    - exact HC5 W (prod X Y) X Z (pair X Y W h k) (pi0 X Y) f HW HP1 HX HZ HP4a HP2 Hf.
    - prove comp W X Z f (comp W (prod X Y) X (pi0 X Y) (pair X Y W h k))
          = comp W Y Z g (comp W (prod X Y) Y (pi1 X Y) (pair X Y W h k)).
      rewrite HP4b. rewrite HP4c.
      prove comp W X Z f h = comp W Y Z g k.
      exact Hhk.
    - symmetry.
      exact HC5 W (prod X Y) Y Z (pair X Y W h k) (pi1 X Y) g HW HP1 HY HZ HP4a HP3 Hg.
  }
  apply HE4 W HW (pair X Y W h k) HP4a LP1. assume HE4a. apply HE4a.
  assume HE4a: Hom W P (fac (prod X Y) Z pi0f pi1g W (pair X Y W h k)).
  assume HE4b: comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) (fac (prod X Y) Z pi0f pi1g W (pair X Y W h k)) = pair X Y W h k.
  assume HE4c: forall u:set, Hom W P u
          -> comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) u = pair X Y W h k
          -> u = fac (prod X Y) Z pi0f pi1g W (pair X Y W h k).
  claim Lhk: Hom W P (pairP W h k).
  { exact HE4a. }
  apply and4I.
  + prove Hom W P (pairP W h k). exact Lhk.
  + prove comp W P X pi0P (pairP W h k) = h.
    transitivity comp W (prod X Y) X (pi0 X Y) (comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) (fac (prod X Y) Z pi0f pi1g W (pair X Y W h k))).
    * exact HC5 W P (prod X Y) X (pairP W h k) (canonmap (prod X Y) Z pi0f pi1g) (pi0 X Y) HW HE1 HP1 HX HE4a HE2 HP2.
    * rewrite HE4b.
      prove comp W (prod X Y) X (pi0 X Y) (pair X Y W h k) = h.
      exact HP4b.
  + prove comp W P Y pi1P (pairP W h k) = k.
    transitivity comp W (prod X Y) Y (pi1 X Y) (comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) (fac (prod X Y) Z pi0f pi1g W (pair X Y W h k))).
    * exact HC5 W P (prod X Y) Y (pairP W h k) (canonmap (prod X Y) Z pi0f pi1g) (pi1 X Y) HW HE1 HP1 HY HE4a HE2 HP3.
    * rewrite HE4b.
      prove comp W (prod X Y) Y (pi1 X Y) (pair X Y W h k) = k.
      exact HP4c.
  + let u. assume Hu: Hom W P u.
    assume Huh: comp W P X pi0P u = h.
    assume Huk: comp W P Y pi1P u = k.
    prove u = pairP W h k.
    prove u = fac (prod X Y) Z pi0f pi1g W (pair X Y W h k).
    apply HE4c u Hu.
    prove comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) u = pair X Y W h k.
    apply HP4d (comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) u).
    * prove Hom W (prod X Y) (comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) u).
      exact HC2 W P (prod X Y) u (canonmap (prod X Y) Z pi0f pi1g) HW HE1 HP1 Hu HE2.
    * prove comp W (prod X Y) X (pi0 X Y) (comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) u) = h.
      rewrite <- HC5 W P (prod X Y) X u (canonmap (prod X Y) Z pi0f pi1g) (pi0 X Y) HW HE1 HP1 HX Hu HE2 HP2.
      prove comp W P X (comp P (prod X Y) X (pi0 X Y) (canonmap (prod X Y) Z pi0f pi1g)) u = h.
      exact Huh.
    * prove comp W (prod X Y) Y (pi1 X Y) (comp W P (prod X Y) (canonmap (prod X Y) Z pi0f pi1g) u) = k.
      rewrite <- HC5 W P (prod X Y) Y u (canonmap (prod X Y) Z pi0f pi1g) (pi1 X Y) HW HE1 HP1 HY Hu HE2 HP3.
      prove comp W P Y (comp P (prod X Y) Y (pi1 X Y) (canonmap (prod X Y) Z pi0f pi1g)) u = k.
      exact Huk.
Qed.

Theorem product_equalizer_pullback_constr_ex:
 MetaCat Obj Hom id comp
 ->
 (exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  equalizer_constr_p Obj Hom id comp quot canonmap fac)
 ->
 (exists prod:set -> set -> set,
  exists pi0:set -> set -> set,
  exists pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  product_constr_p Obj Hom id comp prod pi0 pi1 pair)
 ->
  exists pb:set -> set -> set -> set -> set -> set,
  exists pi0:set -> set -> set -> set -> set -> set,
  exists pi1:set -> set -> set -> set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pullback_constr_p Obj Hom id comp pb pi0 pi1 pair.
assume HC HE HP.
apply HE. let quot. assume HE.
apply HE. let canonmap. assume HE.
apply HE. let fac.
assume HE: equalizer_constr_p Obj Hom id comp quot canonmap fac.
apply HP. let prod. assume HP.
apply HP. let pi0. assume HP.
apply HP. let pi1. assume HP.
apply HP. let pair.
assume HP: product_constr_p Obj Hom id comp prod pi0 pi1 pair.
witness (fun X Y Z f g => quot (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y))).
witness (fun X Y Z f g => comp (quot (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y))) (prod X Y) X (pi0 X Y) (canonmap (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y)))).
witness (fun X Y Z f g => comp (quot (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y))) (prod X Y) Y (pi1 X Y) (canonmap (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y)))).
witness (fun X Y Z f g W h k => fac (prod X Y) Z (comp (prod X Y) X Z f (pi0 X Y)) (comp (prod X Y) Y Z g (pi1 X Y)) W (pair X Y W h k)).
exact product_equalizer_pullback_constr HC quot canonmap fac HE prod pi0 pi1 pair HP.
Qed.

End LimsCoLims2.

Section LimsCoLims3.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Theorem coproduct_coequalizer_pushout_constr_ex:
 MetaCat Obj Hom id comp
 ->
 (exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  coequalizer_constr_p Obj Hom id comp quot canonmap fac)
 ->
 (exists coprod:set -> set -> set,
  exists i0:set -> set -> set,
  exists i1:set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set,
  coproduct_constr_p Obj Hom id comp coprod i0 i1 copair)
 ->
  exists po:set -> set -> set -> set -> set -> set,
  exists i0:set -> set -> set -> set -> set -> set,
  exists i1:set -> set -> set -> set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pushout_constr_p Obj Hom id comp po i0 i1 copair.
assume HC HE HP.
claim LC: MetaCat Obj (fun X Y => Hom Y X) id (fun X Y Z f g => comp Z Y X g f).
{ exact MetaCatOp Obj Hom id comp HC. }
prove exists pb:set -> set -> set -> set -> set -> set,
      exists pi0:set -> set -> set -> set -> set -> set,
      exists pi1:set -> set -> set -> set -> set -> set,
      exists pair:set -> set -> set -> set -> set -> set -> set -> set -> set,
      pullback_constr_p Obj (fun X Y => Hom Y X) id (fun X Y Z f g => comp Z Y X g f) pb pi0 pi1 pair.
apply product_equalizer_pullback_constr_ex Obj (fun X Y => Hom Y X) id (fun X Y Z f g => comp Z Y X g f) LC.
- apply HE. let quot. assume HE.
  apply HE. let canonmap. assume HE.
  apply HE. let fac.
  assume HE: coequalizer_constr_p Obj Hom id comp quot canonmap fac.
  witness (fun X Y:set => quot Y X).
  witness (fun X Y:set => canonmap Y X).
  witness (fun X Y:set => fac Y X).
  exact coequalizer_equalizer_constr_Op Obj Hom id comp quot canonmap fac HE.
- exact HP.
Qed.

End LimsCoLims3.

Definition SetHom : set -> set -> set -> prop
  := fun X Y f => f :e Y :^: X.

Theorem MetaCatSet_initial_gen : forall Obj:set -> prop,
  Obj 0
  ->
  exists Y:set, exists uniqa:set -> set,
  initial_p Obj SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) Y uniqa.
let Obj. assume HO.
witness 0. witness (fun X => (fun x :e 0 => 0)).
prove Obj 0
   /\ forall X:set, Obj X
       -> SetHom 0 X (fun x :e 0 => 0)
       /\ forall h':set, SetHom 0 X h' -> h' = (fun x :e 0 => 0).
apply andI.
- exact HO.
- let X. assume HX. apply andI.
  + prove SetHom 0 X (fun x :e 0 => 0). prove (fun x :e 0 => 0) :e Pi_ x :e 0, X.
    apply lam_Pi. let x. assume Hx: x :e 0.
    prove False. exact EmptyE x Hx.
  + let h. assume Hh: h :e Pi_ x :e 0, X.
    prove h = (fun x :e 0 => 0).
    transitivity (fun x :e 0 => h x).
    * symmetry. exact Pi_eta 0 (fun _ => X) h Hh.
    * apply lam_ext. let x. assume Hx: x :e 0.
      prove False. exact EmptyE x Hx.
Qed.

Theorem MetaCatSet_initial : exists Y:set, exists uniqa:set -> set,
  initial_p (fun _ => True) SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) Y uniqa.
exact MetaCatSet_initial_gen (fun _ => True) TrueI.
Qed.

Theorem MetaCatSet_terminal_gen : forall Obj:set -> prop,
  Obj 1
  ->
  exists Y:set, exists uniqa:set -> set,
  terminal_p Obj SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) Y uniqa.
let Obj. assume HO.
witness 1. witness (fun X => (fun x :e X => 0)).
prove Obj 1
   /\ forall X:set, Obj X
       -> SetHom X 1 (fun x :e X => 0)
       /\ forall h':set, SetHom X 1 h' -> h' = (fun x :e X => 0).
apply andI.
- exact HO.
- let X. assume HX. apply andI.
  + prove SetHom X 1 (fun x :e X => 0). prove (fun x :e X => 0) :e Pi_ x :e X, 1.
    apply lam_Pi. let x. assume Hx: x :e X.
    exact In_0_1.
  + let h. assume Hh: h :e Pi_ x :e X, 1.
    prove h = (fun x :e X => 0).
    transitivity (fun x :e X => h x).
    * symmetry. exact Pi_eta X (fun _ => 1) h Hh.
    * apply lam_ext. let x. assume Hx: x :e X.
      prove h x = 0.
      apply SingE 0 (h x).
      prove h x :e {0}.
      rewrite <- eq_1_Sing0.
      prove h x :e 1.
      exact ap_Pi X (fun _ => 1) h x Hh Hx.
Qed.

Theorem MetaCatSet_terminal : exists Y:set, exists uniqa:set -> set,
  terminal_p (fun _ => True) SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) Y uniqa.
exact MetaCatSet_terminal_gen (fun _ => True) TrueI.
Qed.

Theorem MetaCatSet_coproduct_gen : forall Obj:set -> prop,
  (forall X, Obj X -> forall Y, Obj Y -> Obj (setsum X Y))
  ->
  exists coprod:set -> set -> set,
  exists i0 i1:set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set,
  coproduct_constr_p Obj SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) coprod i0 i1 copair.
let Obj.
assume HO: forall X, Obj X -> forall Y, Obj Y -> Obj (setsum X Y).
witness setsum.
witness (fun X Y => fun x :e X => Inj0 x).
witness (fun X Y => fun y :e Y => Inj1 y).
witness (fun X Y W h k => (fun z :e X :+: Y => combine_funcs X Y (fun x => h x) (fun y => k y) z)).
let X Y.
assume HX: Obj X.
assume HY: Obj Y.
set Z := X :+: Y.
set i0 := (fun x :e X => Inj0 x).
set i1 := (fun y :e Y => Inj1 y).
set comb := fun W:set => fun h k:set => (fun z :e X :+: Y => combine_funcs X Y (fun x => h x) (fun y => k y) z).
prove Obj X
   /\ Obj Y
   /\ Obj Z
   /\ SetHom X Z i0
   /\ SetHom Y Z i1
   /\ forall W, Obj W -> forall h k:set, SetHom X W h -> SetHom Y W k ->
              SetHom Z W (comb W h k)
           /\ (fun x :e X => comb W h k (i0 x)) = h
           /\ (fun y :e Y => comb W h k (i1 y)) = k
           /\ forall hk:set, SetHom Z W hk
               -> (fun x :e X => hk (i0 x)) = h
               -> (fun y :e Y => hk (i1 y)) = k
               -> hk = comb W h k.
apply and6I.
- exact HX.
- exact HY.
- exact HO X HX Y HY.
- prove SetHom X Z i0.
  prove i0 :e Pi_ x :e X, Z.
  apply lam_Pi.
  let x. assume Hx. 
  prove Inj0 x :e X :+: Y.
  exact Inj0_setsum X Y x Hx.
- prove SetHom Y Z i1.
  prove i1 :e Pi_ y :e Y, Z.
  apply lam_Pi.
  let y. assume Hy. 
  prove Inj1 y :e X :+: Y.
  exact Inj1_setsum X Y y Hy.
- let W. assume HW: Obj W.
  let h k.
  assume Hh: SetHom X W h.
  assume Hk: SetHom Y W k.
  prove SetHom Z W (comb W h k)
     /\ (fun x :e X => comb W h k (i0 x)) = h
     /\ (fun y :e Y => comb W h k (i1 y)) = k
     /\ forall hk:set, SetHom Z W hk
                  -> (fun x :e X => hk (i0 x)) = h
                  -> (fun y :e Y => hk (i1 y)) = k
                  -> hk = comb W h k.
  apply and4I.
  + prove SetHom Z W (comb W h k).
    prove (fun z :e X :+: Y => combine_funcs X Y (fun x => h x) (fun y => k y) z) :e Pi_ z :e Z, W.
    apply lam_Pi.
    let z. assume Hz: z :e X :+: Y.
    prove (combine_funcs X Y (fun x => h x) (fun y => k y) z) :e W.
    apply setsum_Inj_inv X Y z Hz.
    * assume H1. apply H1. let x. assume H2. apply H2.
      assume Hx: x :e X.
      assume H2: z = Inj0 x.
      rewrite H2.
      prove (combine_funcs X Y (fun x => h x) (fun y => k y) (Inj0 x)) :e W.
      rewrite combine_funcs_eq1 X Y (fun x => h x) (fun y => k y) x.
      prove h x :e W.
      exact ap_Pi X (fun _ => W) h x Hh Hx.
    * assume H1. apply H1. let y. assume H2. apply H2.
      assume Hy: y :e Y.
      assume H2: z = Inj1 y.
      rewrite H2.
      prove (combine_funcs X Y (fun x => h x) (fun y => k y) (Inj1 y)) :e W.
      rewrite combine_funcs_eq2 X Y (fun x => h x) (fun y => k y) y.
      prove k y :e W.
      exact ap_Pi Y (fun _ => W) k y Hk Hy.
  + prove (fun x :e X => comb W h k (i0 x)) = h.
    transitivity (fun x :e X => h x).
    * apply lam_ext. let x. assume Hx.
      prove comb W h k (i0 x) = h x.
      prove (fun z :e X :+: Y => combine_funcs X Y (fun x => h x) (fun y => k y) z) ((fun x :e X => Inj0 x) x) = h x.
      rewrite beta X Inj0 x Hx.
      prove (fun z :e X :+: Y => combine_funcs X Y (fun x => h x) (fun y => k y) z) (Inj0 x) = h x.
      rewrite beta (X :+: Y) (fun z => combine_funcs X Y (fun x => h x) (fun y => k y) z) (Inj0 x) (Inj0_setsum X Y x Hx).
      apply combine_funcs_eq1.
    * exact Pi_eta X (fun _ => W) h Hh.
  + prove (fun y :e Y => comb W h k (i1 y)) = k.
    transitivity (fun y :e Y => k y).
    * apply lam_ext. let y. assume Hy.
      prove comb W h k (i1 y) = k y.
      prove (fun z :e X :+: Y => combine_funcs X Y (fun x => h x) (fun y => k y) z) ((fun y :e Y => Inj1 y) y) = k y.
      rewrite beta Y Inj1 y Hy.
      prove (fun z :e X :+: Y => combine_funcs X Y (fun x => h x) (fun y => k y) z) (Inj1 y) = k y.
      rewrite beta (X :+: Y) (fun z => combine_funcs X Y (fun x => h x) (fun y => k y) z) (Inj1 y) (Inj1_setsum X Y y Hy).
      apply combine_funcs_eq2.
    * exact Pi_eta Y (fun _ => W) k Hk.
  + let hk.
    assume Hhk: SetHom Z W hk.
    assume Hhkh: (fun x :e X => hk (i0 x)) = h.
    assume Hhkk: (fun y :e Y => hk (i1 y)) = k.
    prove hk = comb W h k.
    transitivity (fun z :e Z => hk z).
    * symmetry. exact Pi_eta Z (fun _ => W) hk Hhk.
    * { prove (fun z :e Z => hk z) = (fun z :e X :+: Y => combine_funcs X Y (fun x => h x) (fun y => k y) z).
        apply lam_ext.
        let z. assume Hz.
        prove hk z = combine_funcs X Y (fun x => h x) (fun y => k y) z.
        apply setsum_Inj_inv X Y z Hz.
        - assume H1. apply H1. let x. assume H2. apply H2.
          assume Hx: x :e X.
          assume H2: z = Inj0 x.
          rewrite H2.
          prove hk (Inj0 x) = combine_funcs X Y (fun x => h x) (fun y => k y) (Inj0 x).
	  rewrite combine_funcs_eq1.
          prove hk (Inj0 x) = h x.
	  rewrite <- Hhkh. rewrite beta X (fun x => hk (i0 x)) x Hx.
          prove hk (Inj0 x) = hk (i0 x).
	  f_equal.
	  prove Inj0 x = (fun x :e X => Inj0 x) x.
	  rewrite beta X Inj0 x Hx. reflexivity.
        - assume H1. apply H1. let y. assume H2. apply H2.
          assume Hy: y :e Y.
          assume H2: z = Inj1 y.
          rewrite H2.
          prove hk (Inj1 y) = combine_funcs X Y (fun x => h x) (fun y => k y) (Inj1 y).
	  rewrite combine_funcs_eq2.
          prove hk (Inj1 y) = k y.
	  rewrite <- Hhkk. rewrite beta Y (fun y => hk (i1 y)) y Hy.
          prove hk (Inj1 y) = hk (i1 y).
	  f_equal.
	  prove Inj1 y = (fun y :e Y => Inj1 y) y.
	  rewrite beta Y Inj1 y Hy. reflexivity.
      }  
Qed.

Theorem MetaCatSet_coproduct : exists coprod:set -> set -> set,
  exists i0 i1:set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set,
  coproduct_constr_p (fun _ => True) SetHom
  (fun X => fun x :e X => x) (fun X Y Z f g => (fun x :e X => f (g x))) coprod i0 i1 copair.
claim L1: forall X, True -> forall Y, True -> True.
{ exact (fun _ _ _ _ => TrueI). }
exact MetaCatSet_coproduct_gen (fun _ => True) L1.
Qed.

Theorem MetaCatSet_product_gen : forall Obj:set -> prop,
  (forall X, Obj X -> forall Y, Obj Y -> Obj (setprod X Y))
  ->
  exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  product_constr_p Obj SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) prod pi0 pi1 pair.
let Obj.
assume HO: forall X, Obj X -> forall Y, Obj Y -> Obj (X :*: Y).
witness setprod.
witness (fun X Y => (fun z :e X :*: Y => z 0)).
witness (fun X Y => (fun z :e X :*: Y => z 1)).
witness (fun X Y W h k => (fun w :e W => (h w,k w))).
let X Y.
assume HX: Obj X.
assume HY: Obj Y.
set Z := X :*: Y.
set pi0 := (fun z :e Z => z 0).
set pi1 := (fun z :e Z => z 1).
set pair := fun W:set => fun h k:set => (fun w :e W => (h w,k w)).
prove product_p Obj SetHom (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) X Y Z pi0 pi1 pair.
prove Obj X
   /\ Obj Y
   /\ Obj Z
   /\ SetHom Z X pi0
   /\ SetHom Z Y pi1
   /\ forall W, Obj W -> forall h k:set, SetHom W X h -> SetHom W Y k ->
              SetHom W Z (pair W h k)
           /\ (fun w :e W => pi0 (pair W h k w)) = h
           /\ (fun w :e W => pi1 (pair W h k w)) = k
           /\ forall u:set, SetHom W Z u
               -> (fun w :e W => pi0 (u w)) = h
               -> (fun w :e W => pi1 (u w)) = k
               -> u = pair W h k.
apply and6I.
- exact HX.
- exact HY.
- exact HO X HX Y HY.
- prove SetHom Z X pi0.
  prove pi0 :e Pi_ z :e Z, X.
  apply lam_Pi.
  exact ap0_Sigma X (fun _ => Y).
- prove SetHom Z Y pi1.
  prove pi1 :e Pi_ z :e Z, Y.
  apply lam_Pi.
  exact ap1_Sigma X (fun _ => Y).
- let W. assume HW: Obj W.
  let h k.
  assume Hh: SetHom W X h.
  assume Hk: SetHom W Y k.
  claim L1: forall w :e W, (h w,k w) :e Z.
  { let w. assume Hw: w :e W.
    prove (h w,k w) :e X :*: Y.
    apply tuple_2_setprod.
    - exact ap_Pi W (fun _ => X) h w Hh Hw.
    - exact ap_Pi W (fun _ => Y) k w Hk Hw.
  }
  claim L2: (fun w :e W => (h w,k w)) :e Pi_ w :e W, Z.
  { prove (fun w :e W => (h w,k w)) :e Pi_ w :e W, Z.
    apply lam_Pi.
    exact L1.
  }
  prove SetHom W Z (pair W h k)
     /\ (fun w :e W => pi0 (pair W h k w)) = h
     /\ (fun w :e W => pi1 (pair W h k w)) = k
     /\ forall u:set, SetHom W Z u
                  -> (fun w :e W => pi0 (u w)) = h
                  -> (fun w :e W => pi1 (u w)) = k
                  -> u = pair W h k.
  apply and4I.
  + prove SetHom W Z (pair W h k). exact L2.
  + prove (fun w :e W => pi0 (pair W h k w)) = h.
    transitivity (fun w :e W => h w).
    * apply lam_ext.
      let w. assume Hw.
      prove pi0 ((fun w :e W => (h w,k w)) w) = h w.
      rewrite beta W (fun w => (h w,k w)) w Hw.
      prove (fun z :e Z => z 0) (h w,k w) = h w.
      rewrite beta Z (fun z => z 0) (h w,k w) (L1 w Hw).
      prove (h w,k w) 0 = h w.
      apply tuple_2_0_eq.
    * prove (fun w :e W => h w) = h.
      exact Pi_eta W (fun _ => X) h Hh.
  + prove (fun w :e W => pi1 (pair W h k w)) = k.
    transitivity (fun w :e W => k w).
    * apply lam_ext.
      let w. assume Hw.
      prove pi1 ((fun w :e W => (h w,k w)) w) = k w.
      rewrite beta W (fun w => (h w,k w)) w Hw.
      prove (fun z :e Z => z 1) (h w,k w) = k w.
      rewrite beta Z (fun z => z 1) (h w,k w) (L1 w Hw).
      prove (h w,k w) 1 = k w.
      apply tuple_2_1_eq.
    * prove (fun w :e W => k w) = k.
      exact Pi_eta W (fun _ => Y) k Hk.
  + let u.
    assume Hu: SetHom W Z u.
    assume Huh: (fun w :e W => pi0 (u w)) = h.
    assume Huk: (fun w :e W => pi1 (u w)) = k.
    prove u = pair W h k.
    transitivity (fun w :e W => u w).
    * symmetry. exact Pi_eta W (fun _ => Z) u Hu.
    * prove (fun w :e W => u w) = (fun w :e W => (h w,k w)).
      apply lam_ext.
      let w. assume Hw.
      prove u w = (h w,k w).
      claim L3: u w :e Z.
      { exact ap_Pi W (fun _ => Z) u w Hu Hw. }
      rewrite <- tuple_Sigma_eta X (fun _ => Y) (u w) L3.
      prove (u w 0,u w 1) = (h w,k w).
      claim L4: u w 0 = h w.
      { rewrite <- Huh.
        prove u w 0 = (fun w :e W => pi0 (u w)) w.
	transitivity pi0 (u w).
	- prove u w 0 = (fun z :e Z => z 0) (u w).
          symmetry. exact beta Z (fun z => z 0) (u w) L3.
	- symmetry. exact beta W (fun w => pi0 (u w)) w Hw.
      }
      claim L5: u w 1 = k w.
      { rewrite <- Huk.
        prove u w 1 = (fun w :e W => pi1 (u w)) w.
	transitivity pi1 (u w).
	- prove u w 1 = (fun z :e Z => z 1) (u w).
          symmetry. exact beta Z (fun z => z 1) (u w) L3.
	- symmetry. exact beta W (fun w => pi1 (u w)) w Hw.
      }
      rewrite L4. rewrite L5.
      reflexivity.
Qed.

Theorem MetaCatSet_product : exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  product_constr_p (fun _ => True) SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) prod pi0 pi1 pair.
claim L1: forall X, True -> forall Y, True -> True.
{ exact (fun _ _ _ _ => TrueI). }
exact MetaCatSet_product_gen (fun _ => True) L1.
Qed.

Theorem UnivOf_Subq_closed : forall N, forall X :e UnivOf N, forall Q c= X, Q :e UnivOf N.
let N X. assume HX: X :e UnivOf N. let Q. assume HQ: Q c= X.
claim LZ: ZF_closed (UnivOf N).
{ exact UnivOf_ZF_closed N. }
claim LQ: Q :e Power X.
{ exact PowerI X Q HQ. }
exact UnivOf_TransSet N (Power X) (ZF_Power_closed (UnivOf N) LZ X HX) Q LQ.
Qed.

Definition famunion_closed : set->prop := fun U:set => forall X :e U, forall F:set->set, (forall x :e X, F x :e U) -> famunion X F :e U.

Theorem Union_Repl_famunion_closed : forall U:set, Union_closed U -> Repl_closed U -> famunion_closed U.
let U.
assume HU: Union_closed U.
assume HR: Repl_closed U.
let X.
assume HX: X :e U.
let F.
assume HF: forall x :e X, F x :e U.
prove famunion X F :e U.
prove Union {F x|x :e X} :e U.
apply HU.
prove {F x|x :e X} :e U.
exact HR X HX F HF.
Qed.

Theorem ZF_closed_0 : forall U X, TransSet U -> ZF_closed U -> X :e U -> 0 :e U.
let U X. assume H1 H2 H3.
apply ZF_closed_E U H2.
assume HU HP HR.
claim L1: Power X :e U.
{ apply HP. exact H3. }
apply H1 (Power X) L1 0.
prove 0 :e Power X. apply Empty_In_Power.
Qed.

Theorem ZF_Inj1_closed : forall U, TransSet U -> ZF_closed U -> forall X :e U, Inj1 X :e U.
let U.
assume HUT: TransSet U.
assume HU: ZF_closed U.
apply In_ind.
let X.
assume IH: forall x :e X, x :e U -> Inj1 x :e U.
assume HX: X :e U.
rewrite Inj1_eq.
prove ({Empty} :\/: {Inj1 x|x :e X}) :e U.
apply ZF_binunion_closed U HU.
- apply ZF_Sing_closed U HU.
  apply HUT (Power X) (ZF_Power_closed U HU X HX) Empty (Empty_In_Power X).
- apply ZF_Repl_closed U HU X HX.
  let x. assume Hx: x :e X.
  apply IH x Hx.
  prove x :e U.
  exact HUT X HX x Hx.
Qed.

Theorem ZF_Inj0_closed : forall U, TransSet U -> ZF_closed U -> forall X :e U, Inj0 X :e U.
let U.
assume HUT: TransSet U.
assume HU: ZF_closed U.
let X. assume HX: X :e U.
prove {Inj1 x|x :e X} :e U.
apply ZF_Repl_closed U HU X HX.
let x. assume Hx: x :e X.
apply ZF_Inj1_closed U HUT HU x.
prove x :e U.
exact HUT X HX x Hx.
Qed.

Theorem ZF_setsum_closed : forall U, TransSet U -> ZF_closed U ->
  forall X Y :e U, (X :+: Y) :e U.
let U. 
assume HUT: TransSet U.
assume HU: ZF_closed U.
let X. assume HX: X :e U.
let Y. assume HY: Y :e U.
prove ({Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}) :e U.
apply ZF_binunion_closed U HU.
- prove {Inj0 x|x :e X} :e U.
  apply ZF_Repl_closed U HU X HX Inj0.
  let x. assume Hx: x :e X.
  prove Inj0 x :e U.
  apply ZF_Inj0_closed U HUT HU x.
  prove x :e U.
  exact HUT X HX x Hx.
- apply ZF_Repl_closed U HU Y HY Inj1.
  let y. assume Hy: y :e Y.
  prove Inj1 y :e U.
  apply ZF_Inj1_closed U HUT HU y.
  prove y :e U.
  exact HUT Y HY y Hy.
Qed.

Theorem ZF_Sigma_closed : forall U, TransSet U -> ZF_closed U
  ->
  forall X :e U, forall Y:set->set, (forall x :e X, Y x :e U) -> (Sigma_ x :e X, Y x) :e U.
let U.
assume HUT: TransSet U.
assume HU: ZF_closed U.
apply ZF_closed_E U HU.
assume HUU HUP HUR.
let X. assume HX: X :e U.
let Y. assume HY: forall x :e X, Y x :e U.
prove (\/_ x :e X, {setsum x y|y :e Y x}) :e U.
claim L1: famunion_closed U.
{ apply Union_Repl_famunion_closed.
  - exact HUU.
  - exact HUR.
}
apply L1 X HX (fun x => {setsum x y|y :e Y x}).
let x. assume Hx: x :e X.
prove {setsum x y|y :e Y x} :e U.
apply HUR (Y x) (HY x Hx) (fun y => setsum x y).
let y. assume Hy: y :e Y x.
prove setsum x y :e U.
apply ZF_setsum_closed U HUT HU.
- prove x :e U. exact HUT X HX x Hx.
- prove y :e U. exact HUT (Y x) (HY x Hx) y Hy.
Qed.

Theorem ZF_setprod_closed : forall U, TransSet U -> ZF_closed U ->
  forall X Y :e U, (X :*: Y) :e U.
let U. assume HUT HU.
let X. assume HX.
let Y. assume HY.
exact ZF_Sigma_closed U HUT HU X HX (fun _ => Y) (fun _ _ => HY).
Qed.

Theorem ZF_Pi_closed : forall U, TransSet U -> ZF_closed U
  ->
  forall X :e U, forall Y:set->set, (forall x :e X, Y x :e U) -> (Pi_ x :e X, Y x) :e U.
let U.
assume HUT: TransSet U.
assume HU: ZF_closed U.
apply ZF_closed_E U HU.
assume HUU HUP HUR.
let X. assume HX: X :e U.
let Y. assume HY: forall x :e X, Y x :e U.
prove (Pi_ x :e X, Y x) :e U.
claim L1: (Pi_ x :e X, Y x) :e Power (Power (Sigma_ x :e X, Union (Y x))).
{ exact Sep_In_Power (Power (Sigma_ x :e X, Union (Y x))) (fun f => forall x :e X, f x :e Y x). }
claim L2: (Power (Power (Sigma_ x :e X, Union (Y x)))) :e U.
{ apply HUP. apply HUP.
  apply ZF_Sigma_closed U HUT HU X HX (fun x => Union (Y x)).
  let x. assume Hx: x :e X.
  prove Union (Y x) :e U.
  apply HUU. exact HY x Hx.
}
exact HUT (Power (Power (Sigma_ x :e X, Union (Y x)))) L2 (Pi_ x :e X, Y x) L1.
Qed.

Theorem ZF_setexp_closed : forall U, TransSet U -> ZF_closed U ->
  forall X Y :e U, (Y :^: X) :e U.
let U. assume HUT HU.
let X. assume HX.
let Y. assume HY.
exact ZF_Pi_closed U HUT HU X HX (fun _ => Y) (fun x Hx => HY).
Qed.

Theorem MetaCatHFSet_initial : exists Y:set, exists uniqa:set -> set,
  initial_p (fun X => X :e UnivOf Empty) SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) Y uniqa.
exact MetaCatSet_initial_gen (fun X => X :e UnivOf Empty) (UnivOf_In Empty).
Qed.

Theorem MetaCatSmallSet_initial : exists Y:set, exists uniqa:set -> set,
  initial_p (fun X => X :e UnivOf (UnivOf Empty)) SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) Y uniqa.
claim L1: 0 :e UnivOf (UnivOf Empty).
{ exact ZF_closed_0 (UnivOf (UnivOf Empty)) (UnivOf Empty) (UnivOf_TransSet (UnivOf Empty)) (UnivOf_ZF_closed (UnivOf Empty)) (UnivOf_In (UnivOf Empty)). }
exact MetaCatSet_initial_gen (fun X => X :e UnivOf (UnivOf Empty)) L1.
Qed.

Theorem MetaCatHFSet_terminal : exists Y:set, exists uniqa:set -> set,
  terminal_p (fun X => X :e UnivOf Empty) SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) Y uniqa.
claim L1: 1 :e UnivOf Empty.
{ apply ZF_ordsucc_closed.
  - exact UnivOf_ZF_closed Empty.
  - exact ZF_closed_0 (UnivOf Empty) Empty (UnivOf_TransSet Empty) (UnivOf_ZF_closed Empty) (UnivOf_In Empty).
}
exact MetaCatSet_terminal_gen (fun X => X :e UnivOf Empty) L1.
Qed.

Theorem MetaCatSmallSet_terminal : exists Y:set, exists uniqa:set -> set,
  terminal_p (fun X => X :e UnivOf (UnivOf Empty)) SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) Y uniqa.
claim L1: 1 :e UnivOf (UnivOf Empty).
{ apply ZF_ordsucc_closed.
  - exact UnivOf_ZF_closed (UnivOf Empty).
  - exact ZF_closed_0 (UnivOf (UnivOf Empty)) (UnivOf Empty) (UnivOf_TransSet (UnivOf Empty)) (UnivOf_ZF_closed (UnivOf Empty)) (UnivOf_In (UnivOf Empty)).
}
exact MetaCatSet_terminal_gen (fun X => X :e UnivOf (UnivOf Empty)) L1.
Qed.

Theorem MetaCatHFSet_coproduct : exists coprod:set -> set -> set,
  exists i0 i1:set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set,
  coproduct_constr_p (fun X => X :e UnivOf Empty) SetHom
  (fun X => fun x :e X => x) (fun X Y Z f g => (fun x :e X => f (g x))) coprod i0 i1 copair.
claim L1: forall X Y :e UnivOf Empty, X :+: Y :e UnivOf Empty.
{ exact ZF_setsum_closed (UnivOf Empty) (UnivOf_TransSet Empty) (UnivOf_ZF_closed Empty). }
exact MetaCatSet_coproduct_gen (fun X => X :e UnivOf Empty) L1.
Qed.

Theorem MetaCatSmallSet_coproduct : exists coprod:set -> set -> set,
  exists i0 i1:set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set,
  coproduct_constr_p (fun X => X :e UnivOf (UnivOf Empty)) SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) coprod i0 i1 copair.
claim L1: forall X Y :e UnivOf (UnivOf Empty), X :+: Y :e UnivOf (UnivOf Empty).
{ exact ZF_setsum_closed (UnivOf (UnivOf Empty)) (UnivOf_TransSet (UnivOf Empty)) (UnivOf_ZF_closed (UnivOf Empty)). }
exact MetaCatSet_coproduct_gen (fun X => X :e UnivOf (UnivOf Empty)) L1.
Qed.

Theorem MetaCatHFSet_product : exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  product_constr_p (fun X => X :e UnivOf Empty) SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) prod pi0 pi1 pair.
claim L1: forall X Y :e UnivOf Empty, X :*: Y :e UnivOf Empty.
{ exact ZF_setprod_closed (UnivOf Empty) (UnivOf_TransSet Empty) (UnivOf_ZF_closed Empty). }
exact MetaCatSet_product_gen (fun X => X :e UnivOf Empty) L1.
Qed.

Theorem MetaCatSmallSet_product : exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  product_constr_p (fun X => X :e UnivOf (UnivOf Empty)) SetHom
  (fun X => (fun x :e X => x)) (fun X Y Z f g => (fun x :e X => f (g x))) prod pi0 pi1 pair.
claim L1: forall X Y :e UnivOf (UnivOf Empty), X :*: Y :e UnivOf (UnivOf Empty).
{ exact ZF_setprod_closed (UnivOf (UnivOf Empty)) (UnivOf_TransSet (UnivOf Empty)) (UnivOf_ZF_closed (UnivOf Empty)). }
exact MetaCatSet_product_gen (fun X => X :e UnivOf (UnivOf Empty)) L1.
Qed.

Section MetaFunctor.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.
Variable Obj': set -> prop.
Variable Hom': set -> set -> set -> prop.
Variable id': set -> set.
Variable comp': set -> set -> set -> set -> set -> set.

Variable F0:set -> set.
Variable F1:set -> set -> set -> set.

Definition MetaFunctor : prop :=
     (forall X, Obj X -> Obj' (F0 X))
  /\ (forall X Y f, Obj X -> Obj Y -> Hom X Y f -> Hom' (F0 X) (F0 Y) (F1 X Y f))
  /\ (forall X, Obj X -> F1 X X (id X) = id' (F0 X))
  /\ (forall X Y Z f g, Obj X -> Obj Y -> Obj Z -> Hom X Y f -> Hom Y Z g -> F1 X Z (comp X Y Z g f) = comp' (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f)).

Theorem MetaFunctorI: 
     (forall X, Obj X -> Obj' (F0 X))
  -> (forall X Y f, Obj X -> Obj Y -> Hom X Y f -> Hom' (F0 X) (F0 Y) (F1 X Y f))
  -> (forall X, Obj X -> F1 X X (id X) = id' (F0 X))
  -> (forall X Y Z f g, Obj X -> Obj Y -> Obj Z -> Hom X Y f -> Hom Y Z g -> F1 X Z (comp X Y Z g f) = comp' (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f))
  -> MetaFunctor.
exact and4I (forall X, Obj X -> Obj' (F0 X))
            (forall X Y f, Obj X -> Obj Y -> Hom X Y f -> Hom' (F0 X) (F0 Y) (F1 X Y f))
            (forall X, Obj X -> F1 X X (id X) = id' (F0 X))
            (forall X Y Z f g, Obj X -> Obj Y -> Obj Z -> Hom X Y f -> Hom Y Z g -> F1 X Z (comp X Y Z g f) = comp' (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f)).
Qed.

Theorem MetaFunctorE: MetaFunctor ->
 forall p:prop,
     ((forall X, Obj X -> Obj' (F0 X))
   -> (forall X Y f, Obj X -> Obj Y -> Hom X Y f -> Hom' (F0 X) (F0 Y) (F1 X Y f))
   -> (forall X, Obj X -> F1 X X (id X) = id' (F0 X))
   -> (forall X Y Z f g, Obj X -> Obj Y -> Obj Z -> Hom X Y f -> Hom Y Z g -> F1 X Z (comp X Y Z g f) = comp' (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f))
   -> p)
  -> p.
exact and4E (forall X, Obj X -> Obj' (F0 X))
            (forall X Y f, Obj X -> Obj Y -> Hom X Y f -> Hom' (F0 X) (F0 Y) (F1 X Y f))
            (forall X, Obj X -> F1 X X (id X) = id' (F0 X))
            (forall X Y Z f g, Obj X -> Obj Y -> Obj Z -> Hom X Y f -> Hom Y Z g -> F1 X Z (comp X Y Z g f) = comp' (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f)).
Qed.
  
Definition MetaFunctor_strict : prop := MetaCat Obj Hom id comp /\ MetaCat Obj' Hom' id' comp' /\ MetaFunctor.

Theorem MetaFunctor_strict_I :
    MetaCat Obj Hom id comp
 -> MetaCat Obj' Hom' id' comp'
 -> MetaFunctor
 -> MetaFunctor_strict.
exact and3I (MetaCat Obj Hom id comp) (MetaCat Obj' Hom' id' comp') MetaFunctor.
Qed.

Theorem MetaFunctor_strict_E : MetaFunctor_strict ->
 forall p:prop,
    (MetaCat Obj Hom id comp
  -> MetaCat Obj' Hom' id' comp'
  -> MetaFunctor
  -> p)
 -> p.
exact and3E (MetaCat Obj Hom id comp) (MetaCat Obj' Hom' id' comp') MetaFunctor.
Qed.

End MetaFunctor.

Section IdFunctor.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Theorem MetaCat_IdFunctor : MetaFunctor Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f).
apply MetaFunctorI.
- let X. assume HX. exact HX.
- let X Y f. assume HX HY Hf. exact Hf.
- let X. assume HX. reflexivity.
- let X Y Z f g. assume HX HY HZ Hf Hg. reflexivity.
Qed.

Theorem MetaCat_IdFunctor_strict : MetaCat Obj Hom id comp
 -> MetaFunctor_strict Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f).
assume HC.
apply MetaFunctor_strict_I.
- exact HC.
- exact HC.
- exact MetaCat_IdFunctor.
Qed.

End IdFunctor.

Section CompFunctors.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.
Variable Obj': set -> prop.
Variable Hom': set -> set -> set -> prop.
Variable id': set -> set.
Variable comp': set -> set -> set -> set -> set -> set.
Variable Obj'': set -> prop.
Variable Hom'': set -> set -> set -> prop.
Variable id'': set -> set.
Variable comp'': set -> set -> set -> set -> set -> set.
Variable F0: set -> set.
Variable F1: set -> set -> set -> set.
Variable G0: set -> set.
Variable G1: set -> set -> set -> set.

Theorem MetaCat_CompFunctors :
    MetaFunctor Obj Hom id comp Obj' Hom' id' comp' F0 F1
 -> MetaFunctor Obj' Hom' id' comp' Obj'' Hom'' id'' comp'' G0 G1
 -> MetaFunctor Obj Hom id comp Obj'' Hom'' id'' comp'' (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)).
assume HF HG.
apply MetaFunctorE Obj Hom id comp Obj' Hom' id' comp' F0 F1 HF.
assume HF1 HF2 HF3 HF4.
apply MetaFunctorE Obj' Hom' id' comp' Obj'' Hom'' id'' comp'' G0 G1 HG.
assume HG1 HG2 HG3 HG4.
apply MetaFunctorI.
- let X. assume HX. prove Obj'' (G0 (F0 X)). apply HG1. apply HF1. exact HX.
- let X Y f. assume HX HY Hf.
  prove Hom'' (G0 (F0 X)) (G0 (F0 Y)) (G1 (F0 X) (F0 Y) (F1 X Y f)).
  apply HG2.
  + apply HF1. exact HX.
  + apply HF1. exact HY.
  + apply HF2.
    * exact HX.
    * exact HY.
    * exact Hf.
- let X. assume HX.
  prove G1 (F0 X) (F0 X) (F1 X X (id X)) = id'' (G0 (F0 X)).
  transitivity G1 (F0 X) (F0 X) (id' (F0 X)).
  + f_equal. exact HF3 X HX.
  + exact HG3 (F0 X) (HF1 X HX).
- let X Y Z f g. assume HX HY HZ Hf Hg.
  prove G1 (F0 X) (F0 Z) (F1 X Z (comp X Y Z g f))
      = comp'' (G0 (F0 X)) (G0 (F0 Y)) (G0 (F0 Z)) (G1 (F0 Y) (F0 Z) (F1 Y Z g)) (G1 (F0 X) (F0 Y) (F1 X Y f)).
  transitivity G1 (F0 X) (F0 Z) (comp' (F0 X) (F0 Y) (F0 Z) (F1 Y Z g) (F1 X Y f)).
  + f_equal. exact HF4 X Y Z f g HX HY HZ Hf Hg.
  + apply HG4 (F0 X) (F0 Y) (F0 Z) (F1 X Y f) (F1 Y Z g) (HF1 X HX) (HF1 Y HY) (HF1 Z HZ).
    * exact HF2 X Y f HX HY Hf.
    * exact HF2 Y Z g HY HZ Hg.
Qed.

Theorem MetaCat_CompFunctors_strict :
    MetaFunctor_strict Obj Hom id comp Obj' Hom' id' comp' F0 F1
 -> MetaFunctor_strict Obj' Hom' id' comp' Obj'' Hom'' id'' comp'' G0 G1
 -> MetaFunctor_strict Obj Hom id comp Obj'' Hom'' id'' comp'' (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)).
assume HF HG.
apply MetaFunctor_strict_E Obj Hom id comp Obj' Hom' id' comp' F0 F1 HF.
assume HC _ HF.
apply MetaFunctor_strict_E Obj' Hom' id' comp' Obj'' Hom'' id'' comp'' G0 G1 HG.
assume _ HC'' HG.
apply MetaFunctor_strict_I.
- exact HC.
- exact HC''.
- apply MetaCat_CompFunctors.
  + exact HF.
  + exact HG.
Qed.

End CompFunctors.

Section MetaNatTrans.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.
Variable Obj': set -> prop.
Variable Hom': set -> set -> set -> prop.
Variable id': set -> set.
Variable comp': set -> set -> set -> set -> set -> set.

Variable F0:set -> set.
Variable F1:set -> set -> set -> set.
Variable G0:set -> set.
Variable G1:set -> set -> set -> set.

Variable eta:set -> set.

Definition MetaNatTrans : prop :=
    (forall X, Obj X -> Hom' (F0 X) (G0 X) (eta X))
 /\ (forall X Y f, Obj X -> Obj Y -> Hom X Y f
      -> comp' (F0 X) (G0 X) (G0 Y) (G1 X Y f) (eta X)
       = comp' (F0 X) (F0 Y) (G0 Y) (eta Y) (F1 X Y f)).

Theorem MetaNatTransI:
    (forall X, Obj X -> Hom' (F0 X) (G0 X) (eta X))
 -> (forall X Y f, Obj X -> Obj Y -> Hom X Y f
      -> comp' (F0 X) (G0 X) (G0 Y) (G1 X Y f) (eta X)
       = comp' (F0 X) (F0 Y) (G0 Y) (eta Y) (F1 X Y f))
 -> MetaNatTrans.
exact andI (forall X, Obj X -> Hom' (F0 X) (G0 X) (eta X))
           (forall X Y f, Obj X -> Obj Y -> Hom X Y f
             -> comp' (F0 X) (G0 X) (G0 Y) (G1 X Y f) (eta X)
              = comp' (F0 X) (F0 Y) (G0 Y) (eta Y) (F1 X Y f)).
Qed.

Theorem MetaNatTransE: MetaNatTrans ->
 forall p:prop,
    ((forall X, Obj X -> Hom' (F0 X) (G0 X) (eta X))
  -> (forall X Y f, Obj X -> Obj Y -> Hom X Y f
      -> comp' (F0 X) (G0 X) (G0 Y) (G1 X Y f) (eta X)
       = comp' (F0 X) (F0 Y) (G0 Y) (eta Y) (F1 X Y f))
  -> p)
 -> p.
assume H. exact H.
Qed.

Definition MetaNatTrans_strict : prop :=
    MetaCat Obj Hom id comp
 /\ MetaCat Obj' Hom' id' comp'
 /\ MetaFunctor Obj Hom id comp Obj' Hom' id' comp' F0 F1
 /\ MetaFunctor Obj Hom id comp Obj' Hom' id' comp' G0 G1
 /\ MetaNatTrans.

Theorem MetaNatTrans_strict_I: MetaCat Obj Hom id comp
   -> MetaCat Obj' Hom' id' comp'
   -> MetaFunctor Obj Hom id comp Obj' Hom' id' comp' F0 F1
   -> MetaFunctor Obj Hom id comp Obj' Hom' id' comp' G0 G1
   -> MetaNatTrans
   -> MetaNatTrans_strict.
exact and5I (MetaCat Obj Hom id comp)
            (MetaCat Obj' Hom' id' comp')
            (MetaFunctor Obj Hom id comp Obj' Hom' id' comp' F0 F1)
            (MetaFunctor Obj Hom id comp Obj' Hom' id' comp' G0 G1)
            MetaNatTrans.
Qed.

Theorem MetaNatTrans_strict_E: MetaNatTrans_strict ->
 forall p:prop,
     (MetaCat Obj Hom id comp
   -> MetaCat Obj' Hom' id' comp'
   -> MetaFunctor Obj Hom id comp Obj' Hom' id' comp' F0 F1
   -> MetaFunctor Obj Hom id comp Obj' Hom' id' comp' G0 G1
   -> MetaNatTrans
   -> p)
  -> p.
assume H.
exact and5E (MetaCat Obj Hom id comp)
            (MetaCat Obj' Hom' id' comp')
            (MetaFunctor Obj Hom id comp Obj' Hom' id' comp' F0 F1)
            (MetaFunctor Obj Hom id comp Obj' Hom' id' comp' G0 G1)
            MetaNatTrans H.
Qed.

End MetaNatTrans.

Section CompFunctorNatTrans.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.
Variable Obj': set -> prop.
Variable Hom': set -> set -> set -> prop.
Variable id': set -> set.
Variable comp': set -> set -> set -> set -> set -> set.
Variable Obj'': set -> prop.
Variable Hom'': set -> set -> set -> prop.
Variable id'': set -> set.
Variable comp'': set -> set -> set -> set -> set -> set.
Variable F0: set -> set.
Variable F1: set -> set -> set -> set.
Variable G0: set -> set.
Variable G1: set -> set -> set -> set.
Variable H0: set -> set.
Variable H1: set -> set -> set -> set.
Variable eta:set -> set.

(**
  F,G: C -> C'
  H: C' -> C''
  eta: F -> G
  HF: C -> C''
  HG: C -> C''
  H eta: HF -> HG
**)
Theorem MetaCat_CompFunctorNatTrans:
    MetaFunctor Obj Hom id comp Obj' Hom' id' comp' F0 F1
 -> MetaFunctor Obj Hom id comp Obj' Hom' id' comp' G0 G1
 -> MetaNatTrans Obj Hom id comp Obj' Hom' id' comp' F0 F1 G0 G1 eta
 -> MetaFunctor Obj' Hom' id' comp' Obj'' Hom'' id'' comp'' H0 H1
 -> MetaNatTrans Obj Hom id comp Obj'' Hom'' id'' comp''
                 (fun X => H0 (F0 X))
		 (fun X Y f => H1 (F0 X) (F0 Y) (F1 X Y f))
                 (fun X => H0 (G0 X))
		 (fun X Y f => H1 (G0 X) (G0 Y) (G1 X Y f))
                 (fun X => H1 (F0 X) (G0 X) (eta X)).
assume HF HG Heta HH.
apply MetaFunctorE Obj Hom id comp Obj' Hom' id' comp' F0 F1 HF.
assume HF1 HF2 HF3 HF4.
apply MetaFunctorE Obj Hom id comp Obj' Hom' id' comp' G0 G1 HG.
assume HG1 HG2 HG3 HG4.
apply MetaNatTransE Obj Hom id comp Obj' Hom' id' comp' F0 F1 G0 G1 eta Heta.
assume Heta1 Heta2.
apply MetaFunctorE Obj' Hom' id' comp' Obj'' Hom'' id'' comp'' H0 H1 HH.
assume HH1 HH2 HH3 HH4.
apply MetaNatTransI.
- let X. assume HX. prove Hom'' (H0 (F0 X)) (H0 (G0 X)) (H1 (F0 X) (G0 X) (eta X)).
  apply HH2.
  + prove Obj' (F0 X). apply HF1. exact HX.
  + prove Obj' (G0 X). apply HG1. exact HX.
  + prove Hom' (F0 X) (G0 X) (eta X). apply Heta1. exact HX.
- let X Y f. assume HX HY Hf.
  prove comp'' (H0 (F0 X)) (H0 (G0 X)) (H0 (G0 Y)) (H1 (G0 X) (G0 Y) (G1 X Y f)) (H1 (F0 X) (G0 X) (eta X))
      = comp'' (H0 (F0 X)) (H0 (F0 Y)) (H0 (G0 Y)) (H1 (F0 Y) (G0 Y) (eta Y)) (H1 (F0 X) (F0 Y) (F1 X Y f)).
  transitivity H1 (F0 X) (G0 Y) (comp' (F0 X) (G0 X) (G0 Y) (G1 X Y f) (eta X)),
               H1 (F0 X) (G0 Y) (comp' (F0 X) (F0 Y) (G0 Y) (eta Y) (F1 X Y f)).
  + symmetry. apply HH4.
    * apply HF1. exact HX.
    * apply HG1. exact HX.
    * apply HG1. exact HY.
    * exact Heta1 X HX.
    * exact HG2 X Y f HX HY Hf.
  + f_equal. exact Heta2 X Y f HX HY Hf.
  + apply HH4.
    * apply HF1. exact HX.
    * apply HF1. exact HY.
    * apply HG1. exact HY.
    * exact HF2 X Y f HX HY Hf.
    * exact Heta1 Y HY.
Qed.

End CompFunctorNatTrans.

Section CompNatTransFunctor.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.
Variable Obj': set -> prop.
Variable Hom': set -> set -> set -> prop.
Variable id': set -> set.
Variable comp': set -> set -> set -> set -> set -> set.
Variable Obj'': set -> prop.
Variable Hom'': set -> set -> set -> prop.
Variable id'': set -> set.
Variable comp'': set -> set -> set -> set -> set -> set.
Variable F0: set -> set.
Variable F1: set -> set -> set -> set.
Variable G0: set -> set.
Variable G1: set -> set -> set -> set.
Variable H0: set -> set.
Variable H1: set -> set -> set -> set.
Variable eta:set -> set.

(**
  H: C -> C'
  F,G: C' -> C''
  eta: F -> G
  FH: C -> C''
  GH: C -> C''
  eta H: FH -> GH
**)
Theorem MetaCat_CompNatTransFunctor:
    MetaNatTrans Obj' Hom' id' comp' Obj'' Hom'' id'' comp'' F0 F1 G0 G1 eta
 -> MetaFunctor Obj Hom id comp Obj' Hom' id' comp' H0 H1
 -> MetaNatTrans Obj Hom id comp Obj'' Hom'' id'' comp''
                 (fun X => F0 (H0 X))
		 (fun X Y f => F1 (H0 X) (H0 Y) (H1 X Y f))
                 (fun X => G0 (H0 X))
		 (fun X Y f => G1 (H0 X) (H0 Y) (H1 X Y f))
                 (fun X => eta (H0 X)).
assume Heta HH.
apply MetaNatTransE Obj' Hom' id' comp' Obj'' Hom'' id'' comp'' F0 F1 G0 G1 eta Heta.
assume Heta1 Heta2.
apply MetaFunctorE Obj Hom id comp Obj' Hom' id' comp' H0 H1 HH.
assume HH1 HH2 HH3 HH4.
apply MetaNatTransI.
- let X. assume HX. prove Hom'' (F0 (H0 X)) (G0 (H0 X)) (eta (H0 X)).
  apply Heta1.
  prove Obj' (H0 X). apply HH1. exact HX.
- let X Y f. assume HX HY Hf.
  prove comp'' (F0 (H0 X)) (G0 (H0 X)) (G0 (H0 Y)) (G1 (H0 X) (H0 Y) (H1 X Y f)) (eta (H0 X))
      = comp'' (F0 (H0 X)) (F0 (H0 Y)) (G0 (H0 Y)) (eta (H0 Y)) (F1 (H0 X) (H0 Y) (H1 X Y f)).
  apply Heta2 (H0 X) (H0 Y) (H1 X Y f).
  + apply HH1. exact HX.
  + apply HH1. exact HY.
  + apply HH2.
    * exact HX.
    * exact HY.
    * exact Hf.
Qed.

End CompNatTransFunctor.

Section MetaMonad.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.

Variable T0: set -> set.
Variable T1: set -> set -> set -> set.
Variable eta: set -> set.
Variable mu: set -> set.

Definition MetaMonad : prop :=
    (forall X, Obj X -> comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (T1 (T0 (T0 X)) (T0 X) (mu X))  = comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (mu (T0 X))) 
 /\ (forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (eta (T0 X)) = id (T0 X)) 
 /\ (forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (T1 X (T0 X) (eta X)) = id (T0 X)).
  
Definition MetaMonad_strict : prop :=
    MetaNatTrans_strict Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) T0 T1 eta 
 /\ MetaNatTrans_strict Obj Hom id comp Obj Hom id comp (fun X => T0 (T0 X)) (fun X Y f => T1 (T0 X) (T0 Y) (T1 X Y f)) T0 T1 mu 
 /\ MetaMonad.

Theorem MetaMonadI:
    (forall X, Obj X -> comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (T1 (T0 (T0 X)) (T0 X) (mu X)) = comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (mu (T0 X)))
 -> (forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (eta (T0 X)) = id (T0 X))
 -> (forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (T1 X (T0 X) (eta X)) = id (T0 X))
 -> MetaMonad.
exact and3I (forall X, Obj X -> comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (T1 (T0 (T0 X)) (T0 X) (mu X)) = comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (mu (T0 X)))
            (forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (eta (T0 X)) = id (T0 X))
	    (forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (T1 X (T0 X) (eta X)) = id (T0 X)).
Qed.

Theorem MetaMonadE: MetaMonad ->
 (forall p:prop,
     ((forall X, Obj X -> comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (T1 (T0 (T0 X)) (T0 X) (mu X)) = comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (mu (T0 X)))
   -> (forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (eta (T0 X)) = id (T0 X))
   -> (forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (T1 X (T0 X) (eta X)) = id (T0 X))
   -> p)
  -> p).
exact and3E (forall X, Obj X -> comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (T1 (T0 (T0 X)) (T0 X) (mu X)) = comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (mu (T0 X)))
            (forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (eta (T0 X)) = id (T0 X))
	    (forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (T1 X (T0 X) (eta X)) = id (T0 X)).
Qed.

Theorem MetaMonad_strict_I:
    MetaNatTrans_strict Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) T0 T1 eta
 -> MetaNatTrans_strict Obj Hom id comp Obj Hom id comp (fun X => T0 (T0 X)) (fun X Y f => T1 (T0 X) (T0 Y) (T1 X Y f)) T0 T1 mu
 -> MetaMonad
 -> MetaMonad_strict.
exact and3I (MetaNatTrans_strict Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) T0 T1 eta)
            (MetaNatTrans_strict Obj Hom id comp Obj Hom id comp (fun X => T0 (T0 X)) (fun X Y f => T1 (T0 X) (T0 Y) (T1 X Y f)) T0 T1 mu)
            MetaMonad.
Qed.

Theorem MetaMonad_strict_E: MetaMonad_strict ->
 forall p:prop,
     (MetaNatTrans_strict Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) T0 T1 eta
   -> MetaNatTrans_strict Obj Hom id comp Obj Hom id comp (fun X => T0 (T0 X)) (fun X Y f => T1 (T0 X) (T0 Y) (T1 X Y f)) T0 T1 mu
   -> MetaMonad
   -> p)
  -> p.
exact and3E (MetaNatTrans_strict Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) T0 T1 eta)
           (MetaNatTrans_strict Obj Hom id comp Obj Hom id comp (fun X => T0 (T0 X)) (fun X Y f => T1 (T0 X) (T0 Y) (T1 X Y f)) T0 T1 mu)
	   MetaMonad.
Qed.

End MetaMonad.

Section MetaAdjunction.

Variable Obj: set -> prop.
Variable Hom: set -> set -> set -> prop.
Variable id: set -> set.
Variable comp: set -> set -> set -> set -> set -> set.
Variable Obj': set -> prop.
Variable Hom': set -> set -> set -> prop.
Variable id': set -> set.
Variable comp': set -> set -> set -> set -> set -> set.

Variable F0: set -> set.
Variable F1: set -> set -> set -> set.
Variable G0: set -> set.
Variable G1: set -> set -> set -> set.
Variable eta : set -> set.
Variable eps : set -> set.

Definition MetaAdjunction : prop :=
    (forall X, Obj X -> comp' (F0 X) (F0 (G0 (F0 X))) (F0 X) (eps (F0 X)) (F1 X (G0 (F0 X)) (eta X)) = id' (F0 X))
 /\ (forall Y, Obj' Y -> comp (G0 Y) (G0 (F0 (G0 Y))) (G0 Y) (G1 (F0 (G0 Y)) Y (eps Y)) (eta (G0 Y)) = id (G0 Y)).

Definition MetaAdjunction_strict : prop :=
    MetaFunctor_strict Obj Hom id comp Obj' Hom' id' comp' F0 F1 
 /\ MetaFunctor Obj' Hom' id' comp' Obj Hom id comp G0 G1 
 /\ MetaNatTrans Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)) eta 
 /\ MetaNatTrans Obj' Hom' id' comp' Obj' Hom' id' comp' (fun Y => F0 (G0 Y)) (fun X Y g => F1 (G0 X) (G0 Y) (G1 X Y g)) (fun Y => Y) (fun X Y g => g) eps 
 /\ MetaAdjunction.

Theorem MetaAdjunctionI: 
    (forall X, Obj X -> comp' (F0 X) (F0 (G0 (F0 X))) (F0 X) (eps (F0 X)) (F1 X (G0 (F0 X)) (eta X)) = id' (F0 X))
 -> (forall Y, Obj' Y -> comp (G0 Y) (G0 (F0 (G0 Y))) (G0 Y) (G1 (F0 (G0 Y)) Y (eps Y)) (eta (G0 Y)) = id (G0 Y))
 -> MetaAdjunction.
exact andI (forall X, Obj X -> comp' (F0 X) (F0 (G0 (F0 X))) (F0 X) (eps (F0 X)) (F1 X (G0 (F0 X)) (eta X)) = id' (F0 X))
           (forall Y, Obj' Y -> comp (G0 Y) (G0 (F0 (G0 Y))) (G0 Y) (G1 (F0 (G0 Y)) Y (eps Y)) (eta (G0 Y)) = id (G0 Y)).
Qed.

Theorem MetaAdjunctionE: MetaAdjunction ->
 forall p:prop,
      ((forall X, Obj X -> comp' (F0 X) (F0 (G0 (F0 X))) (F0 X) (eps (F0 X)) (F1 X (G0 (F0 X)) (eta X)) = id' (F0 X))
    -> (forall Y, Obj' Y -> comp (G0 Y) (G0 (F0 (G0 Y))) (G0 Y) (G1 (F0 (G0 Y)) Y (eps Y)) (eta (G0 Y)) = id (G0 Y))
    -> p)
   -> p.
exact (fun H => H).
Qed.

Theorem MetaAdjunction_strict_I:
    MetaFunctor_strict Obj Hom id comp Obj' Hom' id' comp' F0 F1
 -> MetaFunctor Obj' Hom' id' comp' Obj Hom id comp G0 G1
 -> MetaNatTrans Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)) eta
 -> MetaNatTrans Obj' Hom' id' comp' Obj' Hom' id' comp' (fun Y => F0 (G0 Y)) (fun X Y g => F1 (G0 X) (G0 Y) (G1 X Y g)) (fun Y => Y) (fun X Y g => g) eps
 -> MetaAdjunction
 -> MetaAdjunction_strict.
exact and5I (MetaFunctor_strict Obj Hom id comp Obj' Hom' id' comp' F0 F1)
            (MetaFunctor Obj' Hom' id' comp' Obj Hom id comp G0 G1)
            (MetaNatTrans Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)) eta)
            (MetaNatTrans Obj' Hom' id' comp' Obj' Hom' id' comp' (fun Y => F0 (G0 Y)) (fun X Y g => F1 (G0 X) (G0 Y) (G1 X Y g)) (fun Y => Y) (fun X Y g => g) eps)
            MetaAdjunction.
Qed.

Theorem MetaAdjunction_strict_E: MetaAdjunction_strict ->
 forall p:prop,
     (MetaFunctor_strict Obj Hom id comp Obj' Hom' id' comp' F0 F1
   -> MetaFunctor Obj' Hom' id' comp' Obj Hom id comp G0 G1
   -> MetaNatTrans Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)) eta
   -> MetaNatTrans Obj' Hom' id' comp' Obj' Hom' id' comp' (fun Y => F0 (G0 Y)) (fun X Y g => F1 (G0 X) (G0 Y) (G1 X Y g)) (fun Y => Y) (fun X Y g => g) eps
   -> MetaAdjunction
   -> p)
  -> p.
exact and5E (MetaFunctor_strict Obj Hom id comp Obj' Hom' id' comp' F0 F1)
            (MetaFunctor Obj' Hom' id' comp' Obj Hom id comp G0 G1)
            (MetaNatTrans Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)) eta)
            (MetaNatTrans Obj' Hom' id' comp' Obj' Hom' id' comp' (fun Y => F0 (G0 Y)) (fun X Y g => F1 (G0 X) (G0 Y) (G1 X Y g)) (fun Y => Y) (fun X Y g => g) eps)
            MetaAdjunction.
Qed.

(**
   F: C -> C'
   G: C' -> C
   eta: 1 -> GF
   eps: FG -> 1
   f o eps_X = eps_Y o FGf (Heps2)  f:X->Y, FGf:FGX->FGY, eps_X:FGX->X, eps_Y:FGY->Y
   eps_{F X} o F eta_X = id_{F X} (HA1)
   G eps_Y o eta_{G Y} = id_{G Y} (HA2)
   T: C -> C := GF
   mu: T^2 -> T := G eps F
   To prove:
   1. mu o T mu = mu o mu T
   2. mu o eta T = id
   3. mu o T eta = id

   eta: 1 -> T
   eta T: T -> T^2
   T eta : T -> T^2
   mu o T eta : T -> T

 eps_X : FGX -> X arrow in C' for X obj in C'
 eps_{FX} : FGFX -> FX arrow in C' for X obj in C
 eps_{FGFX} : FGFGFX -> FGFX arrow in C' for X obj in C

   f o eps_X = eps_Y o FGf (Heps2)  f:X->Y, FGf:FGX->FGY, eps_X:FGX->X, eps_Y:FGY->Y
 Let f := eps_{FX} : FGFX -> FX, X := FGFX, Y := FX.
 (Heps2') eps_{FX} o eps_{FGFX} = eps_{FX} o FG(eps_{FX})

 Proof of 1:
   mu_X o T(mu_X)
 = G(eps_{F X}) o GFG(eps_{F X})
 = G(eps_{F X} o FG(eps_{F X}))
 = G(eps_{F X} o eps_{FGF X}) by (Heps2')
 = G(eps_{F X}) o G(eps_{FGF X})
 = mu_X o mu_{T X}

 Proof of 2:
   mu_X o eta_{T X}
 = G(eps_{F X}) o eta_{GFX}
 = id_{F X} by (HA2)
 
 Proof of 3:
   mu_X o T(eta_X)
 = G(eps_{F X}) o GF(eta_X)
 = G(eps_{F X} o F(eta_X))
 = G(id_{F X}) by (HA1)
 = id_{T X}

 **)
Theorem MetaAdjunctionMonad:
    MetaFunctor Obj Hom id comp Obj' Hom' id' comp' F0 F1
 -> MetaFunctor Obj' Hom' id' comp' Obj Hom id comp G0 G1
 -> MetaNatTrans Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)) eta
 -> MetaNatTrans Obj' Hom' id' comp' Obj' Hom' id' comp' (fun Y => F0 (G0 Y)) (fun X Y g => F1 (G0 X) (G0 Y) (G1 X Y g)) (fun Y => Y) (fun X Y g => g) eps
 -> MetaAdjunction
 -> MetaMonad Obj Hom id comp (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)) eta (fun X => G1 (F0 (G0 (F0 X))) (F0 X) (eps (F0 X))).
assume HF.
apply MetaFunctorE Obj Hom id comp Obj' Hom' id' comp' F0 F1 HF.
assume HF1 HF2 HF3 HF4.
assume HG.
apply MetaFunctorE Obj' Hom' id' comp' Obj Hom id comp G0 G1 HG.
assume HG1 HG2 HG3 HG4.
assume Heta.
apply MetaNatTransE Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)) eta Heta.
assume Heta1 Heta2.
assume Heps.
apply MetaNatTransE Obj' Hom' id' comp' Obj' Hom' id' comp' (fun Y => F0 (G0 Y)) (fun X Y g => F1 (G0 X) (G0 Y) (G1 X Y g)) (fun Y => Y) (fun X Y g => g) eps Heps.
assume Heps1: forall X, Obj' X -> Hom' (F0 (G0 X)) X (eps X).
assume Heps2: forall X Y f, Obj' X -> Obj' Y -> Hom' X Y f -> comp' (F0 (G0 X)) X Y f (eps X) = comp' (F0 (G0 X)) (F0 (G0 Y)) Y (eps Y) (F1 (G0 X) (G0 Y) (G1 X Y f)).
assume HA.
apply MetaAdjunctionE HA.
assume HA1 HA2.
set T0 : set -> set := fun X => G0 (F0 X).
set T1 : set -> set -> set -> set := fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f).
set mu : set -> set := fun X => G1 (F0 (G0 (F0 X))) (F0 X) (eps (F0 X)).
claim LT: MetaFunctor Obj Hom id comp Obj Hom id comp T0 T1.
{ exact MetaCat_CompFunctors Obj Hom id comp Obj' Hom' id' comp' Obj Hom id comp F0 F1 G0 G1 HF HG. }
apply MetaFunctorE Obj Hom id comp Obj Hom id comp T0 T1 LT.
assume HT01 HT02 HT03 HT04.
apply MetaMonadI.
- prove forall X, Obj X -> comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (T1 (T0 (T0 X)) (T0 X) (mu X)) = comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (mu (T0 X)).
  let X. assume HX.
  claim LFX: Obj' (F0 X).
  { apply HF1. exact HX. }
  claim LTX: Obj (T0 X).
  { exact HT01 X HX. }
  claim LFTX: Obj' (F0 (T0 X)).
  { apply HF1. exact LTX. }
  claim LTTX: Obj (T0 (T0 X)).
  { exact HT01 (T0 X) LTX. }
  claim LFTTX: Obj' (F0 (T0 (T0 X))).
  { apply HF1. exact LTTX. }
  claim LepsFX: Hom' (F0 (T0 X)) (F0 X) (eps (F0 X)).
  { exact Heps1 (F0 X) LFX. }
  claim LmuX: Hom (T0 (T0 X)) (T0 X) (mu X).
  { exact HG2 (F0 (T0 X)) (F0 X) (eps (F0 X)) LFTX LFX LepsFX. }
  claim LFmuX: Hom' (F0 (T0 (T0 X))) (F0 (T0 X)) (F1 (T0 (T0 X)) (T0 X) (mu X)).
  { exact HF2 (T0 (T0 X)) (T0 X) (mu X) LTTX LTX LmuX. }
  prove comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (T1 (T0 (T0 X)) (T0 X) (mu X))
      = comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (mu (T0 X)).
  transitivity G1 (F0 (T0 (T0 X))) (F0 X) (comp' (F0 (T0 (T0 X))) (F0 (T0 X)) (F0 X) (eps (F0 X)) (F1 (T0 (T0 X)) (T0 X) (mu X))),
               G1 (F0 (T0 (T0 X))) (F0 X) (comp' (F0 (T0 (T0 X))) (F0 (T0 X)) (F0 X) (eps (F0 X)) (eps (F0 (T0 X)))).
  + prove comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (T1 (T0 (T0 X)) (T0 X) (mu X))
        = G1 (F0 (T0 (T0 X))) (F0 X) (comp' (F0 (T0 (T0 X))) (F0 (T0 X)) (F0 X) (eps (F0 X)) (F1 (T0 (T0 X)) (T0 X) (mu X))).
    symmetry.
    exact HG4 (F0 (T0 (T0 X))) (F0 (T0 X)) (F0 X) (F1 (T0 (T0 X)) (T0 X) (mu X)) (eps (F0 X)) LFTTX LFTX LFX LFmuX LepsFX.
  + prove G1 (F0 (T0 (T0 X))) (F0 X) (comp' (F0 (T0 (T0 X))) (F0 (T0 X)) (F0 X) (eps (F0 X)) (F1 (T0 (T0 X)) (T0 X) (mu X)))
        = G1 (F0 (T0 (T0 X))) (F0 X) (comp' (F0 (T0 (T0 X))) (F0 (T0 X)) (F0 X) (eps (F0 X)) (eps (F0 (T0 X)))).
    f_equal.
    symmetry.
    prove comp' (F0 (T0 (T0 X))) (F0 (T0 X)) (F0 X) (eps (F0 X)) (eps (F0 (T0 X))) = comp' (F0 (T0 (T0 X))) (F0 (T0 X)) (F0 X) (eps (F0 X)) (F1 (T0 (T0 X)) (T0 X) (mu X)).
    exact Heps2 (F0 (T0 X)) (F0 X) (eps (F0 X)) LFTX LFX LepsFX.
  + prove G1 (F0 (T0 (T0 X))) (F0 X) (comp' (F0 (T0 (T0 X))) (F0 (T0 X)) (F0 X) (eps (F0 X)) (eps (F0 (T0 X))))
        = comp (T0 (T0 (T0 X))) (T0 (T0 X)) (T0 X) (mu X) (mu (T0 X)).
    exact HG4 (F0 (T0 (T0 X))) (F0 (T0 X)) (F0 X) (eps (F0 (T0 X))) (eps (F0 X))
              LFTTX LFTX LFX
	      (Heps1 (F0 (T0 X)) LFTX) LepsFX.
- prove forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (eta (T0 X)) = id (T0 X).
  let X. assume HX.
  prove comp (G0 (F0 X)) (G0 (F0 (G0 (F0 X)))) (G0 (F0 X)) (G1 (F0 (G0 (F0 X))) (F0 X) (eps (F0 X))) (eta (G0 (F0 X)))
      = id (G0 (F0 X)).
  exact HA2 (F0 X) (HF1 X HX).
- prove forall X, Obj X -> comp (T0 X) (T0 (T0 X)) (T0 X) (mu X) (T1 X (T0 X) (eta X)) = id (T0 X).
  let X. assume HX.
  prove comp (G0 (F0 X)) (G0 (F0 (T0 X))) (G0 (F0 X)) (G1 (F0 (T0 X)) (F0 X) (eps (F0 X))) (G1 (F0 X) (F0 (T0 X)) (F1 X (T0 X) (eta X)))
      = id (T0 X).
  claim LFX: Obj' (F0 X).
  { apply HF1. exact HX. }
  claim LTX: Obj (T0 X).
  { exact HT01 X HX. }
  claim LFTX: Obj' (F0 (T0 X)).
  { apply HF1. exact LTX. }
  transitivity G1 (F0 X) (F0 X) (comp' (F0 X) (F0 (T0 X)) (F0 X) (eps (F0 X)) (F1 X (T0 X) (eta X))),
               G1 (F0 X) (F0 X) (id' (F0 X)).
  + prove comp (G0 (F0 X)) (G0 (F0 (T0 X))) (G0 (F0 X)) (G1 (F0 (T0 X)) (F0 X) (eps (F0 X))) (G1 (F0 X) (F0 (T0 X)) (F1 X (T0 X) (eta X)))
        = G1 (F0 X) (F0 X) (comp' (F0 X) (F0 (T0 X)) (F0 X) (eps (F0 X)) (F1 X (T0 X) (eta X))).
    symmetry.
    apply HG4 (F0 X) (F0 (T0 X)) (F0 X) (F1 X (T0 X) (eta X)) (eps (F0 X)).
    * exact LFX.
    * exact LFTX.
    * exact LFX.
    * prove Hom' (F0 X) (F0 (T0 X)) (F1 X (T0 X) (eta X)).
      exact HF2 X (T0 X) (eta X) HX LTX (Heta1 X HX).
    * prove Hom' (F0 (G0 (F0 X))) (F0 X) (eps (F0 X)).
      exact Heps1 (F0 X) (HF1 X HX).
  + prove G1 (F0 X) (F0 X) (comp' (F0 X) (F0 (T0 X)) (F0 X) (eps (F0 X)) (F1 X (T0 X) (eta X)))
        = G1 (F0 X) (F0 X) (id' (F0 X)).
    f_equal.
    exact HA1 X HX.
  + prove G1 (F0 X) (F0 X) (id' (F0 X))
        = id (T0 X).
    exact HG3 (F0 X) LFX.
Qed.

Theorem MetaAdjunctionMonad_strict:
    MetaAdjunction_strict
 -> MetaMonad_strict Obj Hom id comp (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)) eta (fun X => G1 (F0 (G0 (F0 X))) (F0 X) (eps (F0 X))).
assume HA.
apply MetaAdjunction_strict_E HA.
assume HA1 HG Heta Heps HA5.
apply MetaFunctor_strict_E Obj Hom id comp Obj' Hom' id' comp' F0 F1 HA1.
assume HC HC' HF.
set T0 : set -> set := fun X => G0 (F0 X).
set T1 : set -> set -> set -> set := fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f).
set mu : set -> set := fun X => G1 (F0 (G0 (F0 X))) (F0 X) (eps (F0 X)).
claim LT: MetaFunctor Obj Hom id comp Obj Hom id comp T0 T1.
{ exact MetaCat_CompFunctors Obj Hom id comp Obj' Hom' id' comp' Obj Hom id comp F0 F1 G0 G1 HF HG. }
claim LTT: MetaFunctor Obj Hom id comp Obj Hom id comp (fun X => T0 (T0 X)) (fun X Y f => T1 (T0 X) (T0 Y) (T1 X Y f)).
{ exact MetaCat_CompFunctors Obj Hom id comp Obj Hom id comp Obj Hom id comp T0 T1 T0 T1 LT LT. }
claim LFT: MetaFunctor Obj Hom id comp Obj' Hom' id' comp' (fun X => F0 (T0 X)) (fun X Y f => F1 (T0 X) (T0 Y) (T1 X Y f)).
{ exact MetaCat_CompFunctors Obj Hom id comp Obj Hom id comp Obj' Hom' id' comp' T0 T1 F0 F1 LT HF. }
claim LepsF: MetaNatTrans Obj Hom id comp Obj' Hom' id' comp' (fun X => F0 (G0 (F0 X))) (fun X Y f => F1 (G0 (F0 X)) (G0 (F0 Y)) (G1 (F0 X) (F0 Y) (F1 X Y f))) F0 F1 (fun X => eps (F0 X)).
{ exact MetaCat_CompNatTransFunctor Obj Hom id comp Obj' Hom' id' comp' Obj' Hom' id' comp' (fun X => F0 (G0 X)) (fun X Y f => F1 (G0 X) (G0 Y) (G1 X Y f)) (fun X => X) (fun X Y f => f) F0 F1 eps Heps HF. }
claim Lmu : MetaNatTrans Obj Hom id comp Obj Hom id comp (fun Y => T0 (T0 Y)) (fun X Y g => T1 (T0 X) (T0 Y) (T1 X Y g)) T0 T1 mu.
{ exact MetaCat_CompFunctorNatTrans
   Obj Hom id comp Obj' Hom' id' comp' Obj Hom id comp
   (fun X => F0 (G0 (F0 X))) (fun X Y f => F1 (G0 (F0 X)) (G0 (F0 Y)) (G1 (F0 X) (F0 Y) (F1 X Y f))) F0 F1
   G0 G1
   (fun X => eps (F0 X))
   LFT HF LepsF HG.
}
apply MetaMonad_strict_I.
- apply MetaNatTrans_strict_I.
  + exact HC.
  + exact HC.
  + exact MetaCat_IdFunctor Obj Hom id comp.
  + exact LT.
  + prove MetaNatTrans Obj Hom id comp Obj Hom id comp (fun X => X) (fun X Y f => f) (fun X => G0 (F0 X)) (fun X Y f => G1 (F0 X) (F0 Y) (F1 X Y f)) eta.
    exact Heta.
- apply MetaNatTrans_strict_I.
  + exact HC.
  + exact HC.
  + exact LTT.
  + exact LT.
  + prove MetaNatTrans Obj Hom id comp Obj Hom id comp (fun Y => T0 (T0 Y)) (fun X Y g => T1 (T0 X) (T0 Y) (T1 X Y g)) T0 T1 mu.
    exact Lmu.
- exact MetaAdjunctionMonad HF HG Heta Heps HA5.
Qed.

End MetaAdjunction.

Section MetaCatConcrete.

Variable Obj: set -> prop.
Variable U: set -> set.
Variable Hom: set -> set -> set -> prop.

Theorem MetaCatConcrete :
    (forall X Y f, Obj X -> Obj Y -> Hom X Y f -> f :e U Y :^: U X)
 -> (forall X, Obj X -> Hom X X (lam_id (U X)))
 -> (forall X Y Z f g, Obj X -> Obj Y -> Obj Z -> Hom X Y f -> Hom Y Z g -> Hom X Z (lam_comp (U X) g f))
 -> MetaCat Obj Hom (fun X => lam_id (U X)) (fun X Y Z g f => lam_comp (U X) g f).
assume H1 H2 H3.
apply MetaCat_I.
- exact H2.
- exact H3.
- let X Y f. assume HX HY Hf.
  prove lam_comp (U X) f (lam_id (U X)) = f.
  exact lam_comp_id_R (U X) (U Y) f (H1 X Y f HX HY Hf).
- let X Y f. assume HX HY Hf.
  prove lam_comp (U X) (lam_id (U Y)) f = f.
  exact lam_comp_id_L (U X) (U Y) f (H1 X Y f HX HY Hf).
- let X Y Z W f g h. assume HX HY HZ HW Hf Hg Hh.
  symmetry.
  exact lam_comp_assoc (U X) (U Y) f (H1 X Y f HX HY Hf) g h.
Qed.

Theorem MetaCatConcreteForgetful:
    (forall X Y f, Obj X -> Obj Y -> Hom X Y f -> f :e U Y :^: U X)
 -> MetaFunctor Obj Hom (fun X => lam_id (U X)) (fun X Y Z f g => (lam_comp (U X) f g)) (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g)) U (fun X Y f => f).
assume H1.
set F0 := U.
set F1 := fun X Y f:set => f.
apply MetaFunctorI.
- let X. assume _. exact TrueI.
- exact H1.
- let X. assume _. reflexivity.
- let X Y Z f g. assume _ _ _ _ _. reflexivity.
Qed.

End MetaCatConcrete.

Theorem MetaCatSet : MetaCat (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z g f => lam_comp X g f).
apply MetaCatConcrete (fun _ => True) (fun X => X) SetHom.
- let X Y f. assume HX HY Hf. exact Hf.
- let X. assume HX. exact lam_id_exp_In X.
- let X Y Z f g. assume HX HY HZ Hf Hg. exact lam_comp_exp_In X Y Z f Hf g Hg.
Qed.

Theorem MetaCatHFSet : MetaCat (fun X => X :e UnivOf Empty) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g)).
apply MetaCatConcrete (fun X => X :e UnivOf Empty) (fun X => X) SetHom.
- let X Y f. assume HX HY Hf. exact Hf.
- let X. assume HX. exact lam_id_exp_In X.
- let X Y Z f g. assume HX HY HZ Hf Hg. exact lam_comp_exp_In X Y Z f Hf g Hg.
Qed.

Theorem MetaCatSmallSet : MetaCat (fun X => X :e UnivOf (UnivOf Empty)) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g)).
apply MetaCatConcrete (fun X => X :e UnivOf (UnivOf Empty)) (fun X => X) SetHom.
- let X Y f. assume HX HY Hf. exact Hf.
- let X. assume HX. exact lam_id_exp_In X.
- let X Y Z f g. assume HX HY HZ Hf Hg. exact lam_comp_exp_In X Y Z f Hf g Hg.
Qed.

Theorem MetaCatConcreteForgetful_strict: forall Obj:set -> prop, forall U:set -> set, forall Hom:set -> set -> set -> prop,
    (forall X Y f, Obj X -> Obj Y -> Hom X Y f -> f :e U Y :^: U X)
 -> (forall X, Obj X -> Hom X X (lam_id (U X)))
 -> (forall X Y Z f g, Obj X -> Obj Y -> Obj Z -> Hom X Y f -> Hom Y Z g -> Hom X Z (lam_comp (U X) g f))
 -> MetaFunctor_strict Obj Hom (fun X => lam_id (U X)) (fun X Y Z f g => (lam_comp (U X) f g)) (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g)) U (fun X Y f => f).
let Obj U Hom.
assume H1 H2 H3.
apply MetaFunctor_strict_I.
- exact MetaCatConcrete Obj U Hom H1 H2 H3.
- exact MetaCatSet.
- exact MetaCatConcreteForgetful Obj U Hom H1.
Qed.

Definition Hom_struct_e : set -> set -> set -> prop
  := fun X Y f =>
      unpack_e_o X
       (fun X' eX =>
        unpack_e_o Y
         (fun Y' eY =>
	   f :e Y' :^: X' /\ f eX = eY)).

Definition Hom_struct_u : set -> set -> set -> prop
  := fun X Y f =>
      unpack_u_o X
       (fun X' uX =>
        unpack_u_o Y
         (fun Y' uY =>
	   f :e Y' :^: X' /\ forall x :e X', f (uX x) = uY (f x))).

Definition Hom_struct_b : set -> set -> set -> prop
  := fun X Y f =>
      unpack_b_o X
       (fun X' opX =>
        unpack_b_o Y
         (fun Y' opY =>
	   f :e Y' :^: X' /\ forall x y :e X', f (opX x y) = opY (f x) (f y))).

Definition Hom_struct_p : set -> set -> set -> prop
  := fun X Y f =>
      unpack_p_o X
       (fun X' pX =>
        unpack_p_o Y
         (fun Y' pY =>
	   f :e Y' :^: X' /\ forall x :e X', pX x -> pY (f x))).

Definition Hom_struct_r : set -> set -> set -> prop
  := fun X Y f =>
      unpack_r_o X
       (fun X' rX =>
        unpack_r_o Y
         (fun Y' rY =>
	   f :e Y' :^: X' /\ forall x y :e X', rX x y -> rY (f x) (f y))).

Definition Hom_struct_c : set -> set -> set -> prop
  := fun X Y f =>
      unpack_c_o X
       (fun X' CX =>
        unpack_c_o Y
         (fun Y' CY =>
	   f :e Y' :^: X' /\ forall U:set -> prop, (forall y, U y -> y :e Y') -> CY U -> CX (fun x => x :e X' /\ U (f x)))).

Definition Hom_struct_b_b_e : set -> set -> set -> prop
  := fun X Y f =>
      unpack_b_b_e_o X
       (fun X' opX op2X eX =>
        unpack_b_b_e_o Y
         (fun Y' opY op2Y eY =>
	      f :e Y' :^: X'
	   /\ (forall x y :e X', f (opX x y) = opY (f x) (f y))
	   /\ (forall x y :e X', f (op2X x y) = op2Y (f x) (f y))
	   /\ f eX = eY)).

Definition Hom_struct_b_b_e_e : set -> set -> set -> prop
  := fun X Y f =>
      unpack_b_b_e_e_o X
       (fun X' opX op2X eX e2X =>
        unpack_b_b_e_e_o Y
         (fun Y' opY op2Y eY e2Y =>
	      f :e Y' :^: X'
	   /\ (forall x y :e X', f (opX x y) = opY (f x) (f y))
	   /\ (forall x y :e X', f (op2X x y) = op2Y (f x) (f y))
	   /\ f eX = eY
	   /\ f e2X = e2Y)).

Definition Hom_struct_b_b_r_e_e : set -> set -> set -> prop
  := fun X Y f =>
      unpack_b_b_r_e_e_o X
       (fun X' opX op2X rX eX e2X =>
        unpack_b_b_r_e_e_o Y
         (fun Y' opY op2Y rY eY e2Y =>
	      f :e Y' :^: X'
	   /\ (forall x y :e X', f (opX x y) = opY (f x) (f y))
	   /\ (forall x y :e X', f (op2X x y) = op2Y (f x) (f y))
	   /\ (forall x y :e X', rX x y -> rY (f x) (f y))
	   /\ f eX = eY
	   /\ f e2X = e2Y)).

Theorem Hom_struct_e_pack :
 forall X Y eX eY f,
    (Hom_struct_e (pack_e X eX) (pack_e Y eY) f)
  = (f :e Y :^: X /\ f eX = eY).
let X Y eX eY f.
set Phi : set -> set -> set -> set -> prop
  := fun X eX Y eY => f :e Y :^: X /\ f eX = eY.
set PhiX : set -> set -> prop
 := fun X eX => unpack_e_o (pack_e Y eY) (fun Y' eY => Phi X eX Y' eY).
prove unpack_e_o (pack_e X eX) PhiX = Phi X eX Y eY.
transitivity PhiX X eX.
- exact unpack_e_o_eq PhiX X eX.
- prove unpack_e_o (pack_e Y eY) (Phi X eX) = Phi X eX Y eY.
  exact unpack_e_o_eq (Phi X eX) Y eY.
Qed.

Theorem Hom_struct_u_pack :
 forall X Y, forall opX opY:set -> set,
 forall f,
    (Hom_struct_u (pack_u X opX) (pack_u Y opY) f)
  = (f :e Y :^: X /\ (forall x :e X, f (opX x) = opY (f x))).
let X Y opX opY f.
set Phi : set -> (set -> set) -> set -> (set -> set) -> prop
  := fun X opX Y opY =>
	      f :e Y :^: X
	   /\ (forall x :e X, f (opX x) = opY (f x)).
set PhiX : set -> (set -> set) -> prop
 := fun X opX =>
      unpack_u_o (pack_u Y opY)
       (fun Y' opY => Phi X opX Y' opY).
prove unpack_u_o (pack_u X opX) PhiX = Phi X opX Y opY.
claim L1: forall opX:set -> set,
          forall opY':set -> set, (forall x :e Y, opY x = opY' x)
       -> Phi X opX Y opY' = Phi X opX Y opY.
{ let opX.
  let opY'. assume HopY'.
  apply prop_ext_2.
  - assume H. apply H.
    assume H1 H2.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x :e X, f (opX x) = opY (f x)).
    apply andI.
    + exact H1.
    + let x. assume Hx. rewrite HopY' (f x) (Lf x Hx).
      exact H2 x Hx.
  - assume H. apply H.
    assume H1 H2.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x :e X, f (opX x) = opY' (f x)).
    apply andI.
    + exact H1.
    + let x. assume Hx. rewrite <- HopY' (f x) (Lf x Hx).
      exact H2 x Hx.
}
claim L2: forall opX':set -> set, (forall x :e X, opX x = opX' x)
       -> PhiX X opX' = PhiX X opX.
{ let opX'. assume HopX'.
  prove PhiX X opX' = PhiX X opX.
  prove unpack_u_o (pack_u Y opY)
          (fun Y' opY => Phi X opX' Y' opY)
      = unpack_u_o (pack_u Y opY)
          (fun Y' opY => Phi X opX Y' opY).
  transitivity Phi X opX' Y opY,
               Phi X opX Y opY.
  - prove unpack_u_o (pack_u Y opY) (Phi X opX')
      = Phi X opX' Y opY.
    exact unpack_u_o_eq (Phi X opX') Y opY (L1 opX').
  - prove Phi X opX' Y opY
        = Phi X opX Y opY.
    apply prop_ext_2.
    + assume H. apply H.
      assume H1 H2.
      prove f :e Y :^: X
         /\ (forall x :e X, f (opX x) = opY (f x)).
      apply andI.
      * exact H1.
      * let x. assume Hx. rewrite HopX' x Hx.
        exact H2 x Hx.
    + assume H. apply H.
      assume H1 H2.
      prove f :e Y :^: X
         /\ (forall x :e X, f (opX' x) = opY (f x)).
      apply andI.
      * exact H1.
      * let x. assume Hx. rewrite <- HopX' x Hx.
        exact H2 x Hx.
  - symmetry.
    exact unpack_u_o_eq (Phi X opX) Y opY (L1 opX).
}
transitivity PhiX X opX.
- exact unpack_u_o_eq PhiX X opX L2.
- prove unpack_u_o (pack_u Y opY) (Phi X opX)
      = Phi X opX Y opY.
  exact unpack_u_o_eq (Phi X opX) Y opY (L1 opX).
Qed.

Theorem Hom_struct_b_pack :
 forall X Y, forall opX opY:set -> set -> set,
 forall f,
    (Hom_struct_b (pack_b X opX) (pack_b Y opY) f)
  = (f :e Y :^: X /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))).
let X Y opX opY f.
set Phi : set -> (set -> set -> set) -> set -> (set -> set -> set) -> prop
  := fun X opX Y opY =>
	      f :e Y :^: X
	   /\ (forall x y :e X, f (opX x y) = opY (f x) (f y)).
set PhiX : set -> (set -> set -> set) -> prop
 := fun X opX =>
      unpack_b_o (pack_b Y opY)
       (fun Y' opY => Phi X opX Y' opY).
prove unpack_b_o (pack_b X opX) PhiX = Phi X opX Y opY.
claim L1: forall opX:set -> set -> set,
          forall opY':set -> set -> set, (forall x y :e Y, opY x y = opY' x y)
       -> Phi X opX Y opY' = Phi X opX Y opY.
{ let opX.
  let opY'. assume HopY'.
  apply prop_ext_2.
  - assume H. apply H.
    assume H1 H2.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x y :e X, f (opX x y) = opY (f x) (f y)).
    apply andI.
    + exact H1.
    + let x. assume Hx. let y. assume Hy. rewrite HopY' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H2 x Hx y Hy.
  - assume H. apply H.
    assume H1 H2.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x y :e X, f (opX x y) = opY' (f x) (f y)).
    apply andI.
    + exact H1.
    + let x. assume Hx. let y. assume Hy. rewrite <- HopY' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H2 x Hx y Hy.
}
claim L2: forall opX':set -> set -> set, (forall x y :e X, opX x y = opX' x y)
       -> PhiX X opX' = PhiX X opX.
{ let opX'. assume HopX'.
  prove PhiX X opX' = PhiX X opX.
  prove unpack_b_o (pack_b Y opY)
          (fun Y' opY => Phi X opX' Y' opY)
      = unpack_b_o (pack_b Y opY)
          (fun Y' opY => Phi X opX Y' opY).
  transitivity Phi X opX' Y opY,
               Phi X opX Y opY.
  - prove unpack_b_o (pack_b Y opY) (Phi X opX')
      = Phi X opX' Y opY.
    exact unpack_b_o_eq (Phi X opX') Y opY (L1 opX').
  - prove Phi X opX' Y opY
        = Phi X opX Y opY.
    apply prop_ext_2.
    + assume H. apply H.
      assume H1 H2.
      prove f :e Y :^: X
         /\ (forall x y :e X, f (opX x y) = opY (f x) (f y)).
      apply andI.
      * exact H1.
      * let x. assume Hx. let y. assume Hy. rewrite HopX' x Hx y Hy.
        exact H2 x Hx y Hy.
    + assume H. apply H.
      assume H1 H2.
      prove f :e Y :^: X
         /\ (forall x y :e X, f (opX' x y) = opY (f x) (f y)).
      apply andI.
      * exact H1.
      * let x. assume Hx. let y. assume Hy. rewrite <- HopX' x Hx y Hy.
        exact H2 x Hx y Hy.
  - symmetry.
    exact unpack_b_o_eq (Phi X opX) Y opY (L1 opX).
}
transitivity PhiX X opX.
- exact unpack_b_o_eq PhiX X opX L2.
- prove unpack_b_o (pack_b Y opY) (Phi X opX)
      = Phi X opX Y opY.
  exact unpack_b_o_eq (Phi X opX) Y opY (L1 opX).
Qed.

Theorem Hom_struct_p_pack :
 forall X Y, forall pX pY:set -> prop, forall f,
    (Hom_struct_p (pack_p X pX) (pack_p Y pY) f)
  = (f :e Y :^: X /\ (forall x :e X, pX x -> pY (f x))).
let X Y pX pY f.
set Phi : set -> (set -> prop) -> set -> (set -> prop) -> prop
  := fun X pX Y pY => f :e Y :^: X /\ (forall x :e X, pX x -> pY (f x)).
set PhiX : set -> (set -> prop) -> prop
 := fun X pX => unpack_p_o (pack_p Y pY) (fun Y' pY => Phi X pX Y' pY).
prove unpack_p_o (pack_p X pX) PhiX
    = Phi X pX Y pY.
claim L1: forall pX:set -> prop,
          forall pY':set -> prop, (forall x :e Y, pY x <-> pY' x)
       -> Phi X pX Y pY' = Phi X pX Y pY.
{ let pX.
  let pY'. assume HpY'.
  apply prop_ext_2.
  - assume H. apply H.
    assume H1 H2.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x :e X, pX x -> pY (f x)).
    apply andI.
    + exact H1.
    + let x. assume Hx H7. apply iffER (pY (f x)) (pY' (f x)) (HpY' (f x) (Lf x Hx)).
      exact H2 x Hx H7.
  - assume H. apply H.
    assume H1 H2.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x :e X, pX x -> pY' (f x)).
    apply andI.
    + exact H1.
    + let x. assume Hx H7. apply iffEL (pY (f x)) (pY' (f x)) (HpY' (f x) (Lf x Hx)).
      exact H2 x Hx H7.
}
claim L2: forall pX':set -> prop, (forall x :e X, pX x <-> pX' x)
       -> PhiX X pX' = PhiX X pX.
{ let pX'. assume HpX'.
  prove PhiX X pX' = PhiX X pX.
  prove unpack_p_o (pack_p Y pY) (fun Y' pY => Phi X pX' Y' pY)
      = unpack_p_o (pack_p Y pY) (fun Y' pY => Phi X pX Y' pY).
  transitivity Phi X pX' Y pY,
               Phi X pX Y pY.
  - prove unpack_p_o (pack_p Y pY) (Phi X pX')
      = Phi X pX' Y pY.
    exact unpack_p_o_eq (Phi X pX') Y pY (L1 pX').
  - prove Phi X pX' Y pY
        = Phi X pX Y pY.
    apply prop_ext_2.
    + assume H. apply H.
      assume H1 H2.
      prove f :e Y :^: X
         /\ (forall x :e X, pX x -> pY (f x)).
      apply andI.
      * exact H1.
      * let x. assume Hx H7. apply H2 x Hx.
        apply iffEL (pX x) (pX' x) (HpX' x Hx).
        exact H7.
    + assume H. apply H.
      assume H1 H2.
      prove f :e Y :^: X
         /\ (forall x :e X, pX' x -> pY (f x)).
      apply andI.
      * exact H1.
      * let x. assume Hx H7. apply H2 x Hx.
        apply iffER (pX x) (pX' x) (HpX' x Hx).
	exact H7.
  - symmetry.
    exact unpack_p_o_eq (Phi X pX) Y pY (L1 pX).
}
transitivity PhiX X pX.
- exact unpack_p_o_eq PhiX X pX L2.
- prove unpack_p_o (pack_p Y pY) (Phi X pX)
      = Phi X pX Y pY.
  exact unpack_p_o_eq (Phi X pX) Y pY (L1 pX).
Qed.

Theorem Hom_struct_r_pack :
 forall X Y, forall rX rY:set -> set -> prop, forall f,
    (Hom_struct_r (pack_r X rX) (pack_r Y rY) f)
  = (f :e Y :^: X /\ (forall x y :e X, rX x y -> rY (f x) (f y))).
let X Y rX rY f.
set Phi : set -> (set -> set -> prop) -> set -> (set -> set -> prop) -> prop
  := fun X rX Y rY => f :e Y :^: X /\ (forall x y :e X, rX x y -> rY (f x) (f y)).
set PhiX : set -> (set -> set -> prop) -> prop
 := fun X rX => unpack_r_o (pack_r Y rY) (fun Y' rY => Phi X rX Y' rY).
prove unpack_r_o (pack_r X rX) PhiX
    = Phi X rX Y rY.
claim L1: forall rX:set -> set -> prop,
          forall rY':set -> set -> prop, (forall x y :e Y, rY x y <-> rY' x y)
       -> Phi X rX Y rY' = Phi X rX Y rY.
{ let rX.
  let rY'. assume HrY'.
  apply prop_ext_2.
  - assume H. apply H.
    assume H1 H2.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x y :e X, rX x y -> rY (f x) (f y)).
    apply andI.
    + exact H1.
    + let x. assume Hx. let y. assume Hy H7. apply iffER (rY (f x) (f y)) (rY' (f x) (f y)) (HrY' (f x) (Lf x Hx) (f y) (Lf y Hy)).
      exact H2 x Hx y Hy H7.
  - assume H. apply H.
    assume H1 H2.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x y :e X, rX x y -> rY' (f x) (f y)).
    apply andI.
    + exact H1.
    + let x. assume Hx. let y. assume Hy H7. apply iffEL (rY (f x) (f y)) (rY' (f x) (f y)) (HrY' (f x) (Lf x Hx) (f y) (Lf y Hy)).
      exact H2 x Hx y Hy H7.
}
claim L2: forall rX':set -> set -> prop, (forall x y :e X, rX x y <-> rX' x y)
       -> PhiX X rX' = PhiX X rX.
{ let rX'. assume HrX'.
  prove PhiX X rX' = PhiX X rX.
  prove unpack_r_o (pack_r Y rY) (fun Y' rY => Phi X rX' Y' rY)
      = unpack_r_o (pack_r Y rY) (fun Y' rY => Phi X rX Y' rY).
  transitivity Phi X rX' Y rY,
               Phi X rX Y rY.
  - prove unpack_r_o (pack_r Y rY) (Phi X rX')
      = Phi X rX' Y rY.
    exact unpack_r_o_eq (Phi X rX') Y rY (L1 rX').
  - prove Phi X rX' Y rY
        = Phi X rX Y rY.
    apply prop_ext_2.
    + assume H. apply H.
      assume H1 H2.
      prove f :e Y :^: X
         /\ (forall x y :e X, rX x y -> rY (f x) (f y)).
      apply andI.
      * exact H1.
      * let x. assume Hx. let y. assume Hy H7. apply H2 x Hx y Hy.
        apply iffEL (rX x y) (rX' x y) (HrX' x Hx y Hy).
        exact H7.
    + assume H. apply H.
      assume H1 H2.
      prove f :e Y :^: X
         /\ (forall x y :e X, rX' x y -> rY (f x) (f y)).
      apply andI.
      * exact H1.
      * let x. assume Hx. let y. assume Hy H7. apply H2 x Hx y Hy.
        apply iffER (rX x y) (rX' x y) (HrX' x Hx y Hy).
	exact H7.
  - symmetry.
    exact unpack_r_o_eq (Phi X rX) Y rY (L1 rX).
}
transitivity PhiX X rX.
- exact unpack_r_o_eq PhiX X rX L2.
- prove unpack_r_o (pack_r Y rY) (Phi X rX)
      = Phi X rX Y rY.
  exact unpack_r_o_eq (Phi X rX) Y rY (L1 rX).
Qed.

Theorem Hom_struct_c_pack :
 forall X Y, forall CX CY:(set -> prop) -> prop, forall f,
    (Hom_struct_c (pack_c X CX) (pack_c Y CY) f)
  = (f :e Y :^: X /\ (forall U:set -> prop, (forall y, U y -> y :e Y) -> CY U -> CX (fun x => x :e X /\ U (f x)))).
let X Y CX CY f.
set Phi : set -> ((set -> prop) -> prop) -> set -> ((set -> prop) -> prop) -> prop
  := fun X CX Y CY => f :e Y :^: X /\ (forall U:set -> prop, (forall y, U y -> y :e Y) -> CY U -> CX (fun x => x :e X /\ U (f x))).
set PhiX : set -> ((set -> prop) -> prop) -> prop
 := fun X CX => unpack_c_o (pack_c Y CY) (fun Y' CY => Phi X CX Y' CY).
prove unpack_c_o (pack_c X CX) PhiX = Phi X CX Y CY.
claim L1: forall CX:(set -> prop) -> prop,
          forall CY':(set -> prop) -> prop, (forall U:set -> prop, (forall y, U y -> y :e Y) -> (CY U <-> CY' U))
       -> Phi X CX Y CY' = Phi X CX Y CY.
{ let CX.
  let CY'. assume HCY'.
  apply prop_ext_2.
  - assume H. apply H.
    assume H1 H2.
    prove f :e Y :^: X
       /\ (forall U:set -> prop, (forall y, U y -> y :e Y) -> CY U -> CX (fun x => x :e X /\ U (f x))).
    apply andI.
    + exact H1.
    + let U. assume HU1 HU2.
      prove CX (fun x => x :e X /\ U (f x)).
      apply H2.
      * exact HU1.
      * prove CY' U.
        exact iffEL (CY U) (CY' U) (HCY' U HU1) HU2.
  - assume H. apply H.
    assume H1 H2.
    prove f :e Y :^: X
       /\ (forall U:set -> prop, (forall y, U y -> y :e Y) -> CY' U -> CX (fun x => x :e X /\ U (f x))).
    apply andI.
    + exact H1.
    + let U. assume HU1 HU2.
      prove CX (fun x => x :e X /\ U (f x)).
      apply H2.
      * exact HU1.
      * prove CY U.
        exact iffER (CY U) (CY' U) (HCY' U HU1) HU2.
}
claim L2: forall CX':(set -> prop) -> prop, (forall U:set -> prop, (forall x, U x -> x :e X) -> (CX U <-> CX' U))
       -> PhiX X CX' = PhiX X CX.
{ let CX'. assume HCX'.
  prove PhiX X CX' = PhiX X CX.
  prove unpack_c_o (pack_c Y CY) (fun Y' CY => Phi X CX' Y' CY)
      = unpack_c_o (pack_c Y CY) (fun Y' CY => Phi X CX Y' CY).
  transitivity Phi X CX' Y CY,
               Phi X CX Y CY.
  - prove unpack_c_o (pack_c Y CY) (Phi X CX')
      = Phi X CX' Y CY.
    exact unpack_c_o_eq (Phi X CX') Y CY (L1 CX').
  - prove Phi X CX' Y CY
        = Phi X CX Y CY.
    apply prop_ext_2.
    + assume H. apply H.
      assume H1: f :e Y :^: X.
      assume H2: forall U:set -> prop, (forall y, U y -> y :e Y) -> CY U -> CX' (fun x => x :e X /\ U (f x)).
      prove f :e Y :^: X
         /\ (forall U:set -> prop, (forall y, U y -> y :e Y) -> CY U -> CX (fun x => x :e X /\ U (f x))).
      apply andI.
      * exact H1.
      * let U.
        assume HU1: forall y, U y -> y :e Y.
	assume HU2: CY U.
        claim LU: forall x, x :e X /\ U (f x) -> x :e X.
	{ let x. exact andEL (x :e X) (U (f x)). }
        apply iffER (CX (fun x => x :e X /\ U (f x)))
	            (CX' (fun x => x :e X /\ U (f x)))
		    (HCX' (fun x => x :e X /\ U (f x)) LU).
        exact H2 U HU1 HU2.
    + assume H. apply H.
      assume H1 H2.
      prove f :e Y :^: X
         /\ (forall U:set -> prop, (forall y, U y -> y :e Y) -> CY U -> CX' (fun x => x :e X /\ U (f x))).
      apply andI.
      * exact H1.
      * let U.
        assume HU1: forall y, U y -> y :e Y.
	assume HU2: CY U.
        claim LU: forall x, x :e X /\ U (f x) -> x :e X.
	{ let x. exact andEL (x :e X) (U (f x)). }
        apply iffEL (CX (fun x => x :e X /\ U (f x)))
	            (CX' (fun x => x :e X /\ U (f x)))
		    (HCX' (fun x => x :e X /\ U (f x)) LU).
        exact H2 U HU1 HU2.
  - symmetry.
    exact unpack_c_o_eq (Phi X CX) Y CY (L1 CX).
}
transitivity PhiX X CX.
- exact unpack_c_o_eq PhiX X CX L2.
- prove unpack_c_o (pack_c Y CY) (Phi X CX)
      = Phi X CX Y CY.
  exact unpack_c_o_eq (Phi X CX) Y CY (L1 CX).
Qed.

Theorem Hom_struct_b_b_e_pack :
 forall X Y, forall opX op2X opY op2Y:set -> set -> set,
 forall eX eY f,
    (Hom_struct_b_b_e (pack_b_b_e X opX op2X eX) (pack_b_b_e Y opY op2Y eY) f)
  = (f :e Y :^: X
	   /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
	   /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
	   /\ f eX = eY).
let X Y opX op2X opY op2Y eX eY f.
set Phi : set -> (set -> set -> set) -> (set -> set -> set) -> set -> set -> (set -> set -> set) -> (set -> set -> set) -> set -> prop
  := fun X opX op2X eX Y opY op2Y eY =>
	      f :e Y :^: X
	   /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
	   /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
	   /\ f eX = eY.
set PhiX : set -> (set -> set -> set) -> (set -> set -> set) -> set -> prop
 := fun X opX op2X eX =>
      unpack_b_b_e_o (pack_b_b_e Y opY op2Y eY)
       (fun Y' opY op2Y eY => Phi X opX op2X eX Y' opY op2Y eY).
prove unpack_b_b_e_o (pack_b_b_e X opX op2X eX) PhiX
    = Phi X opX op2X eX Y opY op2Y eY.
claim L1: forall opX op2X:set -> set -> set,
          forall opY':set -> set -> set, (forall x y :e Y, opY x y = opY' x y)
       -> forall op2Y':set -> set -> set, (forall x y :e Y, op2Y x y = op2Y' x y)
       -> Phi X opX op2X eX Y opY' op2Y' eY = Phi X opX op2X eX Y opY op2Y eY.
{ let opX op2X.
  let opY'. assume HopY'.
  let op2Y'. assume Hop2Y'.
  apply prop_ext_2.
  - assume H.
    apply and4E (f :e Y :^: X) (forall x y :e X, f (opX x y) = opY' (f x) (f y)) (forall x y :e X, f (op2X x y) = op2Y' (f x) (f y)) (f eX = eY) H.
    assume H1 H2 H3 H4.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
       /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
       /\ f eX = eY.
    apply and4I.
    + exact H1.
    + let x. assume Hx. let y. assume Hy. rewrite HopY' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H2 x Hx y Hy.
    + let x. assume Hx. let y. assume Hy. rewrite Hop2Y' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H3 x Hx y Hy.
    + exact H4.
  - assume H.
    apply and4E (f :e Y :^: X) (forall x y :e X, f (opX x y) = opY (f x) (f y)) (forall x y :e X, f (op2X x y) = op2Y (f x) (f y)) (f eX = eY) H.
    assume H1 H2 H3 H4.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x y :e X, f (opX x y) = opY' (f x) (f y))
       /\ (forall x y :e X, f (op2X x y) = op2Y' (f x) (f y))
       /\ f eX = eY.
    apply and4I.
    + exact H1.
    + let x. assume Hx. let y. assume Hy. rewrite <- HopY' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H2 x Hx y Hy.
    + let x. assume Hx. let y. assume Hy. rewrite <- Hop2Y' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H3 x Hx y Hy.
    + exact H4.
}
claim L2: forall opX':set -> set -> set, (forall x y :e X, opX x y = opX' x y)
       -> forall op2X':set -> set -> set, (forall x y :e X, op2X x y = op2X' x y)
       -> PhiX X opX' op2X' eX = PhiX X opX op2X eX.
{ let opX'. assume HopX'.
  let op2X'. assume Hop2X'.
  prove PhiX X opX' op2X' eX = PhiX X opX op2X eX.
  prove unpack_b_b_e_o (pack_b_b_e Y opY op2Y eY)
          (fun Y' opY op2Y eY => Phi X opX' op2X' eX Y' opY op2Y eY)
      = unpack_b_b_e_o (pack_b_b_e Y opY op2Y eY)
          (fun Y' opY op2Y eY => Phi X opX op2X eX Y' opY op2Y eY).
  transitivity Phi X opX' op2X' eX Y opY op2Y eY,
               Phi X opX op2X eX Y opY op2Y eY.
  - prove unpack_b_b_e_o (pack_b_b_e Y opY op2Y eY) (Phi X opX' op2X' eX)
      = Phi X opX' op2X' eX Y opY op2Y eY.
    exact unpack_b_b_e_o_eq (Phi X opX' op2X' eX) Y opY op2Y eY (L1 opX' op2X').
  - prove Phi X opX' op2X' eX Y opY op2Y eY
        = Phi X opX op2X eX Y opY op2Y eY.
    apply prop_ext_2.
    + assume H.
      apply and4E (f :e Y :^: X) (forall x y :e X, f (opX' x y) = opY (f x) (f y)) (forall x y :e X, f (op2X' x y) = op2Y (f x) (f y)) (f eX = eY) H.
      assume H1 H2 H3 H4.
      prove f :e Y :^: X
         /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
         /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
         /\ f eX = eY.
      apply and4I.
      * exact H1.
      * let x. assume Hx. let y. assume Hy. rewrite HopX' x Hx y Hy.
        exact H2 x Hx y Hy.
      * let x. assume Hx. let y. assume Hy. rewrite Hop2X' x Hx y Hy.
        exact H3 x Hx y Hy.
      * exact H4.
    + assume H.
      apply and4E (f :e Y :^: X) (forall x y :e X, f (opX x y) = opY (f x) (f y)) (forall x y :e X, f (op2X x y) = op2Y (f x) (f y)) (f eX = eY) H.
      assume H1 H2 H3 H4.
      prove f :e Y :^: X
         /\ (forall x y :e X, f (opX' x y) = opY (f x) (f y))
         /\ (forall x y :e X, f (op2X' x y) = op2Y (f x) (f y))
         /\ f eX = eY.
      apply and4I.
      * exact H1.
      * let x. assume Hx. let y. assume Hy. rewrite <- HopX' x Hx y Hy.
        exact H2 x Hx y Hy.
      * let x. assume Hx. let y. assume Hy. rewrite <- Hop2X' x Hx y Hy.
        exact H3 x Hx y Hy.
      * exact H4.
  - symmetry.
    exact unpack_b_b_e_o_eq (Phi X opX op2X eX) Y opY op2Y eY (L1 opX op2X).
}
transitivity PhiX X opX op2X eX.
- exact unpack_b_b_e_o_eq PhiX X opX op2X eX L2.
- prove unpack_b_b_e_o (pack_b_b_e Y opY op2Y eY) (Phi X opX op2X eX)
      = Phi X opX op2X eX Y opY op2Y eY.
  exact unpack_b_b_e_o_eq (Phi X opX op2X eX) Y opY op2Y eY (L1 opX op2X).
Qed.

Theorem Hom_struct_b_b_e_e_pack :
 forall X Y, forall opX op2X opY op2Y:set -> set -> set,
 forall eX e2X eY e2Y f,
    (Hom_struct_b_b_e_e (pack_b_b_e_e X opX op2X eX e2X) (pack_b_b_e_e Y opY op2Y eY e2Y) f)
  = (f :e Y :^: X
	   /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
	   /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
	   /\ f eX = eY
	   /\ f e2X = e2Y).
let X Y opX op2X opY op2Y eX e2X eY e2Y f.
set Phi : set -> (set -> set -> set) -> (set -> set -> set) -> set -> set -> set -> (set -> set -> set) -> (set -> set -> set) -> set -> set -> prop
  := fun X opX op2X eX e2X Y opY op2Y eY e2Y =>
	      f :e Y :^: X
	   /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
	   /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
	   /\ f eX = eY
	   /\ f e2X = e2Y.
set PhiX : set -> (set -> set -> set) -> (set -> set -> set) -> set -> set -> prop
 := fun X opX op2X eX e2X =>
      unpack_b_b_e_e_o (pack_b_b_e_e Y opY op2Y eY e2Y)
       (fun Y' opY op2Y eY e2Y => Phi X opX op2X eX e2X Y' opY op2Y eY e2Y).
prove unpack_b_b_e_e_o (pack_b_b_e_e X opX op2X eX e2X) PhiX
    = Phi X opX op2X eX e2X Y opY op2Y eY e2Y.
claim L1: forall opX op2X:set -> set -> set,
          forall opY':set -> set -> set, (forall x y :e Y, opY x y = opY' x y)
       -> forall op2Y':set -> set -> set, (forall x y :e Y, op2Y x y = op2Y' x y)
       -> Phi X opX op2X eX e2X Y opY' op2Y' eY e2Y = Phi X opX op2X eX e2X Y opY op2Y eY e2Y.
{ let opX op2X.
  let opY'. assume HopY'.
  let op2Y'. assume Hop2Y'.
  apply prop_ext_2.
  - assume H.
    apply and5E (f :e Y :^: X) (forall x y :e X, f (opX x y) = opY' (f x) (f y)) (forall x y :e X, f (op2X x y) = op2Y' (f x) (f y)) (f eX = eY) (f e2X = e2Y) H.
    assume H1 H2 H3 H4 H5.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
       /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
       /\ f eX = eY
       /\ f e2X = e2Y.
    apply and5I.
    + exact H1.
    + let x. assume Hx. let y. assume Hy. rewrite HopY' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H2 x Hx y Hy.
    + let x. assume Hx. let y. assume Hy. rewrite Hop2Y' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H3 x Hx y Hy.
    + exact H4.
    + exact H5.
  - assume H.
    apply and5E (f :e Y :^: X) (forall x y :e X, f (opX x y) = opY (f x) (f y)) (forall x y :e X, f (op2X x y) = op2Y (f x) (f y)) (f eX = eY) (f e2X = e2Y) H.
    assume H1 H2 H3 H4 H5.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x y :e X, f (opX x y) = opY' (f x) (f y))
       /\ (forall x y :e X, f (op2X x y) = op2Y' (f x) (f y))
       /\ f eX = eY
       /\ f e2X = e2Y.
    apply and5I.
    + exact H1.
    + let x. assume Hx. let y. assume Hy. rewrite <- HopY' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H2 x Hx y Hy.
    + let x. assume Hx. let y. assume Hy. rewrite <- Hop2Y' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H3 x Hx y Hy.
    + exact H4.
    + exact H5.
}
claim L2: forall opX':set -> set -> set, (forall x y :e X, opX x y = opX' x y)
       -> forall op2X':set -> set -> set, (forall x y :e X, op2X x y = op2X' x y)
       -> PhiX X opX' op2X' eX e2X = PhiX X opX op2X eX e2X.
{ let opX'. assume HopX'.
  let op2X'. assume Hop2X'.
  prove PhiX X opX' op2X' eX e2X = PhiX X opX op2X eX e2X.
  prove unpack_b_b_e_e_o (pack_b_b_e_e Y opY op2Y eY e2Y)
          (fun Y' opY op2Y eY e2Y => Phi X opX' op2X' eX e2X Y' opY op2Y eY e2Y)
      = unpack_b_b_e_e_o (pack_b_b_e_e Y opY op2Y eY e2Y)
          (fun Y' opY op2Y eY e2Y => Phi X opX op2X eX e2X Y' opY op2Y eY e2Y).
  transitivity Phi X opX' op2X' eX e2X Y opY op2Y eY e2Y,
               Phi X opX op2X eX e2X Y opY op2Y eY e2Y.
  - prove unpack_b_b_e_e_o (pack_b_b_e_e Y opY op2Y eY e2Y) (Phi X opX' op2X' eX e2X)
      = Phi X opX' op2X' eX e2X Y opY op2Y eY e2Y.
    exact unpack_b_b_e_e_o_eq (Phi X opX' op2X' eX e2X) Y opY op2Y eY e2Y (L1 opX' op2X').
  - prove Phi X opX' op2X' eX e2X Y opY op2Y eY e2Y
        = Phi X opX op2X eX e2X Y opY op2Y eY e2Y.
    apply prop_ext_2.
    + assume H.
      apply and5E (f :e Y :^: X) (forall x y :e X, f (opX' x y) = opY (f x) (f y)) (forall x y :e X, f (op2X' x y) = op2Y (f x) (f y)) (f eX = eY) (f e2X = e2Y) H.
      assume H1 H2 H3 H4 H5.
      prove f :e Y :^: X
         /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
         /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
         /\ f eX = eY
         /\ f e2X = e2Y.
      apply and5I.
      * exact H1.
      * let x. assume Hx. let y. assume Hy. rewrite HopX' x Hx y Hy.
        exact H2 x Hx y Hy.
      * let x. assume Hx. let y. assume Hy. rewrite Hop2X' x Hx y Hy.
        exact H3 x Hx y Hy.
      * exact H4.
      * exact H5.
    + assume H.
      apply and5E (f :e Y :^: X) (forall x y :e X, f (opX x y) = opY (f x) (f y)) (forall x y :e X, f (op2X x y) = op2Y (f x) (f y)) (f eX = eY) (f e2X = e2Y) H.
      assume H1 H2 H3 H4 H5.
      prove f :e Y :^: X
         /\ (forall x y :e X, f (opX' x y) = opY (f x) (f y))
         /\ (forall x y :e X, f (op2X' x y) = op2Y (f x) (f y))
         /\ f eX = eY
         /\ f e2X = e2Y.
      apply and5I.
      * exact H1.
      * let x. assume Hx. let y. assume Hy. rewrite <- HopX' x Hx y Hy.
        exact H2 x Hx y Hy.
      * let x. assume Hx. let y. assume Hy. rewrite <- Hop2X' x Hx y Hy.
        exact H3 x Hx y Hy.
      * exact H4.
      * exact H5.
  - symmetry.
    exact unpack_b_b_e_e_o_eq (Phi X opX op2X eX e2X) Y opY op2Y eY e2Y (L1 opX op2X).
}
transitivity PhiX X opX op2X eX e2X.
- exact unpack_b_b_e_e_o_eq PhiX X opX op2X eX e2X L2.
- prove unpack_b_b_e_e_o (pack_b_b_e_e Y opY op2Y eY e2Y) (Phi X opX op2X eX e2X)
      = Phi X opX op2X eX e2X Y opY op2Y eY e2Y.
  exact unpack_b_b_e_e_o_eq (Phi X opX op2X eX e2X) Y opY op2Y eY e2Y (L1 opX op2X).
Qed.

Theorem Hom_struct_b_b_r_e_e_pack :
 forall X Y, forall opX op2X opY op2Y:set -> set -> set,
 forall rX rY:set -> set -> prop,
 forall eX e2X eY e2Y f,
    (Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X opX op2X rX eX e2X) (pack_b_b_r_e_e Y opY op2Y rY eY e2Y) f)
  = (f :e Y :^: X
	   /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
	   /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
	   /\ (forall x y :e X, rX x y -> rY (f x) (f y))
	   /\ f eX = eY
	   /\ f e2X = e2Y).
let X Y opX op2X opY op2Y rX rY eX e2X eY e2Y f.
set Phi : set -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> prop) -> set -> set -> set -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> prop) -> set -> set -> prop
  := fun X opX op2X rX eX e2X Y opY op2Y rY eY e2Y =>
	      f :e Y :^: X
	   /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
	   /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
	   /\ (forall x y :e X, rX x y -> rY (f x) (f y))
	   /\ f eX = eY
	   /\ f e2X = e2Y.
set PhiX : set -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> prop) -> set -> set -> prop
 := fun X opX op2X rX eX e2X =>
      unpack_b_b_r_e_e_o (pack_b_b_r_e_e Y opY op2Y rY eY e2Y)
       (fun Y' opY op2Y rY eY e2Y => Phi X opX op2X rX eX e2X Y' opY op2Y rY eY e2Y).
prove unpack_b_b_r_e_e_o (pack_b_b_r_e_e X opX op2X rX eX e2X) PhiX
    = Phi X opX op2X rX eX e2X Y opY op2Y rY eY e2Y.
claim L1: forall opX op2X:set -> set -> set, forall rX:set -> set -> prop,
          forall opY':set -> set -> set, (forall x y :e Y, opY x y = opY' x y)
       -> forall op2Y':set -> set -> set, (forall x y :e Y, op2Y x y = op2Y' x y)
       -> forall rY':set -> set -> prop, (forall x y :e Y, rY x y <-> rY' x y)
       -> Phi X opX op2X rX eX e2X Y opY' op2Y' rY' eY e2Y = Phi X opX op2X rX eX e2X Y opY op2Y rY eY e2Y.
{ let opX op2X rX.
  let opY'. assume HopY'.
  let op2Y'. assume Hop2Y'.
  let rY'. assume HrY'.
  apply prop_ext_2.
  - assume H.
    apply and6E (f :e Y :^: X) (forall x y :e X, f (opX x y) = opY' (f x) (f y)) (forall x y :e X, f (op2X x y) = op2Y' (f x) (f y)) (forall x y :e X, rX x y -> rY' (f x) (f y)) (f eX = eY) (f e2X = e2Y) H.
    assume H1 H2 H3 H4 H5 H6.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
       /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
       /\ (forall x y :e X, rX x y -> rY (f x) (f y))
       /\ f eX = eY
       /\ f e2X = e2Y.
    apply and6I.
    + exact H1.
    + let x. assume Hx. let y. assume Hy. rewrite HopY' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H2 x Hx y Hy.
    + let x. assume Hx. let y. assume Hy. rewrite Hop2Y' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H3 x Hx y Hy.
    + let x. assume Hx. let y. assume Hy H7. apply iffER (rY (f x) (f y)) (rY' (f x) (f y)) (HrY' (f x) (Lf x Hx) (f y) (Lf y Hy)).
      exact H4 x Hx y Hy H7.
    + exact H5.
    + exact H6.
  - assume H.
    apply and6E (f :e Y :^: X) (forall x y :e X, f (opX x y) = opY (f x) (f y)) (forall x y :e X, f (op2X x y) = op2Y (f x) (f y)) (forall x y :e X, rX x y -> rY (f x) (f y)) (f eX = eY) (f e2X = e2Y) H.
    assume H1 H2 H3 H4 H5 H6.
    claim Lf: forall x :e X, f x :e Y.
    { let x. exact ap_Pi X (fun _ => Y) f x H1. }
    prove f :e Y :^: X
       /\ (forall x y :e X, f (opX x y) = opY' (f x) (f y))
       /\ (forall x y :e X, f (op2X x y) = op2Y' (f x) (f y))
       /\ (forall x y :e X, rX x y -> rY' (f x) (f y))
       /\ f eX = eY
       /\ f e2X = e2Y.
    apply and6I.
    + exact H1.
    + let x. assume Hx. let y. assume Hy. rewrite <- HopY' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H2 x Hx y Hy.
    + let x. assume Hx. let y. assume Hy. rewrite <- Hop2Y' (f x) (Lf x Hx) (f y) (Lf y Hy).
      exact H3 x Hx y Hy.
    + let x. assume Hx. let y. assume Hy H7. apply iffEL (rY (f x) (f y)) (rY' (f x) (f y)) (HrY' (f x) (Lf x Hx) (f y) (Lf y Hy)).
      exact H4 x Hx y Hy H7.
    + exact H5.
    + exact H6.
}
claim L2: forall opX':set -> set -> set, (forall x y :e X, opX x y = opX' x y)
       -> forall op2X':set -> set -> set, (forall x y :e X, op2X x y = op2X' x y)
       -> forall rX':set -> set -> prop, (forall x y :e X, rX x y <-> rX' x y)
       -> PhiX X opX' op2X' rX' eX e2X = PhiX X opX op2X rX eX e2X.
{ let opX'. assume HopX'.
  let op2X'. assume Hop2X'.
  let rX'. assume HrX'.
  prove PhiX X opX' op2X' rX' eX e2X = PhiX X opX op2X rX eX e2X.
  prove unpack_b_b_r_e_e_o (pack_b_b_r_e_e Y opY op2Y rY eY e2Y)
          (fun Y' opY op2Y rY eY e2Y => Phi X opX' op2X' rX' eX e2X Y' opY op2Y rY eY e2Y)
      = unpack_b_b_r_e_e_o (pack_b_b_r_e_e Y opY op2Y rY eY e2Y)
          (fun Y' opY op2Y rY eY e2Y => Phi X opX op2X rX eX e2X Y' opY op2Y rY eY e2Y).
  transitivity Phi X opX' op2X' rX' eX e2X Y opY op2Y rY eY e2Y,
               Phi X opX op2X rX eX e2X Y opY op2Y rY eY e2Y.
  - prove unpack_b_b_r_e_e_o (pack_b_b_r_e_e Y opY op2Y rY eY e2Y) (Phi X opX' op2X' rX' eX e2X)
      = Phi X opX' op2X' rX' eX e2X Y opY op2Y rY eY e2Y.
    exact unpack_b_b_r_e_e_o_eq (Phi X opX' op2X' rX' eX e2X) Y opY op2Y rY eY e2Y (L1 opX' op2X' rX').
  - prove Phi X opX' op2X' rX' eX e2X Y opY op2Y rY eY e2Y
        = Phi X opX op2X rX eX e2X Y opY op2Y rY eY e2Y.
    apply prop_ext_2.
    + assume H.
      apply and6E (f :e Y :^: X) (forall x y :e X, f (opX' x y) = opY (f x) (f y)) (forall x y :e X, f (op2X' x y) = op2Y (f x) (f y)) (forall x y :e X, rX' x y -> rY (f x) (f y)) (f eX = eY) (f e2X = e2Y) H.
      assume H1 H2 H3 H4 H5 H6.
      prove f :e Y :^: X
         /\ (forall x y :e X, f (opX x y) = opY (f x) (f y))
         /\ (forall x y :e X, f (op2X x y) = op2Y (f x) (f y))
         /\ (forall x y :e X, rX x y -> rY (f x) (f y))
         /\ f eX = eY
         /\ f e2X = e2Y.
      apply and6I.
      * exact H1.
      * let x. assume Hx. let y. assume Hy. rewrite HopX' x Hx y Hy.
        exact H2 x Hx y Hy.
      * let x. assume Hx. let y. assume Hy. rewrite Hop2X' x Hx y Hy.
        exact H3 x Hx y Hy.
      * let x. assume Hx. let y. assume Hy H7. apply H4 x Hx y Hy.
        apply iffEL (rX x y) (rX' x y) (HrX' x Hx y Hy).
        exact H7.
      * exact H5.
      * exact H6.
    + assume H.
      apply and6E (f :e Y :^: X) (forall x y :e X, f (opX x y) = opY (f x) (f y)) (forall x y :e X, f (op2X x y) = op2Y (f x) (f y)) (forall x y :e X, rX x y -> rY (f x) (f y)) (f eX = eY) (f e2X = e2Y) H.
      assume H1 H2 H3 H4 H5 H6.
      prove f :e Y :^: X
         /\ (forall x y :e X, f (opX' x y) = opY (f x) (f y))
         /\ (forall x y :e X, f (op2X' x y) = op2Y (f x) (f y))
         /\ (forall x y :e X, rX' x y -> rY (f x) (f y))
         /\ f eX = eY
         /\ f e2X = e2Y.
      apply and6I.
      * exact H1.
      * let x. assume Hx. let y. assume Hy. rewrite <- HopX' x Hx y Hy.
        exact H2 x Hx y Hy.
      * let x. assume Hx. let y. assume Hy. rewrite <- Hop2X' x Hx y Hy.
        exact H3 x Hx y Hy.
      * let x. assume Hx. let y. assume Hy H7. apply H4 x Hx y Hy.
        apply iffER (rX x y) (rX' x y) (HrX' x Hx y Hy).
	exact H7.
      * exact H5.
      * exact H6.
  - symmetry.
    exact unpack_b_b_r_e_e_o_eq (Phi X opX op2X rX eX e2X) Y opY op2Y rY eY e2Y (L1 opX op2X rX).
}
transitivity PhiX X opX op2X rX eX e2X.
- exact unpack_b_b_r_e_e_o_eq PhiX X opX op2X rX eX e2X L2.
- prove unpack_b_b_r_e_e_o (pack_b_b_r_e_e Y opY op2Y rY eY e2Y) (Phi X opX op2X rX eX e2X)
      = Phi X opX op2X rX eX e2X Y opY op2Y rY eY e2Y.
  exact unpack_b_b_r_e_e_o_eq (Phi X opX op2X rX eX e2X) Y opY op2Y rY eY e2Y (L1 opX op2X rX).
Qed.

Section MetaCatStruct.

Variable Obj: set -> prop.

Theorem MetaCat_struct_e_gen :
    (forall X, Obj X -> struct_e X)
 -> MetaCat Obj Hom_struct_e (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f).
assume HO.
apply MetaCatConcrete Obj (fun X => X 0) Hom_struct_e.
- let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_e u Y f -> f :e Y 0 :^: u 0).
  let X' eX. assume HeX.
  apply HO Y HY (fun u => Hom_struct_e (pack_e X' eX) u f -> f :e u 0 :^: pack_e X' eX 0).
  let Y' eY. assume HeY.
  prove Hom_struct_e (pack_e X' eX) (pack_e Y' eY) f -> f :e pack_e Y' eY 0 :^: pack_e X' eX 0.
  rewrite Hom_struct_e_pack.
  assume Hf: f :e Y' :^: X' /\ f eX = eY.
  apply Hf. assume Hf1 Hf2.
  rewrite <- pack_e_0_eq2. rewrite <- pack_e_0_eq2.
  exact Hf1.
- let X. assume HX.
  apply HO X HX (fun u => Hom_struct_e u u (lam_id (u 0))).
  let X' eX. assume HeX.
  prove Hom_struct_e (pack_e X' eX) (pack_e X' eX) (lam_id (pack_e X' eX 0)).
  rewrite <- pack_e_0_eq2. rewrite Hom_struct_e_pack.
  prove lam_id X' :e X' :^: X' /\ lam_id X' eX = eX.
  apply andI.
  + exact lam_id_exp_In X'.
  + prove (fun x :e X' => x) eX = eX.
    exact beta X' (fun x => x) eX HeX.
- let X Y Z f g.
  assume HX HY HZ.
  apply HO X HX (fun u => Hom_struct_e u Y f -> Hom_struct_e Y Z g -> Hom_struct_e u Z (lam_comp (u 0) g f)).
  let X' eX. assume HeX.
  prove Hom_struct_e (pack_e X' eX) Y f -> Hom_struct_e Y Z g -> Hom_struct_e (pack_e X' eX) Z (lam_comp (pack_e X' eX 0) g f).
  rewrite <- pack_e_0_eq2.
  prove Hom_struct_e (pack_e X' eX) Y f -> Hom_struct_e Y Z g -> Hom_struct_e (pack_e X' eX) Z (lam_comp X' g f).
  apply HO Y HY (fun u => Hom_struct_e (pack_e X' eX) u f -> Hom_struct_e u Z g -> Hom_struct_e (pack_e X' eX) Z (lam_comp X' g f)).
  let Y' eY. assume HeY.
  prove Hom_struct_e (pack_e X' eX) (pack_e Y' eY) f -> Hom_struct_e (pack_e Y' eY) Z g -> Hom_struct_e (pack_e X' eX) Z (lam_comp X' g f).
  rewrite Hom_struct_e_pack.
  assume Hf: f :e Y' :^: X' /\ f eX = eY.
  apply HO Z HZ (fun u => Hom_struct_e (pack_e Y' eY) u g -> Hom_struct_e (pack_e X' eX) u (lam_comp X' g f)).
  let Z' eZ. assume HeZ.
  prove Hom_struct_e (pack_e Y' eY) (pack_e Z' eZ) g -> Hom_struct_e (pack_e X' eX) (pack_e Z' eZ) (lam_comp X' g f).
  rewrite Hom_struct_e_pack.
  rewrite Hom_struct_e_pack.
  assume Hg: g :e Z' :^: Y' /\ g eY = eZ.
  apply Hf. assume Hf1 Hf2.
  apply Hg. assume Hg1 Hg2.
  prove lam_comp X' g f :e Z' :^: X' /\ lam_comp X' g f eX = eZ.
  apply andI.
  + exact lam_comp_exp_In X' Y' Z' f Hf1 g Hg1.
  + prove (fun x :e X' => g (f x)) eX = eZ.
    rewrite beta X' (fun x => g (f x)) eX HeX.
    prove g (f eX) = eZ.
    rewrite Hf2. exact Hg2.
Qed.

Theorem MetaCat_struct_e_Forgetful_gen :
    (forall X, Obj X -> struct_e X)
 -> MetaFunctor Obj Hom_struct_e (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f)
                (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
		(fun X => X 0) (fun X Y f => f).
assume HO.
claim L1: forall X Y f, Obj X -> Obj Y -> Hom_struct_e X Y f -> f :e Y 0 :^: X 0.
{ let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_e u Y f -> f :e Y 0 :^: u 0).
  let X' eX. assume HeX.
  apply HO Y HY (fun u => Hom_struct_e (pack_e X' eX) u f -> f :e u 0 :^: pack_e X' eX 0).
  let Y' eY. assume HeY.
  prove Hom_struct_e (pack_e X' eX) (pack_e Y' eY) f -> f :e pack_e Y' eY 0 :^: pack_e X' eX 0.
  rewrite Hom_struct_e_pack.
  assume Hf.
  rewrite <- pack_e_0_eq2. rewrite <- pack_e_0_eq2.
  apply Hf. assume Hf1 _. exact Hf1.
}
exact MetaCatConcreteForgetful Obj (fun X => X 0) Hom_struct_e L1.
Qed.

Theorem MetaCat_struct_p_gen :
    (forall X, Obj X -> struct_p X)
 -> MetaCat Obj Hom_struct_p (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f).
assume HO.
apply MetaCatConcrete Obj (fun X => X 0) Hom_struct_p.
- let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_p u Y f -> f :e Y 0 :^: u 0).
  let X' pX.
  apply HO Y HY (fun u => Hom_struct_p (pack_p X' pX) u f -> f :e u 0 :^: pack_p X' pX 0).
  let Y' pY.
  prove Hom_struct_p (pack_p X' pX) (pack_p Y' pY) f -> f :e pack_p Y' pY 0 :^: pack_p X' pX 0.
  rewrite Hom_struct_p_pack.
  assume Hf: f :e Y' :^: X' /\ (forall x :e X', pX x -> pY (f x)).
  apply Hf. assume Hf1 Hf2.
  rewrite <- pack_p_0_eq2. rewrite <- pack_p_0_eq2.
  exact Hf1.
- let X. assume HX.
  apply HO X HX (fun u => Hom_struct_p u u (lam_id (u 0))).
  let X' pX.
  prove Hom_struct_p (pack_p X' pX) (pack_p X' pX) (lam_id (pack_p X' pX 0)).
  rewrite <- pack_p_0_eq2. rewrite Hom_struct_p_pack.
  prove lam_id X' :e X' :^: X' /\ (forall x :e X', pX x -> pX (lam_id X' x)).
  apply andI.
  + exact lam_id_exp_In X'.
  + let x. assume Hx Hx2.
    prove pX ((fun x :e X' => x) x).
    rewrite beta X' (fun x => x) x Hx.
    exact Hx2.
- let X Y Z f g.
  assume HX HY HZ.
  apply HO X HX (fun u => Hom_struct_p u Y f -> Hom_struct_p Y Z g -> Hom_struct_p u Z (lam_comp (u 0) g f)).
  let X' pX.
  prove Hom_struct_p (pack_p X' pX) Y f -> Hom_struct_p Y Z g -> Hom_struct_p (pack_p X' pX) Z (lam_comp (pack_p X' pX 0) g f).
  rewrite <- pack_p_0_eq2.
  prove Hom_struct_p (pack_p X' pX) Y f -> Hom_struct_p Y Z g -> Hom_struct_p (pack_p X' pX) Z (lam_comp X' g f).
  apply HO Y HY (fun u => Hom_struct_p (pack_p X' pX) u f -> Hom_struct_p u Z g -> Hom_struct_p (pack_p X' pX) Z (lam_comp X' g f)).
  let Y' pY.
  prove Hom_struct_p (pack_p X' pX) (pack_p Y' pY) f -> Hom_struct_p (pack_p Y' pY) Z g -> Hom_struct_p (pack_p X' pX) Z (lam_comp X' g f).
  rewrite Hom_struct_p_pack.
  assume Hf: f :e Y' :^: X' /\ (forall x :e X', pX x -> pY (f x)).
  apply HO Z HZ (fun u => Hom_struct_p (pack_p Y' pY) u g -> Hom_struct_p (pack_p X' pX) u (lam_comp X' g f)).
  let Z' pZ.
  prove Hom_struct_p (pack_p Y' pY) (pack_p Z' pZ) g -> Hom_struct_p (pack_p X' pX) (pack_p Z' pZ) (lam_comp X' g f).
  rewrite Hom_struct_p_pack.
  rewrite Hom_struct_p_pack.
  assume Hg: g :e Z' :^: Y' /\ (forall y :e Y', pY y -> pZ (g y)).
  apply Hf. assume Hf1 Hf2.
  apply Hg. assume Hg1 Hg2.
  prove lam_comp X' g f :e Z' :^: X' /\ (forall x :e X', pX x -> pZ (lam_comp X' g f x)).
  apply andI.
  + exact lam_comp_exp_In X' Y' Z' f Hf1 g Hg1.
  + let x. assume Hx Hx2.
    prove pZ ((fun x :e X' => g (f x)) x).
    rewrite beta X' (fun x => g (f x)) x Hx.
    prove pZ (g (f x)).
    apply Hg2 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx).
    apply Hf2 x Hx.
    exact Hx2.
Qed.

Theorem MetaCat_struct_p_Forgetful_gen :
    (forall X, Obj X -> struct_p X)
 -> MetaFunctor Obj Hom_struct_p (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f)
                (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
		(fun X => X 0) (fun X Y f => f).
assume HO.
claim L1: forall X Y f, Obj X -> Obj Y -> Hom_struct_p X Y f -> f :e Y 0 :^: X 0.
{ let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_p u Y f -> f :e Y 0 :^: u 0).
  let X' pX.
  apply HO Y HY (fun u => Hom_struct_p (pack_p X' pX) u f -> f :e u 0 :^: pack_p X' pX 0).
  let Y' pY.
  prove Hom_struct_p (pack_p X' pX) (pack_p Y' pY) f -> f :e pack_p Y' pY 0 :^: pack_p X' pX 0.
  rewrite Hom_struct_p_pack.
  assume Hf.
  rewrite <- pack_p_0_eq2. rewrite <- pack_p_0_eq2.
  apply Hf. assume Hf1 _. exact Hf1.
}
exact MetaCatConcreteForgetful Obj (fun X => X 0) Hom_struct_p L1.
Qed.

Theorem MetaCat_struct_r_gen :
    (forall X, Obj X -> struct_r X)
 -> MetaCat Obj Hom_struct_r (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f).
assume HO.
apply MetaCatConcrete Obj (fun X => X 0) Hom_struct_r.
- let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_r u Y f -> f :e Y 0 :^: u 0).
  let X' rX.
  apply HO Y HY (fun u => Hom_struct_r (pack_r X' rX) u f -> f :e u 0 :^: pack_r X' rX 0).
  let Y' rY.
  prove Hom_struct_r (pack_r X' rX) (pack_r Y' rY) f -> f :e pack_r Y' rY 0 :^: pack_r X' rX 0.
  rewrite Hom_struct_r_pack.
  assume Hf: f :e Y' :^: X' /\ (forall x x' :e X', rX x x' -> rY (f x) (f x')).
  apply Hf. assume Hf1 Hf2.
  rewrite <- pack_r_0_eq2. rewrite <- pack_r_0_eq2.
  exact Hf1.
- let X. assume HX.
  apply HO X HX (fun u => Hom_struct_r u u (lam_id (u 0))).
  let X' rX.
  prove Hom_struct_r (pack_r X' rX) (pack_r X' rX) (lam_id (pack_r X' rX 0)).
  rewrite <- pack_r_0_eq2. rewrite Hom_struct_r_pack.
  prove lam_id X' :e X' :^: X' /\ (forall x x' :e X', rX x x' -> rX (lam_id X' x) (lam_id X' x')).
  apply andI.
  + exact lam_id_exp_In X'.
  + let x. assume Hx. let x'. assume Hx' Hx2.
    prove rX ((fun x :e X' => x) x) ((fun x :e X' => x) x').
    rewrite beta X' (fun x => x) x Hx.
    rewrite beta X' (fun x => x) x' Hx'.
    exact Hx2.
- let X Y Z f g.
  assume HX HY HZ.
  apply HO X HX (fun u => Hom_struct_r u Y f -> Hom_struct_r Y Z g -> Hom_struct_r u Z (lam_comp (u 0) g f)).
  let X' rX.
  prove Hom_struct_r (pack_r X' rX) Y f -> Hom_struct_r Y Z g -> Hom_struct_r (pack_r X' rX) Z (lam_comp (pack_r X' rX 0) g f).
  rewrite <- pack_r_0_eq2.
  prove Hom_struct_r (pack_r X' rX) Y f -> Hom_struct_r Y Z g -> Hom_struct_r (pack_r X' rX) Z (lam_comp X' g f).
  apply HO Y HY (fun u => Hom_struct_r (pack_r X' rX) u f -> Hom_struct_r u Z g -> Hom_struct_r (pack_r X' rX) Z (lam_comp X' g f)).
  let Y' rY.
  prove Hom_struct_r (pack_r X' rX) (pack_r Y' rY) f -> Hom_struct_r (pack_r Y' rY) Z g -> Hom_struct_r (pack_r X' rX) Z (lam_comp X' g f).
  rewrite Hom_struct_r_pack.
  assume Hf: f :e Y' :^: X' /\ (forall x x' :e X', rX x x' -> rY (f x) (f x')).
  apply HO Z HZ (fun u => Hom_struct_r (pack_r Y' rY) u g -> Hom_struct_r (pack_r X' rX) u (lam_comp X' g f)).
  let Z' rZ.
  prove Hom_struct_r (pack_r Y' rY) (pack_r Z' rZ) g -> Hom_struct_r (pack_r X' rX) (pack_r Z' rZ) (lam_comp X' g f).
  rewrite Hom_struct_r_pack.
  rewrite Hom_struct_r_pack.
  assume Hg: g :e Z' :^: Y' /\ (forall y y' :e Y', rY y y' -> rZ (g y) (g y')).
  apply Hf. assume Hf1 Hf2.
  apply Hg. assume Hg1 Hg2.
  prove lam_comp X' g f :e Z' :^: X' /\ (forall x x' :e X', rX x x' -> rZ (lam_comp X' g f x) (lam_comp X' g f x')).
  apply andI.
  + exact lam_comp_exp_In X' Y' Z' f Hf1 g Hg1.
  + let x. assume Hx. let x'. assume Hx' Hx2.
    prove rZ ((fun x :e X' => g (f x)) x) ((fun x :e X' => g (f x)) x').
    rewrite beta X' (fun x => g (f x)) x Hx.
    rewrite beta X' (fun x => g (f x)) x' Hx'.
    prove rZ (g (f x)) (g (f x')).
    apply Hg2 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx) (f x') (ap_Pi X' (fun _ => Y') f x' Hf1 Hx').
    apply Hf2 x Hx x' Hx'.
    exact Hx2.
Qed.

Theorem MetaCat_struct_r_Forgetful_gen :
    (forall X, Obj X -> struct_r X)
 -> MetaFunctor Obj Hom_struct_r (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f)
                (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
		(fun X => X 0) (fun X Y f => f).
assume HO.
claim L1: forall X Y f, Obj X -> Obj Y -> Hom_struct_r X Y f -> f :e Y 0 :^: X 0.
{ let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_r u Y f -> f :e Y 0 :^: u 0).
  let X' rX.
  apply HO Y HY (fun u => Hom_struct_r (pack_r X' rX) u f -> f :e u 0 :^: pack_r X' rX 0).
  let Y' rY.
  prove Hom_struct_r (pack_r X' rX) (pack_r Y' rY) f -> f :e pack_r Y' rY 0 :^: pack_r X' rX 0.
  rewrite Hom_struct_r_pack.
  assume Hf.
  rewrite <- pack_r_0_eq2. rewrite <- pack_r_0_eq2.
  apply Hf. assume Hf1 _. exact Hf1.
}
exact MetaCatConcreteForgetful Obj (fun X => X 0) Hom_struct_r L1.
Qed.

Theorem MetaCat_struct_u_gen :
    (forall X, Obj X -> struct_u X)
 -> MetaCat Obj Hom_struct_u (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f).
assume HO.
apply MetaCatConcrete Obj (fun X => X 0) Hom_struct_u.
- let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_u u Y f -> f :e Y 0 :^: u 0).
  let X' uX. assume HuX.
  apply HO Y HY (fun u => Hom_struct_u (pack_u X' uX) u f -> f :e u 0 :^: pack_u X' uX 0).
  let Y' uY. assume HuY.
  prove Hom_struct_u (pack_u X' uX) (pack_u Y' uY) f -> f :e pack_u Y' uY 0 :^: pack_u X' uX 0.
  rewrite Hom_struct_u_pack.
  assume Hf: f :e Y' :^: X' /\ (forall x :e X', f (uX x) = uY (f x)).
  apply Hf. assume Hf1 Hf2.
  rewrite <- pack_u_0_eq2. rewrite <- pack_u_0_eq2.
  exact Hf1.
- let X. assume HX.
  apply HO X HX (fun u => Hom_struct_u u u (lam_id (u 0))).
  let X' uX. assume HuX.
  prove Hom_struct_u (pack_u X' uX) (pack_u X' uX) (lam_id (pack_u X' uX 0)).
  rewrite <- pack_u_0_eq2. rewrite Hom_struct_u_pack.
  prove lam_id X' :e X' :^: X' /\ (forall x :e X', lam_id X' (uX x) = uX (lam_id X' x)).
  apply andI.
  + exact lam_id_exp_In X'.
  + let x. assume Hx.
    prove lam_id X' (uX x) = uX ((fun x :e X' => x) x).
    rewrite beta X' (fun x => x) x Hx.
    exact beta X' (fun x => x) (uX x) (HuX x Hx).
- let X Y Z f g.
  assume HX HY HZ.
  apply HO X HX (fun u => Hom_struct_u u Y f -> Hom_struct_u Y Z g -> Hom_struct_u u Z (lam_comp (u 0) g f)).
  let X' uX. assume HuX.
  prove Hom_struct_u (pack_u X' uX) Y f -> Hom_struct_u Y Z g -> Hom_struct_u (pack_u X' uX) Z (lam_comp (pack_u X' uX 0) g f).
  rewrite <- pack_u_0_eq2.
  prove Hom_struct_u (pack_u X' uX) Y f -> Hom_struct_u Y Z g -> Hom_struct_u (pack_u X' uX) Z (lam_comp X' g f).
  apply HO Y HY (fun u => Hom_struct_u (pack_u X' uX) u f -> Hom_struct_u u Z g -> Hom_struct_u (pack_u X' uX) Z (lam_comp X' g f)).
  let Y' uY. assume HuY.
  prove Hom_struct_u (pack_u X' uX) (pack_u Y' uY) f -> Hom_struct_u (pack_u Y' uY) Z g -> Hom_struct_u (pack_u X' uX) Z (lam_comp X' g f).
  rewrite Hom_struct_u_pack.
  assume Hf: f :e Y' :^: X' /\ (forall x :e X', f (uX x) = uY (f x)).
  apply HO Z HZ (fun u => Hom_struct_u (pack_u Y' uY) u g -> Hom_struct_u (pack_u X' uX) u (lam_comp X' g f)).
  let Z' uZ. assume HuZ.
  prove Hom_struct_u (pack_u Y' uY) (pack_u Z' uZ) g -> Hom_struct_u (pack_u X' uX) (pack_u Z' uZ) (lam_comp X' g f).
  rewrite Hom_struct_u_pack.
  rewrite Hom_struct_u_pack.
  assume Hg: g :e Z' :^: Y' /\ (forall y :e Y', g (uY y) = uZ (g y)).
  apply Hf. assume Hf1 Hf2.
  apply Hg. assume Hg1 Hg2.
  prove lam_comp X' g f :e Z' :^: X' /\ (forall x :e X', lam_comp X' g f (uX x) = uZ (lam_comp X' g f x)).
  apply andI.
  + exact lam_comp_exp_In X' Y' Z' f Hf1 g Hg1.
  + let x. assume Hx.
    prove lam_comp X' g f (uX x) = uZ ((fun x :e X' => g (f x)) x).
    rewrite beta X' (fun x => g (f x)) x Hx.
    prove (fun x :e X' => g (f x)) (uX x) = uZ (g (f x)).
    rewrite beta X' (fun x => g (f x)) (uX x) (HuX x Hx).
    prove g (f (uX x)) = uZ (g (f x)).
    rewrite <- Hg2 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx).
    prove g (f (uX x)) = g (uY (f x)).
    f_equal.
    exact Hf2 x Hx.
Qed.

Theorem MetaCat_struct_u_Forgetful_gen :
    (forall X, Obj X -> struct_u X)
 -> MetaFunctor Obj Hom_struct_u (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f)
                (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
		(fun X => X 0) (fun X Y f => f).
assume HO.
claim L1: forall X Y f, Obj X -> Obj Y -> Hom_struct_u X Y f -> f :e Y 0 :^: X 0.
{ let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_u u Y f -> f :e Y 0 :^: u 0).
  let X' uX. assume HuX.
  apply HO Y HY (fun u => Hom_struct_u (pack_u X' uX) u f -> f :e u 0 :^: pack_u X' uX 0).
  let Y' uY. assume HuY.
  prove Hom_struct_u (pack_u X' uX) (pack_u Y' uY) f -> f :e pack_u Y' uY 0 :^: pack_u X' uX 0.
  rewrite Hom_struct_u_pack.
  assume Hf.
  rewrite <- pack_u_0_eq2. rewrite <- pack_u_0_eq2.
  apply Hf. assume Hf1 _. exact Hf1.
}
exact MetaCatConcreteForgetful Obj (fun X => X 0) Hom_struct_u L1.
Qed.

Theorem MetaCat_struct_b_gen :
    (forall X, Obj X -> struct_b X)
 -> MetaCat Obj Hom_struct_b (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f).
assume HO.
apply MetaCatConcrete Obj (fun X => X 0) Hom_struct_b.
- let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_b u Y f -> f :e Y 0 :^: u 0).
  let X' bX. assume HbX.
  apply HO Y HY (fun u => Hom_struct_b (pack_b X' bX) u f -> f :e u 0 :^: pack_b X' bX 0).
  let Y' bY. assume HbY.
  prove Hom_struct_b (pack_b X' bX) (pack_b Y' bY) f -> f :e pack_b Y' bY 0 :^: pack_b X' bX 0.
  rewrite Hom_struct_b_pack.
  assume Hf: f :e Y' :^: X' /\ (forall x x' :e X', f (bX x x') = bY (f x) (f x')).
  apply Hf. assume Hf1 Hf2.
  rewrite <- pack_b_0_eq2. rewrite <- pack_b_0_eq2.
  exact Hf1.
- let X. assume HX.
  apply HO X HX (fun u => Hom_struct_b u u (lam_id (u 0))).
  let X' bX. assume HbX.
  prove Hom_struct_b (pack_b X' bX) (pack_b X' bX) (lam_id (pack_b X' bX 0)).
  rewrite <- pack_b_0_eq2. rewrite Hom_struct_b_pack.
  prove lam_id X' :e X' :^: X' /\ (forall x x' :e X', lam_id X' (bX x x') = bX (lam_id X' x) (lam_id X' x')).
  apply andI.
  + exact lam_id_exp_In X'.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_id X' (bX x x') = bX ((fun x :e X' => x) x) ((fun x :e X' => x) x').
    rewrite beta X' (fun x => x) x Hx.
    rewrite beta X' (fun x => x) x' Hx'.
    exact beta X' (fun x => x) (bX x x') (HbX x Hx x' Hx').
- let X Y Z f g.
  assume HX HY HZ.
  apply HO X HX (fun u => Hom_struct_b u Y f -> Hom_struct_b Y Z g -> Hom_struct_b u Z (lam_comp (u 0) g f)).
  let X' bX. assume HbX.
  prove Hom_struct_b (pack_b X' bX) Y f -> Hom_struct_b Y Z g -> Hom_struct_b (pack_b X' bX) Z (lam_comp (pack_b X' bX 0) g f).
  rewrite <- pack_b_0_eq2.
  prove Hom_struct_b (pack_b X' bX) Y f -> Hom_struct_b Y Z g -> Hom_struct_b (pack_b X' bX) Z (lam_comp X' g f).
  apply HO Y HY (fun u => Hom_struct_b (pack_b X' bX) u f -> Hom_struct_b u Z g -> Hom_struct_b (pack_b X' bX) Z (lam_comp X' g f)).
  let Y' bY. assume HbY.
  prove Hom_struct_b (pack_b X' bX) (pack_b Y' bY) f -> Hom_struct_b (pack_b Y' bY) Z g -> Hom_struct_b (pack_b X' bX) Z (lam_comp X' g f).
  rewrite Hom_struct_b_pack.
  assume Hf: f :e Y' :^: X' /\ (forall x x' :e X', f (bX x x') = bY (f x) (f x')).
  apply HO Z HZ (fun u => Hom_struct_b (pack_b Y' bY) u g -> Hom_struct_b (pack_b X' bX) u (lam_comp X' g f)).
  let Z' bZ. assume HbZ.
  prove Hom_struct_b (pack_b Y' bY) (pack_b Z' bZ) g -> Hom_struct_b (pack_b X' bX) (pack_b Z' bZ) (lam_comp X' g f).
  rewrite Hom_struct_b_pack.
  rewrite Hom_struct_b_pack.
  assume Hg: g :e Z' :^: Y' /\ (forall y y' :e Y', g (bY y y') = bZ (g y) (g y')).
  apply Hf. assume Hf1 Hf2.
  apply Hg. assume Hg1 Hg2.
  prove lam_comp X' g f :e Z' :^: X' /\ (forall x x' :e X', lam_comp X' g f (bX x x') = bZ (lam_comp X' g f x) (lam_comp X' g f x')).
  apply andI.
  + exact lam_comp_exp_In X' Y' Z' f Hf1 g Hg1.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_comp X' g f (bX x x') = bZ ((fun x :e X' => g (f x)) x) ((fun x :e X' => g (f x)) x').
    rewrite beta X' (fun x => g (f x)) x Hx.
    rewrite beta X' (fun x => g (f x)) x' Hx'.
    prove (fun x :e X' => g (f x)) (bX x x') = bZ (g (f x)) (g (f x')).
    rewrite beta X' (fun x => g (f x)) (bX x x') (HbX x Hx x' Hx').
    prove g (f (bX x x')) = bZ (g (f x)) (g (f x')).
    rewrite <- Hg2 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx) (f x') (ap_Pi X' (fun _ => Y') f x' Hf1 Hx').
    prove g (f (bX x x')) = g (bY (f x) (f x')).
    f_equal.
    exact Hf2 x Hx x' Hx'.
Qed.

Theorem MetaCat_struct_b_Forgetful_gen :
    (forall X, Obj X -> struct_b X)
 -> MetaFunctor Obj Hom_struct_b (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f)
                (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
		(fun X => X 0) (fun X Y f => f).
assume HO.
claim L1: forall X Y f, Obj X -> Obj Y -> Hom_struct_b X Y f -> f :e Y 0 :^: X 0.
{ let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_b u Y f -> f :e Y 0 :^: u 0).
  let X' bX. assume HbX.
  apply HO Y HY (fun u => Hom_struct_b (pack_b X' bX) u f -> f :e u 0 :^: pack_b X' bX 0).
  let Y' bY. assume HbY.
  prove Hom_struct_b (pack_b X' bX) (pack_b Y' bY) f -> f :e pack_b Y' bY 0 :^: pack_b X' bX 0.
  rewrite Hom_struct_b_pack.
  assume Hf.
  rewrite <- pack_b_0_eq2. rewrite <- pack_b_0_eq2.
  apply Hf. assume Hf1 _. exact Hf1.
}
exact MetaCatConcreteForgetful Obj (fun X => X 0) Hom_struct_b L1.
Qed.

Theorem MetaCat_struct_c_gen :
    (forall X, Obj X -> struct_c X)
 -> MetaCat Obj Hom_struct_c (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f).
assume HO.
apply MetaCatConcrete Obj (fun X => X 0) Hom_struct_c.
- let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_c u Y f -> f :e Y 0 :^: u 0).
  let X' CX.
  apply HO Y HY (fun u => Hom_struct_c (pack_c X' CX) u f -> f :e u 0 :^: pack_c X' CX 0).
  let Y' CY.
  prove Hom_struct_c (pack_c X' CX) (pack_c Y' CY) f -> f :e pack_c Y' CY 0 :^: pack_c X' CX 0.
  rewrite Hom_struct_c_pack.
  assume Hf: f :e Y' :^: X' /\ (forall U:set -> prop, (forall y, U y -> y :e Y') -> CY U -> CX (fun x => x :e X' /\ U (f x))).
  apply Hf. assume Hf1 Hf2.
  rewrite <- pack_c_0_eq2. rewrite <- pack_c_0_eq2.
  exact Hf1.
- let X. assume HX.
  apply HO X HX (fun u => Hom_struct_c u u (lam_id (u 0))).
  let X' CX.
  prove Hom_struct_c (pack_c X' CX) (pack_c X' CX) (lam_id (pack_c X' CX 0)).
  rewrite <- pack_c_0_eq2. rewrite Hom_struct_c_pack.
  prove lam_id X' :e X' :^: X' /\ (forall U:set -> prop, (forall y, U y -> y :e X') -> CX U -> CX (fun x => x :e X' /\ U (lam_id X' x))).
  apply andI.
  + exact lam_id_exp_In X'.
  + let U. assume HU1 HU2.
    claim L1: U = (fun x => x :e X' /\ U (lam_id X' x)).
    { apply pred_ext_2.
      - let x. assume Hx. prove x :e X' /\ U (lam_id X' x).
        apply andI.
	+ exact HU1 x Hx.
	+ prove U ((fun x :e X' => x) x).
	  rewrite beta X' (fun x => x) x (HU1 x Hx).
	  exact Hx.
      - let x. assume Hx. apply Hx. assume Hx1.
        prove U ((fun x :e X' => x) x) -> U x.
	rewrite beta X' (fun x => x) x Hx1.
	assume Hx2. exact Hx2.
    }
    rewrite <- L1.
    exact HU2.
- let X Y Z f g.
  assume HX HY HZ.
  apply HO X HX (fun u => Hom_struct_c u Y f -> Hom_struct_c Y Z g -> Hom_struct_c u Z (lam_comp (u 0) g f)).
  let X' CX.
  prove Hom_struct_c (pack_c X' CX) Y f -> Hom_struct_c Y Z g -> Hom_struct_c (pack_c X' CX) Z (lam_comp (pack_c X' CX 0) g f).
  rewrite <- pack_c_0_eq2.
  prove Hom_struct_c (pack_c X' CX) Y f -> Hom_struct_c Y Z g -> Hom_struct_c (pack_c X' CX) Z (lam_comp X' g f).
  apply HO Y HY (fun u => Hom_struct_c (pack_c X' CX) u f -> Hom_struct_c u Z g -> Hom_struct_c (pack_c X' CX) Z (lam_comp X' g f)).
  let Y' CY.
  prove Hom_struct_c (pack_c X' CX) (pack_c Y' CY) f -> Hom_struct_c (pack_c Y' CY) Z g -> Hom_struct_c (pack_c X' CX) Z (lam_comp X' g f).
  rewrite Hom_struct_c_pack.
  assume Hf: f :e Y' :^: X' /\ (forall U:set -> prop, (forall y, U y -> y :e Y') -> CY U -> CX (fun x => x :e X' /\ U (f x))).
  apply HO Z HZ (fun u => Hom_struct_c (pack_c Y' CY) u g -> Hom_struct_c (pack_c X' CX) u (lam_comp X' g f)).
  let Z' CZ.
  prove Hom_struct_c (pack_c Y' CY) (pack_c Z' CZ) g -> Hom_struct_c (pack_c X' CX) (pack_c Z' CZ) (lam_comp X' g f).
  rewrite Hom_struct_c_pack.
  rewrite Hom_struct_c_pack.
  assume Hg: g :e Z' :^: Y' /\ (forall U:set -> prop, (forall z, U z -> z :e Z') -> CZ U -> CY (fun y => y :e Y' /\ U (g y))).
  apply Hf. assume Hf1 Hf2.
  apply Hg. assume Hg1 Hg2.
  prove lam_comp X' g f :e Z' :^: X' /\ (forall U:set -> prop, (forall z, U z -> z :e Z') -> CZ U -> CX (fun x => x :e X' /\ U (lam_comp X' g f x))).
  apply andI.
  + exact lam_comp_exp_In X' Y' Z' f Hf1 g Hg1.
  + let U.
    assume HU1: forall z, U z -> z :e Z'.
    assume HU2: CZ U.
    claim L2: CY (fun y => y :e Y' /\ U (g y)).
    { exact Hg2 U HU1 HU2. }
    claim L3: forall y, y :e Y' /\ U (g y) -> y :e Y'.
    { let y. exact andEL (y :e Y') (U (g y)). }
    claim L4: CX (fun x => x :e X' /\ (f x :e Y' /\ U (g (f x)))).
    { exact Hf2 (fun y => y :e Y' /\ U (g y)) L3 L2. }
    claim L5: (fun x:set => x :e X' /\ (f x :e Y' /\ U (g (f x))))
            = (fun x:set => x :e X' /\ U (lam_comp X' g f x)).
    { apply pred_ext_2.
      - let x. assume Hx. apply Hx. assume Hx1 Hx23. apply Hx23. assume Hx2 Hx3.
        prove x :e X' /\ U (lam_comp X' g f x).
        apply andI.
	+ exact Hx1.
	+ prove U ((fun x :e X' => g (f x)) x).
	  rewrite beta X' (fun x => g (f x)) x Hx1.
	  exact Hx3.
      - let x. assume Hx. apply Hx. assume Hx1.
	prove U ((fun x :e X' => g (f x)) x) -> x :e X' /\ (f x :e Y' /\ U (g (f x))).
        rewrite beta X' (fun x => g (f x)) x Hx1.
        assume Hx2.
	prove x :e X' /\ (f x :e Y' /\ U (g (f x))).
        apply andI.
	+ exact Hx1.
	+ apply andI.
	  * exact ap_Pi X' (fun _ => Y') f x Hf1 Hx1.
	  * exact Hx2.
    }
    rewrite <- L5.
    exact L4.
Qed.

Theorem MetaCat_struct_c_Forgetful_gen :
    (forall X, Obj X -> struct_c X)
 -> MetaFunctor Obj Hom_struct_c (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f)
                (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
		(fun X => X 0) (fun X Y f => f).
assume HO.
claim L1: forall X Y f, Obj X -> Obj Y -> Hom_struct_c X Y f -> f :e Y 0 :^: X 0.
{ let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_c u Y f -> f :e Y 0 :^: u 0).
  let X' CX.
  apply HO Y HY (fun u => Hom_struct_c (pack_c X' CX) u f -> f :e u 0 :^: pack_c X' CX 0).
  let Y' CY.
  prove Hom_struct_c (pack_c X' CX) (pack_c Y' CY) f -> f :e pack_c Y' CY 0 :^: pack_c X' CX 0.
  rewrite Hom_struct_c_pack.
  assume Hf.
  rewrite <- pack_c_0_eq2. rewrite <- pack_c_0_eq2.
  apply Hf. assume Hf1 _. exact Hf1.
}
exact MetaCatConcreteForgetful Obj (fun X => X 0) Hom_struct_c L1.
Qed.

Theorem MetaCat_struct_b_b_e_gen :
    (forall X, Obj X -> struct_b_b_e X)
 -> MetaCat Obj Hom_struct_b_b_e (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f).
assume HO.
apply MetaCatConcrete Obj (fun X => X 0) Hom_struct_b_b_e.
- let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_b_b_e u Y f -> f :e Y 0 :^: u 0).
  let X' bX. assume HbX. let b2X. assume Hb2X. let eX. assume HeX.
  apply HO Y HY (fun u => Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) u f -> f :e u 0 :^: pack_b_b_e X' bX b2X eX 0).
  let Y' bY. assume HbY. let b2Y. assume Hb2Y. let eY. assume HeY.
  prove Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) (pack_b_b_e Y' bY b2Y eY) f -> f :e pack_b_b_e Y' bY b2Y eY 0 :^: pack_b_b_e X' bX b2X eX 0.
  rewrite Hom_struct_b_b_e_pack.
  assume Hf: f :e Y' :^: X'
          /\ (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
          /\ (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
          /\ f eX = eY.
  apply and4E (f :e Y' :^: X')
              (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
              (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
              (f eX = eY) Hf.
  assume Hf1: f :e Y' :^: X'.
  assume Hf2: forall x x' :e X', f (bX x x') = bY (f x) (f x').
  assume Hf3: forall x x' :e X', f (b2X x x') = b2Y (f x) (f x').
  assume Hf4: f eX = eY.
  prove f :e pack_b_b_e Y' bY b2Y eY 0 :^: pack_b_b_e X' bX b2X eX 0.
  rewrite <- pack_b_b_e_0_eq2. rewrite <- pack_b_b_e_0_eq2.
  prove f :e Y' :^: X'.
  exact Hf1.
- let X. assume HX.
  apply HO X HX (fun u => Hom_struct_b_b_e u u (lam_id (u 0))).
  let X' bX. assume HbX. let b2X. assume Hb2X. let eX. assume HeX.
  prove Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) (pack_b_b_e X' bX b2X eX) (lam_id (pack_b_b_e X' bX b2X eX 0)).
  rewrite <- pack_b_b_e_0_eq2. rewrite Hom_struct_b_b_e_pack.
  prove lam_id X' :e X' :^: X'
     /\ (forall x x' :e X', lam_id X' (bX x x') = bX (lam_id X' x) (lam_id X' x'))
     /\ (forall x x' :e X', lam_id X' (b2X x x') = b2X (lam_id X' x) (lam_id X' x'))
     /\ lam_id X' eX = eX.
  apply and4I.
  + exact lam_id_exp_In X'.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_id X' (bX x x') = bX ((fun x :e X' => x) x) ((fun x :e X' => x) x').
    rewrite beta X' (fun x => x) x Hx.
    rewrite beta X' (fun x => x) x' Hx'.
    exact beta X' (fun x => x) (bX x x') (HbX x Hx x' Hx').
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_id X' (b2X x x') = b2X ((fun x :e X' => x) x) ((fun x :e X' => x) x').
    rewrite beta X' (fun x => x) x Hx.
    rewrite beta X' (fun x => x) x' Hx'.
    exact beta X' (fun x => x) (b2X x x') (Hb2X x Hx x' Hx').
  + prove (fun x :e X' => x) eX = eX.
    exact beta X' (fun x => x) eX HeX.
- let X Y Z f g.
  assume HX HY HZ.
  apply HO X HX (fun u => Hom_struct_b_b_e u Y f -> Hom_struct_b_b_e Y Z g -> Hom_struct_b_b_e u Z (lam_comp (u 0) g f)).
  let X' bX. assume HbX. let b2X. assume Hb2X. let eX. assume HeX.
  prove Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) Y f -> Hom_struct_b_b_e Y Z g -> Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) Z (lam_comp (pack_b_b_e X' bX b2X eX 0) g f).
  rewrite <- pack_b_b_e_0_eq2.
  prove Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) Y f -> Hom_struct_b_b_e Y Z g -> Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) Z (lam_comp X' g f).
  apply HO Y HY (fun u => Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) u f -> Hom_struct_b_b_e u Z g -> Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) Z (lam_comp X' g f)).
  let Y' bY. assume HbY. let b2Y. assume Hb2Y. let eY. assume HeY.
  prove Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) (pack_b_b_e Y' bY b2Y eY) f -> Hom_struct_b_b_e (pack_b_b_e Y' bY b2Y eY) Z g -> Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) Z (lam_comp X' g f).
  rewrite Hom_struct_b_b_e_pack.
  assume Hf: f :e Y' :^: X'
          /\ (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
          /\ (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
          /\ f eX = eY.
  apply HO Z HZ (fun u => Hom_struct_b_b_e (pack_b_b_e Y' bY b2Y eY) u g -> Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) u (lam_comp X' g f)).
  let Z' bZ. assume HbZ. let b2Z. assume Hb2Z. let eZ. assume HeZ.
  prove Hom_struct_b_b_e (pack_b_b_e Y' bY b2Y eY) (pack_b_b_e Z' bZ b2Z eZ) g -> Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) (pack_b_b_e Z' bZ b2Z eZ) (lam_comp X' g f).
  rewrite Hom_struct_b_b_e_pack.
  rewrite Hom_struct_b_b_e_pack.
  assume Hg: g :e Z' :^: Y'
          /\ (forall y y' :e Y', g (bY y y') = bZ (g y) (g y'))
          /\ (forall y y' :e Y', g (b2Y y y') = b2Z (g y) (g y'))
          /\ g eY = eZ.
  apply and4E (f :e Y' :^: X')
              (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
              (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
              (f eX = eY) Hf.
  assume Hf1: f :e Y' :^: X'.
  assume Hf2: forall x x' :e X', f (bX x x') = bY (f x) (f x').
  assume Hf3: forall x x' :e X', f (b2X x x') = b2Y (f x) (f x').
  assume Hf4: f eX = eY.
  apply and4E (g :e Z' :^: Y')
              (forall y y' :e Y', g (bY y y') = bZ (g y) (g y'))
              (forall y y' :e Y', g (b2Y y y') = b2Z (g y) (g y'))
              (g eY = eZ) Hg.
  assume Hg1: g :e Z' :^: Y'.
  assume Hg2: forall y y' :e Y', g (bY y y') = bZ (g y) (g y').
  assume Hg3: forall y y' :e Y', g (b2Y y y') = b2Z (g y) (g y').
  assume Hg4: g eY = eZ.
  prove lam_comp X' g f :e Z' :^: X'
     /\ (forall x x' :e X', lam_comp X' g f (bX x x') = bZ (lam_comp X' g f x) (lam_comp X' g f x'))
     /\ (forall x x' :e X', lam_comp X' g f (b2X x x') = b2Z (lam_comp X' g f x) (lam_comp X' g f x'))
     /\ lam_comp X' g f eX = eZ.
  apply and4I.
  + exact lam_comp_exp_In X' Y' Z' f Hf1 g Hg1.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_comp X' g f (bX x x') = bZ ((fun x :e X' => g (f x)) x) ((fun x :e X' => g (f x)) x').
    rewrite beta X' (fun x => g (f x)) x Hx.
    rewrite beta X' (fun x => g (f x)) x' Hx'.
    prove (fun x :e X' => g (f x)) (bX x x') = bZ (g (f x)) (g (f x')).
    rewrite beta X' (fun x => g (f x)) (bX x x') (HbX x Hx x' Hx').
    prove g (f (bX x x')) = bZ (g (f x)) (g (f x')).
    rewrite <- Hg2 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx) (f x') (ap_Pi X' (fun _ => Y') f x' Hf1 Hx').
    prove g (f (bX x x')) = g (bY (f x) (f x')).
    f_equal.
    exact Hf2 x Hx x' Hx'.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_comp X' g f (b2X x x') = b2Z ((fun x :e X' => g (f x)) x) ((fun x :e X' => g (f x)) x').
    rewrite beta X' (fun x => g (f x)) x Hx.
    rewrite beta X' (fun x => g (f x)) x' Hx'.
    prove (fun x :e X' => g (f x)) (b2X x x') = b2Z (g (f x)) (g (f x')).
    rewrite beta X' (fun x => g (f x)) (b2X x x') (Hb2X x Hx x' Hx').
    prove g (f (b2X x x')) = b2Z (g (f x)) (g (f x')).
    rewrite <- Hg3 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx) (f x') (ap_Pi X' (fun _ => Y') f x' Hf1 Hx').
    prove g (f (b2X x x')) = g (b2Y (f x) (f x')).
    f_equal.
    exact Hf3 x Hx x' Hx'.
  + prove (fun x :e X' => g (f x)) eX = eZ.
    rewrite beta X' (fun x => g (f x)) eX HeX.
    prove g (f eX) = eZ.
    rewrite Hf4. exact Hg4.
Qed.

Theorem MetaCat_struct_b_b_e_Forgetful_gen :
    (forall X, Obj X -> struct_b_b_e X)
 -> MetaFunctor Obj Hom_struct_b_b_e (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f)
                (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
		(fun X => X 0) (fun X Y f => f).
assume HO.
claim L1: forall X Y f, Obj X -> Obj Y -> Hom_struct_b_b_e X Y f -> f :e Y 0 :^: X 0.
{ let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_b_b_e u Y f -> f :e Y 0 :^: u 0).
  let X' bX. assume HbX. let b2X. assume Hb2X. let eX. assume HeX.
  apply HO Y HY (fun u => Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) u f -> f :e u 0 :^: pack_b_b_e X' bX b2X eX 0).
  let Y' bY. assume HbY. let b2Y. assume Hb2Y. let eY. assume HeY.
  prove Hom_struct_b_b_e (pack_b_b_e X' bX b2X eX) (pack_b_b_e Y' bY b2Y eY) f -> f :e pack_b_b_e Y' bY b2Y eY 0 :^: pack_b_b_e X' bX b2X eX 0.
  rewrite Hom_struct_b_b_e_pack.
  assume Hf.
  rewrite <- pack_b_b_e_0_eq2. rewrite <- pack_b_b_e_0_eq2.
  apply Hf. assume Hf _. apply Hf. assume Hf _. apply Hf. assume Hf1 _. exact Hf1.
}
exact MetaCatConcreteForgetful Obj (fun X => X 0) Hom_struct_b_b_e L1.
Qed.

Theorem MetaCat_struct_b_b_e_e_gen :
    (forall X, Obj X -> struct_b_b_e_e X)
 -> MetaCat Obj Hom_struct_b_b_e_e (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f).
assume HO.
apply MetaCatConcrete Obj (fun X => X 0) Hom_struct_b_b_e_e.
- let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_b_b_e_e u Y f -> f :e Y 0 :^: u 0).
  let X' bX. assume HbX. let b2X. assume Hb2X. let eX. assume HeX. let e2X. assume He2X.
  apply HO Y HY (fun u => Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) u f -> f :e u 0 :^: pack_b_b_e_e X' bX b2X eX e2X 0).
  let Y' bY. assume HbY. let b2Y. assume Hb2Y. let eY. assume HeY. let e2Y. assume He2Y.
  prove Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) (pack_b_b_e_e Y' bY b2Y eY e2Y) f -> f :e pack_b_b_e_e Y' bY b2Y eY e2Y 0 :^: pack_b_b_e_e X' bX b2X eX e2X 0.
  rewrite Hom_struct_b_b_e_e_pack.
  assume Hf: f :e Y' :^: X'
          /\ (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
          /\ (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
          /\ f eX = eY
          /\ f e2X = e2Y.
  apply and5E (f :e Y' :^: X')
              (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
              (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
              (f eX = eY) (f e2X = e2Y) Hf.
  assume Hf1: f :e Y' :^: X'.
  assume Hf2: forall x x' :e X', f (bX x x') = bY (f x) (f x').
  assume Hf3: forall x x' :e X', f (b2X x x') = b2Y (f x) (f x').
  assume Hf4: f eX = eY.
  assume Hf5: f e2X = e2Y.
  prove f :e pack_b_b_e_e Y' bY b2Y eY e2Y 0 :^: pack_b_b_e_e X' bX b2X eX e2X 0.
  rewrite <- pack_b_b_e_e_0_eq2. rewrite <- pack_b_b_e_e_0_eq2.
  prove f :e Y' :^: X'.
  exact Hf1.
- let X. assume HX.
  apply HO X HX (fun u => Hom_struct_b_b_e_e u u (lam_id (u 0))).
  let X' bX. assume HbX. let b2X. assume Hb2X. let eX. assume HeX. let e2X. assume He2X.
  prove Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) (pack_b_b_e_e X' bX b2X eX e2X) (lam_id (pack_b_b_e_e X' bX b2X eX e2X 0)).
  rewrite <- pack_b_b_e_e_0_eq2. rewrite Hom_struct_b_b_e_e_pack.
  prove lam_id X' :e X' :^: X'
     /\ (forall x x' :e X', lam_id X' (bX x x') = bX (lam_id X' x) (lam_id X' x'))
     /\ (forall x x' :e X', lam_id X' (b2X x x') = b2X (lam_id X' x) (lam_id X' x'))
     /\ lam_id X' eX = eX
     /\ lam_id X' e2X = e2X.
  apply and5I.
  + exact lam_id_exp_In X'.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_id X' (bX x x') = bX ((fun x :e X' => x) x) ((fun x :e X' => x) x').
    rewrite beta X' (fun x => x) x Hx.
    rewrite beta X' (fun x => x) x' Hx'.
    exact beta X' (fun x => x) (bX x x') (HbX x Hx x' Hx').
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_id X' (b2X x x') = b2X ((fun x :e X' => x) x) ((fun x :e X' => x) x').
    rewrite beta X' (fun x => x) x Hx.
    rewrite beta X' (fun x => x) x' Hx'.
    exact beta X' (fun x => x) (b2X x x') (Hb2X x Hx x' Hx').
  + prove (fun x :e X' => x) eX = eX.
    exact beta X' (fun x => x) eX HeX.
  + prove (fun x :e X' => x) e2X = e2X.
    exact beta X' (fun x => x) e2X He2X.
- let X Y Z f g.
  assume HX HY HZ.
  apply HO X HX (fun u => Hom_struct_b_b_e_e u Y f -> Hom_struct_b_b_e_e Y Z g -> Hom_struct_b_b_e_e u Z (lam_comp (u 0) g f)).
  let X' bX. assume HbX. let b2X. assume Hb2X. let eX. assume HeX. let e2X. assume He2X.
  prove Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) Y f -> Hom_struct_b_b_e_e Y Z g -> Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) Z (lam_comp (pack_b_b_e_e X' bX b2X eX e2X 0) g f).
  rewrite <- pack_b_b_e_e_0_eq2.
  prove Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) Y f -> Hom_struct_b_b_e_e Y Z g -> Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) Z (lam_comp X' g f).
  apply HO Y HY (fun u => Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) u f -> Hom_struct_b_b_e_e u Z g -> Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) Z (lam_comp X' g f)).
  let Y' bY. assume HbY. let b2Y. assume Hb2Y. let eY. assume HeY. let e2Y. assume He2Y.
  prove Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) (pack_b_b_e_e Y' bY b2Y eY e2Y) f -> Hom_struct_b_b_e_e (pack_b_b_e_e Y' bY b2Y eY e2Y) Z g -> Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) Z (lam_comp X' g f).
  rewrite Hom_struct_b_b_e_e_pack.
  assume Hf: f :e Y' :^: X'
          /\ (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
          /\ (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
          /\ f eX = eY
          /\ f e2X = e2Y.
  apply HO Z HZ (fun u => Hom_struct_b_b_e_e (pack_b_b_e_e Y' bY b2Y eY e2Y) u g -> Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) u (lam_comp X' g f)).
  let Z' bZ. assume HbZ. let b2Z. assume Hb2Z. let eZ. assume HeZ. let e2Z. assume He2Z.
  prove Hom_struct_b_b_e_e (pack_b_b_e_e Y' bY b2Y eY e2Y) (pack_b_b_e_e Z' bZ b2Z eZ e2Z) g -> Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) (pack_b_b_e_e Z' bZ b2Z eZ e2Z) (lam_comp X' g f).
  rewrite Hom_struct_b_b_e_e_pack.
  rewrite Hom_struct_b_b_e_e_pack.
  assume Hg: g :e Z' :^: Y'
          /\ (forall y y' :e Y', g (bY y y') = bZ (g y) (g y'))
          /\ (forall y y' :e Y', g (b2Y y y') = b2Z (g y) (g y'))
          /\ g eY = eZ
          /\ g e2Y = e2Z.
  apply and5E (f :e Y' :^: X')
              (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
              (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
              (f eX = eY) (f e2X = e2Y) Hf.
  assume Hf1: f :e Y' :^: X'.
  assume Hf2: forall x x' :e X', f (bX x x') = bY (f x) (f x').
  assume Hf3: forall x x' :e X', f (b2X x x') = b2Y (f x) (f x').
  assume Hf4: f eX = eY.
  assume Hf5: f e2X = e2Y.
  apply and5E (g :e Z' :^: Y')
              (forall y y' :e Y', g (bY y y') = bZ (g y) (g y'))
              (forall y y' :e Y', g (b2Y y y') = b2Z (g y) (g y'))
              (g eY = eZ) (g e2Y = e2Z) Hg.
  assume Hg1: g :e Z' :^: Y'.
  assume Hg2: forall y y' :e Y', g (bY y y') = bZ (g y) (g y').
  assume Hg3: forall y y' :e Y', g (b2Y y y') = b2Z (g y) (g y').
  assume Hg4: g eY = eZ.
  assume Hg5: g e2Y = e2Z.
  prove lam_comp X' g f :e Z' :^: X'
     /\ (forall x x' :e X', lam_comp X' g f (bX x x') = bZ (lam_comp X' g f x) (lam_comp X' g f x'))
     /\ (forall x x' :e X', lam_comp X' g f (b2X x x') = b2Z (lam_comp X' g f x) (lam_comp X' g f x'))
     /\ lam_comp X' g f eX = eZ
     /\ lam_comp X' g f e2X = e2Z.
  apply and5I.
  + exact lam_comp_exp_In X' Y' Z' f Hf1 g Hg1.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_comp X' g f (bX x x') = bZ ((fun x :e X' => g (f x)) x) ((fun x :e X' => g (f x)) x').
    rewrite beta X' (fun x => g (f x)) x Hx.
    rewrite beta X' (fun x => g (f x)) x' Hx'.
    prove (fun x :e X' => g (f x)) (bX x x') = bZ (g (f x)) (g (f x')).
    rewrite beta X' (fun x => g (f x)) (bX x x') (HbX x Hx x' Hx').
    prove g (f (bX x x')) = bZ (g (f x)) (g (f x')).
    rewrite <- Hg2 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx) (f x') (ap_Pi X' (fun _ => Y') f x' Hf1 Hx').
    prove g (f (bX x x')) = g (bY (f x) (f x')).
    f_equal.
    exact Hf2 x Hx x' Hx'.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_comp X' g f (b2X x x') = b2Z ((fun x :e X' => g (f x)) x) ((fun x :e X' => g (f x)) x').
    rewrite beta X' (fun x => g (f x)) x Hx.
    rewrite beta X' (fun x => g (f x)) x' Hx'.
    prove (fun x :e X' => g (f x)) (b2X x x') = b2Z (g (f x)) (g (f x')).
    rewrite beta X' (fun x => g (f x)) (b2X x x') (Hb2X x Hx x' Hx').
    prove g (f (b2X x x')) = b2Z (g (f x)) (g (f x')).
    rewrite <- Hg3 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx) (f x') (ap_Pi X' (fun _ => Y') f x' Hf1 Hx').
    prove g (f (b2X x x')) = g (b2Y (f x) (f x')).
    f_equal.
    exact Hf3 x Hx x' Hx'.
  + prove (fun x :e X' => g (f x)) eX = eZ.
    rewrite beta X' (fun x => g (f x)) eX HeX.
    prove g (f eX) = eZ.
    rewrite Hf4. exact Hg4.
  + prove (fun x :e X' => g (f x)) e2X = e2Z.
    rewrite beta X' (fun x => g (f x)) e2X He2X.
    prove g (f e2X) = e2Z.
    rewrite Hf5. exact Hg5.
Qed.

Theorem MetaCat_struct_b_b_e_e_Forgetful_gen :
    (forall X, Obj X -> struct_b_b_e_e X)
 -> MetaFunctor Obj Hom_struct_b_b_e_e (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f)
                (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
		(fun X => X 0) (fun X Y f => f).
assume HO.
claim L1: forall X Y f, Obj X -> Obj Y -> Hom_struct_b_b_e_e X Y f -> f :e Y 0 :^: X 0.
{ let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_b_b_e_e u Y f -> f :e Y 0 :^: u 0).
  let X' bX. assume HbX. let b2X. assume Hb2X. let eX. assume HeX. let e2X. assume He2X.
  apply HO Y HY (fun u => Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) u f -> f :e u 0 :^: pack_b_b_e_e X' bX b2X eX e2X 0).
  let Y' bY. assume HbY. let b2Y. assume Hb2Y. let eY. assume HeY. let e2Y. assume He2Y.
  prove Hom_struct_b_b_e_e (pack_b_b_e_e X' bX b2X eX e2X) (pack_b_b_e_e Y' bY b2Y eY e2Y) f -> f :e pack_b_b_e_e Y' bY b2Y eY e2Y 0 :^: pack_b_b_e_e X' bX b2X eX e2X 0.
  rewrite Hom_struct_b_b_e_e_pack.
  assume Hf.
  rewrite <- pack_b_b_e_e_0_eq2. rewrite <- pack_b_b_e_e_0_eq2.
  apply Hf. assume Hf _. apply Hf. assume Hf _. apply Hf. assume Hf _.
  apply Hf. assume Hf1 _. exact Hf1.
}
exact MetaCatConcreteForgetful Obj (fun X => X 0) Hom_struct_b_b_e_e L1.
Qed.

Theorem MetaCat_struct_b_b_r_e_e_gen :
    (forall X, Obj X -> struct_b_b_r_e_e X)
 -> MetaCat Obj Hom_struct_b_b_r_e_e (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f).
assume HO.
apply MetaCatConcrete Obj (fun X => X 0) Hom_struct_b_b_r_e_e.
- let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_b_b_r_e_e u Y f -> f :e Y 0 :^: u 0).
  let X' bX. assume HbX. let b2X. assume Hb2X. let rX eX. assume HeX. let e2X. assume He2X.
  apply HO Y HY (fun u => Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) u f -> f :e u 0 :^: pack_b_b_r_e_e X' bX b2X rX eX e2X 0).
  let Y' bY. assume HbY. let b2Y. assume Hb2Y. let rY eY. assume HeY. let e2Y. assume He2Y.
  prove Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) (pack_b_b_r_e_e Y' bY b2Y rY eY e2Y) f -> f :e pack_b_b_r_e_e Y' bY b2Y rY eY e2Y 0 :^: pack_b_b_r_e_e X' bX b2X rX eX e2X 0.
  rewrite Hom_struct_b_b_r_e_e_pack.
  assume Hf: f :e Y' :^: X'
          /\ (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
          /\ (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
	  /\ (forall x x' :e X', rX x x' -> rY (f x) (f x'))
          /\ f eX = eY
          /\ f e2X = e2Y.
  apply and6E (f :e Y' :^: X')
              (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
              (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
	      (forall x x' :e X', rX x x' -> rY (f x) (f x'))
              (f eX = eY) (f e2X = e2Y) Hf.
  assume Hf1: f :e Y' :^: X'.
  assume Hf2: forall x x' :e X', f (bX x x') = bY (f x) (f x').
  assume Hf3: forall x x' :e X', f (b2X x x') = b2Y (f x) (f x').
  assume Hf4: forall x x' :e X', rX x x' -> rY (f x) (f x').
  assume Hf5: f eX = eY.
  assume Hf6: f e2X = e2Y.
  prove f :e pack_b_b_r_e_e Y' bY b2Y rY eY e2Y 0 :^: pack_b_b_r_e_e X' bX b2X rX eX e2X 0.
  rewrite <- pack_b_b_r_e_e_0_eq2. rewrite <- pack_b_b_r_e_e_0_eq2.
  prove f :e Y' :^: X'.
  exact Hf1.
- let X. assume HX.
  apply HO X HX (fun u => Hom_struct_b_b_r_e_e u u (lam_id (u 0))).
  let X' bX. assume HbX. let b2X. assume Hb2X. let rX eX. assume HeX. let e2X. assume He2X.
  prove Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) (pack_b_b_r_e_e X' bX b2X rX eX e2X) (lam_id (pack_b_b_r_e_e X' bX b2X rX eX e2X 0)).
  rewrite <- pack_b_b_r_e_e_0_eq2. rewrite Hom_struct_b_b_r_e_e_pack.
  prove lam_id X' :e X' :^: X'
     /\ (forall x x' :e X', lam_id X' (bX x x') = bX (lam_id X' x) (lam_id X' x'))
     /\ (forall x x' :e X', lam_id X' (b2X x x') = b2X (lam_id X' x) (lam_id X' x'))
     /\ (forall x x' :e X', rX x x' -> rX (lam_id X' x) (lam_id X' x'))
     /\ lam_id X' eX = eX
     /\ lam_id X' e2X = e2X.
  apply and6I.
  + exact lam_id_exp_In X'.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_id X' (bX x x') = bX ((fun x :e X' => x) x) ((fun x :e X' => x) x').
    rewrite beta X' (fun x => x) x Hx.
    rewrite beta X' (fun x => x) x' Hx'.
    exact beta X' (fun x => x) (bX x x') (HbX x Hx x' Hx').
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_id X' (b2X x x') = b2X ((fun x :e X' => x) x) ((fun x :e X' => x) x').
    rewrite beta X' (fun x => x) x Hx.
    rewrite beta X' (fun x => x) x' Hx'.
    exact beta X' (fun x => x) (b2X x x') (Hb2X x Hx x' Hx').
  + let x. assume Hx. let x'. assume Hx' Hxx'.
    prove rX ((fun x :e X' => x) x) ((fun x :e X' => x) x').
    rewrite beta X' (fun x => x) x Hx.
    rewrite beta X' (fun x => x) x' Hx'.
    exact Hxx'.
  + prove (fun x :e X' => x) eX = eX.
    exact beta X' (fun x => x) eX HeX.
  + prove (fun x :e X' => x) e2X = e2X.
    exact beta X' (fun x => x) e2X He2X.
- let X Y Z f g.
  assume HX HY HZ.
  apply HO X HX (fun u => Hom_struct_b_b_r_e_e u Y f -> Hom_struct_b_b_r_e_e Y Z g -> Hom_struct_b_b_r_e_e u Z (lam_comp (u 0) g f)).
  let X' bX. assume HbX. let b2X. assume Hb2X. let rX eX. assume HeX. let e2X. assume He2X.
  prove Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) Y f -> Hom_struct_b_b_r_e_e Y Z g -> Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) Z (lam_comp (pack_b_b_r_e_e X' bX b2X rX eX e2X 0) g f).
  rewrite <- pack_b_b_r_e_e_0_eq2.
  prove Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) Y f -> Hom_struct_b_b_r_e_e Y Z g -> Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) Z (lam_comp X' g f).
  apply HO Y HY (fun u => Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) u f -> Hom_struct_b_b_r_e_e u Z g -> Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) Z (lam_comp X' g f)).
  let Y' bY. assume HbY. let b2Y. assume Hb2Y. let rY eY. assume HeY. let e2Y. assume He2Y.
  prove Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) (pack_b_b_r_e_e Y' bY b2Y rY eY e2Y) f -> Hom_struct_b_b_r_e_e (pack_b_b_r_e_e Y' bY b2Y rY eY e2Y) Z g -> Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) Z (lam_comp X' g f).
  rewrite Hom_struct_b_b_r_e_e_pack.
  assume Hf: f :e Y' :^: X'
          /\ (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
          /\ (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
	  /\ (forall x x' :e X', rX x x' -> rY (f x) (f x'))
          /\ f eX = eY
          /\ f e2X = e2Y.
  apply HO Z HZ (fun u => Hom_struct_b_b_r_e_e (pack_b_b_r_e_e Y' bY b2Y rY eY e2Y) u g -> Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) u (lam_comp X' g f)).
  let Z' bZ. assume HbZ. let b2Z. assume Hb2Z. let rZ eZ. assume HeZ. let e2Z. assume He2Z.
  prove Hom_struct_b_b_r_e_e (pack_b_b_r_e_e Y' bY b2Y rY eY e2Y) (pack_b_b_r_e_e Z' bZ b2Z rZ eZ e2Z) g -> Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) (pack_b_b_r_e_e Z' bZ b2Z rZ eZ e2Z) (lam_comp X' g f).
  rewrite Hom_struct_b_b_r_e_e_pack.
  rewrite Hom_struct_b_b_r_e_e_pack.
  assume Hg: g :e Z' :^: Y'
          /\ (forall y y' :e Y', g (bY y y') = bZ (g y) (g y'))
          /\ (forall y y' :e Y', g (b2Y y y') = b2Z (g y) (g y'))
	  /\ (forall y y' :e Y', rY y y' -> rZ (g y) (g y'))
          /\ g eY = eZ
          /\ g e2Y = e2Z.
  apply and6E (f :e Y' :^: X')
              (forall x x' :e X', f (bX x x') = bY (f x) (f x'))
              (forall x x' :e X', f (b2X x x') = b2Y (f x) (f x'))
	      (forall x x' :e X', rX x x' -> rY (f x) (f x'))
              (f eX = eY) (f e2X = e2Y) Hf.
  assume Hf1: f :e Y' :^: X'.
  assume Hf2: forall x x' :e X', f (bX x x') = bY (f x) (f x').
  assume Hf3: forall x x' :e X', f (b2X x x') = b2Y (f x) (f x').
  assume Hf4: forall x x' :e X', rX x x' -> rY (f x) (f x').
  assume Hf5: f eX = eY.
  assume Hf6: f e2X = e2Y.
  apply and6E (g :e Z' :^: Y')
              (forall y y' :e Y', g (bY y y') = bZ (g y) (g y'))
              (forall y y' :e Y', g (b2Y y y') = b2Z (g y) (g y'))
	      (forall y y' :e Y', rY y y' -> rZ (g y) (g y'))
              (g eY = eZ) (g e2Y = e2Z) Hg.
  assume Hg1: g :e Z' :^: Y'.
  assume Hg2: forall y y' :e Y', g (bY y y') = bZ (g y) (g y').
  assume Hg3: forall y y' :e Y', g (b2Y y y') = b2Z (g y) (g y').
  assume Hg4: forall y y' :e Y', rY y y' -> rZ (g y) (g y').
  assume Hg5: g eY = eZ.
  assume Hg6: g e2Y = e2Z.
  prove lam_comp X' g f :e Z' :^: X'
     /\ (forall x x' :e X', lam_comp X' g f (bX x x') = bZ (lam_comp X' g f x) (lam_comp X' g f x'))
     /\ (forall x x' :e X', lam_comp X' g f (b2X x x') = b2Z (lam_comp X' g f x) (lam_comp X' g f x'))
     /\ (forall x x' :e X', rX x x' -> rZ (lam_comp X' g f x) (lam_comp X' g f x'))
     /\ lam_comp X' g f eX = eZ
     /\ lam_comp X' g f e2X = e2Z.
  apply and6I.
  + exact lam_comp_exp_In X' Y' Z' f Hf1 g Hg1.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_comp X' g f (bX x x') = bZ ((fun x :e X' => g (f x)) x) ((fun x :e X' => g (f x)) x').
    rewrite beta X' (fun x => g (f x)) x Hx.
    rewrite beta X' (fun x => g (f x)) x' Hx'.
    prove (fun x :e X' => g (f x)) (bX x x') = bZ (g (f x)) (g (f x')).
    rewrite beta X' (fun x => g (f x)) (bX x x') (HbX x Hx x' Hx').
    prove g (f (bX x x')) = bZ (g (f x)) (g (f x')).
    rewrite <- Hg2 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx) (f x') (ap_Pi X' (fun _ => Y') f x' Hf1 Hx').
    prove g (f (bX x x')) = g (bY (f x) (f x')).
    f_equal.
    exact Hf2 x Hx x' Hx'.
  + let x. assume Hx. let x'. assume Hx'.
    prove lam_comp X' g f (b2X x x') = b2Z ((fun x :e X' => g (f x)) x) ((fun x :e X' => g (f x)) x').
    rewrite beta X' (fun x => g (f x)) x Hx.
    rewrite beta X' (fun x => g (f x)) x' Hx'.
    prove (fun x :e X' => g (f x)) (b2X x x') = b2Z (g (f x)) (g (f x')).
    rewrite beta X' (fun x => g (f x)) (b2X x x') (Hb2X x Hx x' Hx').
    prove g (f (b2X x x')) = b2Z (g (f x)) (g (f x')).
    rewrite <- Hg3 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx) (f x') (ap_Pi X' (fun _ => Y') f x' Hf1 Hx').
    prove g (f (b2X x x')) = g (b2Y (f x) (f x')).
    f_equal.
    exact Hf3 x Hx x' Hx'.
  + let x. assume Hx. let x'. assume Hx' Hxx'.
    prove rZ (lam_comp X' g f x) (lam_comp X' g f x').
    prove rZ ((fun x :e X' => g (f x)) x) ((fun x :e X' => g (f x)) x').
    rewrite beta X' (fun x => g (f x)) x Hx.
    rewrite beta X' (fun x => g (f x)) x' Hx'.
    prove rZ (g (f x)) (g (f x')).
    apply Hg4 (f x) (ap_Pi X' (fun _ => Y') f x Hf1 Hx) (f x') (ap_Pi X' (fun _ => Y') f x' Hf1 Hx').
    exact Hf4 x Hx x' Hx' Hxx'.
  + prove (fun x :e X' => g (f x)) eX = eZ.
    rewrite beta X' (fun x => g (f x)) eX HeX.
    prove g (f eX) = eZ.
    rewrite Hf5. exact Hg5.
  + prove (fun x :e X' => g (f x)) e2X = e2Z.
    rewrite beta X' (fun x => g (f x)) e2X He2X.
    prove g (f e2X) = e2Z.
    rewrite Hf6. exact Hg6.
Qed.

Theorem MetaCat_struct_b_b_r_e_e_Forgetful_gen :
    (forall X, Obj X -> struct_b_b_r_e_e X)
 -> MetaFunctor Obj Hom_struct_b_b_r_e_e (fun X => lam_id (X 0)) (fun X Y Z g f => lam_comp (X 0) g f)
                (fun _ => True) SetHom (fun X => lam_id X) (fun X Y Z f g => (lam_comp X f g))
		(fun X => X 0) (fun X Y f => f).
assume HO.
claim L1: forall X Y f, Obj X -> Obj Y -> Hom_struct_b_b_r_e_e X Y f -> f :e Y 0 :^: X 0.
{ let X Y f. assume HX HY.
  apply HO X HX (fun u => Hom_struct_b_b_r_e_e u Y f -> f :e Y 0 :^: u 0).
  let X' bX. assume HbX. let b2X. assume Hb2X. let rX eX. assume HeX. let e2X. assume He2X.
  apply HO Y HY (fun u => Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) u f -> f :e u 0 :^: pack_b_b_r_e_e X' bX b2X rX eX e2X 0).
  let Y' bY. assume HbY. let b2Y. assume Hb2Y. let rY eY. assume HeY. let e2Y. assume He2Y.
  prove Hom_struct_b_b_r_e_e (pack_b_b_r_e_e X' bX b2X rX eX e2X) (pack_b_b_r_e_e Y' bY b2Y rY eY e2Y) f -> f :e pack_b_b_r_e_e Y' bY b2Y rY eY e2Y 0 :^: pack_b_b_r_e_e X' bX b2X rX eX e2X 0.
  rewrite Hom_struct_b_b_r_e_e_pack.
  assume Hf.
  rewrite <- pack_b_b_r_e_e_0_eq2. rewrite <- pack_b_b_r_e_e_0_eq2.
  apply Hf. assume Hf _. apply Hf. assume Hf _. apply Hf. assume Hf _.
  apply Hf. assume Hf _. apply Hf. assume Hf1 _. exact Hf1.
}
exact MetaCatConcreteForgetful Obj (fun X => X 0) Hom_struct_b_b_r_e_e L1.
Qed.

End MetaCatStruct.
