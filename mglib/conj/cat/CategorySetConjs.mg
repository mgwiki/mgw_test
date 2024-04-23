(** $I sig/PfgEJul2021Preamble7.mgs **)

Proposition MetaCatSet_coequalizer_gen : forall Obj:set -> prop,
  (forall X, Obj X -> forall Q c= X, Obj Q)
  ->
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  coequalizer_constr_p Obj SetHom
    (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
    quot canonmap fac.
Admitted.

Proposition MetaCatSet_coequalizer :
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  coequalizer_constr_p (fun _ => True) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  quot canonmap fac.
Admitted.

Proposition MetaCatHFSet_coequalizer :
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  coequalizer_constr_p (fun X => X :e UnivOf Empty) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  quot canonmap fac.
Admitted.

Proposition MetaCatSmallSet_coequalizer :
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  coequalizer_constr_p (fun X => X :e UnivOf (UnivOf Empty)) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  quot canonmap fac.
Admitted.

Proposition MetaCatSet_equalizer_gen : forall Obj:set -> prop,
  (forall X, Obj X -> forall Q c= X, Obj Q)
  ->
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  equalizer_constr_p Obj SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  quot canonmap fac.
Admitted.

Proposition MetaCatHFSet_equalizer_gen : forall Obj:set -> prop,
  (forall X, Obj X -> forall Q c= X, Obj Q)
  ->
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  equalizer_constr_p (fun X => X :e UnivOf Empty) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  quot canonmap fac.
Admitted.

Proposition MetaCatSmallSet_equalizer_gen : forall Obj:set -> prop,
  (forall X, Obj X -> forall Q c= X, Obj Q)
  ->
  exists quot:set -> set -> set -> set -> set,
  exists canonmap:set -> set -> set -> set -> set,
  exists fac:set -> set -> set -> set -> set -> set -> set,
  equalizer_constr_p (fun X => X :e UnivOf (UnivOf Empty)) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  quot canonmap fac.
Admitted.

Proposition MetaCatSet_pullback_gen : forall Obj:set -> prop,
  MetaCat Obj SetHom (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  ->
  (forall X, Obj X -> forall Q c= X, Obj Q)
  ->
  (forall X, Obj X -> forall Y, Obj Y -> Obj (setprod X Y))
  ->
  exists pb:set -> set -> set -> set -> set -> set,
  exists pi0:set -> set -> set -> set -> set -> set,
  exists pi1:set -> set -> set -> set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pullback_constr_p Obj SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  pb pi0 pi1 pair.
Admitted.

Proposition MetaCatSet_pullback :
  exists pb:set -> set -> set -> set -> set -> set,
  exists pi0:set -> set -> set -> set -> set -> set,
  exists pi1:set -> set -> set -> set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pullback_constr_p (fun _ => True) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  pb pi0 pi1 pair.
Admitted.

Proposition MetaCatHFSet_pullback :
  exists pb:set -> set -> set -> set -> set -> set,
  exists pi0:set -> set -> set -> set -> set -> set,
  exists pi1:set -> set -> set -> set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pullback_constr_p (fun X => X :e UnivOf Empty) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  pb pi0 pi1 pair.
Admitted.

Proposition MetaCatSmallSet_pullback :
  exists pb:set -> set -> set -> set -> set -> set,
  exists pi0:set -> set -> set -> set -> set -> set,
  exists pi1:set -> set -> set -> set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pullback_constr_p (fun X => X :e UnivOf (UnivOf Empty)) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  pb pi0 pi1 pair.
Admitted.

Proposition MetaCatSet_pushout_gen : forall Obj:set -> prop,
  MetaCat Obj SetHom (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  ->
  (forall X, Obj X -> forall Q c= X, Obj Q)
  ->
  (forall X, Obj X -> forall Y, Obj Y -> Obj (setsum X Y))
  ->
  exists po:set -> set -> set -> set -> set -> set,
  exists i0:set -> set -> set -> set -> set -> set,
  exists i1:set -> set -> set -> set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pushout_constr_p Obj SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  po i0 i1 copair.
Admitted.

Proposition MetaCatSet_pushout :
  exists po:set -> set -> set -> set -> set -> set,
  exists i0:set -> set -> set -> set -> set -> set,
  exists i1:set -> set -> set -> set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pushout_constr_p (fun _ => True) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  po i0 i1 copair.
Admitted.

Proposition MetaCatHFSet_pushout :
  exists po:set -> set -> set -> set -> set -> set,
  exists i0:set -> set -> set -> set -> set -> set,
  exists i1:set -> set -> set -> set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pushout_constr_p (fun X => X :e UnivOf Empty) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  po i0 i1 copair.
Admitted.

Proposition MetaCatSmallSet_pushout :
  exists po:set -> set -> set -> set -> set -> set,
  exists i0:set -> set -> set -> set -> set -> set,
  exists i1:set -> set -> set -> set -> set -> set,
  exists copair:set -> set -> set -> set -> set -> set -> set -> set -> set,
  pushout_constr_p (fun X => X :e UnivOf (UnivOf Empty)) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  po i0 i1 copair.
Admitted.

Proposition MetaCatSet_product_exponent_gen_setprod_setexp : forall Obj:set -> prop,
  (forall X, Obj X -> forall Y, Obj Y -> Obj (setprod X Y))
  ->
  (forall X, Obj X -> forall Y, Obj Y -> Obj (Y :^: X))
  ->
  product_exponent_constr_p Obj SetHom
         (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
         setprod
         (fun X Y => (fun z :e X :*: Y => z 0))
         (fun X Y => (fun z :e X :*: Y => z 1))
         (fun X Y W h k => (fun w :e W => (h w,k w)))
         (fun X Y => Y :^: X)
         (fun X Y => (fun fx :e (Y :^: X) :*: X => fx 0 (fx 1)))
         (fun X Y W f => (fun w :e W => fun x :e X => f(w,x))).
Admitted.

Proposition MetaCatSet_product_exponent_gen : forall Obj:set -> prop,
  (forall X, Obj X -> forall Y, Obj Y -> Obj (setprod X Y))
  ->
  (forall X, Obj X -> forall Y, Obj Y -> Obj (Y :^: X))
  ->
  exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  exists exp:set -> set -> set,
  exists a:set -> set -> set,
  exists lm:set -> set -> set -> set -> set,
  product_exponent_constr_p Obj SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  prod pi0 pi1 pair exp a lm.
Admitted.

Proposition MetaCatSet_product_exponent : exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  exists exp:set -> set -> set,
  exists a:set -> set -> set,
  exists lm:set -> set -> set -> set -> set,
  product_exponent_constr_p (fun _ => True) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  prod pi0 pi1 pair exp a lm.
Admitted.

Proposition MetaCatHFSet_product_exponent : exists prod:set -> set -> set,
  exists pi0 pi1:set -> set -> set,
  exists pair:set -> set -> set -> set -> set -> set,
  exists exp:set -> set -> set,
  exists a:set -> set -> set,
  exists lm:set -> set -> set -> set -> set,
  product_exponent_constr_p (fun X => X :e UnivOf Empty) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  prod pi0 pi1 pair exp a lm.
Admitted.

Proposition MetaCatSet_monic_inj_gen : forall Obj:set -> prop,
  forall X Y, forall f:set,
  monic Obj SetHom (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g) X Y f
  ->
  forall u v :e X, f u = f v -> u = v.
Admitted.

Proposition MetaCatSet_subobject_classifier_gen : forall Obj:set -> prop,
  Obj 1 -> Obj 2
  ->
  subobject_classifier_p Obj SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  1 (fun X:set => (fun x :e X => 0)) 2 (fun _ :e 1 => 1)
  (fun X Y:set => fun m:set => (fun y :e Y => if (exists x :e X, m x = y) then 1 else 0))
  (fun X Y:set => fun m:set => fun W:set => fun h k:set => (fun w :e W => inv X (fun x => m x) (k w))).
Admitted.

Proposition MetaCatSet_subobject_classifier_gen_ex : forall Obj:set -> prop,
  Obj 1 -> Obj 2
  ->
  exists one:set, exists uniqa:set -> set,
  exists Omega:set, exists tru:set,
  exists ch:set -> set -> set -> set,
  exists constr:set -> set -> set -> set -> set -> set -> set,
  subobject_classifier_p Obj SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  one uniqa Omega tru ch constr.
Admitted.

Proposition MetaCatSet_subobject_classifier :
  exists one:set, exists uniqa:set -> set,
  exists Omega:set, exists tru:set,
  exists ch:set -> set -> set -> set,
  exists constr:set -> set -> set -> set -> set -> set -> set,
  subobject_classifier_p (fun _ => True) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  one uniqa Omega tru ch constr.
Admitted.

Proposition MetaCatHFSet_subobject_classifier :
  exists one:set, exists uniqa:set -> set,
  exists Omega:set, exists tru:set,
  exists ch:set -> set -> set -> set,
  exists constr:set -> set -> set -> set -> set -> set -> set,
  subobject_classifier_p (fun X => X :e UnivOf Empty) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  one uniqa Omega tru ch constr.
Admitted.

Proposition MetaCatSmallSet_subobject_classifier :
  exists one:set, exists uniqa:set -> set,
  exists Omega:set, exists tru:set,
  exists ch:set -> set -> set -> set,
  exists constr:set -> set -> set -> set -> set -> set -> set,
  subobject_classifier_p (fun X => X :e UnivOf (UnivOf Empty)) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  one uniqa Omega tru ch constr.
Admitted.

Proposition MetaCatSet_nno_gen : forall Obj:set -> prop,
  Obj 1 -> Obj omega
  ->
  nno_p Obj SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  1 (fun X:set => (fun x :e X => 0)) omega (fun _ :e 1 => 0) (fun n :e omega => ordsucc n)
  (fun X:set => fun x f:set => (fun n :e omega => nat_primrec (x 0) (fun _ v => f v) n)).
Admitted.

Proposition MetaCatSet_nno_gen_ex : forall Obj:set -> prop,
  Obj 1 -> Obj omega
  ->
  exists one:set,
  exists uniqa:set -> set,
  exists N:set,
  exists zer suc:set,
  exists rec:set -> set -> set -> set,
  nno_p Obj SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  one uniqa N zer suc rec.
Admitted.

Proposition MetaCatSet_nno :
  exists one:set,
  exists uniqa:set -> set,
  exists N:set,
  exists zer suc:set,
  exists rec:set -> set -> set -> set,
  nno_p (fun _ => True) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  one uniqa N zer suc rec.
Admitted.

Proposition MetaCatSmallSet_nno :
  exists one:set,
  exists uniqa:set -> set,
  exists N:set,
  exists zer suc:set,
  exists rec:set -> set -> set -> set,
  nno_p (fun X => X :e UnivOf (UnivOf Empty)) SetHom
  (fun X => lam_id X) (fun X Y Z f g => lam_comp X f g)
  one uniqa N zer suc rec.
Admitted.
