(** $T setmm **)
(** $I sig/DefaultElts.mgs **)

Theorem idi: (forall ph:prop, (ph -> ph)).
let ph:prop.
assume idi_1: ph.
exact idi_1.
Qed.
