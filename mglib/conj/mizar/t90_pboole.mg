(** $I sig/MizarPreamble.mgs **)

Theorem t90_pboole:
 forall esk6_1:set -> set,
 forall esk5_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall k5_pboole:set -> set -> set -> set,
 forall r6_pboole:set -> set -> set -> prop,
 forall k2_pboole:set -> set -> set -> set,
 forall k4_pboole:set -> set -> set -> set,
 forall k3_pboole:set -> set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
     (forall X1 X2 X3, (r6_pboole X2 (k4_pboole X2 (k2_pboole X2 X1 X3) (k3_pboole X2 X1 X3)) (k2_pboole X2 (k4_pboole X2 X1 X3) (k4_pboole X2 X3 X1)) -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r6_pboole X2 (k4_pboole X2 (k2_pboole X2 X1 X3) X4) (k2_pboole X2 (k4_pboole X2 X1 X4) (k4_pboole X2 X3 X4)) -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r6_pboole X2 (k4_pboole X2 X1 (k4_pboole X2 X3 X4)) (k2_pboole X2 (k4_pboole X2 X1 X3) (k3_pboole X2 X1 X4)) -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r6_pboole X2 (k4_pboole X2 (k4_pboole X2 X1 X3) X4) (k4_pboole X2 X1 (k2_pboole X2 X3 X4)) -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r6_pboole X2 (k3_pboole X2 (k3_pboole X2 X1 X3) X4) (k3_pboole X2 X1 (k3_pboole X2 X3 X4)) -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r6_pboole X2 (k2_pboole X2 (k2_pboole X2 X1 X3) X4) (k2_pboole X2 X1 (k2_pboole X2 X3 X4)) -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2 X3, ((k2_pboole X2 (k4_pboole X2 X1 X3) (k4_pboole X2 X3 X1)) = (k5_pboole X2 X1 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2 X3, (r6_pboole X2 X3 X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r6_pboole X2 X1 X3 -> False)
  -> (forall X2 X1 X3, (v1_partfun1 (k4_pboole X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_partfun1 (k3_pboole X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_partfun1 (k2_pboole X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_partfun1 (k5_pboole X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v4_relat_1 (k4_pboole X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v4_relat_1 (k3_pboole X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v4_relat_1 (k2_pboole X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v4_relat_1 (k5_pboole X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_funct_1 (k4_pboole X1 X2 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_funct_1 (k3_pboole X1 X2 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_funct_1 (k2_pboole X1 X2 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_funct_1 (k5_pboole X1 X2 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_relat_1 (k4_pboole X1 X2 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_relat_1 (k3_pboole X1 X2 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_relat_1 (k2_pboole X1 X2 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_relat_1 (k5_pboole X1 X2 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2 X3, ((k3_pboole X2 X1 X3) = (k3_pboole X2 X3 X1) -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2 X3, ((k2_pboole X2 X1 X3) = (k2_pboole X2 X3 X1) -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2 X3, ((k5_pboole X2 X1 X3) = (k5_pboole X2 X3 X1) -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> r6_pboole X1 X2 X3 -> False)
  -> (forall X3 X1 X2, (r6_pboole X3 X1 X2 -> False) -> X1 = X2 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, ((k3_pboole X2 X1 X1) = X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X2 X1, ((k2_pboole X2 X1 X1) = X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X2 X1, (r6_pboole X2 X1 X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (r6_pboole esk1_0 (k5_pboole esk1_0 (k5_pboole esk1_0 esk2_0 esk3_0) esk4_0) (k5_pboole esk1_0 esk2_0 (k5_pboole esk1_0 esk3_0 esk4_0)) -> False)
  -> (forall X1, (v1_partfun1 (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk6_1 X1) X1 -> False) -> False)
  -> ((v1_partfun1 esk4_0 esk1_0 -> False) -> False)
  -> ((v1_partfun1 esk3_0 esk1_0 -> False) -> False)
  -> ((v1_partfun1 esk2_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk4_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk3_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk6_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk6_1 X1) -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk5_0 -> False) -> False)
  -> ((v1_relat_1 esk4_0 -> False) -> False)
  -> ((v1_relat_1 esk3_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> False.
Admitted.
