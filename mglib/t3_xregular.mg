Theorem t3_xregular:
 forall k3_tarski:set -> set,
 forall esk6_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk10_1:set -> set,
 forall esk11_2:set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk12_1:set -> set,
 forall esk14_2:set -> set -> set,
 forall esk1_0:set,
 forall esk2_1:set -> set,
 forall esk13_1:set -> set,
 forall esk9_0:set,
 forall esk8_0:set,
 forall k1_xboole_0:set,
 forall esk3_1:set -> set,
 forall esk7_2:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk4_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> r2_hidden (esk4_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> r2_hidden (esk4_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk6_2 X1 X2) X3 -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk5_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (esk6_2 X1 X2) (esk7_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> r2_hidden X2 (esk10_1 X1) -> r1_xboole_0 (esk11_2 X1 X2) X1 -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X3 X2 -> False) -> (r2_hidden X1 (esk10_1 X2) -> False) -> r2_hidden X3 X1 -> r2_hidden X1 (k3_tarski X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X1 X2 -> False) -> (r2_hidden X1 (esk12_1 X2) -> False) -> r2_hidden X1 (k3_tarski (k3_tarski X2)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X3 X2 X1, (r1_xboole_0 X1 (k2_xboole_0 X2 X3) -> False) -> r1_xboole_0 X1 X3 -> r1_xboole_0 X1 X2 -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 X2 -> False) -> r1_xboole_0 X1 (k2_xboole_0 X2 X3) -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 X2 -> False) -> r1_xboole_0 X1 (k2_xboole_0 X3 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> r2_hidden X2 (esk10_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski (k3_tarski X2)) -> False) -> r2_hidden X1 (esk12_1 X2) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> r1_xboole_0 X1 X2 -> r2_hidden X1 (esk12_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski X2) -> False) -> r2_hidden X1 (esk10_1 X2) -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, r2_hidden X1 esk1_0 -> r1_xboole_0 (esk2_1 X1) esk1_0 -> False)
  -> (forall X1, (r2_hidden (esk2_1 X1) (esk3_1 X1) -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (r2_hidden (esk3_1 X1) X1 -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r1_xboole_0 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk13_1 X1) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k2_xboole_0 X1 X2) X3) = (k2_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((v1_xboole_0 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
