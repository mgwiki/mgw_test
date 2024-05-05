(** $I sig/MizarPreamble.mgs **)

Theorem t5_xregular:
 forall v1_xboole_0:set -> prop,
 forall k3_tarski:set -> set,
 forall esk19_1:set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk7_3:set -> set -> set -> set,
 forall esk20_1:set -> set,
 forall esk12_1:set -> set,
 forall esk9_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk15_2:set -> set -> set,
 forall esk21_2:set -> set -> set,
 forall esk5_1:set -> set,
 forall esk4_1:set -> set,
 forall k1_xboole_0:set,
 forall esk10_0:set,
 forall esk11_0:set,
 forall esk22_1:set -> set,
 forall esk3_1:set -> set,
 forall esk2_1:set -> set,
 forall esk1_0:set,
 forall esk23_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall esk17_2:set -> set -> set,
 forall esk16_1:set -> set,
 forall esk8_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X1 X2 -> False) -> (r2_hidden X1 (esk19_1 X2) -> False) -> r2_hidden X1 (k3_tarski (k3_tarski (k3_tarski (k3_tarski X2)))) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk8_2 X1 X2) X3 -> r2_hidden (esk8_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk7_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X3 X2 -> False) -> (r2_hidden X1 (esk20_1 X2) -> False) -> r2_hidden X3 X1 -> r2_hidden X1 (k3_tarski (k3_tarski (k3_tarski X2))) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski (k3_tarski (k3_tarski (k3_tarski X2)))) -> False) -> r2_hidden X1 (esk19_1 X2) -> False)
  -> (forall X3 X5 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X3 X2 -> False) -> (r2_hidden X1 (esk12_1 X2) -> False) -> r2_hidden X5 X1 -> r2_hidden X4 X5 -> r2_hidden X3 X4 -> r2_hidden X1 (k3_tarski X2) -> False)
  -> (forall X3 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_xboole_0 X3 X2 -> False) -> (r2_hidden X1 (esk16_1 X2) -> False) -> r2_hidden X4 X1 -> r2_hidden X3 X4 -> r2_hidden X1 (k3_tarski (k3_tarski X2)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> (r2_hidden (esk8_2 X1 X2) (esk9_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk17_2 X1 X2) (esk18_2 X1 X2) -> False) -> r2_hidden X2 (esk16_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk14_2 X1 X2) (esk15_2 X1 X2) -> False) -> r2_hidden X2 (esk12_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk13_2 X1 X2) (esk14_2 X1 X2) -> False) -> r2_hidden X2 (esk12_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> r2_hidden X2 (esk20_1 X1) -> r1_xboole_0 (esk21_2 X1 X2) X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> r2_hidden X2 (esk16_1 X1) -> r1_xboole_0 (esk17_2 X1 X2) X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> r2_hidden X2 (esk12_1 X1) -> r1_xboole_0 (esk13_2 X1 X2) X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski (k3_tarski (k3_tarski X2))) -> False) -> r2_hidden X1 (esk20_1 X2) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X3 X2 X1, (r1_xboole_0 X1 (k2_xboole_0 X2 X3) -> False) -> r1_xboole_0 X1 X3 -> r1_xboole_0 X1 X2 -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 X2 -> False) -> r1_xboole_0 X1 (k2_xboole_0 X2 X3) -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 X2 -> False) -> r1_xboole_0 X1 (k2_xboole_0 X3 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk21_2 X1 X2) X2 -> False) -> r2_hidden X2 (esk20_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk18_2 X1 X2) X2 -> False) -> r2_hidden X2 (esk16_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk15_2 X1 X2) X2 -> False) -> r2_hidden X2 (esk12_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski (k3_tarski X2)) -> False) -> r2_hidden X1 (esk16_1 X2) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> r1_xboole_0 X1 X2 -> r2_hidden X1 (esk19_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k3_tarski X2) -> False) -> r2_hidden X1 (esk12_1 X2) -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk23_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk23_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, r2_hidden X1 esk1_0 -> r1_xboole_0 (esk2_1 X1) esk1_0 -> False)
  -> (forall X1, (r2_hidden (esk4_1 X1) (esk5_1 X1) -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X1, (r2_hidden (esk3_1 X1) (esk4_1 X1) -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X1, (r2_hidden (esk2_1 X1) (esk3_1 X1) -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (r2_hidden (esk5_1 X1) X1 -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r1_xboole_0 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk22_1 X1) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k2_xboole_0 X1 X2) X3) = (k2_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((v1_xboole_0 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
