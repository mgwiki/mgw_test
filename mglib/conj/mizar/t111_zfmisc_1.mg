(** $I sig/MizarPreamble.mgs **)

Theorem t111_zfmisc_1:
 forall esk9_3:set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall esk13_3:set -> set -> set -> set,
 forall esk17_1:set -> set,
 forall esk16_1:set -> set,
 forall esk20_1:set -> set,
 forall esk4_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk11_2:set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk24_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk23_1:set -> set,
 forall k1_xboole_0:set,
 forall esk25_1:set -> set,
 forall esk19_0:set,
 forall o_0_0_xboole_0:set,
 forall esk18_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk22_2:set -> set -> set,
 forall esk21_2:set -> set -> set,
 forall esk15_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall esk7_4:set -> set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X3 X2 X4 X1, ((k2_tarski (k2_tarski (esk6_4 X2 X3 X4 X1) (esk7_4 X2 X3 X4 X1)) (k1_tarski (esk6_4 X2 X3 X4 X1))) = X1 -> False) -> X4 = (k2_zfmisc_1 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> ((k2_tarski (k2_tarski (esk9_3 X1 X2 X3) (esk10_3 X1 X2 X3)) (k1_tarski (esk9_3 X1 X2 X3))) = (esk8_3 X1 X2 X3) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk7_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk6_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X5 X4 X1 X2 X3, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (esk8_3 X1 X2 X3) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden (esk8_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk12_3 X1 X2 X3) X3 -> r2_hidden (esk12_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk12_3 X1 X2 X3) X3 -> r2_hidden (esk12_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> (esk5_3 X1 X2 X3) = X1 -> r2_hidden (esk5_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> (esk5_3 X1 X2 X3) = X2 -> r2_hidden (esk5_3 X1 X2 X3) X3 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> ((esk5_3 X1 X2 X3) = X2 -> False) -> ((esk5_3 X1 X2 X3) = X1 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k2_zfmisc_1 X2 X4) -> X5 = (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk14_2 X1 X2) X3 -> r2_hidden (esk14_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk13_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk13_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X3 X1, ((k2_tarski (k2_tarski (esk16_1 X1) (esk17_1 X1)) (k1_tarski (esk16_1 X1))) = X1 -> False) -> r2_hidden X1 (k2_zfmisc_1 X2 X3) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> (r2_hidden (esk14_2 X1 X2) (esk15_2 X1 X2) -> False) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 (esk20_1 X2) -> False) -> X1 = X3 -> r2_hidden X4 X3 -> r2_hidden X4 X2 -> r2_hidden X1 (k3_tarski X2) -> False)
  -> (forall X1 X2, (r2_hidden (esk22_2 X1 X2) (esk21_2 X1 X2) -> False) -> r2_hidden X2 (esk20_1 X1) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk4_2 X1 X2) = X1 -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> (r2_hidden (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk11_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r2_hidden (esk22_2 X1 X2) X1 -> False) -> r2_hidden X2 (esk20_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> ((r1_tarski esk1_0 (k2_zfmisc_1 esk1_0 esk2_0) -> False) -> (r1_tarski esk1_0 (k2_zfmisc_1 esk3_0 esk1_0) -> False) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk4_2 X1 X2) = X1 -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk24_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk24_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r2_hidden X1 (k3_tarski X2) -> False) -> r2_hidden X1 (esk20_1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> (X1 = X3 -> False) -> X2 = (k2_tarski X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((esk21_2 X2 X1) = X1 -> False) -> r2_hidden X1 (esk20_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X2 X4) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X4 X2) -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r1_xboole_0 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk25_1 X1) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, v1_xboole_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (esk1_0 = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
