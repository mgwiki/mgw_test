(** $I sig/MizarPreamble.mgs **)

Theorem l18_taxonom2:
 forall k2_xboole_0:set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall esk24_3:set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v4_taxonom2:set -> prop,
 forall esk3_0:set,
 forall esk2_0:set,
 forall k5_setfam_1:set -> set -> set,
 forall esk1_0:set,
 forall k3_tarski:set -> set,
 forall esk10_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall v3_taxonom2:set -> prop,
 forall m1_taxonom2:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk6_1:set -> set,
 forall esk7_1:set -> set,
 forall esk17_1:set -> set,
 forall esk21_1:set -> set,
 forall esk20_0:set,
 forall esk19_1:set -> set,
 forall esk16_1:set -> set,
 forall esk18_0:set,
 forall esk15_1:set -> set,
 forall esk22_1:set -> set,
 forall k1_xboole_0:set,
 forall esk23_1:set -> set,
 forall esk13_1:set -> set,
 forall esk12_1:set -> set,
 forall esk5_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall k1_tarski:set -> set,
 forall v3_abian:set -> set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall k7_subset_1:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk14_3:set -> set -> set -> set,
 forall k4_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk14_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk14_3 X1 X2 X3) X3 -> r2_hidden (esk14_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk14_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk14_3 X1 X2 X3) X2 -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> v4_taxonom2 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r2_hidden X1 (esk24_3 X3 X2 X4) -> False)
  -> (forall X4 X3 X1 X2, (r1_tarski X1 X2 -> False) -> v4_taxonom2 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r2_hidden X1 (esk24_3 X3 X4 X2) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk14_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk14_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X1 X4 X2, (r2_hidden X1 (esk24_3 X4 X2 X3) -> False) -> v4_taxonom2 X2 -> r1_tarski X1 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X4)) -> False)
  -> (forall X1, (esk3_0 = X1 -> False) -> v4_taxonom2 X1 -> r1_tarski X1 esk2_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> r1_tarski (k5_setfam_1 esk1_0 esk3_0) (k5_setfam_1 esk1_0 X1) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk10_2 X1 X2) X3 -> r2_hidden (esk10_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk9_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk9_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = X2 -> False) -> v3_abian X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> (r2_hidden (esk10_2 X1 X2) (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X3 X2, (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (r1_xboole_0 X2 X3 -> False) -> v3_taxonom2 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk4_2 X1 X2) = X1 -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> (r2_hidden (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) X2 -> False) -> r1_tarski X3 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v3_taxonom2 X1 -> False) -> m1_taxonom2 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k4_xboole_0 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_taxonom2 X1 X2 -> False) -> v3_taxonom2 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k4_xboole_0 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (r1_xboole_0 X2 X3 -> False) -> v4_taxonom2 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k4_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk4_2 X1 X2) = X1 -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_taxonom2 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk5_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> r1_xboole_0 (esk6_1 X1) (esk7_1 X1) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> r1_tarski (esk7_1 X1) (esk6_1 X1) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> r1_tarski (esk6_1 X1) (esk7_1 X1) -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> r1_xboole_0 (esk12_1 X1) (esk13_1 X1) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> (r2_hidden (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> (r2_hidden (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> (r2_hidden (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> (r2_hidden (esk12_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> (esk13_1 X1) = (esk12_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk21_1 X1) X1 -> False)
  -> ((k5_setfam_1 esk1_0 esk3_0) = esk1_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (forall X1 X2, (r1_tarski (k4_xboole_0 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> False) -> False)
  -> ((v3_abian esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_taxonom2 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((r1_tarski esk3_0 esk2_0 -> False) -> False)
  -> ((m1_taxonom2 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v4_taxonom2 (esk22_1 X1) -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v4_taxonom2 esk3_0 -> False) -> False)
  -> False.
Admitted.
