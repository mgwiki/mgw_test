(** $I sig/MizarPreamble.mgs **)

Theorem t13_interva1:
 forall k2_setfam_1:set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk7_4:set -> set -> set -> set -> set,
 forall esk8_4:set -> set -> set -> set -> set,
 forall k8_subset_1:set -> set -> set -> set,
 forall esk23_2:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk22_1:set -> set,
 forall k1_xboole_0:set,
 forall esk21_1:set -> set,
 forall esk20_0:set,
 forall esk19_1:set -> set,
 forall esk13_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk18_0:set,
 forall esk12_1:set -> set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk5_0:set,
 forall esk2_0:set,
 forall esk16_1:set -> set,
 forall esk17_1:set -> set,
 forall esk6_2:set -> set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall k2_interva1:set -> set -> set -> set,
 forall m1_interva1:set -> set -> prop,
 forall k1_interva1:set -> set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall a_3_0_interva1:set -> set -> set -> set,
 forall esk14_4:set -> set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk15_6:set -> set -> set -> set -> set -> set -> set,
 forall k4_subset_1:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_5_1_interva1:set -> set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
     (forall X6 X4 X1 X3 X5 X2, (v1_xboole_0 X2 -> False) -> (r1_tarski (esk15_6 X1 X2 X3 X4 X5 X6) (k4_subset_1 X2 X4 X6) -> False) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_5_1_interva1 X2 X3 X4 X5 X6) -> False)
  -> (forall X6 X3 X4 X2 X5 X1, (v1_xboole_0 X1 -> False) -> (r1_tarski (k4_subset_1 X1 X2 X3) (esk15_6 X4 X1 X2 X5 X3 X6) -> False) -> m1_subset_1 X6 (k1_zfmisc_1 X1) -> m1_subset_1 X5 (k1_zfmisc_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r2_hidden X4 (a_5_1_interva1 X1 X2 X5 X3 X6) -> False)
  -> (forall X6 X4 X1 X3 X5 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk15_6 X1 X2 X3 X4 X5 X6) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_5_1_interva1 X2 X3 X4 X5 X6) -> False)
  -> (forall X6 X4 X1 X3 X5 X2, ((esk15_6 X1 X2 X3 X4 X5 X6) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_5_1_interva1 X2 X3 X4 X5 X6) -> False)
  -> (forall X3 X6 X5 X7 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X3 (a_5_1_interva1 X2 X4 X6 X5 X7) -> False) -> X1 = X3 -> m1_subset_1 X7 (k1_zfmisc_1 X2) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> r1_tarski X1 (k4_subset_1 X2 X6 X7) -> r1_tarski (k4_subset_1 X2 X4 X5) X1 -> False)
  -> (forall X3 X2 X4 X1, ((k2_xboole_0 (esk7_4 X2 X3 X4 X1) (esk8_4 X2 X3 X4 X1)) = X1 -> False) -> X4 = (k2_setfam_1 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X3 X1 X4 X2, (m1_subset_1 (esk14_4 X1 X2 X3 X4) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_0_interva1 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (r1_tarski (esk14_4 X1 X2 X3 X4) X4 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_0_interva1 X2 X3 X4) -> False)
  -> (forall X1 X2 X4 X3, (r1_tarski X1 (esk14_4 X2 X3 X1 X4) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> r2_hidden X2 (a_3_0_interva1 X3 X1 X4) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk8_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k2_setfam_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk7_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k2_setfam_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X3 X1 X4 X2, ((esk14_4 X1 X2 X3 X4) = X1 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_0_interva1 X2 X3 X4) -> False)
  -> (forall X3 X2 X1, (X3 = (k2_setfam_1 X1 X2) -> False) -> ((k2_xboole_0 (esk10_3 X1 X2 X3) (esk11_3 X1 X2 X3)) = (esk9_3 X1 X2 X3) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X5 X4 X1 X2 X3, (X3 = (k2_setfam_1 X1 X2) -> False) -> (esk9_3 X1 X2 X3) = (k2_xboole_0 X4 X5) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden (esk9_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X4 X1 X2, (r1_tarski X1 X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> r2_hidden X2 (k1_interva1 X3 X1 X4) -> False)
  -> (forall X3 X4 X1 X2, (r1_tarski X1 X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> r2_hidden X1 (k1_interva1 X3 X4 X2) -> False)
  -> (forall X1 X5 X4 X2 X3, (r2_hidden X3 (a_3_0_interva1 X2 X4 X5) -> False) -> X1 = X3 -> r1_tarski X4 X1 -> r1_tarski X1 X5 -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_setfam_1 X1 X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_setfam_1 X1 X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X4 X2 X3, (r2_hidden X2 (k1_interva1 X4 X1 X3) -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X1 (k1_zfmisc_1 X4) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k1_interva1 X2 X1 X3) (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_interva1 (k2_interva1 X2 X1 X3) X2 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((a_3_0_interva1 X2 X1 X3) = (k1_interva1 X2 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k2_interva1 X2 X1 X3) = (k1_interva1 X2 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k8_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k8_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X4 X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) (k2_xboole_0 X2 X4) -> False) -> r1_tarski X3 X4 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk23_2 X3 X2) -> False)
  -> (forall X4 X2 X1 X3 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k2_setfam_1 X2 X4) -> X5 = (k2_xboole_0 X1 X3) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k3_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k8_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) X2 -> False) -> r1_tarski X3 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk23_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_interva1 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = X1 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_interva1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_setfam_1 (k2_interva1 esk1_0 esk2_0 esk3_0) (k2_interva1 esk1_0 esk4_0 esk5_0)) = (a_5_1_interva1 esk1_0 esk2_0 esk3_0 esk4_0 esk5_0) -> False)
  -> (forall X1, v1_subset_1 (esk21_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k3_xboole_0 X1 X2) (k3_xboole_0 X1 X3)) = (k3_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k2_xboole_0 X1 X2) X3) = (k2_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X1 X2, (r1_tarski (k3_xboole_0 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_setfam_1 X1 X2) = (k2_setfam_1 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_interva1 (esk12_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((r1_tarski esk4_0 esk5_0 -> False) -> False)
  -> ((r1_tarski esk2_0 esk3_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.