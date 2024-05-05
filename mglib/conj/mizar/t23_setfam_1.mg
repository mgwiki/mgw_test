(** $I sig/MizarPreamble.mgs **)

Theorem t23_setfam_1:
 forall esk7_3:set -> set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk14_1:set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk17_0:set,
 forall esk13_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk15_0:set,
 forall esk16_1:set -> set,
 forall o_2_0_setfam_1:set -> set -> set,
 forall esk18_1:set -> set,
 forall esk19_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk3_3:set -> set -> set -> set,
 forall k1_setfam_1:set -> set,
 forall k1_xboole_0:set,
 forall esk10_3:set -> set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall esk9_4:set -> set -> set -> set -> set,
 forall esk8_4:set -> set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall k3_setfam_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X3 X2 X4 X1, ((k3_xboole_0 (esk8_4 X2 X3 X4 X1) (esk9_4 X2 X3 X4 X1)) = X1 -> False) -> X4 = (k3_setfam_1 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X2 -> r2_hidden (esk7_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk9_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k3_setfam_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk8_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k3_setfam_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k3_setfam_1 X1 X2) -> False) -> ((k3_xboole_0 (esk11_3 X1 X2 X3) (esk12_3 X1 X2 X3)) = (esk10_3 X1 X2 X3) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X5 X4 X1 X2 X3, (X3 = (k3_setfam_1 X1 X2) -> False) -> (esk10_3 X1 X2 X3) = (k3_xboole_0 X4 X5) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden (esk10_3 X1 X2 X3) X3 -> False)
  -> (forall X2 X3 X1, (X3 = (k3_setfam_1 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_setfam_1 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X3 = (k1_setfam_1 X2) -> r2_hidden X1 (esk3_3 X2 X3 X1) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> r2_hidden (esk4_2 X1 X2) X2 -> r2_hidden (esk4_2 X1 X2) (esk5_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden X3 X2 -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X1 -> False) -> X2 = (k1_setfam_1 X1) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk5_2 X1 X2) X1 -> False) -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk4_2 X1 X2) X3 -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> r2_hidden X3 X1 -> False)
  -> (forall X4 X2 X1 X3 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k3_setfam_1 X2 X4) -> X5 = (k3_xboole_0 X1 X3) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k1_setfam_1 X4) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk14_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> X2 = k1_xboole_0 -> X1 = (k1_setfam_1 X2) -> False)
  -> (forall X2 X1, (X1 = (k1_setfam_1 X2) -> False) -> X2 = k1_xboole_0 -> X1 = k1_xboole_0 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k1_setfam_1 (k3_setfam_1 esk1_0 esk2_0)) = (k3_xboole_0 (k1_setfam_1 esk1_0) (k1_setfam_1 esk2_0)) -> False)
  -> (forall X1, v1_subset_1 (esk18_1 X1) X1 -> False)
  -> (r1_xboole_0 esk1_0 esk2_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (forall X1 X2, (m1_subset_1 (o_2_0_setfam_1 X1 X2) (k3_xboole_0 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_setfam_1 X1 X2) = (k3_setfam_1 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk16_1 X1) -> False) -> False)
  -> ((v1_xboole_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
