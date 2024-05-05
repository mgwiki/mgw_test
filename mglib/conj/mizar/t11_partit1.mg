(** $I sig/MizarPreamble.mgs **)

Theorem t11_partit1:
 forall esk10_4:set -> set -> set -> set -> set,
 forall r2_partit1:set -> set -> set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall k3_subset_1:set -> set -> set,
 forall k1_setfam_1:set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v5_membered:set -> prop,
 forall v3_membered:set -> prop,
 forall v1_membered:set -> prop,
 forall v1_int_1:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall esk28_1:set -> set,
 forall v1_setfam_1:set -> prop,
 forall esk9_1:set -> set,
 forall esk21_1:set -> set,
 forall esk26_1:set -> set,
 forall esk25_0:set,
 forall esk22_0:set,
 forall esk23_1:set -> set,
 forall esk15_1:set -> set,
 forall esk20_0:set,
 forall esk16_1:set -> set,
 forall esk18_0:set,
 forall esk24_0:set,
 forall v7_membered:set -> prop,
 forall esk27_1:set -> set,
 forall esk19_1:set -> set,
 forall v1_xxreal_0:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v2_membered:set -> prop,
 forall v4_membered:set -> prop,
 forall v6_membered:set -> prop,
 forall k6_setfam_1:set -> set -> set,
 forall esk29_2:set -> set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk13_2:set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall esk30_3:set -> set -> set -> set,
 forall k8_setfam_1:set -> set -> set,
 forall k1_xboole_0:set,
 forall esk14_3:set -> set -> set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk17_5:set -> set -> set -> set -> set -> set,
 forall r1_partit1:set -> set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall a_4_1_partit1:set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall m1_eqrel_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X4 X5 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 (esk17_5 X3 X1 X2 X4 X5) -> False) -> m1_eqrel_1 X4 X1 -> m1_eqrel_1 X2 X1 -> m1_subset_1 X5 X1 -> r2_hidden X3 (a_4_1_partit1 X1 X2 X4 X5) -> False)
  -> (forall X4 X5 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 (esk17_5 X3 X1 X4 X2 X5) -> False) -> m1_eqrel_1 X4 X1 -> m1_eqrel_1 X2 X1 -> m1_subset_1 X5 X1 -> r2_hidden X3 (a_4_1_partit1 X1 X4 X2 X5) -> False)
  -> (forall X4 X5 X1 X3 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk17_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 X2) -> False) -> m1_eqrel_1 X4 X2 -> m1_eqrel_1 X3 X2 -> m1_subset_1 X5 X2 -> r2_hidden X1 (a_4_1_partit1 X2 X3 X4 X5) -> False)
  -> (forall X5 X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 (esk17_5 X2 X3 X4 X5 X1) -> False) -> m1_eqrel_1 X5 X3 -> m1_eqrel_1 X4 X3 -> m1_subset_1 X1 X3 -> r2_hidden X2 (a_4_1_partit1 X3 X4 X5 X1) -> False)
  -> (forall X4 X5 X1 X3 X2, ((esk17_5 X1 X2 X3 X4 X5) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> m1_eqrel_1 X4 X2 -> m1_eqrel_1 X3 X2 -> m1_subset_1 X5 X2 -> r2_hidden X1 (a_4_1_partit1 X2 X3 X4 X5) -> False)
  -> (forall X3 X4 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_partit1 X1 X2 X3 X4 -> False) -> (r1_partit1 X1 X2 (esk10_4 X1 X2 X3 X4) -> False) -> m1_eqrel_1 X3 X1 -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X3 X4 -> r1_partit1 X1 X2 X4 -> False)
  -> (forall X3 X4 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_partit1 X1 X3 X2 X4 -> False) -> (r1_partit1 X1 X2 (esk10_4 X1 X3 X2 X4) -> False) -> m1_eqrel_1 X3 X1 -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X3 X4 -> r1_partit1 X1 X2 X4 -> False)
  -> (forall X3 X4 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_partit1 X1 X2 X3 X4 -> False) -> (r1_tarski (esk10_4 X1 X2 X3 X4) X4 -> False) -> m1_eqrel_1 X3 X1 -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X3 X4 -> r1_partit1 X1 X2 X4 -> False)
  -> (forall X3 X4 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_partit1 X1 X2 X3 X4 -> False) -> (esk10_4 X1 X2 X3 X4) = X4 -> m1_eqrel_1 X3 X1 -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X3 X4 -> r1_partit1 X1 X2 X4 -> False)
  -> (forall X3 X4 X6 X5 X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X3 (a_4_1_partit1 X2 X5 X6 X4) -> False) -> X1 = X3 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X5 X2 -> m1_subset_1 X4 X2 -> r2_hidden X4 X1 -> r1_partit1 X2 X6 X1 -> r1_partit1 X2 X5 X1 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X4 X5 X1 X2, (X1 = X2 -> False) -> (v1_xboole_0 X3 -> False) -> m1_eqrel_1 X5 X3 -> m1_eqrel_1 X4 X3 -> r1_tarski X1 X2 -> r1_partit1 X3 X5 X1 -> r1_partit1 X3 X4 X1 -> r2_partit1 X3 X4 X5 X2 -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (a_4_1_partit1 X1 X2 X3 X4) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> m1_eqrel_1 X3 X1 -> m1_eqrel_1 X2 X1 -> m1_subset_1 X4 X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk14_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk14_3 X1 X2 X3) X3 -> r2_hidden (esk14_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 X3 -> False) -> m1_eqrel_1 X4 X1 -> m1_eqrel_1 X2 X1 -> r2_partit1 X1 X2 X4 X3 -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 X3 -> False) -> m1_eqrel_1 X4 X1 -> m1_eqrel_1 X2 X1 -> r2_partit1 X1 X4 X2 X3 -> False)
  -> (forall X1, r2_hidden esk4_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 esk1_0) -> r2_partit1 esk1_0 esk2_0 esk3_0 X1 -> False)
  -> (forall X2 X3 X1, ((k8_setfam_1 X1 X3) = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 (k8_setfam_1 X1 X3) -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r1_partit1 X1 X2 (esk30_3 X1 X2 X3) -> False)
  -> (forall X2 X3 X1, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk14_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk14_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X3 X1, ((k8_setfam_1 X1 X3) = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk30_3 X1 X2 X3) X3 -> False) -> (r1_partit1 X1 X2 (k8_setfam_1 X1 X3) -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk14_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk14_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_tarski (esk5_3 X1 X2 X3) X2 -> False) -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X2 X3 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 (k3_subset_1 X1 X3) -> False) -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, ((k3_tarski (esk5_3 X2 X3 X1)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> m1_eqrel_1 X3 X2 -> r1_partit1 X2 X3 X1 -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X3 = (k1_setfam_1 X2) -> r2_hidden X1 (esk6_3 X2 X3 X1) -> False)
  -> (forall X1 X2, ((esk12_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r1_xboole_0 (esk12_2 X1 X2) (esk13_2 X1 X2) -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> (r1_xboole_0 X4 X1 -> False) -> m1_eqrel_1 X3 X2 -> r2_hidden X4 X3 -> r2_hidden X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (esk5_3 X1 X2 X3) = k1_xboole_0 -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X2 X3 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> r2_hidden (esk7_2 X1 X2) (esk8_2 X1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, ((esk12_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, ((esk12_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> (esk13_2 X1 X2) = (esk12_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden X3 X2 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> X2 = (k1_setfam_1 X1) -> False)
  -> (forall X1 X2, ((esk12_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk13_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> r1_xboole_0 X1 (k3_subset_1 X2 X3) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk12_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, X1 = k1_xboole_0 -> m1_eqrel_1 X2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 (k3_subset_1 X3 X2) -> False) -> r1_tarski X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, (X1 = k1_xboole_0 -> False) -> (v1_xboole_0 X4 -> False) -> (r1_partit1 X4 X2 X3 -> False) -> X3 = (k3_tarski X1) -> m1_eqrel_1 X2 X4 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X1 -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X3 -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> r2_hidden X3 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk29_2 X3 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k6_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, ((k5_setfam_1 X1 X2) = X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k3_xboole_0 X1 X3) (k3_xboole_0 X2 X3) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 X1 -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> ((k8_setfam_1 X2 X1) = (k6_setfam_1 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_subset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk11_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k4_xboole_0 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 (k3_subset_1 X2 X1)) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k1_setfam_1 X4) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k6_setfam_1 X2 X1) = (k1_setfam_1 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k4_xboole_0 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k8_setfam_1 X2 X1) = X2 -> False) -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (r2_hidden (esk29_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k4_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 X1) = (k4_xboole_0 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski (k3_tarski X1) (k3_tarski X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v6_membered (k4_xboole_0 X1 X2) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (v6_membered (k3_xboole_0 X1 X2) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (v6_membered (k3_xboole_0 X2 X1) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (v5_membered (k4_xboole_0 X1 X2) -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, (v5_membered (k3_xboole_0 X1 X2) -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, (v5_membered (k3_xboole_0 X2 X1) -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k4_xboole_0 X1 X2) -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k3_xboole_0 X1 X2) -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k3_xboole_0 X2 X1) -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v3_membered (k4_xboole_0 X1 X2) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v3_membered (k3_xboole_0 X1 X2) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v3_membered (k3_xboole_0 X2 X1) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k4_xboole_0 X1 X2) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k3_xboole_0 X1 X2) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k3_xboole_0 X2 X1) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k4_xboole_0 X1 X2) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k3_xboole_0 X1 X2) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k3_xboole_0 X2 X1) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> r1_tarski X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk21_1 X1) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> X2 = k1_xboole_0 -> X1 = (k1_setfam_1 X2) -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (X1 = (k1_setfam_1 X2) -> False) -> X2 = k1_xboole_0 -> X1 = k1_xboole_0 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk26_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X1 X2, (m1_subset_1 (k4_xboole_0 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((m1_subset_1 esk4_0 esk1_0 -> False) -> False)
  -> ((m1_eqrel_1 esk3_0 esk1_0 -> False) -> False)
  -> ((m1_eqrel_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk23_1 X1) -> False) -> False)
  -> ((v7_membered esk25_0 -> False) -> False)
  -> ((v6_membered esk25_0 -> False) -> False)
  -> ((v6_membered esk22_0 -> False) -> False)
  -> ((v6_membered esk18_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
