(** $I sig/MizarPreamble.mgs **)

Theorem t2_bvfunc_2:
 forall m1_eqrel_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk9_4:set -> set -> set -> set -> set,
 forall r1_bvfunc_2:set -> set -> set -> prop,
 forall esk11_3:set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall k3_tarski:set -> set,
 forall k1_setfam_1:set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall k3_xboole_0:set -> set -> set,
 forall esk22_1:set -> set,
 forall esk24_1:set -> set,
 forall v2_card_3:set -> prop,
 forall esk27_1:set -> set,
 forall esk17_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk23_0:set,
 forall esk18_1:set -> set,
 forall v1_eqrel_1:set -> set -> prop,
 forall esk25_1:set -> set,
 forall esk21_1:set -> set,
 forall esk26_0:set,
 forall esk28_1:set -> set,
 forall esk8_1:set -> set,
 forall esk29_1:set -> set,
 forall v1_setfam_1:set -> prop,
 forall esk30_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk13_2:set -> set -> set,
 forall k6_setfam_1:set -> set -> set,
 forall esk31_2:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk15_2:set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall k3_subset_1:set -> set -> set,
 forall esk32_3:set -> set -> set -> set,
 forall k8_setfam_1:set -> set -> set,
 forall k1_xboole_0:set,
 forall esk19_4:set -> set -> set -> set -> set,
 forall a_3_0_bvfunc_2:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k1_partit1:set -> set,
 forall esk20_5:set -> set -> set -> set -> set -> set,
 forall r1_partit1:set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X2 X3 X4 X5 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X2 (a_3_0_bvfunc_2 X1 X3 X4) -> False) -> X2 = X5 -> m1_subset_1 X4 X1 -> r2_hidden X4 X5 -> m1_subset_1 X5 (k1_zfmisc_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_partit1 X1 (esk20_5 X2 X1 X3 X4 X5) X5 -> False)
  -> (forall X1 X3 X4 X5 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (a_3_0_bvfunc_2 X2 X3 X4) -> False) -> (m1_eqrel_1 (esk20_5 X1 X2 X3 X4 X5) X2 -> False) -> X1 = X5 -> m1_subset_1 X4 X2 -> r2_hidden X4 X5 -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> False)
  -> (forall X1 X3 X4 X5 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (a_3_0_bvfunc_2 X2 X3 X4) -> False) -> (r2_hidden (esk20_5 X1 X2 X3 X4 X5) X3 -> False) -> X1 = X5 -> m1_subset_1 X4 X2 -> r2_hidden X4 X5 -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (v1_xboole_0 X1 -> False) -> r1_tarski X4 X3 -> r1_bvfunc_2 X1 X2 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_partit1 X1 (esk9_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X5 X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> (r1_partit1 X2 X1 (esk19_4 X4 X2 X3 X5) -> False) -> m1_subset_1 X5 X2 -> r2_hidden X1 X3 -> m1_eqrel_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> r2_hidden X4 (a_3_0_bvfunc_2 X2 X3 X5) -> False)
  -> (forall X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk19_4 X1 X2 X3 X4) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> r2_hidden X1 (a_3_0_bvfunc_2 X2 X3 X4) -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 (esk19_4 X2 X3 X4 X1) -> False) -> m1_subset_1 X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_partit1 X3)) -> r2_hidden X2 (a_3_0_bvfunc_2 X3 X4 X1) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk9_4 X1 X2 X3 X4) X1 -> False) -> r1_tarski X4 X3 -> r1_bvfunc_2 X1 X2 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X2 -> False) -> r1_tarski X4 X3 -> r1_bvfunc_2 X1 X2 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_bvfunc_2 X2 X3 X4 -> False) -> (r1_partit1 X2 X1 (esk11_3 X2 X3 X4) -> False) -> r2_hidden X1 X3 -> m1_eqrel_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> r1_partit1 X2 (esk10_3 X2 X3 X4) X4 -> False)
  -> (forall X4 X1 X3 X2, ((esk19_4 X1 X2 X3 X4) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> r2_hidden X1 (a_3_0_bvfunc_2 X2 X3 X4) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk16_3 X1 X2 X3) X3 -> r2_hidden (esk16_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_2 X1 X2 X3 -> False) -> (r1_tarski (esk11_3 X1 X2 X3) X3 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_partit1 X1 (esk10_3 X1 X2 X3) X3 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_2 X1 X2 X3 -> False) -> (esk11_3 X1 X2 X3) = X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_partit1 X1 (esk10_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_bvfunc_2 X2 X3 X4 -> False) -> (m1_eqrel_1 (esk10_3 X2 X3 X4) X2 -> False) -> (r1_partit1 X2 X1 (esk11_3 X2 X3 X4) -> False) -> r2_hidden X1 X3 -> m1_eqrel_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_bvfunc_2 X2 X3 X4 -> False) -> (r2_hidden (esk10_3 X2 X3 X4) X3 -> False) -> (r1_partit1 X2 X1 (esk11_3 X2 X3 X4) -> False) -> r2_hidden X1 X3 -> m1_eqrel_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> False)
  -> (forall X2 X3 X1, ((k8_setfam_1 X1 X3) = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 (k8_setfam_1 X1 X3) -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r1_partit1 X1 X2 (esk32_3 X1 X2 X3) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_2 X1 X2 X3 -> False) -> (m1_eqrel_1 (esk10_3 X1 X2 X3) X1 -> False) -> (r1_tarski (esk11_3 X1 X2 X3) X3 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_2 X1 X2 X3 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X2 -> False) -> (r1_tarski (esk11_3 X1 X2 X3) X3 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk16_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_2 X1 X2 X3 -> False) -> (m1_eqrel_1 (esk10_3 X1 X2 X3) X1 -> False) -> (esk11_3 X1 X2 X3) = X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_2 X1 X2 X3 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X2 -> False) -> (esk11_3 X1 X2 X3) = X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X2 X3 X1, ((k8_setfam_1 X1 X3) = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk32_3 X1 X2 X3) X3 -> False) -> (r1_partit1 X1 X2 (k8_setfam_1 X1 X3) -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (r1_partit1 X2 X1 X4 -> False) -> r2_hidden X1 X3 -> m1_eqrel_1 X1 X2 -> r1_bvfunc_2 X2 X3 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_tarski (esk4_3 X1 X2 X3) X2 -> False) -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X2 X3 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 (k3_subset_1 X1 X3) -> False) -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, ((k3_tarski (esk4_3 X2 X3 X1)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> m1_eqrel_1 X3 X2 -> r1_partit1 X2 X3 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (a_3_0_bvfunc_2 X1 X2 X3) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X3 = (k1_setfam_1 X2) -> r2_hidden X1 (esk5_3 X2 X3 X1) -> False)
  -> (forall X1 X2, ((esk14_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r1_xboole_0 (esk14_2 X1 X2) (esk15_2 X1 X2) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> (r1_xboole_0 X4 X1 -> False) -> r2_hidden X4 X3 -> r2_hidden X1 X3 -> m1_eqrel_1 X3 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (esk4_3 X1 X2 X3) = k1_xboole_0 -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X2 X3 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> r2_hidden (esk6_2 X1 X2) (esk7_2 X1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, ((esk14_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk15_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, ((esk14_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> (esk15_2 X1 X2) = (esk14_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden X3 X2 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> X2 = (k1_setfam_1 X1) -> False)
  -> (forall X1 X2, ((esk14_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk15_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> r1_xboole_0 X1 (k3_subset_1 X2 X3) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk14_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (X2 = (k1_partit1 X1) -> False) -> r2_hidden (esk12_2 X1 X2) X2 -> m1_eqrel_1 (esk12_2 X1 X2) X1 -> False)
  -> (forall X2 X3 X1, X1 = k1_xboole_0 -> r2_hidden X1 X2 -> m1_eqrel_1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1, r2_hidden esk3_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 esk1_0) -> r1_bvfunc_2 esk1_0 esk2_0 X1 -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 (k3_subset_1 X3 X2) -> False) -> r1_tarski X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, (X1 = k1_xboole_0 -> False) -> (v1_xboole_0 X4 -> False) -> (r1_partit1 X4 X2 X3 -> False) -> X3 = (k3_tarski X1) -> m1_eqrel_1 X2 X4 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X3 -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> r2_hidden X3 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk31_2 X3 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k6_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, ((k5_setfam_1 X1 X2) = X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k3_xboole_0 X1 X3) (k3_xboole_0 X2 X3) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (X2 = (k1_partit1 X1) -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> (m1_eqrel_1 (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 X1 -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> ((k8_setfam_1 X2 X1) = (k6_setfam_1 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_subset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk13_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k4_xboole_0 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 (k3_subset_1 X2 X1)) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k1_setfam_1 X4) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k6_setfam_1 X2 X1) = (k1_setfam_1 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k4_xboole_0 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k8_setfam_1 X2 X1) = X2 -> False) -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (r2_hidden (esk31_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k4_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 X1) = (k4_xboole_0 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski (k3_tarski X1) (k3_tarski X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (m1_eqrel_1 X1 X3 -> False) -> X2 = (k1_partit1 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k1_partit1 X2) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> r1_tarski X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk29_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk24_1 X1) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> X2 = k1_xboole_0 -> X1 = (k1_setfam_1 X2) -> False)
  -> (forall X1, (v2_card_3 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = (k1_setfam_1 X2) -> False) -> X2 = k1_xboole_0 -> X1 = k1_xboole_0 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk28_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_partit1 X1) -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (esk2_0 = k1_xboole_0 -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_partit1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k4_xboole_0 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_partit1 esk1_0)) -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (k1_partit1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((m1_subset_1 esk3_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk25_1 X1) -> False) -> False)
  -> ((v1_xboole_0 esk23_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
