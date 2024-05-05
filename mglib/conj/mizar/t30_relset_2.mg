(** $I sig/MizarPreamble.mgs **)

Theorem t30_relset_2:
 forall esk16_5:set -> set -> set -> set -> set -> set,
 forall a_4_3_relset_2:set -> set -> set -> set -> set,
 forall k8_setfam_1:set -> set -> set,
 forall k4_relset_2:set -> set -> set -> set,
 forall k6_partfun1:set -> set,
 forall k8_eqrel_1:set -> set -> set,
 forall k7_relset_1:set -> set -> set -> set -> set,
 forall k5_relset_2:set -> set -> set -> set -> set,
 forall k1_xboole_0:set,
 forall k7_relat_1:set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k1_setfam_1:set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall m1_eqrel_1:set -> set -> prop,
 forall k3_tarski:set -> set,
 forall esk12_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk31_2:set -> set -> set,
 forall k6_setfam_1:set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk10_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk29_1:set -> set,
 forall v1_relat_2:set -> prop,
 forall esk32_1:set -> set,
 forall v3_relat_1:set -> prop,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk5_0:set,
 forall esk25_0:set,
 forall esk19_2:set -> set -> set,
 forall esk22_1:set -> set,
 forall esk27_2:set -> set -> set,
 forall esk24_1:set -> set,
 forall esk15_1:set -> set,
 forall esk21_0:set,
 forall o_0_0_xboole_0:set,
 forall esk23_0:set,
 forall v4_relat_2:set -> prop,
 forall esk14_1:set -> set,
 forall esk17_2:set -> set -> set,
 forall esk18_0:set,
 forall esk28_1:set -> set,
 forall v2_relat_1:set -> prop,
 forall esk20_1:set -> set,
 forall esk9_2:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk26_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk11_3:set -> set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall k3_relset_2:set -> set -> set,
 forall v3_relat_2:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall v8_relat_2:set -> prop,
 forall k7_eqrel_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall k9_relat_1:set -> set -> set,
 forall k6_relset_2:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_relset_2:set -> set -> set -> set -> set,
 forall esk30_5:set -> set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X1 X4 X5 X2 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 (k6_relset_2 X2 X3 X5 X4) -> False) -> m1_subset_1 X1 X3 -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> r2_hidden X1 (k1_relset_2 X2 X3 X4 (esk30_5 X3 X2 X5 X1 X4)) -> False)
  -> (forall X2 X5 X1 X4 X3, ((k6_relset_2 X2 X3 (esk16_5 X1 X2 X3 X4 X5) X4) = X1 -> False) -> (v1_xboole_0 X3 -> False) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> r2_hidden X1 (a_4_3_relset_2 X2 X3 X4 X5) -> False)
  -> (forall X2 X5 X1 X4 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 (esk16_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> r2_hidden X1 (a_4_3_relset_2 X2 X3 X4 X5) -> False)
  -> (forall X2 X5 X1 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk16_5 X1 X2 X3 X4 X5) X5 -> False) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> r2_hidden X1 (a_4_3_relset_2 X2 X3 X4 X5) -> False)
  -> (forall X4 X5 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X4 (k6_relset_2 X2 X1 X3 X5) -> False) -> (r2_hidden (esk30_5 X1 X2 X3 X4 X5) X3 -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 X1)) -> False)
  -> (forall X1 X2 X6 X5 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 (k1_relset_2 X2 X3 X5 X6) -> False) -> m1_subset_1 X1 X3 -> r2_hidden X6 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> r2_hidden X1 (k6_relset_2 X2 X3 X4 X5) -> False)
  -> (forall X1 X4 X3 X6 X2 X5, (r2_hidden X5 (k1_relset_2 X2 X4 X3 X6) -> False) -> r2_hidden X6 X1 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> r2_hidden X5 (k6_relset_2 X2 X4 X1 X3) -> False)
  -> (forall X4 X3 X1 X2, ((k8_setfam_1 X4 (k7_relset_1 (k1_zfmisc_1 X2) (k1_zfmisc_1 X4) (k4_relset_2 X4 X2 X3) (k8_eqrel_1 X1 (k6_partfun1 X1)))) = (k5_relset_2 X2 X4 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> False)
  -> (forall X3 X2 X6 X5 X1 X4, (v1_xboole_0 X4 -> False) -> (r2_hidden X3 (a_4_3_relset_2 X2 X4 X5 X6) -> False) -> X3 = (k6_relset_2 X2 X4 X1 X5) -> r2_hidden X1 X6 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> False)
  -> (forall X1 X3 X2 X4, (X4 = k1_xboole_0 -> False) -> (k7_relset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 X2) (k4_relset_2 X2 X1 X3) (k8_eqrel_1 X4 (k6_partfun1 X4))) = k1_xboole_0 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X3 X1 X2, (m1_subset_1 (k6_relset_2 X2 X4 X1 X3) (k1_zfmisc_1 X4) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> False)
  -> (forall X4 X3 X1 X2, ((k6_relset_2 X2 X4 X1 X3) = (k5_relset_2 X2 X4 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k1_relset_2 X2 X3 X1 X4) (k1_zfmisc_1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k7_relset_1 X2 X3 X1 X4) (k1_zfmisc_1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X4 X3 X1, ((k7_relset_1 (k1_zfmisc_1 X2) (k1_zfmisc_1 X3) (k4_relset_2 X3 X2 X4) (k8_eqrel_1 X1 (k6_partfun1 X1))) = k1_xboole_0 -> False) -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X4 X1, ((k6_relset_2 X2 X4 X1 X3) = X4 -> False) -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> False)
  -> (forall X4 X1 X2 X3, ((k1_relset_2 X2 X3 X1 X4) = (k9_relat_1 X1 X4) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X1 X2 X3, ((k7_relset_1 X2 X3 X1 X4) = (k7_relat_1 X1 X4) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_relset_2 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 (k1_zfmisc_1 X2) (k1_zfmisc_1 X1))) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X1)) -> False)
  -> (forall X3 X2 X1, (v1_funct_2 (k4_relset_2 X1 X2 X3) (k1_zfmisc_1 X2) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X1)) -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k4_relset_2 X1 X2 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X1)) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X3 = (k1_setfam_1 X2) -> r2_hidden X1 (esk6_3 X2 X3 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k7_eqrel_1 X2 X1) (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> v3_relat_2 X1 -> v8_relat_2 X1 -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (m1_eqrel_1 (k8_eqrel_1 X2 X1) X2 -> False) -> v3_relat_2 X1 -> v8_relat_2 X1 -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X2 X3, ((k4_relset_2 X3 X2 X1) = (k3_relset_2 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, ((k7_eqrel_1 X2 X1) = (k8_eqrel_1 X2 X1) -> False) -> v3_relat_2 X1 -> v8_relat_2 X1 -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> r2_hidden (esk7_2 X1 X2) (esk8_2 X1 X2) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk12_2 X1 X2) X3 -> r2_hidden (esk12_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk11_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk11_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden X3 X2 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> X2 = (k1_setfam_1 X1) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> (r2_hidden (esk12_2 X1 X2) (esk13_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X1 -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X3 -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> r2_hidden X3 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk31_2 X3 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (k6_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk9_2 X1 X2) = X1 -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> (r2_hidden (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> ((k8_setfam_1 X2 X1) = (k6_setfam_1 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk10_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k1_setfam_1 X4) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k6_setfam_1 X2 X1) = (k1_setfam_1 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k8_setfam_1 X2 X1) = X2 -> False) -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk31_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk9_2 X1 X2) = X1 -> False) -> (r2_hidden (esk9_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk26_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk10_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_tarski (k1_setfam_1 X2) (k1_setfam_1 X1) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk26_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk26_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k7_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k7_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k7_relat_1 X1 (k1_tarski X2)) = (k9_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk26_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk26_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relset_2 X1 X2) -> False) -> v1_relat_1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relset_2 X1 X2) -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (k3_tarski X2) = k1_xboole_0 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_relat_1 X1 -> v3_relat_2 X1 -> v8_relat_2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_tarski X1) = k1_xboole_0 -> False) -> (r2_hidden (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k6_partfun1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> X2 = k1_xboole_0 -> X1 = (k1_setfam_1 X2) -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k3_tarski X1) = k1_xboole_0 -> False) -> (esk32_1 X1) = k1_xboole_0 -> False)
  -> (forall X2 X1, (X1 = (k1_setfam_1 X2) -> False) -> X2 = k1_xboole_0 -> X1 = k1_xboole_0 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k6_relset_2 esk1_0 esk2_0 (k5_setfam_1 esk1_0 esk4_0) esk3_0) = (k8_setfam_1 esk2_0 esk5_0) -> False)
  -> (forall X1, v1_subset_1 (esk28_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> (((a_4_3_relset_2 esk1_0 esk2_0 esk3_0 esk4_0) = esk5_0 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk17_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k6_partfun1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk2_0)) -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (k8_eqrel_1 X1 (k6_partfun1 X1)) X1 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk27_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk17_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk27_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk17_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (k1_zfmisc_1 esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_relat_1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k1_setfam_1 (k1_tarski X1)) = X1 -> False) -> False)
  -> (forall X1, (v4_relat_2 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_2 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_2 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v8_relat_2 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v8_relat_2 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v3_relat_2 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v3_relat_2 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk24_1 X1) -> False) -> False)
  -> ((v2_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
