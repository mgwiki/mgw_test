(** $I sig/MizarPreamble.mgs **)

Theorem t7_bvfunc11:
 forall esk6_4:set -> set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall k4_subset_1:set -> set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall esk25_2:set -> set -> set,
 forall k6_setfam_1:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk12_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall k3_tarski:set -> set,
 forall v1_funcop_1:set -> prop,
 forall v1_setfam_1:set -> prop,
 forall v2_funcop_1:set -> prop,
 forall esk26_1:set -> set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk4_0:set,
 forall esk22_0:set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall esk18_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk27_1:set -> set,
 forall v1_eqrel_1:set -> set -> prop,
 forall esk17_1:set -> set,
 forall esk20_0:set,
 forall o_0_0_xboole_0:set,
 forall esk19_0:set,
 forall esk16_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk23_0:set,
 forall esk24_1:set -> set,
 forall v2_card_3:set -> prop,
 forall esk21_1:set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall v2_relat_1:set -> prop,
 forall k1_setfam_1:set -> set,
 forall esk13_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall k4_xboole_0:set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk15_2:set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall k5_bvfunc_2:set -> set -> set -> set,
 forall k7_subset_1:set -> set -> set -> set,
 forall k4_bvfunc_2:set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall esk5_4:set -> set -> set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall esk9_5:set -> set -> set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall k8_setfam_1:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall m1_eqrel_1:set -> set -> prop,
 forall esk7_6:set -> set -> set -> set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k1_bvfunc_2:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_funct_1:set -> prop,
 forall k2_bvfunc_2:set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k1_xboole_0:set,
     (forall X2 X3 X1 X6 X4 X5, (X5 = k1_xboole_0 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden X5 X4 -> False) -> (k9_xtuple_0 X1) = X3 -> (k10_xtuple_0 X1) = X6 -> X5 = (k8_setfam_1 X2 X6) -> X4 = (k2_bvfunc_2 X2 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_eqrel_1 X4 X2 -> m1_subset_1 X6 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X2)) -> r2_hidden (k1_funct_1 X1 (esk7_6 X2 X3 X4 X5 X1 X6)) (esk7_6 X2 X3 X4 X5 X1 X6) -> False)
  -> (forall X1 X2 X5 X6 X3 X4, (X4 = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden X4 X3 -> False) -> (r2_hidden (esk7_6 X1 X2 X3 X4 X5 X6) X2 -> False) -> (k9_xtuple_0 X5) = X2 -> (k10_xtuple_0 X5) = X6 -> X4 = (k8_setfam_1 X1 X6) -> X3 = (k2_bvfunc_2 X1 X2) -> v1_relat_1 X5 -> v1_funct_1 X5 -> m1_eqrel_1 X3 X1 -> m1_subset_1 X6 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X1 X5 X2 X3 X4, (X4 = (k2_bvfunc_2 X2 X3) -> False) -> ((esk8_3 X2 X3 X4) = k1_xboole_0 -> False) -> (v1_xboole_0 X2 -> False) -> (k9_xtuple_0 X1) = X3 -> (k10_xtuple_0 X1) = X5 -> (esk8_3 X2 X3 X4) = (k8_setfam_1 X2 X5) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_eqrel_1 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X2)) -> r2_hidden (esk8_3 X2 X3 X4) X4 -> r2_hidden (k1_funct_1 X1 (esk9_5 X2 X3 X4 X1 X5)) (esk9_5 X2 X3 X4 X1 X5) -> False)
  -> (forall X4 X5 X1 X2 X3, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> ((esk8_3 X1 X2 X3) = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk9_5 X1 X2 X3 X4 X5) X2 -> False) -> (k9_xtuple_0 X4) = X2 -> (k10_xtuple_0 X4) = X5 -> (esk8_3 X1 X2 X3) = (k8_setfam_1 X1 X5) -> v1_relat_1 X4 -> v1_funct_1 X4 -> m1_eqrel_1 X3 X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> False)
  -> (forall X4 X2 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (k1_funct_1 (esk5_4 X3 X2 X4 X5) X1) X1 -> False) -> X4 = (k2_bvfunc_2 X3 X2) -> m1_eqrel_1 X4 X3 -> r2_hidden X5 X4 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X3)) -> False)
  -> (forall X3 X2 X4 X1, ((k10_xtuple_0 (esk5_4 X1 X2 X3 X4)) = (esk6_4 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> X3 = (k2_bvfunc_2 X1 X2) -> m1_eqrel_1 X3 X1 -> r2_hidden X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk6_4 X1 X2 X3 X4) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> X3 = (k2_bvfunc_2 X1 X2) -> m1_eqrel_1 X3 X1 -> r2_hidden X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X4 X3 X1 X2, ((k8_setfam_1 X2 (esk6_4 X2 X3 X4 X1)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> X4 = (k2_bvfunc_2 X2 X3) -> m1_eqrel_1 X4 X2 -> r2_hidden X1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X2)) -> False)
  -> (forall X3 X2 X4 X1, ((k9_xtuple_0 (esk5_4 X1 X2 X3 X4)) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> X3 = (k2_bvfunc_2 X1 X2) -> m1_eqrel_1 X3 X1 -> r2_hidden X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk5_4 X1 X2 X3 X4) -> False) -> X3 = (k2_bvfunc_2 X1 X2) -> m1_eqrel_1 X3 X1 -> r2_hidden X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk5_4 X1 X2 X3 X4) -> False) -> X3 = (k2_bvfunc_2 X1 X2) -> m1_eqrel_1 X3 X1 -> r2_hidden X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X1 X3 X2 X4, (X4 = (k2_bvfunc_2 X3 X2) -> False) -> (v1_xboole_0 X3 -> False) -> (r2_hidden (esk8_3 X3 X2 X4) X4 -> False) -> (r2_hidden (k1_funct_1 (esk10_3 X3 X2 X4) X1) X1 -> False) -> m1_eqrel_1 X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X3)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> ((k8_setfam_1 X1 (esk11_3 X1 X2 X3)) = (esk8_3 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> ((k10_xtuple_0 (esk10_3 X1 X2 X3)) = (esk11_3 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (m1_subset_1 (esk11_3 X1 X2 X3) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> ((k9_xtuple_0 (esk10_3 X1 X2 X3)) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk10_3 X1 X2 X3) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk10_3 X1 X2 X3) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_2 X1 (k7_subset_1 (k1_bvfunc_2 X1) X3 (k4_bvfunc_2 X1 X2))) = (k5_bvfunc_2 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (esk8_3 X1 X2 X3) = k1_xboole_0 -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X1 X2, ((esk14_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r1_xboole_0 (esk14_2 X1 X2) (esk15_2 X1 X2) -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> (r1_xboole_0 X4 X1 -> False) -> m1_eqrel_1 X3 X2 -> r2_hidden X4 X3 -> r2_hidden X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (k5_bvfunc_2 X1 X2 X3) X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, ((esk14_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk15_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, ((esk14_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> (esk15_2 X1 X2) = (esk14_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, ((esk14_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk15_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk14_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, X1 = k1_xboole_0 -> m1_eqrel_1 X2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X4 X2 X3, (v1_xboole_0 X3 -> False) -> X1 = k1_xboole_0 -> X2 = (k2_bvfunc_2 X3 X4) -> m1_eqrel_1 X2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_bvfunc_2 X3)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk25_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k6_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (k2_bvfunc_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk12_2 X1 X2) = X1 -> r2_hidden (esk12_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k2_zfmisc_1 (k1_tarski X3) (k1_tarski X2)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v4_relat_1 (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X3)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, ((k5_setfam_1 X1 X2) = X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k4_bvfunc_2 X1 X2) (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> ((k8_setfam_1 X2 X1) = (k6_setfam_1 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k2_zfmisc_1 X3 (k1_tarski X2)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk13_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False)
  -> (forall X2 X1, ((k6_setfam_1 X2 X1) = (k1_setfam_1 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_funcop_1 (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X1)) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, ((k8_setfam_1 X2 X1) = X2 -> False) -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k1_tarski (k1_funct_1 X1 X2)) = (k10_xtuple_0 X1) -> False) -> (k1_tarski X2) = (k9_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk12_2 X1 X2) = X1 -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_funcop_1 (k2_zfmisc_1 X2 (k1_tarski X1)) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, X1 = X2 -> (k4_xboole_0 (k1_tarski X1) (k1_tarski X2)) = (k1_tarski X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> ((k10_xtuple_0 (k2_zfmisc_1 X1 (k1_tarski X2))) = (k1_tarski X2) -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_relat_1 (k2_zfmisc_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (r2_hidden X1 X2 -> False) -> (k4_xboole_0 (k1_tarski X1) X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k4_bvfunc_2 X1 X2) = (k1_tarski X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_partfun1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k4_xboole_0 (k1_tarski X1) X2) = k1_xboole_0 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> ((k4_xboole_0 (k1_tarski X1) (k1_tarski X2)) = (k1_tarski X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk21_1 X1) -> False) -> False)
  -> (forall X1, (v2_card_3 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_xboole_0 (k1_tarski X1) (k1_tarski X2)) -> False)
  -> ((k5_bvfunc_2 esk1_0 esk3_0 esk2_0) = esk4_0 -> False)
  -> (forall X1, v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (esk4_0 = esk3_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_zfmisc_1 X1 (k1_tarski X2)) (k1_zfmisc_1 (k2_zfmisc_1 X1 (k1_tarski X2))) -> False) -> False)
  -> (forall X2 X1 X3, ((k2_xboole_0 (k4_xboole_0 X1 X3) (k4_xboole_0 X2 X3)) = (k4_xboole_0 (k2_xboole_0 X1 X2) X3) -> False) -> False)
  -> (forall X2 X1, (r1_tarski (k10_xtuple_0 (k2_zfmisc_1 X1 (k1_tarski X2))) (k1_tarski X2) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 (k1_tarski X2) -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) (k1_tarski X1) -> False) -> False)
  -> (forall X2 X1, ((k1_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) X1) = X2 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_bvfunc_2 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v2_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 (k1_tarski X1) (k1_tarski X2)) = (k2_xboole_0 (k1_tarski X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X1 X2, (v1_partfun1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, ((k9_xtuple_0 (k2_zfmisc_1 X1 (k1_tarski X2))) = X1 -> False) -> False)
  -> (forall X1 X2, (v3_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (k2_zfmisc_1 k1_xboole_0 (k1_tarski X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_bvfunc_2 esk1_0)) -> False) -> False)
  -> (((k2_xboole_0 (k1_tarski esk3_0) (k1_tarski esk4_0)) = esk2_0 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (k1_bvfunc_2 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((m1_eqrel_1 esk4_0 esk1_0 -> False) -> False)
  -> ((m1_eqrel_1 esk3_0 esk1_0 -> False) -> False)
  -> (forall X1, ((k1_setfam_1 (k1_tarski X1)) = X1 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk27_1 X1) -> False) -> False)
  -> ((v3_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funcop_1 esk19_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
