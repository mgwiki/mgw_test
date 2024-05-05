(** $I sig/MizarPreamble.mgs **)

Theorem t6_bvfunc11:
 forall esk5_4:set -> set -> set -> set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall k4_funct_4:set -> set -> set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall k2_tarski:set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall k2_partit1:set -> set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall esk24_2:set -> set -> set,
 forall v1_funcop_1:set -> prop,
 forall v1_setfam_1:set -> prop,
 forall v2_funcop_1:set -> prop,
 forall esk39_1:set -> set,
 forall v2_card_3:set -> prop,
 forall esk33_1:set -> set,
 forall v1_eqrel_1:set -> set -> prop,
 forall esk32_1:set -> set,
 forall esk34_0:set,
 forall o_0_0_xboole_0:set,
 forall esk35_0:set,
 forall esk31_1:set -> set,
 forall esk37_0:set,
 forall esk38_1:set -> set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk36_1:set -> set,
 forall esk20_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk15_2:set -> set -> set,
 forall k6_setfam_1:set -> set -> set,
 forall esk19_2:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk17_3:set -> set -> set -> set,
 forall esk23_2:set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall k1_setfam_1:set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall esk27_3:set -> set -> set -> set,
 forall esk28_3:set -> set -> set -> set,
 forall esk29_3:set -> set -> set -> set,
 forall esk30_3:set -> set -> set -> set,
 forall k6_subset_1:set -> set -> set,
 forall esk21_3:set -> set -> set -> set,
 forall esk26_4:set -> set -> set -> set -> set,
 forall esk25_4:set -> set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall k3_setfam_1:set -> set -> set,
 forall esk22_4:set -> set -> set -> set -> set,
 forall v2_bvfunc_2:set -> set -> prop,
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
  -> (forall X3 X1 X4 X2, (v1_xboole_0 X2 -> False) -> (k9_xtuple_0 X1) = X3 -> (k10_xtuple_0 X1) = X4 -> (k8_setfam_1 X2 X4) = k1_xboole_0 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_bvfunc_2 X3 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X2)) -> r2_hidden (k1_funct_1 X1 (esk22_4 X2 X3 X1 X4)) (esk22_4 X2 X3 X1 X4) -> False)
  -> (forall X4 X2 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (k1_funct_1 (esk5_4 X3 X2 X4 X5) X1) X1 -> False) -> X4 = (k2_bvfunc_2 X3 X2) -> m1_eqrel_1 X4 X3 -> r2_hidden X5 X4 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X3)) -> False)
  -> (forall X3 X2 X4 X1, ((k3_xboole_0 (esk25_4 X2 X3 X4 X1) (esk26_4 X2 X3 X4 X1)) = X1 -> False) -> X4 = (k3_setfam_1 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X3 X2 X4 X1, ((k10_xtuple_0 (esk5_4 X1 X2 X3 X4)) = (esk6_4 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> X3 = (k2_bvfunc_2 X1 X2) -> m1_eqrel_1 X3 X1 -> r2_hidden X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk22_4 X1 X2 X3 X4) X2 -> False) -> (k9_xtuple_0 X3) = X2 -> (k10_xtuple_0 X3) = X4 -> (k8_setfam_1 X1 X4) = k1_xboole_0 -> v1_relat_1 X3 -> v1_funct_1 X3 -> v2_bvfunc_2 X2 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk6_4 X1 X2 X3 X4) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> X3 = (k2_bvfunc_2 X1 X2) -> m1_eqrel_1 X3 X1 -> r2_hidden X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X4 X3 X1 X2, ((k8_setfam_1 X2 (esk6_4 X2 X3 X4 X1)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> X4 = (k2_bvfunc_2 X2 X3) -> m1_eqrel_1 X4 X2 -> r2_hidden X1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X2)) -> False)
  -> (forall X3 X2 X4 X1, ((k9_xtuple_0 (esk5_4 X1 X2 X3 X4)) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> X3 = (k2_bvfunc_2 X1 X2) -> m1_eqrel_1 X3 X1 -> r2_hidden X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk5_4 X1 X2 X3 X4) -> False) -> X3 = (k2_bvfunc_2 X1 X2) -> m1_eqrel_1 X3 X1 -> r2_hidden X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk5_4 X1 X2 X3 X4) -> False) -> X3 = (k2_bvfunc_2 X1 X2) -> m1_eqrel_1 X3 X1 -> r2_hidden X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk21_3 X1 X2 X3) X3 -> r2_hidden (esk21_3 X1 X2 X3) X2 -> r2_hidden (esk21_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X5 X4 X1, (v1_xboole_0 X1 -> False) -> (v4_relat_1 (k4_funct_4 X2 X3 X4 X5) X1 -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk26_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k3_setfam_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk25_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k3_setfam_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk30_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk30_3 X1 X2 X3) X3 -> r2_hidden (esk30_3 X1 X2 X3) X1 -> False)
  -> (forall X4 X3 X1 X2, (X1 = X2 -> False) -> ((k10_xtuple_0 (k4_funct_4 X1 X2 X3 X4)) = (k2_tarski X3 X4) -> False) -> False)
  -> (forall X4 X3 X1 X2, (X1 = X2 -> False) -> ((k1_funct_1 (k4_funct_4 X1 X2 X3 X4) X1) = X3 -> False) -> False)
  -> (forall X1 X3 X2 X4, (X4 = (k2_bvfunc_2 X3 X2) -> False) -> (v1_xboole_0 X3 -> False) -> (r2_hidden (esk8_3 X3 X2 X4) X4 -> False) -> (r2_hidden (k1_funct_1 (esk10_3 X3 X2 X4) X1) X1 -> False) -> m1_eqrel_1 X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X3)) -> False)
  -> (forall X3 X2 X1, (X3 = (k3_setfam_1 X1 X2) -> False) -> ((k3_xboole_0 (esk28_3 X1 X2 X3) (esk29_3 X1 X2 X3)) = (esk27_3 X1 X2 X3) -> False) -> (r2_hidden (esk27_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> ((k8_setfam_1 X1 (esk11_3 X1 X2 X3)) = (esk8_3 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> ((k10_xtuple_0 (esk10_3 X1 X2 X3)) = (esk11_3 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X5 X4 X1 X2 X3, (X3 = (k3_setfam_1 X1 X2) -> False) -> (esk27_3 X1 X2 X3) = (k3_xboole_0 X4 X5) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden (esk27_3 X1 X2 X3) X3 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (m1_subset_1 (esk11_3 X1 X2 X3) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> ((k9_xtuple_0 (esk10_3 X1 X2 X3)) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk30_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk30_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk10_3 X1 X2 X3) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk10_3 X1 X2 X3) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_bvfunc_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (esk8_3 X1 X2 X3) = k1_xboole_0 -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> (esk16_3 X1 X2 X3) = X1 -> r2_hidden (esk16_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> (esk16_3 X1 X2 X3) = X2 -> r2_hidden (esk16_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk30_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk30_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk21_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk21_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk21_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk21_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_setfam_1 X1 X2) -> False) -> (r2_hidden (esk27_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_setfam_1 X1 X2) -> False) -> (r2_hidden (esk27_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk28_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> ((esk16_3 X1 X2 X3) = X2 -> False) -> ((esk16_3 X1 X2 X3) = X1 -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X3 = (k1_setfam_1 X2) -> r2_hidden X1 (esk12_3 X2 X3 X1) -> False)
  -> (forall X2 X3 X4 X1, ((k8_setfam_1 X2 X1) = (k9_subset_1 X2 X3 X4) -> False) -> X1 = (k2_tarski X3 X4) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v2_bvfunc_2 X2 X3 -> False) -> (r2_hidden (k1_funct_1 (esk23_2 X3 X2) X1) X1 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X3)) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> r2_hidden (esk13_2 X1 X2) X2 -> r2_hidden (esk13_2 X1 X2) (esk14_2 X1 X2) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk17_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (k2_partit1 X1 X2 X3) X1 -> False) -> m1_eqrel_1 X3 X1 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk17_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk18_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk18_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, ((k2_partit1 X1 X2 X3) = (k2_partit1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_eqrel_1 X3 X1 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X3 X1, ((k2_partit1 X1 X2 X3) = (k6_subset_1 (k3_setfam_1 X2 X3) (k1_tarski k1_xboole_0)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_eqrel_1 X3 X1 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden X3 X2 -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X1 -> False) -> X2 = (k1_setfam_1 X1) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_bvfunc_2 X2 X1 -> False) -> (m1_subset_1 (esk24_2 X1 X2) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X1 X4 X2 X3, (v1_xboole_0 X3 -> False) -> X1 = k1_xboole_0 -> X2 = (k2_bvfunc_2 X3 X4) -> m1_eqrel_1 X2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_bvfunc_2 X3)) -> False)
  -> (forall X2 X1, ((k10_xtuple_0 (esk23_2 X1 X2)) = (esk24_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (v2_bvfunc_2 X2 X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk19_2 X1 X2)) = (esk18_2 X1 X2) -> False) -> (r2_hidden (esk18_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, ((k8_setfam_1 X1 (esk24_2 X1 X2)) = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_bvfunc_2 X2 X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk14_2 X1 X2) X1 -> False) -> r2_hidden (esk13_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk13_2 X1 X2) X3 -> False) -> (r2_hidden (esk13_2 X1 X2) X2 -> False) -> r2_hidden X3 X1 -> False)
  -> (forall X4 X2 X1 X3 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k3_setfam_1 X2 X4) -> X5 = (k3_xboole_0 X1 X3) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk18_2 X1 X2) X2 -> False) -> (r2_hidden (esk19_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk23_2 X1 X2)) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_bvfunc_2 X2 X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_bvfunc_2 X2 X1 -> False) -> (v1_funct_1 (esk23_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_bvfunc_2 X2 X1 -> False) -> (v1_relat_1 (esk23_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k6_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (k2_bvfunc_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk15_2 X1 X2) = X1 -> r2_hidden (esk15_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> ((k8_setfam_1 X2 X1) = (k6_setfam_1 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk20_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k6_subset_1 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k1_setfam_1 X4) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k6_setfam_1 X2 X1) = (k1_setfam_1 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k6_subset_1 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k8_setfam_1 X2 X1) = X2 -> False) -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k6_subset_1 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk15_2 X1 X2) = X1 -> False) -> (r2_hidden (esk15_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk20_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> (X1 = X3 -> False) -> X2 = (k2_tarski X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X2 X4) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X4 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk39_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk36_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk39_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk36_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk39_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk36_1 X1) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> X2 = k1_xboole_0 -> X1 = (k1_setfam_1 X2) -> False)
  -> (forall X1, (v2_card_3 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = (k1_setfam_1 X2) -> False) -> X2 = k1_xboole_0 -> X1 = k1_xboole_0 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_partit1 esk1_0 esk3_0 esk4_0) = (k2_bvfunc_2 esk1_0 esk2_0) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_xboole_0 (esk38_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk37_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (esk4_0 = esk3_0 -> False)
  -> (forall X3 X4 X1 X2, (r1_tarski (k10_xtuple_0 (k4_funct_4 X1 X2 X3 X4)) (k2_tarski X3 X4) -> False) -> False)
  -> (forall X1 X2 X4 X3, ((k9_xtuple_0 (k4_funct_4 X1 X2 X3 X4)) = (k2_tarski X1 X2) -> False) -> False)
  -> (forall X4 X1 X3 X2, ((k1_funct_1 (k4_funct_4 X1 X2 X3 X4) X2) = X4 -> False) -> False)
  -> (forall X2 X3 X4 X1, (v1_funct_1 (k4_funct_4 X1 X2 X3 X4) -> False) -> False)
  -> (forall X2 X3 X4 X1, (v1_relat_1 (k4_funct_4 X1 X2 X3 X4) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk38_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_bvfunc_2 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k3_setfam_1 X1 X2) = (k3_setfam_1 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_bvfunc_2 esk1_0)) -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (esk38_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (esk33_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (k1_bvfunc_2 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk31_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((v2_bvfunc_2 esk2_0 esk1_0 -> False) -> False)
  -> ((m1_eqrel_1 esk4_0 esk1_0 -> False) -> False)
  -> ((m1_eqrel_1 esk3_0 esk1_0 -> False) -> False)
  -> (((k2_tarski esk3_0 esk4_0) = esk2_0 -> False) -> False)
  -> ((v1_funcop_1 esk34_0 -> False) -> False)
  -> ((v1_funct_1 esk34_0 -> False) -> False)
  -> ((v1_relat_1 esk34_0 -> False) -> False)
  -> ((v1_xboole_0 esk35_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
