(** $I sig/MizarPreamble.mgs **)

Theorem t8_partit1:
 forall esk19_5:set -> set -> set -> set -> set -> set,
 forall a_4_0_partit1:set -> set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk36_3:set -> set -> set -> set,
 forall m1_eqrel_1:set -> set -> prop,
 forall esk35_3:set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall v1_relat_1:set -> prop,
 forall k8_setfam_1:set -> set -> set,
 forall esk38_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall r1_partit1:set -> set -> set -> prop,
 forall k1_relset_1:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall esk13_3:set -> set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk18_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall esk37_2:set -> set -> set,
 forall k6_setfam_1:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v1_subset_1:set -> set -> prop,
 forall v6_membered:set -> prop,
 forall v4_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall esk24_1:set -> set,
 forall esk33_1:set -> set,
 forall esk30_0:set,
 forall esk27_0:set,
 forall esk22_2:set -> set -> set,
 forall esk16_1:set -> set,
 forall esk25_0:set,
 forall esk17_1:set -> set,
 forall esk28_1:set -> set,
 forall esk23_2:set -> set -> set,
 forall esk21_0:set,
 forall esk29_0:set,
 forall esk32_1:set -> set,
 forall v7_membered:set -> prop,
 forall esk26_1:set -> set,
 forall esk8_1:set -> set,
 forall v1_setfam_1:set -> prop,
 forall esk34_1:set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v1_int_1:set -> prop,
 forall v1_membered:set -> prop,
 forall v3_membered:set -> prop,
 forall v5_membered:set -> prop,
 forall k5_setfam_1:set -> set -> set,
 forall esk31_2:set -> set -> set,
 forall esk15_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk14_2:set -> set -> set,
 forall k11_eqrel_1:set -> set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall k1_setfam_1:set -> set,
 forall k3_tarski:set -> set,
 forall k1_xboole_0:set,
 forall k1_funct_1:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_4_3_partit1:set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall esk20_5:set -> set -> set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
     (forall X2 X5 X1 X4 X3, ((k3_funct_2 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) X4 (esk20_5 X1 X3 X5 X2 X4)) = X1 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r2_hidden X1 (a_4_3_partit1 X3 X5 X2 X4) -> v1_funct_2 X4 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)))) -> False)
  -> (forall X2 X5 X1 X4 X3, ((k3_funct_2 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) X4 (esk19_5 X1 X3 X5 X2 X4)) = X1 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r2_hidden X1 (a_4_0_partit1 X3 X5 X2 X4) -> v1_funct_2 X4 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)))) -> False)
  -> (forall X2 X1 X3 X5 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 (esk19_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 X2) X4 -> False) -> v1_funct_1 X5 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_4_0_partit1 X2 X3 X4 X5) -> v1_funct_2 X5 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)))) -> False)
  -> (forall X2 X1 X3 X5 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk20_5 X1 X2 X3 X4 X5) X3 -> False) -> v1_funct_1 X5 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_4_3_partit1 X2 X3 X4 X5) -> v1_funct_2 X5 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)))) -> False)
  -> (forall X2 X1 X3 X5 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk19_5 X1 X2 X3 X4 X5) X3 -> False) -> v1_funct_1 X5 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_4_0_partit1 X2 X3 X4 X5) -> v1_funct_2 X5 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)))) -> False)
  -> (forall X2 X1 X3 X5 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk20_5 X1 X2 X3 X4 X5) X4 -> False) -> v1_funct_1 X5 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_4_3_partit1 X2 X3 X4 X5) -> v1_funct_2 X5 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)))) -> False)
  -> (forall X2 X1 X6 X5 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden X4 (a_4_0_partit1 X2 X6 X3 X5) -> False) -> X4 = (k3_funct_2 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) X5 X1) -> v1_funct_1 X5 -> r2_hidden X1 X6 -> m2_subset_1 X1 (k1_zfmisc_1 X2) X3 -> m1_subset_1 X6 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> v1_funct_2 X5 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)))) -> False)
  -> (forall X2 X1 X6 X5 X3 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden X3 (a_4_3_partit1 X4 X6 X2 X5) -> False) -> X3 = (k3_funct_2 X2 (k1_zfmisc_1 (k1_zfmisc_1 X4)) X5 X1) -> v1_funct_1 X5 -> m1_subset_1 X1 X2 -> r2_hidden X1 X6 -> m1_subset_1 X6 (k1_zfmisc_1 (k1_zfmisc_1 X4)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X4)) -> v1_funct_2 X5 X2 (k1_zfmisc_1 (k1_zfmisc_1 X4)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X4)))) -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (a_4_3_partit1 X1 X2 X3 X4) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> v1_funct_1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> v1_funct_2 X4 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)))) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_3 X1 X2 X3) X3 -> False) -> (r1_tarski (k1_funct_1 (esk36_3 X1 X2 X3) X4) X2 -> False) -> m1_eqrel_1 X2 X1 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X4 X3 X2 X5, (X5 = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_tarski (k1_funct_1 (esk36_3 X1 X2 X3) X4) X2 -> False) -> (esk35_3 X1 X2 X3) = (k3_tarski X5) -> m1_eqrel_1 X2 X1 -> r2_hidden X4 X3 -> r1_tarski X5 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X4 X3 X1 X2, ((k3_tarski (k1_funct_1 (esk36_3 X2 X3 X4) X1)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk35_3 X2 X3 X4) X4 -> False) -> m1_eqrel_1 X3 X2 -> r2_hidden X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X4 X3 X2 X5, (X5 = k1_xboole_0 -> False) -> ((k3_tarski (k1_funct_1 (esk36_3 X2 X3 X4) X1)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> (esk35_3 X2 X3 X4) = (k3_tarski X5) -> m1_eqrel_1 X3 X2 -> r2_hidden X1 X4 -> r1_tarski X5 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_3 X1 X2 X3) X3 -> False) -> (k1_funct_1 (esk36_3 X1 X2 X3) X4) = k1_xboole_0 -> m1_eqrel_1 X2 X1 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X4 X2 X3 X5, (X5 = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (esk35_3 X1 X2 X3) = (k3_tarski X5) -> (k1_funct_1 (esk36_3 X1 X2 X3) X4) = k1_xboole_0 -> m1_eqrel_1 X2 X1 -> r2_hidden X4 X3 -> r1_tarski X5 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk36_3 X1 X2 X3)) = X3 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk36_3 X1 X2 X3) -> False) -> (r2_hidden (esk35_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk36_3 X1 X2 X3) -> False) -> (r2_hidden (esk35_3 X1 X2 X3) X3 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> ((k9_xtuple_0 (esk36_3 X1 X2 X3)) = X3 -> False) -> (v1_xboole_0 X1 -> False) -> (esk35_3 X1 X2 X3) = (k3_tarski X4) -> m1_eqrel_1 X2 X1 -> r1_tarski X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2 X3 X4, (X4 = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk36_3 X1 X2 X3) -> False) -> (esk35_3 X1 X2 X3) = (k3_tarski X4) -> m1_eqrel_1 X2 X1 -> r1_tarski X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2 X3 X4, (X4 = k1_xboole_0 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk36_3 X1 X2 X3) -> False) -> (esk35_3 X1 X2 X3) = (k3_tarski X4) -> m1_eqrel_1 X2 X1 -> r1_tarski X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k8_setfam_1 X2 X3) -> False) -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (esk38_3 X2 X1 X3) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X2 X1 X3, (r2_hidden X2 (k8_setfam_1 X1 X3) -> False) -> (r2_hidden (esk38_3 X1 X2 X3) X3 -> False) -> r2_hidden X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_tarski (esk4_3 X1 X2 X3) X2 -> False) -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X2 X3 -> False)
  -> (forall X3 X1 X2, ((k3_tarski (esk4_3 X2 X3 X1)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> m1_eqrel_1 X3 X2 -> r1_partit1 X2 X3 X1 -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> ((k1_relset_1 X2 X1) = X2 -> False) -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X3 = (k1_setfam_1 X2) -> r2_hidden X1 (esk5_3 X2 X3 X1) -> False)
  -> (forall X3 X2 X1, (X1 = k1_xboole_0 -> False) -> X3 = k1_xboole_0 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (esk4_3 X1 X2 X3) = k1_xboole_0 -> m1_eqrel_1 X2 X1 -> r1_partit1 X1 X2 X3 -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v1_funct_2 X2 X1 X3 -> False) -> (k1_relset_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 X2 -> False) -> X1 = (k11_eqrel_1 X3 X4 X2) -> m1_eqrel_1 X2 X3 -> m1_subset_1 X4 X3 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 X2 -> False) -> X2 = (k11_eqrel_1 X3 X1 X4) -> m1_eqrel_1 X4 X3 -> m1_subset_1 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1 X4, (X2 = (k11_eqrel_1 X4 X1 X3) -> False) -> (v1_xboole_0 X4 -> False) -> m1_eqrel_1 X3 X4 -> m1_subset_1 X1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X4) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k11_eqrel_1 X1 X2 X3) (k1_zfmisc_1 X1) -> False) -> m1_eqrel_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> r2_hidden X1 (k8_setfam_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> r2_hidden (esk6_2 X1 X2) (esk7_2 X1 X2) -> False)
  -> (forall X1 X2 X3, (v1_funct_2 X1 X2 X3 -> False) -> X3 = k1_xboole_0 -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk9_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk9_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk10_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk10_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk14_2 X1 X2) X3 -> r2_hidden (esk14_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk13_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk13_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden X3 X2 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> X2 = (k1_setfam_1 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> v1_relat_1 X1 -> r1_tarski (k10_xtuple_0 X1) X3 -> r1_tarski (k9_xtuple_0 X1) X2 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk18_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X3 X2 X1, (X1 = k1_xboole_0 -> False) -> (v1_xboole_0 X4 -> False) -> (r1_partit1 X4 X2 X3 -> False) -> X3 = (k3_tarski X1) -> m1_eqrel_1 X2 X4 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk11_2 X1 X2)) = (esk10_2 X1 X2) -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> (r2_hidden (esk14_2 X1 X2) (esk15_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X3 -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> r2_hidden X3 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk37_2 X3 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> (r2_hidden (esk11_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k6_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> (r2_hidden (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r1_partit1 X1 X2 X1 -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> ((k8_setfam_1 X2 X1) = (k6_setfam_1 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk12_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1, (r1_partit1 esk1_0 esk2_0 X1 -> False) -> r2_hidden X1 esk3_0 -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k1_setfam_1 X4) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, ((k6_setfam_1 X2 X1) = (k1_setfam_1 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k8_setfam_1 X2 X1) = X2 -> False) -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk37_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk31_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk31_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk31_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
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
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk31_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk31_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk33_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk33_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk33_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk26_1 X1) -> False) -> False)
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
  -> (r1_partit1 esk1_0 esk2_0 (k8_setfam_1 esk1_0 esk3_0) -> False)
  -> (forall X1, v1_subset_1 (esk32_1 X1) X1 -> False)
  -> ((k8_setfam_1 esk1_0 esk3_0) = k1_xboole_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk30_0 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk23_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk22_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk23_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk22_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk23_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk22_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_eqrel_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk28_1 X1) -> False) -> False)
  -> ((v7_membered esk30_0 -> False) -> False)
  -> ((v6_membered esk30_0 -> False) -> False)
  -> ((v6_membered esk27_0 -> False) -> False)
  -> ((v6_membered esk21_0 -> False) -> False)
  -> ((v1_xboole_0 esk25_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
