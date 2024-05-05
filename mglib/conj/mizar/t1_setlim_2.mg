(** $I sig/MizarPreamble.mgs **)

Theorem t1_setlim_2:
 forall esk8_4:set -> set -> set -> set -> set,
 forall a_3_2_setlim_1:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall r1_xxreal_0:set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall k2_relset_1:set -> set -> set,
 forall k10_nat_1:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall k1_setlim_1:set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk23_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall esk13_1:set -> set,
 forall v1_xreal_0:set -> prop,
 forall k1_numbers:set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk18_1:set -> set,
 forall esk22_0:set,
 forall esk10_2:set -> set -> set,
 forall esk16_1:set -> set,
 forall esk5_1:set -> set,
 forall esk21_0:set,
 forall esk11_0:set,
 forall esk14_0:set,
 forall esk19_0:set,
 forall esk17_1:set -> set,
 forall esk12_2:set -> set -> set,
 forall esk15_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall v1_xcmplx_0:set -> prop,
 forall k4_ordinal1:set,
 forall esk20_1:set -> set,
 forall v3_ordinal1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall esk4_2:set -> set -> set,
 forall k1_setfam_1:set -> set,
 forall a_2_1_setlim_1:set -> set -> set,
 forall k9_nat_1:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall k6_setfam_1:set -> set -> set,
 forall k3_prob_1:set -> set -> set,
 forall k2_setlim_1:set -> set -> set,
 forall v7_ordinal1:set -> prop,
 forall a_3_0_setlim_2:set -> set -> set -> set,
 forall k8_nat_1:set -> set -> set -> set,
 forall esk7_4:set -> set -> set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall a_3_3_setlim_1:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall esk9_4:set -> set -> set -> set -> set,
 forall k9_setfam_1:set -> set,
 forall k5_numbers:set,
     (forall X4 X1 X2 X3, ((k3_funct_2 k5_numbers (k9_setfam_1 X2) X3 (esk9_4 X1 X2 X3 X4)) = X1 -> False) -> v1_funct_1 X3 -> m1_subset_1 X4 k5_numbers -> r2_hidden X1 (a_3_3_setlim_1 X2 X3 X4) -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X3 X1 X4 X2, ((k3_funct_2 k5_numbers X2 X3 (esk8_4 X1 X4 X2 X3)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X3 -> m1_subset_1 X4 k5_numbers -> v1_funct_2 X3 k5_numbers X2 -> r2_hidden X1 (a_3_2_setlim_1 X4 X2 X3) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X2)) -> False)
  -> (forall X4 X1 X2 X3, ((k8_nat_1 (k9_setfam_1 X2) X3 (esk7_4 X1 X4 X2 X3)) = X1 -> False) -> v1_funct_1 X3 -> m1_subset_1 X4 k5_numbers -> r2_hidden X1 (a_3_0_setlim_2 X4 X2 X3) -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X1 X2 X3 X4, (r1_xxreal_0 X1 (esk9_4 X2 X3 X4 X1) -> False) -> v1_funct_1 X4 -> m1_subset_1 X1 k5_numbers -> r2_hidden X2 (a_3_3_setlim_1 X3 X4 X1) -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X3) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X3))) -> False)
  -> (forall X1 X2 X3 X4, (r1_xxreal_0 X1 (esk7_4 X2 X1 X3 X4) -> False) -> v1_funct_1 X4 -> m1_subset_1 X1 k5_numbers -> r2_hidden X2 (a_3_0_setlim_2 X1 X3 X4) -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X3) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X3))) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (esk9_4 X1 X2 X3 X4) k5_numbers -> False) -> v1_funct_1 X3 -> m1_subset_1 X4 k5_numbers -> r2_hidden X1 (a_3_3_setlim_1 X2 X3 X4) -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X2 X1 X3 X4, (m1_subset_1 (esk7_4 X1 X2 X3 X4) k5_numbers -> False) -> v1_funct_1 X4 -> m1_subset_1 X2 k5_numbers -> r2_hidden X1 (a_3_0_setlim_2 X2 X3 X4) -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X3) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X3))) -> False)
  -> (forall X4 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r1_xxreal_0 X1 (esk8_4 X2 X1 X3 X4) -> False) -> v1_funct_1 X4 -> m1_subset_1 X1 k5_numbers -> v1_funct_2 X4 k5_numbers X3 -> r2_hidden X2 (a_3_2_setlim_1 X1 X3 X4) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X3)) -> False)
  -> (forall X4 X1 X2 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 (esk8_4 X1 X2 X3 X4) k5_numbers -> False) -> v1_funct_1 X4 -> m1_subset_1 X2 k5_numbers -> v1_funct_2 X4 k5_numbers X3 -> r2_hidden X1 (a_3_2_setlim_1 X2 X3 X4) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X3)) -> False)
  -> (forall X1 X5 X4 X3 X2, (r2_hidden X2 (a_3_3_setlim_1 X3 X4 X5) -> False) -> X2 = (k3_funct_2 k5_numbers (k9_setfam_1 X3) X4 X1) -> v1_funct_1 X4 -> r1_xxreal_0 X5 X1 -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X1 k5_numbers -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X3) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X3))) -> False)
  -> (forall X2 X5 X4 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X2 (a_3_2_setlim_1 X5 X3 X4) -> False) -> X2 = (k3_funct_2 k5_numbers X3 X4 X1) -> v1_funct_1 X4 -> r1_xxreal_0 X5 X1 -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X1 k5_numbers -> v1_funct_2 X4 k5_numbers X3 -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X3)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X4 X3 X5 X2, (r2_hidden X2 (a_3_0_setlim_2 X5 X3 X4) -> False) -> X2 = (k8_nat_1 (k9_setfam_1 X3) X4 X1) -> v1_funct_1 X4 -> r1_xxreal_0 X5 X1 -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X1 k5_numbers -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X3) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X3))) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (a_3_3_setlim_1 X2 X1 X3) (k9_setfam_1 (k9_setfam_1 X2)) -> False) -> v1_funct_1 X1 -> m1_subset_1 X3 k5_numbers -> v1_funct_2 X1 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X3 X1 X2, ((k2_relset_1 X2 (k10_nat_1 X2 X3 X1)) = (a_3_2_setlim_1 X1 X2 X3) -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X3 -> m1_subset_1 X1 k5_numbers -> v1_funct_2 X3 k5_numbers X2 -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k10_nat_1 X1 X2 X3) (k9_setfam_1 (k2_zfmisc_1 k5_numbers X1)) -> False) -> v1_funct_1 X2 -> v7_ordinal1 X3 -> v1_funct_2 X2 k5_numbers X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k10_nat_1 X1 X2 X3) k5_numbers X1 -> False) -> v1_funct_1 X2 -> v7_ordinal1 X3 -> v1_funct_2 X2 k5_numbers X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X1)) -> False)
  -> (forall X1 X2, (m1_subset_1 (k2_setlim_1 X1 X2) (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X1 X2, (v1_funct_2 (k2_setlim_1 X1 X2) k5_numbers (k9_setfam_1 X1) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k8_nat_1 X2 X1 X3) X2 -> False) -> v1_funct_1 X1 -> v7_ordinal1 X3 -> v1_funct_2 X1 k5_numbers X2 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k10_nat_1 X1 X2 X3) -> False) -> v1_funct_1 X2 -> v7_ordinal1 X3 -> v1_funct_2 X2 k5_numbers X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X1)) -> False)
  -> (forall X2 X1, ((k6_setfam_1 X2 (k2_relset_1 (k9_setfam_1 X2) X1)) = (k3_prob_1 X2 X1) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_prob_1 X2 X1) (k9_setfam_1 X2) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X2 X3 X1, ((k10_nat_1 X1 X2 X3) = (k9_nat_1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> v7_ordinal1 X3 -> v1_funct_2 X2 k5_numbers X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X1)) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_setlim_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X3 X2 X1, ((k8_nat_1 X2 X1 X3) = (k1_funct_1 X1 X3) -> False) -> v1_funct_1 X1 -> v7_ordinal1 X3 -> v1_funct_2 X1 k5_numbers X2 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X2)) -> False)
  -> (forall X2 X1, ((k2_setlim_1 X2 X1) = (k1_setlim_1 X1) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X2 X1, (X1 = (k1_setlim_1 X2) -> False) -> (k9_xtuple_0 X1) = k5_numbers -> (k1_funct_1 X1 (esk4_2 X2 X1)) = (k1_setfam_1 (a_2_1_setlim_1 X2 (esk4_2 X2 X1))) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk6_3 X1 X2 X3)) = X1 -> False) -> v1_funct_1 X2 -> v1_relat_1 X2 -> m1_subset_1 X3 k5_numbers -> r2_hidden X1 (a_2_1_setlim_1 X2 X3) -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 X1 (esk6_3 X2 X3 X1) -> False) -> v1_funct_1 X3 -> v1_relat_1 X3 -> m1_subset_1 X1 k5_numbers -> r2_hidden X2 (a_2_1_setlim_1 X3 X1) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (esk6_3 X1 X2 X3) k5_numbers -> False) -> v1_funct_1 X2 -> v1_relat_1 X2 -> m1_subset_1 X3 k5_numbers -> r2_hidden X1 (a_2_1_setlim_1 X2 X3) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X4 X2, (r2_hidden X2 (a_2_1_setlim_1 X3 X4) -> False) -> X2 = (k1_funct_1 X3 X1) -> v1_funct_1 X3 -> v1_relat_1 X3 -> r1_xxreal_0 X4 X1 -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk23_2 X3 X2) -> False)
  -> (forall X1 X2 X3, ((k1_funct_1 X2 X1) = (k1_setfam_1 (a_2_1_setlim_1 X3 X1)) -> False) -> X2 = (k1_setlim_1 X3) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_relat_1 X3 -> v1_relat_1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, (v4_relat_1 (k9_nat_1 X1 X2) k5_numbers -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v7_ordinal1 X2 -> v1_partfun1 X1 k5_numbers -> v4_relat_1 X1 k5_numbers -> False)
  -> (forall X2 X1, (v1_partfun1 (k9_nat_1 X1 X2) k5_numbers -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v7_ordinal1 X2 -> v1_partfun1 X1 k5_numbers -> v4_relat_1 X1 k5_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k6_setfam_1 X2 X1) (k9_setfam_1 X2) -> False) -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X2 X1, (v1_relat_1 (k9_nat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v7_ordinal1 X2 -> v1_partfun1 X1 k5_numbers -> v4_relat_1 X1 k5_numbers -> False)
  -> (forall X2 X1, (v1_funct_1 (k9_nat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v7_ordinal1 X2 -> v1_partfun1 X1 k5_numbers -> v4_relat_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (X2 = (k1_setlim_1 X1) -> False) -> (m1_subset_1 (esk4_2 X1 X2) k5_numbers -> False) -> (k9_xtuple_0 X2) = k5_numbers -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_relset_1 X2 X1) (k9_setfam_1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k6_setfam_1 X2 X1) = (k1_setfam_1 X1) -> False) -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk23_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, ((k2_relset_1 X2 X1) = (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k9_setfam_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, ((k9_xtuple_0 X1) = k5_numbers -> False) -> X1 = (k1_setlim_1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_relat_1 (k1_setlim_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k1_setlim_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k8_nat_1 (k9_setfam_1 esk2_0) (k2_setlim_1 esk2_0 esk3_0) esk1_0) = (k3_prob_1 esk2_0 (k10_nat_1 (k9_setfam_1 esk2_0) esk3_0 esk1_0)) -> False)
  -> (forall X1, v1_subset_1 (esk18_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k9_setfam_1 X1) -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk12_2 X1 X2) (k9_setfam_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk10_2 X1 X2) (k9_setfam_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk10_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 esk2_0))) -> False) -> False)
  -> ((v1_funct_2 esk3_0 k5_numbers (k9_setfam_1 esk2_0) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk12_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk10_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk10_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k9_setfam_1 X1) (k9_setfam_1 (k9_setfam_1 X1)) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk10_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk10_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k9_setfam_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk1_0 k5_numbers -> False) -> False)
  -> (forall X1, (v5_ordinal1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk16_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk17_1 X1) -> False) -> False)
  -> ((v1_xxreal_0 esk21_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk21_0 -> False) -> False)
  -> ((v7_ordinal1 esk22_0 -> False) -> False)
  -> ((v7_ordinal1 esk19_0 -> False) -> False)
  -> ((v1_xreal_0 esk21_0 -> False) -> False)
  -> ((v1_xreal_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v2_ordinal1 esk15_0 -> False) -> False)
  -> ((v1_ordinal1 esk15_0 -> False) -> False)
  -> ((v3_ordinal1 esk15_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
