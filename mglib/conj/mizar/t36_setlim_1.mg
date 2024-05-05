(** $I sig/MizarPreamble.mgs **)

Theorem t36_setlim_1:
 forall k6_prob_1:set -> set -> set -> set -> set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v1_prob_1:set -> set -> prop,
 forall v4_prob_1:set -> set -> prop,
 forall m1_prob_1:set -> set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k3_setlim_1:set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk25_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall esk10_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall k1_numbers:set,
 forall r1_tarski:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall v3_ordinal1:set -> prop,
 forall esk16_1:set -> set,
 forall v2_relat_1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall esk5_0:set,
 forall esk20_1:set -> set,
 forall esk23_0:set,
 forall esk14_0:set,
 forall esk15_2:set -> set -> set,
 forall esk22_1:set -> set,
 forall esk31_0:set,
 forall esk28_0:set,
 forall esk18_0:set,
 forall esk17_0:set,
 forall esk12_0:set,
 forall esk21_0:set,
 forall esk9_1:set -> set,
 forall esk24_1:set -> set,
 forall esk26_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall esk19_0:set,
 forall esk32_0:set,
 forall esk13_1:set -> set,
 forall esk27_1:set -> set,
 forall k1_xboole_0:set,
 forall v5_ordinal1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall k4_ordinal1:set,
 forall esk30_1:set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v2_finsub_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk29_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v2_prob_1:set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k4_setlim_1:set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall k9_setfam_1:set -> set,
 forall k2_nat_1:set -> set -> set,
 forall esk33_4:set -> set -> set -> set -> set,
 forall k5_numbers:set,
 forall r2_hidden:set -> set -> prop,
     (forall X4 X1 X2 X3, (r2_hidden X1 (k3_funct_2 k5_numbers (k9_setfam_1 X2) X3 (k2_nat_1 X4 (esk33_4 X4 X2 X1 X3))) -> False) -> v1_funct_1 X3 -> m1_subset_1 X4 k5_numbers -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> r2_hidden X1 (k3_funct_2 k5_numbers (k9_setfam_1 X2) (k4_setlim_1 X2 X3) X4) -> False)
  -> (forall X1 X3 X4 X5 X2, (r2_hidden X2 (k3_funct_2 k5_numbers (k9_setfam_1 X3) (k4_setlim_1 X3 X4) X5) -> False) -> v1_funct_1 X4 -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X1 k5_numbers -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X3) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X3))) -> r2_hidden X2 (k3_funct_2 k5_numbers (k9_setfam_1 X3) X4 (k2_nat_1 X5 X1)) -> False)
  -> (forall X1 X3 X2 X4, (m1_subset_1 (esk33_4 X1 X2 X3 X4) k5_numbers -> False) -> v1_funct_1 X4 -> m1_subset_1 X1 k5_numbers -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> r2_hidden X3 (k3_funct_2 k5_numbers (k9_setfam_1 X2) (k4_setlim_1 X2 X4) X1) -> False)
  -> (forall X1, ((k6_prob_1 esk1_0 (k9_setfam_1 esk1_0) (k3_funct_2 k5_numbers (k9_setfam_1 esk1_0) esk3_0 X1) (k3_funct_2 k5_numbers (k9_setfam_1 esk1_0) esk4_0 X1)) = (k3_funct_2 k5_numbers (k9_setfam_1 esk1_0) esk2_0 X1) -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_prob_1 (k6_prob_1 X2 X1 X3 X4) X2 X1 -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> v1_prob_1 X1 X2 -> v4_prob_1 X1 X2 -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X4 X3 X2 X1, ((k6_prob_1 X2 X1 X3 X4) = (k6_prob_1 X2 X1 X4 X3) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> v1_prob_1 X1 X2 -> v4_prob_1 X1 X2 -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X4 X3 X2 X1, ((k6_prob_1 X2 X1 X3 X4) = (k2_xboole_0 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> v1_prob_1 X1 X2 -> v4_prob_1 X1 X2 -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X2 -> False)
  -> (forall X4 X2 X1 X3, ((k6_prob_1 X2 X1 X3 X3) = X3 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> v1_prob_1 X1 X2 -> v4_prob_1 X1 X2 -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k4_setlim_1 X1 X2) (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X1 X2, (v1_funct_2 (k4_setlim_1 X1 X2) k5_numbers (k9_setfam_1 X1) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X2 X1, (v1_funct_2 (k3_setlim_1 X1) k5_numbers (k9_setfam_1 X2) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X1 X2, (v1_funct_1 (k4_setlim_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X2 X1, ((k4_setlim_1 X2 X1) = (k3_setlim_1 X1) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X2 X1, (v2_prob_1 (k3_setlim_1 X1) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X2 X1, (v1_funct_1 (k3_setlim_1 X1) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 (k9_setfam_1 X2) -> False) -> v1_prob_1 X1 X2 -> v4_prob_1 X1 X2 -> m1_prob_1 X3 X2 X1 -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X1 X2 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 X1 X3 -> False) -> v1_prob_1 X3 X2 -> v4_prob_1 X3 X2 -> m1_prob_1 X1 X2 X3 -> m1_subset_1 X3 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_prob_1 (esk8_2 X2 X1) X2 X1 -> False) -> v1_prob_1 X1 X2 -> v4_prob_1 X1 X2 -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (m1_prob_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> v1_prob_1 X2 X3 -> v4_prob_1 X2 X3 -> m1_subset_1 X2 (k9_setfam_1 (k9_setfam_1 X3)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk25_2 X1 X2) (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False) -> m1_subset_1 X2 (k9_setfam_1 (k9_setfam_1 X1)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k9_setfam_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk29_2 X1 X2) X2 -> False) -> v1_prob_1 X2 X1 -> v4_prob_1 X2 X1 -> m1_subset_1 X2 (k9_setfam_1 (k9_setfam_1 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_2 (esk25_2 X1 X2) k5_numbers (k9_setfam_1 X1) -> False) -> m1_subset_1 X2 (k9_setfam_1 (k9_setfam_1 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 (esk29_2 X1 X2) -> False) -> v1_prob_1 X2 X1 -> v4_prob_1 X2 X1 -> m1_subset_1 X2 (k9_setfam_1 (k9_setfam_1 X1)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk10_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_finsub_1 X1 -> False) -> v1_prob_1 X1 X2 -> v4_prob_1 X1 X2 -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X2 X1, (m2_subset_1 (k2_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v5_relat_1 (esk25_2 X1 X2) (k9_setfam_1 X1) -> False) -> m1_subset_1 X2 (k9_setfam_1 (k9_setfam_1 X1)) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> m1_subset_1 X2 (k9_setfam_1 (k9_setfam_1 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v4_relat_1 (esk25_2 X1 X2) k5_numbers -> False) -> m1_subset_1 X2 (k9_setfam_1 (k9_setfam_1 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (esk25_2 X1 X2) -> False) -> m1_subset_1 X2 (k9_setfam_1 (k9_setfam_1 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk25_2 X1 X2) -> False) -> m1_subset_1 X2 (k9_setfam_1 (k9_setfam_1 X1)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k9_setfam_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k9_setfam_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_nat_1 X2 X1) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k9_setfam_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_relat_1 (k3_setlim_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k3_setlim_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k6_prob_1 esk1_0 (k9_setfam_1 esk1_0) (k3_funct_2 k5_numbers (k9_setfam_1 esk1_0) (k4_setlim_1 esk1_0 esk3_0) esk5_0) (k3_funct_2 k5_numbers (k9_setfam_1 esk1_0) (k4_setlim_1 esk1_0 esk4_0) esk5_0)) = (k3_funct_2 k5_numbers (k9_setfam_1 esk1_0) (k4_setlim_1 esk1_0 esk2_0) esk5_0) -> False)
  -> (forall X1, v1_subset_1 (esk27_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k9_setfam_1 X1) -> False)
  -> (v1_xboole_0 esk32_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk15_2 X1 X2) (k9_setfam_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk11_2 X1 X2) (k9_setfam_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk11_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 esk1_0))) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 esk1_0))) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 esk1_0))) -> False) -> False)
  -> ((v1_funct_2 esk4_0 k5_numbers (k9_setfam_1 esk1_0) -> False) -> False)
  -> ((v1_funct_2 esk3_0 k5_numbers (k9_setfam_1 esk1_0) -> False) -> False)
  -> ((v1_funct_2 esk2_0 k5_numbers (k9_setfam_1 esk1_0) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk26_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk15_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk11_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk26_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k9_setfam_1 (k9_setfam_1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k9_setfam_1 (k9_setfam_1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k9_setfam_1 X1) (k9_setfam_1 (k9_setfam_1 X1)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk26_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_prob_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_prob_1 (k9_setfam_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_prob_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_prob_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_prob_1 (k9_setfam_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k9_setfam_1 k1_numbers) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((m1_subset_1 esk5_0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (forall X1, (v5_ordinal1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v2_finsub_1 (esk13_1 X1) -> False) -> False)
  -> (forall X1, (v2_finsub_1 (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk24_1 X1) -> False) -> False)
  -> ((v1_xxreal_0 esk31_0 -> False) -> False)
  -> ((v2_relat_1 esk21_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk31_0 -> False) -> False)
  -> ((v7_ordinal1 esk32_0 -> False) -> False)
  -> ((v7_ordinal1 esk28_0 -> False) -> False)
  -> ((v1_xreal_0 esk31_0 -> False) -> False)
  -> ((v1_xreal_0 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk31_0 -> False) -> False)
  -> ((v1_xboole_0 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk19_0 -> False) -> False)
  -> ((v1_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
