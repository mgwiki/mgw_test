(** $I sig/MizarPreamble.mgs **)

Theorem t69_setlim_2:
 forall r2_hidden:set -> set -> prop,
 forall esk22_4:set -> set -> set -> set -> set,
 forall k2_nat_1:set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall k4_kurato_0:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall k1_numbers:set,
 forall v3_ordinal1:set -> prop,
 forall esk12_1:set -> set,
 forall k4_ordinal1:set,
 forall v1_xxreal_0:set -> prop,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk14_0:set,
 forall esk11_2:set -> set -> set,
 forall esk16_1:set -> set,
 forall esk20_0:set,
 forall esk10_0:set,
 forall esk13_0:set,
 forall esk18_0:set,
 forall esk7_1:set -> set,
 forall esk15_1:set -> set,
 forall esk9_2:set -> set -> set,
 forall esk21_0:set,
 forall esk17_1:set -> set,
 forall v5_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall esk19_1:set -> set,
 forall v6_ordinal1:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk5_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk8_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v7_ordinal1:set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk23_3:set -> set -> set -> set,
 forall esk4_4:set -> set -> set -> set -> set,
 forall k9_setfam_1:set -> set,
 forall k8_nat_1:set -> set -> set -> set,
 forall k7_subset_1:set -> set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k5_numbers:set,
 forall m1_subset_1:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall k3_setlim_2:set -> set -> set -> set,
     (forall X3 X1 X2 X4, (X2 = (k3_setlim_2 X1 X3 X4) -> False) -> (k7_subset_1 X1 (k8_nat_1 (k9_setfam_1 X1) X3 (esk4_4 X1 X3 X4 X2)) (k8_nat_1 (k9_setfam_1 X1) X4 (esk4_4 X1 X3 X4 X2))) = (k8_nat_1 (k9_setfam_1 X1) X2 (esk4_4 X1 X3 X4 X2)) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X1) -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X1) -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X4 X1 X2 X3, (r2_hidden X1 (k3_funct_2 k5_numbers (k9_setfam_1 X2) X3 (k2_nat_1 X4 (esk22_4 X2 X3 X1 X4))) -> False) -> v1_funct_1 X3 -> m1_subset_1 X4 k5_numbers -> r2_hidden X1 (k4_kurato_0 X2 X3) -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X1 X3 X4 X2, (r2_hidden X2 (k4_kurato_0 X3 X4) -> False) -> v1_funct_1 X4 -> m1_subset_1 X1 k5_numbers -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X3) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X3))) -> r2_hidden X2 (k3_funct_2 k5_numbers (k9_setfam_1 X3) X4 (k2_nat_1 (esk23_3 X3 X4 X2) X1)) -> False)
  -> (forall X3 X1 X2 X4, (X4 = (k3_setlim_2 X1 X2 X3) -> False) -> (m1_subset_1 (esk4_4 X1 X2 X3 X4) k5_numbers -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X1) -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X1) -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X5 X4 X3 X2 X1, ((k8_nat_1 (k9_setfam_1 X2) X1 X5) = (k7_subset_1 X2 (k8_nat_1 (k9_setfam_1 X2) X3 X5) (k8_nat_1 (k9_setfam_1 X2) X4 X5)) -> False) -> X1 = (k3_setlim_2 X2 X3 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X5 k5_numbers -> v1_funct_2 X4 k5_numbers (k9_setfam_1 X2) -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X2) -> v1_funct_2 X1 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X4 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X4 X3 X1 X2, (m1_subset_1 (esk22_4 X1 X2 X3 X4) k5_numbers -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 k5_numbers -> r2_hidden X3 (k4_kurato_0 X1 X2) -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (k3_setlim_2 X1 X2 X3) (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X1) -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X2 X1 X3, (v1_funct_2 (k3_setlim_2 X1 X2 X3) k5_numbers (k9_setfam_1 X1) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X1) -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X2 X1 X3, (v1_funct_1 (k3_setlim_2 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 k5_numbers (k9_setfam_1 X1) -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X3 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (r2_hidden X3 (k4_kurato_0 X1 X2) -> False) -> (m1_subset_1 (esk23_3 X1 X2 X3) k5_numbers -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 k5_numbers (k9_setfam_1 X1) -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X1))) -> False)
  -> (forall X2 X3 X1, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk6_3 X1 X2 X3) X2 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k8_nat_1 X2 X1 X3) X2 -> False) -> v1_funct_1 X1 -> v7_ordinal1 X3 -> v1_funct_2 X1 k5_numbers X2 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k4_kurato_0 X2 X1) (k9_setfam_1 X2) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers (k9_setfam_1 X2) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 X2))) -> False)
  -> (forall X3 X2 X1, ((k8_nat_1 X2 X1 X3) = (k1_funct_1 X1 X3) -> False) -> v1_funct_1 X1 -> v7_ordinal1 X3 -> v1_funct_2 X1 k5_numbers X2 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 k5_numbers X2)) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k9_setfam_1 X2) -> False) -> m1_subset_1 X1 (k9_setfam_1 X2) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k9_setfam_1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk8_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k9_setfam_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (m2_subset_1 (k2_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k9_setfam_1 X2) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k4_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k4_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k4_xboole_0 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k4_xboole_0 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k4_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_nat_1 X2 X1) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk5_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k9_setfam_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk12_1 X1) -> False)
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
  -> (r1_tarski (k7_subset_1 esk1_0 (k4_kurato_0 esk1_0 esk2_0) (k4_kurato_0 esk1_0 esk3_0)) (k4_kurato_0 esk1_0 (k3_setlim_2 esk1_0 esk2_0 esk3_0)) -> False)
  -> (forall X1, v1_subset_1 (esk17_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k9_setfam_1 X1) -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk11_2 X1 X2) (k9_setfam_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk9_2 X1 X2) (k9_setfam_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk9_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 esk1_0))) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k9_setfam_1 (k2_zfmisc_1 k5_numbers (k9_setfam_1 esk1_0))) -> False) -> False)
  -> ((v1_funct_2 esk3_0 k5_numbers (k9_setfam_1 esk1_0) -> False) -> False)
  -> ((v1_funct_2 esk2_0 k5_numbers (k9_setfam_1 esk1_0) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk11_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk9_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k9_setfam_1 X1) (k9_setfam_1 (k9_setfam_1 X1)) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk9_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk9_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k9_setfam_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v5_ordinal1 (esk16_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk15_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk16_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk16_1 X1) -> False) -> False)
  -> ((v1_xxreal_0 esk20_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk20_0 -> False) -> False)
  -> ((v7_ordinal1 esk21_0 -> False) -> False)
  -> ((v7_ordinal1 esk18_0 -> False) -> False)
  -> ((v1_xreal_0 esk20_0 -> False) -> False)
  -> ((v1_xreal_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v2_ordinal1 esk14_0 -> False) -> False)
  -> ((v1_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
