(** $I sig/MizarPreamble.mgs **)

Theorem t8_pythtrip:
 forall esk7_2:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall k3_xcmplx_0:set -> set -> set,
 forall v2_xxreal_0:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v3_xxreal_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k6_nat_d:set -> set -> set,
 forall v5_finset_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk29_1:set -> set,
 forall k4_xcmplx_0:set -> set,
 forall np__1:set,
 forall v2_setfam_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk28_0:set,
 forall esk18_0:set,
 forall esk11_0:set,
 forall esk6_1:set -> set,
 forall esk19_0:set,
 forall esk21_0:set,
 forall esk26_0:set,
 forall esk27_0:set,
 forall esk24_0:set,
 forall esk14_0:set,
 forall esk16_0:set,
 forall esk25_0:set,
 forall esk12_0:set,
 forall esk10_0:set,
 forall esk13_0:set,
 forall esk23_0:set,
 forall esk22_0:set,
 forall esk9_0:set,
 forall esk8_0:set,
 forall esk17_0:set,
 forall esk20_0:set,
 forall esk30_0:set,
 forall k1_xboole_0:set,
 forall v3_relat_1:set -> prop,
 forall v2_finset_1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall k4_ordinal1:set,
 forall esk15_1:set -> set,
 forall v3_ordinal1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_int_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall r1_int_1:set -> set -> prop,
 forall esk4_2:set -> set -> set,
 forall k7_xcmplx_0:set -> set -> set,
 forall k1_numbers:set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall k4_nat_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k5_numbers:set,
 forall k6_numbers:set,
 forall v7_ordinal1:set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall r1_nat_d:set -> set -> prop,
 forall k3_int_2:set -> set -> set,
     (forall X2 X1 X3, (X3 = (k3_int_2 X1 X2) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_nat_d X3 X2 -> r1_nat_d X3 X1 -> r1_nat_d (esk5_3 X1 X2 X3) X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k3_int_2 X1 X2) -> False) -> (r1_nat_d (esk5_3 X1 X2 X3) X1 -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_nat_d X3 X2 -> r1_nat_d X3 X1 -> False)
  -> (forall X2 X1 X3, (X3 = (k3_int_2 X1 X2) -> False) -> (r1_nat_d (esk5_3 X1 X2 X3) X2 -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_nat_d X3 X2 -> r1_nat_d X3 X1 -> False)
  -> (forall X2 X1 X3, (X3 = (k3_int_2 X1 X2) -> False) -> (v7_ordinal1 (esk5_3 X1 X2 X3) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_nat_d X3 X2 -> r1_nat_d X3 X1 -> False)
  -> (forall X3 X2 X1, (X1 = k6_numbers -> False) -> (r1_nat_d X2 X3 -> False) -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> r1_nat_d (k4_nat_1 X1 X2) (k4_nat_1 X1 X3) -> False)
  -> (forall X3 X1 X2, (r1_nat_d (k4_nat_1 X3 X1) (k4_nat_1 X3 X2) -> False) -> r1_nat_d X1 X2 -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (r1_nat_d (k4_nat_1 X1 X2) (k4_nat_1 X1 X3) -> False) -> X1 = k6_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk7_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1 X4, (r1_nat_d X1 X4 -> False) -> X4 = (k3_int_2 X2 X3) -> v7_ordinal1 X4 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_nat_d X1 X3 -> r1_nat_d X1 X2 -> False)
  -> (forall X2 X1, (m2_subset_1 (k4_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k7_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k7_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (r1_nat_d X1 (k3_xcmplx_0 X2 X3) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_nat_d X1 X2 -> False)
  -> (forall X1 X2, ((k3_xcmplx_0 X2 (esk4_2 X2 X1)) = X1 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_nat_d X2 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k3_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v7_ordinal1 (esk4_2 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_nat_d X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X1 X2, (r1_nat_d X1 X2 -> False) -> X1 = (k3_int_2 X2 X3) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X3 X1 X2, (r1_nat_d X1 X2 -> False) -> X1 = (k3_int_2 X3 X2) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X3 X2, (r1_nat_d X3 X2 -> False) -> X2 = (k3_xcmplx_0 X3 X1) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k4_nat_1 X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k4_nat_1 X1 X2) = (k4_nat_1 X2 X1) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k6_nat_d X1 X2) k5_numbers -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (r1_int_1 X1 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_nat_d X1 X2 -> False)
  -> (forall X1 X2, (r1_nat_d X1 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_int_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_int_1 (k3_xcmplx_0 X1 X2) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k7_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k3_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k3_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k3_int_2 X1 X2) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k3_int_2 X1 X2) = (k3_int_2 X2 X1) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, ((k3_int_2 X1 X2) = (k6_nat_d X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k6_nat_d X1 X2) = (k6_nat_d X2 X1) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_int_1 X1 X1 -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (r1_nat_d X1 X1 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v3_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v2_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v2_setfam_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk29_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 X1 np__1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k6_nat_d X1 k6_numbers) = X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (r2_hidden X1 k4_ordinal1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 k6_numbers X1) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_int_1 (k4_xcmplx_0 X1) -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk15_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk29_1 X1) -> False) -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_int_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v2_setfam_1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k6_nat_d (k4_nat_1 esk1_0 esk2_0) (k4_nat_1 esk1_0 esk3_0)) = (k4_nat_1 esk1_0 (k6_nat_d esk2_0 esk3_0)) -> False)
  -> (v1_xboole_0 esk30_0 -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk8_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (((k7_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((m1_subset_1 esk17_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk9_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 esk3_0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 esk2_0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 esk1_0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (((k7_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v5_finset_1 esk30_0 -> False) -> False)
  -> ((v2_relat_1 esk19_0 -> False) -> False)
  -> ((v2_xxreal_0 esk22_0 -> False) -> False)
  -> ((v2_xxreal_0 esk21_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xcmplx_0 esk26_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk23_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk21_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk9_0 -> False) -> False)
  -> ((v1_xxreal_0 esk27_0 -> False) -> False)
  -> ((v1_xxreal_0 esk26_0 -> False) -> False)
  -> ((v1_xxreal_0 esk24_0 -> False) -> False)
  -> ((v1_xxreal_0 esk23_0 -> False) -> False)
  -> ((v1_xxreal_0 esk22_0 -> False) -> False)
  -> ((v1_xxreal_0 esk21_0 -> False) -> False)
  -> ((v1_xxreal_0 esk14_0 -> False) -> False)
  -> ((v1_xxreal_0 esk9_0 -> False) -> False)
  -> ((v3_xxreal_0 esk24_0 -> False) -> False)
  -> ((v3_xxreal_0 esk23_0 -> False) -> False)
  -> ((v1_int_1 esk16_0 -> False) -> False)
  -> ((v1_int_1 esk9_0 -> False) -> False)
  -> ((v1_xreal_0 esk26_0 -> False) -> False)
  -> ((v1_xreal_0 esk23_0 -> False) -> False)
  -> ((v1_xreal_0 esk21_0 -> False) -> False)
  -> ((v1_xreal_0 esk13_0 -> False) -> False)
  -> ((v1_xreal_0 esk9_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v2_ordinal1 esk18_0 -> False) -> False)
  -> ((v1_ordinal1 esk18_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v7_ordinal1 esk28_0 -> False) -> False)
  -> ((v7_ordinal1 esk25_0 -> False) -> False)
  -> ((v1_finset_1 esk30_0 -> False) -> False)
  -> ((v1_finset_1 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 esk27_0 -> False) -> False)
  -> ((v1_xboole_0 esk26_0 -> False) -> False)
  -> ((v1_xboole_0 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
