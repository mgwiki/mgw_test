(** $I sig/MizarPreamble.mgs **)

Theorem t5_fib_num:
 forall k3_int_2:set -> set -> set,
 forall esk23_0:set,
 forall r1_xxreal_0:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k5_numbers:set,
 forall esk22_0:set,
 forall esk21_0:set,
 forall esk24_0:set,
 forall v1_xcmplx_0:set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall k3_xcmplx_0:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall k1_numbers:set,
 forall esk25_2:set -> set -> set,
 forall v3_xxreal_0:set -> prop,
 forall k6_xcmplx_0:set -> set -> set,
 forall k4_xcmplx_0:set -> set,
 forall v1_xxreal_0:set -> prop,
 forall k6_nat_d:set -> set -> set,
 forall v1_finset_1:set -> prop,
 forall v4_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v6_membered:set -> prop,
 forall esk9_1:set -> set,
 forall k4_ordinal1:set,
 forall v3_ordinal1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk13_0:set,
 forall esk20_0:set,
 forall esk12_0:set,
 forall esk7_0:set,
 forall esk6_0:set,
 forall esk17_0:set,
 forall esk8_0:set,
 forall esk10_0:set,
 forall esk18_0:set,
 forall esk14_0:set,
 forall esk3_1:set -> set,
 forall esk5_0:set,
 forall esk11_0:set,
 forall esk15_0:set,
 forall np__0:set,
 forall k1_xboole_0:set,
 forall v7_membered:set -> prop,
 forall esk16_1:set -> set,
 forall v2_setfam_1:set -> prop,
 forall esk26_1:set -> set,
 forall k6_numbers:set,
 forall esk19_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v1_membered:set -> prop,
 forall v3_membered:set -> prop,
 forall v5_membered:set -> prop,
 forall v5_finset_1:set -> prop,
 forall v1_int_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k5_xcmplx_0:set -> set,
 forall v1_xreal_0:set -> prop,
 forall v2_xxreal_0:set -> prop,
 forall k7_xcmplx_0:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall np__1:set,
 forall k1_nat_1:set -> set -> set,
 forall k1_pre_ff:set -> set,
 forall k4_nat_1:set -> set -> set,
 forall k2_nat_1:set -> set -> set,
 forall v7_ordinal1:set -> prop,
     (forall X2 X1, ((k2_nat_1 (k4_nat_1 (k1_pre_ff X2) (k1_pre_ff X1)) (k4_nat_1 (k1_pre_ff (k1_nat_1 X2 np__1)) (k1_pre_ff (k1_nat_1 X1 np__1)))) = (k1_pre_ff (k1_nat_1 X1 (k1_nat_1 X2 np__1))) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1 X3 X4, ((k3_int_2 (k1_pre_ff X3) (k1_pre_ff X4)) = (k1_pre_ff (k3_int_2 X3 X4)) -> False) -> ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (r1_xxreal_0 esk23_0 X2 -> False) -> (r1_xxreal_0 esk23_0 X1 -> False) -> (k3_int_2 (k1_pre_ff esk22_0) (k1_pre_ff esk21_0)) = (k1_pre_ff (k3_int_2 esk22_0 esk21_0)) -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1 X3 X4, ((k3_int_2 (k1_pre_ff X3) (k1_pre_ff X4)) = (k1_pre_ff (k3_int_2 X3 X4)) -> False) -> ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> ((k3_int_2 (k1_pre_ff esk21_0) (k1_pre_ff esk22_0)) = (k1_pre_ff (k3_int_2 esk21_0 esk22_0)) -> False) -> (r1_xxreal_0 esk23_0 X2 -> False) -> (r1_xxreal_0 esk23_0 X1 -> False) -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (k3_int_2 (k1_pre_ff esk22_0) (k1_pre_ff esk21_0)) = (k1_pre_ff (k3_int_2 esk22_0 esk21_0)) -> (k3_int_2 (k1_pre_ff esk23_0) (k1_pre_ff esk24_0)) = (k1_pre_ff (k3_int_2 esk23_0 esk24_0)) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1 X3 X4, ((k3_int_2 (k1_pre_ff X3) (k1_pre_ff X4)) = (k1_pre_ff (k3_int_2 X3 X4)) -> False) -> ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (r1_xxreal_0 esk23_0 X2 -> False) -> (r1_xxreal_0 esk23_0 X1 -> False) -> (m1_subset_1 esk22_0 k5_numbers -> False) -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1 X3 X4, ((k3_int_2 (k1_pre_ff X3) (k1_pre_ff X4)) = (k1_pre_ff (k3_int_2 X3 X4)) -> False) -> ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (r1_xxreal_0 esk23_0 X2 -> False) -> (r1_xxreal_0 esk23_0 X1 -> False) -> (m1_subset_1 esk21_0 k5_numbers -> False) -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> ((k3_int_2 (k1_pre_ff esk21_0) (k1_pre_ff esk22_0)) = (k1_pre_ff (k3_int_2 esk21_0 esk22_0)) -> False) -> (k3_int_2 (k1_pre_ff esk23_0) (k1_pre_ff esk24_0)) = (k1_pre_ff (k3_int_2 esk23_0 esk24_0)) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (r1_xxreal_0 esk24_0 esk23_0 -> False) -> (k3_int_2 (k1_pre_ff esk22_0) (k1_pre_ff esk21_0)) = (k1_pre_ff (k3_int_2 esk22_0 esk21_0)) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (m1_subset_1 esk24_0 k5_numbers -> False) -> (k3_int_2 (k1_pre_ff esk22_0) (k1_pre_ff esk21_0)) = (k1_pre_ff (k3_int_2 esk22_0 esk21_0)) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (m1_subset_1 esk23_0 k5_numbers -> False) -> (k3_int_2 (k1_pre_ff esk22_0) (k1_pre_ff esk21_0)) = (k1_pre_ff (k3_int_2 esk22_0 esk21_0)) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (m1_subset_1 esk22_0 k5_numbers -> False) -> (k3_int_2 (k1_pre_ff esk23_0) (k1_pre_ff esk24_0)) = (k1_pre_ff (k3_int_2 esk23_0 esk24_0)) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (m1_subset_1 esk21_0 k5_numbers -> False) -> (k3_int_2 (k1_pre_ff esk23_0) (k1_pre_ff esk24_0)) = (k1_pre_ff (k3_int_2 esk23_0 esk24_0)) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> ((k3_int_2 (k1_pre_ff esk21_0) (k1_pre_ff esk22_0)) = (k1_pre_ff (k3_int_2 esk21_0 esk22_0)) -> False) -> (r1_xxreal_0 esk24_0 esk23_0 -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> ((k3_int_2 (k1_pre_ff esk21_0) (k1_pre_ff esk22_0)) = (k1_pre_ff (k3_int_2 esk21_0 esk22_0)) -> False) -> (m1_subset_1 esk24_0 k5_numbers -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> ((k3_int_2 (k1_pre_ff esk21_0) (k1_pre_ff esk22_0)) = (k1_pre_ff (k3_int_2 esk21_0 esk22_0)) -> False) -> (m1_subset_1 esk23_0 k5_numbers -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, ((k2_nat_1 (k1_pre_ff X1) (k1_pre_ff (k1_nat_1 X1 np__1))) = (k1_pre_ff (k2_nat_1 (k1_nat_1 X1 np__1) np__1)) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k3_int_2 X1 (k4_nat_1 X2 X3)) = (k3_int_2 X1 X3) -> False) -> (k3_int_2 X1 X2) = np__1 -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k3_xcmplx_0 X1 X3) (k3_xcmplx_0 X2 X3)) = (k3_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k3_int_2 (k2_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) X2) = (k3_int_2 X1 X2) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk4_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (m1_subset_1 esk22_0 k5_numbers -> False) -> (r1_xxreal_0 esk24_0 esk23_0 -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (m1_subset_1 esk22_0 k5_numbers -> False) -> (m1_subset_1 esk24_0 k5_numbers -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (m1_subset_1 esk22_0 k5_numbers -> False) -> (m1_subset_1 esk23_0 k5_numbers -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (m1_subset_1 esk21_0 k5_numbers -> False) -> (r1_xxreal_0 esk24_0 esk23_0 -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (m1_subset_1 esk21_0 k5_numbers -> False) -> (m1_subset_1 esk24_0 k5_numbers -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff X2)) = (k1_pre_ff (k3_int_2 X1 X2)) -> False) -> (m1_subset_1 esk21_0 k5_numbers -> False) -> (m1_subset_1 esk23_0 k5_numbers -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m2_subset_1 (k4_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, (m2_subset_1 (k2_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (m2_subset_1 (k1_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k7_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k7_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k3_int_2 X1 (k2_nat_1 X2 X1)) = (k3_int_2 X1 X2) -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, ((k3_int_2 (k1_pre_ff X1) (k1_pre_ff (k2_nat_1 X1 np__1))) = np__1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, ((k2_xcmplx_0 X2 (esk25_2 X2 X1)) = X1 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X2 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k6_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k6_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k3_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 (k5_xcmplx_0 X1) (k5_xcmplx_0 X2)) = (k5_xcmplx_0 (k3_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v7_ordinal1 (esk25_2 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> r1_xxreal_0 X2 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k6_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k6_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X2 X1, ((k4_nat_1 X1 X2) = (k4_nat_1 X2 X1) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k4_nat_1 X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, ((k1_nat_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_nat_1 X2 X1) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, ((k1_nat_1 X1 X2) = (k1_nat_1 X2 X1) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X2 X1, ((k7_xcmplx_0 (k5_xcmplx_0 X1) (k5_xcmplx_0 X2)) = (k7_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k6_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k6_nat_d X1 X2) k5_numbers -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 (k5_xcmplx_0 X2)) = (k7_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 (k5_xcmplx_0 X2)) = (k7_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k3_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k3_int_2 X1 X2) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (v1_int_1 (k6_xcmplx_0 X1 X2) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (v1_int_1 (k3_xcmplx_0 X1 X2) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (v1_int_1 (k2_xcmplx_0 X1 X2) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k7_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k3_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k6_nat_d X1 X2) = (k6_nat_d X2 X1) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k3_int_2 X1 X2) = (k6_nat_d X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k3_int_2 X1 X2) = (k3_int_2 X2 X1) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk9_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v2_xxreal_0 (k5_xcmplx_0 X1) -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v3_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v2_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v3_xxreal_0 (k5_xcmplx_0 X1) -> False)
  -> (forall X1, (X1 = k6_numbers -> False) -> ((k1_nat_1 (esk26_1 X1) np__1) = X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (m1_subset_1 (k1_pre_ff X1) k5_numbers -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_setfam_1 X1 -> False) -> (m1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (v2_xxreal_0 (k5_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 (k5_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k5_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k5_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, ((k7_xcmplx_0 np__1 X1) = (k5_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k5_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k5_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, ((k6_nat_d X1 X1) = X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk19_1 X1) -> False)
  -> (forall X1, (v2_setfam_1 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk9_1 X1) -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 X1 np__1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k6_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k6_nat_d X1 k6_numbers) = X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (r1_xxreal_0 k6_numbers X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (r2_hidden X1 k4_ordinal1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 k6_numbers X1) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (X1 = k6_numbers -> False) -> (v7_ordinal1 (esk26_1 X1) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, ((k5_xcmplx_0 (k5_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_int_1 (k4_xcmplx_0 X1) -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k5_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k5_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k5_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk9_1 X1) -> False) -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v2_setfam_1 X1 -> False)
  -> (forall X1, (v2_setfam_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_int_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k3_int_2 (k1_pre_ff esk1_0) (k1_pre_ff esk2_0)) = (k1_pre_ff (k3_int_2 esk1_0 esk2_0)) -> False)
  -> (r1_xxreal_0 np__0 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__1 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__1 np__0 -> False)
  -> (v2_setfam_1 esk13_0 -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk7_0 -> False)
  -> (v1_xboole_0 esk5_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk3_1 X1) X1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k7_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__0 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__1 -> False) -> False)
  -> ((m1_subset_1 esk12_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__0 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((m1_subset_1 esk6_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 esk2_0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 esk1_0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> (((k7_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v2_xxreal_0 esk14_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v5_finset_1 esk20_0 -> False) -> False)
  -> ((v3_xxreal_0 esk17_0 -> False) -> False)
  -> ((v7_membered esk15_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_finset_1 esk20_0 -> False) -> False)
  -> ((v1_finset_1 esk5_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_int_1 esk10_0 -> False) -> False)
  -> ((v1_int_1 esk6_0 -> False) -> False)
  -> ((v1_xreal_0 esk18_0 -> False) -> False)
  -> ((v1_xreal_0 esk17_0 -> False) -> False)
  -> ((v1_xreal_0 esk14_0 -> False) -> False)
  -> ((v1_xreal_0 esk8_0 -> False) -> False)
  -> ((v1_xreal_0 esk6_0 -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v1_xxreal_0 esk18_0 -> False) -> False)
  -> ((v1_xxreal_0 esk17_0 -> False) -> False)
  -> ((v1_xxreal_0 esk14_0 -> False) -> False)
  -> ((v1_xxreal_0 esk6_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk18_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk17_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk14_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk6_0 -> False) -> False)
  -> ((v6_membered esk15_0 -> False) -> False)
  -> ((v6_membered esk11_0 -> False) -> False)
  -> ((v6_membered esk7_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> (((k1_pre_ff np__1) = np__1 -> False) -> False)
  -> (((k1_pre_ff k6_numbers) = k6_numbers -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
