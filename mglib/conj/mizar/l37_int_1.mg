(** $I sig/MizarPreamble.mgs **)

Theorem l37_int_1:
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall v2_xxreal_0:set -> prop,
 forall k4_xcmplx_0:set -> set,
 forall v7_ordinal1:set -> prop,
 forall k5_real_1:set -> set -> set,
 forall k3_real_1:set -> set -> set,
 forall v6_ordinal1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall k1_real_1:set -> set,
 forall v3_ordinal1:set -> prop,
 forall k4_ordinal1:set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall np__1:set,
 forall esk19_0:set,
 forall esk10_0:set,
 forall esk6_0:set,
 forall esk13_0:set,
 forall esk17_0:set,
 forall o_0_0_xboole_0:set,
 forall esk9_0:set,
 forall esk5_0:set,
 forall esk7_0:set,
 forall esk16_0:set,
 forall esk8_0:set,
 forall esk15_0:set,
 forall esk18_0:set,
 forall esk14_0:set,
 forall esk12_0:set,
 forall esk4_0:set,
 forall esk2_1:set -> set,
 forall esk11_0:set,
 forall v1_finset_1:set -> prop,
 forall np__0:set,
 forall k1_xboole_0:set,
 forall v5_ordinal1:set -> prop,
 forall k6_numbers:set,
 forall v1_int_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk21_1:set -> set,
 forall k7_real_1:set -> set -> set,
 forall k6_xcmplx_0:set -> set -> set,
 forall v3_xxreal_0:set -> prop,
 forall esk20_0:set,
 forall k5_numbers:set,
 forall esk1_0:set,
 forall esk3_2:set -> set -> set,
 forall v1_xreal_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k1_numbers:set,
 forall esk22_2:set -> set -> set,
 forall esk23_2:set -> set -> set,
 forall r1_xxreal_0:set -> set -> prop,
 forall esk24_2:set -> set -> set,
     (forall X4 X2 X1 X3, (r1_xxreal_0 (esk24_2 X1 X2) X3 -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X3 -> r2_hidden X4 X1 -> r2_hidden X3 X2 -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> r1_xxreal_0 (esk22_2 X1 X2) (esk23_2 X1 X2) -> False)
  -> (forall X4 X2 X3 X1, (r1_xxreal_0 X1 (esk24_2 X2 X3) -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X1 -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> r1_xxreal_0 (esk22_2 X2 X3) (esk23_2 X2 X3) -> False)
  -> (forall X4 X2 X1 X3, (r1_xxreal_0 (esk24_2 X1 X2) X3 -> False) -> (r2_hidden (esk23_2 X1 X2) X2 -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X3 -> r2_hidden X4 X1 -> r2_hidden X3 X2 -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X4 X2 X1 X3, (r1_xxreal_0 (esk24_2 X1 X2) X3 -> False) -> (r2_hidden (esk22_2 X1 X2) X1 -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X3 -> r2_hidden X4 X1 -> r2_hidden X3 X2 -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X4 X2 X3 X1, (r1_xxreal_0 X1 (esk24_2 X2 X3) -> False) -> (r2_hidden (esk23_2 X2 X3) X3 -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X1 -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X4 X2 X3 X1, (r1_xxreal_0 X1 (esk24_2 X2 X3) -> False) -> (r2_hidden (esk22_2 X2 X3) X2 -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X1 -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1 X2, (v1_xreal_0 (esk24_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> r1_xxreal_0 (esk22_2 X1 X2) (esk23_2 X1 X2) -> False)
  -> (forall X3 X4 X2 X1, (v1_xreal_0 (esk23_2 X1 X2) -> False) -> (r1_xxreal_0 (esk24_2 X1 X2) X3 -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X3 -> r2_hidden X4 X1 -> r2_hidden X3 X2 -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X3 X4 X2 X1, (v1_xreal_0 (esk22_2 X1 X2) -> False) -> (r1_xxreal_0 (esk24_2 X1 X2) X3 -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X3 -> r2_hidden X4 X1 -> r2_hidden X3 X2 -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1 X4 X3 X2, (v1_xreal_0 (esk23_2 X2 X3) -> False) -> (r1_xxreal_0 X1 (esk24_2 X2 X3) -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X1 -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1 X4 X3 X2, (v1_xreal_0 (esk22_2 X2 X3) -> False) -> (r1_xxreal_0 X1 (esk24_2 X2 X3) -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X1 -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 X1 X3 -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 (k2_xcmplx_0 X1 X2) (k2_xcmplx_0 X3 X2) -> False)
  -> (forall X2 X1, (v1_xreal_0 (esk24_2 X1 X2) -> False) -> (r2_hidden (esk23_2 X1 X2) X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X2 X1, (v1_xreal_0 (esk24_2 X1 X2) -> False) -> (r2_hidden (esk22_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk3_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xreal_0 (esk23_2 X1 X2) -> False) -> (v1_xreal_0 (esk24_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X2 X1, (v1_xreal_0 (esk22_2 X1 X2) -> False) -> (v1_xreal_0 (esk24_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 (k2_xcmplx_0 X1 X3) (k2_xcmplx_0 X2 X3) -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (r1_xxreal_0 X1 esk1_0 -> False) -> m2_subset_1 X1 k1_numbers k5_numbers -> False)
  -> (forall X1 X2, (r2_hidden (k2_xcmplx_0 X1 X2) k5_numbers -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r2_hidden X2 k5_numbers -> r2_hidden X1 k5_numbers -> False)
  -> (forall X1 X2, (r1_xxreal_0 X2 X1 -> False) -> v1_xreal_0 X2 -> r2_hidden X2 k5_numbers -> r2_hidden X1 esk20_0 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k6_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k6_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (m1_subset_1 (k5_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X1 -> m1_subset_1 X2 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k7_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2, (m1_subset_1 (k3_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X1 -> m1_subset_1 X2 k1_numbers -> False)
  -> (forall X1, (r2_hidden X1 esk20_0 -> False) -> m1_subset_1 X1 k1_numbers -> r1_xxreal_0 (esk21_1 X1) X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k6_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k6_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, ((k5_real_1 X1 X2) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X1 -> m1_subset_1 X2 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k7_real_1 X2 X1) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2, ((k3_real_1 X1 X2) = (k3_real_1 X2 X1) -> False) -> v1_xreal_0 X1 -> m1_subset_1 X2 k1_numbers -> False)
  -> (forall X1 X2, ((k3_real_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X1 -> m1_subset_1 X2 k1_numbers -> False)
  -> (forall X2 X1, ((k6_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (r2_hidden X1 esk20_0 -> False) -> (r2_hidden (esk21_1 X1) k5_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_int_1 (k6_xcmplx_0 X1 X2) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (v1_int_1 (k2_xcmplx_0 X1 X2) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_xreal_0 (esk21_1 X1) -> False) -> (r2_hidden X1 esk20_0 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (k1_real_1 X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, ((k1_real_1 (k1_real_1 X1)) = X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k1_real_1 X1) = (k4_xcmplx_0 X1) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v3_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v2_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, v3_xxreal_0 X1 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> r2_hidden X1 k1_numbers -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k6_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (r2_hidden X1 k1_numbers -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_int_1 (k4_xcmplx_0 X1) -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_int_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_xxreal_0 np__1 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__0 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__1 np__0 -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk2_1 X1) X1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__1 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__0 -> False) -> False)
  -> ((m1_subset_1 esk20_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 esk10_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((m1_subset_1 esk6_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 esk4_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v2_xxreal_0 esk13_0 -> False) -> False)
  -> ((v2_xxreal_0 esk12_0 -> False) -> False)
  -> ((v2_xxreal_0 esk6_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xcmplx_0 esk17_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk14_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk12_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk6_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk4_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xxreal_0 esk18_0 -> False) -> False)
  -> ((v1_xxreal_0 esk17_0 -> False) -> False)
  -> ((v1_xxreal_0 esk15_0 -> False) -> False)
  -> ((v1_xxreal_0 esk14_0 -> False) -> False)
  -> ((v1_xxreal_0 esk13_0 -> False) -> False)
  -> ((v1_xxreal_0 esk12_0 -> False) -> False)
  -> ((v1_xxreal_0 esk8_0 -> False) -> False)
  -> ((v1_xxreal_0 esk6_0 -> False) -> False)
  -> ((v1_xxreal_0 esk4_0 -> False) -> False)
  -> ((v3_xxreal_0 esk15_0 -> False) -> False)
  -> ((v3_xxreal_0 esk14_0 -> False) -> False)
  -> ((v1_int_1 esk9_0 -> False) -> False)
  -> ((v1_int_1 esk4_0 -> False) -> False)
  -> ((v2_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 esk5_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v7_ordinal1 esk19_0 -> False) -> False)
  -> ((v7_ordinal1 esk16_0 -> False) -> False)
  -> ((v1_xreal_0 esk17_0 -> False) -> False)
  -> ((v1_xreal_0 esk14_0 -> False) -> False)
  -> ((v1_xreal_0 esk12_0 -> False) -> False)
  -> ((v1_xreal_0 esk7_0 -> False) -> False)
  -> ((v1_xreal_0 esk6_0 -> False) -> False)
  -> ((v1_xreal_0 esk4_0 -> False) -> False)
  -> ((v1_xreal_0 esk1_0 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k1_xboole_0 = o_0_0_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
