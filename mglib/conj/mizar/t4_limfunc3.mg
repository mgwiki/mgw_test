(** $I sig/MizarPreamble.mgs **)

Theorem t4_limfunc3:
 forall k2_xboole_0:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall a_2_0_limfunc3:set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall v1_xxreal_0:set -> prop,
 forall esk11_3:set -> set -> set -> set,
 forall a_2_1_rcomp_1:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall k6_xcmplx_0:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk4_2:set -> set -> set,
 forall v3_xxreal_0:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall k2_rcomp_1:set -> set -> set,
 forall v4_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v6_membered:set -> prop,
 forall k4_xxreal_1:set -> set -> set,
 forall v1_rat_1:set -> prop,
 forall k5_numbers:set,
 forall v5_ordinal1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall np__0:set,
 forall esk28_0:set,
 forall esk19_0:set,
 forall esk17_0:set,
 forall esk21_0:set,
 forall esk23_0:set,
 forall esk14_0:set,
 forall esk27_0:set,
 forall esk16_0:set,
 forall esk15_0:set,
 forall esk25_0:set,
 forall o_0_0_xboole_0:set,
 forall esk26_0:set,
 forall esk24_0:set,
 forall esk20_0:set,
 forall esk7_1:set -> set,
 forall esk13_0:set,
 forall esk18_0:set,
 forall esk22_0:set,
 forall v1_finset_1:set -> prop,
 forall np__1:set,
 forall k1_xboole_0:set,
 forall v7_membered:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall k4_ordinal1:set,
 forall v1_int_1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v1_membered:set -> prop,
 forall v3_membered:set -> prop,
 forall v5_membered:set -> prop,
 forall k4_xcmplx_0:set -> set,
 forall v2_xxreal_0:set -> prop,
 forall esk3_2:set -> set -> set,
 forall k1_tarski:set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall esk29_2:set -> set -> set,
 forall v1_xreal_0:set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall k6_numbers:set,
 forall k7_subset_1:set -> set -> set -> set,
 forall k4_subset_1:set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall k7_real_1:set -> set -> set,
 forall a_2_2_limfunc3:set -> set -> set,
 forall k9_real_1:set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall r1_xxreal_0:set -> set -> prop,
 forall a_2_1_limfunc3:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_numbers:set,
 forall r2_hidden:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall k4_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X1 X3, m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X1 (a_2_1_limfunc3 X2 X3) -> r1_xxreal_0 (esk10_3 X1 X2 X3) (k9_real_1 X3 X2) -> False)
  -> (forall X2 X1 X3, m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X1 (a_2_0_limfunc3 X2 X3) -> r1_xxreal_0 (esk9_3 X1 X2 X3) (k9_real_1 X3 X2) -> False)
  -> (forall X1 X3 X2, m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> r2_hidden X3 (a_2_2_limfunc3 X2 X1) -> r1_xxreal_0 (k7_real_1 X1 X2) (esk12_3 X3 X2 X1) -> False)
  -> (forall X1 X3 X2, m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> r2_hidden X3 (a_2_0_limfunc3 X2 X1) -> r1_xxreal_0 (k7_real_1 X1 X2) (esk9_3 X3 X2 X1) -> False)
  -> (forall X2 X3 X1, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk6_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X1 X3, m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X1 (a_2_2_limfunc3 X2 X3) -> r1_xxreal_0 (esk12_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X2 X3, m1_subset_1 X3 k1_numbers -> m1_subset_1 X1 k1_numbers -> r2_hidden X2 (a_2_1_limfunc3 X3 X1) -> r1_xxreal_0 X1 (esk10_3 X2 X3 X1) -> False)
  -> (forall X2 X1 X3, v1_xxreal_0 X3 -> v1_xxreal_0 X2 -> r2_hidden X1 (a_2_1_rcomp_1 X2 X3) -> r1_xxreal_0 (esk11_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X2 X3, v1_xxreal_0 X3 -> v1_xxreal_0 X1 -> r2_hidden X2 (a_2_1_rcomp_1 X3 X1) -> r1_xxreal_0 X1 (esk11_3 X2 X3 X1) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk12_3 X1 X2 X3) k1_numbers -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X1 (a_2_2_limfunc3 X2 X3) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk10_3 X1 X2 X3) k1_numbers -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X1 (a_2_1_limfunc3 X2 X3) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk9_3 X1 X2 X3) k1_numbers -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X1 (a_2_0_limfunc3 X2 X3) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk11_3 X1 X2 X3) k1_numbers -> False) -> v1_xxreal_0 X3 -> v1_xxreal_0 X2 -> r2_hidden X1 (a_2_1_rcomp_1 X2 X3) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X4 X1, (r1_xxreal_0 X1 (k9_real_1 X3 X4) -> False) -> (r2_hidden X2 (a_2_0_limfunc3 X4 X3) -> False) -> (r1_xxreal_0 (k7_real_1 X3 X4) X1 -> False) -> X1 = X2 -> m1_subset_1 X4 k1_numbers -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X4 X1 X3, (r1_xxreal_0 X1 X3 -> False) -> (r2_hidden X2 (a_2_2_limfunc3 X4 X3) -> False) -> (r1_xxreal_0 (k7_real_1 X3 X4) X1 -> False) -> X1 = X2 -> m1_subset_1 X4 k1_numbers -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X4 X2 X3 X1, (r1_xxreal_0 X3 X1 -> False) -> (r1_xxreal_0 X1 (k9_real_1 X3 X4) -> False) -> (r2_hidden X2 (a_2_1_limfunc3 X4 X3) -> False) -> X1 = X2 -> m1_subset_1 X4 k1_numbers -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1 X3, ((esk12_3 X1 X2 X3) = X1 -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X1 (a_2_2_limfunc3 X2 X3) -> False)
  -> (forall X2 X1 X3, ((esk10_3 X1 X2 X3) = X1 -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X1 (a_2_1_limfunc3 X2 X3) -> False)
  -> (forall X2 X1 X3, ((esk9_3 X1 X2 X3) = X1 -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X1 (a_2_0_limfunc3 X2 X3) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, ((esk11_3 X1 X2 X3) = X1 -> False) -> v1_xxreal_0 X3 -> v1_xxreal_0 X2 -> r2_hidden X1 (a_2_1_rcomp_1 X2 X3) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk8_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, (r1_xxreal_0 X2 k6_numbers -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X3 X1 -> r1_xxreal_0 (k2_xcmplx_0 X1 X2) X3 -> False)
  -> (forall X1 X2 X3, (r1_xxreal_0 X3 k6_numbers -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X2 X1 -> r1_xxreal_0 X1 (k6_xcmplx_0 X2 X3) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk29_2 X3 X2) -> False)
  -> (forall X3 X2 X4 X1, (r1_xxreal_0 X4 X1 -> False) -> (r1_xxreal_0 X1 X3 -> False) -> (r2_hidden X2 (a_2_1_rcomp_1 X3 X4) -> False) -> X1 = X2 -> v1_xxreal_0 X4 -> v1_xxreal_0 X3 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk3_2 X1 X2) = X1 -> r2_hidden (esk3_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k4_xboole_0 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k6_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k6_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k4_xboole_0 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k7_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k9_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (r2_hidden (esk29_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> r1_xxreal_0 X2 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k4_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk3_2 X1 X2) = X1 -> False) -> (r2_hidden (esk3_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_rcomp_1 X1 X2) (k1_zfmisc_1 k1_numbers) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k6_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k6_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X2 X1, ((k9_real_1 X1 X2) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k7_real_1 X2 X1) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk4_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k6_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v5_membered (k2_xboole_0 X1 X2) -> False) -> v5_membered X2 -> v5_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k2_xboole_0 X1 X2) -> False) -> v4_membered X2 -> v4_membered X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v3_membered (k2_xboole_0 X1 X2) -> False) -> v3_membered X2 -> v3_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k2_xboole_0 X1 X2) -> False) -> v2_membered X2 -> v2_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k2_xboole_0 X1 X2) -> False) -> v1_membered X2 -> v1_membered X1 -> False)
  -> (forall X2 X1, (v6_membered (k2_xboole_0 X1 X2) -> False) -> v6_membered X2 -> v6_membered X1 -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k4_xxreal_1 X1 X2) = (k2_rcomp_1 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, ((k2_rcomp_1 X1 X2) = (a_2_1_rcomp_1 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v5_membered (k4_xboole_0 X1 X2) -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k4_xboole_0 X1 X2) -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v3_membered (k4_xboole_0 X1 X2) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k4_xboole_0 X1 X2) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k4_xboole_0 X1 X2) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (v6_membered (k4_xboole_0 X1 X2) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v3_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v2_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, v3_xxreal_0 X1 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k6_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v5_membered (k1_tarski X1) -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v4_membered (k1_tarski X1) -> False) -> v1_rat_1 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_membered (k1_tarski X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v2_membered (k1_tarski X1) -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_membered (k1_tarski X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v6_membered (k1_tarski X1) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k4_subset_1 k1_numbers (k2_rcomp_1 (k9_real_1 esk2_0 esk1_0) esk2_0) (k2_rcomp_1 esk2_0 (k7_real_1 esk2_0 esk1_0))) = (k7_subset_1 k1_numbers (k2_rcomp_1 (k9_real_1 esk2_0 esk1_0) (k7_real_1 esk2_0 esk1_0)) (k1_tarski esk2_0)) -> False)
  -> (r1_xxreal_0 np__1 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__0 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 esk1_0 k6_numbers -> False)
  -> (r1_xxreal_0 np__1 np__0 -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__1 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__0 -> False) -> False)
  -> ((m1_subset_1 esk18_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__0 -> False) -> False)
  -> ((m1_subset_1 esk2_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 esk1_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v2_xxreal_0 esk21_0 -> False) -> False)
  -> ((v2_xxreal_0 esk20_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v3_xxreal_0 esk24_0 -> False) -> False)
  -> ((v3_xxreal_0 esk23_0 -> False) -> False)
  -> ((v7_membered esk22_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v2_ordinal1 esk19_0 -> False) -> False)
  -> ((v1_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk27_0 -> False) -> False)
  -> ((v1_xboole_0 esk26_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v7_ordinal1 esk28_0 -> False) -> False)
  -> ((v7_ordinal1 esk25_0 -> False) -> False)
  -> ((v1_xreal_0 esk26_0 -> False) -> False)
  -> ((v1_xreal_0 esk23_0 -> False) -> False)
  -> ((v1_xreal_0 esk20_0 -> False) -> False)
  -> ((v1_xreal_0 esk15_0 -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v1_xxreal_0 esk27_0 -> False) -> False)
  -> ((v1_xxreal_0 esk26_0 -> False) -> False)
  -> ((v1_xxreal_0 esk24_0 -> False) -> False)
  -> ((v1_xxreal_0 esk23_0 -> False) -> False)
  -> ((v1_xxreal_0 esk21_0 -> False) -> False)
  -> ((v1_xxreal_0 esk20_0 -> False) -> False)
  -> ((v1_xxreal_0 esk16_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk26_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk23_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk20_0 -> False) -> False)
  -> ((v6_membered esk22_0 -> False) -> False)
  -> ((v6_membered esk17_0 -> False) -> False)
  -> ((v6_membered esk13_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
