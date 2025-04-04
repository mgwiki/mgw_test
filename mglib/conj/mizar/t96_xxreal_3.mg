(** $I sig/MizarPreamble.mgs **)

Theorem t96_xxreal_3:
 forall k1_xxreal_3:set -> set -> set,
 forall epred2_3:set -> set -> set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall esk25_3:set -> set -> set -> set,
 forall esk26_3:set -> set -> set -> set,
 forall k6_numbers:set,
 forall epred3_2:set -> set -> prop,
 forall k2_xxreal_0:set,
 forall v2_xxreal_0:set -> prop,
 forall v3_xxreal_0:set -> prop,
 forall k1_xxreal_0:set,
 forall r1_xxreal_0:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall k4_ordinal1:set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall esk24_0:set,
 forall esk14_0:set,
 forall esk12_0:set,
 forall esk4_1:set -> set,
 forall esk23_0:set,
 forall esk8_0:set,
 forall esk17_0:set,
 forall esk19_0:set,
 forall esk10_0:set,
 forall esk11_0:set,
 forall esk6_0:set,
 forall esk9_0:set,
 forall esk20_0:set,
 forall esk16_0:set,
 forall esk21_0:set,
 forall esk22_0:set,
 forall k4_tarski:set -> set -> set,
 forall esk7_0:set,
 forall k5_numbers:set,
 forall esk18_0:set,
 forall esk13_0:set,
 forall esk15_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall k1_numbers:set,
 forall v3_ordinal1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk5_2:set -> set -> set,
 forall epred1_2:set -> set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall esk28_3:set -> set -> set -> set,
 forall esk27_3:set -> set -> set -> set,
 forall k3_xcmplx_0:set -> set -> set,
 forall v1_xreal_0:set -> prop,
 forall epred4_3:set -> set -> set -> prop,
 forall k4_xxreal_3:set -> set -> set,
     (forall X2 X1 X3, ((k3_xcmplx_0 (esk27_3 X2 X3 X1) (esk28_3 X2 X3 X1)) = X1 -> False) -> X1 = (k4_xxreal_3 X2 X3) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X2 X1 X3, ((k2_xcmplx_0 (esk25_3 X2 X3 X1) (esk26_3 X2 X3 X1)) = X1 -> False) -> X1 = (k1_xxreal_3 X2 X3) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> epred2_3 X1 X3 X2 -> False)
  -> (forall X1 X3 X2, (v1_xcmplx_0 (esk28_3 X1 X2 X3) -> False) -> X3 = (k4_xxreal_3 X1 X2) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> epred4_3 X3 X2 X1 -> False)
  -> (forall X1 X3 X2, (v1_xcmplx_0 (esk27_3 X1 X2 X3) -> False) -> X3 = (k4_xxreal_3 X1 X2) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> epred4_3 X3 X2 X1 -> False)
  -> (forall X1 X3 X2, (v1_xcmplx_0 (esk26_3 X1 X2 X3) -> False) -> X3 = (k1_xxreal_3 X1 X2) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> epred2_3 X3 X2 X1 -> False)
  -> (forall X1 X3 X2, (v1_xcmplx_0 (esk25_3 X1 X2 X3) -> False) -> X3 = (k1_xxreal_3 X1 X2) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> epred2_3 X3 X2 X1 -> False)
  -> (forall X1 X3 X2, ((esk28_3 X2 X1 X3) = X1 -> False) -> X3 = (k4_xxreal_3 X2 X1) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> epred4_3 X3 X1 X2 -> False)
  -> (forall X1 X3 X2, ((esk27_3 X1 X2 X3) = X1 -> False) -> X3 = (k4_xxreal_3 X1 X2) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> epred4_3 X3 X2 X1 -> False)
  -> (forall X1 X3 X2, ((esk26_3 X2 X1 X3) = X1 -> False) -> X3 = (k1_xxreal_3 X2 X1) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> epred2_3 X3 X1 X2 -> False)
  -> (forall X1 X3 X2, ((esk25_3 X1 X2 X3) = X1 -> False) -> X3 = (k1_xxreal_3 X1 X2) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> epred2_3 X3 X2 X1 -> False)
  -> (forall X2 X1 X3 X4 X5, (X5 = (k4_xxreal_3 X3 X4) -> False) -> X2 = X4 -> X1 = X3 -> X5 = (k3_xcmplx_0 X1 X2) -> v1_xreal_0 X4 -> v1_xreal_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> epred4_3 X5 X4 X3 -> False)
  -> (forall X2 X1 X3 X4 X5, (X5 = (k1_xxreal_3 X3 X4) -> False) -> X2 = X4 -> X1 = X3 -> X5 = (k2_xcmplx_0 X1 X2) -> v1_xreal_0 X4 -> v1_xreal_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> epred2_3 X5 X4 X3 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, ((k1_xxreal_3 (k4_xxreal_3 X1 X2) (k4_xxreal_3 X1 X3)) = (k4_xxreal_3 X1 (k1_xxreal_3 X2 X3)) -> False) -> v1_xxreal_0 X3 -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X3 X1, (X1 = k6_numbers -> False) -> X1 = (k4_xxreal_3 X2 X3) -> epred3_2 X3 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X3 X2 X1, (X1 = k6_numbers -> False) -> X1 = (k1_xxreal_3 X2 X3) -> epred1_2 X2 X3 -> epred2_3 X1 X3 X2 -> False)
  -> (forall X2 X3 X1, (X1 = k2_xxreal_0 -> False) -> (v1_xreal_0 X2 -> False) -> X1 = (k4_xxreal_3 X2 X3) -> v3_xxreal_0 X2 -> v2_xxreal_0 X3 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X2 X3 X1, (X1 = k2_xxreal_0 -> False) -> (v1_xreal_0 X2 -> False) -> X1 = (k4_xxreal_3 X2 X3) -> v3_xxreal_0 X3 -> v2_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X3 X2 X1, (X1 = k2_xxreal_0 -> False) -> (v1_xreal_0 X3 -> False) -> X1 = (k4_xxreal_3 X2 X3) -> v3_xxreal_0 X2 -> v2_xxreal_0 X3 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X3 X2 X1, (X1 = k2_xxreal_0 -> False) -> (v1_xreal_0 X3 -> False) -> X1 = (k4_xxreal_3 X2 X3) -> v3_xxreal_0 X3 -> v2_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xxreal_0 -> False) -> (v1_xreal_0 X2 -> False) -> X1 = (k4_xxreal_3 X2 X3) -> v2_xxreal_0 X3 -> v2_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xxreal_0 -> False) -> (v1_xreal_0 X2 -> False) -> X1 = (k4_xxreal_3 X2 X3) -> v3_xxreal_0 X3 -> v3_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X3 X2 X1, (X1 = k1_xxreal_0 -> False) -> (v1_xreal_0 X3 -> False) -> X1 = (k4_xxreal_3 X2 X3) -> v2_xxreal_0 X3 -> v2_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X3 X2 X1, (X1 = k1_xxreal_0 -> False) -> (v1_xreal_0 X3 -> False) -> X1 = (k4_xxreal_3 X2 X3) -> v3_xxreal_0 X3 -> v3_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k3_xcmplx_0 X1 X3) (k3_xcmplx_0 X2 X3)) = (k3_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X3 X1, (X1 = (k4_xxreal_3 X2 X3) -> False) -> X1 = k6_numbers -> epred3_2 X3 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X3 X2 X1, (X1 = (k1_xxreal_3 X2 X3) -> False) -> X1 = k6_numbers -> epred1_2 X2 X3 -> epred2_3 X1 X3 X2 -> False)
  -> (forall X1 X3 X2, (X1 = (k4_xxreal_3 X2 X3) -> False) -> (v1_xreal_0 X2 -> False) -> X1 = k2_xxreal_0 -> v3_xxreal_0 X2 -> v2_xxreal_0 X3 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X1 X3 X2, (X1 = (k4_xxreal_3 X2 X3) -> False) -> (v1_xreal_0 X2 -> False) -> X1 = k2_xxreal_0 -> v3_xxreal_0 X3 -> v2_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X1 X3 X2, (X1 = (k4_xxreal_3 X2 X3) -> False) -> (v1_xreal_0 X2 -> False) -> X1 = k1_xxreal_0 -> v2_xxreal_0 X3 -> v2_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X1 X3 X2, (X1 = (k4_xxreal_3 X2 X3) -> False) -> (v1_xreal_0 X2 -> False) -> X1 = k1_xxreal_0 -> v3_xxreal_0 X3 -> v3_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X1 X2 X3, (X1 = (k4_xxreal_3 X2 X3) -> False) -> (v1_xreal_0 X3 -> False) -> X1 = k2_xxreal_0 -> v3_xxreal_0 X2 -> v2_xxreal_0 X3 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X1 X2 X3, (X1 = (k4_xxreal_3 X2 X3) -> False) -> (v1_xreal_0 X3 -> False) -> X1 = k2_xxreal_0 -> v3_xxreal_0 X3 -> v2_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X1 X2 X3, (X1 = (k4_xxreal_3 X2 X3) -> False) -> (v1_xreal_0 X3 -> False) -> X1 = k1_xxreal_0 -> v2_xxreal_0 X3 -> v2_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X1 X2 X3, (X1 = (k4_xxreal_3 X2 X3) -> False) -> (v1_xreal_0 X3 -> False) -> X1 = k1_xxreal_0 -> v3_xxreal_0 X3 -> v3_xxreal_0 X2 -> epred4_3 X1 X3 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk5_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (X2 = k2_xxreal_0 -> False) -> (X1 = k1_xxreal_0 -> False) -> X3 = k1_xxreal_0 -> X1 = (k1_xxreal_3 X2 X3) -> epred2_3 X1 X3 X2 -> False)
  -> (forall X1 X3 X2, (X2 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> X3 = k2_xxreal_0 -> X1 = (k1_xxreal_3 X2 X3) -> epred2_3 X1 X3 X2 -> False)
  -> (forall X1 X2 X3, (X3 = k2_xxreal_0 -> False) -> (X1 = k1_xxreal_0 -> False) -> X2 = k1_xxreal_0 -> X1 = (k1_xxreal_3 X2 X3) -> epred2_3 X1 X3 X2 -> False)
  -> (forall X1 X2 X3, (X3 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> X2 = k2_xxreal_0 -> X1 = (k1_xxreal_3 X2 X3) -> epred2_3 X1 X3 X2 -> False)
  -> (forall X2 X1, ((k1_xxreal_3 (k4_xxreal_3 X1 k6_numbers) (k4_xxreal_3 X1 X2)) = (k4_xxreal_3 X1 (k1_xxreal_3 k6_numbers X2)) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X3 X1 X2, (X2 = k2_xxreal_0 -> False) -> (X1 = (k1_xxreal_3 X2 X3) -> False) -> X3 = k1_xxreal_0 -> X1 = k1_xxreal_0 -> epred2_3 X1 X3 X2 -> False)
  -> (forall X3 X1 X2, (X2 = k1_xxreal_0 -> False) -> (X1 = (k1_xxreal_3 X2 X3) -> False) -> X3 = k2_xxreal_0 -> X1 = k2_xxreal_0 -> epred2_3 X1 X3 X2 -> False)
  -> (forall X2 X1 X3, (X3 = k2_xxreal_0 -> False) -> (X1 = (k1_xxreal_3 X2 X3) -> False) -> X2 = k1_xxreal_0 -> X1 = k1_xxreal_0 -> epred2_3 X1 X3 X2 -> False)
  -> (forall X2 X1 X3, (X3 = k1_xxreal_0 -> False) -> (X1 = (k1_xxreal_3 X2 X3) -> False) -> X2 = k2_xxreal_0 -> X1 = k2_xxreal_0 -> epred2_3 X1 X3 X2 -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v1_xreal_0 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v2_xxreal_0 X2 -> v2_xxreal_0 X1 -> v1_xreal_0 (k1_xxreal_3 X1 X2) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v1_xreal_0 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X2 -> v3_xxreal_0 X1 -> v1_xreal_0 (k1_xxreal_3 X1 X2) -> False)
  -> (forall X1 X2 X3, (epred4_3 X3 X2 X1 -> False) -> v1_xxreal_0 X3 -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2 X3, (epred2_3 X3 X2 X1 -> False) -> v1_xxreal_0 X3 -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> v1_xboole_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v1_xboole_0 (k4_xxreal_3 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v2_xxreal_0 (k1_xxreal_3 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 (k4_xxreal_3 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k3_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v2_xxreal_0 (k4_xxreal_3 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 (k4_xxreal_3 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 (k1_xxreal_3 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v1_xreal_0 X1 -> False) -> (v1_xboole_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> v2_xxreal_0 X2 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v1_xreal_0 X1 -> False) -> (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v2_xxreal_0 X2 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v1_xreal_0 X1 -> False) -> (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> v2_xxreal_0 X2 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v1_xreal_0 X1 -> False) -> (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X2 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v1_xxreal_0 X2 -> v1_xreal_0 X1 -> v1_xreal_0 (k1_xxreal_3 X1 X2) -> False)
  -> (forall X3 X1 X2 X4, ((k3_xcmplx_0 X3 X4) = (k4_xxreal_3 X1 X2) -> False) -> X2 = X4 -> X1 = X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v1_xcmplx_0 X4 -> v1_xcmplx_0 X3 -> False)
  -> (forall X3 X1 X2 X4, ((k2_xcmplx_0 X3 X4) = (k1_xxreal_3 X1 X2) -> False) -> X2 = X4 -> X1 = X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v1_xcmplx_0 X4 -> v1_xcmplx_0 X3 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v2_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v2_xxreal_0 X2 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X2 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X2 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v2_xxreal_0 X2 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X2 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X2 -> v3_xxreal_0 X1 -> False)
  -> (forall X2 X1, (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X2 -> False)
  -> (forall X2 X1, (v2_xxreal_0 X1 -> False) -> (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v2_xxreal_0 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v2_xxreal_0 X2 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (v1_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (v1_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v1_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (v1_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k3_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k3_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xxreal_0 (k4_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xxreal_0 (k1_xxreal_3 X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k4_xxreal_3 X1 X2) = (k4_xxreal_3 X2 X1) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, ((k1_xxreal_3 X1 X2) = (k1_xxreal_3 X2 X1) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (epred1_2 X1 X2 -> False) -> X2 = k1_xxreal_0 -> X2 = k2_xxreal_0 -> X1 = k1_xxreal_0 -> X1 = k2_xxreal_0 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (epred1_2 X1 X2 -> False) -> X2 = k1_xxreal_0 -> X2 = k2_xxreal_0 -> X1 = k1_xxreal_0 -> X1 = k2_xxreal_0 -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X1 X2 -> False) -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (epred3_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, (X2 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (v1_xreal_0 X1 -> False) -> (epred1_2 X1 X2 -> False) -> X2 = k2_xxreal_0 -> X1 = k1_xxreal_0 -> False)
  -> (forall X1 X2, (X2 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (v1_xreal_0 X1 -> False) -> (epred1_2 X2 X1 -> False) -> X2 = k2_xxreal_0 -> X1 = k1_xxreal_0 -> False)
  -> (forall X1 X2, (X2 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (v1_xreal_0 X2 -> False) -> (epred1_2 X1 X2 -> False) -> X2 = k2_xxreal_0 -> X1 = k1_xxreal_0 -> False)
  -> (forall X1 X2, (X2 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (v1_xreal_0 X2 -> False) -> (epred1_2 X2 X1 -> False) -> X2 = k2_xxreal_0 -> X1 = k1_xxreal_0 -> False)
  -> (forall X1 X2, (X2 = k1_xxreal_0 -> False) -> (X2 = k2_xxreal_0 -> False) -> (X1 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (v1_xreal_0 X1 -> False) -> (epred1_2 X2 X1 -> False) -> False)
  -> (forall X1 X2, (X2 = k1_xxreal_0 -> False) -> (X2 = k2_xxreal_0 -> False) -> (X1 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (v1_xreal_0 X2 -> False) -> (epred1_2 X2 X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (X1 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (r2_hidden X1 k1_numbers -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k1_xxreal_3 (k4_xxreal_3 esk3_0 esk1_0) (k4_xxreal_3 esk3_0 esk2_0)) = (k4_xxreal_3 esk3_0 (k1_xxreal_3 esk1_0 esk2_0)) -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xreal_0 esk18_0 -> False)
  -> (v1_xreal_0 esk12_0 -> False)
  -> (v1_xreal_0 k2_xxreal_0 -> False)
  -> (v1_xreal_0 k1_xxreal_0 -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk4_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk7_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((r1_xxreal_0 k6_numbers esk2_0 -> False) -> False)
  -> ((r1_xxreal_0 k6_numbers esk1_0 -> False) -> False)
  -> (((k4_tarski k6_numbers k1_numbers) = k2_xxreal_0 -> False) -> False)
  -> ((v1_xboole_0 esk23_0 -> False) -> False)
  -> ((v1_xboole_0 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v7_ordinal1 esk24_0 -> False) -> False)
  -> ((v7_ordinal1 esk21_0 -> False) -> False)
  -> ((v2_xxreal_0 esk17_0 -> False) -> False)
  -> ((v2_xxreal_0 esk16_0 -> False) -> False)
  -> ((v2_xxreal_0 esk12_0 -> False) -> False)
  -> ((v2_xxreal_0 esk7_0 -> False) -> False)
  -> ((v2_xxreal_0 k1_xxreal_0 -> False) -> False)
  -> ((v3_xxreal_0 esk20_0 -> False) -> False)
  -> ((v3_xxreal_0 esk19_0 -> False) -> False)
  -> ((v3_xxreal_0 esk18_0 -> False) -> False)
  -> ((v3_xxreal_0 k2_xxreal_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk22_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk19_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk16_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk15_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk9_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk7_0 -> False) -> False)
  -> ((v1_xreal_0 esk22_0 -> False) -> False)
  -> ((v1_xreal_0 esk19_0 -> False) -> False)
  -> ((v1_xreal_0 esk16_0 -> False) -> False)
  -> ((v1_xreal_0 esk10_0 -> False) -> False)
  -> ((v1_xreal_0 esk7_0 -> False) -> False)
  -> ((v2_ordinal1 esk13_0 -> False) -> False)
  -> ((v1_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 esk6_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_xxreal_0 esk23_0 -> False) -> False)
  -> ((v1_xxreal_0 esk22_0 -> False) -> False)
  -> ((v1_xxreal_0 esk20_0 -> False) -> False)
  -> ((v1_xxreal_0 esk19_0 -> False) -> False)
  -> ((v1_xxreal_0 esk18_0 -> False) -> False)
  -> ((v1_xxreal_0 esk17_0 -> False) -> False)
  -> ((v1_xxreal_0 esk16_0 -> False) -> False)
  -> ((v1_xxreal_0 esk12_0 -> False) -> False)
  -> ((v1_xxreal_0 esk11_0 -> False) -> False)
  -> ((v1_xxreal_0 esk7_0 -> False) -> False)
  -> ((v1_xxreal_0 esk3_0 -> False) -> False)
  -> ((v1_xxreal_0 esk2_0 -> False) -> False)
  -> ((v1_xxreal_0 esk1_0 -> False) -> False)
  -> ((v1_xxreal_0 k2_xxreal_0 -> False) -> False)
  -> ((v1_xxreal_0 k1_xxreal_0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> ((k1_xxreal_0 = k1_numbers -> False) -> False)
  -> False.
Admitted.
