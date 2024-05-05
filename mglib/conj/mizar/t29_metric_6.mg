(** $I sig/MizarPreamble.mgs **)

Theorem t29_metric_6:
 forall u1_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v2_struct_0:set -> prop,
 forall k6_numbers:set,
 forall k1_numbers:set,
 forall r1_tarski:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v8_metric_1:set -> prop,
 forall v6_tbsp_1:set -> set -> prop,
 forall esk4_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall k4_metric_1:set -> set -> set -> set,
 forall v6_metric_1:set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall esk22_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk16_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall v3_ordinal1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall esk19_0:set,
 forall esk23_0:set,
 forall esk20_0:set,
 forall esk28_0:set,
 forall esk14_0:set,
 forall esk25_0:set,
 forall esk7_0:set,
 forall esk8_0:set,
 forall esk11_0:set,
 forall esk13_0:set,
 forall esk12_0:set,
 forall esk27_0:set,
 forall esk21_0:set,
 forall esk24_0:set,
 forall esk9_1:set -> set,
 forall k5_numbers:set,
 forall esk17_0:set,
 forall esk29_0:set,
 forall np__2:set,
 forall np__0:set,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall k4_ordinal1:set,
 forall v7_ordinal1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall k1_xboole_0:set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk15_1:set -> set,
 forall esk26_1:set -> set,
 forall k4_xcmplx_0:set -> set,
 forall k6_xcmplx_0:set -> set -> set,
 forall v2_xxreal_0:set -> prop,
 forall k7_xcmplx_0:set -> set -> set,
 forall v3_xxreal_0:set -> prop,
 forall esk6_2:set -> set -> set,
 forall v1_finset_1:set -> prop,
 forall esk10_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall v1_xreal_0:set -> prop,
 forall k9_metric_1:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall l1_metric_1:set -> prop,
 forall r1_xxreal_0:set -> set -> prop,
 forall esk31_1:set -> set,
 forall k7_real_1:set -> set -> set,
 forall esk30_1:set -> set,
 forall esk32_1:set -> set,
 forall k2_metric_1:set -> set -> set -> set,
 forall v9_metric_1:set -> prop,
     (forall X1, (v9_metric_1 X1 -> False) -> l1_metric_1 X1 -> r1_xxreal_0 (k2_metric_1 X1 (esk30_1 X1) (esk32_1 X1)) (k7_real_1 (k2_metric_1 X1 (esk30_1 X1) (esk31_1 X1)) (k2_metric_1 X1 (esk31_1 X1) (esk32_1 X1))) -> False)
  -> (forall X2 X3 X4 X1, (r1_xxreal_0 (k2_metric_1 X1 X2 X4) (k7_real_1 (k2_metric_1 X1 X2 X3) (k2_metric_1 X1 X3 X4)) -> False) -> v9_metric_1 X1 -> l1_metric_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X4 X2, l1_metric_1 X2 -> v1_xreal_0 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> r1_xxreal_0 X1 (k2_metric_1 X2 X3 X4) -> r2_hidden X4 (k9_metric_1 X2 X3 X1) -> False)
  -> (forall X4 X2 X1 X3, (v2_struct_0 X3 -> False) -> (v6_tbsp_1 X4 X3 -> False) -> (r1_xxreal_0 X1 k6_numbers -> False) -> v8_metric_1 X3 -> v9_metric_1 X3 -> l1_metric_1 X3 -> m1_subset_1 X1 k1_numbers -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X3)) -> r1_tarski X4 (k9_metric_1 X3 X2 X1) -> False)
  -> (forall X3 X4 X2 X1, (v2_struct_0 X1 -> False) -> (r1_xxreal_0 X2 (k2_metric_1 X1 X3 X4) -> False) -> (r2_hidden X4 (k9_metric_1 X1 X3 X2) -> False) -> l1_metric_1 X1 -> v1_xreal_0 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (r1_tarski X1 (k9_metric_1 X2 (esk5_2 X2 X1) (esk4_2 X2 X1)) -> False) -> v8_metric_1 X2 -> v9_metric_1 X2 -> l1_metric_1 X2 -> v6_tbsp_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X4 X1, v2_struct_0 X1 -> l1_metric_1 X1 -> v1_xreal_0 X4 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_hidden X2 (k9_metric_1 X1 X3 X4) -> False)
  -> (forall X3 X2 X1, (r1_xxreal_0 k6_numbers (k4_metric_1 X1 X2 X3) -> False) -> v6_metric_1 X1 -> v8_metric_1 X1 -> v9_metric_1 X1 -> l1_metric_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (r1_xxreal_0 X1 k6_numbers -> False) -> m1_subset_1 X1 k1_numbers -> r1_tarski esk2_0 (k9_metric_1 esk1_0 esk3_0 X1) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_metric_1 X1 X2 X3) k1_numbers -> False) -> v8_metric_1 X1 -> l1_metric_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (v6_tbsp_1 (k9_metric_1 X1 X2 X3) X1 -> False) -> v6_metric_1 X1 -> v8_metric_1 X1 -> v9_metric_1 X1 -> l1_metric_1 X1 -> v1_xreal_0 X3 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k2_metric_1 X1 X2 X3) k1_numbers -> False) -> l1_metric_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k4_metric_1 X1 X2 X3) = (k2_metric_1 X1 X2 X3) -> False) -> v8_metric_1 X1 -> l1_metric_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k4_metric_1 X1 X2 X3) = (k4_metric_1 X1 X3 X2) -> False) -> v8_metric_1 X1 -> l1_metric_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_metric_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_metric_1 X1 -> v1_xreal_0 X3 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r1_xxreal_0 X2 X1 -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X3 X4 -> r1_xxreal_0 (k2_xcmplx_0 X2 X4) (k2_xcmplx_0 X1 X3) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v8_metric_1 X1 -> v9_metric_1 X1 -> l1_metric_1 X1 -> v6_tbsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r1_xxreal_0 (esk4_2 X1 X2) k6_numbers -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk5_2 X1 X2) (u1_struct_0 X1) -> False) -> v8_metric_1 X1 -> v9_metric_1 X1 -> l1_metric_1 X1 -> v6_tbsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2 X4, (r1_xxreal_0 (k2_xcmplx_0 X1 X3) (k2_xcmplx_0 X2 X4) -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X3 X4 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk4_2 X1 X2) k1_numbers -> False) -> v8_metric_1 X1 -> v9_metric_1 X1 -> l1_metric_1 X1 -> v6_tbsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk10_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v6_tbsp_1 X2 X1 -> False) -> v6_metric_1 X1 -> v8_metric_1 X1 -> v9_metric_1 X1 -> l1_metric_1 X1 -> v1_finset_1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v6_tbsp_1 X2 X1 -> False) -> l1_metric_1 X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 X1 X3 -> False) -> v1_xxreal_0 X3 -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> r1_xxreal_0 X2 X3 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v6_metric_1 X1 -> v8_metric_1 X1 -> v9_metric_1 X1 -> l1_metric_1 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k6_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k6_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m1_subset_1 (k7_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k6_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k6_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k7_real_1 X2 X1) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k6_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_metric_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v6_metric_1 X1 -> v8_metric_1 X1 -> v9_metric_1 X1 -> l1_metric_1 X1 -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k7_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_finset_1 (esk22_1 X1) -> False) -> v6_metric_1 X1 -> v8_metric_1 X1 -> v9_metric_1 X1 -> l1_metric_1 X1 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v9_metric_1 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (u1_struct_0 X1) -> False) -> l1_metric_1 X1 -> False)
  -> (forall X1, (v9_metric_1 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (u1_struct_0 X1) -> False) -> l1_metric_1 X1 -> False)
  -> (forall X1, (v9_metric_1 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (u1_struct_0 X1) -> False) -> l1_metric_1 X1 -> False)
  -> (forall X2 X1, (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_tbsp_1 (esk18_1 X1) X1 -> False) -> l1_metric_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v2_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v3_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk16_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk15_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 X1 np__1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k6_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 k6_numbers X1) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_metric_1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_xxreal_0 (k7_xcmplx_0 np__1 np__2) np__0 -> False)
  -> (r1_xxreal_0 np__2 (k7_xcmplx_0 np__1 np__2) -> False)
  -> (r1_xxreal_0 np__1 (k7_xcmplx_0 np__1 np__2) -> False)
  -> (r1_xxreal_0 np__2 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__0 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__1 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__2 np__0 -> False)
  -> (r1_xxreal_0 np__2 np__1 -> False)
  -> (r1_xxreal_0 np__1 np__0 -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 np__2 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (((k6_xcmplx_0 (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2) (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2) (k7_xcmplx_0 np__1 np__2)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2) (k7_xcmplx_0 np__1 np__2)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k7_xcmplx_0 np__1 np__2) (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 (k7_xcmplx_0 np__1 np__2) (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2)) = (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2) -> False) -> False)
  -> (((k6_xcmplx_0 (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2) (k4_xcmplx_0 np__1)) = (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> ((r1_xxreal_0 (k7_xcmplx_0 np__1 np__2) (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 (k7_xcmplx_0 np__1 np__2) (k7_xcmplx_0 np__1 np__2)) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 (k7_xcmplx_0 np__1 np__2) (k7_xcmplx_0 np__1 np__2)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2) np__1) = (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2)) = (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> ((m2_subset_1 np__2 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> (((k6_xcmplx_0 (k7_xcmplx_0 np__1 np__2) np__1) = (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2) -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k7_xcmplx_0 np__1 np__2)) = (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2) -> False) -> False)
  -> (((k7_xcmplx_0 np__1 (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k4_xcmplx_0 (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2)) = (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 np__1 (k7_xcmplx_0 np__1 np__2)) = (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> (((k4_xcmplx_0 (k7_xcmplx_0 np__1 np__2)) = (k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2) -> False) -> False)
  -> ((r1_xxreal_0 (k7_xcmplx_0 np__1 np__2) np__2 -> False) -> False)
  -> ((r1_xxreal_0 (k7_xcmplx_0 np__1 np__2) np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> (((k7_xcmplx_0 np__1 (k7_xcmplx_0 np__1 np__2)) = np__2 -> False) -> False)
  -> (((k7_xcmplx_0 (k4_xcmplx_0 np__1) np__2) = (k7_xcmplx_0 np__1 (k4_xcmplx_0 np__2)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__2)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__2)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k7_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__2 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__0 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__1 -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) np__2) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__2) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__2) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__2) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 np__2 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__0 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((m1_subset_1 np__2 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__2 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((v6_tbsp_1 esk2_0 esk1_0 -> False) -> False)
  -> (((k7_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__2) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__0) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__1) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__1) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__1) = np__2 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__2)) = np__2 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v3_xxreal_0 esk24_0 -> False) -> False)
  -> ((v3_xxreal_0 esk23_0 -> False) -> False)
  -> ((v2_xxreal_0 esk21_0 -> False) -> False)
  -> ((v2_xxreal_0 esk20_0 -> False) -> False)
  -> ((v2_xxreal_0 np__2 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xcmplx_0 esk27_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk23_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk20_0 -> False) -> False)
  -> ((v1_xxreal_0 esk28_0 -> False) -> False)
  -> ((v1_xxreal_0 esk27_0 -> False) -> False)
  -> ((v1_xxreal_0 esk24_0 -> False) -> False)
  -> ((v1_xxreal_0 esk23_0 -> False) -> False)
  -> ((v1_xxreal_0 esk21_0 -> False) -> False)
  -> ((v1_xxreal_0 esk20_0 -> False) -> False)
  -> ((v1_xxreal_0 esk14_0 -> False) -> False)
  -> ((v7_ordinal1 esk29_0 -> False) -> False)
  -> ((v7_ordinal1 esk25_0 -> False) -> False)
  -> ((v1_xboole_0 esk28_0 -> False) -> False)
  -> ((v1_xboole_0 esk27_0 -> False) -> False)
  -> ((v1_xboole_0 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_xreal_0 esk27_0 -> False) -> False)
  -> ((v1_xreal_0 esk23_0 -> False) -> False)
  -> ((v1_xreal_0 esk20_0 -> False) -> False)
  -> ((v1_xreal_0 esk13_0 -> False) -> False)
  -> ((v2_ordinal1 esk17_0 -> False) -> False)
  -> ((v1_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((l1_struct_0 esk8_0 -> False) -> False)
  -> ((l1_metric_1 esk7_0 -> False) -> False)
  -> ((l1_metric_1 esk1_0 -> False) -> False)
  -> ((v9_metric_1 esk1_0 -> False) -> False)
  -> ((v8_metric_1 esk1_0 -> False) -> False)
  -> ((v6_metric_1 esk1_0 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> ((k1_xboole_0 = k6_numbers -> False) -> False)
  -> False.
Admitted.
