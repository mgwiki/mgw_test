(** $I sig/MizarPreamble.mgs **)

Theorem t7_polyeq_5:
 forall v1_xboole_0:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall k3_xcmplx_0:set -> set -> set,
 forall k20_sin_cos:set -> set,
 forall k13_complex1:set -> set -> set,
 forall k17_sin_cos:set -> set,
 forall k2_xcmplx_0:set -> set -> set,
 forall k1_power:set -> set -> set,
 forall k1_polyeq_5:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall k7_xcmplx_0:set -> set -> set,
 forall v3_xxreal_0:set -> prop,
 forall k1_numbers:set,
 forall k7_real_1:set -> set -> set,
 forall k2_numbers:set,
 forall r1_tarski:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall np__1:set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall esk22_0:set,
 forall esk13_0:set,
 forall esk11_0:set,
 forall esk16_0:set,
 forall esk20_0:set,
 forall esk17_0:set,
 forall esk9_0:set,
 forall k31_sin_cos:set,
 forall esk19_0:set,
 forall esk7_0:set,
 forall esk8_0:set,
 forall esk5_0:set,
 forall esk10_0:set,
 forall esk18_0:set,
 forall esk21_0:set,
 forall esk15_0:set,
 forall esk6_0:set,
 forall esk3_1:set -> set,
 forall k1_xcmplx_0:set,
 forall esk12_0:set,
 forall esk14_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall v5_ordinal1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall k16_complex1:set -> set,
 forall k4_ordinal1:set,
 forall k8_real_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v2_xxreal_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall k5_numbers:set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_newton:set -> set -> set,
 forall k3_binop_2:set -> set -> set,
 forall k7_complex1:set,
 forall k18_sin_cos:set -> set,
 forall k5_binop_2:set -> set -> set,
 forall k17_complex1:set -> set,
 forall k2_power:set -> set -> set,
 forall k21_sin_cos:set -> set,
 forall k12_binop_2:set -> set -> set,
 forall k9_binop_2:set -> set -> set,
 forall k32_sin_cos:set,
 forall np__2:set,
 forall k1_comptrig:set -> set,
 forall k11_binop_2:set -> set -> set,
 forall k6_numbers:set,
     (forall X1 X3 X2, (X2 = k6_numbers -> False) -> ((k1_newton (k3_binop_2 (k11_binop_2 (k2_power X2 (k17_complex1 X1)) (k21_sin_cos (k12_binop_2 (k9_binop_2 (k1_comptrig X1) (k11_binop_2 (k11_binop_2 np__2 k32_sin_cos) X3)) X2))) (k5_binop_2 (k11_binop_2 (k2_power X2 (k17_complex1 X1)) (k18_sin_cos (k12_binop_2 (k9_binop_2 (k1_comptrig X1) (k11_binop_2 (k11_binop_2 np__2 k32_sin_cos) X3)) X2))) k7_complex1)) X2) = X1 -> False) -> v1_xcmplx_0 X1 -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 (k1_power X1 (k17_complex1 X2)) (k2_xcmplx_0 (k20_sin_cos (k13_complex1 (k1_comptrig X2) X1)) (k3_xcmplx_0 (k17_sin_cos (k13_complex1 (k1_comptrig X2) X1)) k7_complex1))) = (k1_polyeq_5 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_xcmplx_0 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k3_xcmplx_0 X1 X3) (k3_xcmplx_0 X2 X3)) = (k3_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk4_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k7_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k7_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k3_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> v1_xboole_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> v1_xboole_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (m1_subset_1 (k2_power X1 X2) k1_numbers -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k7_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, ((k2_power X1 X2) = (k1_power X1 X2) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k1_numbers -> False)
  -> (forall X2 X1, ((k8_real_1 X1 X2) = (k8_real_1 X2 X1) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k8_real_1 X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k7_real_1 X2 X1) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k12_binop_2 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k13_complex1 X1 X2) k2_numbers -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k9_binop_2 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_binop_2 X1 X2) k2_numbers -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_binop_2 X1 X2) k2_numbers -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k11_binop_2 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_xcmplx_0 (k1_polyeq_5 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k7_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 (k1_power X1 X2) -> False) -> v7_ordinal1 X1 -> v1_xreal_0 X2 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k3_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k1_newton X1 X2) -> False) -> v7_ordinal1 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k3_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k1_newton X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k7_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k3_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 (k1_newton X1 X2) -> False) -> v1_xcmplx_0 X1 -> v7_ordinal1 X2 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k12_binop_2 X1 X2) = (k7_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, ((k13_complex1 X1 X2) = (k7_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k9_binop_2 X1 X2) = (k9_binop_2 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, ((k9_binop_2 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, ((k5_binop_2 X1 X2) = (k5_binop_2 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k5_binop_2 X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k11_binop_2 X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, ((k3_binop_2 X1 X2) = (k3_binop_2 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k3_binop_2 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k11_binop_2 X1 X2) = (k11_binop_2 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (k21_sin_cos X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (m1_subset_1 (k18_sin_cos X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k21_sin_cos X1) = (k20_sin_cos X1) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, ((k18_sin_cos X1) = (k17_sin_cos X1) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, v3_xxreal_0 X1 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (m1_subset_1 (k1_comptrig X1) k1_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k17_complex1 X1) k1_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, ((k16_complex1 (k16_complex1 X1)) = (k16_complex1 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k17_complex1 (k17_complex1 X1)) = (k17_complex1 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 X1 np__1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (r2_hidden X1 k4_ordinal1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 k6_numbers X1) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k16_complex1 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k17_sin_cos X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k20_sin_cos X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k17_complex1 X1) = (k16_complex1 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k1_newton (k1_polyeq_5 esk2_0 esk1_0) esk2_0) = esk1_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 np__2 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (((k2_xcmplx_0 (k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) k1_xcmplx_0) (k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) k1_xcmplx_0)) = k1_xcmplx_0 -> False) -> False)
  -> (((k3_xcmplx_0 (k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) k1_xcmplx_0) np__1) = (k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) k1_xcmplx_0) -> False) -> False)
  -> (((k3_xcmplx_0 np__1 (k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) k1_xcmplx_0)) = (k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) k1_xcmplx_0) -> False) -> False)
  -> (((k3_xcmplx_0 np__2 (k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) k1_xcmplx_0)) = k1_xcmplx_0 -> False) -> False)
  -> (((k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) k1_xcmplx_0) = (k3_xcmplx_0 k1_xcmplx_0 (k7_xcmplx_0 np__1 np__2)) -> False) -> False)
  -> (((k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) (k3_xcmplx_0 np__2 k1_xcmplx_0)) = k1_xcmplx_0 -> False) -> False)
  -> (((k3_xcmplx_0 (k3_xcmplx_0 np__2 k1_xcmplx_0) (k7_xcmplx_0 np__1 np__2)) = k1_xcmplx_0 -> False) -> False)
  -> (((k2_xcmplx_0 (k7_xcmplx_0 np__1 np__2) (k7_xcmplx_0 np__1 np__2)) = np__1 -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__2 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> (((k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) np__1) = (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> (((k3_xcmplx_0 (k3_xcmplx_0 np__2 k1_xcmplx_0) np__1) = (k3_xcmplx_0 np__2 k1_xcmplx_0) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 np__1) np__1) = (k2_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 np__2) np__1) = (k2_xcmplx_0 k1_xcmplx_0 np__2) -> False) -> False)
  -> (((k3_xcmplx_0 np__1 (k7_xcmplx_0 np__1 np__2)) = (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> (((k3_xcmplx_0 np__1 (k3_xcmplx_0 np__2 k1_xcmplx_0)) = (k3_xcmplx_0 np__2 k1_xcmplx_0) -> False) -> False)
  -> (((k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) np__2) = np__1 -> False) -> False)
  -> (((k7_xcmplx_0 np__1 (k7_xcmplx_0 np__1 np__2)) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 (k7_xcmplx_0 np__1 np__2)) = np__1 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 k1_xcmplx_0) = (k3_xcmplx_0 k1_xcmplx_0 np__2) -> False) -> False)
  -> (((k3_xcmplx_0 np__2 k1_xcmplx_0) = (k2_xcmplx_0 k1_xcmplx_0 k1_xcmplx_0) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk3_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk11_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk6_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__2 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__2 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 k32_sin_cos k1_numbers -> False) -> False)
  -> ((m1_subset_1 k7_complex1 k2_numbers -> False) -> False)
  -> (((k7_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__2) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 k1_xcmplx_0) = k1_xcmplx_0 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 np__1) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 k1_xcmplx_0 np__1) = k1_xcmplx_0 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__1) = np__2 -> False) -> False)
  -> ((v2_xxreal_0 esk16_0 -> False) -> False)
  -> ((v2_xxreal_0 esk15_0 -> False) -> False)
  -> ((v2_xxreal_0 esk6_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v2_xxreal_0 np__2 -> False) -> False)
  -> ((v1_xxreal_0 esk21_0 -> False) -> False)
  -> ((v1_xxreal_0 esk20_0 -> False) -> False)
  -> ((v1_xxreal_0 esk18_0 -> False) -> False)
  -> ((v1_xxreal_0 esk17_0 -> False) -> False)
  -> ((v1_xxreal_0 esk16_0 -> False) -> False)
  -> ((v1_xxreal_0 esk15_0 -> False) -> False)
  -> ((v1_xxreal_0 esk10_0 -> False) -> False)
  -> ((v1_xxreal_0 esk6_0 -> False) -> False)
  -> ((v3_xxreal_0 esk18_0 -> False) -> False)
  -> ((v3_xxreal_0 esk17_0 -> False) -> False)
  -> ((v1_xreal_0 esk20_0 -> False) -> False)
  -> ((v1_xreal_0 esk17_0 -> False) -> False)
  -> ((v1_xreal_0 esk15_0 -> False) -> False)
  -> ((v1_xreal_0 esk9_0 -> False) -> False)
  -> ((v1_xreal_0 esk6_0 -> False) -> False)
  -> ((v1_xreal_0 k31_sin_cos -> False) -> False)
  -> ((v2_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk5_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v7_ordinal1 esk22_0 -> False) -> False)
  -> ((v7_ordinal1 esk19_0 -> False) -> False)
  -> ((v7_ordinal1 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 esk7_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk20_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk17_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk15_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk14_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk8_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk6_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk1_0 -> False) -> False)
  -> ((v1_xcmplx_0 k1_xcmplx_0 -> False) -> False)
  -> ((k7_complex1 = k1_xcmplx_0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k31_sin_cos = k32_sin_cos -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
