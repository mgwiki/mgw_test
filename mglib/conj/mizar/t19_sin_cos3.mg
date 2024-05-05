(** $I sig/MizarPreamble.mgs **)

Theorem t19_sin_cos3:
 forall k1_funct_1:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk4_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k4_xcmplx_0:set -> set,
 forall k6_xcmplx_0:set -> set -> set,
 forall k9_binop_2:set -> set -> set,
 forall k2_numbers:set,
 forall r1_tarski:set -> set -> prop,
 forall v4_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v6_membered:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall k5_numbers:set,
 forall k25_sin_cos:set -> set,
 forall k17_sin_cos:set -> set,
 forall np__1:set,
 forall k19_sin_cos:set,
 forall k6_numbers:set,
 forall v7_membered:set -> prop,
 forall k1_xboole_0:set,
 forall v1_finset_1:set -> prop,
 forall esk11_0:set,
 forall esk9_0:set,
 forall esk5_2:set -> set -> set,
 forall esk3_1:set -> set,
 forall k4_ordinal1:set,
 forall v2_xxreal_0:set -> prop,
 forall esk8_0:set,
 forall esk7_2:set -> set -> set,
 forall np__0:set,
 forall k1_xcmplx_0:set,
 forall esk6_0:set,
 forall esk10_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall k14_sin_cos:set -> set,
 forall k16_sin_cos:set,
 forall k24_sin_cos:set,
 forall k20_sin_cos:set -> set,
 forall v1_int_1:set -> prop,
 forall v1_membered:set -> prop,
 forall v3_membered:set -> prop,
 forall v5_membered:set -> prop,
 forall k11_binop_2:set -> set -> set,
 forall k10_binop_2:set -> set -> set,
 forall v1_xreal_0:set -> prop,
 forall k1_seq_1:set -> set -> set,
 forall v3_valued_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k3_xcmplx_0:set -> set -> set,
 forall k2_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall k7_complex1:set,
 forall k5_binop_2:set -> set -> set,
 forall k3_binop_2:set -> set -> set,
 forall k15_sin_cos:set -> set,
 forall k26_sin_cos:set -> set,
 forall k18_sin_cos:set -> set,
 forall k21_sin_cos:set -> set,
 forall k1_numbers:set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1, ((k5_binop_2 (k26_sin_cos X1) (k3_binop_2 (k21_sin_cos X2) (k5_binop_2 (k18_sin_cos X2) k7_complex1))) = (k15_sin_cos (k3_binop_2 X1 (k5_binop_2 X2 k7_complex1))) -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k3_xcmplx_0 X1 X3) (k3_xcmplx_0 X2 X3)) = (k3_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk4_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> v1_xboole_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_seq_1 X1 X2) k1_numbers -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, ((k6_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k10_binop_2 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k9_binop_2 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k11_binop_2 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_binop_2 X1 X2) k2_numbers -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_binop_2 X1 X2) k2_numbers -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k1_funct_1 X1 X2) = (k1_seq_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k3_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k10_binop_2 X1 X2) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, ((k9_binop_2 X1 X2) = (k9_binop_2 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, ((k9_binop_2 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k11_binop_2 X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, ((k5_binop_2 X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k3_binop_2 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k11_binop_2 X1 X2) = (k11_binop_2 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, ((k3_binop_2 X1 X2) = (k3_binop_2 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k5_binop_2 X1 X2) = (k5_binop_2 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (k26_sin_cos X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (m1_subset_1 (k21_sin_cos X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (m1_subset_1 (k18_sin_cos X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v1_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k2_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k25_sin_cos X1) = (k26_sin_cos X1) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, ((k20_sin_cos X1) = (k21_sin_cos X1) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, ((k17_sin_cos X1) = (k18_sin_cos X1) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xcmplx_0 X1 -> v1_xboole_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k15_sin_cos X1) k2_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, ((k1_seq_1 k24_sin_cos X1) = (k25_sin_cos X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, ((k1_seq_1 k19_sin_cos X1) = (k20_sin_cos X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, ((k1_seq_1 k16_sin_cos X1) = (k17_sin_cos X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k6_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k14_sin_cos X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k15_sin_cos X1) = (k14_sin_cos X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k3_binop_2 (k11_binop_2 (k3_funct_2 k1_numbers k1_numbers k24_sin_cos esk1_0) (k3_funct_2 k1_numbers k1_numbers k19_sin_cos esk2_0)) (k5_binop_2 (k11_binop_2 (k3_funct_2 k1_numbers k1_numbers k24_sin_cos esk1_0) (k3_funct_2 k1_numbers k1_numbers k16_sin_cos esk2_0)) k7_complex1)) = (k15_sin_cos (k3_binop_2 esk1_0 (k5_binop_2 esk2_0 k7_complex1))) -> False)
  -> (v1_finset_1 k2_numbers -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (v1_xboole_0 esk6_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k2_numbers -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1))) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1)) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) np__1) = (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) k1_xcmplx_0) = (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) np__0) = (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) np__1) = (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) -> False) -> False)
  -> (((k3_xcmplx_0 np__1 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1)) = (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) np__1) = (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1))) = k1_xcmplx_0 -> False) -> False)
  -> (((k4_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1))) = (k2_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 np__1) (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) k1_xcmplx_0) = (k2_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 k1_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1)) = (k2_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k4_xcmplx_0 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1)) = (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk7_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk5_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (((k6_xcmplx_0 np__1 (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1)) = k1_xcmplx_0 -> False) -> False)
  -> (((k6_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) = (k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) = (k6_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) = (k3_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) k1_xcmplx_0) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = (k2_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) = (k2_xcmplx_0 np__1 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk5_2 X1 X2) X1 X2 -> False) -> False)
  -> (((k3_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) = (k4_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1))) -> False) -> False)
  -> (((k6_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1))) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 np__1)) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1))) = (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) -> False) -> False)
  -> (((k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) (k4_xcmplx_0 np__1)) = (k6_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) -> False) -> False)
  -> ((m1_subset_1 k16_sin_cos (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False) -> False)
  -> ((m1_subset_1 k19_sin_cos (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False) -> False)
  -> ((m1_subset_1 k24_sin_cos (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False) -> False)
  -> (((k3_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) = (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) np__1) = (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) -> False) -> False)
  -> (((k3_xcmplx_0 np__1 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 np__1) (k2_xcmplx_0 k1_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = (k2_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) np__1) = (k6_xcmplx_0 np__1 k1_xcmplx_0) -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((v1_funct_2 k16_sin_cos k1_numbers k1_numbers -> False) -> False)
  -> ((v1_funct_2 k19_sin_cos k1_numbers k1_numbers -> False) -> False)
  -> ((v1_funct_2 k24_sin_cos k1_numbers k1_numbers -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 np__1) k1_xcmplx_0) = (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) -> False) -> False)
  -> (((k6_xcmplx_0 np__1 (k2_xcmplx_0 k1_xcmplx_0 np__1)) = (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) k1_xcmplx_0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 np__1) np__0) = (k2_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 np__1) np__1) = (k2_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) k1_xcmplx_0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) k1_xcmplx_0) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = k1_xcmplx_0 -> False) -> False)
  -> (((k3_xcmplx_0 k1_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 k1_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1))) = np__1 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk7_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk5_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk5_2 X1 X2) X1 -> False) -> False)
  -> (((k4_xcmplx_0 (k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0)) = k1_xcmplx_0 -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 np__1) np__1) = k1_xcmplx_0 -> False) -> False)
  -> (((k6_xcmplx_0 (k2_xcmplx_0 k1_xcmplx_0 np__1) k1_xcmplx_0) = np__1 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk5_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk7_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk5_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk7_2 X1 X2) -> False) -> False)
  -> (((k6_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) = (k2_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) = (k6_xcmplx_0 np__0 k1_xcmplx_0) -> False) -> False)
  -> (((k2_xcmplx_0 k1_xcmplx_0 (k4_xcmplx_0 np__1)) = (k6_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__1 k1_xcmplx_0) = (k2_xcmplx_0 k1_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk3_1 X1) X1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 (k4_xcmplx_0 np__1) k1_xcmplx_0) = (k4_xcmplx_0 k1_xcmplx_0) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 k1_xcmplx_0 k1_xcmplx_0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 esk1_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 k7_complex1 k2_numbers -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 k1_xcmplx_0 np__0) = k1_xcmplx_0 -> False) -> False)
  -> (((k6_xcmplx_0 k1_xcmplx_0 k1_xcmplx_0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 k1_xcmplx_0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 k1_xcmplx_0) = k1_xcmplx_0 -> False) -> False)
  -> (((k3_xcmplx_0 k1_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 k1_xcmplx_0 np__1) = k1_xcmplx_0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_funct_1 k16_sin_cos -> False) -> False)
  -> ((v1_funct_1 k19_sin_cos -> False) -> False)
  -> ((v1_funct_1 k24_sin_cos -> False) -> False)
  -> ((v7_membered esk11_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k2_numbers -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v1_xcmplx_0 esk10_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk8_0 -> False) -> False)
  -> ((v1_xcmplx_0 k1_xcmplx_0 -> False) -> False)
  -> ((v1_membered k2_numbers -> False) -> False)
  -> ((v6_membered esk11_0 -> False) -> False)
  -> ((v6_membered esk9_0 -> False) -> False)
  -> ((v6_membered esk6_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> ((k1_xcmplx_0 = k7_complex1 -> False) -> False)
  -> False.
Admitted.
