(** $I sig/MizarPreamble.mgs **)

Theorem t35_quatern3:
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_funct_2:set -> set -> set -> prop,
 forall m2_funct_2:set -> set -> set -> set -> prop,
 forall a_0_0_quaterni:set,
 forall r2_hidden:set -> set -> prop,
 forall k6_numbers:set,
 forall k1_seq_1:set -> set -> set,
 forall np__2:set,
 forall k1_numbers:set,
 forall k9_funct_2:set -> set -> set,
 forall np__4:set,
 forall np__3:set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v1_xreal_0:set -> prop,
 forall r1_xxreal_0:set -> set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall k3_xcmplx_0:set -> set -> set,
 forall v2_xxreal_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v5_membered:set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall v3_membered:set -> prop,
 forall v1_membered:set -> prop,
 forall k7_quaterni:set -> set -> set,
 forall v7_ordinal1:set -> prop,
 forall v1_rat_1:set -> prop,
 forall k1_funct_2:set -> set -> set,
 forall k2_numbers:set,
 forall k6_square_1:set -> set,
 forall np__1:set,
 forall k13_quaterni:set -> set,
 forall k15_quaterni:set -> set,
 forall v7_membered:set -> prop,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall np__0:set,
 forall esk11_0:set,
 forall k4_ordinal1:set,
 forall esk10_0:set,
 forall esk5_1:set -> set,
 forall esk4_2:set -> set -> set,
 forall esk9_0:set,
 forall esk12_0:set,
 forall k1_xboole_0:set,
 forall k16_quaterni:set -> set,
 forall k14_quaterni:set -> set,
 forall k3_quatern2:set -> set,
 forall k3_square_1:set -> set,
 forall k5_numbers:set,
 forall v1_int_1:set -> prop,
 forall k6_subset_1:set -> set -> set,
 forall v1_xxreal_0:set -> prop,
 forall v6_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v4_membered:set -> prop,
 forall k1_quaterni:set,
 forall k9_real_1:set -> set -> set,
 forall k4_xcmplx_0:set -> set,
 forall esk13_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall k6_xcmplx_0:set -> set -> set,
 forall k26_quaterni:set -> set -> set,
 forall esk8_1:set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k32_quaterni:set -> set,
 forall k5_square_1:set -> set,
 forall k20_quaterni:set -> set,
 forall k19_quaterni:set -> set,
 forall k18_quaterni:set -> set,
 forall k17_quaterni:set -> set,
 forall k7_real_1:set -> set -> set,
 forall k7_square_1:set -> set,
 forall v1_quaterni:set -> prop,
     (forall X1, ((k7_square_1 (k7_real_1 (k7_real_1 (k7_real_1 (k5_square_1 (k17_quaterni X1)) (k5_square_1 (k18_quaterni X1))) (k5_square_1 (k19_quaterni X1))) (k5_square_1 (k20_quaterni X1)))) = (k32_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_2 X1 X2 X3 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X4 X1 X2 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 X1 X4 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 X1 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X1 X2, (r2_hidden X2 a_0_0_quaterni -> False) -> X1 = X2 -> (k1_seq_1 X1 np__2) = k6_numbers -> (k1_seq_1 X1 np__3) = k6_numbers -> m2_funct_2 X1 np__4 k1_numbers (k9_funct_2 np__4 k1_numbers) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m2_funct_2 (esk6_3 X3 X1 X2) X3 X1 X2 -> False) -> m1_funct_2 X2 X3 X1 -> False)
  -> (forall X2 X1 X3 X4, (v1_xboole_0 X4 -> False) -> (m2_funct_2 X1 X3 X4 X2 -> False) -> m1_subset_1 X1 X2 -> m1_funct_2 X2 X3 X4 -> False)
  -> (forall X1, (m2_funct_2 (esk8_1 X1) np__4 k1_numbers (k9_funct_2 np__4 k1_numbers) -> False) -> r2_hidden X1 a_0_0_quaterni -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2 X4, (r1_xxreal_0 (k2_xcmplx_0 X1 X3) (k2_xcmplx_0 X2 X4) -> False) -> v1_xreal_0 X4 -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X3 X4 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 (k32_quaterni (k26_quaterni X1 X2)) (k2_xcmplx_0 (k32_quaterni X1) (k32_quaterni X2)) -> False) -> v1_quaterni X2 -> v1_quaterni X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k3_xcmplx_0 X1 X3) (k3_xcmplx_0 X2 X3)) = (k3_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 (k6_xcmplx_0 X1 X2) X3 -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 (k2_xcmplx_0 X2 X3) -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 (k2_xcmplx_0 X1 X3) X2 -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 (k6_xcmplx_0 X2 X3) -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 X1 (k6_xcmplx_0 X3 X2) -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 (k2_xcmplx_0 X1 X2) X3 -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 X1 (k2_xcmplx_0 X2 X3) -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 (k6_xcmplx_0 X1 X2) X3 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk7_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk13_2 X3 X2) -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k26_quaterni (k26_quaterni X1 X2) X3) = (k26_quaterni X1 (k26_quaterni X2 X3)) -> False) -> v1_quaterni X3 -> v1_quaterni X2 -> v1_quaterni X1 -> False)
  -> (forall X3 X2 X1, v1_xboole_0 X1 -> m1_funct_2 X1 X2 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_funct_2 (k9_funct_2 X2 X1) X2 X1 -> False) -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m1_subset_1 (k9_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k7_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (r2_hidden (esk13_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k9_real_1 X1 X2) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k7_real_1 X2 X1) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k6_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k26_quaterni X1 X2) k1_quaterni -> False) -> v1_quaterni X2 -> v1_quaterni X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v5_membered (k2_xboole_0 X1 X2) -> False) -> v5_membered X2 -> v5_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k2_xboole_0 X1 X2) -> False) -> v4_membered X2 -> v4_membered X1 -> False)
  -> (forall X2 X1, (v3_membered (k2_xboole_0 X1 X2) -> False) -> v3_membered X2 -> v3_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k2_xboole_0 X1 X2) -> False) -> v2_membered X2 -> v2_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k2_xboole_0 X1 X2) -> False) -> v1_membered X2 -> v1_membered X1 -> False)
  -> (forall X2 X1, (v6_membered (k2_xboole_0 X1 X2) -> False) -> v6_membered X2 -> v6_membered X1 -> False)
  -> (forall X2 X1, (v1_quaterni (k7_quaterni X1 X2) -> False) -> v1_quaterni X2 -> v1_quaterni X1 -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k7_quaterni X1 X2) = (k7_quaterni X2 X1) -> False) -> v1_quaterni X2 -> v1_quaterni X1 -> False)
  -> (forall X2 X1, ((k7_quaterni X1 X2) = (k26_quaterni X1 X2) -> False) -> v1_quaterni X2 -> v1_quaterni X1 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k26_quaterni X1 X2) = (k26_quaterni X2 X1) -> False) -> v1_quaterni X2 -> v1_quaterni X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (k7_square_1 X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (m1_subset_1 (k5_square_1 X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, ((k1_seq_1 (esk8_1 X1) np__3) = k6_numbers -> False) -> r2_hidden X1 a_0_0_quaterni -> False)
  -> (forall X1, ((k1_seq_1 (esk8_1 X1) np__2) = k6_numbers -> False) -> r2_hidden X1 a_0_0_quaterni -> False)
  -> (forall X2 X1, (v5_membered (k6_subset_1 X1 X2) -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k6_subset_1 X1 X2) -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v3_membered (k6_subset_1 X1 X2) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k6_subset_1 X1 X2) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k6_subset_1 X1 X2) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (v6_membered (k6_subset_1 X1 X2) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, ((k1_funct_2 X2 X1) = (k9_funct_2 X2 X1) -> False) -> (v1_xboole_0 X1 -> False) -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v1_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k2_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k7_square_1 X1) = (k6_square_1 X1) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, ((k5_square_1 X1) = (k3_square_1 X1) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k20_quaterni X1) k1_numbers -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, (m1_subset_1 (k19_quaterni X1) k1_numbers -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, (m1_subset_1 (k18_quaterni X1) k1_numbers -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, (m1_subset_1 (k17_quaterni X1) k1_numbers -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, (m1_subset_1 (k3_quatern2 X1) k1_numbers -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, ((esk8_1 X1) = X1 -> False) -> r2_hidden X1 a_0_0_quaterni -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 X1) = (k3_square_1 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v1_quaterni X1 -> False) -> m1_subset_1 X1 k1_quaterni -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k6_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k14_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, (v1_xreal_0 (k13_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, (v1_xreal_0 (k16_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, (v1_xreal_0 (k15_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, (v1_xreal_0 (k6_square_1 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k32_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k18_quaterni X1) = (k14_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, ((k17_quaterni X1) = (k13_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, ((k20_quaterni X1) = (k16_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, ((k19_quaterni X1) = (k15_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, ((k3_quatern2 X1) = (k32_quaterni X1) -> False) -> v1_quaterni X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_xxreal_0 (k3_quatern2 (k26_quaterni (k26_quaterni esk1_0 esk2_0) esk3_0)) (k7_real_1 (k7_real_1 (k3_quatern2 esk1_0) (k3_quatern2 esk2_0)) (k3_quatern2 esk3_0)) -> False)
  -> (r1_xxreal_0 np__1 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__0 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__1 np__0 -> False)
  -> (r1_xxreal_0 np__3 np__1 -> False)
  -> (r1_xxreal_0 np__3 np__0 -> False)
  -> (r1_xxreal_0 np__3 np__2 -> False)
  -> (r1_xxreal_0 np__2 np__1 -> False)
  -> (r1_xxreal_0 np__2 np__0 -> False)
  -> (r1_xxreal_0 np__4 np__1 -> False)
  -> (r1_xxreal_0 np__4 np__0 -> False)
  -> (r1_xxreal_0 np__4 np__3 -> False)
  -> (r1_xxreal_0 np__4 np__2 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 np__3 -> False)
  -> (v1_xboole_0 np__2 -> False)
  -> (v1_xboole_0 np__4 -> False)
  -> (v1_xboole_0 k1_quaterni -> False)
  -> (forall X2 X1, (m1_funct_2 (esk4_2 X1 X2) X1 X2 -> False) -> False)
  -> (((k2_xboole_0 (k6_subset_1 (k9_funct_2 np__4 k1_numbers) a_0_0_quaterni) k2_numbers) = k1_quaterni -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__3 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__2 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__4 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__3) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__4) (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__3)) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__2)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__4)) = np__3 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__3) (k4_xcmplx_0 np__3)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__3) (k4_xcmplx_0 np__4)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__3)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__2)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__4)) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__4) (k4_xcmplx_0 np__4)) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__2)) = np__4 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) X1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__2) = (k4_xcmplx_0 np__3) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) np__1) = (k4_xcmplx_0 np__3) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) np__2) = (k4_xcmplx_0 np__4) -> False) -> False)
  -> (((k3_xcmplx_0 (k4_xcmplx_0 np__2) np__1) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k3_xcmplx_0 (k4_xcmplx_0 np__4) np__1) = (k4_xcmplx_0 np__4) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 np__1 (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k3_xcmplx_0 np__2 (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__4) -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__1 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__0 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__2) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) np__2) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 (k4_xcmplx_0 np__2)) = np__3 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 (k4_xcmplx_0 np__1)) = np__3 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 (k4_xcmplx_0 np__2)) = np__4 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 (k4_xcmplx_0 np__2)) = np__0 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__3) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__2) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__4) = (k4_xcmplx_0 np__3) -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__3) = (k4_xcmplx_0 np__3) -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__2) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__4) = (k4_xcmplx_0 np__4) -> False) -> False)
  -> (((k6_xcmplx_0 np__3 np__4) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__3) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__4) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__3 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__3 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__2 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__2 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__4 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__4 k5_numbers -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__3 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__4 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__0 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__3 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__4 -> False) -> False)
  -> ((r1_xxreal_0 np__3 np__3 -> False) -> False)
  -> ((r1_xxreal_0 np__3 np__4 -> False) -> False)
  -> ((r1_xxreal_0 np__2 np__3 -> False) -> False)
  -> ((r1_xxreal_0 np__2 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__2 np__4 -> False) -> False)
  -> ((r1_xxreal_0 np__4 np__4 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__3 np__1) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 np__3 np__3) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__3 np__2) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__1) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__0) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__2) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__4 np__1) = np__3 -> False) -> False)
  -> (((k6_xcmplx_0 np__4 np__0) = np__4 -> False) -> False)
  -> (((k6_xcmplx_0 np__4 np__3) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__4 np__2) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 np__4 np__4) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__3) = np__3 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__2) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__4) = np__4 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__2) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__3 np__1) = np__3 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 np__1) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 np__2) = np__4 -> False) -> False)
  -> (((k3_xcmplx_0 np__4 np__1) = np__4 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__1) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__3) = np__4 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__2) = np__3 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__3 np__1) = np__4 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 np__1) = np__3 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 np__2) = np__4 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__3)) = np__3 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__2)) = np__2 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__4)) = np__4 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v2_xxreal_0 np__3 -> False) -> False)
  -> ((v2_xxreal_0 np__2 -> False) -> False)
  -> ((v2_xxreal_0 np__4 -> False) -> False)
  -> ((v7_membered esk12_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v7_membered k2_numbers -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v1_membered k2_numbers -> False) -> False)
  -> ((v6_membered esk12_0 -> False) -> False)
  -> ((v6_membered esk11_0 -> False) -> False)
  -> ((v6_membered esk9_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> ((v1_quaterni esk10_0 -> False) -> False)
  -> ((v1_quaterni esk3_0 -> False) -> False)
  -> ((v1_quaterni esk2_0 -> False) -> False)
  -> ((v1_quaterni esk1_0 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
