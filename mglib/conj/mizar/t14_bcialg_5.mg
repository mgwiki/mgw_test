(** $I sig/MizarPreamble.mgs **)

Theorem t14_bcialg_5:
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall v3_xxreal_0:set -> prop,
 forall esk29_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall esk5_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk6_0:set,
 forall esk1_0:set,
 forall esk32_0:set,
 forall esk22_0:set,
 forall esk19_0:set,
 forall esk14_1:set -> set,
 forall esk12_0:set,
 forall esk9_0:set,
 forall esk24_0:set,
 forall esk30_0:set,
 forall esk27_0:set,
 forall esk18_0:set,
 forall esk17_0:set,
 forall esk28_0:set,
 forall esk10_0:set,
 forall esk16_0:set,
 forall o_0_0_xboole_0:set,
 forall esk31_0:set,
 forall esk26_0:set,
 forall esk25_0:set,
 forall esk11_0:set,
 forall esk23_0:set,
 forall v5_ordinal1:set -> prop,
 forall l2_struct_0:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall k4_ordinal1:set,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall v13_struct_0:set -> set -> prop,
 forall esk20_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk21_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v2_xxreal_0:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall esk15_2:set -> set -> set,
 forall u1_bcialg_1:set -> set,
 forall k5_binop_1:set -> set -> set -> set -> set,
 forall l1_bcialg_1:set -> prop,
 forall esk13_4:set -> set -> set -> set -> set,
 forall k1_bcialg_2:set -> set -> set -> set -> set,
 forall k1_bcialg_1:set -> set -> set -> set,
 forall np__1:set,
 forall k2_nat_1:set -> set -> set,
 forall m1_bcialg_5:set -> set -> set -> set -> set -> prop,
 forall v3_bcialg_1:set -> prop,
 forall v5_bcialg_1:set -> prop,
 forall l2_bcialg_1:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall v7_bcialg_1:set -> prop,
 forall v4_bcialg_1:set -> prop,
 forall k1_bcialg_5:set -> set -> set -> set -> set -> set,
 forall esk8_5:set -> set -> set -> set -> set -> set,
 forall esk7_5:set -> set -> set -> set -> set -> set,
 forall v2_struct_0:set -> prop,
     (forall X4 X3 X2 X5 X1, (v2_struct_0 X1 -> False) -> (m1_bcialg_5 X1 X2 X3 X4 X5 -> False) -> (k1_bcialg_5 X1 (esk8_5 X2 X3 X4 X5 X1) (esk7_5 X2 X3 X4 X5 X1) X4 X5) = (k1_bcialg_5 X1 (esk7_5 X2 X3 X4 X5 X1) (esk8_5 X2 X3 X4 X5 X1) X2 X3) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X4 k1_numbers k5_numbers -> m2_subset_1 X3 k1_numbers k5_numbers -> m2_subset_1 X2 k1_numbers k5_numbers -> False)
  -> (forall X6 X4 X2 X3 X5 X7 X1, ((k1_bcialg_5 X1 X6 X7 X2 X3) = (k1_bcialg_5 X1 X7 X6 X4 X5) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X4 k1_numbers k5_numbers -> m2_subset_1 X3 k1_numbers k5_numbers -> m2_subset_1 X2 k1_numbers k5_numbers -> m1_bcialg_5 X1 X2 X3 X4 X5 -> False)
  -> (forall X3 X2 X1 X4 X5, (v2_struct_0 X5 -> False) -> (m1_bcialg_5 X5 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk8_5 X1 X2 X3 X4 X5) (u1_struct_0 X5) -> False) -> v3_bcialg_1 X5 -> v4_bcialg_1 X5 -> v5_bcialg_1 X5 -> v7_bcialg_1 X5 -> l2_bcialg_1 X5 -> m2_subset_1 X4 k1_numbers k5_numbers -> m2_subset_1 X3 k1_numbers k5_numbers -> m2_subset_1 X2 k1_numbers k5_numbers -> m2_subset_1 X1 k1_numbers k5_numbers -> False)
  -> (forall X3 X2 X1 X4 X5, (v2_struct_0 X5 -> False) -> (m1_bcialg_5 X5 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk7_5 X1 X2 X3 X4 X5) (u1_struct_0 X5) -> False) -> v3_bcialg_1 X5 -> v4_bcialg_1 X5 -> v5_bcialg_1 X5 -> v7_bcialg_1 X5 -> l2_bcialg_1 X5 -> m2_subset_1 X4 k1_numbers k5_numbers -> m2_subset_1 X3 k1_numbers k5_numbers -> m2_subset_1 X2 k1_numbers k5_numbers -> m2_subset_1 X1 k1_numbers k5_numbers -> False)
  -> (forall X4 X5 X2 X3 X1, ((k1_bcialg_2 X1 (k1_bcialg_2 X1 X2 (k1_bcialg_1 X1 X2 X3) (k2_nat_1 X4 np__1)) (k1_bcialg_1 X1 X3 X2) X5) = (k1_bcialg_5 X1 X2 X3 X4 X5) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X4 k1_numbers k5_numbers -> False)
  -> (forall X4 X3 X2 X5 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k1_bcialg_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X5 X3 X2 X4 X1, v2_struct_0 X1 -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_bcialg_5 X1 X2 X3 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (l2_bcialg_1 X1 -> False) -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_bcialg_5 X1 X2 X3 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_bcialg_1 X1 -> False) -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_bcialg_5 X1 X2 X3 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v5_bcialg_1 X1 -> False) -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_bcialg_5 X1 X2 X3 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v4_bcialg_1 X1 -> False) -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_bcialg_5 X1 X2 X3 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v3_bcialg_1 X1 -> False) -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_bcialg_5 X1 X2 X3 X4 X5 -> False)
  -> (forall X3 X2 X1 X4, (m1_bcialg_5 (esk13_4 X1 X2 X3 X4) X1 X2 X3 X4 -> False) -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X5 X2 X3 X4 X6 X1, ((k1_bcialg_2 X1 (k1_bcialg_2 X1 X2 X3 X5) X4 X6) = (k1_bcialg_2 X1 (k1_bcialg_2 X1 X2 X4 X6) X3 X5) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X6 k5_numbers -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X5 X1, ((k1_bcialg_2 X1 (k1_bcialg_2 X1 X2 X3 X4) X3 X5) = (k1_bcialg_2 X1 X2 X3 (k2_nat_1 X4 X5)) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k1_bcialg_2 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X4 k5_numbers -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k5_binop_1 (u1_struct_0 X1) (u1_bcialg_1 X1) X2 X3) = (k1_bcialg_1 X1 X2 X3) -> False) -> l1_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (m1_subset_1 (u1_bcialg_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1))) -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k1_bcialg_1 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v1_funct_2 (u1_bcialg_1 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk15_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m2_subset_1 (k2_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_nat_1 X2 X1) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk21_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, v3_xxreal_0 X1 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk20_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_funct_1 (u1_bcialg_1 X1) -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (l2_struct_0 X1 -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (l1_bcialg_1 X1 -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (m1_bcialg_5 esk5_0 (k2_nat_1 esk1_0 esk6_0) esk2_0 esk3_0 (k2_nat_1 esk4_0 esk6_0) -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk32_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (v2_struct_0 esk19_0 -> False)
  -> ((m1_bcialg_5 esk5_0 esk1_0 esk2_0 esk3_0 esk4_0 -> False) -> False)
  -> ((m2_subset_1 esk6_0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 esk4_0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 esk3_0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 esk2_0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 esk1_0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk22_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((l2_struct_0 esk19_0 -> False) -> False)
  -> ((l2_struct_0 esk12_0 -> False) -> False)
  -> ((l2_bcialg_1 esk11_0 -> False) -> False)
  -> ((l1_bcialg_1 esk9_0 -> False) -> False)
  -> ((v2_xxreal_0 esk25_0 -> False) -> False)
  -> ((v2_xxreal_0 esk24_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xcmplx_0 esk30_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk26_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk24_0 -> False) -> False)
  -> ((v1_xboole_0 esk31_0 -> False) -> False)
  -> ((v1_xboole_0 esk30_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xxreal_0 esk31_0 -> False) -> False)
  -> ((v1_xxreal_0 esk30_0 -> False) -> False)
  -> ((v1_xxreal_0 esk27_0 -> False) -> False)
  -> ((v1_xxreal_0 esk26_0 -> False) -> False)
  -> ((v1_xxreal_0 esk25_0 -> False) -> False)
  -> ((v1_xxreal_0 esk24_0 -> False) -> False)
  -> ((v1_xxreal_0 esk18_0 -> False) -> False)
  -> ((v3_xxreal_0 esk27_0 -> False) -> False)
  -> ((v3_xxreal_0 esk26_0 -> False) -> False)
  -> ((v1_xreal_0 esk30_0 -> False) -> False)
  -> ((v1_xreal_0 esk26_0 -> False) -> False)
  -> ((v1_xreal_0 esk24_0 -> False) -> False)
  -> ((v1_xreal_0 esk17_0 -> False) -> False)
  -> ((v2_ordinal1 esk23_0 -> False) -> False)
  -> ((v1_ordinal1 esk23_0 -> False) -> False)
  -> ((v3_ordinal1 esk23_0 -> False) -> False)
  -> ((v3_ordinal1 esk22_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v7_ordinal1 esk32_0 -> False) -> False)
  -> ((v7_ordinal1 esk28_0 -> False) -> False)
  -> ((v7_struct_0 esk19_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((k1_xboole_0 = o_0_0_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
