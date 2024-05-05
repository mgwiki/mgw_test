(** $I sig/MizarPreamble.mgs **)

Theorem t26_geomtrap:
 forall r1_analmetr:set -> set -> set -> prop,
 forall r1_geomtrap:set -> set -> set -> set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk19_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall v4_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v6_membered:set -> prop,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall v1_int_1:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall k1_xboole_0:set,
 forall k5_numbers:set,
 forall esk27_1:set -> set,
 forall esk25_1:set -> set,
 forall l2_algstr_0:set -> prop,
 forall l2_struct_0:set -> prop,
 forall l1_algstr_0:set -> prop,
 forall esk23_1:set -> set,
 forall esk22_0:set,
 forall esk15_0:set,
 forall esk17_0:set,
 forall esk21_1:set -> set,
 forall k4_ordinal1:set,
 forall v2_xxreal_0:set -> prop,
 forall esk12_0:set,
 forall esk8_0:set,
 forall esk10_0:set,
 forall esk9_0:set,
 forall esk11_0:set,
 forall esk13_1:set -> set,
 forall esk20_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk7_0:set,
 forall esk6_0:set,
 forall esk5_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall v7_membered:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk16_1:set -> set,
 forall esk26_1:set -> set,
 forall k1_numbers:set,
 forall v1_xxreal_0:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_membered:set -> prop,
 forall v3_membered:set -> prop,
 forall v5_membered:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk24_1:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk14_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall r2_geomtrap:set -> set -> set -> set -> set -> set -> set -> prop,
 forall v2_rlvect_1:set -> prop,
 forall v4_rlvect_1:set -> prop,
 forall v6_rlvect_1:set -> prop,
 forall v8_rlvect_1:set -> prop,
 forall u1_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall r1_analoaf:set -> set -> set -> set -> set -> prop,
 forall k1_geomtrap:set -> set -> set -> set,
 forall r3_analmetr:set -> set -> set -> set -> set -> set -> set -> prop,
 forall l1_rlvect_1:set -> prop,
 forall v7_rlvect_1:set -> prop,
 forall v5_rlvect_1:set -> prop,
 forall v3_rlvect_1:set -> prop,
 forall v13_algstr_0:set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X6 X4 X2 X3 X5 X7 X1, (v2_struct_0 X1 -> False) -> (r2_geomtrap X1 X6 X7 X2 X3 X4 X5 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_analoaf X1 X2 X3 X4 X5 -> r3_analmetr X1 X4 X5 (k1_geomtrap X1 X2 X3) (k1_geomtrap X1 X4 X5) X6 X7 -> r3_analmetr X1 X2 X3 (k1_geomtrap X1 X2 X3) (k1_geomtrap X1 X4 X5) X6 X7 -> False)
  -> (forall X1 X2 X4 X7 X6 X5 X3 X8 X9, (X8 = X9 -> False) -> (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 X4 X5 X6 X7 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> r1_analmetr X1 X6 X7 -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_geomtrap X1 X2 X3 X8 X9 -> r3_analmetr X1 X4 X5 X8 X9 X6 X7 -> False)
  -> (forall X1 X2 X4 X7 X6 X5 X3 X8 X9, (X8 = X9 -> False) -> (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 X4 X5 X6 X7 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> r1_analmetr X1 X6 X7 -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_geomtrap X1 X2 X3 X8 X9 -> r3_analmetr X1 X8 X9 X4 X5 X6 X7 -> False)
  -> (forall X1 X2 X4 X7 X6 X5 X3 X8 X9, (X8 = X9 -> False) -> (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 X4 X5 X6 X7 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> r1_analmetr X1 X6 X7 -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_geomtrap X1 X4 X5 X8 X9 -> r3_analmetr X1 X2 X3 X8 X9 X6 X7 -> False)
  -> (forall X1 X2 X4 X7 X6 X5 X3 X8 X9, (X8 = X9 -> False) -> (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 X4 X5 X6 X7 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> r1_analmetr X1 X6 X7 -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_geomtrap X1 X4 X5 X8 X9 -> r3_analmetr X1 X8 X9 X2 X3 X6 X7 -> False)
  -> (forall X1 X2 X4 X7 X6 X5 X3 X8 X9, (X8 = X9 -> False) -> (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 X4 X5 X6 X7 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> r1_analmetr X1 X6 X7 -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_geomtrap X1 X8 X9 X2 X3 -> r3_analmetr X1 X4 X5 X8 X9 X6 X7 -> False)
  -> (forall X1 X2 X4 X7 X6 X5 X3 X8 X9, (X8 = X9 -> False) -> (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 X4 X5 X6 X7 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> r1_analmetr X1 X6 X7 -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_geomtrap X1 X8 X9 X2 X3 -> r3_analmetr X1 X8 X9 X4 X5 X6 X7 -> False)
  -> (forall X1 X2 X4 X7 X6 X5 X3 X8 X9, (X8 = X9 -> False) -> (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 X4 X5 X6 X7 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> r1_analmetr X1 X6 X7 -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_geomtrap X1 X8 X9 X4 X5 -> r3_analmetr X1 X2 X3 X8 X9 X6 X7 -> False)
  -> (forall X1 X2 X4 X7 X6 X5 X3 X8 X9, (X8 = X9 -> False) -> (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 X4 X5 X6 X7 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> r1_analmetr X1 X6 X7 -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_geomtrap X1 X8 X9 X4 X5 -> r3_analmetr X1 X8 X9 X2 X3 X6 X7 -> False)
  -> (forall X6 X4 X2 X3 X5 X7 X1, (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 (k1_geomtrap X1 X2 X3) (k1_geomtrap X1 X4 X5) X6 X7 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_geomtrap X1 X6 X7 X2 X3 X4 X5 -> False)
  -> (forall X6 X4 X2 X3 X5 X7 X1, (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 (k1_geomtrap X1 X4 X5) (k1_geomtrap X1 X2 X3) X6 X7 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_geomtrap X1 X6 X7 X4 X5 X2 X3 -> False)
  -> (forall X3 X4 X5 X2 X7 X6 X1, (v2_struct_0 X1 -> False) -> (r1_analoaf X1 X2 X3 X4 X5 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_geomtrap X1 X6 X7 X2 X3 X4 X5 -> False)
  -> (forall X4 X3 X2 X6 X5 X1, (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X2 X3 X4 X5 X6 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> r1_analmetr X1 X5 X6 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X6 X5 X1, (v2_struct_0 X1 -> False) -> (r3_analmetr X1 X2 X3 X4 X4 X5 X6 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> r1_analmetr X1 X5 X6 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r1_analoaf X1 X2 X3 X5 X4 -> False) -> (r1_analoaf X1 X2 X3 X4 X5 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_geomtrap X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r1_analoaf X1 X2 X3 (k1_geomtrap X1 X2 X4) (k1_geomtrap X1 X3 X5) -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r1_analoaf X1 X2 X3 X4 X5 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_analoaf X1 X3 X2 X5 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r1_analoaf X1 X2 X3 X4 X5 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_analoaf X1 X4 X5 X2 X3 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r1_geomtrap X1 X2 X3 X4 X5 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r1_geomtrap X1 X2 X3 X5 X4 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_analoaf X1 X2 X3 (k1_geomtrap X1 X2 X3) X3 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_analoaf X1 X2 X3 X2 (k1_geomtrap X1 X2 X3) -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X5 X1, ((k1_geomtrap X1 (k1_geomtrap X1 X2 X3) (k1_geomtrap X1 X4 X5)) = (k1_geomtrap X1 (k1_geomtrap X1 X2 X4) (k1_geomtrap X1 X3 X5)) -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k1_geomtrap X1 X2 X3) (u1_struct_0 X1) -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k1_geomtrap X1 X2 X3) = (k1_geomtrap X1 X3 X2) -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, ((k1_geomtrap X1 X2 X2) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> v5_rlvect_1 X1 -> v6_rlvect_1 X1 -> v7_rlvect_1 X1 -> v8_rlvect_1 X1 -> l1_rlvect_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk14_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk19_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk25_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk18_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk27_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (l2_struct_0 X1 -> False) -> l2_algstr_0 X1 -> False)
  -> (forall X1, (l2_algstr_0 X1 -> False) -> l1_rlvect_1 X1 -> False)
  -> (forall X1, (l1_algstr_0 X1 -> False) -> l2_algstr_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_algstr_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_geomtrap esk1_0 esk2_0 esk3_0 esk4_0 esk5_0 (k1_geomtrap esk1_0 esk4_0 esk6_0) (k1_geomtrap esk1_0 esk5_0 esk7_0) -> False)
  -> (forall X1, v1_subset_1 (esk23_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk17_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> ((r2_geomtrap esk1_0 esk2_0 esk3_0 esk4_0 esk5_0 esk6_0 esk7_0 -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((r1_analmetr esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk7_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk21_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((l2_struct_0 esk17_0 -> False) -> False)
  -> ((l2_struct_0 esk12_0 -> False) -> False)
  -> ((l2_algstr_0 esk11_0 -> False) -> False)
  -> ((l1_algstr_0 esk8_0 -> False) -> False)
  -> ((v7_membered esk22_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v6_membered esk22_0 -> False) -> False)
  -> ((v6_membered esk20_0 -> False) -> False)
  -> ((v6_membered esk15_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> ((v7_struct_0 esk17_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((l1_rlvect_1 esk9_0 -> False) -> False)
  -> ((l1_rlvect_1 esk1_0 -> False) -> False)
  -> ((v8_rlvect_1 esk1_0 -> False) -> False)
  -> ((v7_rlvect_1 esk1_0 -> False) -> False)
  -> ((v6_rlvect_1 esk1_0 -> False) -> False)
  -> ((v5_rlvect_1 esk1_0 -> False) -> False)
  -> ((v4_rlvect_1 esk1_0 -> False) -> False)
  -> ((v3_rlvect_1 esk1_0 -> False) -> False)
  -> ((v2_rlvect_1 esk1_0 -> False) -> False)
  -> ((v13_algstr_0 esk1_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
