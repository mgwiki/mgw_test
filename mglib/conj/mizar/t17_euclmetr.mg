(** $I sig/MizarPreamble.mgs **)

Theorem t17_euclmetr:
 forall v2_struct_0:set -> prop,
 forall l1_analmetr:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall r10_analmetr:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v2_analmetr:set -> prop,
 forall v3_analmetr:set -> prop,
 forall r5_analmetr:set -> set -> set -> set -> prop,
 forall g1_analoaf:set -> set -> set,
 forall v1_analoaf:set -> prop,
 forall k3_analmetr:set -> set,
 forall r5_aff_1:set -> set -> set -> prop,
 forall r8_analmetr:set -> set -> set -> prop,
 forall r9_analmetr:set -> set -> set -> prop,
 forall k4_analmetr:set -> set -> set -> set,
 forall k2_aff_1:set -> set -> set -> set,
 forall esk25_3:set -> set -> set -> set,
 forall r3_aff_1:set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk12_2:set -> set -> set,
 forall esk22_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall k1_numbers:set,
 forall v1_xxreal_0:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall esk24_0:set,
 forall esk18_0:set,
 forall k5_numbers:set,
 forall esk14_0:set,
 forall v2_xxreal_0:set -> prop,
 forall esk20_0:set,
 forall esk15_0:set,
 forall esk9_0:set,
 forall esk8_0:set,
 forall esk10_0:set,
 forall esk13_0:set,
 forall esk21_0:set,
 forall esk23_0:set,
 forall esk11_1:set -> set,
 forall esk19_0:set,
 forall v5_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall k4_ordinal1:set,
 forall v7_ordinal1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk16_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk17_1:set -> set,
 forall esk7_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall k1_aff_1:set -> set -> set -> set,
 forall r7_analmetr:set -> set -> set -> prop,
 forall v2_diraf:set -> prop,
 forall v1_aff_1:set -> set -> prop,
 forall v1_diraf:set -> prop,
 forall esk26_3:set -> set -> set -> set,
 forall v7_struct_0:set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall u1_analoaf:set -> set,
 forall l1_analoaf:set -> prop,
 forall v4_analmetr:set -> set -> prop,
 forall r6_analmetr:set -> set -> set -> set -> prop,
 forall r4_analmetr:set -> set -> set -> set -> set -> prop,
 forall esk2_0:set,
 forall esk5_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall u1_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
     (forall X1, m1_subset_1 X1 (u1_struct_0 esk1_0) -> r4_analmetr esk1_0 esk2_0 esk5_0 esk2_0 X1 -> r4_analmetr esk1_0 esk3_0 esk5_0 esk4_0 X1 -> False)
  -> (forall X5 X6 X7 X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r4_analmetr X1 X4 X5 X6 X7 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r2_hidden X7 X3 -> r2_hidden X6 X3 -> r2_hidden X5 X2 -> r2_hidden X4 X2 -> r10_analmetr X1 X2 X3 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X5 X2 X1, (v2_struct_0 X1 -> False) -> (v4_analmetr X4 X1 -> False) -> l1_analmetr X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r6_analmetr X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X2 X5 X1, (v2_struct_0 X1 -> False) -> (r5_analmetr X1 X2 X3 X4 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> r2_hidden X4 X5 -> r2_hidden X3 X5 -> r2_hidden X2 X5 -> v4_analmetr X5 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (m1_subset_1 (u1_analoaf X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)))) -> False) -> l1_analoaf X1 -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_analoaf X1 X3) = (g1_analoaf X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_analoaf X3 X1) = (g1_analoaf X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X3) (k2_zfmisc_1 X3 X3))) -> False)
  -> (forall X1 X2, (v1_analoaf (g1_analoaf X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X1 X2, (l1_analoaf (g1_analoaf X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X4 X5 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r8_analmetr X1 X4 X5 -> False) -> X3 = X5 -> X2 = X4 -> l1_analmetr X1 -> v2_analmetr X1 -> r5_aff_1 (k3_analmetr X1) X2 X3 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X1))) -> False)
  -> (forall X4 X5 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r5_aff_1 (k3_analmetr X1) X4 X5 -> False) -> X3 = X5 -> X2 = X4 -> l1_analmetr X1 -> v2_analmetr X1 -> r8_analmetr X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X1))) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X1))) -> False)
  -> (forall X2 X4 X3 X1, (v2_struct_0 X1 -> False) -> (r9_analmetr X1 X2 X4 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> r10_analmetr X1 X4 X3 -> r10_analmetr X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X2 X1, (v2_struct_0 X1 -> False) -> (r10_analmetr X1 X4 X3 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r10_analmetr X1 X2 X3 -> r9_analmetr X1 X2 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X4 X3, (v2_struct_0 X3 -> False) -> (r5_analmetr X3 X1 X2 X4 -> False) -> X1 = X2 -> l1_analmetr X3 -> v2_analmetr X3 -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> False)
  -> (forall X2 X1 X4 X3, (v2_struct_0 X3 -> False) -> (r5_analmetr X3 X1 X4 X2 -> False) -> X1 = X2 -> l1_analmetr X3 -> v2_analmetr X3 -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> False)
  -> (forall X2 X1 X4 X3, (v2_struct_0 X3 -> False) -> (r5_analmetr X3 X4 X1 X2 -> False) -> X1 = X2 -> l1_analmetr X3 -> v2_analmetr X3 -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk26_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_analoaf X1 -> v1_diraf X1 -> v2_diraf X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> (r2_hidden (esk26_3 X1 X2 X3) X2 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> v2_diraf X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> (r2_hidden (esk26_3 X1 X2 X3) X3 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> v2_diraf X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X5 X3 X2 X4 X1, ((k4_analmetr X1 X2 X3) = (k2_aff_1 (k3_analmetr X1) X4 X5) -> False) -> (v2_struct_0 X1 -> False) -> X3 = X5 -> X2 = X4 -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X4 (u1_struct_0 (k3_analmetr X1)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (v7_struct_0 X1 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> r2_hidden X2 X4 -> r2_hidden X2 X3 -> r5_aff_1 X1 X3 X4 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r10_analmetr X1 X2 (esk25_3 X1 X2 X3) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> v4_analmetr X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X4 X5 X2, (v2_struct_0 X2 -> False) -> (v4_analmetr X1 X2 -> False) -> l1_analmetr X2 -> r7_analmetr X2 X1 X3 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X4 X5 X2, (v2_struct_0 X2 -> False) -> (v4_analmetr X1 X2 -> False) -> l1_analmetr X2 -> r7_analmetr X2 X3 X1 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk25_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> v4_analmetr X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X2 X3 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X2 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r8_analmetr X1 X2 X3 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r9_analmetr X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r9_analmetr X1 X2 X3 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r8_analmetr X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r9_analmetr X1 X3 X2 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r9_analmetr X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r7_analmetr X1 X2 X3 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r10_analmetr X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r10_analmetr X1 X2 X3 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r7_analmetr X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r10_analmetr X1 X3 X2 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r10_analmetr X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X1 (esk25_3 X2 X3 X1) -> False) -> v3_analmetr X2 -> l1_analmetr X2 -> v4_analmetr X3 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X4 X1 X3, (X1 = X3 -> False) -> (v2_struct_0 X2 -> False) -> (v4_analmetr X4 X2 -> False) -> X4 = (k4_analmetr X2 X1 X3) -> l1_analmetr X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k1_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k2_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k4_analmetr X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_analmetr X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (v4_analmetr X3 X2 -> False) -> X1 = X3 -> l1_analmetr X2 -> v2_analmetr X2 -> v1_aff_1 X1 (k3_analmetr X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X2))) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r10_analmetr X1 X2 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (v1_aff_1 X3 (k3_analmetr X2) -> False) -> X1 = X3 -> l1_analmetr X2 -> v2_analmetr X2 -> v4_analmetr X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X2))) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (k2_aff_1 X2 X1 X3) -> False) -> l1_analoaf X2 -> v1_diraf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (k2_aff_1 X2 X3 X1) -> False) -> l1_analoaf X2 -> v1_diraf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X2, ((k4_analmetr X2 (esk6_2 X2 X1) (esk7_2 X2 X1)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_analmetr X2 -> v4_analmetr X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, ((k1_aff_1 X1 X2 X3) = (k2_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k2_aff_1 X1 X2 X3) = (k2_aff_1 X1 X3 X2) -> False) -> (v7_struct_0 X1 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_analmetr X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X2))) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk7_2 X1 X2) (u1_struct_0 X1) -> False) -> l1_analmetr X1 -> v4_analmetr X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk6_2 X1 X2) (u1_struct_0 X1) -> False) -> l1_analmetr X1 -> v4_analmetr X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (esk7_2 X1 X2) = (esk6_2 X1 X2) -> l1_analmetr X1 -> v4_analmetr X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk12_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X2))) -> False) -> l1_analmetr X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 X1 (u1_struct_0 X2) -> False) -> l1_analmetr X2 -> m1_subset_1 X1 (u1_struct_0 (k3_analmetr X2)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 X1 (u1_struct_0 (k3_analmetr X2)) -> False) -> l1_analmetr X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_analoaf (u1_struct_0 X1) (u1_analoaf X1)) = X1 -> False) -> l1_analoaf X1 -> v1_analoaf X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> v7_struct_0 (k3_analmetr X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> v7_struct_0 (k3_analmetr X1) -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_diraf (k3_analmetr X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_diraf (k3_analmetr X1) -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_diraf (k3_analmetr X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_analoaf (k3_analmetr X1) -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_analoaf (k3_analmetr X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk17_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_analmetr X1 -> v2_struct_0 (k3_analmetr X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_analmetr X1 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk16_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_analoaf (k3_analmetr X1) -> False) -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_analoaf (k3_analmetr X1) -> False) -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (l1_analoaf (k3_analmetr X1) -> False) -> l1_analmetr X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_analoaf X1 -> False) -> l1_analmetr X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r5_analmetr esk1_0 esk2_0 esk3_0 esk5_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk18_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk14_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((v2_xxreal_0 esk20_0 -> False) -> False)
  -> ((v2_xxreal_0 esk14_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xxreal_0 esk23_0 -> False) -> False)
  -> ((v1_xxreal_0 esk20_0 -> False) -> False)
  -> ((v1_xxreal_0 esk14_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk23_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk20_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk23_0 -> False) -> False)
  -> ((v7_ordinal1 esk24_0 -> False) -> False)
  -> ((v7_ordinal1 esk21_0 -> False) -> False)
  -> ((v1_xreal_0 esk23_0 -> False) -> False)
  -> ((v1_xreal_0 esk20_0 -> False) -> False)
  -> ((v1_xreal_0 esk15_0 -> False) -> False)
  -> ((v1_xreal_0 esk14_0 -> False) -> False)
  -> ((v2_ordinal1 esk19_0 -> False) -> False)
  -> ((v1_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((l1_analoaf esk9_0 -> False) -> False)
  -> ((l1_analmetr esk18_0 -> False) -> False)
  -> ((l1_analmetr esk8_0 -> False) -> False)
  -> ((l1_analmetr esk1_0 -> False) -> False)
  -> ((v3_analmetr esk1_0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> False.
Admitted.
