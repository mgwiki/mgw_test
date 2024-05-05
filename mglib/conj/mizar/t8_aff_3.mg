(** $I sig/MizarPreamble.mgs **)

Theorem t8_aff_3:
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v1_aff_1:set -> set -> prop,
 forall r5_aff_1:set -> set -> set -> prop,
 forall epred1_10:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> prop,
 forall esk29_10:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall esk28_10:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk5_1:set -> set,
 forall esk9_1:set -> set,
 forall esk8_1:set -> set,
 forall esk3_1:set -> set,
 forall esk4_1:set -> set,
 forall esk2_1:set -> set,
 forall esk7_1:set -> set,
 forall esk10_1:set -> set,
 forall esk6_1:set -> set,
 forall v6_aff_3:set -> prop,
 forall r3_aff_1:set -> set -> set -> prop,
 forall esk27_4:set -> set -> set -> set -> set,
 forall k2_aff_1:set -> set -> set -> set,
 forall k1_aff_1:set -> set -> set -> set,
 forall esk24_1:set -> set,
 forall k1_xboole_0:set,
 forall v1_xboole_0:set -> prop,
 forall esk1_0:set,
 forall esk22_0:set,
 forall esk21_0:set,
 forall esk23_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk25_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk26_1:set -> set,
 forall v2_struct_0:set -> prop,
 forall v8_aff_3:set -> prop,
 forall v2_diraf:set -> prop,
 forall esk13_1:set -> set,
 forall esk18_1:set -> set,
 forall esk20_1:set -> set,
 forall esk16_1:set -> set,
 forall esk14_1:set -> set,
 forall esk12_1:set -> set,
 forall esk15_1:set -> set,
 forall esk19_1:set -> set,
 forall esk17_1:set -> set,
 forall esk11_1:set -> set,
 forall l1_analoaf:set -> prop,
 forall v1_diraf:set -> prop,
 forall v7_struct_0:set -> prop,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
 forall esk30_11:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall epred2_11:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> prop,
     (forall X1 X3 X6 X7 X9 X11 X10 X8 X5 X4 X2, (epred2_11 X1 X11 X9 X7 X3 X6 X4 X5 X8 X2 X10 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk30_11 X5 X2 X4 X6 X3 X7 X8 X9 X10 X11 X1) -> False) -> False)
  -> (forall X1 X3 X4 X6 X7 X8 X10 X11 X9 X5 X2, (epred2_11 X1 X11 X9 X2 X7 X3 X6 X4 X8 X5 X10 -> False) -> (r1_aff_1 X1 X2 X3 (esk30_11 X4 X5 X6 X3 X7 X2 X8 X9 X10 X11 X1) -> False) -> False)
  -> (forall X1 X3 X4 X6 X10 X11 X9 X8 X7 X5 X2, (epred2_11 X1 X11 X9 X8 X3 X7 X6 X4 X2 X5 X10 -> False) -> (r1_aff_1 X1 X2 X3 (esk30_11 X4 X5 X6 X7 X3 X8 X2 X9 X10 X11 X1) -> False) -> False)
  -> (forall X11 X2 X4 X6 X8 X10 X9 X7 X5 X3 X1, (epred2_11 X11 X10 X8 X6 X5 X4 X3 X1 X7 X2 X9 -> False) -> (m1_subset_1 (esk30_11 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11) (u1_struct_0 X11) -> False) -> False)
  -> (forall X1 X3 X4 X6 X8 X11 X10 X9 X7 X5 X2, (epred2_11 X11 X10 X8 X6 X5 X4 X1 X2 X7 X3 X9 -> False) -> (esk30_11 X2 X3 X1 X4 X5 X6 X7 X8 X9 X10 X11) = X1 -> False)
  -> (forall X6 X5 X2 X1 X8 X4 X9 X10 X3 X11 X7 X12, (X7 = X12 -> False) -> (X5 = X6 -> False) -> (X3 = X11 -> False) -> (X2 = X11 -> False) -> (X2 = X3 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> (r1_aff_1 X1 X9 X10 X5 -> False) -> (r1_aff_1 X1 X4 X8 X6 -> False) -> r2_hidden X10 X2 -> r2_hidden X9 X11 -> r2_hidden X8 X2 -> r2_hidden X6 X3 -> r2_hidden X5 X3 -> r2_hidden X4 X11 -> v1_aff_1 X11 X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> r5_aff_1 X1 X2 X11 -> m1_subset_1 X12 (u1_struct_0 X1) -> r1_aff_1 X1 X9 X10 X7 -> r1_aff_1 X1 X9 X5 X12 -> r1_aff_1 X1 X4 X8 X7 -> r1_aff_1 X1 X4 X6 X12 -> r2_analoaf X1 X10 X5 X8 X6 -> r2_analoaf X1 X10 X5 X7 X12 -> epred2_11 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> epred2_11 X1 (esk11_1 X1) (esk13_1 X1) (esk17_1 X1) (esk18_1 X1) (esk19_1 X1) (esk20_1 X1) (esk15_1 X1) (esk16_1 X1) (esk14_1 X1) (esk12_1 X1) -> False)
  -> (forall X1 X3 X4 X6 X7 X10 X9 X8 X5 X2, (epred1_10 X1 X2 X8 X3 X6 X7 X5 X4 X9 X10 -> False) -> (r2_analoaf X1 X2 X3 (esk28_10 X4 X5 X6 X3 X7 X8 X2 X9 X10 X1) (esk29_10 X4 X5 X6 X3 X7 X8 X2 X9 X10 X1) -> False) -> False)
  -> (forall X6 X8 X11 X10 X9 X7 X2 X5 X4 X3 X1, (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (epred2_11 X1 X6 X7 X8 X3 X5 X9 X4 X10 X2 X11 -> False) -> False)
  -> (forall X11 X9 X7 X5 X2 X3 X4 X6 X8 X10 X1, (v7_struct_0 X1 -> False) -> (epred2_11 X1 X2 X4 X8 X9 X10 X11 X6 X7 X5 X3 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v8_aff_3 X1 -> m1_subset_1 X11 (u1_struct_0 X1) -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X6 X7 X8 X9 X10 X11 X5 X1 X4 X3 X2, (epred2_11 X1 X5 X6 X2 X7 X4 X8 X3 X9 X10 X11 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X6 X9 X11 X10 X8 X7 X5 X1 X4 X3 X2, (epred2_11 X1 X5 X6 X7 X4 X8 X9 X10 X2 X3 X11 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X5 X8 X11 X10 X9 X7 X6 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred2_11 X1 X5 X6 X2 X7 X8 X4 X3 X9 X10 X11 -> False) -> False)
  -> (forall X5 X7 X9 X10 X11 X8 X6 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred2_11 X1 X5 X6 X7 X8 X9 X4 X10 X2 X3 X11 -> False) -> False)
  -> (forall X5 X7 X9 X10 X11 X8 X6 X4 X1 X2 X3, (epred2_11 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 -> False) -> r5_aff_1 X1 X2 X3 -> False)
  -> (forall X5 X7 X9 X11 X10 X8 X6 X4 X3 X2 X1, (r5_aff_1 X1 X2 X3 -> False) -> (epred2_11 X1 X2 X4 X5 X6 X7 X8 X9 X10 X11 X3 -> False) -> False)
  -> (forall X4 X6 X8 X11 X10 X9 X7 X5 X3 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_11 X2 X1 X3 X4 X5 X6 X7 X8 X9 X10 X11 -> False) -> False)
  -> (forall X3 X4 X6 X8 X11 X10 X9 X7 X5 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_11 X2 X3 X1 X4 X5 X6 X7 X8 X9 X10 X11 -> False) -> False)
  -> (forall X3 X5 X7 X9 X11 X10 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_11 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X1 -> False) -> False)
  -> (forall X5 X7 X11 X10 X9 X8 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_11 X3 X2 X4 X5 X6 X7 X8 X1 X9 X10 X11 -> False) -> False)
  -> (forall X5 X7 X9 X11 X10 X8 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_11 X3 X2 X4 X5 X6 X7 X8 X9 X10 X1 X11 -> False) -> False)
  -> (forall X4 X5 X6 X8 X11 X10 X9 X7 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_11 X3 X4 X2 X5 X1 X6 X7 X8 X9 X10 X11 -> False) -> False)
  -> (forall X4 X5 X8 X11 X10 X9 X7 X6 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_11 X3 X4 X2 X5 X6 X1 X7 X8 X9 X10 X11 -> False) -> False)
  -> (forall X4 X7 X9 X11 X10 X8 X6 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_11 X3 X4 X5 X1 X6 X7 X8 X9 X10 X11 X2 -> False) -> False)
  -> (forall X4 X6 X8 X10 X11 X9 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_11 X3 X4 X5 X6 X7 X8 X9 X10 X1 X11 X2 -> False) -> False)
  -> (forall X3 X5 X7 X9 X10 X11 X8 X6 X4 X2 X1, (epred2_11 X3 X1 X2 X4 X5 X6 X7 X8 X9 X10 X11 -> False) -> X1 = X2 -> False)
  -> (forall X3 X4 X6 X8 X10 X11 X9 X7 X5 X2 X1, (epred2_11 X3 X1 X4 X5 X6 X7 X8 X9 X10 X11 X2 -> False) -> X1 = X2 -> False)
  -> (forall X3 X6 X8 X10 X11 X9 X7 X5 X4 X2 X1, (epred2_11 X3 X4 X2 X5 X6 X7 X8 X9 X10 X11 X1 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X10 X11 X8 X6 X4 X2 X1, (epred2_11 X3 X4 X5 X6 X1 X2 X7 X8 X9 X10 X11 -> False) -> X1 = X2 -> False)
  -> (forall X2 X4 X6 X8 X9 X10 X7 X5 X3 X1, (epred1_10 X10 X7 X6 X4 X3 X5 X2 X1 X8 X9 -> False) -> (esk29_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = (esk28_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) -> False)
  -> (forall X1 X3 X4 X5 X7 X10 X9 X8 X6 X2, (epred1_10 X1 X3 X8 X6 X5 X7 X2 X4 X9 X10 -> False) -> (r1_aff_1 X1 X2 X3 (esk28_10 X4 X2 X5 X6 X7 X8 X3 X9 X10 X1) -> False) -> False)
  -> (forall X1 X3 X4 X6 X8 X10 X9 X7 X5 X2, (epred1_10 X1 X8 X3 X7 X6 X2 X5 X4 X9 X10 -> False) -> (r1_aff_1 X1 X2 X3 (esk28_10 X4 X5 X6 X7 X2 X3 X8 X9 X10 X1) -> False) -> False)
  -> (forall X1 X3 X4 X5 X6 X8 X10 X9 X7 X2, (epred1_10 X1 X8 X7 X3 X5 X6 X2 X4 X9 X10 -> False) -> (r1_aff_1 X1 X2 X3 (esk29_10 X4 X2 X5 X3 X6 X7 X8 X9 X10 X1) -> False) -> False)
  -> (forall X1 X3 X4 X8 X10 X9 X7 X6 X5 X2, (epred1_10 X1 X8 X7 X6 X3 X2 X5 X4 X9 X10 -> False) -> (r1_aff_1 X1 X2 X3 (esk29_10 X4 X5 X3 X6 X2 X7 X8 X9 X10 X1) -> False) -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (epred1_10 X10 X7 X6 X4 X3 X5 X2 X1 X8 X9 -> False) -> (m1_subset_1 (esk29_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) (u1_struct_0 X10) -> False) -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (epred1_10 X10 X7 X6 X4 X3 X5 X2 X1 X8 X9 -> False) -> (m1_subset_1 (esk28_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) (u1_struct_0 X10) -> False) -> False)
  -> (forall X10 X9 X5 X3 X6 X7 X2 X4 X1 X8 X11 X12, (X11 = X12 -> False) -> (X9 = X10 -> False) -> (X8 = X10 -> False) -> (X8 = X9 -> False) -> (r1_aff_1 X1 X7 X2 X4 -> False) -> (r1_aff_1 X1 X6 X3 X5 -> False) -> (r2_analoaf X1 X2 X4 X3 X5 -> False) -> r2_hidden X7 X8 -> r2_hidden X6 X8 -> r2_hidden X5 X9 -> r2_hidden X4 X9 -> r2_hidden X3 X10 -> r2_hidden X2 X10 -> v1_aff_1 X10 X1 -> v1_aff_1 X9 X1 -> v1_aff_1 X8 X1 -> r5_aff_1 X1 X10 X9 -> r5_aff_1 X1 X10 X8 -> m1_subset_1 X12 (u1_struct_0 X1) -> m1_subset_1 X11 (u1_struct_0 X1) -> r1_aff_1 X1 X7 X4 X12 -> r1_aff_1 X1 X7 X2 X11 -> r1_aff_1 X1 X6 X5 X12 -> r1_aff_1 X1 X6 X3 X11 -> r2_analoaf X1 X2 X4 X11 X12 -> epred1_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> epred1_10 X1 (esk5_1 X1) (esk6_1 X1) (esk9_1 X1) (esk10_1 X1) (esk8_1 X1) (esk7_1 X1) (esk3_1 X1) (esk4_1 X1) (esk2_1 X1) -> False)
  -> (forall X7 X10 X9 X8 X6 X1 X3 X4 X5 X2, (epred1_10 X1 X2 X4 X3 X5 X6 X7 X8 X9 X10 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X5 X6 X10 X9 X8 X7 X1 X4 X3 X2, (epred1_10 X1 X3 X5 X4 X6 X7 X2 X8 X9 X10 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X7 X10 X9 X8 X6 X5 X1 X4 X3 X2, (epred1_10 X1 X5 X3 X6 X4 X2 X7 X8 X9 X10 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X10 X8 X6 X4 X3 X2 X5 X7 X9 X1, (v7_struct_0 X1 -> False) -> (epred1_10 X1 X5 X6 X9 X10 X8 X7 X3 X4 X2 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v6_aff_3 X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X6 X8 X10 X9 X7 X5 X3 X2 X1, (r5_aff_1 X1 X2 X3 -> False) -> (epred1_10 X1 X4 X5 X6 X7 X8 X9 X3 X10 X2 -> False) -> False)
  -> (forall X4 X6 X8 X10 X9 X7 X5 X3 X2 X1, (r5_aff_1 X1 X2 X3 -> False) -> (epred1_10 X1 X4 X5 X6 X7 X8 X9 X10 X3 X2 -> False) -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_10 X2 X3 X4 X5 X6 X7 X8 X1 X9 X10 -> False) -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_10 X2 X3 X4 X5 X6 X7 X8 X9 X1 X10 -> False) -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_10 X2 X3 X4 X5 X6 X7 X8 X9 X10 X1 -> False) -> False)
  -> (forall X5 X7 X9 X10 X8 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_10 X3 X1 X4 X5 X6 X7 X8 X9 X10 X2 -> False) -> False)
  -> (forall X4 X5 X7 X9 X10 X8 X6 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_10 X3 X4 X1 X5 X6 X7 X8 X9 X10 X2 -> False) -> False)
  -> (forall X4 X7 X9 X10 X8 X6 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_10 X3 X4 X5 X1 X6 X7 X8 X9 X2 X10 -> False) -> False)
  -> (forall X4 X6 X7 X9 X10 X8 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_10 X3 X4 X5 X6 X1 X7 X8 X9 X2 X10 -> False) -> False)
  -> (forall X4 X6 X9 X10 X8 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_10 X3 X4 X5 X6 X7 X1 X8 X2 X9 X10 -> False) -> False)
  -> (forall X4 X6 X8 X9 X10 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_10 X3 X4 X5 X6 X7 X8 X1 X2 X9 X10 -> False) -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X2 X1, (epred1_10 X3 X4 X5 X6 X7 X8 X9 X1 X2 X10 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X2 X1, (epred1_10 X3 X4 X5 X6 X7 X8 X9 X2 X10 X1 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X2 X1, (epred1_10 X3 X4 X5 X6 X7 X8 X9 X10 X2 X1 -> False) -> X1 = X2 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X2 X3 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X4 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X3 X2 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X3 X2 -> False)
  -> (forall X3 X2 X6 X7 X1 X4 X5, (X4 = X5 -> False) -> (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X7 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X6 -> v1_aff_1 X7 X1 -> v1_aff_1 X6 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X4 X5 -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X2 X4 -> False)
  -> (forall X1 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden X5 X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X4 X6 -> r2_hidden X3 X6 -> r2_hidden X2 X6 -> v1_aff_1 X6 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X4 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X5 X4 X2 X3 X1 X6 X7, (X6 = X7 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X7 X3 -> r2_hidden X6 X3 -> r2_hidden X5 X2 -> r2_hidden X4 X2 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X5 X2 X6 X7 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X7 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X6 -> r3_aff_1 X1 X6 X7 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X4 X5 X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X6 -> r1_aff_1 X1 X2 X3 X5 -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X3 X4 X5 X2 X6 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X6 -> r2_hidden X4 X6 -> r2_hidden X3 X6 -> r2_hidden X2 X6 -> v1_aff_1 X6 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk27_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (v1_aff_1 (esk27_4 X1 X2 X3 X4) X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk27_4 X2 X1 X3 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X1 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk27_4 X2 X3 X1 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X1 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk27_4 X2 X3 X4 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X4 X1 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X3 X2 -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X5 -> r2_hidden X2 X5 -> v1_aff_1 X5 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X5 X4 X3 X1 X2, (v7_struct_0 X2 -> False) -> (r1_aff_1 X2 X3 X4 X5 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r2_hidden X5 X1 -> r2_hidden X4 X1 -> r2_hidden X3 X1 -> v1_aff_1 X1 X2 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X4 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X3 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X4 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X4 X3 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X4 X2 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1 X4 X5, (X4 = X5 -> False) -> (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X5 -> r2_hidden X3 X4 -> r2_hidden X2 X5 -> r2_hidden X2 X4 -> v1_aff_1 X5 X1 -> v1_aff_1 X4 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X2 X4 -> r2_hidden X2 X3 -> r5_aff_1 X1 X3 X4 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X3 X4, (X3 = X4 -> False) -> (X1 = (k2_aff_1 X2 X3 X4) -> False) -> (v7_struct_0 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r2_hidden X4 X1 -> r2_hidden X3 X1 -> v1_aff_1 X1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X4 X2 X1 X3, (X1 = X3 -> False) -> (v7_struct_0 X4 -> False) -> (r2_hidden X1 X2 -> False) -> X2 = (k2_aff_1 X4 X1 X3) -> v1_diraf X4 -> l1_analoaf X4 -> m1_subset_1 X3 (u1_struct_0 X4) -> m1_subset_1 X1 (u1_struct_0 X4) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X4)) -> False)
  -> (forall X4 X2 X1 X3, (X1 = X3 -> False) -> (v7_struct_0 X4 -> False) -> (r2_hidden X1 X2 -> False) -> X2 = (k2_aff_1 X4 X3 X1) -> v1_diraf X4 -> l1_analoaf X4 -> m1_subset_1 X3 (u1_struct_0 X4) -> m1_subset_1 X1 (u1_struct_0 X4) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X4)) -> False)
  -> (forall X2 X1 X3 X4, (X3 = X4 -> False) -> (v7_struct_0 X2 -> False) -> (v1_aff_1 X1 X2 -> False) -> X1 = (k2_aff_1 X2 X3 X4) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k1_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k2_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k1_aff_1 X1 X2 X3) = (k2_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k2_aff_1 X1 X2 X3) = (k2_aff_1 X1 X3 X2) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk3_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk2_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v8_aff_3 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk25_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk24_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (v6_aff_3 esk1_0 -> v8_aff_3 esk1_0 -> False)
  -> ((v6_aff_3 esk1_0 -> False) -> (v8_aff_3 esk1_0 -> False) -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) X1 -> False) -> False)
  -> ((l1_struct_0 esk22_0 -> False) -> False)
  -> ((l1_analoaf esk21_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v2_diraf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
