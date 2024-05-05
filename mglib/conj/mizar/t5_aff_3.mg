(** $I sig/MizarPreamble.mgs **)

Theorem t5_aff_3:
 forall epred1_13:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> prop,
 forall esk7_1:set -> set,
 forall esk10_1:set -> set,
 forall esk12_1:set -> set,
 forall esk8_1:set -> set,
 forall esk4_1:set -> set,
 forall esk3_1:set -> set,
 forall esk2_1:set -> set,
 forall esk6_1:set -> set,
 forall esk13_1:set -> set,
 forall esk11_1:set -> set,
 forall esk9_1:set -> set,
 forall esk5_1:set -> set,
 forall v3_aff_3:set -> prop,
 forall esk32_4:set -> set -> set -> set -> set,
 forall r5_aff_1:set -> set -> set -> prop,
 forall esk33_3:set -> set -> set -> set,
 forall r3_aff_1:set -> set -> set -> prop,
 forall esk29_1:set -> set,
 forall k1_xboole_0:set,
 forall v1_xboole_0:set -> prop,
 forall esk1_0:set,
 forall esk28_1:set -> set,
 forall esk26_0:set,
 forall esk27_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk30_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk31_1:set -> set,
 forall v2_struct_0:set -> prop,
 forall k1_aff_1:set -> set -> set -> set,
 forall k2_aff_1:set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall v4_aff_3:set -> prop,
 forall v2_diraf:set -> prop,
 forall esk17_1:set -> set,
 forall esk19_1:set -> set,
 forall esk21_1:set -> set,
 forall esk24_1:set -> set,
 forall esk22_1:set -> set,
 forall esk14_1:set -> set,
 forall esk16_1:set -> set,
 forall esk15_1:set -> set,
 forall esk25_1:set -> set,
 forall esk23_1:set -> set,
 forall esk20_1:set -> set,
 forall esk18_1:set -> set,
 forall l1_analoaf:set -> prop,
 forall v1_diraf:set -> prop,
 forall v7_struct_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
 forall epred2_13:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> prop,
 forall v1_aff_1:set -> set -> prop,
 forall r1_aff_1:set -> set -> set -> set -> prop,
     (forall X10 X8 X7 X3 X2 X6 X12 X1 X9 X4 X5 X11 X13, (X11 = X13 -> False) -> (X10 = X13 -> False) -> (X10 = X11 -> False) -> (X7 = X8 -> False) -> (X4 = X5 -> False) -> (X2 = X3 -> False) -> (X1 = X9 -> False) -> (X1 = X4 -> False) -> (X1 = X2 -> False) -> (r2_hidden X1 X10 -> False) -> (r1_aff_1 X12 X5 X3 X6 -> False) -> (r1_aff_1 X12 X4 X2 X9 -> False) -> r2_hidden X9 X11 -> r2_hidden X6 X11 -> r2_hidden X5 X10 -> r2_hidden X4 X10 -> r2_hidden X3 X13 -> r2_hidden X2 X13 -> r2_hidden X1 X13 -> r2_hidden X1 X11 -> v1_aff_1 X13 X12 -> v1_aff_1 X11 X12 -> v1_aff_1 X10 X12 -> r1_aff_1 X12 X5 X6 X8 -> r1_aff_1 X12 X5 X3 X7 -> r1_aff_1 X12 X4 X9 X8 -> r1_aff_1 X12 X4 X2 X7 -> r2_analoaf X12 X2 X9 X7 X8 -> r2_analoaf X12 X2 X9 X3 X6 -> epred2_13 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 -> False)
  -> (forall X10 X7 X6 X9 X1 X11 X3 X2 X8 X4 X5 X12 X13, (X12 = X13 -> False) -> (X10 = X13 -> False) -> (X10 = X12 -> False) -> (X6 = X7 -> False) -> (X4 = X5 -> False) -> (X1 = X9 -> False) -> (X1 = X8 -> False) -> (X1 = X4 -> False) -> (r2_hidden X1 X10 -> False) -> (r1_aff_1 X11 X8 X9 X4 -> False) -> (r1_aff_1 X11 X3 X2 X5 -> False) -> r2_hidden X9 X12 -> r2_hidden X8 X13 -> r2_hidden X5 X10 -> r2_hidden X4 X10 -> r2_hidden X3 X13 -> r2_hidden X2 X12 -> r2_hidden X1 X13 -> r2_hidden X1 X12 -> v1_aff_1 X13 X11 -> v1_aff_1 X12 X11 -> v1_aff_1 X10 X11 -> r1_aff_1 X11 X8 X9 X6 -> r1_aff_1 X11 X8 X4 X7 -> r1_aff_1 X11 X3 X5 X7 -> r1_aff_1 X11 X3 X2 X6 -> r2_analoaf X11 X9 X4 X6 X7 -> r2_analoaf X11 X9 X4 X2 X5 -> epred1_13 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> epred2_13 (esk17_1 X1) (esk18_1 X1) (esk19_1 X1) (esk20_1 X1) (esk21_1 X1) (esk23_1 X1) (esk24_1 X1) (esk25_1 X1) (esk22_1 X1) (esk15_1 X1) (esk16_1 X1) X1 (esk14_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> epred1_13 (esk5_1 X1) (esk7_1 X1) (esk9_1 X1) (esk10_1 X1) (esk11_1 X1) (esk12_1 X1) (esk13_1 X1) (esk8_1 X1) (esk6_1 X1) (esk4_1 X1) X1 (esk2_1 X1) (esk3_1 X1) -> False)
  -> (forall X7 X10 X11 X13 X12 X9 X8 X6 X2 X5 X4 X3 X1, (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (epred2_13 X6 X2 X4 X7 X8 X5 X9 X10 X3 X11 X12 X1 X13 -> False) -> False)
  -> (forall X8 X10 X11 X13 X12 X9 X7 X6 X2 X5 X4 X3 X1, (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (epred2_13 X6 X2 X7 X8 X9 X10 X4 X5 X3 X11 X12 X1 X13 -> False) -> False)
  -> (forall X8 X10 X11 X13 X12 X9 X7 X6 X2 X5 X4 X3 X1, (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (epred1_13 X6 X4 X7 X3 X5 X8 X9 X10 X2 X11 X1 X12 X13 -> False) -> False)
  -> (forall X7 X10 X11 X13 X12 X9 X8 X6 X2 X5 X4 X3 X1, (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (epred1_13 X6 X7 X8 X3 X9 X4 X5 X10 X2 X11 X1 X12 X13 -> False) -> False)
  -> (forall X13 X11 X9 X7 X5 X2 X3 X4 X6 X8 X10 X12 X1, (v7_struct_0 X1 -> False) -> (epred2_13 X5 X6 X7 X8 X9 X11 X12 X13 X10 X3 X4 X1 X2 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v4_aff_3 X1 -> m1_subset_1 X13 (u1_struct_0 X1) -> m1_subset_1 X12 (u1_struct_0 X1) -> m1_subset_1 X11 (u1_struct_0 X1) -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X13 X11 X9 X7 X5 X2 X3 X4 X6 X8 X10 X12 X1, (v7_struct_0 X1 -> False) -> (epred1_13 X5 X7 X9 X10 X11 X12 X13 X8 X6 X4 X1 X2 X3 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v3_aff_3 X1 -> m1_subset_1 X13 (u1_struct_0 X1) -> m1_subset_1 X12 (u1_struct_0 X1) -> m1_subset_1 X11 (u1_struct_0 X1) -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X5 X6 X7 X9 X12 X13 X11 X10 X8 X1 X4 X3 X2, (epred2_13 X5 X3 X6 X2 X7 X8 X9 X10 X4 X11 X12 X1 X13 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X5 X8 X10 X12 X13 X11 X9 X7 X6 X1 X4 X3 X2, (epred2_13 X5 X6 X3 X7 X2 X4 X8 X9 X10 X11 X12 X1 X13 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X5 X8 X10 X12 X13 X11 X9 X7 X6 X1 X4 X3 X2, (epred1_13 X5 X3 X2 X6 X4 X7 X8 X9 X10 X11 X1 X12 X13 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X5 X7 X8 X10 X12 X13 X11 X9 X6 X1 X4 X3 X2, (epred1_13 X5 X6 X7 X4 X8 X9 X10 X2 X3 X11 X1 X12 X13 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X8 X9 X11 X13 X12 X10 X7 X6 X5 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred2_13 X5 X3 X6 X2 X7 X8 X4 X9 X10 X11 X12 X1 X13 -> False) -> False)
  -> (forall X6 X7 X8 X9 X11 X13 X12 X10 X5 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred2_13 X5 X6 X3 X7 X2 X8 X4 X9 X10 X11 X12 X1 X13 -> False) -> False)
  -> (forall X6 X9 X11 X13 X12 X10 X8 X7 X5 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred2_13 X5 X6 X7 X2 X8 X9 X10 X4 X3 X11 X12 X1 X13 -> False) -> False)
  -> (forall X6 X8 X11 X13 X12 X10 X9 X7 X5 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred2_13 X5 X6 X7 X8 X2 X3 X9 X4 X10 X11 X12 X1 X13 -> False) -> False)
  -> (forall X6 X9 X11 X13 X12 X10 X8 X7 X5 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred1_13 X5 X3 X2 X6 X7 X4 X8 X9 X10 X11 X1 X12 X13 -> False) -> False)
  -> (forall X6 X7 X8 X9 X11 X13 X12 X10 X5 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred1_13 X5 X6 X2 X7 X3 X8 X4 X9 X10 X11 X1 X12 X13 -> False) -> False)
  -> (forall X6 X9 X11 X13 X12 X10 X8 X7 X5 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred1_13 X5 X6 X7 X3 X8 X9 X4 X2 X10 X11 X1 X12 X13 -> False) -> False)
  -> (forall X6 X8 X11 X13 X12 X10 X9 X7 X5 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred1_13 X5 X6 X7 X8 X9 X4 X10 X2 X3 X11 X1 X12 X13 -> False) -> False)
  -> (forall X4 X6 X8 X10 X11 X12 X13 X9 X7 X5 X3 X2 X1, (epred2_13 X1 X3 X4 X5 X6 X7 X8 X9 X10 X2 X11 X12 X13 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X4 X6 X8 X10 X11 X12 X13 X9 X7 X5 X3 X2 X1, (epred1_13 X1 X3 X4 X5 X6 X7 X8 X9 X10 X2 X11 X12 X13 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X12 X13 X10 X8 X6 X4 X2 X1, (epred2_13 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X4 X5 X7 X9 X11 X12 X13 X10 X8 X6 X3 X2 X1, (epred2_13 X1 X3 X4 X2 X5 X6 X7 X8 X9 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X4 X6 X8 X11 X12 X13 X10 X9 X7 X5 X3 X2 X1, (epred2_13 X1 X3 X4 X5 X6 X7 X8 X9 X2 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X12 X13 X10 X8 X6 X4 X2 X1, (epred2_13 X3 X1 X2 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X12 X13 X10 X8 X6 X4 X2 X1, (epred2_13 X3 X4 X5 X1 X2 X6 X7 X8 X9 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X12 X13 X10 X8 X6 X4 X2 X1, (epred2_13 X3 X4 X5 X6 X7 X8 X1 X2 X9 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X12 X13 X10 X8 X6 X4 X2 X1, (epred2_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X1 X2 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X12 X13 X10 X8 X6 X4 X2 X1, (epred2_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X1 X12 X13 X2 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X13 X12 X10 X8 X6 X4 X2 X1, (epred2_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X2 X13 X1 -> False) -> X1 = X2 -> False)
  -> (forall X4 X5 X7 X9 X11 X12 X13 X10 X8 X6 X3 X2 X1, (epred1_13 X1 X3 X4 X2 X5 X6 X7 X8 X9 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X4 X6 X8 X9 X11 X12 X13 X10 X7 X5 X3 X2 X1, (epred1_13 X1 X3 X4 X5 X6 X7 X8 X2 X9 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X4 X6 X8 X11 X12 X13 X10 X9 X7 X5 X3 X2 X1, (epred1_13 X1 X3 X4 X5 X6 X7 X8 X9 X2 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X12 X13 X10 X8 X6 X4 X2 X1, (epred1_13 X3 X4 X5 X1 X2 X6 X7 X8 X9 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X12 X13 X10 X8 X6 X4 X2 X1, (epred1_13 X3 X4 X5 X6 X7 X1 X2 X8 X9 X10 X11 X12 X13 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X12 X13 X10 X8 X6 X4 X2 X1, (epred1_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X2 X12 X1 X13 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X12 X13 X10 X8 X6 X4 X2 X1, (epred1_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X2 X12 X13 X1 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X13 X12 X10 X8 X6 X4 X2 X1, (epred1_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X2 X1 -> False) -> X1 = X2 -> False)
  -> (forall X4 X6 X8 X10 X13 X12 X11 X9 X7 X5 X3 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X1 X12 X2 X13 -> False) -> False)
  -> (forall X4 X6 X8 X10 X12 X13 X11 X9 X7 X5 X3 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X1 X2 X13 -> False) -> False)
  -> (forall X4 X6 X8 X10 X12 X13 X11 X9 X7 X5 X3 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X2 X1 -> False) -> False)
  -> (forall X4 X6 X8 X10 X13 X12 X11 X9 X7 X5 X3 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X1 X2 X12 X13 -> False) -> False)
  -> (forall X4 X6 X8 X10 X12 X13 X11 X9 X7 X5 X3 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X2 X1 X13 -> False) -> False)
  -> (forall X4 X6 X8 X10 X12 X13 X11 X9 X7 X5 X3 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_13 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X2 X13 X1 -> False) -> False)
  -> (forall X3 X5 X7 X9 X11 X13 X12 X10 X8 X6 X4 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_13 X1 X3 X4 X5 X6 X7 X8 X9 X10 X11 X2 X12 X13 -> False) -> False)
  -> (forall X3 X5 X7 X9 X11 X13 X12 X10 X8 X6 X4 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_13 X1 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X2 -> False) -> False)
  -> (forall X5 X7 X9 X11 X13 X12 X10 X8 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_13 X3 X1 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X2 -> False) -> False)
  -> (forall X4 X5 X7 X9 X11 X13 X12 X10 X8 X6 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_13 X3 X4 X1 X5 X6 X7 X8 X9 X10 X11 X12 X13 X2 -> False) -> False)
  -> (forall X4 X7 X9 X13 X12 X11 X10 X8 X6 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_13 X3 X4 X5 X1 X6 X7 X8 X9 X10 X2 X11 X12 X13 -> False) -> False)
  -> (forall X4 X6 X7 X9 X13 X12 X11 X10 X8 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_13 X3 X4 X5 X6 X1 X7 X8 X9 X10 X2 X11 X12 X13 -> False) -> False)
  -> (forall X4 X6 X9 X11 X13 X12 X10 X8 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_13 X3 X4 X5 X6 X7 X1 X8 X9 X10 X11 X2 X12 X13 -> False) -> False)
  -> (forall X4 X6 X8 X10 X11 X13 X12 X9 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_13 X3 X4 X5 X6 X7 X8 X9 X10 X1 X11 X2 X12 X13 -> False) -> False)
  -> (forall X3 X5 X7 X9 X11 X13 X12 X10 X8 X6 X4 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_13 X1 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X2 X13 -> False) -> False)
  -> (forall X3 X5 X7 X9 X11 X13 X12 X10 X8 X6 X4 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_13 X1 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X2 -> False) -> False)
  -> (forall X5 X7 X9 X11 X13 X12 X10 X8 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_13 X3 X1 X4 X5 X6 X7 X8 X9 X10 X11 X12 X2 X13 -> False) -> False)
  -> (forall X4 X5 X7 X9 X11 X13 X12 X10 X8 X6 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_13 X3 X4 X1 X5 X6 X7 X8 X9 X10 X11 X12 X13 X2 -> False) -> False)
  -> (forall X4 X7 X9 X13 X12 X11 X10 X8 X6 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_13 X3 X4 X5 X1 X6 X7 X8 X9 X10 X2 X11 X12 X13 -> False) -> False)
  -> (forall X4 X6 X7 X9 X13 X12 X11 X10 X8 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_13 X3 X4 X5 X6 X1 X7 X8 X9 X10 X2 X11 X12 X13 -> False) -> False)
  -> (forall X4 X6 X8 X11 X13 X12 X10 X9 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_13 X3 X4 X5 X6 X7 X8 X9 X1 X10 X11 X12 X13 X2 -> False) -> False)
  -> (forall X4 X6 X8 X10 X11 X13 X12 X9 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_13 X3 X4 X5 X6 X7 X8 X9 X10 X1 X11 X12 X2 X13 -> False) -> False)
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
  -> (forall X1 X6 X3 X4 X2 X5, (X2 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> X2 = X6 -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X5 -> r2_analoaf X1 X3 X4 X6 X5 -> False)
  -> (forall X1 X2 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X5 -> r2_analoaf X1 X3 X4 X3 X5 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X1 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X4 X5 X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X6 -> r1_aff_1 X1 X2 X3 X5 -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk32_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (v1_aff_1 (esk32_4 X1 X2 X3 X4) X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk32_4 X2 X1 X3 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X1 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk32_4 X2 X3 X1 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X1 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk32_4 X2 X3 X4 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X4 X1 -> False)
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
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> (r2_hidden (esk33_3 X1 X2 X3) X2 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> (r2_hidden (esk33_3 X1 X2 X3) X3 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
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
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk3_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk2_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_3 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v3_aff_3 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk30_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk29_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (v4_aff_3 esk1_0 -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) X1 -> False) -> False)
  -> ((l1_struct_0 esk27_0 -> False) -> False)
  -> ((v3_aff_3 esk1_0 -> False) -> False)
  -> ((l1_analoaf esk26_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v2_diraf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
