(** $I sig/MizarPreamble.mgs **)

Theorem t7_conmetr1:
 forall v1_aff_1:set -> set -> prop,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
 forall esk29_6:set -> set -> set -> set -> set -> set -> set,
 forall r3_aff_1:set -> set -> set -> prop,
 forall esk23_3:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v2_struct_0:set -> prop,
 forall esk22_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk21_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk17_0:set,
 forall esk18_0:set,
 forall esk19_1:set -> set,
 forall esk1_0:set,
 forall k1_xboole_0:set,
 forall r1_tarski:set -> set -> prop,
 forall esk20_1:set -> set,
 forall r5_aff_1:set -> set -> set -> prop,
 forall esk24_4:set -> set -> set -> set -> set,
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall esk25_5:set -> set -> set -> set -> set -> set,
 forall v4_aff_2:set -> prop,
 forall esk12_1:set -> set,
 forall esk14_1:set -> set,
 forall esk15_1:set -> set,
 forall esk16_1:set -> set,
 forall esk13_1:set -> set,
 forall esk28_6:set -> set -> set -> set -> set -> set -> set,
 forall esk30_6:set -> set -> set -> set -> set -> set -> set,
 forall esk31_6:set -> set -> set -> set -> set -> set -> set,
 forall esk27_6:set -> set -> set -> set -> set -> set -> set,
 forall epred2_6:set -> set -> set -> set -> set -> set -> prop,
 forall v2_conmetr1:set -> prop,
 forall v2_diraf:set -> prop,
 forall esk5_1:set -> set,
 forall esk8_1:set -> set,
 forall esk10_1:set -> set,
 forall esk7_1:set -> set,
 forall esk4_1:set -> set,
 forall esk2_1:set -> set,
 forall esk11_1:set -> set,
 forall esk9_1:set -> set,
 forall esk6_1:set -> set,
 forall esk3_1:set -> set,
 forall l1_analoaf:set -> prop,
 forall v1_diraf:set -> prop,
 forall v7_struct_0:set -> prop,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk26_11:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall epred1_11:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> prop,
     (forall X1 X2 X4 X6 X8 X10 X11 X9 X7 X5 X3, (epred1_11 X11 X1 X8 X7 X5 X4 X3 X2 X6 X9 X10 -> False) -> r2_hidden X1 (esk26_11 X2 X3 X4 X5 X6 X7 X8 X9 X1 X10 X11) -> False)
  -> (forall X1 X2 X4 X6 X9 X10 X11 X8 X7 X5 X3, (epred1_11 X11 X9 X1 X7 X5 X4 X3 X2 X6 X8 X10 -> False) -> r2_hidden X1 (esk26_11 X2 X3 X4 X5 X6 X7 X1 X8 X9 X10 X11) -> False)
  -> (forall X1 X2 X5 X7 X9 X10 X11 X8 X6 X4 X3, (epred1_11 X11 X9 X7 X6 X4 X1 X3 X2 X5 X8 X10 -> False) -> r2_hidden X1 (esk26_11 X2 X3 X1 X4 X5 X6 X7 X8 X9 X10 X11) -> False)
  -> (forall X1 X2 X4 X7 X9 X10 X11 X8 X6 X5 X3, (epred1_11 X11 X9 X7 X6 X5 X4 X3 X2 X1 X8 X10 -> False) -> r2_hidden X1 (esk26_11 X2 X3 X4 X5 X1 X6 X7 X8 X9 X10 X11) -> False)
  -> (forall X11 X2 X4 X6 X8 X10 X9 X7 X5 X3 X1, (epred1_11 X11 X9 X7 X6 X4 X3 X2 X1 X5 X8 X10 -> False) -> (m1_subset_1 (esk26_11 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11) (k1_zfmisc_1 (u1_struct_0 X11)) -> False) -> False)
  -> (forall X11 X2 X4 X6 X8 X10 X9 X7 X5 X3 X1, (epred1_11 X11 X9 X7 X6 X4 X3 X2 X1 X5 X8 X10 -> False) -> (v1_aff_1 (esk26_11 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11) X11 -> False) -> False)
  -> (forall X1 X2 X4 X6 X7 X9 X10 X11 X8 X5 X3, (epred1_11 X11 X9 X7 X1 X5 X4 X3 X2 X6 X8 X10 -> False) -> (r2_hidden X1 (esk26_11 X2 X3 X4 X5 X6 X1 X7 X8 X9 X10 X11) -> False) -> False)
  -> (forall X1 X2 X4 X5 X7 X9 X10 X11 X8 X6 X3, (epred1_11 X11 X9 X7 X6 X1 X4 X3 X2 X5 X8 X10 -> False) -> (r2_hidden X1 (esk26_11 X2 X3 X4 X1 X5 X6 X7 X8 X9 X10 X11) -> False) -> False)
  -> (forall X1 X2 X3 X5 X7 X9 X10 X11 X8 X6 X4, (epred1_11 X11 X9 X7 X6 X4 X3 X1 X2 X5 X8 X10 -> False) -> (r2_hidden X1 (esk26_11 X2 X1 X3 X4 X5 X6 X7 X8 X9 X10 X11) -> False) -> False)
  -> (forall X1 X2 X4 X6 X8 X9 X10 X11 X7 X5 X3, (epred1_11 X11 X9 X8 X7 X5 X4 X3 X2 X6 X1 X10 -> False) -> (r2_hidden X1 (esk26_11 X2 X3 X4 X5 X6 X7 X8 X1 X9 X10 X11) -> False) -> False)
  -> (forall X1 X2 X4 X6 X8 X10 X11 X9 X7 X5 X3, (epred1_11 X11 X10 X8 X7 X5 X4 X3 X2 X6 X9 X1 -> False) -> (r2_hidden X1 (esk26_11 X2 X3 X4 X5 X6 X7 X8 X9 X10 X1 X11) -> False) -> False)
  -> (forall X12 X9 X6 X4 X2 X11 X1 X3 X5 X7 X10 X8, (r2_hidden X10 X8 -> False) -> (r2_hidden X9 X12 -> False) -> (r2_hidden X7 X8 -> False) -> (r2_hidden X6 X12 -> False) -> (r2_hidden X5 X8 -> False) -> (r2_hidden X4 X8 -> False) -> (r2_hidden X3 X12 -> False) -> (r2_hidden X2 X12 -> False) -> (r2_analoaf X1 X3 X4 X6 X7 -> False) -> r2_hidden X11 X12 -> r2_hidden X11 X8 -> r2_hidden X10 X12 -> r2_hidden X9 X8 -> r2_hidden X7 X12 -> r2_hidden X6 X8 -> r2_hidden X5 X12 -> r2_hidden X4 X12 -> r2_hidden X3 X8 -> r2_hidden X2 X8 -> v1_aff_1 X12 X1 -> v1_aff_1 X8 X1 -> r2_analoaf X1 X10 X2 X5 X9 -> r2_analoaf X1 X3 X10 X6 X5 -> r2_analoaf X1 X2 X4 X9 X7 -> m1_subset_1 X12 (k1_zfmisc_1 (u1_struct_0 X1)) -> epred1_11 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> epred1_11 X1 (esk3_1 X1) (esk5_1 X1) (esk6_1 X1) (esk8_1 X1) (esk9_1 X1) (esk10_1 X1) (esk11_1 X1) (esk7_1 X1) (esk4_1 X1) (esk2_1 X1) -> False)
  -> (forall X7 X9 X10 X11 X8 X6 X1 X3 X4 X5 X2, (epred1_11 X1 X6 X2 X3 X7 X4 X5 X8 X9 X10 X11 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X8 X9 X11 X10 X7 X6 X2 X5 X4 X3 X1, (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (epred1_11 X1 X2 X6 X3 X7 X8 X5 X9 X4 X10 X11 -> False) -> False)
  -> (forall X7 X8 X10 X11 X9 X6 X2 X5 X4 X3 X1, (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (epred1_11 X1 X3 X6 X7 X4 X8 X9 X10 X5 X2 X11 -> False) -> False)
  -> (forall X6 X7 X9 X11 X10 X8 X2 X5 X4 X3 X1, (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (epred1_11 X1 X6 X2 X7 X5 X4 X8 X9 X10 X3 X11 -> False) -> False)
  -> (forall X10 X8 X6 X4 X11 X2 X3 X5 X7 X9 X1, (v7_struct_0 X1 -> False) -> (epred1_11 X1 X3 X5 X6 X8 X9 X10 X11 X7 X4 X2 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v2_conmetr1 X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X11 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X5 X6 X8 X9 X10 X11 X7 X4 X2 X1, (epred1_11 X3 X4 X5 X1 X6 X7 X8 X2 X9 X10 X11 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X5 X8 X9 X10 X11 X7 X6 X4 X2 X1, (epred1_11 X3 X4 X5 X6 X1 X7 X8 X2 X9 X10 X11 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X5 X7 X9 X10 X11 X8 X6 X4 X2 X1, (epred1_11 X3 X4 X5 X6 X7 X8 X1 X2 X9 X10 X11 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X5 X7 X9 X10 X11 X8 X6 X4 X2 X1, (epred1_11 X3 X4 X5 X6 X7 X8 X9 X2 X10 X1 X11 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X5 X7 X11 X10 X9 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_11 X2 X3 X4 X5 X6 X7 X8 X1 X9 X10 X11 -> False) -> False)
  -> (forall X5 X7 X11 X10 X9 X8 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X1 X4 X5 X6 X7 X8 X2 X9 X10 X11 -> False) -> False)
  -> (forall X4 X5 X7 X11 X10 X9 X8 X6 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X4 X1 X5 X6 X7 X8 X2 X9 X10 X11 -> False) -> False)
  -> (forall X4 X6 X11 X10 X9 X8 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X4 X5 X6 X7 X1 X8 X2 X9 X10 X11 -> False) -> False)
  -> (forall X4 X6 X8 X11 X10 X9 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X4 X5 X6 X7 X8 X9 X2 X1 X10 X11 -> False) -> False)
  -> (forall X4 X6 X8 X11 X10 X9 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X4 X5 X6 X7 X8 X9 X2 X10 X11 X1 -> False) -> False)
  -> (forall X1 X2 X4 X6 X5 X3, (epred2_6 X1 X6 X5 X4 X3 X2 -> False) -> r2_analoaf X1 (esk27_6 X2 X3 X4 X5 X6 X1) (esk28_6 X2 X3 X4 X5 X6 X1) (esk30_6 X2 X3 X4 X5 X6 X1) (esk31_6 X2 X3 X4 X5 X6 X1) -> False)
  -> (forall X1 X3 X5 X6 X4 X2, (epred2_6 X1 X6 X5 X4 X3 X2 -> False) -> (r2_analoaf X1 X2 (esk28_6 X2 X3 X4 X5 X6 X1) (esk29_6 X2 X3 X4 X5 X6 X1) (esk31_6 X2 X3 X4 X5 X6 X1) -> False) -> False)
  -> (forall X1 X3 X5 X6 X4 X2, (epred2_6 X1 X6 X5 X4 X3 X2 -> False) -> (r2_analoaf X1 X2 (esk27_6 X2 X3 X4 X5 X6 X1) (esk29_6 X2 X3 X4 X5 X6 X1) (esk30_6 X2 X3 X4 X5 X6 X1) -> False) -> False)
  -> (forall X6 X2 X4 X5 X3 X1, (epred2_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk31_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X6) -> False) -> False)
  -> (forall X6 X2 X4 X5 X3 X1, (epred2_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk30_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X6) -> False) -> False)
  -> (forall X6 X2 X4 X5 X3 X1, (epred2_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X6) -> False) -> False)
  -> (forall X6 X2 X4 X5 X3 X1, (epred2_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk28_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X6) -> False) -> False)
  -> (forall X6 X2 X4 X5 X3 X1, (epred2_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X6) -> False) -> False)
  -> (forall X3 X2 X4 X5 X6 X1, (epred2_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk31_6 X1 X2 X3 X4 X5 X6) X3 -> False) -> False)
  -> (forall X4 X2 X5 X6 X3 X1, (epred2_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk30_6 X1 X2 X3 X4 X5 X6) X4 -> False) -> False)
  -> (forall X5 X2 X4 X6 X3 X1, (epred2_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk29_6 X1 X2 X3 X4 X5 X6) X5 -> False) -> False)
  -> (forall X3 X2 X4 X5 X6 X1, (epred2_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk28_6 X1 X2 X3 X4 X5 X6) X3 -> False) -> False)
  -> (forall X4 X2 X5 X6 X3 X1, (epred2_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk27_6 X1 X2 X3 X4 X5 X6) X4 -> False) -> False)
  -> (forall X1 X4 X5 X6 X3 X2, (epred2_6 X6 X5 X4 X3 X1 X2 -> False) -> (esk28_6 X2 X1 X3 X4 X5 X6) = X1 -> False)
  -> (forall X1 X4 X5 X6 X3 X2, (epred2_6 X6 X5 X4 X3 X1 X2 -> False) -> (esk27_6 X2 X1 X3 X4 X5 X6) = X1 -> False)
  -> (forall X7 X4 X2 X1 X10 X11 X9 X3 X6 X5 X8, (X5 = X8 -> False) -> (X5 = X7 -> False) -> (X5 = X6 -> False) -> (X2 = X4 -> False) -> (X2 = X3 -> False) -> (r2_analoaf X1 X7 X8 X10 X11 -> False) -> r2_hidden X11 X4 -> r2_hidden X10 X3 -> r2_hidden X9 X2 -> r2_hidden X8 X4 -> r2_hidden X7 X3 -> r2_hidden X6 X2 -> r2_hidden X5 X4 -> r2_hidden X5 X3 -> r2_hidden X5 X2 -> v1_aff_1 X4 X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X11 (u1_struct_0 X1) -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> r2_analoaf X1 X6 X8 X9 X11 -> r2_analoaf X1 X6 X7 X9 X10 -> epred2_6 X1 X2 X3 X4 X5 X6 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> epred2_6 X1 (esk12_1 X1) (esk13_1 X1) (esk14_1 X1) (esk15_1 X1) (esk16_1 X1) -> False)
  -> (forall X5 X2 X3 X4 X6 X1, (v7_struct_0 X1 -> False) -> (epred2_6 X1 X2 X3 X4 X5 X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v4_aff_2 X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X5 X6 X3 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_6 X2 X1 X3 X4 X5 X6 -> False) -> False)
  -> (forall X3 X4 X5 X6 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_6 X2 X3 X1 X4 X5 X6 -> False) -> False)
  -> (forall X3 X5 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_6 X2 X3 X4 X1 X5 X6 -> False) -> False)
  -> (forall X5 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_6 X3 X2 X4 X5 X1 X6 -> False) -> False)
  -> (forall X5 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_6 X3 X2 X4 X5 X6 X1 -> False) -> False)
  -> (forall X4 X5 X6 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_6 X3 X4 X2 X5 X1 X6 -> False) -> False)
  -> (forall X4 X6 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_6 X3 X4 X5 X2 X1 X6 -> False) -> False)
  -> (forall X3 X6 X5 X4 X2 X1, (epred2_6 X3 X1 X2 X4 X5 X6 -> False) -> X1 = X2 -> False)
  -> (forall X3 X4 X6 X5 X2 X1, (epred2_6 X3 X1 X4 X2 X5 X6 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X6 X4 X2 X1, (epred2_6 X3 X4 X5 X6 X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X2 X3 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X4 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (r1_aff_1 X1 X2 X3 (esk25_5 X1 X2 X3 X4 X5) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X2 X3 -> False) -> (r1_aff_1 X1 X2 X3 (esk25_5 X1 X4 X5 X2 X3) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (m1_subset_1 (esk25_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X3 X2 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X3 X2 -> False)
  -> (forall X1 X2 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X5 -> r2_analoaf X1 X3 X4 X3 X5 -> False)
  -> (forall X3 X2 X6 X7 X1 X4 X5, (X4 = X5 -> False) -> (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X7 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X6 -> v1_aff_1 X7 X1 -> v1_aff_1 X6 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X4 X5 -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X5 X4 X2 X3 X1 X6 X7, (X6 = X7 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X7 X3 -> r2_hidden X6 X3 -> r2_hidden X5 X2 -> r2_hidden X4 X2 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X5 X2 X6 X7 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X7 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X6 -> r3_aff_1 X1 X6 X7 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk24_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (v1_aff_1 (esk24_4 X1 X2 X3 X4) X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk24_4 X2 X1 X3 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X1 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk24_4 X2 X3 X1 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X1 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk24_4 X2 X3 X4 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X4 X1 -> False)
  -> (forall X4 X1 X2 X3 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 (esk23_3 X1 X2 X3) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X5 X6 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X3 X2 -> False)
  -> (forall X4 X1 X2 X3 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk23_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X5 X6 -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X2 -> False) -> (esk23_3 X2 X1 X3) = X1 -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X6 (u1_struct_0 X2) -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X4 X5 X6 -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X2 -> False) -> (esk23_3 X2 X3 X1) = X1 -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X6 (u1_struct_0 X2) -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X4 X5 X6 -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X5 -> r2_hidden X2 X5 -> v1_aff_1 X5 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X5 X4 X3 X1 X2, (v7_struct_0 X2 -> False) -> (r1_aff_1 X2 X3 X4 X5 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r2_hidden X5 X1 -> r2_hidden X4 X1 -> r2_hidden X3 X1 -> v1_aff_1 X1 X2 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X4 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X3 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X4 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X4 X3 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X4 X2 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X2 X4 -> r2_hidden X2 X3 -> r5_aff_1 X1 X3 X4 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X2 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> (m1_subset_1 (esk4_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> (m1_subset_1 (esk3_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v2_conmetr1 X1 -> False) -> (m1_subset_1 (esk2_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk21_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk20_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (v2_conmetr1 esk1_0 -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((l1_struct_0 esk18_0 -> False) -> False)
  -> ((v4_aff_2 esk1_0 -> False) -> False)
  -> ((l1_analoaf esk17_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v2_diraf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
