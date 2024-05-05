(** $I sig/MizarPreamble.mgs **)

Theorem t7_aff_3:
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v1_aff_1:set -> set -> prop,
 forall r5_aff_1:set -> set -> set -> prop,
 forall epred2_10:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> prop,
 forall esk40_10:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall esk39_10:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk18_1:set -> set,
 forall esk22_1:set -> set,
 forall esk21_1:set -> set,
 forall esk16_1:set -> set,
 forall esk17_1:set -> set,
 forall esk15_1:set -> set,
 forall esk20_1:set -> set,
 forall esk23_1:set -> set,
 forall esk19_1:set -> set,
 forall v6_aff_3:set -> prop,
 forall esk32_3:set -> set -> set -> set,
 forall esk33_3:set -> set -> set -> set,
 forall esk34_3:set -> set -> set -> set,
 forall esk31_3:set -> set -> set -> set,
 forall esk30_4:set -> set -> set -> set -> set,
 forall esk36_3:set -> set -> set -> set,
 forall esk35_3:set -> set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall esk29_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk28_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk25_0:set,
 forall esk24_0:set,
 forall esk26_1:set -> set,
 forall esk1_0:set,
 forall v1_xboole_0:set -> prop,
 forall k1_xboole_0:set,
 forall esk27_1:set -> set,
 forall esk4_2:set -> set -> set,
 forall esk3_2:set -> set -> set,
 forall r2_aff_1:set -> set -> set -> set -> prop,
 forall esk37_4:set -> set -> set -> set -> set,
 forall esk2_4:set -> set -> set -> set -> set,
 forall k1_aff_1:set -> set -> set -> set,
 forall r3_aff_1:set -> set -> set -> prop,
 forall k2_aff_1:set -> set -> set -> set,
 forall v5_aff_3:set -> prop,
 forall v2_diraf:set -> prop,
 forall esk9_1:set -> set,
 forall esk14_1:set -> set,
 forall esk11_1:set -> set,
 forall esk6_1:set -> set,
 forall esk7_1:set -> set,
 forall esk5_1:set -> set,
 forall esk10_1:set -> set,
 forall esk13_1:set -> set,
 forall esk12_1:set -> set,
 forall esk8_1:set -> set,
 forall l1_analoaf:set -> prop,
 forall v1_diraf:set -> prop,
 forall v7_struct_0:set -> prop,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
 forall esk38_11:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall epred1_11:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> prop,
     (forall X1 X3 X6 X7 X8 X11 X10 X9 X5 X4 X2, (epred1_11 X1 X2 X9 X3 X4 X7 X8 X6 X5 X10 X11 -> False) -> r2_analoaf X1 X2 X3 X4 (esk38_11 X5 X6 X4 X7 X3 X8 X9 X2 X10 X11 X1) -> False)
  -> (forall X1 X3 X4 X5 X8 X10 X11 X9 X7 X6 X2, (epred1_11 X1 X9 X8 X3 X5 X6 X7 X2 X4 X10 X11 -> False) -> (r1_aff_1 X1 X2 X3 (esk38_11 X4 X2 X5 X6 X3 X7 X8 X9 X10 X11 X1) -> False) -> False)
  -> (forall X1 X3 X4 X6 X7 X8 X10 X11 X9 X5 X2, (epred1_11 X1 X9 X8 X7 X6 X3 X2 X5 X4 X10 X11 -> False) -> (r1_aff_1 X1 X2 X3 (esk38_11 X4 X5 X6 X3 X7 X2 X8 X9 X10 X11 X1) -> False) -> False)
  -> (forall X11 X2 X4 X6 X8 X10 X9 X7 X5 X3 X1, (epred1_11 X11 X8 X7 X5 X3 X4 X6 X2 X1 X9 X10 -> False) -> (m1_subset_1 (esk38_11 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11) (u1_struct_0 X11) -> False) -> False)
  -> (forall X1 X3 X4 X6 X8 X11 X10 X9 X7 X5 X2, (epred1_11 X11 X8 X7 X5 X1 X4 X6 X3 X2 X9 X10 -> False) -> (esk38_11 X2 X3 X1 X4 X5 X6 X7 X8 X9 X10 X11) = X1 -> False)
  -> (forall X9 X12 X5 X1 X4 X8 X7 X6 X2 X3 X10 X11, (X10 = X11 -> False) -> (X9 = X11 -> False) -> (X9 = X10 -> False) -> (X5 = X12 -> False) -> (X2 = X3 -> False) -> (r1_aff_1 X1 X8 X2 X4 -> False) -> (r1_aff_1 X1 X7 X3 X6 -> False) -> (r2_analoaf X1 X2 X4 X5 X12 -> False) -> r2_hidden X8 X9 -> r2_hidden X7 X9 -> r2_hidden X6 X10 -> r2_hidden X4 X10 -> r2_hidden X3 X11 -> r2_hidden X2 X11 -> v1_aff_1 X11 X1 -> v1_aff_1 X10 X1 -> v1_aff_1 X9 X1 -> r5_aff_1 X1 X11 X10 -> r5_aff_1 X1 X11 X9 -> m1_subset_1 X12 (u1_struct_0 X1) -> r1_aff_1 X1 X8 X4 X12 -> r1_aff_1 X1 X8 X2 X5 -> r1_aff_1 X1 X7 X6 X12 -> r1_aff_1 X1 X7 X3 X5 -> r2_analoaf X1 X2 X4 X3 X6 -> epred1_11 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> epred1_11 X1 (esk8_1 X1) (esk9_1 X1) (esk12_1 X1) (esk14_1 X1) (esk13_1 X1) (esk11_1 X1) (esk10_1 X1) (esk6_1 X1) (esk7_1 X1) (esk5_1 X1) -> False)
  -> (forall X1 X3 X4 X6 X7 X10 X9 X8 X5 X2, (epred2_10 X1 X2 X8 X3 X6 X7 X5 X4 X9 X10 -> False) -> (r2_analoaf X1 X2 X3 (esk39_10 X4 X5 X6 X3 X7 X8 X2 X9 X10 X1) (esk40_10 X4 X5 X6 X3 X7 X8 X2 X9 X10 X1) -> False) -> False)
  -> (forall X8 X11 X10 X9 X7 X6 X2 X5 X4 X3 X1, (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (epred1_11 X1 X2 X4 X3 X6 X5 X7 X8 X9 X10 X11 -> False) -> False)
  -> (forall X11 X9 X7 X5 X2 X3 X4 X6 X8 X10 X1, (v7_struct_0 X1 -> False) -> (epred1_11 X1 X5 X6 X9 X11 X10 X8 X7 X3 X4 X2 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v5_aff_3 X1 -> m1_subset_1 X11 (u1_struct_0 X1) -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X5 X6 X8 X9 X10 X11 X7 X1 X4 X3 X2, (epred1_11 X1 X3 X5 X4 X6 X7 X8 X2 X9 X10 X11 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X7 X9 X10 X11 X8 X6 X5 X1 X4 X3 X2, (epred1_11 X1 X5 X3 X6 X7 X4 X2 X8 X9 X10 X11 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X6 X7 X11 X10 X9 X8 X5 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred1_11 X1 X3 X5 X6 X4 X7 X8 X2 X9 X10 X11 -> False) -> False)
  -> (forall X5 X6 X7 X8 X11 X10 X9 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (epred1_11 X1 X5 X3 X6 X4 X7 X2 X8 X9 X10 X11 -> False) -> False)
  -> (forall X4 X6 X8 X10 X11 X9 X7 X5 X3 X2 X1, (r5_aff_1 X1 X2 X3 -> False) -> (epred1_11 X1 X4 X5 X6 X7 X8 X9 X10 X3 X11 X2 -> False) -> False)
  -> (forall X4 X6 X8 X10 X11 X9 X7 X5 X3 X2 X1, (r5_aff_1 X1 X2 X3 -> False) -> (epred1_11 X1 X4 X5 X6 X7 X8 X9 X10 X11 X3 X2 -> False) -> False)
  -> (forall X3 X5 X7 X9 X11 X10 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_11 X2 X3 X4 X5 X6 X7 X8 X9 X1 X10 X11 -> False) -> False)
  -> (forall X3 X5 X7 X9 X11 X10 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_11 X2 X3 X4 X5 X6 X7 X8 X9 X10 X1 X11 -> False) -> False)
  -> (forall X3 X5 X7 X9 X11 X10 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_11 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X1 -> False) -> False)
  -> (forall X5 X7 X9 X11 X10 X8 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X1 X4 X5 X6 X7 X8 X9 X10 X11 X2 -> False) -> False)
  -> (forall X4 X5 X7 X9 X11 X10 X8 X6 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X4 X1 X5 X6 X7 X8 X9 X10 X11 X2 -> False) -> False)
  -> (forall X4 X7 X9 X11 X10 X8 X6 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X4 X5 X1 X6 X7 X8 X9 X10 X2 X11 -> False) -> False)
  -> (forall X4 X6 X9 X11 X10 X8 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X4 X5 X6 X7 X1 X8 X9 X10 X2 X11 -> False) -> False)
  -> (forall X4 X6 X8 X9 X11 X10 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X4 X5 X6 X7 X8 X1 X9 X2 X10 X11 -> False) -> False)
  -> (forall X4 X6 X8 X11 X10 X9 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_11 X3 X4 X5 X6 X7 X8 X9 X1 X2 X10 X11 -> False) -> False)
  -> (forall X3 X5 X7 X9 X10 X11 X8 X6 X4 X2 X1, (epred1_11 X3 X1 X2 X4 X5 X6 X7 X8 X9 X10 X11 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X10 X8 X6 X4 X2 X1, (epred1_11 X3 X4 X5 X6 X7 X8 X9 X10 X1 X2 X11 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X10 X8 X6 X4 X2 X1, (epred1_11 X3 X4 X5 X6 X7 X8 X9 X10 X2 X11 X1 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X11 X10 X8 X6 X4 X2 X1, (epred1_11 X3 X4 X5 X6 X7 X8 X9 X10 X11 X2 X1 -> False) -> X1 = X2 -> False)
  -> (forall X2 X4 X6 X8 X9 X10 X7 X5 X3 X1, (epred2_10 X10 X7 X6 X4 X3 X5 X2 X1 X8 X9 -> False) -> (esk40_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = (esk39_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) -> False)
  -> (forall X1 X3 X4 X5 X7 X10 X9 X8 X6 X2, (epred2_10 X1 X3 X8 X6 X5 X7 X2 X4 X9 X10 -> False) -> (r1_aff_1 X1 X2 X3 (esk39_10 X4 X2 X5 X6 X7 X8 X3 X9 X10 X1) -> False) -> False)
  -> (forall X1 X3 X4 X6 X8 X10 X9 X7 X5 X2, (epred2_10 X1 X8 X3 X7 X6 X2 X5 X4 X9 X10 -> False) -> (r1_aff_1 X1 X2 X3 (esk39_10 X4 X5 X6 X7 X2 X3 X8 X9 X10 X1) -> False) -> False)
  -> (forall X1 X3 X4 X5 X6 X8 X10 X9 X7 X2, (epred2_10 X1 X8 X7 X3 X5 X6 X2 X4 X9 X10 -> False) -> (r1_aff_1 X1 X2 X3 (esk40_10 X4 X2 X5 X3 X6 X7 X8 X9 X10 X1) -> False) -> False)
  -> (forall X1 X3 X4 X8 X10 X9 X7 X6 X5 X2, (epred2_10 X1 X8 X7 X6 X3 X2 X5 X4 X9 X10 -> False) -> (r1_aff_1 X1 X2 X3 (esk40_10 X4 X5 X3 X6 X2 X7 X8 X9 X10 X1) -> False) -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (epred2_10 X10 X7 X6 X4 X3 X5 X2 X1 X8 X9 -> False) -> (m1_subset_1 (esk40_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) (u1_struct_0 X10) -> False) -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (epred2_10 X10 X7 X6 X4 X3 X5 X2 X1 X8 X9 -> False) -> (m1_subset_1 (esk39_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) (u1_struct_0 X10) -> False) -> False)
  -> (forall X10 X9 X5 X3 X6 X7 X2 X4 X1 X8 X11 X12, (X11 = X12 -> False) -> (X9 = X10 -> False) -> (X8 = X10 -> False) -> (X8 = X9 -> False) -> (r1_aff_1 X1 X7 X2 X4 -> False) -> (r1_aff_1 X1 X6 X3 X5 -> False) -> (r2_analoaf X1 X2 X4 X3 X5 -> False) -> r2_hidden X7 X8 -> r2_hidden X6 X8 -> r2_hidden X5 X9 -> r2_hidden X4 X9 -> r2_hidden X3 X10 -> r2_hidden X2 X10 -> v1_aff_1 X10 X1 -> v1_aff_1 X9 X1 -> v1_aff_1 X8 X1 -> r5_aff_1 X1 X10 X9 -> r5_aff_1 X1 X10 X8 -> m1_subset_1 X12 (u1_struct_0 X1) -> m1_subset_1 X11 (u1_struct_0 X1) -> r1_aff_1 X1 X7 X4 X12 -> r1_aff_1 X1 X7 X2 X11 -> r1_aff_1 X1 X6 X5 X12 -> r1_aff_1 X1 X6 X3 X11 -> r2_analoaf X1 X2 X4 X11 X12 -> epred2_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> epred2_10 X1 (esk18_1 X1) (esk19_1 X1) (esk22_1 X1) (esk23_1 X1) (esk21_1 X1) (esk20_1 X1) (esk16_1 X1) (esk17_1 X1) (esk15_1 X1) -> False)
  -> (forall X7 X10 X9 X8 X6 X1 X3 X4 X5 X2, (epred2_10 X1 X2 X4 X3 X5 X6 X7 X8 X9 X10 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X5 X6 X10 X9 X8 X7 X1 X4 X3 X2, (epred2_10 X1 X3 X5 X4 X6 X7 X2 X8 X9 X10 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X7 X10 X9 X8 X6 X5 X1 X4 X3 X2, (epred2_10 X1 X5 X3 X6 X4 X2 X7 X8 X9 X10 -> False) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X10 X8 X6 X4 X3 X2 X5 X7 X9 X1, (v7_struct_0 X1 -> False) -> (epred2_10 X1 X5 X6 X9 X10 X8 X7 X3 X4 X2 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v6_aff_3 X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X6 X8 X10 X9 X7 X5 X3 X2 X1, (r5_aff_1 X1 X2 X3 -> False) -> (epred2_10 X1 X4 X5 X6 X7 X8 X9 X3 X10 X2 -> False) -> False)
  -> (forall X4 X6 X8 X10 X9 X7 X5 X3 X2 X1, (r5_aff_1 X1 X2 X3 -> False) -> (epred2_10 X1 X4 X5 X6 X7 X8 X9 X10 X3 X2 -> False) -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_10 X2 X3 X4 X5 X6 X7 X8 X1 X9 X10 -> False) -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_10 X2 X3 X4 X5 X6 X7 X8 X9 X1 X10 -> False) -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred2_10 X2 X3 X4 X5 X6 X7 X8 X9 X10 X1 -> False) -> False)
  -> (forall X5 X7 X9 X10 X8 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_10 X3 X1 X4 X5 X6 X7 X8 X9 X10 X2 -> False) -> False)
  -> (forall X4 X5 X7 X9 X10 X8 X6 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_10 X3 X4 X1 X5 X6 X7 X8 X9 X10 X2 -> False) -> False)
  -> (forall X4 X7 X9 X10 X8 X6 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_10 X3 X4 X5 X1 X6 X7 X8 X9 X2 X10 -> False) -> False)
  -> (forall X4 X6 X7 X9 X10 X8 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_10 X3 X4 X5 X6 X1 X7 X8 X9 X2 X10 -> False) -> False)
  -> (forall X4 X6 X9 X10 X8 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_10 X3 X4 X5 X6 X7 X1 X8 X2 X9 X10 -> False) -> False)
  -> (forall X4 X6 X8 X9 X10 X7 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred2_10 X3 X4 X5 X6 X7 X8 X1 X2 X9 X10 -> False) -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X2 X1, (epred2_10 X3 X4 X5 X6 X7 X8 X9 X1 X2 X10 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X2 X1, (epred2_10 X3 X4 X5 X6 X7 X8 X9 X2 X10 X1 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X9 X10 X8 X6 X4 X2 X1, (epred2_10 X3 X4 X5 X6 X7 X8 X9 X10 X2 X1 -> False) -> X1 = X2 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X2 X3 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X4 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X3 X1 X6 X7 X2 X4 X5, (X4 = X5 -> False) -> (X1 = X3 -> False) -> (v7_struct_0 X2 -> False) -> (r3_aff_1 X2 X6 X7 -> False) -> X7 = (k2_aff_1 X2 X4 X5) -> X6 = (k2_aff_1 X2 X1 X3) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r2_analoaf X2 X1 X3 X4 X5 -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X2 X4 -> False)
  -> (forall X3 X4 X2 X1, (X4 = (k1_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> r2_hidden (esk2_4 X1 X2 X3 X4) X4 -> r1_aff_1 X1 X2 X3 (esk2_4 X1 X2 X3 X4) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 (esk31_3 X1 X2 X3) (esk32_3 X1 X2 X3) (esk33_3 X1 X2 X3) (esk34_3 X1 X2 X3) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X3 X4 X5 X2 X6 X7 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X7 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X6 -> r3_aff_1 X1 X6 X7 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X4 X5 X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X6 -> r1_aff_1 X1 X2 X3 X5 -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X3 X2 X4 X1, (X4 = (k1_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden (esk2_4 X1 X2 X3 X4) X4 -> False) -> (r1_aff_1 X1 X2 X3 (esk2_4 X1 X2 X3 X4) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_aff_1 X1 X2 X3 X4 -> False) -> (r1_aff_1 X1 X2 X3 (esk37_4 X1 X2 X3 X4) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X4 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk30_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (v1_aff_1 (esk30_4 X1 X2 X3 X4) X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk30_4 X2 X1 X3 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X1 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk30_4 X2 X3 X1 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X1 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk30_4 X2 X3 X4 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X4 X1 -> False)
  -> (forall X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_aff_1 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk37_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X4 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_aff_1 X1 X2 X3 X4 -> False) -> (r2_hidden (esk37_4 X1 X2 X3 X4) X4 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X4 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_aff_1 X1 X2 X3 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X4 X5 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_aff_1 X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X3 X2 -> False)
  -> (forall X3 X2 X4 X1, (X4 = (k1_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk2_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X5 X4 X3 X2 X1, (v7_struct_0 X1 -> False) -> (r2_hidden X4 X5 -> False) -> X5 = (k1_aff_1 X1 X2 X3) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X5 -> r2_hidden X2 X5 -> v1_aff_1 X5 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X2 X1, (v7_struct_0 X1 -> False) -> (r2_hidden X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X2 X4 -> v1_aff_1 X4 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_aff_1 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X5 X4 X2 X3, (v7_struct_0 X3 -> False) -> (r1_aff_1 X3 X4 X5 X1 -> False) -> X2 = (k1_aff_1 X3 X4 X5) -> v1_diraf X3 -> l1_analoaf X3 -> r2_hidden X1 X2 -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X5 X4 X3 X1 X2, (v7_struct_0 X2 -> False) -> (r1_aff_1 X2 X3 X4 X5 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r2_hidden X5 X1 -> r2_hidden X4 X1 -> r2_hidden X3 X1 -> v1_aff_1 X1 X2 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((k2_aff_1 X2 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1)) = X1 -> False) -> (v7_struct_0 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r3_aff_1 X2 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((k2_aff_1 X2 (esk31_3 X2 X1 X3) (esk32_3 X2 X1 X3)) = X1 -> False) -> (v7_struct_0 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r3_aff_1 X2 X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X4 X1 X3, (v7_struct_0 X3 -> False) -> (r2_aff_1 X3 X4 X1 X2 -> False) -> v1_diraf X3 -> l1_analoaf X3 -> r2_hidden X4 X2 -> r2_hidden X1 X2 -> v1_aff_1 X2 X3 -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X2 X4 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X3 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X4 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X4 X3 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X4 X2 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (esk34_3 X1 X2 X3) = (esk33_3 X1 X2 X3) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (esk32_3 X1 X2 X3) = (esk31_3 X1 X2 X3) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk36_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X2 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X3 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk31_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1 X4 X5, (X4 = X5 -> False) -> (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X5 -> r2_hidden X3 X4 -> r2_hidden X2 X5 -> r2_hidden X2 X4 -> v1_aff_1 X5 X1 -> v1_aff_1 X4 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X2 X4 -> r2_hidden X2 X3 -> r5_aff_1 X1 X3 X4 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 (esk35_3 X1 X3 X2) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk35_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk35_3 X2 X1 X3) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> v1_aff_1 X3 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X4 X1 X3, (X1 = X3 -> False) -> (v7_struct_0 X2 -> False) -> (v1_aff_1 X4 X2 -> False) -> X4 = (k2_aff_1 X2 X1 X3) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k1_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k2_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (v1_aff_1 X1 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r3_aff_1 X2 X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (v1_aff_1 X1 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r3_aff_1 X2 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (k2_aff_1 X2 X1 X3) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (k2_aff_1 X2 X3 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X2, ((k2_aff_1 X2 (esk3_2 X2 X1) (esk4_2 X2 X1)) = X1 -> False) -> (v7_struct_0 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> v1_aff_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, ((k1_aff_1 X1 X2 X3) = (k2_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k2_aff_1 X1 X2 X3) = (k2_aff_1 X1 X3 X2) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk4_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk3_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (esk4_2 X1 X2) = (esk3_2 X1 X2) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v5_aff_3 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v6_aff_3 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk28_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk27_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (v5_aff_3 esk1_0 -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) X1 -> False) -> False)
  -> ((l1_struct_0 esk25_0 -> False) -> False)
  -> ((v6_aff_3 esk1_0 -> False) -> False)
  -> ((l1_analoaf esk24_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v2_diraf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
