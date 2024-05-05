(** $I sig/MizarPreamble.mgs **)

Theorem t6_conmetr1:
 forall r2_hidden:set -> set -> prop,
 forall esk29_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall r5_aff_1:set -> set -> set -> prop,
 forall v7_struct_0:set -> prop,
 forall v1_diraf:set -> prop,
 forall l1_analoaf:set -> prop,
 forall esk2_1:set -> set,
 forall esk5_1:set -> set,
 forall esk3_1:set -> set,
 forall esk7_1:set -> set,
 forall esk6_1:set -> set,
 forall esk4_1:set -> set,
 forall v2_diraf:set -> prop,
 forall v1_conmetr1:set -> prop,
 forall epred3_1:set -> prop,
 forall esk38_5:set -> set -> set -> set -> set -> set,
 forall esk17_5:set -> set -> set -> set -> set -> set,
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall esk33_1:set -> set,
 forall esk35_1:set -> set,
 forall esk34_1:set -> set,
 forall esk37_4:set -> set -> set -> set -> set,
 forall esk36_4:set -> set -> set -> set -> set,
 forall r3_aff_1:set -> set -> set -> prop,
 forall esk14_3:set -> set -> set -> set,
 forall esk15_3:set -> set -> set -> set,
 forall esk19_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk11_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall esk32_1:set -> set,
 forall k1_xboole_0:set,
 forall esk8_0:set,
 forall esk9_0:set,
 forall esk10_1:set -> set,
 forall esk1_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall v11_aff_2:set -> prop,
 forall esk31_1:set -> set,
 forall esk12_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk13_1:set -> set,
 forall v2_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall esk20_1:set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall esk24_1:set -> set,
 forall esk21_1:set -> set,
 forall esk23_1:set -> set,
 forall esk25_1:set -> set,
 forall esk26_1:set -> set,
 forall esk22_1:set -> set,
 forall r2_aff_1:set -> set -> set -> set -> prop,
 forall epred1_1:set -> prop,
 forall v1_aff_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall esk30_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall esk27_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall esk28_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
 forall epred2_7:set -> set -> set -> set -> set -> set -> set -> prop,
     (forall X1 X3 X4 X6 X7 X5 X2, (epred2_7 X1 X7 X2 X3 X5 X4 X6 -> False) -> r2_analoaf X1 X2 X3 (esk27_7 X4 X5 X3 X2 X6 X7 X1) (esk28_7 X4 X5 X3 X2 X6 X7 X1) -> False)
  -> (forall X2 X4 X7 X6 X5 X3 X1, (epred2_7 X7 X6 X4 X3 X2 X1 X5 -> False) -> r2_hidden (esk28_7 X1 X2 X3 X4 X5 X6 X7) (esk29_7 X1 X2 X3 X4 X5 X6 X7) -> False)
  -> (forall X2 X4 X7 X6 X5 X3 X1, (epred2_7 X7 X6 X4 X3 X2 X1 X5 -> False) -> r2_hidden (esk27_7 X1 X2 X3 X4 X5 X6 X7) (esk30_7 X1 X2 X3 X4 X5 X6 X7) -> False)
  -> (forall X1 X2 X4 X6 X7 X5 X3, (epred2_7 X1 X7 X5 X4 X3 X2 X6 -> False) -> (r5_aff_1 X1 (esk29_7 X2 X3 X4 X5 X6 X7 X1) (esk30_7 X2 X3 X4 X5 X6 X7 X1) -> False) -> False)
  -> (forall X2 X4 X7 X6 X5 X3 X1, (epred2_7 X7 X6 X4 X3 X2 X1 X5 -> False) -> (r2_hidden (esk28_7 X1 X2 X3 X4 X5 X6 X7) (esk30_7 X1 X2 X3 X4 X5 X6 X7) -> False) -> False)
  -> (forall X2 X4 X7 X6 X5 X3 X1, (epred2_7 X7 X6 X4 X3 X2 X1 X5 -> False) -> (r2_hidden (esk27_7 X1 X2 X3 X4 X5 X6 X7) (esk29_7 X1 X2 X3 X4 X5 X6 X7) -> False) -> False)
  -> (forall X1 X2 X4 X6 X7 X5 X3, (epred2_7 X7 X1 X5 X4 X3 X2 X6 -> False) -> r2_hidden X1 (esk30_7 X2 X3 X4 X5 X6 X1 X7) -> False)
  -> (forall X1 X2 X4 X5 X6 X7 X3, (epred2_7 X7 X6 X1 X4 X3 X2 X5 -> False) -> r2_hidden X1 (esk30_7 X2 X3 X4 X1 X5 X6 X7) -> False)
  -> (forall X1 X2 X5 X6 X7 X4 X3, (epred2_7 X7 X6 X4 X1 X3 X2 X5 -> False) -> r2_hidden X1 (esk29_7 X2 X3 X1 X4 X5 X6 X7) -> False)
  -> (forall X1 X2 X3 X5 X6 X7 X4, (epred2_7 X7 X6 X4 X3 X1 X2 X5 -> False) -> r2_hidden X1 (esk30_7 X2 X1 X3 X4 X5 X6 X7) -> False)
  -> (forall X1 X3 X5 X6 X7 X4 X2, (epred2_7 X7 X6 X4 X3 X2 X1 X5 -> False) -> r2_hidden X1 (esk29_7 X1 X2 X3 X4 X5 X6 X7) -> False)
  -> (forall X1 X2 X4 X6 X7 X5 X3, (epred2_7 X7 X6 X5 X4 X3 X2 X1 -> False) -> r2_hidden X1 (esk29_7 X2 X3 X4 X5 X1 X6 X7) -> False)
  -> (forall X1 X3 X6 X7 X5 X4 X2, (epred2_7 X1 X7 X2 X6 X5 X4 X3 -> False) -> (r2_analoaf X1 X2 X3 (esk27_7 X4 X5 X6 X2 X3 X7 X1) X4 -> False) -> False)
  -> (forall X1 X3 X6 X7 X5 X4 X2, (epred2_7 X1 X2 X6 X3 X4 X5 X7 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk28_7 X5 X4 X3 X6 X7 X2 X1) -> False) -> False)
  -> (forall X7 X2 X4 X6 X5 X3 X1, (epred2_7 X7 X6 X4 X3 X2 X1 X5 -> False) -> (m1_subset_1 (esk30_7 X1 X2 X3 X4 X5 X6 X7) (k1_zfmisc_1 (u1_struct_0 X7)) -> False) -> False)
  -> (forall X7 X2 X4 X6 X5 X3 X1, (epred2_7 X7 X6 X4 X3 X2 X1 X5 -> False) -> (m1_subset_1 (esk29_7 X1 X2 X3 X4 X5 X6 X7) (k1_zfmisc_1 (u1_struct_0 X7)) -> False) -> False)
  -> (forall X7 X2 X4 X6 X5 X3 X1, (epred2_7 X7 X6 X4 X3 X2 X1 X5 -> False) -> (m1_subset_1 (esk28_7 X1 X2 X3 X4 X5 X6 X7) (u1_struct_0 X7) -> False) -> False)
  -> (forall X7 X2 X4 X6 X5 X3 X1, (epred2_7 X7 X6 X4 X3 X2 X1 X5 -> False) -> (m1_subset_1 (esk27_7 X1 X2 X3 X4 X5 X6 X7) (u1_struct_0 X7) -> False) -> False)
  -> (forall X1 X2 X4 X6 X7 X5 X3, (epred2_7 X7 X1 X5 X4 X3 X2 X6 -> False) -> (r2_hidden X1 (esk29_7 X2 X3 X4 X5 X6 X1 X7) -> False) -> False)
  -> (forall X1 X2 X4 X5 X6 X7 X3, (epred2_7 X7 X6 X1 X4 X3 X2 X5 -> False) -> (r2_hidden X1 (esk29_7 X2 X3 X4 X1 X5 X6 X7) -> False) -> False)
  -> (forall X1 X2 X5 X6 X7 X4 X3, (epred2_7 X7 X6 X4 X1 X3 X2 X5 -> False) -> (r2_hidden X1 (esk30_7 X2 X3 X1 X4 X5 X6 X7) -> False) -> False)
  -> (forall X1 X2 X3 X5 X6 X7 X4, (epred2_7 X7 X6 X4 X3 X1 X2 X5 -> False) -> (r2_hidden X1 (esk29_7 X2 X1 X3 X4 X5 X6 X7) -> False) -> False)
  -> (forall X1 X3 X5 X6 X7 X4 X2, (epred2_7 X7 X6 X4 X3 X2 X1 X5 -> False) -> (r2_hidden X1 (esk30_7 X1 X2 X3 X4 X5 X6 X7) -> False) -> False)
  -> (forall X1 X2 X4 X6 X7 X5 X3, (epred2_7 X7 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden X1 (esk30_7 X2 X3 X4 X5 X1 X6 X7) -> False) -> False)
  -> (forall X11 X8 X6 X4 X2 X1 X3 X5 X7 X9 X10, (r2_hidden X9 X10 -> False) -> (r2_hidden X8 X11 -> False) -> (r2_hidden X7 X10 -> False) -> (r2_hidden X6 X10 -> False) -> (r2_hidden X5 X11 -> False) -> (r2_hidden X4 X10 -> False) -> (r2_hidden X3 X11 -> False) -> (r2_hidden X2 X11 -> False) -> (r2_analoaf X1 X3 X4 X8 X9 -> False) -> r2_hidden X9 X11 -> r2_hidden X8 X10 -> r2_hidden X7 X11 -> r2_hidden X6 X11 -> r2_hidden X5 X10 -> r2_hidden X4 X11 -> r2_hidden X3 X10 -> r2_hidden X2 X10 -> r5_aff_1 X1 X10 X11 -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> r2_analoaf X1 X7 X2 X6 X5 -> r2_analoaf X1 X3 X7 X8 X6 -> r2_analoaf X1 X2 X4 X5 X9 -> m1_subset_1 X11 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X10 (k1_zfmisc_1 (u1_struct_0 X1)) -> epred2_7 X1 X2 X3 X4 X5 X6 X7 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_conmetr1 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> epred2_7 X1 (esk2_1 X1) (esk4_1 X1) (esk5_1 X1) (esk6_1 X1) (esk7_1 X1) (esk3_1 X1) -> False)
  -> (forall X7 X6 X2 X5 X4 X3 X1, (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (epred2_7 X1 X3 X6 X7 X5 X4 X2 -> False) -> False)
  -> (forall X7 X5 X2 X3 X4 X6 X1, (v7_struct_0 X1 -> False) -> (epred2_7 X1 X2 X4 X5 X6 X7 X3 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_conmetr1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X5 X8 X6 X10 X9 X7 X1 X2 X4, (X2 = X4 -> False) -> (X2 = X3 -> False) -> (r2_analoaf X1 X6 X7 X9 X10 -> False) -> epred1_1 X1 -> r2_hidden X10 X4 -> r2_hidden X9 X3 -> r2_hidden X8 X2 -> r2_hidden X7 X4 -> r2_hidden X6 X3 -> r2_hidden X5 X2 -> v1_aff_1 X4 X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> r5_aff_1 X1 X2 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> r2_analoaf X1 X5 X7 X8 X10 -> r2_analoaf X1 X5 X6 X8 X9 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X5 X3 X4, (X3 = X4 -> False) -> (r2_analoaf X1 X2 X3 X3 (esk38_5 X1 X3 X2 X4 X5) -> False) -> epred3_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X3 X3 X5 -> False)
  -> (forall X1 X4 X2 X3 X5, (X3 = X5 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk38_5 X1 X5 X2 X3 X4) -> False) -> epred3_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X5 X5 X4 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X2 X3 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X4 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X5 X6 X7 X4 X2 X3, (X2 = X3 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> epred3_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X3 X5 X2 X4, (X2 = X4 -> False) -> (m1_subset_1 (esk38_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> epred3_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X2 X2 X5 -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (r1_aff_1 X1 X2 X3 (esk17_5 X1 X2 X3 X4 X5) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X2 X3 -> False) -> (r1_aff_1 X1 X2 X3 (esk17_5 X1 X4 X5 X2 X3) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> (m1_subset_1 (esk17_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X6 X5 X7 X3 X4 X2 X1, (r2_analoaf X1 X3 X2 X3 X4 -> False) -> epred3_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X2 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X3 X2 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X3 X2 -> False)
  -> (forall X1 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_aff_1 X1 X4 X5 X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_aff_1 X1 X2 X3 X6 -> r2_analoaf X1 X2 X3 X4 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X2 X4 -> False)
  -> (forall X3 X4 X5 X2 X6 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X6 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_aff_1 X1 X4 X5 X6 -> r2_aff_1 X1 X2 X3 X6 -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, epred3_1 X1 -> r2_analoaf X1 (esk33_1 X1) (esk34_1 X1) (esk33_1 X1) (esk35_1 X1) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> r2_analoaf X1 (esk22_1 X1) (esk23_1 X1) (esk25_1 X1) (esk26_1 X1) -> False)
  -> (forall X4 X3 X2 X1, (r2_analoaf X1 X2 X3 X4 (esk37_4 X1 X2 X3 X4) -> False) -> epred3_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r2_analoaf X1 X2 X3 X4 (esk37_4 X1 X2 X4 X3) -> False) -> epred3_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r2_analoaf X1 X2 X3 X4 (esk36_4 X1 X2 X4 X3) -> False) -> epred3_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X3 X4 X5 X2 X6 X7 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X7 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X6 -> r3_aff_1 X1 X6 X7 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X6 X4 X5 X7 X2 X3 X1, (r2_analoaf X1 X2 X3 X3 X2 -> False) -> epred3_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X6 X5 X7 X2 X3 X4 X1, (r2_analoaf X1 X2 X3 X4 X4 -> False) -> epred3_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (r2_analoaf X1 (esk21_1 X1) (esk23_1 X1) (esk24_1 X1) (esk26_1 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (r2_analoaf X1 (esk21_1 X1) (esk22_1 X1) (esk24_1 X1) (esk25_1 X1) -> False) -> False)
  -> (forall X1 X2 X5 X3 X4, (X3 = X4 -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden X3 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X2 X5 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> r2_aff_1 X1 X3 X4 X5 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X1 X2 X3 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 (esk14_3 X1 X2 X3) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X5 X6 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X3 X2 -> False)
  -> (forall X4 X1 X2 X3 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk14_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X5 X6 -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X2 -> False) -> (esk14_3 X2 X1 X3) = X1 -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X6 (u1_struct_0 X2) -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X4 X5 X6 -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X2 -> False) -> (esk14_3 X2 X3 X1) = X1 -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X6 (u1_struct_0 X2) -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X4 X5 X6 -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X5 -> r2_hidden X2 X5 -> v1_aff_1 X5 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X2 X1, (m1_subset_1 (esk37_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> epred3_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (m1_subset_1 (esk36_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> epred3_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_aff_1 X1 X2 X3 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X4 -> r2_hidden X2 X4 -> r3_aff_1 X1 X4 X5 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X1 X2, (esk36_4 X2 X3 X1 X4) = X1 -> epred3_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X2 X4 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X3 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X4 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X4 X3 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X4 X2 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 (esk16_3 X1 X3 X2) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk16_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk15_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v7_struct_0 X1 -> False) -> (r2_hidden (esk15_3 X1 X2 X3) X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk16_3 X2 X1 X3) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> v1_aff_1 X3 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (v1_aff_1 X1 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r3_aff_1 X2 X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (v1_aff_1 X1 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r3_aff_1 X2 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (v7_struct_0 X2 -> False) -> (esk15_3 X2 X1 X3) = X1 -> v1_diraf X2 -> l1_analoaf X2 -> v1_aff_1 X3 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X2 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (r5_aff_1 X1 (esk18_1 X1) (esk20_1 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (r5_aff_1 X1 (esk18_1 X1) (esk19_1 X1) -> False) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_conmetr1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_conmetr1 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_conmetr1 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_conmetr1 X1 -> False) -> (m1_subset_1 (esk4_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_conmetr1 X1 -> False) -> (m1_subset_1 (esk3_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_conmetr1 X1 -> False) -> (m1_subset_1 (esk2_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (m1_subset_1 (esk35_1 X1) (u1_struct_0 X1) -> False) -> epred3_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk34_1 X1) (u1_struct_0 X1) -> False) -> epred3_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk33_1 X1) (u1_struct_0 X1) -> False) -> epred3_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk32_1 X1) (u1_struct_0 X1) -> False) -> epred3_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk31_1 X1) (u1_struct_0 X1) -> False) -> epred3_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (u1_struct_0 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (u1_struct_0 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (u1_struct_0 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (u1_struct_0 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (u1_struct_0 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (u1_struct_0 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (r2_hidden (esk26_1 X1) (esk20_1 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (r2_hidden (esk25_1 X1) (esk19_1 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (r2_hidden (esk24_1 X1) (esk18_1 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (r2_hidden (esk23_1 X1) (esk20_1 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (r2_hidden (esk22_1 X1) (esk19_1 X1) -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (r2_hidden (esk21_1 X1) (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (epred1_1 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v11_aff_2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v11_aff_2 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk11_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk12_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (v1_aff_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (v1_aff_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (v1_aff_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (epred3_1 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk11_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (esk32_1 X1) = (esk31_1 X1) -> epred3_1 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (esk20_1 X1) = (esk18_1 X1) -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> (esk19_1 X1) = (esk18_1 X1) -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (v1_conmetr1 esk1_0 -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((l1_struct_0 esk9_0 -> False) -> False)
  -> ((v11_aff_2 esk1_0 -> False) -> False)
  -> ((l1_analoaf esk8_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v2_diraf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
