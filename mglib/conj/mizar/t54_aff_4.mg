(** $I sig/MizarPreamble.mgs **)

Theorem t54_aff_4:
 forall v1_aff_1:set -> set -> prop,
 forall epred1_7:set -> set -> set -> set -> set -> set -> set -> prop,
 forall k2_aff_1:set -> set -> set -> set,
 forall r3_aff_1:set -> set -> set -> prop,
 forall esk20_4:set -> set -> set -> set -> set,
 forall esk26_4:set -> set -> set -> set -> set,
 forall esk27_3:set -> set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk16_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall esk11_1:set -> set,
 forall esk9_0:set,
 forall esk10_0:set,
 forall esk14_0:set,
 forall esk17_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall k1_xboole_0:set,
 forall esk15_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall k1_aff_1:set -> set -> set -> set,
 forall k2_aff_4:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk21_4:set -> set -> set -> set -> set,
 forall esk22_3:set -> set -> set -> set,
 forall esk25_3:set -> set -> set -> set,
 forall esk24_3:set -> set -> set -> set,
 forall esk23_3:set -> set -> set -> set,
 forall esk6_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk5_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk19_5:set -> set -> set -> set -> set -> set,
 forall epred2_2:set -> set -> prop,
 forall esk13_6:set -> set -> set -> set -> set -> set -> set,
 forall r5_aff_1:set -> set -> set -> prop,
 forall esk28_6:set -> set -> set -> set -> set -> set -> set,
 forall v2_diraf:set -> prop,
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall v1_diraf:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v1_aff_4:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall l1_analoaf:set -> prop,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
 forall esk12_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall v7_struct_0:set -> prop,
     (forall X3 X5 X2 X4 X6 X7 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X5 X3 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk12_7 X1 X2 X5 X3 X4 X6 X7) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X7 -> r2_hidden X4 X7 -> r2_hidden X3 X7 -> r2_hidden X2 X7 -> v1_aff_4 X7 X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X5 X4 X6 -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X5 X4 X6 X7 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X5 X2 X3 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk12_7 X1 X5 X2 X3 X6 X4 X7) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X6 X7 -> r2_hidden X5 X7 -> r2_hidden X3 X7 -> r2_hidden X2 X7 -> v1_aff_4 X7 X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X2 X6 X4 -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X2 X6 X5 X7 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk12_7 X1 X2 X3 X4 X5 X6 X7) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X7 -> r2_hidden X4 X7 -> r2_hidden X3 X7 -> r2_hidden X2 X7 -> v1_aff_4 X7 X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X5 X6 -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X7 X4 X1 X9 X10 X11 X3 X2 X5 X6 X8, (X6 = X8 -> False) -> (X6 = X7 -> False) -> (X2 = X5 -> False) -> (X2 = X4 -> False) -> (X2 = X3 -> False) -> (r2_analoaf X1 X4 X5 X9 X10 -> False) -> v7_struct_0 X1 -> r2_hidden X11 X6 -> r2_hidden X10 X8 -> r2_hidden X9 X7 -> r2_hidden X5 X8 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X8 -> r2_hidden X2 X7 -> r2_hidden X2 X6 -> v1_aff_1 X8 X1 -> v1_aff_1 X7 X1 -> v1_aff_1 X6 X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> r2_analoaf X1 X3 X5 X11 X10 -> r2_analoaf X1 X3 X4 X11 X9 -> m1_subset_1 X8 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> epred1_7 X1 X3 X4 X5 X9 X11 X2 -> False)
  -> (forall X7 X4 X1 X11 X10 X9 X3 X2 X5 X6 X8, (X6 = X8 -> False) -> (X6 = X7 -> False) -> (X2 = X5 -> False) -> (X2 = X4 -> False) -> (X2 = X3 -> False) -> (v2_diraf X1 -> False) -> (r2_analoaf X1 X4 X5 X9 X10 -> False) -> r2_hidden X11 X6 -> r2_hidden X10 X8 -> r2_hidden X9 X7 -> r2_hidden X5 X8 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X8 -> r2_hidden X2 X7 -> r2_hidden X2 X6 -> v1_aff_1 X8 X1 -> v1_aff_1 X7 X1 -> v1_aff_1 X6 X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> r2_analoaf X1 X3 X5 X11 X10 -> r2_analoaf X1 X3 X4 X11 X9 -> m1_subset_1 X8 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> epred1_7 X1 X3 X4 X5 X9 X11 X2 -> False)
  -> (forall X7 X4 X1 X11 X10 X9 X3 X2 X5 X6 X8, (X6 = X8 -> False) -> (X6 = X7 -> False) -> (X2 = X5 -> False) -> (X2 = X4 -> False) -> (X2 = X3 -> False) -> (l1_analoaf X1 -> False) -> (r2_analoaf X1 X4 X5 X9 X10 -> False) -> r2_hidden X11 X6 -> r2_hidden X10 X8 -> r2_hidden X9 X7 -> r2_hidden X5 X8 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X8 -> r2_hidden X2 X7 -> r2_hidden X2 X6 -> v1_aff_1 X8 X1 -> v1_aff_1 X7 X1 -> v1_aff_1 X6 X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> r2_analoaf X1 X3 X5 X11 X10 -> r2_analoaf X1 X3 X4 X11 X9 -> m1_subset_1 X8 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> epred1_7 X1 X3 X4 X5 X9 X11 X2 -> False)
  -> (forall X7 X4 X1 X11 X10 X9 X3 X2 X5 X6 X8, (X6 = X8 -> False) -> (X6 = X7 -> False) -> (X2 = X5 -> False) -> (X2 = X4 -> False) -> (X2 = X3 -> False) -> (v1_diraf X1 -> False) -> (r2_analoaf X1 X4 X5 X9 X10 -> False) -> r2_hidden X11 X6 -> r2_hidden X10 X8 -> r2_hidden X9 X7 -> r2_hidden X5 X8 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X8 -> r2_hidden X2 X7 -> r2_hidden X2 X6 -> v1_aff_1 X8 X1 -> v1_aff_1 X7 X1 -> v1_aff_1 X6 X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> r2_analoaf X1 X3 X5 X11 X10 -> r2_analoaf X1 X3 X4 X11 X9 -> m1_subset_1 X8 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> epred1_7 X1 X3 X4 X5 X9 X11 X2 -> False)
  -> (forall X7 X5 X2 X3 X4 X6 X1, (v7_struct_0 X1 -> False) -> (epred1_7 X1 X3 X4 X5 X7 X6 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X5 X2 X6 X4 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X5 X3 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk28_6 X1 X2 X5 X3 X4 X6) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v2_diraf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X5 X6 X4 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X5 X2 X3 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk28_6 X1 X5 X2 X3 X6 X4) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v2_diraf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X5 X4 X2 X3 X6 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk13_6 X1 X2 X4 X3 X5 X6) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X4 X5 -> r2_hidden X3 X6 -> r2_hidden X2 X5 -> r5_aff_1 X1 X5 X6 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X2 X6 X5 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk28_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v2_diraf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X6 X4 X2 X3 X5 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk13_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X4 X6 -> r2_hidden X3 X5 -> r2_hidden X2 X5 -> r5_aff_1 X1 X5 X6 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X6 X4 X2 X3 X5 X1, (v7_struct_0 X1 -> False) -> (r2_hidden (esk13_6 X1 X2 X3 X4 X5 X6) X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X4 X6 -> r2_hidden X3 X5 -> r2_hidden X2 X5 -> r5_aff_1 X1 X5 X6 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X9 X10 X5 X8 X7 X6 X1 X2 X4, (X2 = X4 -> False) -> (X2 = X3 -> False) -> (r2_analoaf X1 X5 X6 X7 X8 -> False) -> v7_struct_0 X1 -> r2_hidden X10 X2 -> r2_hidden X9 X2 -> r2_hidden X8 X4 -> r2_hidden X7 X3 -> r2_hidden X6 X4 -> r2_hidden X5 X3 -> v1_aff_1 X4 X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> epred2_2 X1 X9 -> r5_aff_1 X1 X2 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> r2_analoaf X1 X9 X6 X10 X8 -> r2_analoaf X1 X9 X5 X10 X7 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X6 X7 X8 X5 X9 X10 X1 X2 X4, (X2 = X4 -> False) -> (X2 = X3 -> False) -> (v2_diraf X1 -> False) -> (r2_analoaf X1 X5 X6 X7 X8 -> False) -> r2_hidden X10 X2 -> r2_hidden X9 X2 -> r2_hidden X8 X4 -> r2_hidden X7 X3 -> r2_hidden X6 X4 -> r2_hidden X5 X3 -> v1_aff_1 X4 X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> epred2_2 X1 X9 -> r5_aff_1 X1 X2 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> r2_analoaf X1 X9 X6 X10 X8 -> r2_analoaf X1 X9 X5 X10 X7 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X6 X7 X8 X5 X9 X10 X1 X2 X4, (X2 = X4 -> False) -> (X2 = X3 -> False) -> (l1_analoaf X1 -> False) -> (r2_analoaf X1 X5 X6 X7 X8 -> False) -> r2_hidden X10 X2 -> r2_hidden X9 X2 -> r2_hidden X8 X4 -> r2_hidden X7 X3 -> r2_hidden X6 X4 -> r2_hidden X5 X3 -> v1_aff_1 X4 X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> epred2_2 X1 X9 -> r5_aff_1 X1 X2 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> r2_analoaf X1 X9 X6 X10 X8 -> r2_analoaf X1 X9 X5 X10 X7 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X6 X7 X8 X5 X9 X10 X1 X2 X4, (X2 = X4 -> False) -> (X2 = X3 -> False) -> (v1_diraf X1 -> False) -> (r2_analoaf X1 X5 X6 X7 X8 -> False) -> r2_hidden X10 X2 -> r2_hidden X9 X2 -> r2_hidden X8 X4 -> r2_hidden X7 X3 -> r2_hidden X6 X4 -> r2_hidden X5 X3 -> v1_aff_1 X4 X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> epred2_2 X1 X9 -> r5_aff_1 X1 X2 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> r2_analoaf X1 X9 X6 X10 X8 -> r2_analoaf X1 X9 X5 X10 X7 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X3 X2 X5, (X2 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk19_5 X1 X5 X2 X4 X3) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X5 X2 X4 -> False)
  -> (forall X1 X4 X3 X2 X5, (X2 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk19_5 X1 X5 X2 X4 X3) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X5 X4 X2 -> False)
  -> (forall X1, m1_subset_1 X1 (u1_struct_0 esk1_0) -> r2_analoaf esk1_0 esk2_0 esk4_0 esk5_0 X1 -> r2_analoaf esk1_0 esk3_0 esk4_0 esk6_0 X1 -> False)
  -> (forall X1 X3 X5 X2 X4, (X2 = X4 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 (esk19_5 X1 X2 X4 X5 X3) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X5 -> False)
  -> (forall X1 X3 X5 X2 X4, (X2 = X4 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 (esk19_5 X1 X2 X4 X5 X3) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X5 X4 -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk19_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk19_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X3 -> False)
  -> (forall X3 X1 X6 X7 X2 X4 X5, (X4 = X5 -> False) -> (X1 = X3 -> False) -> (v7_struct_0 X2 -> False) -> (r3_aff_1 X2 X6 X7 -> False) -> X7 = (k2_aff_1 X2 X4 X5) -> X6 = (k2_aff_1 X2 X1 X3) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r2_analoaf X2 X1 X3 X4 X5 -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 (esk22_3 X1 X2 X3) (esk23_3 X1 X2 X3) (esk24_3 X1 X2 X3) (esk25_3 X1 X2 X3) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk20_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (v1_aff_1 (esk20_4 X1 X2 X3 X4) X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk20_4 X2 X1 X3 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X1 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk20_4 X2 X3 X1 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X1 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk20_4 X2 X3 X4 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X4 X1 -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> (m1_subset_1 (esk21_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X4 X1 -> v1_aff_1 X3 X1 -> v1_aff_4 X2 X1 -> r1_tarski X4 X2 -> r1_tarski X3 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> (r2_hidden (esk21_4 X1 X2 X3 X4) X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X4 X1 -> v1_aff_1 X3 X1 -> v1_aff_4 X2 X1 -> r1_tarski X4 X2 -> r1_tarski X3 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X4 -> False) -> (r2_hidden (esk21_4 X1 X2 X3 X4) X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X4 X1 -> v1_aff_1 X3 X1 -> v1_aff_4 X2 X1 -> r1_tarski X4 X2 -> r1_tarski X3 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X3 X4 X5 X6, (X5 = X6 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X4 X6 -> r2_hidden X4 X5 -> r2_hidden X3 X6 -> r2_hidden X3 X5 -> r2_hidden X2 X6 -> r2_hidden X2 X5 -> v1_aff_4 X6 X1 -> v1_aff_4 X5 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X5 -> r2_hidden X2 X5 -> v1_aff_1 X5 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk26_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (v7_struct_0 X1 -> False) -> (v1_aff_4 (esk26_4 X1 X2 X3 X4) X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X1 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk26_4 X2 X1 X3 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X4 X3 X1 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk26_4 X2 X3 X1 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X4 X3 X1 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk26_4 X2 X3 X4 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X5 X4 X3 X1 X2, (v7_struct_0 X2 -> False) -> (r1_aff_1 X2 X3 X4 X5 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r2_hidden X5 X1 -> r2_hidden X4 X1 -> r2_hidden X3 X1 -> v1_aff_1 X1 X2 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((k2_aff_1 X2 (esk24_3 X2 X3 X1) (esk25_3 X2 X3 X1)) = X1 -> False) -> (v7_struct_0 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r3_aff_1 X2 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((k2_aff_1 X2 (esk22_3 X2 X1 X3) (esk23_3 X2 X1 X3)) = X1 -> False) -> (v7_struct_0 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r3_aff_1 X2 X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X4 X2 X3 X5 X1, (v7_struct_0 X1 -> False) -> (r1_tarski X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X4 -> r2_hidden X5 X2 -> v1_aff_4 X4 X1 -> r1_tarski X3 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r1_tarski X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X5 X4 -> r2_hidden X5 X3 -> v1_aff_4 X4 X1 -> r1_tarski X2 X4 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (esk25_3 X1 X2 X3) = (esk24_3 X1 X2 X3) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (esk23_3 X1 X2 X3) = (esk22_3 X1 X2 X3) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X4 X3, (X2 = (k2_aff_4 X3 X1 X4) -> False) -> (v7_struct_0 X3 -> False) -> v1_diraf X3 -> l1_analoaf X3 -> r2_hidden X1 X2 -> v1_aff_1 X4 X3 -> r5_aff_1 X3 X4 X2 -> m1_subset_1 X1 (u1_struct_0 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X3)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk25_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk24_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk23_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk22_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (v1_aff_4 (esk27_3 X1 X2 X3) X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (r1_tarski X1 (esk27_3 X2 X1 X3) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r5_aff_1 X2 X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (r1_tarski X1 (esk27_3 X2 X3 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r5_aff_1 X2 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1 X4 X5, (X4 = X5 -> False) -> (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X5 -> r2_hidden X3 X4 -> r2_hidden X2 X5 -> r2_hidden X2 X4 -> v1_aff_1 X5 X1 -> v1_aff_1 X4 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_tarski (k2_aff_1 X1 X2 X3) X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X4 -> r2_hidden X2 X4 -> v1_aff_4 X4 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X4 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> X3 = (k2_aff_4 X1 X4 X2) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X4 X3, (v7_struct_0 X3 -> False) -> (r2_hidden X1 X2 -> False) -> X2 = (k2_aff_4 X3 X1 X4) -> v1_diraf X3 -> l1_analoaf X3 -> v1_aff_1 X4 X3 -> m1_subset_1 X1 (u1_struct_0 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X3)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r3_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r5_aff_1 X1 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r5_aff_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X2 X3, (X2 = X3 -> False) -> (X4 = (k2_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X4 -> r2_hidden X2 X4 -> v1_aff_1 X4 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v7_struct_0 X1 -> False) -> (v1_aff_1 (k2_aff_4 X1 X2 X3) X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X3 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k2_aff_4 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X4 X1 X3, (X1 = X3 -> False) -> (v7_struct_0 X2 -> False) -> (v1_aff_1 X4 X2 -> False) -> X4 = (k2_aff_1 X2 X1 X3) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k1_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k2_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (k2_aff_1 X2 X1 X3) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (k2_aff_1 X2 X3 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X2, ((k2_aff_1 X2 (esk7_2 X2 X1) (esk8_2 X2 X1)) = X1 -> False) -> (v7_struct_0 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> v1_aff_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, ((k1_aff_1 X1 X2 X3) = (k2_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k2_aff_1 X1 X2 X3) = (k2_aff_1 X1 X3 X2) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk8_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk7_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (esk8_2 X1 X2) = (esk7_2 X1 X2) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (epred2_2 X1 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk16_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk15_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_aff_1 esk1_0 esk2_0 esk3_0 esk4_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (esk6_0 = esk5_0 -> False)
  -> ((r2_analoaf esk1_0 esk2_0 esk3_0 esk5_0 esk6_0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((l1_analoaf esk9_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
