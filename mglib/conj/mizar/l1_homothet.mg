(** $I sig/MizarPreamble.mgs **)

Theorem l1_homothet:
 forall esk25_6:set -> set -> set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall v1_aff_1:set -> set -> prop,
 forall esk1_0:set,
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall esk5_0:set,
 forall esk8_0:set,
 forall esk6_0:set,
 forall esk7_0:set,
 forall esk2_0:set,
 forall k1_aff_1:set -> set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk19_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k1_xboole_0:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk18_1:set -> set,
 forall esk17_0:set,
 forall v2_diraf:set -> prop,
 forall esk16_0:set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk20_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk21_1:set -> set,
 forall v2_struct_0:set -> prop,
 forall k2_aff_1:set -> set -> set -> set,
 forall esk22_4:set -> set -> set -> set -> set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall k1_zfmisc_1:set -> set,
 forall v4_aff_2:set -> prop,
 forall l1_analoaf:set -> prop,
 forall esk11_1:set -> set,
 forall esk13_1:set -> set,
 forall esk14_1:set -> set,
 forall esk15_1:set -> set,
 forall esk12_1:set -> set,
 forall v1_diraf:set -> prop,
 forall v7_struct_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk24_6:set -> set -> set -> set -> set -> set -> set,
 forall esk26_6:set -> set -> set -> set -> set -> set -> set,
 forall esk27_6:set -> set -> set -> set -> set -> set -> set,
 forall esk23_6:set -> set -> set -> set -> set -> set -> set,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
 forall epred1_6:set -> set -> set -> set -> set -> set -> prop,
     (forall X1 X2 X4 X6 X5 X3, (epred1_6 X1 X6 X5 X4 X3 X2 -> False) -> r2_analoaf X1 (esk23_6 X2 X3 X4 X5 X6 X1) (esk24_6 X2 X3 X4 X5 X6 X1) (esk26_6 X2 X3 X4 X5 X6 X1) (esk27_6 X2 X3 X4 X5 X6 X1) -> False)
  -> (forall X1 X3 X5 X6 X4 X2, (epred1_6 X1 X6 X5 X4 X3 X2 -> False) -> (r2_analoaf X1 X2 (esk24_6 X2 X3 X4 X5 X6 X1) (esk25_6 X2 X3 X4 X5 X6 X1) (esk27_6 X2 X3 X4 X5 X6 X1) -> False) -> False)
  -> (forall X1 X3 X5 X6 X4 X2, (epred1_6 X1 X6 X5 X4 X3 X2 -> False) -> (r2_analoaf X1 X2 (esk23_6 X2 X3 X4 X5 X6 X1) (esk25_6 X2 X3 X4 X5 X6 X1) (esk26_6 X2 X3 X4 X5 X6 X1) -> False) -> False)
  -> (forall X6 X2 X4 X5 X3 X1, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X6) -> False) -> False)
  -> (forall X6 X2 X4 X5 X3 X1, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk26_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X6) -> False) -> False)
  -> (forall X6 X2 X4 X5 X3 X1, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk25_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X6) -> False) -> False)
  -> (forall X6 X2 X4 X5 X3 X1, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk24_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X6) -> False) -> False)
  -> (forall X6 X2 X4 X5 X3 X1, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk23_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X6) -> False) -> False)
  -> (forall X3 X2 X4 X5 X6 X1, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk27_6 X1 X2 X3 X4 X5 X6) X3 -> False) -> False)
  -> (forall X4 X2 X5 X6 X3 X1, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk26_6 X1 X2 X3 X4 X5 X6) X4 -> False) -> False)
  -> (forall X5 X2 X4 X6 X3 X1, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk25_6 X1 X2 X3 X4 X5 X6) X5 -> False) -> False)
  -> (forall X3 X2 X4 X5 X6 X1, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk24_6 X1 X2 X3 X4 X5 X6) X3 -> False) -> False)
  -> (forall X4 X2 X5 X6 X3 X1, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk23_6 X1 X2 X3 X4 X5 X6) X4 -> False) -> False)
  -> (forall X1 X4 X5 X6 X3 X2, (epred1_6 X6 X5 X4 X3 X1 X2 -> False) -> (esk24_6 X2 X1 X3 X4 X5 X6) = X1 -> False)
  -> (forall X1 X4 X5 X6 X3 X2, (epred1_6 X6 X5 X4 X3 X1 X2 -> False) -> (esk23_6 X2 X1 X3 X4 X5 X6) = X1 -> False)
  -> (forall X7 X4 X2 X1 X10 X11 X9 X3 X6 X5 X8, (X5 = X8 -> False) -> (X5 = X7 -> False) -> (X5 = X6 -> False) -> (X2 = X4 -> False) -> (X2 = X3 -> False) -> (r2_analoaf X1 X7 X8 X10 X11 -> False) -> r2_hidden X11 X4 -> r2_hidden X10 X3 -> r2_hidden X9 X2 -> r2_hidden X8 X4 -> r2_hidden X7 X3 -> r2_hidden X6 X2 -> r2_hidden X5 X4 -> r2_hidden X5 X3 -> r2_hidden X5 X2 -> v1_aff_1 X4 X1 -> v1_aff_1 X3 X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X11 (u1_struct_0 X1) -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> r2_analoaf X1 X6 X8 X9 X11 -> r2_analoaf X1 X6 X7 X9 X10 -> epred1_6 X1 X2 X3 X4 X5 X6 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> epred1_6 X1 (esk11_1 X1) (esk12_1 X1) (esk13_1 X1) (esk14_1 X1) (esk15_1 X1) -> False)
  -> (forall X6 X2 X1 X5 X7 X3 X4, (v4_aff_2 esk1_0 -> False) -> (r1_aff_1 esk1_0 X1 X2 X6 -> False) -> (r1_aff_1 esk1_0 X1 X2 X4 -> False) -> (r2_analoaf esk1_0 X4 X6 X5 X7 -> False) -> m1_subset_1 X7 (u1_struct_0 esk1_0) -> m1_subset_1 X6 (u1_struct_0 esk1_0) -> m1_subset_1 X5 (u1_struct_0 esk1_0) -> m1_subset_1 X4 (u1_struct_0 esk1_0) -> m1_subset_1 X3 (u1_struct_0 esk1_0) -> m1_subset_1 X2 (u1_struct_0 esk1_0) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> r1_aff_1 esk1_0 X1 X6 X7 -> r1_aff_1 esk1_0 X1 X4 X5 -> r1_aff_1 esk1_0 X1 X2 X3 -> r2_analoaf esk1_0 X2 X6 X3 X7 -> r2_analoaf esk1_0 X2 X4 X3 X5 -> False)
  -> (forall X5 X2 X3 X4 X6 X1, (v7_struct_0 X1 -> False) -> (epred1_6 X1 X2 X3 X4 X5 X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v4_aff_2 X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X5 X6 X3 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_6 X2 X1 X3 X4 X5 X6 -> False) -> False)
  -> (forall X3 X4 X5 X6 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_6 X2 X3 X1 X4 X5 X6 -> False) -> False)
  -> (forall X3 X5 X6 X4 X1 X2, (v1_aff_1 X1 X2 -> False) -> (epred1_6 X2 X3 X4 X1 X5 X6 -> False) -> False)
  -> (forall X5 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_6 X3 X2 X4 X5 X1 X6 -> False) -> False)
  -> (forall X5 X6 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_6 X3 X2 X4 X5 X6 X1 -> False) -> False)
  -> (forall X4 X5 X6 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_6 X3 X4 X2 X5 X1 X6 -> False) -> False)
  -> (forall X4 X6 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> (epred1_6 X3 X4 X5 X2 X1 X6 -> False) -> False)
  -> (forall X3 X6 X5 X4 X2 X1, (epred1_6 X3 X1 X2 X4 X5 X6 -> False) -> X1 = X2 -> False)
  -> (forall X3 X4 X6 X5 X2 X1, (epred1_6 X3 X1 X4 X2 X5 X6 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X6 X4 X2 X1, (epred1_6 X3 X4 X5 X6 X1 X2 -> False) -> X1 = X2 -> False)
  -> (v4_aff_2 esk1_0 -> r2_analoaf esk1_0 esk5_0 esk7_0 esk6_0 esk8_0 -> False)
  -> ((r2_analoaf esk1_0 esk3_0 esk7_0 esk4_0 esk8_0 -> False) -> v4_aff_2 esk1_0 -> False)
  -> ((r2_analoaf esk1_0 esk3_0 esk5_0 esk4_0 esk6_0 -> False) -> v4_aff_2 esk1_0 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk22_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (v1_aff_1 (esk22_4 X1 X2 X3 X4) X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk22_4 X2 X1 X3 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X1 X3 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk22_4 X2 X3 X1 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X1 X4 -> False)
  -> (forall X4 X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (esk22_4 X2 X3 X4 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X3 X4 X1 -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X5 -> r2_hidden X2 X5 -> v1_aff_1 X5 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X5 X4 X3 X1 X2, (v7_struct_0 X2 -> False) -> (r1_aff_1 X2 X3 X4 X5 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> r2_hidden X5 X1 -> r2_hidden X4 X1 -> r2_hidden X3 X1 -> v1_aff_1 X1 X2 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (v4_aff_2 esk1_0 -> r1_aff_1 esk1_0 esk2_0 esk3_0 esk7_0 -> False)
  -> (v4_aff_2 esk1_0 -> r1_aff_1 esk1_0 esk2_0 esk3_0 esk5_0 -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1 X4 X5, (X4 = X5 -> False) -> (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> r2_hidden X3 X5 -> r2_hidden X3 X4 -> r2_hidden X2 X5 -> r2_hidden X2 X4 -> v1_aff_1 X5 X1 -> v1_aff_1 X4 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> ((r1_aff_1 esk1_0 esk2_0 esk7_0 esk8_0 -> False) -> v4_aff_2 esk1_0 -> False)
  -> ((r1_aff_1 esk1_0 esk2_0 esk5_0 esk6_0 -> False) -> v4_aff_2 esk1_0 -> False)
  -> ((r1_aff_1 esk1_0 esk2_0 esk3_0 esk4_0 -> False) -> v4_aff_2 esk1_0 -> False)
  -> (forall X2 X4 X1 X3, (X1 = X3 -> False) -> (v7_struct_0 X2 -> False) -> (v1_aff_1 X4 X2 -> False) -> X4 = (k2_aff_1 X2 X1 X3) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k1_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k2_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (k2_aff_1 X2 X1 X3) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X3 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X1 (k2_aff_1 X2 X3 X1) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X2, ((k2_aff_1 X2 (esk9_2 X2 X1) (esk10_2 X2 X1)) = X1 -> False) -> (v7_struct_0 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> v1_aff_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, ((k1_aff_1 X1 X2 X3) = (k2_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k2_aff_1 X1 X2 X3) = (k2_aff_1 X1 X3 X2) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk10_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk9_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (esk10_2 X1 X2) = (esk9_2 X1 X2) -> v1_diraf X1 -> l1_analoaf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
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
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk20_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk19_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> ((m1_subset_1 esk8_0 (u1_struct_0 esk1_0) -> False) -> v4_aff_2 esk1_0 -> False)
  -> ((m1_subset_1 esk7_0 (u1_struct_0 esk1_0) -> False) -> v4_aff_2 esk1_0 -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk1_0) -> False) -> v4_aff_2 esk1_0 -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> v4_aff_2 esk1_0 -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> v4_aff_2 esk1_0 -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> v4_aff_2 esk1_0 -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> v4_aff_2 esk1_0 -> False)
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
  -> (v1_xboole_0 np__1 -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((l1_struct_0 esk17_0 -> False) -> False)
  -> ((l1_analoaf esk16_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v2_diraf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
