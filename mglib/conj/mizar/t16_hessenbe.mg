(** $I sig/MizarPreamble.mgs **)

Theorem t16_hessenbe:
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall v2_struct_0:set -> prop,
 forall v2_collsp:set -> prop,
 forall v4_collsp:set -> prop,
 forall v3_anproj_2:set -> prop,
 forall esk12_1:set -> set,
 forall esk15_1:set -> set,
 forall esk13_1:set -> set,
 forall esk17_1:set -> set,
 forall esk16_1:set -> set,
 forall esk14_1:set -> set,
 forall esk11_1:set -> set,
 forall l1_collsp:set -> prop,
 forall v2_anproj_2:set -> prop,
 forall v3_collsp:set -> prop,
 forall v6_anproj_2:set -> prop,
 forall esk25_1:set -> set,
 forall esk1_0:set,
 forall esk8_0:set,
 forall esk9_0:set,
 forall esk10_0:set,
 forall esk29_0:set,
 forall esk6_0:set,
 forall esk26_0:set,
 forall esk27_0:set,
 forall esk28_1:set -> set,
 forall esk3_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk7_0:set,
 forall l1_struct_0:set -> prop,
 forall v5_anproj_2:set -> prop,
 forall esk21_1:set -> set,
 forall esk22_1:set -> set,
 forall esk19_1:set -> set,
 forall esk20_1:set -> set,
 forall esk23_1:set -> set,
 forall esk24_1:set -> set,
 forall esk18_5:set -> set -> set -> set -> set -> set,
 forall v7_anproj_2:set -> prop,
 forall esk32_8:set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall esk31_8:set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall esk30_8:set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall r1_collsp:set -> set -> set -> set -> prop,
 forall epred1_8:set -> set -> set -> set -> set -> set -> set -> set -> prop,
     (forall X1 X2 X4 X6 X8 X7 X5 X3, (epred1_8 X1 X8 X7 X5 X4 X3 X2 X6 -> False) -> r1_collsp X1 (esk30_8 X2 X3 X4 X5 X6 X7 X8 X1) (esk31_8 X2 X3 X4 X5 X6 X7 X8 X1) (esk32_8 X2 X3 X4 X5 X6 X7 X8 X1) -> False)
  -> (forall X1 X3 X4 X5 X7 X8 X6 X2, (epred1_8 X1 X8 X2 X6 X5 X3 X4 X7 -> False) -> (r1_collsp X1 X2 X3 (esk32_8 X4 X3 X5 X6 X7 X2 X8 X1) -> False) -> False)
  -> (forall X1 X3 X5 X7 X8 X6 X4 X2, (epred1_8 X1 X8 X2 X6 X5 X4 X3 X7 -> False) -> (r1_collsp X1 X2 X3 (esk31_8 X3 X4 X5 X6 X7 X2 X8 X1) -> False) -> False)
  -> (forall X1 X3 X4 X6 X8 X7 X5 X2, (epred1_8 X1 X8 X7 X2 X3 X5 X4 X6 -> False) -> (r1_collsp X1 X2 X3 (esk31_8 X4 X5 X3 X2 X6 X7 X8 X1) -> False) -> False)
  -> (forall X1 X3 X4 X5 X6 X8 X7 X2, (epred1_8 X1 X8 X7 X2 X5 X3 X4 X6 -> False) -> (r1_collsp X1 X2 X3 (esk30_8 X4 X3 X5 X2 X6 X7 X8 X1) -> False) -> False)
  -> (forall X1 X3 X4 X8 X7 X6 X5 X2, (epred1_8 X1 X8 X7 X6 X2 X5 X4 X3 -> False) -> (r1_collsp X1 X2 X3 (esk32_8 X4 X5 X2 X6 X3 X7 X8 X1) -> False) -> False)
  -> (forall X1 X3 X5 X8 X7 X6 X4 X2, (epred1_8 X1 X8 X7 X6 X5 X4 X3 X2 -> False) -> (r1_collsp X1 X2 X3 (esk30_8 X3 X4 X5 X6 X2 X7 X8 X1) -> False) -> False)
  -> (forall X8 X2 X4 X6 X7 X5 X3 X1, (epred1_8 X8 X7 X6 X4 X3 X2 X1 X5 -> False) -> (m1_subset_1 (esk32_8 X1 X2 X3 X4 X5 X6 X7 X8) (u1_struct_0 X8) -> False) -> False)
  -> (forall X8 X2 X4 X6 X7 X5 X3 X1, (epred1_8 X8 X7 X6 X4 X3 X2 X1 X5 -> False) -> (m1_subset_1 (esk31_8 X1 X2 X3 X4 X5 X6 X7 X8) (u1_struct_0 X8) -> False) -> False)
  -> (forall X8 X2 X4 X6 X7 X5 X3 X1, (epred1_8 X8 X7 X6 X4 X3 X2 X1 X5 -> False) -> (m1_subset_1 (esk30_8 X1 X2 X3 X4 X5 X6 X7 X8) (u1_struct_0 X8) -> False) -> False)
  -> (forall X5 X8 X4 X9 X10 X11 X1 X2 X3 X6 X7, (X6 = X7 -> False) -> (X5 = X7 -> False) -> (X5 = X6 -> False) -> (X4 = X8 -> False) -> (X3 = X8 -> False) -> (X3 = X4 -> False) -> (X2 = X8 -> False) -> (X2 = X7 -> False) -> (X2 = X6 -> False) -> (X2 = X4 -> False) -> (r1_collsp X1 X9 X10 X11 -> False) -> (r1_collsp X1 X2 X3 X5 -> False) -> m1_subset_1 X11 (u1_struct_0 X1) -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> r1_collsp X1 X8 X7 X9 -> r1_collsp X1 X5 X8 X11 -> r1_collsp X1 X4 X6 X9 -> r1_collsp X1 X4 X5 X10 -> r1_collsp X1 X3 X7 X10 -> r1_collsp X1 X3 X6 X11 -> r1_collsp X1 X2 X5 X7 -> r1_collsp X1 X2 X5 X6 -> r1_collsp X1 X2 X3 X8 -> r1_collsp X1 X2 X3 X4 -> epred1_8 X1 X2 X3 X4 X5 X6 X7 X8 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_anproj_2 X1 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> epred1_8 X1 (esk11_1 X1) (esk12_1 X1) (esk14_1 X1) (esk15_1 X1) (esk16_1 X1) (esk17_1 X1) (esk13_1 X1) -> False)
  -> (forall X8 X7 X6 X5 X1 X4 X3 X2, (epred1_8 X1 X2 X3 X5 X4 X6 X7 X8 -> False) -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X7 X5 X2 X3 X4 X6 X8 X1, (v2_struct_0 X1 -> False) -> (epred1_8 X1 X2 X3 X5 X6 X7 X8 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> v6_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X6 X7 X8 X5 X2 X3 X4 X1, (r1_collsp X1 X2 X3 X4 -> False) -> (epred1_8 X1 X2 X3 X4 X5 X6 X7 X8 -> False) -> False)
  -> (forall X5 X7 X8 X6 X2 X3 X4 X1, (r1_collsp X1 X2 X3 X4 -> False) -> (epred1_8 X1 X2 X3 X5 X6 X7 X8 X4 -> False) -> False)
  -> (forall X6 X7 X8 X5 X2 X3 X4 X1, (r1_collsp X1 X2 X3 X4 -> False) -> (epred1_8 X1 X2 X5 X6 X3 X4 X7 X8 -> False) -> False)
  -> (forall X6 X7 X8 X5 X2 X3 X4 X1, (r1_collsp X1 X2 X3 X4 -> False) -> (epred1_8 X1 X2 X5 X6 X3 X7 X4 X8 -> False) -> False)
  -> (forall X3 X4 X5 X8 X7 X6 X2 X1, (epred1_8 X3 X1 X4 X2 X5 X6 X7 X8 -> False) -> X1 = X2 -> False)
  -> (forall X3 X4 X6 X8 X7 X5 X2 X1, (epred1_8 X3 X1 X4 X5 X6 X2 X7 X8 -> False) -> X1 = X2 -> False)
  -> (forall X3 X4 X6 X8 X7 X5 X2 X1, (epred1_8 X3 X1 X4 X5 X6 X7 X2 X8 -> False) -> X1 = X2 -> False)
  -> (forall X3 X4 X6 X8 X7 X5 X2 X1, (epred1_8 X3 X1 X4 X5 X6 X7 X8 X2 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X8 X7 X6 X4 X2 X1, (epred1_8 X3 X4 X1 X2 X5 X6 X7 X8 -> False) -> X1 = X2 -> False)
  -> (forall X3 X6 X8 X7 X5 X4 X2 X1, (epred1_8 X3 X4 X1 X5 X6 X7 X8 X2 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X6 X8 X7 X4 X2 X1, (epred1_8 X3 X4 X5 X2 X6 X7 X8 X1 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X8 X7 X6 X4 X2 X1, (epred1_8 X3 X4 X5 X6 X1 X2 X7 X8 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X8 X7 X6 X4 X2 X1, (epred1_8 X3 X4 X5 X6 X1 X7 X2 X8 -> False) -> X1 = X2 -> False)
  -> (forall X3 X5 X7 X8 X6 X4 X2 X1, (epred1_8 X3 X4 X5 X6 X7 X1 X2 X8 -> False) -> X1 = X2 -> False)
  -> (forall X4 X3 X2 X5 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 (esk18_5 X1 X2 X3 X4 X5) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> v7_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X5 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 (esk18_5 X1 X4 X5 X2 X3) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> v7_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X5 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk18_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> v7_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X5 X4 X3 X1 X2 X6, (X2 = X6 -> False) -> (X2 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X5 X2 X6 -> r1_collsp X1 X4 X6 X2 -> r1_collsp X1 X2 X3 X5 -> False)
  -> (forall X5 X2 X3 X1 X4 X6, (X4 = X6 -> False) -> (X2 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X6 X2 X4 -> r1_collsp X1 X4 X6 X5 -> r1_collsp X1 X2 X3 X5 -> False)
  -> (forall X1 X2 X3 X4 X5 X6, (X5 = X6 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X4 X5 X6 -> r1_collsp X1 X3 X2 X6 -> r1_collsp X1 X2 X3 X5 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> l1_collsp X1 -> r1_collsp X1 (esk23_1 X1) (esk23_1 X1) (esk24_1 X1) -> r1_collsp X1 (esk23_1 X1) (esk24_1 X1) (esk23_1 X1) -> r1_collsp X1 (esk23_1 X1) (esk24_1 X1) (esk24_1 X1) -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X4 X5 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X3 X5 -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X1 X3 X4 X2 X5, (X2 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X4 X5 -> r1_collsp X1 X2 X3 X5 -> False)
  -> (forall X1 X3 X4 X2 X5, (X2 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X5 X4 -> r1_collsp X1 X2 X3 X5 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v7_anproj_2 X2 -> False) -> v2_collsp X2 -> v3_collsp X2 -> v4_collsp X2 -> v2_anproj_2 X2 -> v3_anproj_2 X2 -> l1_collsp X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_collsp X2 (esk19_1 X2) (esk20_1 X2) X1 -> r1_collsp X2 (esk21_1 X2) (esk22_1 X2) X1 -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X4 X3 X2 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X2 X3 -> False) -> v2_collsp X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X2 -> False) -> v2_collsp X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X3 -> False) -> v2_collsp X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_anproj_2 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_anproj_2 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_anproj_2 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_anproj_2 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_anproj_2 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_anproj_2 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_anproj_2 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (v5_anproj_2 X1 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> (m1_subset_1 (esk25_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> (m1_subset_1 (esk24_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> (m1_subset_1 (esk23_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_collsp X1 -> False)
  -> (r1_collsp esk1_0 esk10_0 esk9_0 esk8_0 -> False)
  -> (r1_collsp esk1_0 esk4_0 esk2_0 esk7_0 -> False)
  -> (v2_struct_0 esk29_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (esk7_0 = esk6_0 -> False)
  -> (esk7_0 = esk5_0 -> False)
  -> (esk6_0 = esk5_0 -> False)
  -> (esk4_0 = esk3_0 -> False)
  -> (esk3_0 = esk2_0 -> False)
  -> ((r1_collsp esk1_0 esk7_0 esk5_0 esk6_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk7_0 esk2_0 esk8_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk4_0 esk6_0 esk9_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk4_0 esk5_0 esk8_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk4_0 esk2_0 esk3_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk3_0 esk7_0 esk9_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk3_0 esk5_0 esk10_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk2_0 esk6_0 esk10_0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk10_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk9_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk8_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk7_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((l1_struct_0 esk27_0 -> False) -> False)
  -> ((l1_collsp esk29_0 -> False) -> False)
  -> ((l1_collsp esk26_0 -> False) -> False)
  -> ((l1_collsp esk1_0 -> False) -> False)
  -> ((v7_anproj_2 esk1_0 -> False) -> False)
  -> ((v6_anproj_2 esk1_0 -> False) -> False)
  -> ((v3_anproj_2 esk29_0 -> False) -> False)
  -> ((v3_anproj_2 esk1_0 -> False) -> False)
  -> ((v2_anproj_2 esk29_0 -> False) -> False)
  -> ((v2_anproj_2 esk1_0 -> False) -> False)
  -> ((v4_collsp esk29_0 -> False) -> False)
  -> ((v4_collsp esk1_0 -> False) -> False)
  -> ((v3_collsp esk29_0 -> False) -> False)
  -> ((v3_collsp esk1_0 -> False) -> False)
  -> ((v2_collsp esk29_0 -> False) -> False)
  -> ((v2_collsp esk1_0 -> False) -> False)
  -> False.
Admitted.
