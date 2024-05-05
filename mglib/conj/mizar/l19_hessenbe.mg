(** $I sig/MizarPreamble.mgs **)

Theorem l19_hessenbe:
 forall v2_struct_0:set -> prop,
 forall v2_collsp:set -> prop,
 forall v4_collsp:set -> prop,
 forall v3_anproj_2:set -> prop,
 forall v7_anproj_2:set -> prop,
 forall l1_collsp:set -> prop,
 forall v6_anproj_2:set -> prop,
 forall v2_anproj_2:set -> prop,
 forall v3_collsp:set -> prop,
 forall esk19_1:set -> set,
 forall esk1_0:set,
 forall esk10_0:set,
 forall esk11_0:set,
 forall esk9_0:set,
 forall esk8_0:set,
 forall esk6_0:set,
 forall esk22_1:set -> set,
 forall esk20_0:set,
 forall esk21_0:set,
 forall esk3_0:set,
 forall esk5_0:set,
 forall esk7_0:set,
 forall esk23_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall l1_struct_0:set -> prop,
 forall v5_anproj_2:set -> prop,
 forall esk15_1:set -> set,
 forall esk16_1:set -> set,
 forall esk13_1:set -> set,
 forall esk14_1:set -> set,
 forall esk17_1:set -> set,
 forall esk18_1:set -> set,
 forall esk12_5:set -> set -> set -> set -> set -> set,
 forall epred1_2:set -> set -> prop,
 forall epred2_10:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall r1_collsp:set -> set -> set -> set -> prop,
     (forall X7 X6 X2 X12 X3 X11 X4 X1 X5 X9 X8 X10, (X8 = X10 -> False) -> (X6 = X7 -> False) -> (X5 = X9 -> False) -> (X2 = X10 -> False) -> (X2 = X9 -> False) -> (X2 = X7 -> False) -> (r1_collsp X1 X3 X11 X4 -> False) -> (r1_collsp X1 X3 X4 X12 -> False) -> (r1_collsp X1 X2 X8 X6 -> False) -> (r1_collsp X1 X2 X8 X5 -> False) -> (r1_collsp X1 X2 X5 X6 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> m1_subset_1 X12 (u1_struct_0 X1) -> m1_subset_1 X11 (u1_struct_0 X1) -> r1_collsp X1 X10 X9 X4 -> r1_collsp X1 X10 X7 X11 -> r1_collsp X1 X9 X7 X3 -> r1_collsp X1 X8 X6 X12 -> r1_collsp X1 X8 X6 X11 -> r1_collsp X1 X8 X5 X4 -> r1_collsp X1 X5 X6 X3 -> r1_collsp X1 X2 X8 X10 -> r1_collsp X1 X2 X6 X7 -> r1_collsp X1 X2 X5 X12 -> r1_collsp X1 X2 X5 X9 -> epred2_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 -> False)
  -> (forall X10 X8 X6 X4 X3 X2 X5 X7 X9 X1, (v2_struct_0 X1 -> False) -> (epred2_10 X1 X2 X9 X10 X6 X8 X7 X4 X5 X3 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> v6_anproj_2 X1 -> v7_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X8 X7 X4 X6 X9 X10 X11 X1 X3 X5, (X3 = X5 -> False) -> (X2 = X5 -> False) -> (r1_collsp X1 X9 X10 X11 -> False) -> (r1_collsp X1 X5 X7 X8 -> False) -> (r1_collsp X1 X5 X6 X8 -> False) -> (r1_collsp X1 X5 X6 X7 -> False) -> epred1_2 X1 X5 -> m1_subset_1 X11 (u1_struct_0 X1) -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X7 X8 X9 -> r1_collsp X1 X6 X8 X10 -> r1_collsp X1 X6 X7 X11 -> r1_collsp X1 X5 X8 X4 -> r1_collsp X1 X5 X7 X3 -> r1_collsp X1 X5 X6 X2 -> r1_collsp X1 X3 X4 X9 -> r1_collsp X1 X2 X4 X10 -> r1_collsp X1 X2 X3 X11 -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X6 X4 X3 X11 X2 X8 X9 X10 X1 X5 X7, (X5 = X7 -> False) -> (X5 = X6 -> False) -> (r1_collsp X1 X8 X9 X10 -> False) -> (r1_collsp X1 X5 X3 X4 -> False) -> (r1_collsp X1 X5 X2 X4 -> False) -> (r1_collsp X1 X5 X2 X3 -> False) -> epred1_2 X1 X5 -> m1_subset_1 X11 (u1_struct_0 X1) -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X7 X11 X8 -> r1_collsp X1 X6 X11 X9 -> r1_collsp X1 X6 X7 X10 -> r1_collsp X1 X5 X4 X11 -> r1_collsp X1 X5 X3 X7 -> r1_collsp X1 X5 X2 X6 -> r1_collsp X1 X3 X4 X8 -> r1_collsp X1 X2 X4 X9 -> r1_collsp X1 X2 X3 X10 -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X4 X3 X2 X5 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 (esk12_5 X1 X2 X3 X4 X5) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> v7_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X5 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 (esk12_5 X1 X4 X5 X2 X3) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> v7_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X5 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk12_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> v7_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X5 X4 X1 X2 X3 X6 X7, (X6 = X7 -> False) -> (X4 = X5 -> False) -> (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X4 X5 X7 -> r1_collsp X1 X4 X5 X6 -> r1_collsp X1 X2 X3 X7 -> r1_collsp X1 X2 X3 X6 -> False)
  -> (forall X6 X2 X3 X7 X1 X4 X5, (X4 = X5 -> False) -> (X2 = X6 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> X4 = X7 -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X6 X5 X7 -> r1_collsp X1 X2 X4 X5 -> r1_collsp X1 X2 X3 X6 -> False)
  -> (forall X5 X4 X3 X1 X2 X6, (X2 = X6 -> False) -> (X2 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X5 X6 -> r1_collsp X1 X2 X4 X6 -> r1_collsp X1 X2 X3 X5 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> l1_collsp X1 -> r1_collsp X1 (esk17_1 X1) (esk17_1 X1) (esk18_1 X1) -> r1_collsp X1 (esk17_1 X1) (esk18_1 X1) (esk17_1 X1) -> r1_collsp X1 (esk17_1 X1) (esk18_1 X1) (esk18_1 X1) -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X4 X5 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X3 X5 -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X1 X3 X4 X2 X5, (X2 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X4 X5 -> r1_collsp X1 X2 X3 X5 -> False)
  -> (forall X1 X3 X4 X2 X5, (X2 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X5 X4 -> r1_collsp X1 X2 X3 X5 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v7_anproj_2 X2 -> False) -> v2_collsp X2 -> v3_collsp X2 -> v4_collsp X2 -> v2_anproj_2 X2 -> v3_anproj_2 X2 -> l1_collsp X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_collsp X2 (esk13_1 X2) (esk14_1 X2) X1 -> r1_collsp X2 (esk15_1 X2) (esk16_1 X2) X1 -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X4 X3 X2 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X2 X3 -> False) -> v2_collsp X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X2 -> False) -> v2_collsp X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X3 -> False) -> v2_collsp X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (epred1_2 X1 X2 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> v6_anproj_2 X1 -> v7_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (v5_anproj_2 X1 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> (m1_subset_1 (esk19_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> (m1_subset_1 (esk18_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> (m1_subset_1 (esk17_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_collsp X1 -> False)
  -> (r1_collsp esk1_0 esk9_0 esk11_0 esk10_0 -> False)
  -> (r1_collsp esk1_0 esk2_0 esk9_0 esk10_0 -> False)
  -> (r1_collsp esk1_0 esk2_0 esk6_0 esk8_0 -> False)
  -> (r1_collsp esk1_0 esk2_0 esk4_0 esk8_0 -> False)
  -> (r1_collsp esk1_0 esk2_0 esk4_0 esk6_0 -> False)
  -> (v2_struct_0 esk23_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (esk8_0 = esk7_0 -> False)
  -> (esk7_0 = esk2_0 -> False)
  -> (esk6_0 = esk5_0 -> False)
  -> (esk5_0 = esk2_0 -> False)
  -> (esk4_0 = esk3_0 -> False)
  -> (esk3_0 = esk2_0 -> False)
  -> ((r1_collsp esk1_0 esk6_0 esk8_0 esk9_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk5_0 esk7_0 esk9_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk4_0 esk8_0 esk11_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk4_0 esk6_0 esk10_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk3_0 esk7_0 esk11_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk3_0 esk5_0 esk10_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk2_0 esk8_0 esk7_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk2_0 esk6_0 esk5_0 -> False) -> False)
  -> ((r1_collsp esk1_0 esk2_0 esk4_0 esk3_0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk11_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk10_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk9_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk8_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk7_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((l1_struct_0 esk21_0 -> False) -> False)
  -> ((l1_collsp esk23_0 -> False) -> False)
  -> ((l1_collsp esk20_0 -> False) -> False)
  -> ((l1_collsp esk1_0 -> False) -> False)
  -> ((v7_anproj_2 esk1_0 -> False) -> False)
  -> ((v6_anproj_2 esk1_0 -> False) -> False)
  -> ((v3_anproj_2 esk23_0 -> False) -> False)
  -> ((v3_anproj_2 esk1_0 -> False) -> False)
  -> ((v2_anproj_2 esk23_0 -> False) -> False)
  -> ((v2_anproj_2 esk1_0 -> False) -> False)
  -> ((v4_collsp esk23_0 -> False) -> False)
  -> ((v4_collsp esk1_0 -> False) -> False)
  -> ((v3_collsp esk23_0 -> False) -> False)
  -> ((v3_collsp esk1_0 -> False) -> False)
  -> ((v2_collsp esk23_0 -> False) -> False)
  -> ((v2_collsp esk1_0 -> False) -> False)
  -> False.
Admitted.
