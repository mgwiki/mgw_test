(** $I sig/MizarPreamble.mgs **)

Theorem l12_projdes1:
 forall esk7_5:set -> set -> set -> set -> set -> set,
 forall v3_collsp:set -> prop,
 forall r1_projdes1:set -> set -> set -> set -> set -> prop,
 forall v3_anproj_2:set -> prop,
 forall v4_collsp:set -> prop,
 forall v2_collsp:set -> prop,
 forall v7_anproj_2:set -> prop,
 forall esk10_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk4_0:set,
 forall esk25_0:set,
 forall esk24_1:set -> set,
 forall esk23_0:set,
 forall esk22_0:set,
 forall esk2_0:set,
 forall esk6_0:set,
 forall esk5_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk11_1:set -> set,
 forall esk12_1:set -> set,
 forall esk18_1:set -> set,
 forall esk15_1:set -> set,
 forall esk14_1:set -> set,
 forall esk13_1:set -> set,
 forall esk19_1:set -> set,
 forall esk17_1:set -> set,
 forall esk21_1:set -> set,
 forall esk20_1:set -> set,
 forall esk8_1:set -> set,
 forall esk9_1:set -> set,
 forall esk16_6:set -> set -> set -> set -> set -> set -> set,
 forall r1_collsp:set -> set -> set -> set -> prop,
 forall l1_collsp:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall v2_anproj_2:set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X6 X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 (esk16_6 X1 X2 X4 X3 X5 X6) -> False) -> v2_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X4 X3 X6 -> r1_collsp X1 X2 X4 X5 -> False)
  -> (forall X6 X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 (esk16_6 X1 X4 X5 X6 X2 X3) -> False) -> v2_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X5 X6 X3 -> r1_collsp X1 X4 X5 X2 -> False)
  -> (forall X6 X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk16_6 X1 X2 X3 X4 X5 X6) (u1_struct_0 X1) -> False) -> v2_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X3 X4 X6 -> r1_collsp X1 X2 X3 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_collsp X1 X2 X3 (esk7_5 X1 X2 X3 X4 X5) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_projdes1 X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_collsp X1 X2 X3 (esk7_5 X1 X4 X5 X2 X3) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_projdes1 X1 X4 X5 X2 X3 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (m1_subset_1 (esk7_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_projdes1 X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X3 X6 X5 X4 X2, (v2_struct_0 X2 -> False) -> (v7_anproj_2 X2 -> False) -> (r1_projdes1 X2 X3 X4 X5 X6 -> False) -> v2_collsp X2 -> v3_collsp X2 -> v4_collsp X2 -> v2_anproj_2 X2 -> v3_anproj_2 X2 -> l1_collsp X2 -> m1_subset_1 X6 (u1_struct_0 X2) -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_collsp X2 X5 X6 X1 -> r1_collsp X2 X3 X4 X1 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_projdes1 X1 X2 X3 X4 X5 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_projdes1 X1 X3 X4 X5 X2 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_projdes1 X1 X4 X5 X2 X3 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_projdes1 X1 X5 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X1 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X4 X5 X6 -> False) -> v3_collsp X1 -> l1_collsp X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X3 X6 -> r1_collsp X1 X2 X3 X5 -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> l1_collsp X1 -> r1_collsp X1 (esk8_1 X1) (esk8_1 X1) (esk9_1 X1) -> r1_collsp X1 (esk8_1 X1) (esk9_1 X1) (esk8_1 X1) -> r1_collsp X1 (esk8_1 X1) (esk9_1 X1) (esk9_1 X1) -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X4 X5 -> False) -> v2_collsp X1 -> v3_collsp X1 -> l1_collsp X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X3 X5 -> r1_collsp X1 X2 X3 X4 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_anproj_2 X2 -> False) -> l1_collsp X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_collsp X2 (esk17_1 X2) (esk19_1 X2) X1 -> r1_collsp X2 (esk20_1 X2) (esk21_1 X2) X1 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X2 X4 X3 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X3 X2 X4 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X3 X4 X2 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X4 X2 X3 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (v7_anproj_2 X1 -> False) -> (r1_collsp X1 X2 X3 X4 -> False) -> v2_collsp X1 -> v3_collsp X1 -> v4_collsp X1 -> v2_anproj_2 X1 -> v3_anproj_2 X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_collsp X1 X4 X3 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_collsp X1 -> False) -> l1_collsp X1 -> r1_collsp X1 (esk13_1 X1) (esk14_1 X1) (esk15_1 X1) -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X2 X3 -> False) -> v2_collsp X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X2 -> False) -> v2_collsp X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_collsp X1 X2 X3 X3 -> False) -> v2_collsp X1 -> l1_collsp X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_anproj_2 X1 -> False) -> (r1_collsp X1 (esk18_1 X1) (esk19_1 X1) (esk21_1 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_anproj_2 X1 -> False) -> (r1_collsp X1 (esk17_1 X1) (esk18_1 X1) (esk20_1 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_collsp X1 -> False) -> (r1_collsp X1 (esk11_1 X1) (esk12_1 X1) (esk15_1 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_collsp X1 -> False) -> (r1_collsp X1 (esk11_1 X1) (esk12_1 X1) (esk14_1 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_collsp X1 -> False) -> (r1_collsp X1 (esk11_1 X1) (esk12_1 X1) (esk13_1 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_anproj_2 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_anproj_2 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_anproj_2 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_anproj_2 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_anproj_2 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_collsp X1 -> False) -> (m1_subset_1 (esk15_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_collsp X1 -> False) -> (m1_subset_1 (esk14_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_collsp X1 -> False) -> (m1_subset_1 (esk13_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_collsp X1 -> False) -> (m1_subset_1 (esk12_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_collsp X1 -> False) -> (m1_subset_1 (esk11_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_collsp X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> l1_collsp X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_collsp X1 -> False) -> (esk12_1 X1) = (esk11_1 X1) -> l1_collsp X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_collsp X1 -> False)
  -> (r1_projdes1 esk1_0 esk2_0 esk3_0 esk5_0 esk6_0 -> False)
  -> (r1_collsp esk1_0 esk2_0 esk3_0 esk4_0 -> False)
  -> (v7_anproj_2 esk1_0 -> False)
  -> (v2_struct_0 esk25_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> ((r1_projdes1 esk1_0 esk2_0 esk3_0 esk4_0 esk6_0 -> False) -> False)
  -> ((r1_projdes1 esk1_0 esk2_0 esk3_0 esk4_0 esk5_0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((l1_struct_0 esk23_0 -> False) -> False)
  -> ((l1_collsp esk25_0 -> False) -> False)
  -> ((l1_collsp esk22_0 -> False) -> False)
  -> ((l1_collsp esk1_0 -> False) -> False)
  -> ((v3_anproj_2 esk25_0 -> False) -> False)
  -> ((v3_anproj_2 esk1_0 -> False) -> False)
  -> ((v2_anproj_2 esk25_0 -> False) -> False)
  -> ((v2_anproj_2 esk1_0 -> False) -> False)
  -> ((v4_collsp esk25_0 -> False) -> False)
  -> ((v4_collsp esk1_0 -> False) -> False)
  -> ((v3_collsp esk25_0 -> False) -> False)
  -> ((v3_collsp esk1_0 -> False) -> False)
  -> ((v2_collsp esk25_0 -> False) -> False)
  -> ((v2_collsp esk1_0 -> False) -> False)
  -> False.
Admitted.
