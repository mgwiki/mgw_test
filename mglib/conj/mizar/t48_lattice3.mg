(** $I sig/MizarPreamble.mgs **)

Theorem t48_lattice3:
 forall a_2_8_lattice3:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk20_3:set -> set -> set -> set,
 forall esk19_3:set -> set -> set -> set,
 forall r3_lattices:set -> set -> set -> prop,
 forall a_2_10_lattice3:set -> set -> set,
 forall esk14_3:set -> set -> set -> set,
 forall esk15_3:set -> set -> set -> set,
 forall a_2_9_lattice3:set -> set -> set,
 forall v8_lattices:set -> prop,
 forall v9_lattices:set -> prop,
 forall v6_lattices:set -> prop,
 forall a_2_2_lattice3:set -> set -> set,
 forall r3_lattice3:set -> set -> set -> prop,
 forall esk16_3:set -> set -> set -> set,
 forall esk21_3:set -> set -> set -> set,
 forall k9_setfam_1:set -> set,
 forall k16_lattice3:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k3_tarski:set -> set,
 forall esk7_2:set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall esk34_2:set -> set -> set,
 forall v19_lattices:set -> set -> prop,
 forall v21_lattices:set -> set -> prop,
 forall esk5_2:set -> set -> set,
 forall v5_lattices:set -> prop,
 forall v7_lattices:set -> prop,
 forall esk30_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk32_1:set -> set,
 forall esk23_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk29_1:set -> set,
 forall esk28_0:set,
 forall esk11_0:set,
 forall esk24_0:set,
 forall esk12_0:set,
 forall esk10_0:set,
 forall o_0_0_xboole_0:set,
 forall esk9_0:set,
 forall esk13_1:set -> set,
 forall esk27_1:set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall l1_lattices:set -> prop,
 forall v15_lattices:set -> prop,
 forall v14_lattices:set -> prop,
 forall v13_lattices:set -> prop,
 forall esk31_1:set -> set,
 forall esk33_1:set -> set,
 forall k1_xboole_0:set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk25_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk26_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk22_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v20_lattices:set -> set -> prop,
 forall v18_lattices:set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall l2_lattices:set -> prop,
 forall v4_lattices:set -> prop,
 forall esk3_3:set -> set -> set -> set,
 forall esk18_3:set -> set -> set -> set,
 forall esk17_3:set -> set -> set -> set,
 forall a_2_7_lattice3:set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall v4_lattice3:set -> prop,
 forall r4_lattice3:set -> set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall esk4_3:set -> set -> set -> set,
 forall r1_lattices:set -> set -> set -> prop,
 forall l3_lattices:set -> prop,
 forall v10_lattices:set -> prop,
 forall k15_lattice3:set -> set -> set,
     (forall X3 X2 X1, (X2 = (k15_lattice3 X1 X3) -> False) -> (v2_struct_0 X1 -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> r4_lattice3 X1 X2 X3 -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_lattices X1 X2 (esk4_3 X1 X3 X2) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_lattices X1 (esk20_3 X2 X1 X3) (esk19_3 X2 X1 X3) -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> r2_hidden X2 (a_2_8_lattice3 X1 X3) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_lattices X1 (esk17_3 X2 X1 X3) (esk18_3 X2 X1 X3) -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> r2_hidden X2 (a_2_7_lattice3 X1 X3) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_lattices X1 (esk14_3 X2 X1 X3) (esk15_3 X2 X1 X3) -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> r2_hidden X2 (a_2_10_lattice3 X1 X3) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r4_lattice3 X1 X2 X3 -> False) -> l3_lattices X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_lattices X1 (esk3_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X3 X1, (X3 = (k15_lattice3 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> (r4_lattice3 X1 (esk4_3 X1 X2 X3) X2 -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> r4_lattice3 X1 X3 X2 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (X3 = (k15_lattice3 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk4_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> r4_lattice3 X1 X3 X2 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X5 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_10_lattice3 X2 X5) -> False) -> X1 = X3 -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r3_lattices X2 X1 X4 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r2_hidden X4 (a_2_9_lattice3 X2 X5) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> l2_lattices X1 -> r1_lattices X1 X3 X2 -> r1_lattices X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X1 X3 X2, (v2_struct_0 X2 -> False) -> (r1_lattices X2 X4 X1 -> False) -> X4 = (k15_lattice3 X2 X3) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r4_lattice3 X2 X1 X3 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X5 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_8_lattice3 X2 X5) -> False) -> X1 = X3 -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X4 X5 -> r3_lattices X2 X4 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X5 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_7_lattice3 X2 X5) -> False) -> X1 = X3 -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X4 X5 -> r3_lattices X2 X1 X4 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_lattices X1 X4 X2 -> False) -> l3_lattices X1 -> r2_hidden X4 X3 -> r4_lattice3 X1 X2 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_lattices X1 X2 X3 -> False) -> l3_lattices X1 -> v6_lattices X1 -> v8_lattices X1 -> v9_lattices X1 -> r1_lattices X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_lattices X1 X2 X3 -> False) -> l3_lattices X1 -> v6_lattices X1 -> v8_lattices X1 -> v9_lattices X1 -> r3_lattices X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_lattice3 X1 (esk16_3 X2 X1 X3) X3 -> False) -> l3_lattices X1 -> r2_hidden X2 (a_2_2_lattice3 X1 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk15_3 X1 X2 X3) (a_2_9_lattice3 X2 X3) -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_10_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk21_3 X1 X2 X3) (k9_setfam_1 (u1_struct_0 X2)) -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_9_lattice3 X2 X3) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r4_lattice3 X1 X2 X3 -> False) -> (m1_subset_1 (esk3_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l3_lattices X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r4_lattice3 X1 X2 X3 -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X3 -> False) -> l3_lattices X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk20_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_8_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk19_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_8_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk18_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_7_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk17_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_7_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk15_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_10_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk14_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_10_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, ((k15_lattice3 X2 (esk21_3 X1 X2 X3)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_9_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk21_3 X1 X2 X3) X3 -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_9_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk20_3 X1 X2 X3) X3 -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_8_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk18_3 X1 X2 X3) X3 -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_7_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk16_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l3_lattices X2 -> r2_hidden X1 (a_2_2_lattice3 X2 X3) -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_2_lattice3 X2 X4) -> False) -> X1 = X3 -> l3_lattices X2 -> r3_lattice3 X2 X1 X4 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_9_lattice3 X2 X4) -> False) -> X3 = (k15_lattice3 X2 X1) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 X4 -> m1_subset_1 X1 (k9_setfam_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_lattices X1 (k16_lattice3 X1 X2) X3 -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> r2_hidden X3 X2 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r3_lattices X1 X2 (k15_lattice3 X1 X3) -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> r2_hidden X2 X3 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_lattices X1 (k16_lattice3 X1 X2) (k16_lattice3 X1 X3) -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> r1_tarski X3 X2 -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r3_lattices X1 (k15_lattice3 X1 X2) (k15_lattice3 X1 X3) -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> r1_tarski X2 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk7_2 X1 X2) X3 -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_lattices X1 X2 X2 -> False) -> l3_lattices X1 -> v6_lattices X1 -> v8_lattices X1 -> v9_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk6_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X3 X2, ((esk19_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_8_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, ((esk17_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_7_lattice3 X2 X3) -> False)
  -> (forall X1 X3 X2, ((esk14_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v10_lattices X2 -> v4_lattice3 X2 -> l3_lattices X2 -> r2_hidden X1 (a_2_10_lattice3 X2 X3) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r4_lattice3 X1 X2 X3 -> False) -> X2 = (k15_lattice3 X1 X3) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, ((esk16_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l3_lattices X2 -> r2_hidden X1 (a_2_2_lattice3 X2 X3) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> (r2_hidden (esk7_2 X1 X2) (esk8_2 X1 X2) -> False) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk34_2 X3 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v20_lattices X2 X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> v18_lattices X2 X1 -> m1_subset_1 X2 (k9_setfam_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v21_lattices X2 X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> v19_lattices X2 X1 -> m1_subset_1 X2 (k9_setfam_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v18_lattices X1 X2 -> False) -> v10_lattices X2 -> l3_lattices X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k9_setfam_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v19_lattices X1 X2 -> False) -> v10_lattices X2 -> l3_lattices X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k9_setfam_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> (r2_hidden (esk8_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k16_lattice3 X1 (a_2_8_lattice3 X1 X2)) = (k16_lattice3 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> False)
  -> (forall X2 X1, ((k15_lattice3 X1 (a_2_7_lattice3 X1 X2)) = (k15_lattice3 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> v10_lattices X1 -> v4_lattice3 X1 -> l3_lattices X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k15_lattice3 X1 (a_2_2_lattice3 X1 X2)) = (k16_lattice3 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l3_lattices X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk34_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v10_lattices X1 -> False) -> l3_lattices X1 -> v4_lattices X1 -> v5_lattices X1 -> v6_lattices X1 -> v7_lattices X1 -> v8_lattices X1 -> v9_lattices X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k16_lattice3 X1 X2) (u1_struct_0 X1) -> False) -> l3_lattices X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k15_lattice3 X1 X2) (u1_struct_0 X1) -> False) -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k9_setfam_1 (u1_struct_0 X1)) -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk5_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k9_setfam_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k9_setfam_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k9_setfam_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k9_setfam_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v18_lattices (esk22_1 X1) X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v19_lattices (esk22_1 X1) X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v15_lattices X1 -> False) -> l3_lattices X1 -> v13_lattices X1 -> v14_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v15_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v14_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> v8_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk26_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk30_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk25_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk31_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v14_lattices X1 -> False) -> l3_lattices X1 -> v15_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_lattices X1 -> False) -> l3_lattices X1 -> v15_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v9_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v8_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk25_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk33_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk32_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (l2_lattices X1 -> False) -> l3_lattices X1 -> False)
  -> (forall X1, (l1_lattices X1 -> False) -> l3_lattices X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_lattices X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k15_lattice3 esk1_0 (a_2_9_lattice3 esk1_0 esk2_0)) = (k15_lattice3 esk1_0 (k3_tarski esk2_0)) -> False)
  -> (forall X1, v1_subset_1 (esk29_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k9_setfam_1 X1) -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (k9_setfam_1 X1) (k9_setfam_1 (k9_setfam_1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk29_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> ((r1_tarski esk2_0 (k9_setfam_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk27_1 X1) -> False) -> False)
  -> ((l2_lattices esk11_0 -> False) -> False)
  -> ((l1_lattices esk9_0 -> False) -> False)
  -> ((v1_xboole_0 esk24_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((l3_lattices esk12_0 -> False) -> False)
  -> ((l3_lattices esk1_0 -> False) -> False)
  -> ((v4_lattice3 esk1_0 -> False) -> False)
  -> ((v10_lattices esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
