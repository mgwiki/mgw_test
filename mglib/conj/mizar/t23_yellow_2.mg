(** $I sig/MizarPreamble.mgs **)

Theorem t23_yellow_2:
 forall r2_yellow_0:set -> set -> prop,
 forall esk11_3:set -> set -> set -> set,
 forall r1_lattice3:set -> set -> set -> prop,
 forall esk12_3:set -> set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall a_2_2_yellow_2:set -> set -> set,
 forall esk18_3:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall v7_struct_0:set -> prop,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk20_0:set,
 forall esk19_0:set,
 forall esk15_0:set,
 forall esk14_0:set,
 forall esk16_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall k1_xboole_0:set,
 forall l1_struct_0:set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk21_2:set -> set -> set,
 forall esk17_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_2_1_yellow_2:set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall esk13_3:set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall r1_orders_2:set -> set -> set -> prop,
 forall r2_lattice3:set -> set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall l1_orders_2:set -> prop,
 forall r1_yellow_0:set -> set -> prop,
     (forall X1 X4 X2 X3, (r1_yellow_0 X2 X3 -> False) -> (r1_orders_2 X2 (esk7_3 X2 X3 X4) X1 -> False) -> l1_orders_2 X2 -> r2_lattice3 X2 X3 X4 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_orders_2 X2 X4 (esk6_3 X2 X3 X4) -> False)
  -> (forall X1 X4 X2 X3, (r2_yellow_0 X2 X3 -> False) -> (r1_orders_2 X2 X1 (esk12_3 X2 X3 X4) -> False) -> l1_orders_2 X2 -> r1_lattice3 X2 X3 X4 -> r1_lattice3 X2 X3 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_orders_2 X2 (esk11_3 X2 X3 X4) X4 -> False)
  -> (forall X4 X1 X2 X3, (r1_yellow_0 X2 X3 -> False) -> (r2_lattice3 X2 X3 (esk6_3 X2 X3 X4) -> False) -> (r1_orders_2 X2 (esk7_3 X2 X3 X4) X1 -> False) -> l1_orders_2 X2 -> r2_lattice3 X2 X3 X4 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X4 X1 X2 X3, (r2_yellow_0 X2 X3 -> False) -> (r1_orders_2 X2 X1 (esk12_3 X2 X3 X4) -> False) -> (r1_lattice3 X2 X3 (esk11_3 X2 X3 X4) -> False) -> l1_orders_2 X2 -> r1_lattice3 X2 X3 X4 -> r1_lattice3 X2 X3 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X1 X2, (r2_yellow_0 X1 X2 -> False) -> (r1_lattice3 X1 X2 (esk12_3 X1 X2 X3) -> False) -> l1_orders_2 X1 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> r1_orders_2 X1 (esk11_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (r2_lattice3 X1 X2 (esk7_3 X1 X2 X3) -> False) -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> r1_orders_2 X1 X3 (esk6_3 X1 X2 X3) -> False)
  -> (forall X4 X1 X2 X3, (r1_yellow_0 X2 X3 -> False) -> (r1_orders_2 X2 (esk7_3 X2 X3 X4) X1 -> False) -> (m1_subset_1 (esk6_3 X2 X3 X4) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> r2_lattice3 X2 X3 X4 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X4 X1 X2 X3, (r2_yellow_0 X2 X3 -> False) -> (r1_orders_2 X2 X1 (esk12_3 X2 X3 X4) -> False) -> (m1_subset_1 (esk11_3 X2 X3 X4) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> r1_lattice3 X2 X3 X4 -> r1_lattice3 X2 X3 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X1 X2, (r2_yellow_0 X1 X2 -> False) -> (m1_subset_1 (esk12_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> r1_orders_2 X1 (esk11_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> r1_orders_2 X1 X3 (esk6_3 X1 X2 X3) -> False)
  -> (forall X3 X1 X2, (r2_yellow_0 X1 X2 -> False) -> (esk12_3 X1 X2 X3) = X3 -> l1_orders_2 X1 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> r1_orders_2 X1 (esk11_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (esk7_3 X1 X2 X3) = X3 -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> r1_orders_2 X1 X3 (esk6_3 X1 X2 X3) -> False)
  -> (forall X3 X1 X2, (r2_yellow_0 X1 X2 -> False) -> (r1_lattice3 X1 X2 (esk11_3 X1 X2 X3) -> False) -> (r1_lattice3 X1 X2 (esk12_3 X1 X2 X3) -> False) -> l1_orders_2 X1 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (r2_lattice3 X1 X2 (esk6_3 X1 X2 X3) -> False) -> (r2_lattice3 X1 X2 (esk7_3 X1 X2 X3) -> False) -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r2_yellow_0 X1 X2 -> False) -> (r1_lattice3 X1 X2 (esk12_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk11_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r2_yellow_0 X1 X2 -> False) -> (r1_lattice3 X1 X2 (esk11_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk12_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (r2_lattice3 X1 X2 (esk7_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (r2_lattice3 X1 X2 (esk6_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (X3 = (esk9_2 X1 X2) -> False) -> l1_orders_2 X1 -> r2_yellow_0 X1 X2 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> r1_orders_2 X1 (esk10_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X2 = (esk4_2 X1 X3) -> False) -> l1_orders_2 X1 -> r1_yellow_0 X1 X3 -> r2_lattice3 X1 X3 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_orders_2 X1 X2 (esk5_3 X1 X3 X2) -> False)
  -> (forall X3 X1 X2, (r2_yellow_0 X1 X2 -> False) -> (m1_subset_1 (esk11_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> (m1_subset_1 (esk12_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r2_yellow_0 X1 X2 -> False) -> (r1_lattice3 X1 X2 (esk11_3 X1 X2 X3) -> False) -> (esk12_3 X1 X2 X3) = X3 -> l1_orders_2 X1 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (r2_lattice3 X1 X2 (esk6_3 X1 X2 X3) -> False) -> (esk7_3 X1 X2 X3) = X3 -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r2_yellow_0 X1 X2 -> False) -> (m1_subset_1 (esk11_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> (esk12_3 X1 X2 X3) = X3 -> l1_orders_2 X1 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> (esk7_3 X1 X2 X3) = X3 -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (r2_lattice3 X1 X2 X3 -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> r1_orders_2 X1 (esk13_3 X1 X2 X3) X3 -> False)
  -> (forall X2 X3 X1, (r1_lattice3 X1 X3 X2 -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_orders_2 X1 X2 (esk8_3 X1 X3 X2) -> False)
  -> (forall X2 X3 X1, (X3 = (esk9_2 X1 X2) -> False) -> (r1_lattice3 X1 X2 (esk10_3 X1 X2 X3) -> False) -> l1_orders_2 X1 -> r2_yellow_0 X1 X2 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (X3 = (esk4_2 X1 X2) -> False) -> (r2_lattice3 X1 X2 (esk5_3 X1 X2 X3) -> False) -> l1_orders_2 X1 -> r1_yellow_0 X1 X2 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (X3 = (esk9_2 X1 X2) -> False) -> (m1_subset_1 (esk10_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r2_yellow_0 X1 X2 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (X3 = (esk4_2 X1 X2) -> False) -> (m1_subset_1 (esk5_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r1_yellow_0 X1 X2 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_lattice3 X1 X2 (esk17_3 X3 X1 X2) -> False) -> l1_orders_2 X1 -> r2_hidden X3 (a_2_1_yellow_2 X1 X2) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r2_lattice3 X1 X2 (esk18_3 X3 X1 X2) -> False) -> l1_orders_2 X1 -> r2_hidden X3 (a_2_2_yellow_2 X1 X2) -> False)
  -> (forall X2 X4 X3 X1, (r1_orders_2 X1 X3 X4 -> False) -> l1_orders_2 X1 -> r2_hidden X4 X2 -> r1_lattice3 X1 X2 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (r1_orders_2 X1 X4 X3 -> False) -> l1_orders_2 X1 -> r2_hidden X4 X2 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (r1_orders_2 X2 (esk4_2 X2 X3) X1 -> False) -> l1_orders_2 X2 -> r1_yellow_0 X2 X3 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X1 X2, (r1_orders_2 X2 X1 (esk9_2 X2 X3) -> False) -> l1_orders_2 X2 -> r2_yellow_0 X2 X3 -> r1_lattice3 X2 X3 X1 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X2 X3 X1, (r1_lattice3 X1 X2 X3 -> False) -> (m1_subset_1 (esk8_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (r2_lattice3 X1 X2 X3 -> False) -> (m1_subset_1 (esk13_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (r1_lattice3 X1 X2 X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X2 -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (r2_lattice3 X1 X2 X3 -> False) -> (r2_hidden (esk13_3 X1 X2 X3) X2 -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk18_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> r2_hidden X1 (a_2_2_yellow_2 X2 X3) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk17_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> r2_hidden X1 (a_2_1_yellow_2 X2 X3) -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_2_yellow_2 X2 X4) -> False) -> X1 = X3 -> l1_orders_2 X2 -> r2_lattice3 X2 X4 X1 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_1_yellow_2 X2 X4) -> False) -> X1 = X3 -> l1_orders_2 X2 -> r1_lattice3 X2 X4 X1 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X3 X2, ((esk18_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_orders_2 X2 -> r2_hidden X1 (a_2_2_yellow_2 X2 X3) -> False)
  -> (forall X1 X3 X2, ((esk17_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_orders_2 X2 -> r2_hidden X1 (a_2_1_yellow_2 X2 X3) -> False)
  -> (forall X2 X1, (r1_lattice3 X1 X2 (esk9_2 X1 X2) -> False) -> l1_orders_2 X1 -> r2_yellow_0 X1 X2 -> False)
  -> (forall X2 X1, (r2_lattice3 X1 X2 (esk4_2 X1 X2) -> False) -> l1_orders_2 X1 -> r1_yellow_0 X1 X2 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk21_2 X3 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk9_2 X1 X2) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r2_yellow_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk4_2 X1 X2) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> r1_yellow_0 X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk21_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (r1_yellow_0 esk1_0 esk2_0 -> r2_yellow_0 esk1_0 esk3_0 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1 X2, (r1_yellow_0 esk1_0 X1 -> False) -> (r2_yellow_0 esk1_0 X2 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> ((v1_xboole_0 esk19_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk15_0 -> False) -> False)
  -> ((l1_orders_2 esk14_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> False.
Admitted.
