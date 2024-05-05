(** $I sig/MizarPreamble.mgs **)

Theorem t67_boolealg:
 forall k2_lattices:set -> set -> set -> set,
 forall esk5_1:set -> set,
 forall k1_lattices:set -> set -> set -> set,
 forall esk7_1:set -> set,
 forall esk6_1:set -> set,
 forall v11_lattices:set -> prop,
 forall l2_lattices:set -> prop,
 forall esk8_1:set -> set,
 forall esk10_1:set -> set,
 forall esk9_1:set -> set,
 forall v5_lattices:set -> prop,
 forall k2_boolealg:set -> set -> set -> set,
 forall k7_lattices:set -> set -> set,
 forall v4_lattices:set -> prop,
 forall v12_lattices:set -> prop,
 forall esk14_0:set,
 forall esk17_0:set,
 forall esk16_0:set,
 forall esk15_0:set,
 forall esk18_1:set -> set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall l1_struct_0:set -> prop,
 forall v14_lattices:set -> prop,
 forall v13_lattices:set -> prop,
 forall v15_lattices:set -> prop,
 forall v16_lattices:set -> prop,
 forall v9_lattices:set -> prop,
 forall v8_lattices:set -> prop,
 forall k3_boolealg:set -> set -> set -> set,
 forall v6_lattices:set -> prop,
 forall v7_lattices:set -> prop,
 forall esk12_1:set -> set,
 forall esk13_1:set -> set,
 forall esk11_1:set -> set,
 forall l1_lattices:set -> prop,
 forall r1_boolealg:set -> set -> set -> prop,
 forall k3_lattices:set -> set -> set -> set,
 forall k1_boolealg:set -> set -> set -> set,
 forall k4_lattices:set -> set -> set -> set,
 forall v17_lattices:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall l3_lattices:set -> prop,
 forall v10_lattices:set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_boolealg X1 (k1_boolealg X1 (k3_lattices X1 X2 X3) (k4_lattices X1 X2 X3)) (k3_lattices X1 (k1_boolealg X1 X2 X3) (k1_boolealg X1 X3 X2)) -> False) -> v10_lattices X1 -> v17_lattices X1 -> l3_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_boolealg X1 (k1_boolealg X1 X2 (k1_boolealg X1 X3 X4)) (k3_lattices X1 (k1_boolealg X1 X2 X3) (k4_lattices X1 X2 X4)) -> False) -> v10_lattices X1 -> v17_lattices X1 -> l3_lattices X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_boolealg X1 (k1_boolealg X1 (k1_boolealg X1 X2 X3) X4) (k1_boolealg X1 X2 (k3_lattices X1 X3 X4)) -> False) -> v10_lattices X1 -> v17_lattices X1 -> l3_lattices X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_lattices X1 -> False) -> (k1_lattices X1 (k2_lattices X1 (esk5_1 X1) (esk6_1 X1)) (k2_lattices X1 (esk5_1 X1) (esk7_1 X1))) = (k2_lattices X1 (esk5_1 X1) (k1_lattices X1 (esk6_1 X1) (esk7_1 X1))) -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_lattices X1 -> False) -> (k2_lattices X1 (k2_lattices X1 (esk11_1 X1) (esk12_1 X1)) (esk13_1 X1)) = (k2_lattices X1 (esk11_1 X1) (k2_lattices X1 (esk12_1 X1) (esk13_1 X1))) -> l1_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (k1_lattices X1 (k1_lattices X1 (esk8_1 X1) (esk9_1 X1)) (esk10_1 X1)) = (k1_lattices X1 (esk8_1 X1) (k1_lattices X1 (esk9_1 X1) (esk10_1 X1))) -> l2_lattices X1 -> False)
  -> (forall X4 X3 X2 X1, ((k1_lattices X1 (k2_lattices X1 X2 X3) (k2_lattices X1 X2 X4)) = (k2_lattices X1 X2 (k1_lattices X1 X3 X4)) -> False) -> (v2_struct_0 X1 -> False) -> l3_lattices X1 -> v11_lattices X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, ((k2_lattices X1 (k2_lattices X1 X2 X3) X4) = (k2_lattices X1 X2 (k2_lattices X1 X3 X4)) -> False) -> (v2_struct_0 X1 -> False) -> v7_lattices X1 -> l1_lattices X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, ((k1_lattices X1 (k1_lattices X1 X2 X3) X4) = (k1_lattices X1 X2 (k1_lattices X1 X3 X4)) -> False) -> (v2_struct_0 X1 -> False) -> v5_lattices X1 -> l2_lattices X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k3_lattices X1 (k1_boolealg X1 X2 X3) (k1_boolealg X1 X3 X2)) = (k2_boolealg X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_boolealg X1 X3 X2 -> False) -> v10_lattices X1 -> l3_lattices X1 -> r1_boolealg X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k4_lattices X1 X2 (k7_lattices X1 X3)) = (k1_boolealg X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k2_boolealg X1 X2 X3) (u1_struct_0 X1) -> False) -> v10_lattices X1 -> l3_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k1_boolealg X1 X2 X3) (u1_struct_0 X1) -> False) -> v10_lattices X1 -> l3_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k4_lattices X1 X2 X3) (u1_struct_0 X1) -> False) -> v6_lattices X1 -> l1_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k3_lattices X1 X2 X3) (u1_struct_0 X1) -> False) -> v4_lattices X1 -> l2_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k3_boolealg X1 X2 X3) (u1_struct_0 X1) -> False) -> v10_lattices X1 -> l3_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k2_lattices X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k1_lattices X1 X2 X3) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k2_boolealg X1 X2 X3) = (k3_boolealg X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k4_lattices X1 X2 X3) = (k2_lattices X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v6_lattices X1 -> l1_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k3_lattices X1 X2 X3) = (k1_lattices X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> l2_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k4_lattices X1 X2 X3) = (k4_lattices X1 X3 X2) -> False) -> (v2_struct_0 X1 -> False) -> v6_lattices X1 -> l1_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k3_lattices X1 X2 X3) = (k3_lattices X1 X3 X2) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> l2_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k3_boolealg X1 X2 X3) = (k3_boolealg X1 X3 X2) -> False) -> (v2_struct_0 X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> r1_boolealg X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (r1_boolealg X3 X1 X2 -> False) -> X1 = X2 -> v10_lattices X3 -> l3_lattices X3 -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_boolealg X1 X2 X2 -> False) -> v10_lattices X1 -> l3_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k1_lattices X1 X2 X2) = X2 -> False) -> (v2_struct_0 X1 -> False) -> l3_lattices X1 -> v6_lattices X1 -> v8_lattices X1 -> v9_lattices X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k4_lattices X1 X2 X2) = X2 -> False) -> (v2_struct_0 X1 -> False) -> l3_lattices X1 -> v6_lattices X1 -> v8_lattices X1 -> v9_lattices X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k7_lattices X1 (k7_lattices X1 X2)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v10_lattices X1 -> v17_lattices X1 -> l3_lattices X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k7_lattices X1 X2) (u1_struct_0 X1) -> False) -> l3_lattices X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v10_lattices X1 -> False) -> l3_lattices X1 -> v4_lattices X1 -> v5_lattices X1 -> v6_lattices X1 -> v7_lattices X1 -> v8_lattices X1 -> v9_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_lattices X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_lattices X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_lattices X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_lattices X1 -> False) -> (m1_subset_1 (esk13_1 X1) (u1_struct_0 X1) -> False) -> l1_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_lattices X1 -> False) -> (m1_subset_1 (esk12_1 X1) (u1_struct_0 X1) -> False) -> l1_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_lattices X1 -> False) -> (m1_subset_1 (esk11_1 X1) (u1_struct_0 X1) -> False) -> l1_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v17_lattices X1 -> False) -> l3_lattices X1 -> v15_lattices X1 -> v11_lattices X1 -> v16_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v12_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> v11_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v15_lattices X1 -> False) -> l3_lattices X1 -> v13_lattices X1 -> v14_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v16_lattices X1 -> False) -> v17_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_lattices X1 -> False) -> v17_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v15_lattices X1 -> False) -> v17_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v14_lattices X1 -> False) -> l3_lattices X1 -> v15_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_lattices X1 -> False) -> l3_lattices X1 -> v15_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v9_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v8_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_lattices X1 -> False) -> v10_lattices X1 -> l3_lattices X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_lattices X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (l1_lattices X1 -> False) -> l3_lattices X1 -> False)
  -> (forall X1, (l2_lattices X1 -> False) -> l3_lattices X1 -> False)
  -> (r1_boolealg esk1_0 (k3_boolealg esk1_0 (k3_boolealg esk1_0 esk2_0 esk3_0) esk4_0) (k3_boolealg esk1_0 esk2_0 (k3_boolealg esk1_0 esk3_0 esk4_0)) -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((l1_struct_0 esk15_0 -> False) -> False)
  -> ((l1_lattices esk14_0 -> False) -> False)
  -> ((l2_lattices esk16_0 -> False) -> False)
  -> ((l3_lattices esk17_0 -> False) -> False)
  -> ((l3_lattices esk1_0 -> False) -> False)
  -> ((v17_lattices esk1_0 -> False) -> False)
  -> ((v10_lattices esk1_0 -> False) -> False)
  -> False.
Admitted.
