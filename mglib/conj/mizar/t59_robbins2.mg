(** $I sig/MizarPreamble.mgs **)

Theorem t59_robbins2:
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall k6_robbins1:set -> set -> set -> set,
 forall k5_robbins1:set -> set -> set -> set,
 forall v4_lattices:set -> prop,
 forall v6_robbins1:set -> prop,
 forall k4_robbins1:set -> set -> set -> set,
 forall v7_robbins1:set -> prop,
 forall v14_lattices:set -> prop,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall l1_struct_0:set -> prop,
 forall k1_xboole_0:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk14_0:set,
 forall esk13_1:set -> set,
 forall esk11_0:set,
 forall esk12_0:set,
 forall esk10_0:set,
 forall esk9_0:set,
 forall esk1_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall v7_struct_0:set -> prop,
 forall v5_robbins1:set -> prop,
 forall l1_robbins1:set -> prop,
 forall v5_lattices:set -> prop,
 forall esk7_1:set -> set,
 forall esk8_1:set -> set,
 forall esk6_1:set -> set,
 forall l2_lattices:set -> prop,
 forall v1_robbins2:set -> prop,
 forall esk4_1:set -> set,
 forall k1_lattices:set -> set -> set -> set,
 forall esk2_1:set -> set,
 forall esk5_1:set -> set,
 forall esk3_1:set -> set,
 forall k3_robbins1:set -> set -> set,
 forall l2_robbins1:set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X1, (v2_struct_0 X1 -> False) -> (v1_robbins2 X1 -> False) -> (k3_robbins1 X1 (k1_lattices X1 (k3_robbins1 X1 (k1_lattices X1 (k3_robbins1 X1 (k1_lattices X1 (esk2_1 X1) (esk3_1 X1))) (esk4_1 X1))) (k3_robbins1 X1 (k1_lattices X1 (esk2_1 X1) (k3_robbins1 X1 (k1_lattices X1 (k3_robbins1 X1 (esk4_1 X1)) (k3_robbins1 X1 (k1_lattices X1 (esk4_1 X1) (esk5_1 X1))))))))) = (esk4_1 X1) -> l2_robbins1 X1 -> False)
  -> (forall X5 X2 X3 X4 X1, ((k3_robbins1 X1 (k1_lattices X1 (k3_robbins1 X1 (k1_lattices X1 (k3_robbins1 X1 (k1_lattices X1 X2 X3)) X4)) (k3_robbins1 X1 (k1_lattices X1 X2 (k3_robbins1 X1 (k1_lattices X1 (k3_robbins1 X1 X4) (k3_robbins1 X1 (k1_lattices X1 X4 X5)))))))) = X4 -> False) -> (v2_struct_0 X1 -> False) -> l2_robbins1 X1 -> v1_robbins2 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (k1_lattices X1 (k1_lattices X1 (esk6_1 X1) (esk7_1 X1)) (esk8_1 X1)) = (k1_lattices X1 (esk6_1 X1) (k1_lattices X1 (esk7_1 X1) (esk8_1 X1))) -> l2_lattices X1 -> False)
  -> (forall X4 X3 X2 X1, ((k5_robbins1 X1 (k6_robbins1 X1 X2 X3) (k6_robbins1 X1 X2 X4)) = (k6_robbins1 X1 X2 (k5_robbins1 X1 X3 X4)) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v6_robbins1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, ((k6_robbins1 X1 (k5_robbins1 X1 X2 X3) (k5_robbins1 X1 X2 X4)) = (k5_robbins1 X1 X2 (k6_robbins1 X1 X3 X4)) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v6_robbins1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, ((k6_robbins1 X1 (k6_robbins1 X1 X2 X3) X4) = (k6_robbins1 X1 X2 (k6_robbins1 X1 X3 X4)) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v6_robbins1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, ((k1_lattices X1 (k1_lattices X1 X2 X3) X4) = (k1_lattices X1 X2 (k1_lattices X1 X3 X4)) -> False) -> (v2_struct_0 X1 -> False) -> v5_lattices X1 -> l2_lattices X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k4_robbins1 X1 (k1_lattices X1 X3 X2) (k1_lattices X1 X3 (k3_robbins1 X1 X2))) = X3 -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v6_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k3_robbins1 X1 (k6_robbins1 X1 (k3_robbins1 X1 X2) (k3_robbins1 X1 X3))) = (k5_robbins1 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v6_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k6_robbins1 X1 X2 (k5_robbins1 X1 X2 X3)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v6_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k6_robbins1 X1 X2 X3) (u1_struct_0 X1) -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k5_robbins1 X1 X2 X3) (u1_struct_0 X1) -> False) -> v4_lattices X1 -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k4_robbins1 X1 X2 X3) (u1_struct_0 X1) -> False) -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k1_lattices X1 X2 X3) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_robbins1 X1 X2 X3) = (k4_robbins1 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_robbins1 X1 X2 X3) = (k6_robbins1 X1 X3 X2) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k5_robbins1 X1 X2 X3) = (k1_lattices X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k5_robbins1 X1 X2 X3) = (k5_robbins1 X1 X3 X2) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k5_robbins1 X1 X2 X2) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v6_robbins1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k3_robbins1 X1 (k3_robbins1 X1 X2)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v6_robbins1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k3_robbins1 X1 X2) (u1_struct_0 X1) -> False) -> l1_robbins1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v14_lattices X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v6_robbins1 X1 -> v7_robbins1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_robbins2 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> l2_robbins1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_robbins2 X1 -> False) -> (m1_subset_1 (esk4_1 X1) (u1_struct_0 X1) -> False) -> l2_robbins1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_robbins2 X1 -> False) -> (m1_subset_1 (esk3_1 X1) (u1_struct_0 X1) -> False) -> l2_robbins1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_robbins2 X1 -> False) -> (m1_subset_1 (esk2_1 X1) (u1_struct_0 X1) -> False) -> l2_robbins1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_robbins1 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v6_robbins1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_robbins1 X1 -> False) -> v4_lattices X1 -> v5_lattices X1 -> l2_robbins1 X1 -> v5_robbins1 X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_robbins1 X1 -> False) -> l2_robbins1 X1 -> v1_robbins2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> l2_robbins1 X1 -> v1_robbins2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_lattices X1 -> False) -> l2_robbins1 X1 -> v1_robbins2 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (l1_robbins1 X1 -> False) -> l2_robbins1 X1 -> False)
  -> (forall X1, (l2_lattices X1 -> False) -> l2_robbins1 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_robbins1 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l2_lattices X1 -> False)
  -> (v1_robbins2 esk1_0 -> False)
  -> (v2_struct_0 esk14_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> ((l1_robbins1 esk9_0 -> False) -> False)
  -> ((l2_lattices esk11_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((v1_robbins2 esk14_0 -> False) -> False)
  -> ((v5_robbins1 esk1_0 -> False) -> False)
  -> ((l2_robbins1 esk14_0 -> False) -> False)
  -> ((l2_robbins1 esk12_0 -> False) -> False)
  -> ((l2_robbins1 esk1_0 -> False) -> False)
  -> ((v5_lattices esk14_0 -> False) -> False)
  -> ((v5_lattices esk1_0 -> False) -> False)
  -> ((v4_lattices esk14_0 -> False) -> False)
  -> ((v4_lattices esk1_0 -> False) -> False)
  -> False.
Admitted.
