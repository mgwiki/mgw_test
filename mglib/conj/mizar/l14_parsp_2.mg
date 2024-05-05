(** $I sig/MizarPreamble.mgs **)

Theorem l14_parsp_2:
 forall k1_group_1:set -> set,
 forall k5_algstr_0:set -> set -> set -> set,
 forall k8_group_1:set -> set -> set -> set,
 forall k3_rlvect_1:set -> set -> set -> set,
 forall v6_struct_0:set -> prop,
 forall v13_algstr_0:set -> prop,
 forall v3_group_1:set -> prop,
 forall v4_vectsp_1:set -> prop,
 forall v2_rlvect_1:set -> prop,
 forall v4_rlvect_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall v3_rlvect_1:set -> prop,
 forall v5_group_1:set -> prop,
 forall v33_algstr_0:set -> prop,
 forall v2_vectsp_1:set -> prop,
 forall v7_struct_0:set -> prop,
 forall v9_struct_0:set -> set -> prop,
 forall esk26_1:set -> set,
 forall l2_struct_0:set -> prop,
 forall esk25_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk30_0:set,
 forall esk32_0:set,
 forall esk29_0:set,
 forall esk24_0:set,
 forall esk6_0:set,
 forall esk23_1:set -> set,
 forall esk27_0:set,
 forall esk18_0:set,
 forall esk16_0:set,
 forall esk13_0:set,
 forall esk19_0:set,
 forall esk22_0:set,
 forall esk14_0:set,
 forall esk20_0:set,
 forall esk17_0:set,
 forall esk15_0:set,
 forall esk21_0:set,
 forall esk28_0:set,
 forall esk31_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall l5_algstr_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v1_vectsp_1:set -> prop,
 forall v1_group_1:set -> prop,
 forall v6_vectsp_1:set -> prop,
 forall v3_vectsp_1:set -> prop,
 forall l4_algstr_0:set -> prop,
 forall k1_xboole_0:set,
 forall l3_struct_0:set -> prop,
 forall l1_struct_0:set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall l4_struct_0:set -> prop,
 forall k5_struct_0:set -> set,
 forall k4_struct_0:set -> set,
 forall l3_algstr_0:set -> prop,
 forall l2_algstr_0:set -> prop,
 forall k4_algstr_0:set -> set -> set,
 forall l1_algstr_0:set -> prop,
 forall esk7_1:set -> set,
 forall esk9_1:set -> set,
 forall esk8_1:set -> set,
 forall v5_vectsp_1:set -> prop,
 forall l6_algstr_0:set -> prop,
 forall k6_algstr_0:set -> set -> set -> set,
 forall esk10_1:set -> set,
 forall k1_algstr_0:set -> set -> set -> set,
 forall esk12_1:set -> set,
 forall esk11_1:set -> set,
 forall v2_struct_0:set -> prop,
     (forall X1, (v2_struct_0 X1 -> False) -> (v5_vectsp_1 X1 -> False) -> (k1_algstr_0 X1 (k6_algstr_0 X1 (esk10_1 X1) (esk11_1 X1)) (k6_algstr_0 X1 (esk10_1 X1) (esk12_1 X1))) = (k6_algstr_0 X1 (esk10_1 X1) (k1_algstr_0 X1 (esk11_1 X1) (esk12_1 X1))) -> (k1_algstr_0 X1 (k6_algstr_0 X1 (esk11_1 X1) (esk10_1 X1)) (k6_algstr_0 X1 (esk12_1 X1) (esk10_1 X1))) = (k6_algstr_0 X1 (k1_algstr_0 X1 (esk11_1 X1) (esk12_1 X1)) (esk10_1 X1)) -> l6_algstr_0 X1 -> False)
  -> (forall X2 X3 X4 X1, ((k8_group_1 X1 (k3_rlvect_1 X1 X2 (k1_group_1 X1)) X4) = (k8_group_1 X1 (k5_algstr_0 X1 X2 (k1_group_1 X1)) X3) -> False) -> (v2_struct_0 X1 -> False) -> (v6_struct_0 X1 -> False) -> (k5_algstr_0 X1 (k8_group_1 X1 X2 X3) (k8_group_1 X1 X2 X4)) = (k3_rlvect_1 X1 X4 X3) -> v13_algstr_0 X1 -> v33_algstr_0 X1 -> v3_group_1 X1 -> v5_group_1 X1 -> v4_vectsp_1 X1 -> v5_vectsp_1 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l6_algstr_0 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v3_rlvect_1 X1 -> False) -> (k1_algstr_0 X1 (k1_algstr_0 X1 (esk7_1 X1) (esk8_1 X1)) (esk9_1 X1)) = (k1_algstr_0 X1 (esk7_1 X1) (k1_algstr_0 X1 (esk8_1 X1) (esk9_1 X1))) -> l1_algstr_0 X1 -> False)
  -> (forall X4 X3 X2 X1, ((k1_algstr_0 X1 (k6_algstr_0 X1 X2 X4) (k6_algstr_0 X1 X3 X4)) = (k6_algstr_0 X1 (k1_algstr_0 X1 X2 X3) X4) -> False) -> (v2_struct_0 X1 -> False) -> v5_vectsp_1 X1 -> l6_algstr_0 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, ((k1_algstr_0 X1 (k6_algstr_0 X1 X2 X3) (k6_algstr_0 X1 X2 X4)) = (k6_algstr_0 X1 X2 (k1_algstr_0 X1 X3 X4)) -> False) -> (v2_struct_0 X1 -> False) -> v5_vectsp_1 X1 -> l6_algstr_0 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, ((k1_algstr_0 X1 (k1_algstr_0 X1 X2 X3) X4) = (k1_algstr_0 X1 X2 (k1_algstr_0 X1 X3 X4)) -> False) -> v3_rlvect_1 X1 -> l1_algstr_0 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k1_algstr_0 X1 (k4_algstr_0 X1 X3) (k4_algstr_0 X1 X2)) = (k4_algstr_0 X1 (k1_algstr_0 X1 X2 X3)) -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l2_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 (k4_algstr_0 X1 X2) X3) = (k4_algstr_0 X1 (k6_algstr_0 X1 X2 X3)) -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l6_algstr_0 X1 -> v2_vectsp_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k1_algstr_0 X1 X3 (k4_algstr_0 X1 X2)) = (k4_algstr_0 X1 (k5_algstr_0 X1 X2 X3)) -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l2_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 (k4_algstr_0 X1 X2) (k4_algstr_0 X1 X3)) = (k6_algstr_0 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v5_vectsp_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l6_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k8_group_1 X1 X2 X3) (u1_struct_0 X1) -> False) -> v5_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k1_algstr_0 X1 X2 (k4_algstr_0 X1 X3)) = (k5_algstr_0 X1 X2 X3) -> False) -> l2_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k3_rlvect_1 X1 X2 X3) (u1_struct_0 X1) -> False) -> v2_rlvect_1 X1 -> l1_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k6_algstr_0 X1 X2 X3) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k1_algstr_0 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k5_algstr_0 X1 X2 X3) (u1_struct_0 X1) -> False) -> l2_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k6_algstr_0 X1 X2 X3) = (k8_group_1 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v5_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k8_group_1 X1 X2 X3) = (k8_group_1 X1 X3 X2) -> False) -> (v2_struct_0 X1 -> False) -> v5_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k1_algstr_0 X1 X2 X3) = (k3_rlvect_1 X1 X2 X3) -> False) -> v2_rlvect_1 X1 -> l1_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k3_rlvect_1 X1 X2 X3) = (k3_rlvect_1 X1 X3 X2) -> False) -> v2_rlvect_1 X1 -> l1_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k1_algstr_0 X1 (k4_algstr_0 X1 X2) X2) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l2_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k1_algstr_0 X1 X2 (k4_algstr_0 X1 X2)) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l2_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k1_algstr_0 X1 (k4_struct_0 X1) X2) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l2_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k1_algstr_0 X1 X2 (k4_struct_0 X1)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l2_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k4_algstr_0 X1 X2) (u1_struct_0 X1) -> False) -> l2_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l2_struct_0 X1 -> v9_struct_0 (esk26_1 X1) X1 -> False)
  -> (forall X1, (v6_struct_0 X1 -> False) -> l4_struct_0 X1 -> v9_struct_0 (k5_struct_0 X1) X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_vectsp_1 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (u1_struct_0 X1) -> False) -> l6_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_vectsp_1 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (u1_struct_0 X1) -> False) -> l6_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_vectsp_1 X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u1_struct_0 X1) -> False) -> l6_algstr_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (u1_struct_0 X1) -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (v3_rlvect_1 X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> l1_algstr_0 X1 -> False)
  -> (forall X1, (v3_rlvect_1 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> l1_algstr_0 X1 -> False)
  -> (forall X1, (v3_rlvect_1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> l1_algstr_0 X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (u1_struct_0 X1) -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k5_struct_0 X1) (u1_struct_0 X1) -> False) -> l3_struct_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k4_struct_0 X1) (u1_struct_0 X1) -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k1_group_1 X1) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_group_1 X1 -> False) -> l4_algstr_0 X1 -> v3_vectsp_1 X1 -> v6_vectsp_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_vectsp_1 X1 -> False) -> v5_group_1 X1 -> l4_algstr_0 X1 -> v6_vectsp_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_vectsp_1 X1 -> False) -> l6_algstr_0 X1 -> v1_vectsp_1 X1 -> v2_vectsp_1 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v9_struct_0 (esk25_1 X1) X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (v9_struct_0 (k4_struct_0 X1) X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, ((k5_struct_0 X1) = (k1_group_1 X1) -> False) -> (v2_struct_0 X1 -> False) -> v4_vectsp_1 X1 -> l4_algstr_0 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_group_1 X1 -> False) -> v4_vectsp_1 X1 -> l4_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_vectsp_1 X1 -> False) -> v4_vectsp_1 X1 -> l4_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_vectsp_1 X1 -> False) -> v4_vectsp_1 X1 -> l4_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_vectsp_1 X1 -> False) -> v5_vectsp_1 X1 -> l6_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_vectsp_1 X1 -> False) -> v5_vectsp_1 X1 -> l6_algstr_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v6_struct_0 X1 -> False) -> v7_struct_0 X1 -> l4_struct_0 X1 -> False)
  -> (forall X1, (l5_algstr_0 X1 -> False) -> l6_algstr_0 X1 -> False)
  -> (forall X1, (l3_struct_0 X1 -> False) -> l4_algstr_0 X1 -> False)
  -> (forall X1, (l3_struct_0 X1 -> False) -> l4_struct_0 X1 -> False)
  -> (forall X1, (l2_struct_0 X1 -> False) -> l2_algstr_0 X1 -> False)
  -> (forall X1, (l2_struct_0 X1 -> False) -> l4_struct_0 X1 -> False)
  -> (forall X1, (l2_algstr_0 X1 -> False) -> l6_algstr_0 X1 -> False)
  -> (forall X1, (l3_algstr_0 X1 -> False) -> l4_algstr_0 X1 -> False)
  -> (forall X1, (l1_algstr_0 X1 -> False) -> l2_algstr_0 X1 -> False)
  -> (forall X1, (l4_algstr_0 X1 -> False) -> l5_algstr_0 X1 -> False)
  -> (forall X1, (l4_struct_0 X1 -> False) -> l5_algstr_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l3_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_algstr_0 X1 -> False)
  -> ((k8_group_1 esk1_0 (k5_algstr_0 esk1_0 esk2_0 (k1_group_1 esk1_0)) (k5_algstr_0 esk1_0 esk5_0 esk4_0)) = (k8_group_1 esk1_0 (k3_rlvect_1 esk1_0 esk2_0 (k1_group_1 esk1_0)) (k5_algstr_0 esk1_0 esk5_0 esk3_0)) -> False)
  -> (v1_xboole_0 esk30_0 -> False)
  -> (v6_struct_0 esk1_0 -> False)
  -> (v2_struct_0 esk32_0 -> False)
  -> (v2_struct_0 esk31_0 -> False)
  -> (v2_struct_0 esk29_0 -> False)
  -> (v2_struct_0 esk28_0 -> False)
  -> (v2_struct_0 esk24_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (((k8_group_1 esk1_0 esk2_0 (k5_algstr_0 esk1_0 esk3_0 esk4_0)) = (k5_algstr_0 esk1_0 esk5_0 esk6_0) -> False) -> False)
  -> (((k5_algstr_0 esk1_0 (k3_rlvect_1 esk1_0 esk3_0 esk4_0) esk5_0) = esk6_0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v1_xboole_0 esk27_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l5_algstr_0 esk29_0 -> False) -> False)
  -> ((l5_algstr_0 esk21_0 -> False) -> False)
  -> ((l3_struct_0 esk18_0 -> False) -> False)
  -> ((l2_struct_0 esk28_0 -> False) -> False)
  -> ((l2_struct_0 esk16_0 -> False) -> False)
  -> ((l2_algstr_0 esk15_0 -> False) -> False)
  -> ((l3_algstr_0 esk31_0 -> False) -> False)
  -> ((l3_algstr_0 esk17_0 -> False) -> False)
  -> ((l1_algstr_0 esk13_0 -> False) -> False)
  -> ((v1_group_1 esk32_0 -> False) -> False)
  -> ((l4_algstr_0 esk32_0 -> False) -> False)
  -> ((l4_algstr_0 esk24_0 -> False) -> False)
  -> ((l4_algstr_0 esk19_0 -> False) -> False)
  -> ((l4_struct_0 esk20_0 -> False) -> False)
  -> ((v7_struct_0 esk28_0 -> False) -> False)
  -> ((l1_struct_0 esk14_0 -> False) -> False)
  -> ((l6_algstr_0 esk22_0 -> False) -> False)
  -> ((l6_algstr_0 esk1_0 -> False) -> False)
  -> ((v4_rlvect_1 esk1_0 -> False) -> False)
  -> ((v3_rlvect_1 esk1_0 -> False) -> False)
  -> ((v2_rlvect_1 esk1_0 -> False) -> False)
  -> ((v5_vectsp_1 esk1_0 -> False) -> False)
  -> ((v4_vectsp_1 esk29_0 -> False) -> False)
  -> ((v4_vectsp_1 esk24_0 -> False) -> False)
  -> ((v4_vectsp_1 esk1_0 -> False) -> False)
  -> ((v5_group_1 esk32_0 -> False) -> False)
  -> ((v5_group_1 esk31_0 -> False) -> False)
  -> ((v5_group_1 esk1_0 -> False) -> False)
  -> ((v3_group_1 esk32_0 -> False) -> False)
  -> ((v3_group_1 esk31_0 -> False) -> False)
  -> ((v3_group_1 esk1_0 -> False) -> False)
  -> ((v33_algstr_0 esk1_0 -> False) -> False)
  -> ((v13_algstr_0 esk1_0 -> False) -> False)
  -> False.
Admitted.
