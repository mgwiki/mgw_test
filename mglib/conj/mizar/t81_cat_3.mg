(** $I sig/MizarPreamble.mgs **)

Theorem t81_cat_3:
 forall esk11_3:set -> set -> set -> set,
 forall esk4_0:set,
 forall k5_cat_1:set -> set -> set -> set -> set -> set -> set,
 forall m1_cat_1:set -> set -> set -> set -> prop,
 forall esk6_0:set,
 forall esk5_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall k1_xboole_0:set,
 forall esk23_4:set -> set -> set -> set -> set,
 forall a_3_0_cat_1:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk31_2:set -> set -> set,
 forall k1_graph_1:set -> set -> set,
 forall v7_struct_0:set -> prop,
 forall esk26_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk25_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall v15_struct_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall l5_struct_0:set -> prop,
 forall v14_struct_0:set -> prop,
 forall esk28_0:set,
 forall esk22_1:set -> set,
 forall esk19_0:set,
 forall esk17_0:set,
 forall esk20_0:set,
 forall esk18_0:set,
 forall esk24_0:set,
 forall esk27_0:set,
 forall esk29_0:set,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk30_1:set -> set,
 forall k2_graph_1:set -> set -> set,
 forall l1_graph_1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall esk21_3:set -> set -> set -> set,
 forall o_3_1_cat_3:set -> set -> set -> set,
 forall k4_graph_1:set -> set -> set,
 forall esk16_5:set -> set -> set -> set -> set -> set,
 forall esk14_4:set -> set -> set -> set -> set,
 forall esk13_4:set -> set -> set -> set -> set,
 forall esk15_4:set -> set -> set -> set -> set,
 forall esk10_1:set -> set,
 forall esk9_0:set,
 forall esk8_0:set,
 forall esk7_0:set,
 forall k1_cat_1:set -> set -> set -> set,
 forall v11_struct_0:set -> prop,
 forall v2_cat_1:set -> prop,
 forall v4_cat_1:set -> prop,
 forall v6_cat_1:set -> prop,
 forall u4_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall r4_cat_3:set -> set -> set -> set -> prop,
 forall k3_graph_1:set -> set -> set,
 forall l1_cat_1:set -> prop,
 forall v5_cat_1:set -> prop,
 forall v3_cat_1:set -> prop,
 forall k2_cat_1:set -> set -> set -> set,
 forall esk12_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X6 X4 X2 X3 X5 X7 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r2_hidden (esk12_7 X1 X2 X3 X4 X5 X6 X7) (k2_cat_1 X1 X2 X5) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X7 (u4_struct_0 X1) -> m1_subset_1 X6 (u4_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r4_cat_3 X1 X2 X3 X4 -> r2_hidden X7 (k2_cat_1 X1 (k3_graph_1 X1 X4) X5) -> r2_hidden X6 (k2_cat_1 X1 (k3_graph_1 X1 X3) X5) -> False)
  -> (forall X6 X4 X2 X3 X5 X7 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (esk12_7 X1 X2 X3 X4 X5 X6 X7) (u4_struct_0 X1) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X7 (u4_struct_0 X1) -> m1_subset_1 X6 (u4_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r4_cat_3 X1 X2 X3 X4 -> r2_hidden X7 (k2_cat_1 X1 (k3_graph_1 X1 X4) X5) -> r2_hidden X6 (k2_cat_1 X1 (k3_graph_1 X1 X3) X5) -> False)
  -> (forall X8 X6 X5 X7 X1 X2 X3 X4, ((k1_cat_1 X1 X2 X3) = X4 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (esk12_7 X1 X5 X2 X6 X7 X4 X8) = X3 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X8 (u4_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u4_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> r4_cat_3 X1 X5 X2 X6 -> r2_hidden X3 (k2_cat_1 X1 X5 X7) -> r2_hidden X8 (k2_cat_1 X1 (k3_graph_1 X1 X6) X7) -> r2_hidden X4 (k2_cat_1 X1 (k3_graph_1 X1 X2) X7) -> False)
  -> (forall X8 X6 X5 X7 X1 X2 X3 X4, ((k1_cat_1 X1 X2 X3) = X4 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (esk12_7 X1 X5 X6 X2 X7 X8 X4) = X3 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X8 (u4_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u4_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> r4_cat_3 X1 X5 X6 X2 -> r2_hidden X3 (k2_cat_1 X1 X5 X7) -> r2_hidden X8 (k2_cat_1 X1 (k3_graph_1 X1 X6) X7) -> r2_hidden X4 (k2_cat_1 X1 (k3_graph_1 X1 X2) X7) -> False)
  -> (forall X4 X2 X7 X8 X5 X3 X6 X1, ((esk12_7 X1 X7 X2 X5 X8 X4 X6) = X3 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (k1_cat_1 X1 X5 X3) = X6 -> (k1_cat_1 X1 X2 X3) = X4 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u4_struct_0 X1) -> m1_subset_1 X5 (u4_struct_0 X1) -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> r4_cat_3 X1 X7 X2 X5 -> r2_hidden X3 (k2_cat_1 X1 X7 X8) -> r2_hidden X6 (k2_cat_1 X1 (k3_graph_1 X1 X5) X8) -> r2_hidden X4 (k2_cat_1 X1 (k3_graph_1 X1 X2) X8) -> False)
  -> (forall X3 X2 X4 X1, ((esk11_3 X1 X3 X4) = X2 -> False) -> ((k2_cat_1 esk1_0 esk2_0 X1) = k1_xboole_0 -> False) -> ((k2_cat_1 esk1_0 esk4_0 X1) = k1_xboole_0 -> False) -> (r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False) -> (k5_cat_1 esk1_0 esk2_0 esk3_0 X1 esk5_0 X2) = X3 -> (k5_cat_1 esk1_0 esk4_0 esk3_0 X1 esk6_0 X2) = X4 -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> m1_cat_1 X4 esk1_0 esk4_0 X1 -> m1_cat_1 X3 esk1_0 esk2_0 X1 -> m1_cat_1 X2 esk1_0 esk3_0 X1 -> False)
  -> (forall X1, ((k2_cat_1 esk1_0 esk3_0 esk7_0) = k1_xboole_0 -> False) -> (esk10_1 X1) = X1 -> (k5_cat_1 esk1_0 esk2_0 esk3_0 esk7_0 esk5_0 (esk10_1 X1)) = esk8_0 -> (k5_cat_1 esk1_0 esk4_0 esk3_0 esk7_0 esk6_0 (esk10_1 X1)) = esk9_0 -> m1_cat_1 X1 esk1_0 esk3_0 esk7_0 -> r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False)
  -> (forall X3 X5 X6 X2 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_cat_1 (k5_cat_1 X1 X2 X3 X4 X5 X6) X1 X2 X4 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_cat_1 X6 X1 X3 X4 -> m1_cat_1 X5 X1 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r4_cat_3 X1 X3 X2 X4 -> False) -> (k4_graph_1 X1 X4) = X3 -> (k4_graph_1 X1 X2) = X3 -> (esk16_5 X1 X3 X2 X4 X5) = X5 -> (k1_cat_1 X1 X4 (esk16_5 X1 X3 X2 X4 X5)) = (esk15_4 X1 X3 X2 X4) -> (k1_cat_1 X1 X2 (esk16_5 X1 X3 X2 X4 X5)) = (esk14_4 X1 X3 X2 X4) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X5 (u4_struct_0 X1) -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> r2_hidden X5 (k2_cat_1 X1 X3 (esk13_4 X1 X3 X2 X4)) -> False)
  -> (forall X4 X2 X3 X1, ((k2_cat_1 esk1_0 esk2_0 X1) = k1_xboole_0 -> False) -> ((k2_cat_1 esk1_0 esk4_0 X1) = k1_xboole_0 -> False) -> ((k5_cat_1 esk1_0 esk4_0 esk3_0 X1 esk6_0 X2) = X3 -> False) -> (r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False) -> (esk11_3 X1 X4 X3) = X2 -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> m1_cat_1 X4 esk1_0 esk2_0 X1 -> m1_cat_1 X3 esk1_0 esk4_0 X1 -> m1_cat_1 X2 esk1_0 esk3_0 X1 -> False)
  -> (forall X4 X2 X3 X1, ((k2_cat_1 esk1_0 esk2_0 X1) = k1_xboole_0 -> False) -> ((k2_cat_1 esk1_0 esk4_0 X1) = k1_xboole_0 -> False) -> ((k5_cat_1 esk1_0 esk2_0 esk3_0 X1 esk5_0 X2) = X3 -> False) -> (r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False) -> (esk11_3 X1 X3 X4) = X2 -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> m1_cat_1 X4 esk1_0 esk4_0 X1 -> m1_cat_1 X3 esk1_0 esk2_0 X1 -> m1_cat_1 X2 esk1_0 esk3_0 X1 -> False)
  -> (forall X2 X5 X6 X1 X3 X4, ((k2_cat_1 X1 X3 X4) = k1_xboole_0 -> False) -> ((k2_cat_1 X1 X2 X3) = k1_xboole_0 -> False) -> ((k5_cat_1 X1 X2 X3 X4 X5 X6) = (k1_cat_1 X1 X5 X6) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_cat_1 X6 X1 X3 X4 -> m1_cat_1 X5 X1 X2 X3 -> False)
  -> (forall X1, ((esk10_1 X1) = X1 -> False) -> ((k2_cat_1 esk1_0 esk3_0 esk7_0) = k1_xboole_0 -> False) -> ((k5_cat_1 esk1_0 esk4_0 esk3_0 esk7_0 esk6_0 (esk10_1 X1)) = esk9_0 -> False) -> m1_cat_1 X1 esk1_0 esk3_0 esk7_0 -> r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False)
  -> (forall X1, ((esk10_1 X1) = X1 -> False) -> ((k2_cat_1 esk1_0 esk3_0 esk7_0) = k1_xboole_0 -> False) -> ((k5_cat_1 esk1_0 esk2_0 esk3_0 esk7_0 esk5_0 (esk10_1 X1)) = esk8_0 -> False) -> m1_cat_1 X1 esk1_0 esk3_0 esk7_0 -> r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False)
  -> (forall X5 X3 X2 X4 X1, ((esk16_5 X1 X3 X2 X4 X5) = X5 -> False) -> ((k1_cat_1 X1 X2 (esk16_5 X1 X3 X2 X4 X5)) = (esk14_4 X1 X3 X2 X4) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r4_cat_3 X1 X3 X2 X4 -> False) -> (k4_graph_1 X1 X4) = X3 -> (k4_graph_1 X1 X2) = X3 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X5 (u4_struct_0 X1) -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> r2_hidden X5 (k2_cat_1 X1 X3 (esk13_4 X1 X3 X2 X4)) -> False)
  -> (forall X5 X3 X4 X2 X1, ((esk16_5 X1 X3 X4 X2 X5) = X5 -> False) -> ((k1_cat_1 X1 X2 (esk16_5 X1 X3 X4 X2 X5)) = (esk15_4 X1 X3 X4 X2) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r4_cat_3 X1 X3 X4 X2 -> False) -> (k4_graph_1 X1 X4) = X3 -> (k4_graph_1 X1 X2) = X3 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X5 (u4_struct_0 X1) -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> r2_hidden X5 (k2_cat_1 X1 X3 (esk13_4 X1 X3 X4 X2)) -> False)
  -> (forall X5 X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r4_cat_3 X1 X2 X3 X4 -> False) -> (r2_hidden (esk16_5 X1 X2 X3 X4 X5) (k2_cat_1 X1 X2 (esk13_4 X1 X2 X3 X4)) -> False) -> (k4_graph_1 X1 X4) = X2 -> (k4_graph_1 X1 X3) = X2 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X5 (u4_struct_0 X1) -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_hidden X5 (k2_cat_1 X1 X2 (esk13_4 X1 X2 X3 X4)) -> False)
  -> (forall X5 X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r4_cat_3 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk16_5 X1 X2 X3 X4 X5) (u4_struct_0 X1) -> False) -> (k4_graph_1 X1 X4) = X2 -> (k4_graph_1 X1 X3) = X2 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X5 (u4_struct_0 X1) -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_hidden X5 (k2_cat_1 X1 X2 (esk13_4 X1 X2 X3 X4)) -> False)
  -> (forall X3 X4 X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r4_cat_3 X1 X2 X3 X4 -> False) -> (r2_hidden (esk15_4 X1 X2 X3 X4) (k2_cat_1 X1 (k3_graph_1 X1 X4) (esk13_4 X1 X2 X3 X4)) -> False) -> (k4_graph_1 X1 X4) = X2 -> (k4_graph_1 X1 X3) = X2 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r4_cat_3 X1 X2 X3 X4 -> False) -> (r2_hidden (esk14_4 X1 X2 X3 X4) (k2_cat_1 X1 (k3_graph_1 X1 X3) (esk13_4 X1 X2 X3 X4)) -> False) -> (k4_graph_1 X1 X4) = X2 -> (k4_graph_1 X1 X3) = X2 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k2_cat_1 esk1_0 esk2_0 X1) = k1_xboole_0 -> False) -> ((k2_cat_1 esk1_0 esk4_0 X1) = k1_xboole_0 -> False) -> (r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False) -> (m1_cat_1 (esk11_3 X1 X2 X3) esk1_0 esk3_0 X1 -> False) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> m1_cat_1 X3 esk1_0 esk4_0 X1 -> m1_cat_1 X2 esk1_0 esk2_0 X1 -> False)
  -> (forall X1, ((k2_cat_1 esk1_0 esk3_0 esk7_0) = k1_xboole_0 -> False) -> (m1_cat_1 (esk10_1 X1) esk1_0 esk3_0 esk7_0 -> False) -> m1_cat_1 X1 esk1_0 esk3_0 esk7_0 -> r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False)
  -> (forall X3 X4 X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r4_cat_3 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk15_4 X1 X2 X3 X4) (u4_struct_0 X1) -> False) -> (k4_graph_1 X1 X4) = X2 -> (k4_graph_1 X1 X3) = X2 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r4_cat_3 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk14_4 X1 X2 X3 X4) (u4_struct_0 X1) -> False) -> (k4_graph_1 X1 X4) = X2 -> (k4_graph_1 X1 X3) = X2 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r4_cat_3 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk13_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> (k4_graph_1 X1 X4) = X2 -> (k4_graph_1 X1 X3) = X2 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X1 X3 X2, (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> (m1_subset_1 (esk23_4 X1 X2 X3 X4) (u4_struct_0 X2) -> False) -> l1_cat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (a_3_0_cat_1 X2 X3 X4) -> False)
  -> (forall X4 X2 X3 X1, ((k3_graph_1 X1 (esk23_4 X2 X1 X3 X4)) = X3 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> r2_hidden X2 (a_3_0_cat_1 X1 X3 X4) -> False)
  -> (forall X4 X2 X3 X1, ((k4_graph_1 X1 (esk23_4 X2 X1 X3 X4)) = X4 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> r2_hidden X2 (a_3_0_cat_1 X1 X3 X4) -> False)
  -> (forall X1 X2 X3 X4, ((k2_cat_1 X2 X3 X4) = k1_xboole_0 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> (r2_hidden X1 (k2_cat_1 X2 X3 X4) -> False) -> l1_cat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u4_struct_0 X2) -> m1_cat_1 X1 X2 X3 X4 -> False)
  -> (((k2_cat_1 esk1_0 esk3_0 esk7_0) = k1_xboole_0 -> False) -> (m1_cat_1 esk9_0 esk1_0 esk4_0 esk7_0 -> False) -> r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False)
  -> (((k2_cat_1 esk1_0 esk3_0 esk7_0) = k1_xboole_0 -> False) -> (m1_cat_1 esk8_0 esk1_0 esk2_0 esk7_0 -> False) -> r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False)
  -> (forall X1 X2 X3 X4, ((k2_cat_1 X2 X3 X4) = k1_xboole_0 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> (m1_cat_1 X1 X2 X3 X4 -> False) -> l1_cat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u4_struct_0 X2) -> r2_hidden X1 (k2_cat_1 X2 X3 X4) -> False)
  -> (forall X4 X2 X1 X3, ((k4_graph_1 X1 X2) = X3 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> r4_cat_3 X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X1 X3, ((k4_graph_1 X1 X2) = X3 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X4 (u4_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> r4_cat_3 X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X1 X3, ((k3_graph_1 X1 X2) = X3 -> False) -> ((k2_cat_1 X1 X3 X4) = k1_xboole_0 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_cat_1 X2 X1 X3 X4 -> False)
  -> (forall X4 X2 X1 X3, ((k4_graph_1 X1 X2) = X3 -> False) -> ((k2_cat_1 X1 X4 X3) = k1_xboole_0 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_cat_1 X2 X1 X4 X3 -> False)
  -> (forall X4 X1 X3 X2, ((esk23_4 X1 X2 X3 X4) = X1 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> l1_cat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (a_3_0_cat_1 X2 X3 X4) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 X4 (u4_struct_0 X1) -> False) -> l1_cat_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_cat_1 X4 X1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_cat_1 (o_3_1_cat_3 X1 X2 X3) X1 X2 X3 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> ((k2_cat_1 esk1_0 esk4_0 esk7_0) = k1_xboole_0 -> r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False)
  -> ((k2_cat_1 esk1_0 esk2_0 esk7_0) = k1_xboole_0 -> r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False)
  -> (forall X1, ((k2_cat_1 esk1_0 esk2_0 X1) = k1_xboole_0 -> False) -> ((k2_cat_1 esk1_0 esk4_0 X1) = k1_xboole_0 -> False) -> (r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False) -> (k2_cat_1 esk1_0 esk3_0 X1) = k1_xboole_0 -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_cat_1 (esk21_3 X1 X2 X3) X1 X2 X3 -> False) -> l1_cat_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> ((m1_subset_1 esk7_0 (u1_struct_0 esk1_0) -> False) -> r4_cat_3 esk1_0 esk3_0 esk5_0 esk6_0 -> False)
  -> (forall X1 X5 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> (r2_hidden X3 (a_3_0_cat_1 X2 X4 X5) -> False) -> X1 = X3 -> (k4_graph_1 X2 X1) = X5 -> (k3_graph_1 X2 X1) = X4 -> l1_cat_1 X2 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u4_struct_0 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> v5_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> v1_xboole_0 (k2_cat_1 X1 X2 X2) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (k2_cat_1 X1 X2 X3) (k1_zfmisc_1 (u4_struct_0 X1)) -> False) -> l1_cat_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k1_cat_1 X1 X2 X3) (u4_struct_0 X1) -> False) -> l1_cat_1 X1 -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((a_3_0_cat_1 X1 X2 X3) = (k2_cat_1 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_cat_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk31_2 X3 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (k3_graph_1 X1 X2) (u1_struct_0 X1) -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (k4_graph_1 X1 X2) (u1_struct_0 X1) -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_graph_1 X1 X2) (u1_struct_0 X1) -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_graph_1 X1 X2) (u1_struct_0 X1) -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, ((k4_graph_1 X1 X2) = (k2_graph_1 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, ((k3_graph_1 X1 X2) = (k1_graph_1 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk31_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v15_struct_0 X1 -> False) -> l5_struct_0 X1 -> v1_zfmisc_1 (u4_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk26_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v11_struct_0 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (u4_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk30_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk25_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v6_cat_1 X1 -> False) -> l1_cat_1 X1 -> v15_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v5_cat_1 X1 -> False) -> l1_cat_1 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v4_cat_1 X1 -> False) -> l1_cat_1 X1 -> v15_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v3_cat_1 X1 -> False) -> l1_cat_1 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v11_struct_0 X1 -> False) -> v2_struct_0 X1 -> l5_struct_0 X1 -> v14_struct_0 X1 -> False)
  -> (forall X1, (v11_struct_0 X1 -> False) -> v2_struct_0 X1 -> l5_struct_0 X1 -> v14_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u4_struct_0 X1) -> False) -> l5_struct_0 X1 -> v15_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u4_struct_0 X1) -> False) -> v11_struct_0 X1 -> l5_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk25_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v15_struct_0 X1 -> False) -> v11_struct_0 X1 -> l5_struct_0 X1 -> False)
  -> (forall X1, (v14_struct_0 X1 -> False) -> v11_struct_0 X1 -> l5_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v14_struct_0 X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (l1_graph_1 X1 -> False) -> l1_cat_1 X1 -> False)
  -> (forall X1, (l5_struct_0 X1 -> False) -> l1_graph_1 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_cat_1 esk1_0 esk4_0 esk3_0) = k1_xboole_0 -> False)
  -> ((k2_cat_1 esk1_0 esk2_0 esk3_0) = k1_xboole_0 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v15_struct_0 esk27_0 -> False)
  -> (v11_struct_0 esk28_0 -> False)
  -> (v11_struct_0 esk1_0 -> False)
  -> (v2_struct_0 esk28_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> ((m1_cat_1 esk6_0 esk1_0 esk4_0 esk3_0 -> False) -> False)
  -> ((m1_cat_1 esk5_0 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v1_xboole_0 esk24_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_graph_1 esk18_0 -> False) -> False)
  -> ((l5_struct_0 esk27_0 -> False) -> False)
  -> ((l5_struct_0 esk20_0 -> False) -> False)
  -> ((l1_struct_0 esk19_0 -> False) -> False)
  -> ((l1_cat_1 esk28_0 -> False) -> False)
  -> ((l1_cat_1 esk17_0 -> False) -> False)
  -> ((l1_cat_1 esk1_0 -> False) -> False)
  -> ((v6_cat_1 esk1_0 -> False) -> False)
  -> ((v5_cat_1 esk1_0 -> False) -> False)
  -> ((v4_cat_1 esk1_0 -> False) -> False)
  -> ((v3_cat_1 esk1_0 -> False) -> False)
  -> ((v2_cat_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
