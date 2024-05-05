(** $I sig/MizarPreamble.mgs **)

Theorem t76_cat_3:
 forall esk19_4:set -> set -> set -> set -> set,
 forall a_3_0_cat_1:set -> set -> set -> set,
 forall esk18_3:set -> set -> set -> set,
 forall k8_funcop_1:set -> set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk28_2:set -> set -> set,
 forall k2_graph_1:set -> set -> set,
 forall v7_struct_0:set -> prop,
 forall esk23_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk22_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v14_struct_0:set -> prop,
 forall esk25_0:set,
 forall esk20_2:set -> set -> set,
 forall esk17_1:set -> set,
 forall esk21_0:set,
 forall esk14_0:set,
 forall esk12_0:set,
 forall esk15_0:set,
 forall esk13_0:set,
 forall esk24_0:set,
 forall esk26_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall l5_struct_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v15_struct_0:set -> prop,
 forall k1_xboole_0:set,
 forall r1_tarski:set -> set -> prop,
 forall esk27_1:set -> set,
 forall k1_graph_1:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall l1_graph_1:set -> prop,
 forall k4_cat_1:set -> set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall m1_cat_1:set -> set -> set -> set -> prop,
 forall k1_tarski:set -> set,
 forall k1_cat_3:set -> set -> set -> set,
 forall k10_funct_2:set -> set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall k4_graph_1:set -> set -> set,
 forall esk10_4:set -> set -> set -> set -> set,
 forall k3_graph_1:set -> set -> set,
 forall esk8_5:set -> set -> set -> set -> set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall esk9_5:set -> set -> set -> set -> set -> set,
 forall esk7_4:set -> set -> set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall esk5_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall u4_struct_0:set -> set,
 forall k7_partfun1:set -> set -> set -> set,
 forall k1_cat_1:set -> set -> set -> set,
 forall v3_cat_1:set -> prop,
 forall v5_cat_1:set -> prop,
 forall l1_cat_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall m2_cat_3:set -> set -> set -> set -> prop,
 forall k2_cat_1:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall r2_funct_2:set -> set -> set -> set -> prop,
 forall k2_cat_3:set -> set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall r3_cat_3:set -> set -> set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall v1_funct_1:set -> prop,
 forall v6_cat_1:set -> prop,
 forall v4_cat_1:set -> prop,
 forall v2_cat_1:set -> prop,
 forall v11_struct_0:set -> prop,
 forall esk4_6:set -> set -> set -> set -> set -> set -> set,
     (forall X7 X3 X6 X4 X5 X2 X1, ((esk4_6 X1 X3 X4 X2 X5 X6) = X7 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (k1_cat_1 X1 (k7_partfun1 (u4_struct_0 X1) X2 (esk5_7 X1 X3 X4 X2 X5 X6 X7)) X7) = (k7_partfun1 (u4_struct_0 X1) X6 (esk5_7 X1 X3 X4 X2 X5 X6 X7)) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X2 -> m1_subset_1 X7 (u4_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> r3_cat_3 X1 X3 X4 X2 -> m2_cat_3 X6 X1 X5 X4 -> v1_funct_2 X2 X4 (u4_struct_0 X1) -> r2_hidden X7 (k2_cat_1 X1 X3 X5) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X4 (u4_struct_0 X1))) -> r2_funct_2 X4 (u1_struct_0 X1) (k2_cat_3 X1 X4 X2) (k2_cat_3 X1 X4 X6) -> False)
  -> (forall X7 X2 X6 X3 X5 X4 X1, ((esk4_6 X1 X2 X3 X4 X5 X6) = X7 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r2_hidden (esk5_7 X1 X2 X3 X4 X5 X6 X7) X3 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> m1_subset_1 X7 (u4_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r3_cat_3 X1 X2 X3 X4 -> m2_cat_3 X6 X1 X5 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> r2_hidden X7 (k2_cat_1 X1 X2 X5) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> r2_funct_2 X3 (u1_struct_0 X1) (k2_cat_3 X1 X3 X4) (k2_cat_3 X1 X3 X6) -> False)
  -> (forall X5 X3 X4 X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r3_cat_3 X1 X3 X4 X2 -> False) -> (esk8_5 X1 X3 X4 X2 X5) = X5 -> (k1_cat_1 X1 (k7_partfun1 (u4_struct_0 X1) X2 (esk9_5 X1 X3 X4 X2 X5)) (esk8_5 X1 X3 X4 X2 X5)) = (k7_partfun1 (u4_struct_0 X1) (esk7_4 X1 X3 X4 X2) (esk9_5 X1 X3 X4 X2 X5)) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X2 -> m1_subset_1 X5 (u4_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m2_cat_3 X2 X1 X3 X4 -> v1_funct_2 X2 X4 (u4_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X4 (u4_struct_0 X1))) -> r2_hidden X5 (k2_cat_1 X1 X3 (esk6_4 X1 X3 X4 X2)) -> False)
  -> (forall X5 X3 X6 X2 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r2_hidden (esk4_6 X1 X2 X3 X4 X5 X6) (k2_cat_1 X1 X2 X5) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r3_cat_3 X1 X2 X3 X4 -> m2_cat_3 X6 X1 X5 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> r2_funct_2 X3 (u1_struct_0 X1) (k2_cat_3 X1 X3 X4) (k2_cat_3 X1 X3 X6) -> False)
  -> (forall X5 X3 X6 X2 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (esk4_6 X1 X2 X3 X4 X5 X6) (u4_struct_0 X1) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r3_cat_3 X1 X2 X3 X4 -> m2_cat_3 X6 X1 X5 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> r2_funct_2 X3 (u1_struct_0 X1) (k2_cat_3 X1 X3 X4) (k2_cat_3 X1 X3 X6) -> False)
  -> (forall X2 X5 X3 X4 X7 X1 X6 X8, ((k1_cat_1 X1 (k7_partfun1 (u4_struct_0 X1) X4 X8) X7) = (k7_partfun1 (u4_struct_0 X1) X6 X8) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (esk4_6 X1 X2 X3 X4 X5 X6) = X7 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> r2_hidden X8 X3 -> m1_subset_1 X7 (u4_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r3_cat_3 X1 X2 X3 X4 -> m2_cat_3 X6 X1 X5 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> r2_hidden X7 (k2_cat_1 X1 X2 X5) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> r2_funct_2 X3 (u1_struct_0 X1) (k2_cat_3 X1 X3 X4) (k2_cat_3 X1 X3 X6) -> False)
  -> (forall X1 X3 X2 X4 X5 X6, ((esk8_5 X3 X5 X2 X4 X6) = X6 -> False) -> ((k1_cat_1 X3 (k7_partfun1 (u4_struct_0 X3) X4 X1) (esk8_5 X3 X5 X2 X4 X6)) = (k7_partfun1 (u4_struct_0 X3) (esk7_4 X3 X5 X2 X4) X1) -> False) -> (v2_struct_0 X3 -> False) -> (v11_struct_0 X3 -> False) -> (r3_cat_3 X3 X5 X2 X4 -> False) -> v2_cat_1 X3 -> v3_cat_1 X3 -> v4_cat_1 X3 -> v5_cat_1 X3 -> v6_cat_1 X3 -> l1_cat_1 X3 -> v1_funct_1 X4 -> r2_hidden X1 X2 -> m1_subset_1 X6 (u4_struct_0 X3) -> m1_subset_1 X5 (u1_struct_0 X3) -> m2_cat_3 X4 X3 X5 X2 -> v1_funct_2 X4 X2 (u4_struct_0 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u4_struct_0 X3))) -> r2_hidden X6 (k2_cat_1 X3 X5 (esk6_4 X3 X5 X2 X4)) -> False)
  -> (forall X5 X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r3_cat_3 X1 X2 X3 X4 -> False) -> (r2_hidden (esk9_5 X1 X2 X3 X4 X5) X3 -> False) -> (esk8_5 X1 X2 X3 X4 X5) = X5 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> m1_subset_1 X5 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m2_cat_3 X4 X1 X2 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> r2_hidden X5 (k2_cat_1 X1 X2 (esk6_4 X1 X2 X3 X4)) -> False)
  -> (forall X5 X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r3_cat_3 X1 X2 X3 X4 -> False) -> (r2_hidden (esk8_5 X1 X2 X3 X4 X5) (k2_cat_1 X1 X2 (esk6_4 X1 X2 X3 X4)) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> m1_subset_1 X5 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m2_cat_3 X4 X1 X2 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> r2_hidden X5 (k2_cat_1 X1 X2 (esk6_4 X1 X2 X3 X4)) -> False)
  -> (forall X5 X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r3_cat_3 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk8_5 X1 X2 X3 X4 X5) (u4_struct_0 X1) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> m1_subset_1 X5 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m2_cat_3 X4 X1 X2 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> r2_hidden X5 (k2_cat_1 X1 X2 (esk6_4 X1 X2 X3 X4)) -> False)
  -> (forall X2 X3 X4 X1, (X2 = (k2_cat_3 X1 X3 X4) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (k7_partfun1 (u1_struct_0 X1) X2 (esk10_4 X1 X3 X4 X2)) = (k3_graph_1 X1 (k7_partfun1 (u4_struct_0 X1) X4 (esk10_4 X1 X3 X4 X2))) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> v1_funct_2 X2 X3 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u1_struct_0 X1))) -> False)
  -> (forall X4 X1 X3 X2, (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> (r3_cat_3 X2 X4 X1 X3 -> False) -> (r2_funct_2 X1 (u1_struct_0 X2) (k2_cat_3 X2 X1 X3) (k2_cat_3 X2 X1 (esk7_4 X2 X4 X1 X3)) -> False) -> v2_cat_1 X2 -> v3_cat_1 X2 -> v4_cat_1 X2 -> v5_cat_1 X2 -> v6_cat_1 X2 -> l1_cat_1 X2 -> v1_funct_1 X3 -> m1_subset_1 X4 (u1_struct_0 X2) -> m2_cat_3 X3 X2 X4 X1 -> v1_funct_2 X3 X1 (u4_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 (u4_struct_0 X2))) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r3_cat_3 X1 X2 X3 X4 -> False) -> (m2_cat_3 (esk7_4 X1 X2 X3 X4) X1 (esk6_4 X1 X2 X3 X4) X3 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> m1_subset_1 X2 (u1_struct_0 X1) -> m2_cat_3 X4 X1 X2 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r3_cat_3 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk6_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> m1_subset_1 X2 (u1_struct_0 X1) -> m2_cat_3 X4 X1 X2 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> False)
  -> (forall X3 X2 X4 X1, (X4 = (k2_cat_3 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X2 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X2 (u1_struct_0 X1) -> v1_funct_2 X3 X2 (u4_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u1_struct_0 X1))) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u4_struct_0 X1))) -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> (m2_cat_3 X1 X2 X3 X4 -> False) -> v2_cat_1 X2 -> v3_cat_1 X2 -> v4_cat_1 X2 -> v5_cat_1 X2 -> v6_cat_1 X2 -> l1_cat_1 X2 -> v1_funct_1 X1 -> m1_subset_1 X3 (u1_struct_0 X2) -> r3_cat_3 X2 X3 X4 X1 -> v1_funct_2 X1 X4 (u4_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 (u4_struct_0 X2))) -> False)
  -> (forall X3 X1 X2 X4 X5, ((k7_partfun1 (u1_struct_0 X2) X1 X5) = (k3_graph_1 X2 (k7_partfun1 (u4_struct_0 X2) X4 X5)) -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> X1 = (k2_cat_3 X2 X3 X4) -> v2_cat_1 X2 -> v3_cat_1 X2 -> v4_cat_1 X2 -> v5_cat_1 X2 -> v6_cat_1 X2 -> l1_cat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X1 -> r2_hidden X5 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X2) -> v1_funct_2 X1 X3 (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X2))) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u1_struct_0 X2))) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X1 X3 X2, (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> (m1_subset_1 (esk19_4 X1 X2 X3 X4) (u4_struct_0 X2) -> False) -> l1_cat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (a_3_0_cat_1 X2 X3 X4) -> False)
  -> (forall X4 X2 X3 X1, ((k4_graph_1 X1 (esk19_4 X2 X1 X3 X4)) = X4 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> r2_hidden X2 (a_3_0_cat_1 X1 X3 X4) -> False)
  -> (forall X4 X2 X3 X1, ((k3_graph_1 X1 (esk19_4 X2 X1 X3 X4)) = X3 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> r2_hidden X2 (a_3_0_cat_1 X1 X3 X4) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k10_funct_2 X1 X2 X3 X4) X2 -> False) -> v1_funct_1 X3 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X1 X3 X5 X2, ((k4_graph_1 X1 (k7_partfun1 (u4_struct_0 X1) X3 X5)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> r2_hidden X5 X4 -> m1_subset_1 X2 (u1_struct_0 X1) -> m2_cat_3 X3 X1 X2 X4 -> False)
  -> (forall X4 X2 X1 X3, (v2_struct_0 X3 -> False) -> (v11_struct_0 X3 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u4_struct_0 X3))) -> False) -> v2_cat_1 X3 -> v3_cat_1 X3 -> v4_cat_1 X3 -> v5_cat_1 X3 -> v6_cat_1 X3 -> l1_cat_1 X3 -> m1_subset_1 X4 (u1_struct_0 X3) -> m2_cat_3 X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X1 X3, (v2_struct_0 X3 -> False) -> (v11_struct_0 X3 -> False) -> (v1_funct_2 X1 X2 (u4_struct_0 X3) -> False) -> v2_cat_1 X3 -> v3_cat_1 X3 -> v4_cat_1 X3 -> v5_cat_1 X3 -> v6_cat_1 X3 -> l1_cat_1 X3 -> m1_subset_1 X4 (u1_struct_0 X3) -> m2_cat_3 X1 X3 X4 X2 -> False)
  -> (forall X4 X1 X3 X2, ((esk19_4 X1 X2 X3 X4) = X1 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> l1_cat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (a_3_0_cat_1 X2 X3 X4) -> False)
  -> (forall X4 X1 X3 X2, ((k10_funct_2 X1 X2 X3 X4) = (k7_partfun1 X2 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X3 X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m2_cat_3 (k1_cat_3 (u4_struct_0 X1) X4 X3) X1 X2 (k1_tarski X4) -> False) -> (k4_graph_1 X1 X3) = X2 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (k2_cat_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X2 (u1_struct_0 X1))) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 X2 (u4_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u4_struct_0 X1))) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 X4 (u4_struct_0 X1) -> False) -> l1_cat_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_cat_1 X4 X1 X2 X3 -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> (v1_funct_1 X1 -> False) -> v2_cat_1 X2 -> v3_cat_1 X2 -> v4_cat_1 X2 -> v5_cat_1 X2 -> v6_cat_1 X2 -> l1_cat_1 X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m2_cat_3 X1 X2 X3 X4 -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v1_funct_2 (k2_cat_3 X1 X2 X3) X2 (u1_struct_0 X1) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 X2 (u4_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u4_struct_0 X1))) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m2_cat_3 (esk18_3 X1 X2 X3) X1 X2 X3 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_cat_1 (esk16_3 X1 X2 X3) X1 X2 X3 -> False) -> l1_cat_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v1_funct_1 (k2_cat_3 X1 X2 X3) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 X2 (u4_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u4_struct_0 X1))) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_cat_1 (k4_cat_1 X1 X2) X1 X2 X2 -> False) -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X2 X1 X3, ((k4_graph_1 X1 X2) = X3 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> r2_hidden X2 (k2_cat_1 X1 X4 X3) -> False)
  -> (forall X4 X2 X1 X3, ((k3_graph_1 X1 X2) = X3 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> r2_hidden X2 (k2_cat_1 X1 X3 X4) -> False)
  -> (forall X1 X5 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> (r2_hidden X3 (a_3_0_cat_1 X2 X4 X5) -> False) -> X1 = X3 -> (k3_graph_1 X2 X1) = X4 -> (k4_graph_1 X2 X1) = X5 -> l1_cat_1 X2 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u4_struct_0 X2) -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r2_hidden X2 (k2_cat_1 X1 X3 X4) -> False) -> (k3_graph_1 X1 X2) = X3 -> (k4_graph_1 X1 X2) = X4 -> l1_cat_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_cat_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 (k1_tarski X2) X1)) -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> v5_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> v1_xboole_0 (k2_cat_1 X1 X2 X2) -> False)
  -> (forall X3 X2 X1, ((k1_cat_1 X1 (k4_cat_1 X1 X2) X3) = X3 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (k3_graph_1 X1 X3) = X2 -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (k2_cat_1 X1 X2 X3) (k1_zfmisc_1 (u4_struct_0 X1)) -> False) -> l1_cat_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, ((k7_partfun1 X1 (k8_funcop_1 X1 X4 X2) X3) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> r2_hidden X3 X4 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k8_funcop_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X2 X1)) -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k1_cat_1 X1 X2 X3) (u4_struct_0 X1) -> False) -> l1_cat_1 X1 -> m1_subset_1 X3 (u4_struct_0 X1) -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k1_cat_3 X1 X2 X3) (k1_tarski X2) X1 -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X2 X3 X1, ((k2_cat_1 X1 X2 X3) = (a_3_0_cat_1 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_cat_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k8_funcop_1 X1 X2 X3) X2 X1 -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_partfun1 X2 X1 X3) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k8_funcop_1 X1 X2 X3) -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k1_cat_3 X1 X2 X3) -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, ((k4_graph_1 X1 (k4_cat_1 X1 X2)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k3_graph_1 X1 (k4_cat_1 X1 X2)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk28_2 X3 X2) -> False)
  -> (forall X3 X2 X1, ((k1_cat_3 X1 X3 X2) = (k2_zfmisc_1 (k1_tarski X3) (k1_tarski X2)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X2 X1, ((k8_funcop_1 X1 X3 X2) = (k2_zfmisc_1 X3 (k1_tarski X2)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (k4_graph_1 X1 X2) (u1_struct_0 X1) -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (k3_graph_1 X1 X2) (u1_struct_0 X1) -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk11_2 X1 X2) = X1 -> r2_hidden (esk11_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_graph_1 X1 X2) (u1_struct_0 X1) -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_graph_1 X1 X2) (u1_struct_0 X1) -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, ((k4_graph_1 X1 X2) = (k2_graph_1 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, ((k3_graph_1 X1 X2) = (k1_graph_1 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk28_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk11_2 X1 X2) = X1 -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v15_struct_0 X1 -> False) -> l5_struct_0 X1 -> v1_zfmisc_1 (u4_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk23_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v11_struct_0 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (u4_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v6_cat_1 X1 -> False) -> l1_cat_1 X1 -> v15_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v5_cat_1 X1 -> False) -> l1_cat_1 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v4_cat_1 X1 -> False) -> l1_cat_1 X1 -> v15_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v3_cat_1 X1 -> False) -> l1_cat_1 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v11_struct_0 X1 -> False) -> v2_struct_0 X1 -> l5_struct_0 X1 -> v14_struct_0 X1 -> False)
  -> (forall X1, (v11_struct_0 X1 -> False) -> v2_struct_0 X1 -> l5_struct_0 X1 -> v14_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u4_struct_0 X1) -> False) -> l5_struct_0 X1 -> v15_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u4_struct_0 X1) -> False) -> v11_struct_0 X1 -> l5_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk22_1 X1) -> False) -> l1_struct_0 X1 -> False)
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
  -> (r3_cat_3 esk2_0 esk3_0 (k1_tarski esk1_0) (k1_cat_3 (u4_struct_0 esk2_0) esk1_0 (k4_cat_1 esk2_0 esk3_0)) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v15_struct_0 esk24_0 -> False)
  -> (v11_struct_0 esk25_0 -> False)
  -> (v11_struct_0 esk2_0 -> False)
  -> (v2_struct_0 esk25_0 -> False)
  -> (v2_struct_0 esk2_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_zfmisc_1 X1 (k1_tarski X2)) (k1_zfmisc_1 (k2_zfmisc_1 X1 (k1_tarski X2))) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 (k1_tarski X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk20_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk20_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk2_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((l1_graph_1 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l5_struct_0 esk24_0 -> False) -> False)
  -> ((l5_struct_0 esk15_0 -> False) -> False)
  -> ((l1_struct_0 esk14_0 -> False) -> False)
  -> ((l1_cat_1 esk25_0 -> False) -> False)
  -> ((l1_cat_1 esk12_0 -> False) -> False)
  -> ((l1_cat_1 esk2_0 -> False) -> False)
  -> ((v6_cat_1 esk2_0 -> False) -> False)
  -> ((v5_cat_1 esk2_0 -> False) -> False)
  -> ((v4_cat_1 esk2_0 -> False) -> False)
  -> ((v3_cat_1 esk2_0 -> False) -> False)
  -> ((v2_cat_1 esk2_0 -> False) -> False)
  -> False.
Admitted.
