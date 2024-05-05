(** $I sig/MizarPreamble.mgs **)

Theorem t6_cat_3:
 forall v1_xboole_0:set -> prop,
 forall k2_tarski:set -> set -> set,
 forall k5_funct_4:set -> set -> set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall k1_funct_4:set -> set -> set,
 forall k10_funct_2:set -> set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall v1_relat_1:set -> prop,
 forall k1_cat_3:set -> set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall k1_graph_1:set -> set -> set,
 forall esk19_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall k1_xboole_0:set,
 forall v15_struct_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall l5_struct_0:set -> prop,
 forall v14_struct_0:set -> prop,
 forall esk18_0:set,
 forall esk16_0:set,
 forall esk12_2:set -> set -> set,
 forall esk11_1:set -> set,
 forall esk8_0:set,
 forall esk10_0:set,
 forall esk7_0:set,
 forall esk9_0:set,
 forall esk13_0:set,
 forall esk17_0:set,
 forall esk3_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk14_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk15_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall l1_graph_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall k10_xtuple_0:set -> set,
 forall k1_funct_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall r2_funct_2:set -> set -> set -> set -> prop,
 forall esk20_4:set -> set -> set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall k7_partfun1:set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall k3_graph_1:set -> set -> set,
 forall u4_struct_0:set -> set,
 forall v3_cat_1:set -> prop,
 forall v5_cat_1:set -> prop,
 forall l1_cat_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall v6_cat_1:set -> prop,
 forall v4_cat_1:set -> prop,
 forall v2_cat_1:set -> prop,
 forall v11_struct_0:set -> prop,
 forall k2_cat_3:set -> set -> set -> set,
     (forall X2 X3 X4 X1, (X2 = (k2_cat_3 X1 X3 X4) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (k7_partfun1 (u1_struct_0 X1) X2 (esk6_4 X1 X3 X4 X2)) = (k3_graph_1 X1 (k7_partfun1 (u4_struct_0 X1) X4 (esk6_4 X1 X3 X4 X2))) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> v1_funct_2 X4 X3 (u4_struct_0 X1) -> v1_funct_2 X2 X3 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u1_struct_0 X1))) -> False)
  -> (forall X4 X5 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k5_funct_4 X1 X2 X3 X4 X5) (k1_zfmisc_1 (k2_zfmisc_1 (k2_tarski X2 X3) X1)) -> False) -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X5 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k5_funct_4 X1 X2 X3 X4 X5) (k2_tarski X2 X3) X1 -> False) -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X5 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k5_funct_4 X1 X2 X3 X4 X5) -> False) -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X3 X1 X2 X4 -> False) -> (k7_partfun1 X1 X2 (esk20_4 X3 X1 X2 X4)) = (k7_partfun1 X1 X4 (esk20_4 X3 X1 X2 X4)) -> v1_funct_1 X4 -> v1_funct_1 X2 -> v1_funct_2 X4 X3 X1 -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X4 X5 X2 X3 X1, ((k5_funct_4 X1 X4 X5 X2 X3) = (k1_funct_4 (k2_zfmisc_1 (k1_tarski X4) (k1_tarski X2)) (k2_zfmisc_1 (k1_tarski X5) (k1_tarski X3))) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> (r2_funct_2 X1 X2 X3 X4 -> False) -> (r2_hidden (esk20_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X4 X1, (X4 = (k2_cat_3 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (r2_hidden (esk6_4 X1 X2 X3 X4) X2 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X2 (u1_struct_0 X1) -> v1_funct_2 X3 X2 (u4_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u1_struct_0 X1))) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u4_struct_0 X1))) -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2 X4 X5, ((k7_partfun1 (u1_struct_0 X2) X1 X5) = (k3_graph_1 X2 (k7_partfun1 (u4_struct_0 X2) X4 X5)) -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X2 -> False) -> X1 = (k2_cat_3 X2 X3 X4) -> v2_cat_1 X2 -> v3_cat_1 X2 -> v4_cat_1 X2 -> v5_cat_1 X2 -> v6_cat_1 X2 -> l1_cat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X1 -> r2_hidden X5 X3 -> v1_funct_2 X4 X3 (u4_struct_0 X2) -> v1_funct_2 X1 X3 (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u4_struct_0 X2))) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 (u1_struct_0 X2))) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k10_funct_2 X1 X2 X3 X4) X2 -> False) -> v1_funct_1 X3 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X1 X3 X2, ((k10_funct_2 X1 X2 X3 X4) = (k7_partfun1 X2 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (k2_cat_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X2 (u1_struct_0 X1))) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 X2 (u4_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u4_struct_0 X1))) -> False)
  -> (forall X1 X4 X3 X2, ((k10_funct_2 X1 X2 X3 X4) = (k1_funct_1 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> r2_hidden X4 X1 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v1_funct_2 (k2_cat_3 X1 X2 X3) X2 (u1_struct_0 X1) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 X2 (u4_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u4_struct_0 X1))) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v1_funct_1 (k2_cat_3 X1 X2 X3) -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 X2 (u4_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 (u4_struct_0 X1))) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_cat_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 (k1_tarski X2) X1)) -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k1_cat_3 X1 X2 X3) (k1_tarski X2) X1 -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 (k9_xtuple_0 X3) -> False) -> (r2_hidden X1 (k9_xtuple_0 X2) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 (k1_funct_4 X2 X3)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_partfun1 X2 X1 X3) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k1_cat_3 X1 X2 X3) -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 (k9_xtuple_0 (k1_funct_4 X2 X3)) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 (k9_xtuple_0 (k1_funct_4 X3 X2)) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k1_funct_4 X2 X1) X3) = (k1_funct_1 X1 X3) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X3 X2 X1, ((k1_cat_3 X1 X3 X2) = (k2_zfmisc_1 (k1_tarski X3) (k1_tarski X2)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X1 X2, ((k1_funct_1 (k1_funct_4 X2 X1) X3) = (k1_funct_1 X2 X3) -> False) -> (r2_hidden X3 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (m1_subset_1 (k3_graph_1 X1 X2) (u1_struct_0 X1) -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_graph_1 X1 X2) (u1_struct_0 X1) -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X2 X1, ((k3_graph_1 X1 X2) = (k1_graph_1 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> l1_graph_1 X1 -> m1_subset_1 X2 (u4_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 (k2_zfmisc_1 X2 (k1_tarski X3)) X1) = X3 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k1_funct_4 X1 X1) = X1 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
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
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk15_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v11_struct_0 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (u4_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk14_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v6_cat_1 X1 -> False) -> l1_cat_1 X1 -> v15_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v5_cat_1 X1 -> False) -> l1_cat_1 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v4_cat_1 X1 -> False) -> l1_cat_1 X1 -> v15_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (v3_cat_1 X1 -> False) -> l1_cat_1 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v11_struct_0 X1 -> False) -> v2_struct_0 X1 -> l5_struct_0 X1 -> v14_struct_0 X1 -> False)
  -> (forall X1, (v11_struct_0 X1 -> False) -> v2_struct_0 X1 -> l5_struct_0 X1 -> v14_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u4_struct_0 X1) -> False) -> l5_struct_0 X1 -> v15_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u4_struct_0 X1) -> False) -> v11_struct_0 X1 -> l5_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk14_1 X1) -> False) -> l1_struct_0 X1 -> False)
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
  -> (r2_funct_2 (k2_tarski esk1_0 esk2_0) (u1_struct_0 esk3_0) (k2_cat_3 esk3_0 (k2_tarski esk1_0 esk2_0) (k5_funct_4 (u4_struct_0 esk3_0) esk1_0 esk2_0 esk4_0 esk5_0)) (k5_funct_4 (u1_struct_0 esk3_0) esk1_0 esk2_0 (k3_graph_1 esk3_0 esk4_0) (k3_graph_1 esk3_0 esk5_0)) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v15_struct_0 esk16_0 -> False)
  -> (v11_struct_0 esk17_0 -> False)
  -> (v11_struct_0 esk3_0 -> False)
  -> (v2_struct_0 esk17_0 -> False)
  -> (v2_struct_0 esk3_0 -> False)
  -> (forall X3 X4 X2 X1, (r1_tarski (k10_xtuple_0 (k1_funct_4 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X3)) (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X4)))) (k2_tarski X3 X4) -> False) -> False)
  -> (forall X1 X2 X4 X3, ((k9_xtuple_0 (k1_funct_4 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X3)) (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X4)))) = (k2_tarski X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_zfmisc_1 X1 (k1_tarski X2)) (k1_zfmisc_1 (k2_zfmisc_1 X1 (k1_tarski X2))) -> False) -> False)
  -> (forall X2 X1, (r1_tarski (k10_xtuple_0 (k2_zfmisc_1 X1 (k1_tarski X2))) (k1_tarski X2) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 (k1_tarski X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk12_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2, ((k9_xtuple_0 (k2_zfmisc_1 X1 (k1_tarski X2))) = X1 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk12_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u4_struct_0 esk3_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u4_struct_0 esk3_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((l1_graph_1 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l5_struct_0 esk16_0 -> False) -> False)
  -> ((l5_struct_0 esk10_0 -> False) -> False)
  -> ((l1_struct_0 esk9_0 -> False) -> False)
  -> ((l1_cat_1 esk17_0 -> False) -> False)
  -> ((l1_cat_1 esk7_0 -> False) -> False)
  -> ((l1_cat_1 esk3_0 -> False) -> False)
  -> ((v6_cat_1 esk3_0 -> False) -> False)
  -> ((v5_cat_1 esk3_0 -> False) -> False)
  -> ((v4_cat_1 esk3_0 -> False) -> False)
  -> ((v3_cat_1 esk3_0 -> False) -> False)
  -> ((v2_cat_1 esk3_0 -> False) -> False)
  -> False.
Admitted.
