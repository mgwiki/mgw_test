(** $I sig/MizarPreamble.mgs **)

Theorem t39_isocat_1:
 forall k4_isocat_1:set -> set -> set -> set -> set -> set -> set -> set,
 forall k5_isocat_1:set -> set -> set -> set -> set -> set -> set -> set,
 forall k7_nattra_1:set -> set -> set -> set -> set -> set -> set -> set,
 forall epred2_1:set -> prop,
 forall epred5_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall esk18_4:set -> set -> set -> set -> set,
 forall k3_relat_1:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk20_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk25_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk24_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall k1_xboole_0:set,
 forall v15_struct_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall l5_struct_0:set -> prop,
 forall v14_struct_0:set -> prop,
 forall esk27_0:set,
 forall esk23_2:set -> set -> set,
 forall esk19_1:set -> set,
 forall esk15_0:set,
 forall esk16_0:set,
 forall esk14_0:set,
 forall esk17_0:set,
 forall o_0_0_xboole_0:set,
 forall esk22_2:set -> set -> set,
 forall esk26_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk5_0:set,
 forall esk3_0:set,
 forall esk9_0:set,
 forall esk7_0:set,
 forall esk11_0:set,
 forall esk13_0:set,
 forall esk12_0:set,
 forall esk8_0:set,
 forall esk10_0:set,
 forall esk6_0:set,
 forall esk1_0:set,
 forall l1_graph_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk28_1:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall esk21_4:set -> set -> set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall m1_nattra_1:set -> set -> set -> set -> set -> prop,
 forall epred3_1:set -> prop,
 forall epred4_1:set -> prop,
 forall epred1_1:set -> prop,
 forall r2_nattra_1:set -> set -> set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall u4_struct_0:set -> set,
 forall r2_funct_2:set -> set -> set -> set -> prop,
 forall v11_struct_0:set -> prop,
 forall v2_cat_1:set -> prop,
 forall v4_cat_1:set -> prop,
 forall v6_cat_1:set -> prop,
 forall m2_cat_1:set -> set -> set -> prop,
 forall l1_cat_1:set -> prop,
 forall v5_cat_1:set -> prop,
 forall v3_cat_1:set -> prop,
 forall k9_cat_1:set -> set -> set -> set -> set -> set,
 forall k6_isocat_1:set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall m2_nattra_1:set -> set -> set -> set -> set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X2 X6 X4 X9 X8 X5 X7 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (m2_nattra_1 (k6_isocat_1 X1 X2 X3 X4 X5 X6 X7 X8 X9) X1 X3 (k9_cat_1 X1 X2 X3 X4 X6) (k9_cat_1 X1 X2 X3 X5 X7) -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X3 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X3 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X7 X2 X3 -> m2_cat_1 X6 X2 X3 -> m2_cat_1 X5 X1 X2 -> m2_cat_1 X4 X1 X2 -> m2_nattra_1 X9 X2 X3 X6 X7 -> m2_nattra_1 X8 X1 X2 X4 X5 -> False)
  -> (forall X2 X6 X4 X9 X8 X5 X7 X1 X3, ((k7_nattra_1 X1 X3 (k9_cat_1 X1 X2 X3 X4 X6) (k9_cat_1 X1 X2 X3 X5 X6) (k9_cat_1 X1 X2 X3 X5 X7) (k4_isocat_1 X1 X2 X3 X4 X5 X8 X6) (k5_isocat_1 X1 X2 X3 X6 X7 X5 X9)) = (k6_isocat_1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X3 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X3 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X7 X2 X3 -> m2_cat_1 X6 X2 X3 -> m2_cat_1 X5 X1 X2 -> m2_cat_1 X4 X1 X2 -> m2_nattra_1 X9 X2 X3 X6 X7 -> m2_nattra_1 X8 X1 X2 X4 X5 -> False)
  -> (forall X2 X7 X5 X8 X9 X4 X6 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (r2_funct_2 (u1_struct_0 X2) (u4_struct_0 X1) (k4_isocat_1 X2 X3 X1 X4 X6 (k7_nattra_1 X2 X3 X4 X5 X6 X8 X9) X7) (k7_nattra_1 X2 X1 (k9_cat_1 X2 X3 X1 X4 X7) (k9_cat_1 X2 X3 X1 X5 X7) (k9_cat_1 X2 X3 X1 X6 X7) (k4_isocat_1 X2 X3 X1 X4 X5 X8 X7) (k4_isocat_1 X2 X3 X1 X5 X6 X9 X7)) -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X3 -> l1_cat_1 X2 -> epred1_1 X1 -> m2_cat_1 X7 X3 X1 -> m2_cat_1 X6 X2 X3 -> m2_cat_1 X5 X2 X3 -> m2_cat_1 X4 X2 X3 -> r2_nattra_1 X2 X3 X5 X6 -> r2_nattra_1 X2 X3 X4 X5 -> m2_nattra_1 X9 X2 X3 X5 X6 -> m2_nattra_1 X8 X2 X3 X4 X5 -> False)
  -> (forall X2 X7 X5 X8 X9 X4 X6 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (r2_funct_2 (u1_struct_0 X1) (u4_struct_0 X3) (k5_isocat_1 X1 X2 X3 X5 X7 X4 (k7_nattra_1 X2 X3 X5 X6 X7 X8 X9)) (k7_nattra_1 X1 X3 (k9_cat_1 X1 X2 X3 X4 X5) (k9_cat_1 X1 X2 X3 X4 X6) (k9_cat_1 X1 X2 X3 X4 X7) (k5_isocat_1 X1 X2 X3 X5 X6 X4 X8) (k5_isocat_1 X1 X2 X3 X6 X7 X4 X9)) -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X3 -> l1_cat_1 X2 -> epred2_1 X1 -> m2_cat_1 X7 X2 X3 -> m2_cat_1 X6 X2 X3 -> m2_cat_1 X5 X2 X3 -> m2_cat_1 X4 X1 X2 -> r2_nattra_1 X2 X3 X6 X7 -> r2_nattra_1 X2 X3 X5 X6 -> m2_nattra_1 X9 X2 X3 X6 X7 -> m2_nattra_1 X8 X2 X3 X5 X6 -> False)
  -> (forall X3 X8 X6 X9 X5 X7 X1 X2 X4, (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X4 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (r2_funct_2 (u1_struct_0 X1) (u4_struct_0 X2) (k5_isocat_1 X1 X3 X2 (k9_cat_1 X3 X4 X2 X6 X8) (k9_cat_1 X3 X4 X2 X7 X8) X5 (k4_isocat_1 X3 X4 X2 X6 X7 X9 X8)) (k4_isocat_1 X1 X4 X2 (k9_cat_1 X1 X3 X4 X5 X6) (k9_cat_1 X1 X3 X4 X5 X7) (k5_isocat_1 X1 X3 X4 X6 X7 X5 X9) X8) -> False) -> v2_cat_1 X4 -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X4 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X4 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X4 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X4 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X4 -> l1_cat_1 X3 -> l1_cat_1 X2 -> epred4_1 X1 -> m2_cat_1 X8 X4 X2 -> m2_cat_1 X7 X3 X4 -> m2_cat_1 X6 X3 X4 -> m2_cat_1 X5 X1 X3 -> r2_nattra_1 X3 X4 X6 X7 -> m2_nattra_1 X9 X3 X4 X6 X7 -> False)
  -> (forall X1 X5 X3 X9 X8 X7 X4 X6 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (r2_funct_2 (u1_struct_0 X1) (u4_struct_0 X2) (k7_nattra_1 X1 X2 X3 X4 X6 X7 (k7_nattra_1 X1 X2 X4 X5 X6 X8 X9)) (k7_nattra_1 X1 X2 X3 X5 X6 (k7_nattra_1 X1 X2 X3 X4 X5 X7 X8) X9) -> False) -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X6 X1 X2 -> m2_cat_1 X5 X1 X2 -> m2_cat_1 X4 X1 X2 -> m2_cat_1 X3 X1 X2 -> r2_nattra_1 X1 X2 X5 X6 -> r2_nattra_1 X1 X2 X4 X5 -> r2_nattra_1 X1 X2 X3 X4 -> m2_nattra_1 X9 X1 X2 X5 X6 -> m2_nattra_1 X8 X1 X2 X4 X5 -> m2_nattra_1 X7 X1 X2 X3 X4 -> False)
  -> (forall X3 X8 X6 X9 X5 X7 X1 X2 X4, (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X4 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (r2_funct_2 (u1_struct_0 X1) (u4_struct_0 X4) (k5_isocat_1 X1 X2 X4 (k9_cat_1 X2 X3 X4 X6 X7) (k9_cat_1 X2 X3 X4 X6 X8) X5 (k5_isocat_1 X2 X3 X4 X7 X8 X6 X9)) (k5_isocat_1 X1 X3 X4 X7 X8 (k9_cat_1 X1 X2 X3 X5 X6) X9) -> False) -> v2_cat_1 X4 -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X4 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X4 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X4 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X4 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X4 -> l1_cat_1 X3 -> l1_cat_1 X2 -> epred3_1 X1 -> m2_cat_1 X8 X3 X4 -> m2_cat_1 X7 X3 X4 -> m2_cat_1 X6 X2 X3 -> m2_cat_1 X5 X1 X2 -> r2_nattra_1 X3 X4 X7 X8 -> m2_nattra_1 X9 X3 X4 X7 X8 -> False)
  -> (forall X3 X8 X6 X9 X5 X7 X1 X2 X4, (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X4 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (r2_funct_2 (u1_struct_0 X3) (u4_struct_0 X2) (k4_isocat_1 X3 X4 X2 X5 X6 X9 (k9_cat_1 X4 X1 X2 X7 X8)) (k4_isocat_1 X3 X1 X2 (k9_cat_1 X3 X4 X1 X5 X7) (k9_cat_1 X3 X4 X1 X6 X7) (k4_isocat_1 X3 X4 X1 X5 X6 X9 X7) X8) -> False) -> v2_cat_1 X4 -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X4 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X4 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X4 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X4 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X4 -> l1_cat_1 X3 -> l1_cat_1 X2 -> epred5_1 X1 -> m2_cat_1 X8 X1 X2 -> m2_cat_1 X7 X4 X1 -> m2_cat_1 X6 X3 X4 -> m2_cat_1 X5 X3 X4 -> r2_nattra_1 X3 X4 X5 X6 -> m2_nattra_1 X9 X3 X4 X5 X6 -> False)
  -> (forall X2 X5 X7 X4 X6 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (m2_nattra_1 (k5_isocat_1 X1 X2 X3 X4 X5 X6 X7) X1 X3 (k9_cat_1 X1 X2 X3 X6 X4) (k9_cat_1 X1 X2 X3 X6 X5) -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X3 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X3 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X6 X1 X2 -> m2_cat_1 X5 X2 X3 -> m2_cat_1 X4 X2 X3 -> m2_nattra_1 X7 X2 X3 X4 X5 -> False)
  -> (forall X2 X5 X6 X4 X7 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (m2_nattra_1 (k4_isocat_1 X1 X2 X3 X4 X5 X6 X7) X1 X3 (k9_cat_1 X1 X2 X3 X4 X7) (k9_cat_1 X1 X2 X3 X5 X7) -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X3 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X3 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X7 X2 X3 -> m2_cat_1 X5 X1 X2 -> m2_cat_1 X4 X1 X2 -> m2_nattra_1 X6 X1 X2 X4 X5 -> False)
  -> (forall X1 X4 X6 X7 X3 X5 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (m2_nattra_1 (k7_nattra_1 X1 X2 X3 X4 X5 X6 X7) X1 X2 X3 X5 -> False) -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X5 X1 X2 -> m2_cat_1 X4 X1 X2 -> m2_cat_1 X3 X1 X2 -> m2_nattra_1 X7 X1 X2 X4 X5 -> m2_nattra_1 X6 X1 X2 X3 X4 -> False)
  -> (forall X2 X6 X4 X5 X7 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (r2_nattra_1 X1 X3 (k9_cat_1 X1 X2 X3 X4 X6) (k9_cat_1 X1 X2 X3 X5 X7) -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X3 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X3 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X7 X2 X3 -> m2_cat_1 X6 X2 X3 -> m2_cat_1 X5 X1 X2 -> m2_cat_1 X4 X1 X2 -> r2_nattra_1 X2 X3 X6 X7 -> r2_nattra_1 X1 X2 X4 X5 -> False)
  -> (forall X1 X3 X5 X4 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (m1_nattra_1 X5 X1 X2 X3 X4 -> False) -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X4 X1 X2 -> m2_cat_1 X3 X1 X2 -> m2_nattra_1 X5 X1 X2 X3 X4 -> False)
  -> (forall X2 X5 X4 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (m2_cat_1 (k9_cat_1 X1 X2 X3 X4 X5) X1 X3 -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X3 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X3 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X5 X2 X3 -> m2_cat_1 X4 X1 X2 -> False)
  -> (forall X2 X5 X4 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u4_struct_0 X3))) -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X3 -> l1_cat_1 X2 -> m2_cat_1 X5 X2 X3 -> m2_cat_1 X4 X2 X3 -> m1_nattra_1 X1 X2 X3 X4 X5 -> False)
  -> (forall X2 X5 X4 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v1_funct_2 X1 (u1_struct_0 X2) (u4_struct_0 X3) -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X3 -> l1_cat_1 X2 -> m2_cat_1 X5 X2 X3 -> m2_cat_1 X4 X2 X3 -> m1_nattra_1 X1 X2 X3 X4 X5 -> False)
  -> (forall X2 X5 X4 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v1_funct_1 X1 -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X3 -> l1_cat_1 X2 -> m2_cat_1 X5 X2 X3 -> m2_cat_1 X4 X2 X3 -> m1_nattra_1 X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (m1_nattra_1 (esk18_4 X1 X2 X3 X4) X1 X2 X3 X4 -> False) -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X4 X1 X2 -> m2_cat_1 X3 X1 X2 -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (m2_nattra_1 (esk21_4 X1 X2 X3 X4) X1 X2 X3 X4 -> False) -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X4 X1 X2 -> m2_cat_1 X3 X1 X2 -> False)
  -> (forall X2 X5 X4 X1 X3, ((k9_cat_1 X1 X2 X3 X4 X5) = (k3_relat_1 X4 X5) -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X3 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X3 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X5 X2 X3 -> m2_cat_1 X4 X1 X2 -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (r2_nattra_1 X1 X2 X3 X3 -> False) -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X2 -> l1_cat_1 X1 -> m2_cat_1 X4 X1 X2 -> m2_cat_1 X3 X1 X2 -> False)
  -> (forall X4 X3 X1 X2 X5, (v1_xboole_0 X5 -> False) -> (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X5 X4 -> v1_funct_2 X1 X3 X5 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X5 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> False)
  -> (forall X1 X4 X3 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X4 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X1 X2 X4 X5 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X5 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (u4_struct_0 X2) (u4_struct_0 X3))) -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X3 -> l1_cat_1 X2 -> m2_cat_1 X1 X2 X3 -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v1_funct_2 X1 (u4_struct_0 X2) (u4_struct_0 X3) -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X3 -> l1_cat_1 X2 -> m2_cat_1 X1 X2 X3 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v11_struct_0 X3 -> False) -> (v11_struct_0 X2 -> False) -> (v1_funct_1 X1 -> False) -> v2_cat_1 X3 -> v2_cat_1 X2 -> v3_cat_1 X3 -> v3_cat_1 X2 -> v4_cat_1 X3 -> v4_cat_1 X2 -> v5_cat_1 X3 -> v5_cat_1 X2 -> v6_cat_1 X3 -> v6_cat_1 X2 -> l1_cat_1 X3 -> l1_cat_1 X2 -> m2_cat_1 X1 X2 X3 -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v11_struct_0 X2 -> False) -> (v11_struct_0 X1 -> False) -> (m2_cat_1 (esk20_2 X1 X2) X1 X2 -> False) -> v2_cat_1 X2 -> v2_cat_1 X1 -> v3_cat_1 X2 -> v3_cat_1 X1 -> v4_cat_1 X2 -> v4_cat_1 X1 -> v5_cat_1 X2 -> v5_cat_1 X1 -> v6_cat_1 X2 -> v6_cat_1 X1 -> l1_cat_1 X2 -> l1_cat_1 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, ((k3_relat_1 (k3_relat_1 X1 X2) X3) = (k3_relat_1 X1 (k3_relat_1 X2 X3)) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (epred5_1 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (epred4_1 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (epred3_1 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (epred2_1 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v11_struct_0 X1 -> False) -> (epred1_1 X1 -> False) -> v2_cat_1 X1 -> v3_cat_1 X1 -> v4_cat_1 X1 -> v5_cat_1 X1 -> v6_cat_1 X1 -> l1_cat_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
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
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk25_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v11_struct_0 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (u4_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk28_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk24_1 X1) -> False)
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
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk24_1 X1) -> False) -> l1_struct_0 X1 -> False)
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
  -> (r2_funct_2 (u1_struct_0 esk1_0) (u4_struct_0 esk4_0) (k6_isocat_1 esk1_0 esk3_0 esk4_0 (k9_cat_1 esk1_0 esk2_0 esk3_0 esk5_0 esk7_0) (k9_cat_1 esk1_0 esk2_0 esk3_0 esk6_0 esk8_0) esk9_0 esk10_0 (k6_isocat_1 esk1_0 esk2_0 esk3_0 esk5_0 esk6_0 esk7_0 esk8_0 esk11_0 esk12_0) esk13_0) (k6_isocat_1 esk1_0 esk2_0 esk4_0 esk5_0 esk6_0 (k9_cat_1 esk2_0 esk3_0 esk4_0 esk7_0 esk9_0) (k9_cat_1 esk2_0 esk3_0 esk4_0 esk8_0 esk10_0) esk11_0 (k6_isocat_1 esk2_0 esk3_0 esk4_0 esk7_0 esk8_0 esk9_0 esk10_0 esk12_0 esk13_0)) -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v15_struct_0 esk26_0 -> False)
  -> (v11_struct_0 esk27_0 -> False)
  -> (v11_struct_0 esk4_0 -> False)
  -> (v11_struct_0 esk3_0 -> False)
  -> (v11_struct_0 esk2_0 -> False)
  -> (v11_struct_0 esk1_0 -> False)
  -> (v2_struct_0 esk27_0 -> False)
  -> (v2_struct_0 esk4_0 -> False)
  -> (v2_struct_0 esk3_0 -> False)
  -> (v2_struct_0 esk2_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> ((m2_nattra_1 esk13_0 esk3_0 esk4_0 esk9_0 esk10_0 -> False) -> False)
  -> ((m2_nattra_1 esk12_0 esk2_0 esk3_0 esk7_0 esk8_0 -> False) -> False)
  -> ((m2_nattra_1 esk11_0 esk1_0 esk2_0 esk5_0 esk6_0 -> False) -> False)
  -> ((r2_nattra_1 esk3_0 esk4_0 esk9_0 esk10_0 -> False) -> False)
  -> ((r2_nattra_1 esk2_0 esk3_0 esk7_0 esk8_0 -> False) -> False)
  -> ((r2_nattra_1 esk1_0 esk2_0 esk5_0 esk6_0 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk23_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk22_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk22_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m2_cat_1 esk10_0 esk3_0 esk4_0 -> False) -> False)
  -> ((m2_cat_1 esk9_0 esk3_0 esk4_0 -> False) -> False)
  -> ((m2_cat_1 esk8_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m2_cat_1 esk7_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m2_cat_1 esk6_0 esk1_0 esk2_0 -> False) -> False)
  -> ((m2_cat_1 esk5_0 esk1_0 esk2_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk23_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk22_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk23_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk22_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((l1_graph_1 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((l5_struct_0 esk26_0 -> False) -> False)
  -> ((l5_struct_0 esk17_0 -> False) -> False)
  -> ((l1_struct_0 esk16_0 -> False) -> False)
  -> ((l1_cat_1 esk27_0 -> False) -> False)
  -> ((l1_cat_1 esk14_0 -> False) -> False)
  -> ((l1_cat_1 esk4_0 -> False) -> False)
  -> ((l1_cat_1 esk3_0 -> False) -> False)
  -> ((l1_cat_1 esk2_0 -> False) -> False)
  -> ((l1_cat_1 esk1_0 -> False) -> False)
  -> ((v6_cat_1 esk4_0 -> False) -> False)
  -> ((v6_cat_1 esk3_0 -> False) -> False)
  -> ((v6_cat_1 esk2_0 -> False) -> False)
  -> ((v6_cat_1 esk1_0 -> False) -> False)
  -> ((v5_cat_1 esk4_0 -> False) -> False)
  -> ((v5_cat_1 esk3_0 -> False) -> False)
  -> ((v5_cat_1 esk2_0 -> False) -> False)
  -> ((v5_cat_1 esk1_0 -> False) -> False)
  -> ((v4_cat_1 esk4_0 -> False) -> False)
  -> ((v4_cat_1 esk3_0 -> False) -> False)
  -> ((v4_cat_1 esk2_0 -> False) -> False)
  -> ((v4_cat_1 esk1_0 -> False) -> False)
  -> ((v3_cat_1 esk4_0 -> False) -> False)
  -> ((v3_cat_1 esk3_0 -> False) -> False)
  -> ((v3_cat_1 esk2_0 -> False) -> False)
  -> ((v3_cat_1 esk1_0 -> False) -> False)
  -> ((v2_cat_1 esk4_0 -> False) -> False)
  -> ((v2_cat_1 esk3_0 -> False) -> False)
  -> ((v2_cat_1 esk2_0 -> False) -> False)
  -> ((v2_cat_1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
