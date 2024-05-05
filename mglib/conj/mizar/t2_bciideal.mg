(** $I sig/MizarPreamble.mgs **)

Theorem t2_bciideal:
 forall l2_bcialg_1:set -> prop,
 forall v3_bcialg_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall l1_bcialg_1:set -> prop,
 forall k5_binop_1:set -> set -> set -> set -> set,
 forall u1_bcialg_1:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall esk16_1:set -> set,
 forall v5_bcialg_2:set -> set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk19_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall esk14_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk17_0:set,
 forall esk13_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk12_0:set,
 forall esk11_0:set,
 forall esk10_0:set,
 forall esk9_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall k1_xboole_0:set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall l2_struct_0:set -> prop,
 forall esk15_1:set -> set,
 forall v9_struct_0:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk20_1:set -> set,
 forall v10_bcialg_1:set -> set -> prop,
 forall v1_bcialg_2:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall r1_bcialg_1:set -> set -> set -> prop,
 forall esk7_1:set -> set,
 forall esk8_1:set -> set,
 forall esk6_1:set -> set,
 forall v4_bcialg_1:set -> prop,
 forall v2_struct_0:set -> prop,
 forall epred1_1:set -> prop,
 forall v7_bcialg_1:set -> prop,
 forall v5_bcialg_1:set -> prop,
 forall esk23_1:set -> set,
 forall k1_bcialg_1:set -> set -> set -> set,
 forall esk22_1:set -> set,
 forall esk21_1:set -> set,
 forall k4_struct_0:set -> set,
     (forall X1, (k1_bcialg_1 X1 (k1_bcialg_1 X1 (esk21_1 X1) (k1_bcialg_1 X1 (esk21_1 X1) (esk22_1 X1))) (esk22_1 X1)) = (k4_struct_0 X1) -> (k1_bcialg_1 X1 (k1_bcialg_1 X1 (k1_bcialg_1 X1 (esk21_1 X1) (esk22_1 X1)) (k1_bcialg_1 X1 (esk21_1 X1) (esk23_1 X1))) (k1_bcialg_1 X1 (esk23_1 X1) (esk22_1 X1))) = (k4_struct_0 X1) -> v2_struct_0 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (l2_bcialg_1 X1 -> False) -> (k1_bcialg_1 X1 (k1_bcialg_1 X1 (esk21_1 X1) (k1_bcialg_1 X1 (esk21_1 X1) (esk22_1 X1))) (esk22_1 X1)) = (k4_struct_0 X1) -> (k1_bcialg_1 X1 (k1_bcialg_1 X1 (k1_bcialg_1 X1 (esk21_1 X1) (esk22_1 X1)) (k1_bcialg_1 X1 (esk21_1 X1) (esk23_1 X1))) (k1_bcialg_1 X1 (esk23_1 X1) (esk22_1 X1))) = (k4_struct_0 X1) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v4_bcialg_1 X1 -> False) -> (k1_bcialg_1 X1 (k1_bcialg_1 X1 (esk21_1 X1) (k1_bcialg_1 X1 (esk21_1 X1) (esk22_1 X1))) (esk22_1 X1)) = (k4_struct_0 X1) -> (k1_bcialg_1 X1 (k1_bcialg_1 X1 (k1_bcialg_1 X1 (esk21_1 X1) (esk22_1 X1)) (k1_bcialg_1 X1 (esk21_1 X1) (esk23_1 X1))) (k1_bcialg_1 X1 (esk23_1 X1) (esk22_1 X1))) = (k4_struct_0 X1) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v3_bcialg_1 X1 -> False) -> (k1_bcialg_1 X1 (k1_bcialg_1 X1 (esk21_1 X1) (k1_bcialg_1 X1 (esk21_1 X1) (esk22_1 X1))) (esk22_1 X1)) = (k4_struct_0 X1) -> (k1_bcialg_1 X1 (k1_bcialg_1 X1 (k1_bcialg_1 X1 (esk21_1 X1) (esk22_1 X1)) (k1_bcialg_1 X1 (esk21_1 X1) (esk23_1 X1))) (k1_bcialg_1 X1 (esk23_1 X1) (esk22_1 X1))) = (k4_struct_0 X1) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_bcialg_1 X1 -> False) -> (k1_bcialg_1 X1 (k1_bcialg_1 X1 (k1_bcialg_1 X1 (esk6_1 X1) (esk7_1 X1)) (k1_bcialg_1 X1 (esk8_1 X1) (esk7_1 X1))) (k1_bcialg_1 X1 (esk6_1 X1) (esk8_1 X1))) = (k4_struct_0 X1) -> l2_bcialg_1 X1 -> False)
  -> (forall X4 X3 X2 X1, ((k1_bcialg_1 X1 (k1_bcialg_1 X1 (k1_bcialg_1 X1 X2 X3) (k1_bcialg_1 X1 X2 X4)) (k1_bcialg_1 X1 X4 X3)) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> epred1_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, ((k1_bcialg_1 X1 (k1_bcialg_1 X1 (k1_bcialg_1 X1 X2 X3) (k1_bcialg_1 X1 X4 X3)) (k1_bcialg_1 X1 X2 X4)) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X2 X3 X1, ((k1_bcialg_1 X1 (k1_bcialg_1 X1 X2 (k1_bcialg_1 X1 X2 X3)) X3) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> epred1_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_bcialg_1 X1 (k1_bcialg_1 X1 X2 X3) (k1_bcialg_1 X1 X2 X4) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> r1_bcialg_1 X1 X4 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (v2_struct_0 X1 -> False) -> (r1_bcialg_1 X1 (k1_bcialg_1 X1 X2 X3) (k1_bcialg_1 X1 X4 X3) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> r1_bcialg_1 X1 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, ((k1_bcialg_1 X1 (k1_bcialg_1 X1 X2 X3) X4) = (k1_bcialg_1 X1 (k1_bcialg_1 X1 X2 X4) X3) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k5_binop_1 (u1_struct_0 X1) (u1_bcialg_1 X1) X2 X3) = (k1_bcialg_1 X1 X2 X3) -> False) -> l1_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (m1_subset_1 (u1_bcialg_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1))) -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_bcialg_1 X1 X2 X3 -> False) -> (k1_bcialg_1 X1 X2 X3) = (k4_struct_0 X1) -> l2_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k1_bcialg_1 X1 X2 X3) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> l2_bcialg_1 X1 -> r1_bcialg_1 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k1_bcialg_1 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k1_bcialg_1 X1 X2 (k4_struct_0 X1)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_funct_2 (u1_bcialg_1 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (u1_struct_0 X1) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_bcialg_2 (k4_struct_0 X1) X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_bcialg_2 (esk16_1 X1) X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_bcialg_2 (k4_struct_0 X1) X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v10_bcialg_1 (k4_struct_0 X1) X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (l2_bcialg_1 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (u1_struct_0 X1) -> False) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (l2_bcialg_1 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (u1_struct_0 X1) -> False) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (l2_bcialg_1 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (u1_struct_0 X1) -> False) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v4_bcialg_1 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (u1_struct_0 X1) -> False) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v4_bcialg_1 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (u1_struct_0 X1) -> False) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v4_bcialg_1 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (u1_struct_0 X1) -> False) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v3_bcialg_1 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (u1_struct_0 X1) -> False) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v3_bcialg_1 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (u1_struct_0 X1) -> False) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v3_bcialg_1 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (u1_struct_0 X1) -> False) -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> epred1_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l2_struct_0 X1 -> v9_struct_0 (esk15_1 X1) X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_bcialg_1 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_bcialg_1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_bcialg_1 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (u1_struct_0 X1) -> False) -> l2_struct_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) (u1_struct_0 X1) -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k4_struct_0 X1) (u1_struct_0 X1) -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk19_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v9_struct_0 (esk14_1 X1) X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (v9_struct_0 (k4_struct_0 X1) X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk18_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_funct_1 (u1_bcialg_1 X1) -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (epred1_1 X1 -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (l2_struct_0 X1 -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (l1_bcialg_1 X1 -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_bcialg_1 esk1_0 (k1_bcialg_1 esk1_0 (k1_bcialg_1 esk1_0 esk2_0 (k1_bcialg_1 esk1_0 esk3_0 esk4_0)) (k1_bcialg_1 esk1_0 esk2_0 (k1_bcialg_1 esk1_0 esk3_0 esk5_0))) (k1_bcialg_1 esk1_0 esk4_0 esk5_0) -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk17_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((l2_struct_0 esk17_0 -> False) -> False)
  -> ((l2_struct_0 esk12_0 -> False) -> False)
  -> ((l1_bcialg_1 esk9_0 -> False) -> False)
  -> ((v7_struct_0 esk17_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((l2_bcialg_1 esk11_0 -> False) -> False)
  -> ((l2_bcialg_1 esk1_0 -> False) -> False)
  -> ((v7_bcialg_1 esk1_0 -> False) -> False)
  -> ((v5_bcialg_1 esk1_0 -> False) -> False)
  -> ((v4_bcialg_1 esk1_0 -> False) -> False)
  -> ((v3_bcialg_1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
