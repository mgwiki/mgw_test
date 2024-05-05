(** $I sig/MizarPreamble.mgs **)

Theorem t18_bcialg_3:
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall l1_bcialg_1:set -> prop,
 forall k5_binop_1:set -> set -> set -> set -> set,
 forall u1_bcialg_1:set -> set,
 forall a_2_0_bcialg_1:set -> set -> set,
 forall r1_bcialg_1:set -> set -> set -> prop,
 forall esk17_3:set -> set -> set -> set,
 forall esk5_1:set -> set,
 forall esk6_1:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k2_bcialg_1:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk7_1:set -> set,
 forall esk15_2:set -> set -> set,
 forall v10_bcialg_1:set -> set -> prop,
 forall a_1_1_bcialg_1:set -> set,
 forall esk8_1:set -> set,
 forall esk9_1:set -> set,
 forall esk2_0:set,
 forall v7_struct_0:set -> prop,
 forall esk22_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk21_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v9_struct_0:set -> set -> prop,
 forall esk19_1:set -> set,
 forall l2_struct_0:set -> prop,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall k1_xboole_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall esk20_0:set,
 forall esk14_1:set -> set,
 forall esk10_0:set,
 forall esk11_0:set,
 forall esk12_0:set,
 forall esk13_0:set,
 forall v1_funct_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall esk23_1:set -> set,
 forall esk26_2:set -> set -> set,
 forall esk16_2:set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k7_bcialg_1:set -> set -> set,
 forall k6_bcialg_1:set -> set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k5_bcialg_1:set -> set,
 forall v4_bcialg_3:set -> prop,
 forall v3_bcialg_1:set -> prop,
 forall v5_bcialg_1:set -> prop,
 forall v7_bcialg_1:set -> prop,
 forall l2_bcialg_1:set -> prop,
 forall v4_bcialg_1:set -> prop,
 forall k4_struct_0:set -> set,
 forall esk25_1:set -> set,
 forall esk24_1:set -> set,
 forall k1_bcialg_1:set -> set -> set -> set,
 forall v2_struct_0:set -> prop,
     (forall X1, (v2_struct_0 X1 -> False) -> (v4_bcialg_3 X1 -> False) -> (k1_bcialg_1 X1 (k1_bcialg_1 X1 (esk24_1 X1) (k1_bcialg_1 X1 (esk24_1 X1) (esk25_1 X1))) (k1_bcialg_1 X1 (esk25_1 X1) (k1_bcialg_1 X1 (esk25_1 X1) (esk24_1 X1)))) = (k1_bcialg_1 X1 (k4_struct_0 X1) (k1_bcialg_1 X1 (esk24_1 X1) (esk25_1 X1))) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X2 X3 X1, ((k1_bcialg_1 X1 (k1_bcialg_1 X1 X2 (k1_bcialg_1 X1 X2 X3)) (k1_bcialg_1 X1 X3 (k1_bcialg_1 X1 X3 X2))) = (k1_bcialg_1 X1 (k4_struct_0 X1) (k1_bcialg_1 X1 X2 X3)) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> v4_bcialg_3 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X5 X4 X3 X1, (v2_struct_0 X1 -> False) -> (r2_hidden (k1_bcialg_1 X1 X4 X5) (k7_bcialg_1 X1 (k6_bcialg_1 X1 X2 X3)) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m2_subset_1 X3 (u1_struct_0 X1) (k5_bcialg_1 X1) -> m2_subset_1 X2 (u1_struct_0 X1) (k5_bcialg_1 X1) -> m2_subset_1 X5 (u1_struct_0 X1) (k7_bcialg_1 X1 X3) -> m2_subset_1 X4 (u1_struct_0 X1) (k7_bcialg_1 X1 X2) -> False)
  -> (forall X1 X2 X3, ((k1_bcialg_1 esk1_0 X2 (k1_bcialg_1 esk1_0 X2 X3)) = (k1_bcialg_1 esk1_0 X3 (k1_bcialg_1 esk1_0 X3 X2)) -> False) -> (v4_bcialg_3 esk1_0 -> False) -> m2_subset_1 X1 (u1_struct_0 esk1_0) (k5_bcialg_1 esk1_0) -> m2_subset_1 X3 (u1_struct_0 esk1_0) (k7_bcialg_1 esk1_0 X1) -> m2_subset_1 X2 (u1_struct_0 esk1_0) (k7_bcialg_1 esk1_0 X1) -> False)
  -> (forall X3 X2 X1, ((k1_bcialg_1 X1 X2 (k1_bcialg_1 X1 X2 (k1_bcialg_1 X1 X2 X3))) = (k1_bcialg_1 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> ((k1_bcialg_1 esk1_0 esk4_0 (k1_bcialg_1 esk1_0 esk4_0 esk3_0)) = (k1_bcialg_1 esk1_0 esk3_0 (k1_bcialg_1 esk1_0 esk3_0 esk4_0)) -> v4_bcialg_3 esk1_0 -> False)
  -> (forall X2 X3 X4 X1, ((k1_bcialg_1 X1 (k1_bcialg_1 X1 X2 X3) X4) = (k1_bcialg_1 X1 (k1_bcialg_1 X1 X2 X4) X3) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k5_binop_1 (u1_struct_0 X1) (u1_bcialg_1 X1) X2 X3) = (k1_bcialg_1 X1 X2 X3) -> False) -> l1_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X4 X1, ((k1_bcialg_1 X1 X2 X4) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> (k1_bcialg_1 X1 X3 X4) = (k4_struct_0 X1) -> (k1_bcialg_1 X1 X2 X3) = (k4_struct_0 X1) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_bcialg_1 X1 X2 (esk17_3 X3 X1 X2) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> r2_hidden X3 (a_2_0_bcialg_1 X1 X2) -> m2_subset_1 X2 (u1_struct_0 X1) (k5_bcialg_1 X1) -> False)
  -> (forall X2 X3 X1, ((k1_bcialg_1 X1 X3 (k1_bcialg_1 X1 X3 X2)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> (k1_bcialg_1 X1 X2 X3) = (k4_struct_0 X1) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> v4_bcialg_3 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_bcialg_3 X1 -> False) -> (k1_bcialg_1 X1 (esk6_1 X1) (k1_bcialg_1 X1 (esk6_1 X1) (esk5_1 X1))) = (esk5_1 X1) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk17_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> v3_bcialg_1 X2 -> v4_bcialg_1 X2 -> v5_bcialg_1 X2 -> v7_bcialg_1 X2 -> l2_bcialg_1 X2 -> r2_hidden X1 (a_2_0_bcialg_1 X2 X3) -> m2_subset_1 X3 (u1_struct_0 X2) (k5_bcialg_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (u1_bcialg_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1))) -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_0_bcialg_1 X2 X4) -> False) -> X1 = X3 -> v3_bcialg_1 X2 -> v4_bcialg_1 X2 -> v5_bcialg_1 X2 -> v7_bcialg_1 X2 -> l2_bcialg_1 X2 -> r1_bcialg_1 X2 X4 X1 -> m1_subset_1 X1 (u1_struct_0 X2) -> m2_subset_1 X4 (u1_struct_0 X2) (k5_bcialg_1 X2) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m2_subset_1 (k6_bcialg_1 X1 X2 X3) (u1_struct_0 X1) (k5_bcialg_1 X1) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X3 (k5_bcialg_1 X1) -> m1_subset_1 X2 (k5_bcialg_1 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (k1_bcialg_1 X1 X3 X2) = (k4_struct_0 X1) -> (k1_bcialg_1 X1 X2 X3) = (k4_struct_0 X1) -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, ((esk17_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v3_bcialg_1 X2 -> v4_bcialg_1 X2 -> v5_bcialg_1 X2 -> v7_bcialg_1 X2 -> l2_bcialg_1 X2 -> r2_hidden X1 (a_2_0_bcialg_1 X2 X3) -> m2_subset_1 X3 (u1_struct_0 X2) (k5_bcialg_1 X2) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_bcialg_1 X1 X2 X3 -> False) -> (k1_bcialg_1 X1 X2 X3) = (k4_struct_0 X1) -> l2_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k1_bcialg_1 X1 X2 X3) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> l2_bcialg_1 X1 -> r1_bcialg_1 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_bcialg_1 X1 X2 X3) = (k1_bcialg_1 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X3 (k5_bcialg_1 X1) -> m1_subset_1 X2 (k5_bcialg_1 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k1_bcialg_1 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_bcialg_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((a_2_0_bcialg_1 X1 X2) = (k7_bcialg_1 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m2_subset_1 X2 (u1_struct_0 X1) (k5_bcialg_1 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X2 (k5_bcialg_1 X1) -> False) -> (k2_bcialg_1 X1 (k2_bcialg_1 X1 X2)) = X2 -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2, ((k2_bcialg_1 X2 (k2_bcialg_1 X2 X1)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v3_bcialg_1 X2 -> v4_bcialg_1 X2 -> v5_bcialg_1 X2 -> v7_bcialg_1 X2 -> l2_bcialg_1 X2 -> r2_hidden X1 (k5_bcialg_1 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k1_bcialg_1 X1 X2 (k4_struct_0 X1)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k7_bcialg_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X2 (k5_bcialg_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_bcialg_1 X1 -> False) -> (k1_bcialg_1 X1 (esk7_1 X1) (esk7_1 X1)) = (k4_struct_0 X1) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v1_funct_2 (u1_bcialg_1 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk15_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> v1_xboole_0 (k7_bcialg_1 X1 X2) -> m1_subset_1 X2 (k5_bcialg_1 X1) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_1_1_bcialg_1 X2) -> False) -> X1 = X3 -> v3_bcialg_1 X2 -> v4_bcialg_1 X2 -> v5_bcialg_1 X2 -> v7_bcialg_1 X2 -> l2_bcialg_1 X2 -> v10_bcialg_1 X1 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk16_2 X1 X2) (u1_struct_0 X2) -> False) -> v3_bcialg_1 X2 -> v4_bcialg_1 X2 -> v5_bcialg_1 X2 -> v7_bcialg_1 X2 -> l2_bcialg_1 X2 -> r2_hidden X1 (a_1_1_bcialg_1 X2) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k1_bcialg_1 X1 (k4_struct_0 X1) X2) = (k2_bcialg_1 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l2_bcialg_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, ((k1_bcialg_1 X1 (esk5_1 X1) (esk6_1 X1)) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> (v4_bcialg_3 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v10_bcialg_1 (esk16_2 X1 X2) X2 -> False) -> v3_bcialg_1 X2 -> v4_bcialg_1 X2 -> v5_bcialg_1 X2 -> v7_bcialg_1 X2 -> l2_bcialg_1 X2 -> r2_hidden X1 (a_1_1_bcialg_1 X2) -> False)
  -> (forall X2 X1, ((k1_bcialg_1 X1 X2 X2) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> v5_bcialg_1 X1 -> l2_bcialg_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk26_2 X3 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k2_bcialg_1 X1 X2) (u1_struct_0 X1) -> False) -> l2_bcialg_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2, ((esk16_2 X1 X2) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v3_bcialg_1 X2 -> v4_bcialg_1 X2 -> v5_bcialg_1 X2 -> v7_bcialg_1 X2 -> l2_bcialg_1 X2 -> r2_hidden X1 (a_1_1_bcialg_1 X2) -> False)
  -> (forall X1, ((k1_bcialg_1 X1 (esk9_1 X1) (esk8_1 X1)) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> (v7_bcialg_1 X1 -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, ((k1_bcialg_1 X1 (esk8_1 X1) (esk9_1 X1)) = (k4_struct_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> (v7_bcialg_1 X1 -> False) -> l2_bcialg_1 X1 -> False)
  -> ((m2_subset_1 esk4_0 (u1_struct_0 esk1_0) (k7_bcialg_1 esk1_0 esk2_0) -> False) -> v4_bcialg_3 esk1_0 -> False)
  -> ((m2_subset_1 esk3_0 (u1_struct_0 esk1_0) (k7_bcialg_1 esk1_0 esk2_0) -> False) -> v4_bcialg_3 esk1_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k5_bcialg_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_bcialg_3 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (u1_struct_0 X1) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_bcialg_3 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (u1_struct_0 X1) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_bcialg_3 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_bcialg_3 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> ((m2_subset_1 esk2_0 (u1_struct_0 esk1_0) (k5_bcialg_1 esk1_0) -> False) -> v4_bcialg_3 esk1_0 -> False)
  -> (forall X2 X1, (r2_hidden (esk26_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> v1_xboole_0 (k5_bcialg_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, ((a_1_1_bcialg_1 X1) = (k5_bcialg_1 X1) -> False) -> (v2_struct_0 X1 -> False) -> v3_bcialg_1 X1 -> v4_bcialg_1 X1 -> v5_bcialg_1 X1 -> v7_bcialg_1 X1 -> l2_bcialg_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l2_struct_0 X1 -> v9_struct_0 (esk19_1 X1) X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_bcialg_1 X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_bcialg_1 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_bcialg_1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (u1_struct_0 X1) -> False) -> l2_struct_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (u1_struct_0 X1) -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k4_struct_0 X1) (u1_struct_0 X1) -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_bcialg_1 X1 -> False) -> (esk9_1 X1) = (esk8_1 X1) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk22_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v9_struct_0 (esk18_1 X1) X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (v9_struct_0 (k4_struct_0 X1) X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk21_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_funct_1 (u1_bcialg_1 X1) -> False) -> l1_bcialg_1 X1 -> False)
  -> (forall X1, (l2_struct_0 X1 -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (l1_bcialg_1 X1 -> False) -> l2_bcialg_1 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_bcialg_1 X1 -> False)
  -> (v2_struct_0 esk20_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((l2_struct_0 esk20_0 -> False) -> False)
  -> ((l2_struct_0 esk13_0 -> False) -> False)
  -> ((l1_bcialg_1 esk10_0 -> False) -> False)
  -> ((v7_struct_0 esk20_0 -> False) -> False)
  -> ((l1_struct_0 esk11_0 -> False) -> False)
  -> ((l2_bcialg_1 esk12_0 -> False) -> False)
  -> ((l2_bcialg_1 esk1_0 -> False) -> False)
  -> ((v7_bcialg_1 esk1_0 -> False) -> False)
  -> ((v5_bcialg_1 esk1_0 -> False) -> False)
  -> ((v4_bcialg_1 esk1_0 -> False) -> False)
  -> ((v3_bcialg_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
