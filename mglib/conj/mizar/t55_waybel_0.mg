(** $I sig/MizarPreamble.mgs **)

Theorem t55_waybel_0:
 forall u1_struct_0:set -> set,
 forall k1_xboole_0:set,
 forall a_2_7_waybel_0:set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall v1_waybel_0:set -> set -> prop,
 forall v1_lattice3:set -> prop,
 forall esk26_2:set -> set -> set,
 forall v6_orders_2:set -> set -> prop,
 forall esk15_1:set -> set,
 forall esk20_1:set -> set,
 forall esk18_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk23_1:set -> set,
 forall esk21_1:set -> set,
 forall esk8_1:set -> set,
 forall esk16_0:set,
 forall esk10_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall o_0_0_xboole_0:set,
 forall esk5_1:set -> set,
 forall esk14_1:set -> set,
 forall esk17_0:set,
 forall esk7_0:set,
 forall esk25_0:set,
 forall esk19_1:set -> set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v2_orders_2:set -> prop,
 forall v2_lattice3:set -> prop,
 forall v2_yellow_0:set -> prop,
 forall v3_yellow_0:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk13_1:set -> set,
 forall esk22_1:set -> set,
 forall esk24_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall r2_yellow_0:set -> set -> prop,
 forall v3_lattice3:set -> prop,
 forall v5_finset_1:set -> prop,
 forall esk9_1:set -> set,
 forall esk11_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk12_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk27_1:set -> set,
 forall v2_waybel_0:set -> set -> prop,
 forall v1_yellow_0:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v5_orders_2:set -> prop,
 forall k11_waybel_0:set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall v4_orders_2:set -> prop,
 forall l1_orders_2:set -> prop,
 forall v3_orders_2:set -> prop,
 forall k1_yellow_0:set -> set -> set,
 forall esk29_3:set -> set -> set -> set,
 forall r1_yellow_0:set -> set -> prop,
 forall esk28_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk30_3:set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_finset_1:set -> prop,
 forall epred1_3:set -> set -> set -> prop,
     (forall X4 X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (esk29_3 X2 X3 X1) = (k1_yellow_0 X1 X4) -> v1_finset_1 X4 -> r1_yellow_0 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> r1_yellow_0 X1 (esk28_3 X2 X3 X1) -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk29_3 X2 X3 X1) (u1_struct_0 X1) -> False) -> r1_yellow_0 X1 (esk28_3 X2 X3 X1) -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (r2_hidden (esk29_3 X2 X3 X1) X2 -> False) -> r1_yellow_0 X1 (esk28_3 X2 X3 X1) -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X4 X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk28_3 X2 X3 X1) (k1_zfmisc_1 X3) -> False) -> (esk29_3 X2 X3 X1) = (k1_yellow_0 X1 X4) -> v1_finset_1 X4 -> r1_yellow_0 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X4 X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (v1_finset_1 (esk28_3 X2 X3 X1) -> False) -> (esk29_3 X2 X3 X1) = (k1_yellow_0 X1 X4) -> v1_finset_1 X4 -> r1_yellow_0 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X4 X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (esk28_3 X2 X3 X1) = k1_xboole_0 -> (esk29_3 X2 X3 X1) = (k1_yellow_0 X1 X4) -> v1_finset_1 X4 -> r1_yellow_0 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk28_3 X2 X3 X1) (k1_zfmisc_1 X3) -> False) -> (m1_subset_1 (esk29_3 X2 X3 X1) (u1_struct_0 X1) -> False) -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (r2_hidden (esk29_3 X2 X3 X1) X2 -> False) -> (m1_subset_1 (esk28_3 X2 X3 X1) (k1_zfmisc_1 X3) -> False) -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (v1_finset_1 (esk28_3 X2 X3 X1) -> False) -> (m1_subset_1 (esk29_3 X2 X3 X1) (u1_struct_0 X1) -> False) -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (v1_finset_1 (esk28_3 X2 X3 X1) -> False) -> (r2_hidden (esk29_3 X2 X3 X1) X2 -> False) -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk29_3 X2 X3 X1) (u1_struct_0 X1) -> False) -> (esk28_3 X2 X3 X1) = k1_xboole_0 -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (r2_hidden (esk29_3 X2 X3 X1) X2 -> False) -> (esk28_3 X2 X3 X1) = k1_xboole_0 -> r2_hidden (k1_yellow_0 X1 (esk30_3 X2 X3 X1)) X2 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> r1_yellow_0 X3 (esk28_3 X1 X2 X3) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> r1_yellow_0 X3 (esk28_3 X1 X2 X3) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> r1_yellow_0 X3 (esk28_3 X1 X2 X3) -> False)
  -> (forall X3 X1 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> r1_yellow_0 X3 (esk28_3 X1 X2 X3) -> False)
  -> (forall X3 X1 X2, (epred1_3 X3 X2 X1 -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> r1_yellow_0 X3 (esk28_3 X1 X2 X3) -> False)
  -> (forall X3 X1 X2, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> r1_yellow_0 X3 (esk28_3 X1 X2 X3) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> r1_yellow_0 X3 (esk28_3 X1 X2 X3) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk28_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> r1_yellow_0 X3 (esk28_3 X1 X2 X3) -> False)
  -> (forall X3 X1 X2, (epred1_3 X3 X2 X1 -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> r1_yellow_0 X3 (esk28_3 X1 X2 X3) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk28_3 X1 X2 X3) -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (esk28_3 X1 X2 X3) = k1_xboole_0 -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> False)
  -> (forall X2 X3 X1, (epred1_3 X3 X2 X1 -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (esk28_3 X1 X2 X3) = k1_xboole_0 -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk28_3 X1 X2 X3) -> False) -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X2 X3 X1, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk28_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> False)
  -> (forall X2 X3 X1, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> False)
  -> (forall X2 X3 X1, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk28_3 X1 X2 X3) -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk28_3 X1 X2 X3) -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X1 X3 X2, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk28_3 X1 X2 X3) -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (esk28_3 X1 X2 X3) = k1_xboole_0 -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> (esk29_3 X1 X2 X3) = (k1_yellow_0 X3 X4) -> v1_finset_1 X4 -> r1_yellow_0 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (esk28_3 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (esk28_3 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (k1_zfmisc_1 X2) -> False) -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (esk28_3 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk28_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk30_3 X1 X2 X3) -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> (esk28_3 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (v1_finset_1 (esk28_3 X1 X2 X3) -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (esk28_3 X1 X2 X3) = k1_xboole_0 -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X1 -> False) -> (esk28_3 X1 X2 X3) = k1_xboole_0 -> (esk30_3 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, ((k1_yellow_0 X1 X2) = (k1_yellow_0 X1 X3) -> False) -> (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> l1_orders_2 X1 -> r1_yellow_0 X1 X2 -> epred1_3 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) (k1_zfmisc_1 X3) -> False) -> l1_orders_2 X2 -> r2_hidden X1 (a_2_7_waybel_0 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((k1_yellow_0 X2 (esk6_3 X1 X2 X3)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_orders_2 X2 -> r2_hidden X1 (a_2_7_waybel_0 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_yellow_0 X1 (esk6_3 X2 X1 X3) -> False) -> l1_orders_2 X1 -> r2_hidden X2 (a_2_7_waybel_0 X1 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v1_finset_1 (esk6_3 X1 X2 X3) -> False) -> l1_orders_2 X2 -> r2_hidden X1 (a_2_7_waybel_0 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1 X4, (v2_struct_0 X4 -> False) -> (r2_hidden X3 (a_2_7_waybel_0 X4 X2) -> False) -> X3 = (k1_yellow_0 X4 X1) -> l1_orders_2 X4 -> v1_finset_1 X1 -> r1_yellow_0 X4 X1 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X4)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> v3_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> v1_xboole_0 (k11_waybel_0 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_waybel_0 (k11_waybel_0 X1 X2) X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v5_orders_2 X1 -> l1_orders_2 X1 -> v1_yellow_0 X1 -> v1_xboole_0 (k11_waybel_0 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k11_waybel_0 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_yellow_0 X1 X2 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v1_finset_1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk26_2 X3 X2) -> False)
  -> (forall X2 X1, ((k11_waybel_0 X1 X2) = (a_2_7_waybel_0 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v6_orders_2 X2 X1 -> False) -> l1_orders_2 X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v2_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v1_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1, (v1_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> r1_yellow_0 X1 (esk27_1 X1) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk26_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_yellow_0 X1 X2) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> (v1_finset_1 (esk27_1 X1) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r2_yellow_0 X1 X2 -> False) -> v5_orders_2 X1 -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r1_yellow_0 X1 X2 -> False) -> v5_orders_2 X1 -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_waybel_0 (esk15_1 X1) X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_waybel_0 (esk15_1 X1) X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v3_lattice3 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v5_orders_2 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_finset_1 (esk15_1 X1) -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk12_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk11_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v6_orders_2 (esk18_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_waybel_0 (esk9_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_waybel_0 (esk9_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v3_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v1_yellow_0 X1 -> v2_yellow_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_lattice3 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v1_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk11_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, l1_orders_2 X1 -> v2_struct_0 X1 -> v2_lattice3 X1 -> False)
  -> (forall X1, v1_lattice3 X1 -> l1_orders_2 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk24_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk23_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk8_1 X1) -> False)
  -> (forall X1, (v2_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v3_yellow_0 X1 -> False)
  -> (forall X1, (v1_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v3_yellow_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_orders_2 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk13_1 X1) -> False) -> False)
  -> ((v3_lattice3 esk1_0 -> False) -> (r1_yellow_0 esk1_0 esk2_0 -> False) -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k1_yellow_0 esk1_0 (k11_waybel_0 esk1_0 esk2_0)) = (k1_yellow_0 esk1_0 esk2_0) -> False)
  -> (forall X1, v1_subset_1 (esk19_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk7_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk17_0 -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk14_1 X1) -> False) -> False)
  -> ((v5_finset_1 esk25_0 -> False) -> False)
  -> ((v2_orders_2 esk17_0 -> False) -> False)
  -> ((v1_finset_1 esk25_0 -> False) -> False)
  -> ((v1_finset_1 esk7_0 -> False) -> False)
  -> ((v1_xboole_0 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk4_0 -> False) -> False)
  -> ((v3_lattice3 esk17_0 -> False) -> False)
  -> ((l1_orders_2 esk17_0 -> False) -> False)
  -> ((l1_orders_2 esk3_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> ((v1_lattice3 esk1_0 -> False) -> False)
  -> ((v5_orders_2 esk17_0 -> False) -> False)
  -> ((v5_orders_2 esk1_0 -> False) -> False)
  -> ((v4_orders_2 esk17_0 -> False) -> False)
  -> ((v4_orders_2 esk1_0 -> False) -> False)
  -> ((v3_orders_2 esk17_0 -> False) -> False)
  -> ((v3_orders_2 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
