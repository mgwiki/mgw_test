(** $I sig/MizarPreamble.mgs **)

Theorem t43_yellow_4:
 forall k3_yellow_4:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall k4_subset_1:set -> set -> set -> set,
 forall esk16_2:set -> set -> set,
 forall v1_waybel_0:set -> set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk14_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk13_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall k1_xboole_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall esk8_0:set,
 forall esk7_0:set,
 forall o_0_0_xboole_0:set,
 forall esk9_1:set -> set,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk12_1:set -> set,
 forall esk15_1:set -> set,
 forall esk5_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v2_waybel_0:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall u1_struct_0:set -> set,
 forall a_3_18_yellow_4:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall l1_orders_2:set -> prop,
 forall k11_lattice3:set -> set -> set -> set,
 forall esk11_4:set -> set -> set -> set -> set,
 forall esk10_4:set -> set -> set -> set -> set,
     (forall X3 X1 X4 X2, ((k11_lattice3 X2 (esk10_4 X1 X2 X3 X4) (esk11_4 X1 X2 X3 X4)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_orders_2 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_18_yellow_4 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk11_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_18_yellow_4 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_18_yellow_4 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> l1_orders_2 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_18_yellow_4 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X3 -> False) -> l1_orders_2 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_18_yellow_4 X2 X3 X4) -> False)
  -> (forall X4 X5 X6 X3 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X4 (a_3_18_yellow_4 X2 X5 X6) -> False) -> X4 = (k11_lattice3 X2 X1 X3) -> l1_orders_2 X2 -> r2_hidden X3 X6 -> r2_hidden X1 X5 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> l1_orders_2 X1 -> v1_xboole_0 (k3_yellow_4 X1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k3_yellow_4 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k3_yellow_4 X1 X2 X3) = (a_3_18_yellow_4 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k11_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk16_2 X3 X2) -> False)
  -> (forall X1 X2, (v2_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v1_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk16_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk5_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
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
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk14_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_waybel_0 (esk12_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_waybel_0 (esk12_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk13_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k4_subset_1 (u1_struct_0 esk1_0) (k3_yellow_4 esk1_0 esk2_0 esk3_0) (k3_yellow_4 esk1_0 esk2_0 esk4_0)) = (k3_yellow_4 esk1_0 esk2_0 (k4_subset_1 (u1_struct_0 esk1_0) esk3_0 esk4_0)) -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk8_0 -> False) -> False)
  -> ((l1_orders_2 esk7_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
