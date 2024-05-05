(** $I sig/MizarPreamble.mgs **)

Theorem t30_yellow_4:
 forall esk11_4:set -> set -> set -> set -> set,
 forall esk12_4:set -> set -> set -> set -> set,
 forall esk13_4:set -> set -> set -> set -> set,
 forall a_3_0_yellow_2:set -> set -> set -> set,
 forall r1_orders_2:set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall k2_yellow_4:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v2_waybel_0:set -> set -> prop,
 forall r3_orders_2:set -> set -> set -> prop,
 forall v12_waybel_0:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall g1_orders_2:set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall esk26_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk24_1:set -> set,
 forall esk19_1:set -> set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall k1_xboole_0:set,
 forall v16_waybel_0:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk9_1:set -> set,
 forall esk20_0:set,
 forall esk8_0:set,
 forall esk7_0:set,
 forall o_0_0_xboole_0:set,
 forall esk1_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall v3_yellow_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk21_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk22_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk23_1:set -> set,
 forall v2_lattice3:set -> prop,
 forall v25_waybel_0:set -> prop,
 forall v2_yellow_0:set -> prop,
 forall v24_waybel_0:set -> prop,
 forall esk25_1:set -> set,
 forall v1_yellow_0:set -> prop,
 forall v3_lattice3:set -> prop,
 forall u1_orders_2:set -> set,
 forall v1_orders_2:set -> prop,
 forall a_1_0_waybel_0:set -> set,
 forall v1_waybel_0:set -> set -> prop,
 forall k1_yellow_4:set -> set -> set -> set,
 forall esk27_3:set -> set -> set -> set,
 forall k3_waybel_0:set -> set -> set,
 forall k7_domain_1:set -> set -> set -> set,
 forall r1_yellow_0:set -> set -> prop,
 forall v2_struct_0:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall a_3_0_yellow_4:set -> set -> set -> set,
 forall k10_lattice3:set -> set -> set -> set,
 forall esk15_4:set -> set -> set -> set -> set,
 forall esk14_4:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v3_orders_2:set -> prop,
 forall v5_orders_2:set -> prop,
 forall l1_orders_2:set -> prop,
 forall u1_struct_0:set -> set,
 forall k7_waybel_0:set -> set,
 forall k2_yellow_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall a_3_8_yellow_4:set -> set -> set -> set,
 forall v1_lattice3:set -> prop,
 forall v4_orders_2:set -> prop,
 forall k13_lattice3:set -> set -> set -> set,
 forall esk18_4:set -> set -> set -> set -> set,
 forall esk17_4:set -> set -> set -> set -> set,
 forall esk16_4:set -> set -> set -> set -> set,
     (forall X3 X4 X1 X2, ((k13_lattice3 X2 (esk17_4 X1 X2 X3 X4) (esk18_4 X1 X2 X3 X4)) = (esk16_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk16_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk16_4 X1 X2 X3 X4) X3 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_8_yellow_4 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, ((k13_lattice3 X2 (esk12_4 X1 X2 X3 X4) (esk13_4 X1 X2 X3 X4)) = (esk11_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X3 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_0_yellow_2 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden (esk16_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk16_4 X1 X2 X3 X4) X3 -> False) -> (m1_subset_1 (esk18_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_8_yellow_4 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden (esk16_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk16_4 X1 X2 X3 X4) X3 -> False) -> (m1_subset_1 (esk17_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_8_yellow_4 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X3 -> False) -> (m1_subset_1 (esk13_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_0_yellow_2 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X3 -> False) -> (m1_subset_1 (esk12_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_0_yellow_2 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden (esk16_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk16_4 X1 X2 X3 X4) X3 -> False) -> (r2_hidden (esk18_4 X1 X2 X3 X4) X4 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_8_yellow_4 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden (esk16_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk16_4 X1 X2 X3 X4) X3 -> False) -> (r2_hidden (esk17_4 X1 X2 X3 X4) X3 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_8_yellow_4 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X3 -> False) -> (r2_hidden (esk13_4 X1 X2 X3 X4) X4 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_0_yellow_2 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X3 -> False) -> (r2_hidden (esk12_4 X1 X2 X3 X4) X3 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_0_yellow_2 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X1 X4 X2, ((k10_lattice3 X2 (esk14_4 X1 X2 X3 X4) (esk15_4 X1 X2 X3 X4)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_orders_2 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_yellow_4 X2 X3 X4) -> False)
  -> (forall X3 X4 X1 X2, (m1_subset_1 (esk16_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_8_yellow_4 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (m1_subset_1 (esk11_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_0_yellow_2 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk15_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_yellow_4 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk14_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_yellow_4 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk15_4 X1 X2 X3 X4) X4 -> False) -> l1_orders_2 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_yellow_4 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk14_4 X1 X2 X3 X4) X3 -> False) -> l1_orders_2 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_yellow_4 X2 X3 X4) -> False)
  -> (forall X3 X4 X1 X2, ((esk16_4 X1 X2 X3 X4) = X1 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_8_yellow_4 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, ((esk11_4 X1 X2 X3 X4) = X1 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_3_0_yellow_2 X2 X3 X4) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X2 X4 X5 X3 X1, (r1_orders_2 X1 (k13_lattice3 X1 X2 X3) (k13_lattice3 X1 X4 X5) -> False) -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X5 -> r1_orders_2 X1 X2 X4 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X6 X3 X1 X5 X4 X2 X7, (r2_hidden X7 (a_3_8_yellow_4 X2 X4 X5) -> False) -> X6 = X7 -> X6 = (k13_lattice3 X2 X1 X3) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X3 X5 -> r2_hidden X1 X4 -> m1_subset_1 X6 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X5 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X6 X3 X1 X5 X4 X2 X7, (r2_hidden X7 (a_3_0_yellow_2 X2 X4 X5) -> False) -> X6 = X7 -> X6 = (k13_lattice3 X2 X1 X3) -> v3_orders_2 X2 -> v4_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r2_hidden X3 X5 -> r2_hidden X1 X4 -> m1_subset_1 X6 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X5 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> m1_subset_1 X4 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X2 X3 X1, (r1_yellow_0 (k2_yellow_1 (k7_waybel_0 X1)) (k7_domain_1 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X1))) X2 X3) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X1))) -> m1_subset_1 X2 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X1))) -> False)
  -> (forall X4 X5 X6 X3 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X4 (a_3_0_yellow_4 X2 X5 X6) -> False) -> X4 = (k10_lattice3 X2 X1 X3) -> l1_orders_2 X2 -> r2_hidden X3 X6 -> r2_hidden X1 X5 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, ((k10_lattice3 (k2_yellow_1 (k7_waybel_0 X1)) X2 X3) = (k3_waybel_0 X1 (esk27_3 X1 X2 X3)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X1))) -> m1_subset_1 X2 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X1))) -> False)
  -> (forall X1 X5 X2 X3 X4, (r2_hidden X4 (a_3_8_yellow_4 X3 X2 X5) -> False) -> X1 = X4 -> v3_orders_2 X3 -> v4_orders_2 X3 -> v5_orders_2 X3 -> v1_lattice3 X3 -> l1_orders_2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X1 (u1_struct_0 X3) -> m1_subset_1 X5 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X3))) -> m1_subset_1 X2 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X3))) -> False)
  -> (forall X1 X2 X5 X3 X4, (r2_hidden X4 (a_3_8_yellow_4 X3 X5 X2) -> False) -> X1 = X4 -> v3_orders_2 X3 -> v4_orders_2 X3 -> v5_orders_2 X3 -> v1_lattice3 X3 -> l1_orders_2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X1 (u1_struct_0 X3) -> m1_subset_1 X5 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X3))) -> m1_subset_1 X2 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X3))) -> False)
  -> (forall X1 X5 X2 X3 X4, (r2_hidden X4 (a_3_0_yellow_2 X3 X2 X5) -> False) -> X1 = X4 -> v3_orders_2 X3 -> v4_orders_2 X3 -> v5_orders_2 X3 -> v1_lattice3 X3 -> l1_orders_2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X1 (u1_struct_0 X3) -> m1_subset_1 X5 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X3))) -> m1_subset_1 X2 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X3))) -> False)
  -> (forall X1 X2 X5 X3 X4, (r2_hidden X4 (a_3_0_yellow_2 X3 X5 X2) -> False) -> X1 = X4 -> v3_orders_2 X3 -> v4_orders_2 X3 -> v5_orders_2 X3 -> v1_lattice3 X3 -> l1_orders_2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X1 (u1_struct_0 X3) -> m1_subset_1 X5 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X3))) -> m1_subset_1 X2 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X3))) -> False)
  -> (forall X1 X2 X3, (v1_xboole_0 X3 -> False) -> (r1_tarski X2 (k3_waybel_0 X1 (k2_yellow_4 X1 X2 X3)) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (esk27_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X1))) -> m1_subset_1 X2 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X1))) -> False)
  -> (forall X2 X3 X1, ((a_3_0_yellow_2 X1 X2 X3) = (esk27_3 X1 X2 X3) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X1))) -> m1_subset_1 X2 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X1))) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> l1_orders_2 X1 -> v1_xboole_0 (k1_yellow_4 X1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_waybel_0 (k1_yellow_4 X1 X2 X3) X1 -> False) -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v2_waybel_0 X3 X1 -> v2_waybel_0 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v1_waybel_0 (k1_yellow_4 X1 X2 X3) X1 -> False) -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v1_waybel_0 X3 X1 -> v1_waybel_0 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k2_yellow_4 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k1_yellow_4 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (r1_orders_2 X2 X3 X1 -> False) -> (k13_lattice3 X2 X1 X3) = X1 -> v3_orders_2 X2 -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X2 X1, ((k13_lattice3 X1 X3 X2) = X3 -> False) -> v3_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k2_yellow_4 X1 X2 X3) = (k1_yellow_4 X1 X2 X3) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, ((k2_yellow_4 X1 X2 X3) = (k2_yellow_4 X1 X3 X2) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X2 X3 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> r3_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_orders_2 X1 X2 X3 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k1_yellow_4 X1 X2 X3) = (a_3_0_yellow_4 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_tarski X2 X3 -> False) -> r3_orders_2 (k2_yellow_1 X1) X2 X3 -> m1_subset_1 X3 (u1_struct_0 (k2_yellow_1 X1)) -> m1_subset_1 X2 (u1_struct_0 (k2_yellow_1 X1)) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k13_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k3_waybel_0 X1 X2) (k3_waybel_0 X1 X3) -> False) -> l1_orders_2 X1 -> r1_tarski X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k10_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k13_lattice3 X1 X2 X3) = (k10_lattice3 X1 X2 X3) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k13_lattice3 X1 X2 X3) = (k13_lattice3 X1 X3 X2) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r3_orders_2 (k2_yellow_1 X3) X1 X2 -> False) -> r1_tarski X1 X2 -> m1_subset_1 X2 (u1_struct_0 (k2_yellow_1 X3)) -> m1_subset_1 X1 (u1_struct_0 (k2_yellow_1 X3)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X1 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> v1_waybel_0 X1 X2 -> v12_waybel_0 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k7_domain_1 X1 X2 X3) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X1 X3) = (g1_orders_2 X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X3 X1) = (g1_orders_2 X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X2 X3 X1, ((k7_domain_1 X1 X2 X3) = (k7_domain_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden X3 (a_1_0_waybel_0 X2) -> False) -> X1 = X3 -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> v1_waybel_0 X1 X2 -> v12_waybel_0 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> m1_subset_1 X1 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X1 X2, (v1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (l1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_waybel_0 (k3_waybel_0 X1 X2) X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> l1_orders_2 X1 -> v1_waybel_0 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_orders_2 X1 X2 X2 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (m1_subset_1 (u1_orders_2 X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v12_waybel_0 X1 X2 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> m1_subset_1 X1 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v1_waybel_0 X1 X2 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> m1_subset_1 X1 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 X2))) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v1_xboole_0 (k3_waybel_0 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, ((k7_domain_1 X1 X2 X3) = (k2_tarski X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_waybel_0 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk10_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_1_0_waybel_0 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v12_waybel_0 (k3_waybel_0 X1 X2) X1 -> False) -> v4_orders_2 X1 -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk26_2 X3 X2) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> v1_xboole_0 (esk10_2 X1 X2) -> r2_hidden X1 (a_1_0_waybel_0 X2) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v12_waybel_0 (esk10_2 X1 X2) X2 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_1_0_waybel_0 X2) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v1_waybel_0 (esk10_2 X1 X2) X2 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_1_0_waybel_0 X2) -> False)
  -> (forall X1 X2, (v2_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v1_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X1 X2, ((esk10_2 X1 X2) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v3_orders_2 X2 -> v4_orders_2 X2 -> l1_orders_2 X2 -> r2_hidden X1 (a_1_0_waybel_0 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v3_lattice3 (k2_yellow_1 (k7_waybel_0 X1)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v1_yellow_0 X1 -> False)
  -> (forall X1, (v1_orders_2 (k2_yellow_1 (k7_waybel_0 X1)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v1_yellow_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk26_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_lattice3 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> v24_waybel_0 X1 -> v2_yellow_0 X1 -> v25_waybel_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_lattice3 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v24_waybel_0 X1 -> v1_yellow_0 X1 -> False)
  -> (forall X1, (v2_lattice3 (k2_yellow_1 (k7_waybel_0 X1)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> v2_lattice3 X1 -> False)
  -> (forall X1, (v1_orders_2 (k2_yellow_1 (k7_waybel_0 X1)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> v2_lattice3 X1 -> False)
  -> (forall X1, (v1_orders_2 (k2_yellow_1 (k7_waybel_0 X1)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_lattice3 (k2_yellow_1 (k7_waybel_0 X1)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v12_waybel_0 (esk25_1 X1) X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_waybel_0 (esk25_1 X1) X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> v2_yellow_0 X1 -> v25_waybel_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> l1_orders_2 X1 -> v1_xboole_0 (esk25_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> l1_orders_2 X1 -> v1_xboole_0 (k7_waybel_0 X1) -> False)
  -> (forall X1, ((g1_orders_2 (u1_struct_0 X1) (u1_orders_2 X1)) = X1 -> False) -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_waybel_0 (esk23_1 X1) X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_waybel_0 (esk23_1 X1) X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v3_lattice3 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v5_orders_2 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_lattice3 X1 -> False) -> v3_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> v25_waybel_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, ((a_1_0_waybel_0 X1) = (k7_waybel_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_yellow_0 X1 -> False) -> v3_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v24_waybel_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v16_waybel_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_yellow_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v25_waybel_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v25_waybel_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v24_waybel_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_finset_1 (esk23_1 X1) -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk22_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_waybel_0 (esk19_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_waybel_0 (esk19_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v3_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v2_yellow_0 X1 -> v1_yellow_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_lattice3 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v1_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk21_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, l1_orders_2 X1 -> v2_struct_0 X1 -> v2_lattice3 X1 -> False)
  -> (forall X1, v1_lattice3 X1 -> l1_orders_2 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v2_struct_0 (k2_yellow_1 X1) -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v3_yellow_0 X1 -> False)
  -> (forall X1, (v2_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v3_yellow_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_orders_2 (k2_yellow_1 X1) -> False) -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k13_lattice3 (k2_yellow_1 (k7_waybel_0 esk1_0)) esk2_0 esk3_0) = (k3_waybel_0 esk1_0 (k2_yellow_4 esk1_0 esk4_0 esk5_0)) -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 esk1_0))) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 (k2_yellow_1 (k7_waybel_0 esk1_0))) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v13_struct_0 esk20_0 np__1 -> False) -> False)
  -> (forall X1, (v1_orders_2 (k2_yellow_1 X1) -> False) -> False)
  -> (forall X1, (v1_orders_2 (k2_yellow_1 X1) -> False) -> False)
  -> (forall X1, (l1_orders_2 (k2_yellow_1 X1) -> False) -> False)
  -> (forall X1, (v5_orders_2 (k2_yellow_1 X1) -> False) -> False)
  -> (forall X1, (v4_orders_2 (k2_yellow_1 X1) -> False) -> False)
  -> (forall X1, (v3_orders_2 (k2_yellow_1 X1) -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk8_0 -> False) -> False)
  -> ((v1_orders_2 esk20_0 -> False) -> False)
  -> ((l1_orders_2 esk20_0 -> False) -> False)
  -> ((l1_orders_2 esk7_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> ((v1_lattice3 esk1_0 -> False) -> False)
  -> ((v5_orders_2 esk1_0 -> False) -> False)
  -> ((v4_orders_2 esk1_0 -> False) -> False)
  -> ((v3_orders_2 esk20_0 -> False) -> False)
  -> ((v3_orders_2 esk1_0 -> False) -> False)
  -> ((esk3_0 = esk5_0 -> False) -> False)
  -> ((esk2_0 = esk4_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
