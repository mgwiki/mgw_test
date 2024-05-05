(** $I sig/MizarPreamble.mgs **)

Theorem l115_waybel_1:
 forall v2_lattice3:set -> prop,
 forall r1_orders_2:set -> set -> set -> prop,
 forall esk21_4:set -> set -> set -> set -> set,
 forall l1_orders_2:set -> prop,
 forall v5_orders_2:set -> prop,
 forall v2_waybel_1:set -> prop,
 forall v3_orders_2:set -> prop,
 forall v4_orders_2:set -> prop,
 forall esk22_1:set -> set,
 forall esk24_1:set -> set,
 forall esk23_1:set -> set,
 forall k4_yellow_0:set -> set,
 forall k3_yellow_0:set -> set,
 forall r6_waybel_1:set -> set -> set -> prop,
 forall v2_yellow_0:set -> prop,
 forall v24_waybel_0:set -> prop,
 forall v25_waybel_0:set -> prop,
 forall v3_lattice3:set -> prop,
 forall k2_yellow_0:set -> set -> set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall k1_xboole_0:set,
 forall v16_waybel_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk19_0:set,
 forall esk13_0:set,
 forall esk11_1:set -> set,
 forall esk16_0:set,
 forall esk14_0:set,
 forall esk10_0:set,
 forall esk9_0:set,
 forall o_0_0_xboole_0:set,
 forall esk12_0:set,
 forall esk15_0:set,
 forall esk17_0:set,
 forall esk18_0:set,
 forall v3_relat_1:set -> prop,
 forall v3_yellow_0:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall v7_struct_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall l1_struct_0:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k1_yellow_0:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall v1_yellow_0:set -> prop,
 forall esk5_1:set -> set,
 forall v10_waybel_1:set -> prop,
 forall v2_struct_0:set -> prop,
 forall esk7_1:set -> set,
 forall esk8_1:set -> set,
 forall k10_lattice3:set -> set -> set -> set,
 forall esk6_1:set -> set,
 forall k11_lattice3:set -> set -> set -> set,
 forall esk20_4:set -> set -> set -> set -> set,
 forall v1_lattice3:set -> prop,
 forall k12_lattice3:set -> set -> set -> set,
 forall esk2_0:set,
 forall k13_lattice3:set -> set -> set -> set,
 forall esk3_1:set -> set,
 forall r3_orders_2:set -> set -> set -> prop,
 forall esk1_0:set,
 forall u1_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
     (forall X1, m1_subset_1 X1 (u1_struct_0 esk1_0) -> r3_orders_2 esk1_0 (esk3_1 X1) (k13_lattice3 esk1_0 (k12_lattice3 esk1_0 (esk3_1 X1) esk2_0) X1) -> r3_orders_2 esk1_0 (k12_lattice3 esk1_0 (k13_lattice3 esk1_0 (esk3_1 X1) X1) esk2_0) (esk3_1 X1) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k12_lattice3 X1 X2 X3) -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X4 X3 -> r1_orders_2 X1 X4 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_orders_2 X1 (esk21_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X4 X2 X3 X1, (X2 = (k13_lattice3 X1 X3 X4) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X4 X2 -> r1_orders_2 X1 X3 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_orders_2 X1 X2 (esk20_4 X1 X3 X4 X2) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k12_lattice3 X1 X2 X3) -> False) -> (r1_orders_2 X1 (esk21_4 X1 X2 X3 X4) X2 -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X4 X3 -> r1_orders_2 X1 X4 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k12_lattice3 X1 X2 X3) -> False) -> (r1_orders_2 X1 (esk21_4 X1 X2 X3 X4) X3 -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X4 X3 -> r1_orders_2 X1 X4 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (X4 = (k13_lattice3 X1 X2 X3) -> False) -> (r1_orders_2 X1 X2 (esk20_4 X1 X2 X3 X4) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X4 -> r1_orders_2 X1 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (X4 = (k13_lattice3 X1 X3 X2) -> False) -> (r1_orders_2 X1 X2 (esk20_4 X1 X3 X2 X4) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X4 -> r1_orders_2 X1 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k12_lattice3 X1 X2 X3) -> False) -> (m1_subset_1 (esk21_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X4 X3 -> r1_orders_2 X1 X4 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (X4 = (k13_lattice3 X1 X2 X3) -> False) -> (m1_subset_1 (esk20_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X4 -> r1_orders_2 X1 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_waybel_1 X1 -> False) -> (k12_lattice3 X1 (k13_lattice3 X1 (esk22_1 X1) (esk23_1 X1)) (k13_lattice3 X1 (esk22_1 X1) (esk24_1 X1))) = (k13_lattice3 X1 (esk22_1 X1) (k12_lattice3 X1 (esk23_1 X1) (esk24_1 X1))) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_waybel_1 X1 -> False) -> (v2_struct_0 X1 -> False) -> (k10_lattice3 X1 (k11_lattice3 X1 (esk6_1 X1) (esk7_1 X1)) (k11_lattice3 X1 (esk6_1 X1) (esk8_1 X1))) = (k11_lattice3 X1 (esk6_1 X1) (k10_lattice3 X1 (esk7_1 X1) (esk8_1 X1))) -> l1_orders_2 X1 -> False)
  -> (forall X4 X3 X2 X1, ((k12_lattice3 X1 (k13_lattice3 X1 X2 X3) (k13_lattice3 X1 X2 X4)) = (k13_lattice3 X1 X2 (k12_lattice3 X1 X3 X4)) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> v2_waybel_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, ((k10_lattice3 X1 (k11_lattice3 X1 X2 X3) (k11_lattice3 X1 X2 X4)) = (k11_lattice3 X1 X2 (k10_lattice3 X1 X3 X4)) -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v2_waybel_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X5 X1 X2, (r1_orders_2 X2 X1 X5 -> False) -> X5 = (k12_lattice3 X2 X3 X4) -> v5_orders_2 X2 -> v2_lattice3 X2 -> l1_orders_2 X2 -> r1_orders_2 X2 X1 X4 -> r1_orders_2 X2 X1 X3 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X4 X1 X5 X2, (r1_orders_2 X2 X5 X1 -> False) -> X5 = (k13_lattice3 X2 X3 X4) -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r1_orders_2 X2 X4 X1 -> r1_orders_2 X2 X3 X1 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r6_waybel_1 X1 X2 X3 -> False) -> (k10_lattice3 X1 X2 X3) = (k4_yellow_0 X1) -> (k11_lattice3 X1 X2 X3) = (k3_yellow_0 X1) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r1_orders_2 X1 X2 X3 -> False) -> X2 = (k12_lattice3 X1 X3 X4) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r1_orders_2 X1 X2 X3 -> False) -> X2 = (k12_lattice3 X1 X4 X3) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r1_orders_2 X1 X2 X3 -> False) -> X3 = (k13_lattice3 X1 X2 X4) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r1_orders_2 X1 X2 X3 -> False) -> X3 = (k13_lattice3 X1 X4 X2) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X2 X3 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> r3_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_orders_2 X1 X2 X3 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k11_lattice3 X1 X2 X3) = (k3_yellow_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> r6_waybel_1 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k10_lattice3 X1 X2 X3) = (k4_yellow_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> r6_waybel_1 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k12_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k13_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k11_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k10_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k12_lattice3 X1 X2 X3) = (k11_lattice3 X1 X2 X3) -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k13_lattice3 X1 X2 X3) = (k10_lattice3 X1 X2 X3) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k12_lattice3 X1 X2 X3) = (k12_lattice3 X1 X3 X2) -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k13_lattice3 X1 X2 X3) = (k13_lattice3 X1 X3 X2) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2, (v10_waybel_1 X2 -> False) -> (v2_struct_0 X2 -> False) -> l1_orders_2 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> r6_waybel_1 X2 (esk5_1 X2) X1 -> False)
  -> (forall X2 X1, ((k11_lattice3 X1 (k4_yellow_0 X1) X2) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> v2_yellow_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k10_lattice3 X1 (k3_yellow_0 X1) X2) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v1_yellow_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_orders_2 X1 X2 X2 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r6_waybel_1 X1 X2 (esk4_2 X1 X2) -> False) -> l1_orders_2 X1 -> v10_waybel_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k11_lattice3 X1 (k3_yellow_0 X1) X2) = (k3_yellow_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> v1_yellow_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k10_lattice3 X1 (k4_yellow_0 X1) X2) = (k4_yellow_0 X1) -> False) -> (v2_struct_0 X1 -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v2_yellow_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk4_2 X1 X2) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> v10_waybel_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_waybel_1 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (u1_struct_0 X1) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_waybel_1 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (u1_struct_0 X1) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_waybel_1 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (u1_struct_0 X1) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_lattice3 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> v24_waybel_0 X1 -> v2_yellow_0 X1 -> v25_waybel_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_lattice3 X1 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v24_waybel_0 X1 -> v1_yellow_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_yellow_0 X1 X2) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_yellow_0 X1 X2) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk3_1 X1) (u1_struct_0 esk1_0) -> False) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> v2_yellow_0 X1 -> v25_waybel_0 X1 -> False)
  -> (forall X1, (v10_waybel_1 X1 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_waybel_1 X1 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_waybel_1 X1 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_waybel_1 X1 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v3_lattice3 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v5_orders_2 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> v5_orders_2 X1 -> l1_orders_2 X1 -> v25_waybel_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (k4_yellow_0 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (m1_subset_1 (k3_yellow_0 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_yellow_0 X1 -> False) -> v3_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> v24_waybel_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v16_waybel_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_yellow_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v25_waybel_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v25_waybel_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v24_waybel_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v2_yellow_0 X1 -> v1_yellow_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, ((k2_yellow_0 X1 k1_xboole_0) = (k4_yellow_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, ((k1_yellow_0 X1 k1_xboole_0) = (k3_yellow_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v3_yellow_0 X1 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v2_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v1_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, v2_lattice3 X1 -> l1_orders_2 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, v1_lattice3 X1 -> l1_orders_2 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_yellow_0 X1 -> False) -> v3_yellow_0 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_yellow_0 X1 -> False) -> v3_yellow_0 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v3_funct_1 esk18_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v4_funct_1 esk19_0 -> False) -> False)
  -> ((v2_relat_1 esk17_0 -> False) -> False)
  -> ((v2_relat_1 esk16_0 -> False) -> False)
  -> ((v2_relat_1 esk15_0 -> False) -> False)
  -> ((v2_funct_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((v10_waybel_1 esk1_0 -> False) -> False)
  -> ((v2_waybel_1 esk1_0 -> False) -> False)
  -> ((l1_orders_2 esk9_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> ((v3_yellow_0 esk1_0 -> False) -> False)
  -> ((v2_lattice3 esk1_0 -> False) -> False)
  -> ((v1_lattice3 esk1_0 -> False) -> False)
  -> ((v5_orders_2 esk1_0 -> False) -> False)
  -> ((v4_orders_2 esk1_0 -> False) -> False)
  -> ((v3_orders_2 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
