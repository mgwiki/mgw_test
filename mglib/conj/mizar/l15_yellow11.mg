(** $I sig/MizarPreamble.mgs **)

Theorem l15_yellow11:
 forall k13_lattice3:set -> set -> set -> set,
 forall v1_lattice3:set -> prop,
 forall esk36_4:set -> set -> set -> set -> set,
 forall r3_orders_2:set -> set -> set -> prop,
 forall v4_orders_2:set -> prop,
 forall v3_orders_2:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk13_1:set -> set,
 forall esk14_1:set -> set,
 forall esk8_1:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk3_0:set,
 forall v7_struct_0:set -> prop,
 forall esk23_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk22_1:set -> set,
 forall esk28_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v3_lattice3:set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall v3_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall esk35_1:set -> set,
 forall esk32_1:set -> set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall esk29_1:set -> set,
 forall esk33_0:set,
 forall esk24_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall esk25_1:set -> set,
 forall v2_xxreal_0:set -> prop,
 forall esk30_0:set,
 forall esk21_0:set,
 forall esk19_0:set,
 forall esk15_0:set,
 forall esk16_0:set,
 forall o_0_0_xboole_0:set,
 forall esk17_1:set -> set,
 forall esk27_0:set,
 forall esk26_0:set,
 forall v2_orders_2:set -> prop,
 forall k4_ordinal1:set,
 forall v7_ordinal1:set -> prop,
 forall v1_yellow_0:set -> prop,
 forall v2_yellow_0:set -> prop,
 forall v3_yellow_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk20_1:set -> set,
 forall esk34_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk31_1:set -> set,
 forall esk2_0:set,
 forall esk6_0:set,
 forall esk4_0:set,
 forall esk5_0:set,
 forall v1_subset_1:set -> set -> prop,
 forall v6_orders_2:set -> set -> prop,
 forall esk9_1:set -> set,
 forall esk7_1:set -> set,
 forall esk18_2:set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall k10_lattice3:set -> set -> set -> set,
 forall esk11_1:set -> set,
 forall esk10_1:set -> set,
 forall esk12_1:set -> set,
 forall k11_lattice3:set -> set -> set -> set,
 forall v1_yellow11:set -> prop,
 forall esk1_0:set,
 forall v5_orders_2:set -> prop,
 forall l1_orders_2:set -> prop,
 forall esk37_4:set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall r1_orders_2:set -> set -> set -> prop,
 forall v2_lattice3:set -> prop,
 forall k12_lattice3:set -> set -> set -> set,
     (forall X4 X3 X2 X1, (X4 = (k12_lattice3 X1 X2 X3) -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X4 X3 -> r1_orders_2 X1 X4 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_orders_2 X1 (esk37_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X4 X2 X3 X1, (X2 = (k13_lattice3 X1 X3 X4) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X4 X2 -> r1_orders_2 X1 X3 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_orders_2 X1 X2 (esk36_4 X1 X3 X4 X2) -> False)
  -> (forall X3 X2 X1 X4 X5, (X4 = X5 -> False) -> (X3 = X5 -> False) -> (X3 = X4 -> False) -> (X2 = X5 -> False) -> (X2 = X4 -> False) -> (X2 = X3 -> False) -> (X1 = X5 -> False) -> (X1 = X4 -> False) -> (X1 = X3 -> False) -> (X1 = X2 -> False) -> (v1_yellow11 esk1_0 -> False) -> (k12_lattice3 esk1_0 X4 X5) = X4 -> (k12_lattice3 esk1_0 X3 X5) = X3 -> (k12_lattice3 esk1_0 X3 X4) = X1 -> (k12_lattice3 esk1_0 X2 X4) = X2 -> (k12_lattice3 esk1_0 X2 X3) = X1 -> (k12_lattice3 esk1_0 X1 X3) = X1 -> (k12_lattice3 esk1_0 X1 X2) = X1 -> (k13_lattice3 esk1_0 X3 X4) = X5 -> (k13_lattice3 esk1_0 X2 X3) = X5 -> m1_subset_1 X5 (u1_struct_0 esk1_0) -> m1_subset_1 X4 (u1_struct_0 esk1_0) -> m1_subset_1 X3 (u1_struct_0 esk1_0) -> m1_subset_1 X2 (u1_struct_0 esk1_0) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> False)
  -> (forall X3 X4 X2 X1, (r3_orders_2 X1 (k13_lattice3 X1 X2 (k12_lattice3 X1 X3 X4)) (k12_lattice3 X1 (k13_lattice3 X1 X2 X3) X4) -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r3_orders_2 X1 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k12_lattice3 X1 X2 X3) -> False) -> (r1_orders_2 X1 (esk37_4 X1 X2 X3 X4) X2 -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X4 X3 -> r1_orders_2 X1 X4 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k12_lattice3 X1 X2 X3) -> False) -> (r1_orders_2 X1 (esk37_4 X1 X2 X3 X4) X3 -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X4 X3 -> r1_orders_2 X1 X4 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (X4 = (k13_lattice3 X1 X2 X3) -> False) -> (r1_orders_2 X1 X2 (esk36_4 X1 X2 X3 X4) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X4 -> r1_orders_2 X1 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (X4 = (k13_lattice3 X1 X3 X2) -> False) -> (r1_orders_2 X1 X2 (esk36_4 X1 X3 X2 X4) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X4 -> r1_orders_2 X1 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (X4 = (k13_lattice3 X1 X2 X3) -> False) -> (m1_subset_1 (esk36_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X4 -> r1_orders_2 X1 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k12_lattice3 X1 X2 X3) -> False) -> (m1_subset_1 (esk37_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X4 X3 -> r1_orders_2 X1 X4 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_yellow11 X1 -> False) -> (v2_struct_0 X1 -> False) -> (k10_lattice3 X1 (esk10_1 X1) (k11_lattice3 X1 (esk11_1 X1) (esk12_1 X1))) = (k11_lattice3 X1 (k10_lattice3 X1 (esk10_1 X1) (esk11_1 X1)) (esk12_1 X1)) -> l1_orders_2 X1 -> False)
  -> (forall X2 X4 X5 X3 X1, (r1_orders_2 X1 (k12_lattice3 X1 X2 X3) (k12_lattice3 X1 X4 X5) -> False) -> v4_orders_2 X1 -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X5 -> r1_orders_2 X1 X2 X4 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X4 X3 X1, ((k10_lattice3 X1 X2 (k11_lattice3 X1 X3 X4)) = (k11_lattice3 X1 (k10_lattice3 X1 X2 X3) X4) -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v1_yellow11 X1 -> r1_orders_2 X1 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r1_orders_2 X1 (k13_lattice3 X1 X2 X4) (k13_lattice3 X1 X3 X4) -> False) -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (r3_orders_2 X1 (k13_lattice3 X1 X2 X3) X4 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r3_orders_2 X1 X3 X4 -> r3_orders_2 X1 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X5 X1 X2, (r1_orders_2 X2 X1 X5 -> False) -> X5 = (k12_lattice3 X2 X3 X4) -> v5_orders_2 X2 -> v2_lattice3 X2 -> l1_orders_2 X2 -> r1_orders_2 X2 X1 X4 -> r1_orders_2 X2 X1 X3 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X4 X1 X5 X2, (r1_orders_2 X2 X5 X1 -> False) -> X5 = (k13_lattice3 X2 X3 X4) -> v5_orders_2 X2 -> v1_lattice3 X2 -> l1_orders_2 X2 -> r1_orders_2 X2 X4 X1 -> r1_orders_2 X2 X3 X1 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X2 X3 X4 X1, ((k10_lattice3 X1 (k10_lattice3 X1 X2 X3) X4) = (k10_lattice3 X1 X2 (k10_lattice3 X1 X3 X4)) -> False) -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, ((k11_lattice3 X1 (k11_lattice3 X1 X2 X3) X4) = (k11_lattice3 X1 X2 (k11_lattice3 X1 X3 X4)) -> False) -> v4_orders_2 X1 -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X2 X1, (r1_orders_2 X1 X2 X4 -> False) -> v4_orders_2 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X4 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k13_lattice3 X1 (k12_lattice3 X1 X2 X3) X3) = X3 -> False) -> v3_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k12_lattice3 X1 X2 (k13_lattice3 X1 X2 X3)) = X2 -> False) -> v3_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r1_orders_2 X1 X2 X3 -> False) -> X2 = (k12_lattice3 X1 X3 X4) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r1_orders_2 X1 X2 X3 -> False) -> X2 = (k12_lattice3 X1 X4 X3) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r1_orders_2 X1 X2 X3 -> False) -> X3 = (k13_lattice3 X1 X2 X4) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r1_orders_2 X1 X2 X3 -> False) -> X3 = (k13_lattice3 X1 X4 X2) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> v5_orders_2 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X2 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k13_lattice3 X1 X2 X3) = X2 -> False) -> (k12_lattice3 X1 X2 X3) = X3 -> v3_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k12_lattice3 X1 X2 X3) = X3 -> False) -> (k13_lattice3 X1 X2 X3) = X2 -> v3_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k13_lattice3 X1 X2 X3) = X3 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> r3_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k12_lattice3 X1 X2 X3) = X3 -> False) -> v3_orders_2 X1 -> v4_orders_2 X1 -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> r3_orders_2 X1 X3 X2 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_orders_2 X1 X2 X3 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X2 X3 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> r3_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k13_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k12_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k10_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k11_lattice3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k10_lattice3 X1 X2 X3) = (k13_lattice3 X1 X2 X3) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k11_lattice3 X1 X2 X3) = (k12_lattice3 X1 X2 X3) -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k13_lattice3 X1 X2 X3) = (k13_lattice3 X1 X3 X2) -> False) -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k12_lattice3 X1 X2 X3) = (k12_lattice3 X1 X3 X2) -> False) -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_orders_2 X1 X2 X2 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk18_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> l1_orders_2 X1 -> r1_orders_2 X1 (esk7_1 X1) (esk9_1 X1) -> False)
  -> (forall X2 X1, ((k13_lattice3 X1 X2 X2) = X2 -> False) -> v3_orders_2 X1 -> v5_orders_2 X1 -> v1_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k12_lattice3 X1 X2 X2) = X2 -> False) -> v3_orders_2 X1 -> v5_orders_2 X1 -> v2_lattice3 X1 -> l1_orders_2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_yellow11 X1 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 (esk10_1 X1) (esk12_1 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (v6_orders_2 X2 X1 -> False) -> l1_orders_2 X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (v5_orders_2 X1 -> False) -> (r1_orders_2 X1 (esk14_1 X1) (esk13_1 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v5_orders_2 X1 -> False) -> (r1_orders_2 X1 (esk13_1 X1) (esk14_1 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> (r1_orders_2 X1 (esk8_1 X1) (esk9_1 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> (r1_orders_2 X1 (esk7_1 X1) (esk8_1 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (((k13_lattice3 esk1_0 esk4_0 esk5_0) = esk6_0 -> False) -> v1_yellow11 esk1_0 -> False)
  -> (((k13_lattice3 esk1_0 esk3_0 esk4_0) = esk6_0 -> False) -> v1_yellow11 esk1_0 -> False)
  -> (((k12_lattice3 esk1_0 esk5_0 esk6_0) = esk5_0 -> False) -> v1_yellow11 esk1_0 -> False)
  -> (((k12_lattice3 esk1_0 esk4_0 esk6_0) = esk4_0 -> False) -> v1_yellow11 esk1_0 -> False)
  -> (((k12_lattice3 esk1_0 esk4_0 esk5_0) = esk2_0 -> False) -> v1_yellow11 esk1_0 -> False)
  -> (((k12_lattice3 esk1_0 esk3_0 esk5_0) = esk3_0 -> False) -> v1_yellow11 esk1_0 -> False)
  -> (((k12_lattice3 esk1_0 esk3_0 esk4_0) = esk2_0 -> False) -> v1_yellow11 esk1_0 -> False)
  -> (((k12_lattice3 esk1_0 esk2_0 esk4_0) = esk2_0 -> False) -> v1_yellow11 esk1_0 -> False)
  -> (((k12_lattice3 esk1_0 esk2_0 esk3_0) = esk2_0 -> False) -> v1_yellow11 esk1_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v1_yellow11 X1 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_yellow11 X1 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_yellow11 X1 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v3_lattice3 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v5_orders_2 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v5_orders_2 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v5_orders_2 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk23_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v6_orders_2 (esk28_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v3_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v1_yellow_0 X1 -> v2_yellow_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v5_orders_2 X1 -> False) -> (esk14_1 X1) = (esk13_1 X1) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v2_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v1_lattice3 X1 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v3_lattice3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk22_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, v2_lattice3 X1 -> l1_orders_2 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, v1_lattice3 X1 -> l1_orders_2 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk35_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk34_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_1 X1) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk1_0) -> False) -> v1_yellow11 esk1_0 -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> v1_yellow11 esk1_0 -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> v1_yellow11 esk1_0 -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> v1_yellow11 esk1_0 -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> v1_yellow11 esk1_0 -> False)
  -> (forall X1, (v2_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v3_yellow_0 X1 -> False)
  -> (forall X1, (v1_yellow_0 X1 -> False) -> l1_orders_2 X1 -> v3_yellow_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v2_orders_2 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (esk6_0 = esk5_0 -> v1_yellow11 esk1_0 -> False)
  -> (esk6_0 = esk4_0 -> v1_yellow11 esk1_0 -> False)
  -> (esk6_0 = esk3_0 -> v1_yellow11 esk1_0 -> False)
  -> (esk6_0 = esk2_0 -> v1_yellow11 esk1_0 -> False)
  -> (esk5_0 = esk4_0 -> v1_yellow11 esk1_0 -> False)
  -> (esk5_0 = esk3_0 -> v1_yellow11 esk1_0 -> False)
  -> (esk5_0 = esk2_0 -> v1_yellow11 esk1_0 -> False)
  -> (esk4_0 = esk3_0 -> v1_yellow11 esk1_0 -> False)
  -> (esk4_0 = esk2_0 -> v1_yellow11 esk1_0 -> False)
  -> (esk3_0 = esk2_0 -> v1_yellow11 esk1_0 -> False)
  -> (forall X1, v1_subset_1 (esk29_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk27_0 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk25_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v7_ordinal1 esk33_0 -> False) -> False)
  -> ((v7_ordinal1 esk30_0 -> False) -> False)
  -> ((v3_lattice3 esk27_0 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk24_0 -> False) -> False)
  -> ((v1_ordinal1 esk24_0 -> False) -> False)
  -> ((v3_ordinal1 esk24_0 -> False) -> False)
  -> ((v3_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v2_orders_2 esk27_0 -> False) -> False)
  -> ((l1_struct_0 esk16_0 -> False) -> False)
  -> ((l1_orders_2 esk27_0 -> False) -> False)
  -> ((l1_orders_2 esk15_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> ((v2_lattice3 esk1_0 -> False) -> False)
  -> ((v1_lattice3 esk1_0 -> False) -> False)
  -> ((v5_orders_2 esk27_0 -> False) -> False)
  -> ((v5_orders_2 esk1_0 -> False) -> False)
  -> ((v4_orders_2 esk27_0 -> False) -> False)
  -> ((v4_orders_2 esk1_0 -> False) -> False)
  -> ((v3_orders_2 esk27_0 -> False) -> False)
  -> ((v3_orders_2 esk1_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
