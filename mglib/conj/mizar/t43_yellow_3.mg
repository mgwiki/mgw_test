(** $I sig/MizarPreamble.mgs **)

Theorem t43_yellow_3:
 forall v1_orders_2:set -> prop,
 forall u1_orders_2:set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk8_3:set -> set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall np__1:set,
 forall g1_orders_2:set -> set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v2_waybel_0:set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk29_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk17_1:set -> set,
 forall k1_xboole_0:set,
 forall esk32_1:set -> set,
 forall esk30_1:set -> set,
 forall v1_yellow_3:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk1_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk27_1:set -> set,
 forall esk14_0:set,
 forall esk15_2:set -> set -> set,
 forall esk26_2:set -> set -> set,
 forall esk23_1:set -> set,
 forall esk19_0:set,
 forall esk11_0:set,
 forall esk13_0:set,
 forall esk10_0:set,
 forall esk18_0:set,
 forall esk28_0:set,
 forall esk22_0:set,
 forall esk12_1:set -> set,
 forall v1_xtuple_0:set -> prop,
 forall esk24_0:set,
 forall v3_relat_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk16_1:set -> set,
 forall esk31_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk25_1:set -> set,
 forall esk20_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk21_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall v1_waybel_0:set -> set -> prop,
 forall v6_orders_2:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk33_3:set -> set -> set -> set,
 forall k1_yellow_0:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk5_4:set -> set -> set -> set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k1_yellow_3:set -> set -> set,
 forall k2_yellow_3:set -> set -> set -> set -> set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k6_yellow_3:set -> set -> set -> set -> set,
 forall v5_orders_2:set -> prop,
 forall l1_orders_2:set -> prop,
 forall r1_yellow_0:set -> set -> prop,
 forall r2_lattice3:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k3_yellow_3:set -> set -> set,
 forall k7_yellow_3:set -> set -> set -> set -> set,
 forall esk34_6:set -> set -> set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall r1_orders_2:set -> set -> set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X2 X7 X6 X3 X1 X4 X5, (v2_struct_0 X5 -> False) -> (v2_struct_0 X2 -> False) -> (r1_orders_2 X2 X4 X1 -> False) -> v5_orders_2 X5 -> v5_orders_2 X2 -> l1_orders_2 X5 -> l1_orders_2 X2 -> r1_yellow_0 X5 X7 -> r1_yellow_0 X2 X3 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X6 (u1_struct_0 X5) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X5)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r1_orders_2 (k3_yellow_3 X2 X5) (k7_yellow_3 X2 X5 X4 X6) (esk34_6 X2 X5 X3 X7 X4 X6) -> False)
  -> (forall X2 X7 X6 X3 X1 X4 X5, (v2_struct_0 X5 -> False) -> (v2_struct_0 X2 -> False) -> (r1_orders_2 X2 X4 X1 -> False) -> v5_orders_2 X5 -> v5_orders_2 X2 -> l1_orders_2 X5 -> l1_orders_2 X2 -> r1_yellow_0 X5 X7 -> r1_yellow_0 X2 X3 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X6 (u1_struct_0 X5) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X5)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r1_orders_2 (k3_yellow_3 X5 X2) (k7_yellow_3 X5 X2 X6 X4) (esk34_6 X5 X2 X7 X3 X6 X4) -> False)
  -> (forall X2 X7 X3 X6 X1 X4 X5, (v2_struct_0 X5 -> False) -> (v2_struct_0 X2 -> False) -> (r1_orders_2 X2 X4 X1 -> False) -> (r2_lattice3 (k3_yellow_3 X2 X5) (k6_yellow_3 X2 X5 X3 X6) (esk34_6 X2 X5 X3 X6 X4 X7) -> False) -> v5_orders_2 X5 -> v5_orders_2 X2 -> l1_orders_2 X5 -> l1_orders_2 X2 -> r1_yellow_0 X5 X6 -> r1_yellow_0 X2 X3 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X7 (u1_struct_0 X5) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X5)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X7 X6 X3 X1 X4 X5, (v2_struct_0 X5 -> False) -> (v2_struct_0 X2 -> False) -> (r1_orders_2 X2 X4 X1 -> False) -> (r2_lattice3 (k3_yellow_3 X5 X2) (k6_yellow_3 X5 X2 X6 X3) (esk34_6 X5 X2 X6 X3 X7 X4) -> False) -> v5_orders_2 X5 -> v5_orders_2 X2 -> l1_orders_2 X5 -> l1_orders_2 X2 -> r1_yellow_0 X5 X6 -> r1_yellow_0 X2 X3 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X7 (u1_struct_0 X5) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X5)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X4 X5 X6 X1 X2 X3, (m1_subset_1 (k2_yellow_3 X2 X3 X5 X6 X1 X4) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X5) (k2_zfmisc_1 X3 X6))) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X6 X7 X3 X1 X4 X5, (v2_struct_0 X5 -> False) -> (v2_struct_0 X2 -> False) -> (r1_orders_2 X2 X4 X1 -> False) -> (m1_subset_1 (esk34_6 X2 X5 X3 X6 X4 X7) (u1_struct_0 (k3_yellow_3 X2 X5)) -> False) -> v5_orders_2 X5 -> v5_orders_2 X2 -> l1_orders_2 X5 -> l1_orders_2 X2 -> r1_yellow_0 X5 X6 -> r1_yellow_0 X2 X3 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X7 (u1_struct_0 X5) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X5)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X7 X6 X1 X4 X5, (v2_struct_0 X5 -> False) -> (v2_struct_0 X2 -> False) -> (r1_orders_2 X2 X4 X1 -> False) -> (m1_subset_1 (esk34_6 X5 X2 X6 X3 X7 X4) (u1_struct_0 (k3_yellow_3 X5 X2)) -> False) -> v5_orders_2 X5 -> v5_orders_2 X2 -> l1_orders_2 X5 -> l1_orders_2 X2 -> r1_yellow_0 X5 X6 -> r1_yellow_0 X2 X3 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X7 (u1_struct_0 X5) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X5)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2 X3, (X1 = (k3_yellow_3 X2 X3) -> False) -> (u1_struct_0 X1) = (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X3)) -> (u1_orders_2 X1) = (k2_yellow_3 (u1_struct_0 X2) (u1_struct_0 X2) (u1_struct_0 X3) (u1_struct_0 X3) (u1_orders_2 X2) (u1_orders_2 X3)) -> l1_orders_2 X3 -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X4 X5 X6 X1 X2 X3, ((k2_yellow_3 X2 X3 X5 X6 X1 X4) = (k1_yellow_3 X1 X4) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, ((u1_orders_2 X1) = (k2_yellow_3 (u1_struct_0 X2) (u1_struct_0 X2) (u1_struct_0 X3) (u1_struct_0 X3) (u1_orders_2 X2) (u1_orders_2 X3)) -> False) -> X1 = (k3_yellow_3 X2 X3) -> l1_orders_2 X3 -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X3 X2 X4 X1, ((k2_tarski (k2_tarski (esk5_4 X2 X3 X4 X1) (esk6_4 X2 X3 X4 X1)) (k1_tarski (esk5_4 X2 X3 X4 X1))) = X1 -> False) -> X4 = (k2_zfmisc_1 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X1 X2 X6 X3 X5 X4, (v2_struct_0 X4 -> False) -> (v2_struct_0 X1 -> False) -> (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_lattice3 X1 X2 X3 -> False) -> l1_orders_2 X4 -> l1_orders_2 X1 -> m1_subset_1 X6 (u1_struct_0 X4) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r2_lattice3 (k3_yellow_3 X1 X4) (k6_yellow_3 X1 X4 X2 X5) (k7_yellow_3 X1 X4 X3 X6) -> False)
  -> (forall X1 X2 X6 X3 X5 X4, (v2_struct_0 X4 -> False) -> (v2_struct_0 X1 -> False) -> (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_lattice3 X1 X2 X3 -> False) -> l1_orders_2 X4 -> l1_orders_2 X1 -> m1_subset_1 X6 (u1_struct_0 X4) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r2_lattice3 (k3_yellow_3 X4 X1) (k6_yellow_3 X4 X1 X5 X2) (k7_yellow_3 X4 X1 X6 X3) -> False)
  -> (forall X1 X2 X4 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X1 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_yellow_0 X1 X2 -> False) -> v5_orders_2 X3 -> v5_orders_2 X1 -> l1_orders_2 X3 -> l1_orders_2 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X3)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r1_yellow_0 (k3_yellow_3 X1 X3) (k6_yellow_3 X1 X3 X2 X4) -> False)
  -> (forall X1 X2 X4 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X1 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_yellow_0 X1 X2 -> False) -> v5_orders_2 X3 -> v5_orders_2 X1 -> l1_orders_2 X3 -> l1_orders_2 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X3)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r1_yellow_0 (k3_yellow_3 X3 X1) (k6_yellow_3 X3 X1 X4 X2) -> False)
  -> (forall X3 X2 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> ((k2_tarski (k2_tarski (esk8_3 X1 X2 X3) (esk9_3 X1 X2 X3)) (k1_tarski (esk8_3 X1 X2 X3))) = (esk7_3 X1 X2 X3) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X1 X4 X3 X2, (m1_subset_1 (k6_yellow_3 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 (k3_yellow_3 X1 X2))) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X4 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X1 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_yellow_0 (k3_yellow_3 X1 X3) (k6_yellow_3 X1 X3 X2 X4) -> False) -> v5_orders_2 X3 -> v5_orders_2 X1 -> l1_orders_2 X3 -> l1_orders_2 X1 -> r1_yellow_0 X3 X4 -> r1_yellow_0 X1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X3)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (k7_yellow_3 X1 X2 X3 X4) (u1_struct_0 (k3_yellow_3 X1 X2)) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk6_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk5_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X5 X4 X1 X2 X3, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (esk7_3 X1 X2 X3) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden (esk7_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X1 X2, (X1 = (k1_yellow_0 X2 X3) -> False) -> v5_orders_2 X2 -> l1_orders_2 X2 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_orders_2 X2 X1 (esk33_3 X2 X1 X3) -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> v5_orders_2 X1 -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> r1_orders_2 X1 X3 (esk33_3 X1 X3 X2) -> False)
  -> (forall X1 X4 X3 X2, ((k7_yellow_3 X1 X2 X3 X4) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X1 X4 X3 X2, ((k6_yellow_3 X1 X2 X3 X4) = (k2_zfmisc_1 X3 X4) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (X1 = (k1_yellow_0 X2 X3) -> False) -> (r2_lattice3 X2 X3 (esk33_3 X2 X1 X3) -> False) -> v5_orders_2 X2 -> l1_orders_2 X2 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (r2_lattice3 X1 X2 (esk33_3 X1 X3 X2) -> False) -> v5_orders_2 X1 -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (X1 = (k1_yellow_0 X2 X3) -> False) -> (m1_subset_1 (esk33_3 X2 X1 X3) (u1_struct_0 X2) -> False) -> v5_orders_2 X2 -> l1_orders_2 X2 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X1 X2, (r1_yellow_0 X1 X2 -> False) -> (m1_subset_1 (esk33_3 X1 X3 X2) (u1_struct_0 X1) -> False) -> v5_orders_2 X1 -> l1_orders_2 X1 -> r2_lattice3 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X4 X2, (r1_orders_2 X2 X4 X1 -> False) -> X4 = (k1_yellow_0 X2 X3) -> v5_orders_2 X2 -> l1_orders_2 X2 -> r1_yellow_0 X2 X3 -> r2_lattice3 X2 X3 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X2, (v13_struct_0 (g1_orders_2 (k1_tarski X1) X2) np__1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X1))) -> False)
  -> (forall X1 X2, (v1_orders_2 (g1_orders_2 (k1_tarski X1) X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X1))) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v2_struct_0 (g1_orders_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X1 X3) = (g1_orders_2 X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X3 X1) = (g1_orders_2 X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k2_zfmisc_1 X2 X4) -> X5 = (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X3 X1, (r2_lattice3 X1 X2 X3 -> False) -> X3 = (k1_yellow_0 X1 X2) -> v5_orders_2 X1 -> l1_orders_2 X1 -> r1_yellow_0 X1 X2 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X1 X2, (v1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (l1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1, (m1_subset_1 (u1_orders_2 X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, ((u1_struct_0 X1) = (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X3)) -> False) -> X1 = (k3_yellow_3 X2 X3) -> l1_orders_2 X3 -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X2 X1, (v6_orders_2 X2 X1 -> False) -> l1_orders_2 X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v2_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v1_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v2_struct_0 (k3_yellow_3 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_orders_2 (k3_yellow_3 X1 X2) -> False) -> v5_orders_2 X2 -> v5_orders_2 X1 -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X1 X2, (v5_orders_2 (k3_yellow_3 X1 X2) -> False) -> v5_orders_2 X2 -> v5_orders_2 X1 -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_orders_2 (k3_yellow_3 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_yellow_0 X1 X2) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_yellow_3 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_orders_2 (k3_yellow_3 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (l1_orders_2 (k3_yellow_3 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_orders_2 (u1_struct_0 X1) (u1_orders_2 X1)) = X1 -> False) -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_yellow_3 X1 -> False) -> l1_orders_2 X1 -> v1_xboole_0 (u1_orders_2 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk21_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v6_orders_2 (esk25_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_waybel_0 (esk17_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_waybel_0 (esk17_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk20_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk32_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_yellow_3 X1 -> False) -> v2_struct_0 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_yellow_3 X1 -> False) -> v2_struct_0 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk31_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k7_yellow_3 esk1_0 esk2_0 (k1_yellow_0 esk1_0 esk3_0) (k1_yellow_0 esk2_0 esk4_0)) = (k1_yellow_0 (k3_yellow_3 esk1_0 esk2_0) (k6_yellow_3 esk1_0 esk2_0 esk3_0 esk4_0)) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk27_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk4_0 -> False)
  -> (v1_xboole_0 esk3_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk2_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk15_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk26_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk15_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk26_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk26_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((r1_yellow_0 esk2_0 esk4_0 -> False) -> False)
  -> ((r1_yellow_0 esk1_0 esk3_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk23_1 X1) -> False) -> False)
  -> ((v1_xtuple_0 esk19_0 -> False) -> False)
  -> ((v2_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((l1_struct_0 esk11_0 -> False) -> False)
  -> ((v1_orders_2 esk28_0 -> False) -> False)
  -> ((v1_orders_2 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_orders_2 esk28_0 -> False) -> False)
  -> ((l1_orders_2 esk13_0 -> False) -> False)
  -> ((l1_orders_2 esk10_0 -> False) -> False)
  -> ((l1_orders_2 esk2_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> ((v5_orders_2 esk2_0 -> False) -> False)
  -> ((v5_orders_2 esk1_0 -> False) -> False)
  -> ((v2_struct_0 esk28_0 -> False) -> False)
  -> False.
Admitted.
