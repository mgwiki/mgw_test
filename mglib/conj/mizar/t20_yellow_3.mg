(** $I sig/MizarPreamble.mgs **)

Theorem t20_yellow_3:
 forall v2_struct_0:set -> prop,
 forall r1_orders_2:set -> set -> set -> prop,
 forall k3_yellow_3:set -> set -> set,
 forall k7_yellow_3:set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall l1_orders_2:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k6_yellow_3:set -> set -> set -> set -> set,
 forall k9_yellow_3:set -> set -> set -> set,
 forall np__1:set,
 forall g1_orders_2:set -> set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall k2_xtuple_0:set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall esk16_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v2_waybel_0:set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk25_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk24_1:set -> set,
 forall esk29_1:set -> set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk35_1:set -> set,
 forall esk20_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk28_0:set,
 forall esk19_2:set -> set -> set,
 forall esk30_2:set -> set -> set,
 forall esk27_1:set -> set,
 forall esk23_0:set,
 forall esk14_0:set,
 forall esk17_0:set,
 forall esk13_0:set,
 forall esk22_0:set,
 forall esk32_0:set,
 forall esk26_0:set,
 forall esk15_1:set -> set,
 forall esk18_0:set,
 forall esk31_1:set -> set,
 forall v3_relat_1:set -> prop,
 forall esk34_1:set -> set,
 forall esk36_1:set -> set,
 forall k1_xboole_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall esk21_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk33_1:set -> set,
 forall v6_orders_2:set -> set -> prop,
 forall v1_xtuple_0:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall u1_orders_2:set -> set,
 forall o_2_0_yellow_3:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall k1_xtuple_0:set -> set,
 forall v1_orders_2:set -> prop,
 forall k8_yellow_3:set -> set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall v1_waybel_0:set -> set -> prop,
 forall esk5_4:set -> set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk8_4:set -> set -> set -> set -> set,
 forall esk9_4:set -> set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X3 X2 X4 X1, ((k2_tarski (k2_tarski (esk8_4 X2 X3 X4 X1) (esk9_4 X2 X3 X4 X1)) (k1_tarski (esk8_4 X2 X3 X4 X1))) = X1 -> False) -> X4 = (k2_zfmisc_1 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X1 X6 X5 X3 X2 X4, (v2_struct_0 X4 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X2 X3 -> False) -> l1_orders_2 X4 -> l1_orders_2 X1 -> m1_subset_1 X6 (u1_struct_0 X4) -> m1_subset_1 X5 (u1_struct_0 X4) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_orders_2 (k3_yellow_3 X1 X4) (k7_yellow_3 X1 X4 X2 X5) (k7_yellow_3 X1 X4 X3 X6) -> False)
  -> (forall X1 X6 X5 X3 X2 X4, (v2_struct_0 X4 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X2 X3 -> False) -> l1_orders_2 X4 -> l1_orders_2 X1 -> m1_subset_1 X6 (u1_struct_0 X4) -> m1_subset_1 X5 (u1_struct_0 X4) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_orders_2 (k3_yellow_3 X4 X1) (k7_yellow_3 X4 X1 X5 X2) (k7_yellow_3 X4 X1 X6 X3) -> False)
  -> (forall X1 X2 X3 X6 X5 X4, (v2_struct_0 X4 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 (k3_yellow_3 X1 X4) (k7_yellow_3 X1 X4 X2 X5) (k7_yellow_3 X1 X4 X3 X6) -> False) -> l1_orders_2 X4 -> l1_orders_2 X1 -> r1_orders_2 X4 X5 X6 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X6 (u1_struct_0 X4) -> m1_subset_1 X5 (u1_struct_0 X4) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> ((k2_tarski (k2_tarski (esk11_3 X1 X2 X3) (esk12_3 X1 X2 X3)) (k1_tarski (esk11_3 X1 X2 X3))) = (esk10_3 X1 X2 X3) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X1 X4 X3 X2, (m1_subset_1 (k6_yellow_3 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 (k3_yellow_3 X1 X2))) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X4 X1, (r1_orders_2 X1 X2 (esk5_4 X1 X3 X2 X4) -> False) -> l1_orders_2 X1 -> v1_waybel_0 X3 X1 -> r2_hidden X4 X3 -> r2_hidden X2 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X4 X1, (r1_orders_2 X1 X2 (esk5_4 X1 X3 X4 X2) -> False) -> l1_orders_2 X1 -> v1_waybel_0 X3 X1 -> r2_hidden X4 X3 -> r2_hidden X2 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X4 X1, (m1_subset_1 (esk5_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> v1_waybel_0 X2 X1 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X4 X1, (r2_hidden (esk5_4 X1 X2 X3 X4) X2 -> False) -> l1_orders_2 X1 -> v1_waybel_0 X2 X1 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (k7_yellow_3 X1 X2 X3 X4) (u1_struct_0 (k3_yellow_3 X1 X2)) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk9_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk8_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X5 X4 X1 X2 X3, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (esk10_3 X1 X2 X3) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden (esk10_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X3 X2, (v1_waybel_0 X3 X2 -> False) -> l1_orders_2 X2 -> r2_hidden X1 X3 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r1_orders_2 X2 (esk6_2 X2 X3) X1 -> r1_orders_2 X2 (esk7_2 X2 X3) X1 -> False)
  -> (forall X1 X4 X3 X2, ((k7_yellow_3 X1 X2 X3 X4) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X1 X4 X3 X2, ((k6_yellow_3 X1 X2 X3 X4) = (k2_zfmisc_1 X3 X4) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (k9_yellow_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X1 X2)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (k8_yellow_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X1 X2)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X2, (v13_struct_0 (g1_orders_2 (k1_tarski X1) X2) np__1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X1))) -> False)
  -> (forall X1 X2, (v1_orders_2 (g1_orders_2 (k1_tarski X1) X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X1))) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X1 X3 X2, ((k9_yellow_3 X1 X2 X3) = (k2_xtuple_0 X3) -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X1 X2)) -> False)
  -> (forall X1 X3 X2, ((k8_yellow_3 X1 X2 X3) = (k1_xtuple_0 X3) -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X1 X2)) -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v2_struct_0 (g1_orders_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X1 X3) = (g1_orders_2 X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X3 X1) = (g1_orders_2 X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k2_zfmisc_1 X2 X4) -> X5 = (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 (o_2_0_yellow_3 X1 X2) (u1_struct_0 X1) X2 -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (v1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (l1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (u1_orders_2 X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk16_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_waybel_0 X2 X1 -> False) -> (m1_subset_1 (esk7_2 X1 X2) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_waybel_0 X2 X1 -> False) -> (m1_subset_1 (esk6_2 X1 X2) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_waybel_0 X2 X1 -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_waybel_0 X2 X1 -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (k1_xtuple_0 X1) (k2_xtuple_0 X1)) (k1_tarski (k1_xtuple_0 X1))) = X1 -> False) -> v1_xtuple_0 X1 -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (k1_xtuple_0 X1) (k2_xtuple_0 X1)) (k1_tarski (k1_xtuple_0 X1))) = X1 -> False) -> v1_xtuple_0 X1 -> False)
  -> (forall X3 X1 X2, (r2_hidden (k2_xtuple_0 X1) X2 -> False) -> r2_hidden X1 (k2_zfmisc_1 X3 X2) -> False)
  -> (forall X3 X1 X2, (r2_hidden (k1_xtuple_0 X1) X2 -> False) -> r2_hidden X1 (k2_zfmisc_1 X2 X3) -> False)
  -> (forall X2 X1, (v6_orders_2 X2 X1 -> False) -> l1_orders_2 X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v2_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v1_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v2_struct_0 (k3_yellow_3 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_orders_2 (k3_yellow_3 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
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
  -> (v1_waybel_0 esk3_0 esk1_0 -> v1_waybel_0 esk4_0 esk2_0 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk25_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk33_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v6_orders_2 (esk29_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_waybel_0 (esk21_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_waybel_0 (esk21_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk24_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk36_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk35_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk31_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk4_0 -> False)
  -> (v1_xboole_0 esk3_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk2_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> ((v1_waybel_0 (k6_yellow_3 esk1_0 esk2_0 esk3_0 esk4_0) (k3_yellow_3 esk1_0 esk2_0) -> False) -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, ((k2_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X2 -> False) -> False)
  -> (forall X1 X2, ((k1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X1 -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk30_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk30_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk30_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk27_1 X1) -> False) -> False)
  -> ((v1_xtuple_0 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((l1_struct_0 esk14_0 -> False) -> False)
  -> ((v1_orders_2 esk32_0 -> False) -> False)
  -> ((v1_orders_2 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_orders_2 esk32_0 -> False) -> False)
  -> ((l1_orders_2 esk17_0 -> False) -> False)
  -> ((l1_orders_2 esk13_0 -> False) -> False)
  -> ((l1_orders_2 esk2_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> ((v2_struct_0 esk32_0 -> False) -> False)
  -> False.
Admitted.
