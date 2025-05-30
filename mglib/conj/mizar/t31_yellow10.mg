(** $I sig/MizarPreamble.mgs **)

Theorem t31_yellow10:
 forall k3_yellow_3:set -> set -> set,
 forall l1_orders_2:set -> prop,
 forall v1_orders_2:set -> prop,
 forall u1_orders_2:set -> set,
 forall u1_struct_0:set -> set,
 forall v2_struct_0:set -> prop,
 forall r1_orders_2:set -> set -> set -> prop,
 forall k8_yellow_3:set -> set -> set -> set,
 forall k9_yellow_3:set -> set -> set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall esk17_3:set -> set -> set -> set,
 forall esk15_3:set -> set -> set -> set,
 forall esk10_4:set -> set -> set -> set -> set,
 forall k4_waybel_0:set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall k4_yellow_3:set -> set -> set -> set,
 forall np__1:set,
 forall g1_orders_2:set -> set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall k2_xtuple_0:set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v1_waybel_0:set -> set -> prop,
 forall esk33_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk35_1:set -> set,
 forall esk23_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk32_1:set -> set,
 forall esk22_0:set,
 forall esk21_1:set -> set,
 forall esk29_0:set,
 forall o_0_0_xboole_0:set,
 forall esk20_0:set,
 forall esk19_0:set,
 forall esk25_0:set,
 forall esk26_0:set,
 forall esk30_1:set -> set,
 forall esk31_0:set,
 forall v3_relat_1:set -> prop,
 forall v1_yellow_3:set -> prop,
 forall esk34_1:set -> set,
 forall esk36_1:set -> set,
 forall k1_xboole_0:set,
 forall esk24_1:set -> set,
 forall esk27_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk28_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk18_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v2_waybel_0:set -> set -> prop,
 forall v1_xtuple_0:set -> prop,
 forall k1_xtuple_0:set -> set,
 forall k5_yellow_3:set -> set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall k7_yellow_3:set -> set -> set -> set -> set,
 forall k6_yellow_3:set -> set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall k1_tarski:set -> set,
 forall esk13_4:set -> set -> set -> set -> set,
 forall esk14_4:set -> set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k1_yellow_3:set -> set -> set,
 forall k2_yellow_3:set -> set -> set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
     (forall X4 X5 X6 X1 X2 X3, (m1_subset_1 (k2_yellow_3 X2 X3 X5 X6 X1 X4) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X5) (k2_zfmisc_1 X3 X6))) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (X1 = (k3_yellow_3 X2 X3) -> False) -> (u1_struct_0 X1) = (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X3)) -> (u1_orders_2 X1) = (k2_yellow_3 (u1_struct_0 X2) (u1_struct_0 X2) (u1_struct_0 X3) (u1_struct_0 X3) (u1_orders_2 X2) (u1_orders_2 X3)) -> l1_orders_2 X3 -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X4 X5 X6 X1 X2 X3, ((k2_yellow_3 X2 X3 X5 X6 X1 X4) = (k1_yellow_3 X1 X4) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, ((u1_orders_2 X1) = (k2_yellow_3 (u1_struct_0 X2) (u1_struct_0 X2) (u1_struct_0 X3) (u1_struct_0 X3) (u1_orders_2 X2) (u1_orders_2 X3)) -> False) -> X1 = (k3_yellow_3 X2 X3) -> l1_orders_2 X3 -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X3 X2 X4 X1, ((k2_tarski (k2_tarski (esk13_4 X2 X3 X4 X1) (esk14_4 X2 X3 X4 X1)) (k1_tarski (esk13_4 X2 X3 X4 X1))) = X1 -> False) -> X4 = (k2_zfmisc_1 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X1 X3 X4 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 (k3_yellow_3 X1 X2) X3 X4 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 (k3_yellow_3 X1 X2)) -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X1 X2)) -> r1_orders_2 X2 (k9_yellow_3 X1 X2 X3) (k9_yellow_3 X1 X2 X4) -> r1_orders_2 X1 (k8_yellow_3 X1 X2 X3) (k8_yellow_3 X1 X2 X4) -> False)
  -> (forall X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski (esk7_3 X3 X2 X1) X1) (k1_tarski (esk7_3 X3 X2 X1))) X3 -> False) -> X2 = (k10_xtuple_0 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> ((k2_tarski (k2_tarski (esk16_3 X1 X2 X3) (esk17_3 X1 X2 X3)) (k1_tarski (esk16_3 X1 X2 X3))) = (esk15_3 X1 X2 X3) -> False) -> (r2_hidden (esk15_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X1 X4 X3 X2, (m1_subset_1 (k6_yellow_3 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 (k3_yellow_3 X1 X2))) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X1 X2 X3, (r1_orders_2 X1 (esk10_4 X1 X2 X3 X4) X4 -> False) -> X3 = (k4_waybel_0 X1 X2) -> l1_orders_2 X1 -> r2_hidden X4 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (esk10_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> X3 = (k4_waybel_0 X1 X2) -> l1_orders_2 X1 -> r2_hidden X4 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X1 X2 X3, (r2_hidden (esk10_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k4_waybel_0 X1 X2) -> l1_orders_2 X1 -> r2_hidden X4 X3 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (k7_yellow_3 X1 X2 X3 X4) (u1_struct_0 (k3_yellow_3 X1 X2)) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 (k9_yellow_3 X2 X1 X3) (k9_yellow_3 X2 X1 X4) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> r1_orders_2 (k3_yellow_3 X2 X1) X3 X4 -> m1_subset_1 X4 (u1_struct_0 (k3_yellow_3 X2 X1)) -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X2 X1)) -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 (k8_yellow_3 X1 X2 X3) (k8_yellow_3 X1 X2 X4) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> r1_orders_2 (k3_yellow_3 X1 X2) X3 X4 -> m1_subset_1 X4 (u1_struct_0 (k3_yellow_3 X1 X2)) -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X1 X2)) -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k4_waybel_0 X1 X2) -> False) -> l1_orders_2 X1 -> r2_hidden X4 X2 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r2_hidden (esk11_3 X1 X2 X3) X3 -> r1_orders_2 X1 X4 (esk11_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski X1 (esk4_3 X3 X2 X1)) (k1_tarski X1)) X3 -> False) -> X2 = (k9_xtuple_0 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, (X2 = (k9_xtuple_0 X1) -> False) -> r2_hidden (esk5_2 X1 X2) X2 -> r2_hidden (k2_tarski (k2_tarski (esk5_2 X1 X2) X3) (k1_tarski (esk5_2 X1 X2))) X1 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk14_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk13_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X3 X1, (X3 = (k4_waybel_0 X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X3 -> False) -> (r1_orders_2 X1 (esk12_3 X1 X2 X3) (esk11_3 X1 X2 X3) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk9_2 X1 X2) (esk8_2 X1 X2)) (k1_tarski (esk9_2 X1 X2))) X1 -> False) -> False)
  -> (forall X1 X2, (X2 = (k9_xtuple_0 X1) -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk5_2 X1 X2) (esk6_2 X1 X2)) (k1_tarski (esk5_2 X1 X2))) X1 -> False) -> False)
  -> (forall X5 X4 X1 X2 X3, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (esk15_3 X1 X2 X3) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden (esk15_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> r2_hidden (esk8_2 X1 X2) X2 -> r2_hidden (k2_tarski (k2_tarski X3 (esk8_2 X1 X2)) (k1_tarski X3)) X1 -> False)
  -> (forall X1 X4 X3 X2, ((k7_yellow_3 X1 X2 X3 X4) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X1 X4 X3 X2, ((k6_yellow_3 X1 X2 X3 X4) = (k2_zfmisc_1 X3 X4) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (X3 = (k4_waybel_0 X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X3 -> False) -> (m1_subset_1 (esk12_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (k5_yellow_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 (k3_yellow_3 X1 X2))) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (k4_yellow_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 (k3_yellow_3 X1 X2))) -> False)
  -> (forall X2 X3 X1, (X3 = (k4_waybel_0 X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X2 -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X1 X3 X5, (r2_hidden X3 X5 -> False) -> X5 = (k4_waybel_0 X2 X4) -> l1_orders_2 X2 -> r2_hidden X1 X4 -> r1_orders_2 X2 X1 X3 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((k5_yellow_3 X1 X2 X3) = (k10_xtuple_0 X3) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 (k3_yellow_3 X1 X2))) -> False)
  -> (forall X1 X3 X2, ((k4_yellow_3 X1 X2 X3) = (k9_xtuple_0 X3) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 (k3_yellow_3 X1 X2))) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (k9_yellow_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X1 X2)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (k8_yellow_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X1 X2)) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk15_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk17_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk15_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k4_waybel_0 X1 X2) -> False) -> (m1_subset_1 (esk11_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v13_struct_0 (g1_orders_2 (k1_tarski X1) X2) np__1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X1))) -> False)
  -> (forall X1 X2, (v1_orders_2 (g1_orders_2 (k1_tarski X1) X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X1))) -> False)
  -> (forall X1 X3 X2, ((k9_yellow_3 X1 X2 X3) = (k2_xtuple_0 X3) -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X1 X2)) -> False)
  -> (forall X1 X3 X2, ((k8_yellow_3 X1 X2 X3) = (k1_xtuple_0 X3) -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 (k3_yellow_3 X1 X2)) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k9_xtuple_0 X3) -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden X2 X4 -> False) -> X4 = (k10_xtuple_0 X3) -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False)
  -> (forall X5 X4 X2 X3 X1, (r2_hidden X1 (k2_zfmisc_1 X2 X3) -> False) -> X1 = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> r2_hidden (k1_xtuple_0 X1) X2 -> r2_hidden (k2_xtuple_0 X1) X3 -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X1 X3) = (g1_orders_2 X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X3 X1) = (g1_orders_2 X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k2_zfmisc_1 X2 X4) -> X5 = (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (l1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1, (m1_subset_1 (u1_orders_2 X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k4_waybel_0 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, ((k2_tarski (k2_tarski (k1_xtuple_0 X2) (k2_xtuple_0 X2)) (k1_tarski (k1_xtuple_0 X2))) = X2 -> False) -> v1_relat_1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v2_struct_0 (g1_orders_2 (u1_struct_0 X1) (u1_orders_2 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 (k4_waybel_0 X1 X2) -> False) -> l1_orders_2 X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (k1_xtuple_0 X1) (k2_xtuple_0 X1)) (k1_tarski (k1_xtuple_0 X1))) = X1 -> False) -> v1_xtuple_0 X1 -> False)
  -> (forall X1 X2 X3, ((u1_struct_0 X1) = (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X3)) -> False) -> X1 = (k3_yellow_3 X2 X3) -> l1_orders_2 X3 -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X1 X2, (v2_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v1_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk18_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v2_struct_0 (k3_yellow_3 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_orders_2 (g1_orders_2 (u1_struct_0 X1) (u1_orders_2 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk18_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_orders_2 (k3_yellow_3 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
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
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_yellow_3 X1 -> False) -> l1_orders_2 X1 -> v1_xboole_0 (u1_orders_2 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk28_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk33_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_waybel_0 (esk24_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_waybel_0 (esk24_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk27_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk36_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk35_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_yellow_3 X1 -> False) -> l1_orders_2 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_yellow_3 X1 -> False) -> l1_orders_2 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_tarski (k4_waybel_0 (k3_yellow_3 esk1_0 esk2_0) esk3_0) (k6_yellow_3 esk1_0 esk2_0 (k4_waybel_0 esk1_0 (k4_yellow_3 esk1_0 esk2_0 esk3_0)) (k4_waybel_0 esk2_0 (k5_yellow_3 esk1_0 esk2_0 esk3_0))) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk32_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 (k3_yellow_3 esk1_0 esk2_0))) -> False) -> False)
  -> (forall X2 X1, ((k2_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X2 -> False) -> False)
  -> (forall X1 X2, ((k1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X1 -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk30_1 X1) -> False) -> False)
  -> ((v1_xtuple_0 esk26_0 -> False) -> False)
  -> ((v2_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 esk25_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk20_0 -> False) -> False)
  -> ((l1_orders_2 esk19_0 -> False) -> False)
  -> ((l1_orders_2 esk2_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
