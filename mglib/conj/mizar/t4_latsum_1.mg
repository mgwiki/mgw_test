(** $I sig/MizarPreamble.mgs **)

Theorem t4_latsum_1:
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k3_relat_1:set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall r8_relat_2:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v2_waybel_0:set -> set -> prop,
 forall v4_orders_2:set -> prop,
 forall esk20_1:set -> set,
 forall k1_xboole_0:set,
 forall esk22_0:set,
 forall esk2_0:set,
 forall esk18_1:set -> set,
 forall esk21_0:set,
 forall esk16_0:set,
 forall esk17_0:set,
 forall esk19_2:set -> set -> set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall l1_struct_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v1_waybel_0:set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall g1_orders_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall esk15_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall r1_latsum_1:set -> set -> prop,
 forall esk10_3:set -> set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k4_tarski:set -> set -> set,
 forall esk9_5:set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall u1_orders_2:set -> set,
 forall k4_relset_1:set -> set -> set -> set -> set -> set -> set,
 forall v1_orders_2:set -> prop,
 forall l1_orders_2:set -> prop,
 forall k1_latsum_1:set -> set -> set,
     (forall X1 X2 X3, (X1 = (k1_latsum_1 X2 X3) -> False) -> (u1_struct_0 X1) = (k2_xboole_0 (u1_struct_0 X2) (u1_struct_0 X3)) -> (u1_orders_2 X1) = (k2_xboole_0 (k2_xboole_0 (u1_orders_2 X2) (u1_orders_2 X3)) (k4_relset_1 (u1_struct_0 X2) (u1_struct_0 X2) (u1_struct_0 X3) (u1_struct_0 X3) (u1_orders_2 X2) (u1_orders_2 X3))) -> l1_orders_2 X3 -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X4 X5 X6 X1 X2 X3, (m1_subset_1 (k4_relset_1 X2 X3 X5 X6 X1 X4) (k1_zfmisc_1 (k2_zfmisc_1 X2 X6)) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, ((u1_orders_2 X1) = (k2_xboole_0 (k2_xboole_0 (u1_orders_2 X2) (u1_orders_2 X3)) (k4_relset_1 (u1_struct_0 X2) (u1_struct_0 X2) (u1_struct_0 X3) (u1_struct_0 X3) (u1_orders_2 X2) (u1_orders_2 X3))) -> False) -> X1 = (k1_latsum_1 X2 X3) -> l1_orders_2 X3 -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X4 X5 X6 X1 X2 X3, ((k4_relset_1 X2 X3 X5 X6 X1 X4) = (k3_relat_1 X1 X4) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X5 X4 X3, (r2_hidden (k4_tarski (esk9_5 X1 X2 X3 X4 X5) X5) X2 -> False) -> X3 = (k3_relat_1 X1 X2) -> v1_relat_1 X3 -> r2_hidden (k4_tarski X4 X5) X3 -> False)
  -> (forall X3 X2 X5 X1 X4, (r2_hidden (k4_tarski X1 (esk9_5 X2 X3 X4 X1 X5)) X2 -> False) -> X4 = (k3_relat_1 X2 X3) -> v1_relat_1 X4 -> r2_hidden (k4_tarski X1 X5) X4 -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X3 -> r2_hidden (k4_tarski X4 (esk11_3 X1 X2 X3)) X2 -> r2_hidden (k4_tarski (esk10_3 X1 X2 X3) X4) X1 -> r2_hidden (k4_tarski (esk10_3 X1 X2 X3) (esk11_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k3_relat_1 X1 X2) -> False) -> (r2_hidden (k4_tarski (esk10_3 X1 X2 X3) (esk11_3 X1 X2 X3)) X3 -> False) -> (r2_hidden (k4_tarski (esk12_3 X1 X2 X3) (esk11_3 X1 X2 X3)) X2 -> False) -> v1_relat_1 X3 -> False)
  -> (forall X1 X2 X3, (X3 = (k3_relat_1 X1 X2) -> False) -> (r2_hidden (k4_tarski (esk10_3 X1 X2 X3) (esk11_3 X1 X2 X3)) X3 -> False) -> (r2_hidden (k4_tarski (esk10_3 X1 X2 X3) (esk12_3 X1 X2 X3)) X1 -> False) -> v1_relat_1 X3 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X2 -> r2_hidden (esk8_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X2, (r1_latsum_1 X1 X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> r2_hidden (k4_tarski (esk5_2 X1 X2) (esk6_2 X1 X2)) (u1_orders_2 X2) -> r2_hidden (k4_tarski (esk5_2 X1 X2) (esk6_2 X1 X2)) (u1_orders_2 X1) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden (k4_tarski X1 X2) (u1_orders_2 X4) -> False) -> l1_orders_2 X4 -> l1_orders_2 X3 -> r1_latsum_1 X3 X4 -> r2_hidden (k4_tarski X1 X2) (u1_orders_2 X3) -> r2_hidden X2 (k3_xboole_0 (u1_struct_0 X3) (u1_struct_0 X4)) -> r2_hidden X1 (k3_xboole_0 (u1_struct_0 X3) (u1_struct_0 X4)) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden (k4_tarski X1 X2) (u1_orders_2 X4) -> False) -> l1_orders_2 X4 -> l1_orders_2 X3 -> r1_latsum_1 X4 X3 -> r2_hidden (k4_tarski X1 X2) (u1_orders_2 X3) -> r2_hidden X2 (k3_xboole_0 (u1_struct_0 X4) (u1_struct_0 X3)) -> r2_hidden X1 (k3_xboole_0 (u1_struct_0 X4) (u1_struct_0 X3)) -> False)
  -> (forall X2 X1, (r1_latsum_1 X1 X2 -> False) -> (r2_hidden (k4_tarski (esk5_2 X1 X2) (esk6_2 X1 X2)) (u1_orders_2 X2) -> False) -> (r2_hidden (k4_tarski (esk5_2 X1 X2) (esk6_2 X1 X2)) (u1_orders_2 X1) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X4 X2 X5 X3 X1, (r2_hidden (k4_tarski X3 X5) X1 -> False) -> v1_relat_1 X1 -> r2_hidden X5 X2 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> r8_relat_2 X1 X2 -> r2_hidden (k4_tarski X4 X5) X1 -> r2_hidden (k4_tarski X3 X4) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k4_tarski (esk13_2 X1 X2) (esk15_2 X1 X2)) X1 -> False)
  -> (forall X5 X3 X2 X4 X1 X6, (r2_hidden (k4_tarski X1 X4) X6 -> False) -> X6 = (k3_relat_1 X3 X5) -> v1_relat_1 X6 -> r2_hidden (k4_tarski X2 X4) X5 -> r2_hidden (k4_tarski X1 X2) X3 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (k4_tarski (esk14_2 X1 X2) (esk15_2 X1 X2)) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (k4_tarski (esk13_2 X1 X2) (esk14_2 X1 X2)) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X1 X3) = (g1_orders_2 X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X3 X1) = (g1_orders_2 X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X2, (v1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (l1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1, (m1_subset_1 (u1_orders_2 X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (r1_latsum_1 X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) (k3_xboole_0 (u1_struct_0 X1) (u1_struct_0 X2)) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (r1_latsum_1 X1 X2 -> False) -> (r2_hidden (esk5_2 X1 X2) (k3_xboole_0 (u1_struct_0 X1) (u1_struct_0 X2)) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k4_tarski X1 X3) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k4_tarski X3 X1) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k4_tarski X1 X3) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2 X3, ((u1_struct_0 X1) = (k2_xboole_0 (u1_struct_0 X2) (u1_struct_0 X3)) -> False) -> X1 = (k1_latsum_1 X2 X3) -> l1_orders_2 X3 -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X1 X2, (v2_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v1_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (esk15_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (esk13_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v4_orders_2 X1 -> False) -> l1_orders_2 X1 -> r8_relat_2 (u1_orders_2 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_orders_2 (k1_latsum_1 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (l1_orders_2 (k1_latsum_1 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_orders_2 (u1_struct_0 X1) (u1_orders_2 X1)) = X1 -> False) -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (r8_relat_2 (u1_orders_2 X1) (u1_struct_0 X1) -> False) -> l1_orders_2 X1 -> v4_orders_2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_waybel_0 (esk20_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_waybel_0 (esk20_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_hidden (k4_tarski esk3_0 esk4_0) (u1_orders_2 esk1_0) -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((r2_hidden (k4_tarski esk3_0 esk4_0) (u1_orders_2 (k1_latsum_1 esk1_0 esk2_0)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) X1 -> False) -> False)
  -> ((r2_hidden esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((r2_hidden esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((r1_latsum_1 esk1_0 esk2_0 -> False) -> False)
  -> ((l1_struct_0 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v4_orders_2 esk1_0 -> False) -> False)
  -> ((l1_orders_2 esk16_0 -> False) -> False)
  -> ((l1_orders_2 esk2_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> False.
Admitted.
