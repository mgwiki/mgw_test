(** $I sig/MizarPreamble.mgs **)

Theorem t14_latsum_1:
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k3_relat_1:set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall g1_orders_2:set -> set -> set,
 forall esk5_0:set,
 forall v4_relat_1:set -> set -> prop,
 forall v1_waybel_0:set -> set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk19_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall esk16_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall esk17_0:set,
 forall esk13_0:set,
 forall v1_lattice3:set -> prop,
 forall v5_orders_2:set -> prop,
 forall esk12_0:set,
 forall esk14_1:set -> set,
 forall esk15_2:set -> set -> set,
 forall esk21_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v16_waybel_0:set -> prop,
 forall k1_xboole_0:set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk22_1:set -> set,
 forall esk20_1:set -> set,
 forall v2_waybel_0:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall r3_orders_2:set -> set -> set -> prop,
 forall v3_orders_2:set -> prop,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall v4_orders_2:set -> prop,
 forall r1_latsum_1:set -> set -> prop,
 forall r1_orders_2:set -> set -> set -> prop,
 forall v2_struct_0:set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k4_tarski:set -> set -> set,
 forall esk8_5:set -> set -> set -> set -> set -> set,
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
  -> (forall X2 X1 X5 X4 X3, (r2_hidden (k4_tarski (esk8_5 X1 X2 X3 X4 X5) X5) X2 -> False) -> X3 = (k3_relat_1 X1 X2) -> v1_relat_1 X3 -> r2_hidden (k4_tarski X4 X5) X3 -> False)
  -> (forall X3 X2 X5 X1 X4, (r2_hidden (k4_tarski X1 (esk8_5 X2 X3 X4 X1 X5)) X2 -> False) -> X4 = (k3_relat_1 X2 X3) -> v1_relat_1 X4 -> r2_hidden (k4_tarski X1 X5) X4 -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X3 -> r2_hidden (k4_tarski X4 (esk10_3 X1 X2 X3)) X2 -> r2_hidden (k4_tarski (esk9_3 X1 X2 X3) X4) X1 -> r2_hidden (k4_tarski (esk9_3 X1 X2 X3) (esk10_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k3_relat_1 X1 X2) -> False) -> (r2_hidden (k4_tarski (esk9_3 X1 X2 X3) (esk10_3 X1 X2 X3)) X3 -> False) -> (r2_hidden (k4_tarski (esk11_3 X1 X2 X3) (esk10_3 X1 X2 X3)) X2 -> False) -> v1_relat_1 X3 -> False)
  -> (forall X1 X2 X3, (X3 = (k3_relat_1 X1 X2) -> False) -> (r2_hidden (k4_tarski (esk9_3 X1 X2 X3) (esk10_3 X1 X2 X3)) X3 -> False) -> (r2_hidden (k4_tarski (esk9_3 X1 X2 X3) (esk11_3 X1 X2 X3)) X1 -> False) -> v1_relat_1 X3 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X2 -> r2_hidden (esk7_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X4 X3 X6 X5 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X5 X6 -> False) -> X4 = X6 -> X3 = X5 -> v4_orders_2 X1 -> l1_orders_2 X2 -> l1_orders_2 X1 -> r1_latsum_1 X1 X2 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> r1_orders_2 (k1_latsum_1 X1 X2) X3 X4 -> m1_subset_1 X4 (u1_struct_0 (k1_latsum_1 X1 X2)) -> m1_subset_1 X3 (u1_struct_0 (k1_latsum_1 X1 X2)) -> False)
  -> (forall X1 X4 X3 X6 X5 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 X2 X5 X6 -> False) -> X4 = X6 -> X3 = X5 -> v4_orders_2 X2 -> l1_orders_2 X2 -> l1_orders_2 X1 -> r1_latsum_1 X1 X2 -> m1_subset_1 X6 (u1_struct_0 X2) -> m1_subset_1 X5 (u1_struct_0 X2) -> r1_orders_2 (k1_latsum_1 X1 X2) X3 X4 -> m1_subset_1 X4 (u1_struct_0 (k1_latsum_1 X1 X2)) -> m1_subset_1 X3 (u1_struct_0 (k1_latsum_1 X1 X2)) -> False)
  -> (forall X1 X3 X2 X5 X6 X4, (v2_struct_0 X4 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 (k1_latsum_1 X1 X4) X5 X6 -> False) -> X3 = X6 -> X2 = X5 -> v4_orders_2 X1 -> l1_orders_2 X4 -> l1_orders_2 X1 -> r1_latsum_1 X1 X4 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 (k1_latsum_1 X1 X4)) -> m1_subset_1 X5 (u1_struct_0 (k1_latsum_1 X1 X4)) -> False)
  -> (forall X1 X3 X2 X5 X6 X4, (v2_struct_0 X4 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 (k1_latsum_1 X4 X1) X5 X6 -> False) -> X3 = X6 -> X2 = X5 -> v4_orders_2 X1 -> l1_orders_2 X4 -> l1_orders_2 X1 -> r1_latsum_1 X4 X1 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 (k1_latsum_1 X4 X1)) -> m1_subset_1 X5 (u1_struct_0 (k1_latsum_1 X4 X1)) -> False)
  -> (forall X1, m1_subset_1 X1 (u1_struct_0 (k1_latsum_1 esk1_0 esk2_0)) -> r1_orders_2 (k1_latsum_1 esk1_0 esk2_0) X1 esk4_0 -> r1_orders_2 (k1_latsum_1 esk1_0 esk2_0) esk3_0 X1 -> r1_orders_2 (k1_latsum_1 esk1_0 esk2_0) esk3_0 esk4_0 -> r2_hidden X1 (k3_xboole_0 (u1_struct_0 esk1_0) (u1_struct_0 esk2_0)) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_orders_2 X1 X2 X3 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X2 X3 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> r3_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (r2_hidden (k4_tarski X2 X3) (u1_orders_2 X1) -> False) -> l1_orders_2 X1 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3, (r1_orders_2 X3 X1 X2 -> False) -> l1_orders_2 X3 -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> r2_hidden (k4_tarski X1 X2) (u1_orders_2 X3) -> False)
  -> (forall X5 X3 X2 X4 X1 X6, (r2_hidden (k4_tarski X1 X4) X6 -> False) -> X6 = (k3_relat_1 X3 X5) -> v1_relat_1 X6 -> r2_hidden (k4_tarski X2 X4) X5 -> r2_hidden (k4_tarski X1 X2) X3 -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden (k4_tarski X1 X2) (u1_orders_2 (k1_latsum_1 X3 X4)) -> False) -> l1_orders_2 X4 -> l1_orders_2 X3 -> r2_hidden (k4_tarski X1 X2) (u1_orders_2 X3) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden (k4_tarski X1 X2) (u1_orders_2 (k1_latsum_1 X4 X3)) -> False) -> l1_orders_2 X4 -> l1_orders_2 X3 -> r2_hidden (k4_tarski X1 X2) (u1_orders_2 X3) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X1 X3) = (g1_orders_2 X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X3 X1) = (g1_orders_2 X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 X3 (u1_struct_0 X1) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> r2_hidden X3 (k3_xboole_0 (u1_struct_0 X1) (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 X3 (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> r2_hidden X3 (k3_xboole_0 (u1_struct_0 X1) (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (l1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> ((r1_orders_2 (k1_latsum_1 esk1_0 esk2_0) esk3_0 esk4_0 -> False) -> (r1_orders_2 (k1_latsum_1 esk1_0 esk2_0) esk5_0 esk4_0 -> False) -> False)
  -> ((r1_orders_2 (k1_latsum_1 esk1_0 esk2_0) esk3_0 esk4_0 -> False) -> (r1_orders_2 (k1_latsum_1 esk1_0 esk2_0) esk3_0 esk5_0 -> False) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_orders_2 X1 X2 X2 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (m1_subset_1 (u1_orders_2 X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False) -> l1_orders_2 X1 -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 (k1_latsum_1 esk1_0 esk2_0)) -> False) -> (r1_orders_2 (k1_latsum_1 esk1_0 esk2_0) esk3_0 esk4_0 -> False) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> ((r1_orders_2 (k1_latsum_1 esk1_0 esk2_0) esk3_0 esk4_0 -> False) -> (r2_hidden esk5_0 (k3_xboole_0 (u1_struct_0 esk1_0) (u1_struct_0 esk2_0)) -> False) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k4_tarski X1 X3) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k4_tarski X3 X1) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k4_tarski X1 X3) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X2 X2 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
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
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v2_struct_0 (k1_latsum_1 X1 X2) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v2_struct_0 (k1_latsum_1 X1 X2) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_orders_2 (k1_latsum_1 X1 X2) -> False) -> v3_orders_2 X2 -> v3_orders_2 X1 -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_orders_2 (k1_latsum_1 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v1_orders_2 (k1_latsum_1 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_orders_2 (k1_latsum_1 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (l1_orders_2 (k1_latsum_1 X1 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_orders_2 (u1_struct_0 X1) (u1_orders_2 X1)) = X1 -> False) -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_waybel_0 (esk20_1 X1) X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_waybel_0 (esk20_1 X1) X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v16_waybel_0 X1 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_finset_1 (esk20_1 X1) -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk19_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_waybel_0 (esk16_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_waybel_0 (esk16_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk18_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk2_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk15_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 (k1_latsum_1 esk1_0 esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 (k1_latsum_1 esk1_0 esk2_0)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk15_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) X1 -> False) -> False)
  -> ((r2_hidden esk4_0 (u1_struct_0 esk2_0) -> False) -> False)
  -> ((r2_hidden esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((r1_latsum_1 esk1_0 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk13_0 -> False) -> False)
  -> ((l1_orders_2 esk12_0 -> False) -> False)
  -> ((l1_orders_2 esk2_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> ((v1_lattice3 esk2_0 -> False) -> False)
  -> ((v1_lattice3 esk1_0 -> False) -> False)
  -> ((v5_orders_2 esk2_0 -> False) -> False)
  -> ((v5_orders_2 esk1_0 -> False) -> False)
  -> ((v4_orders_2 esk2_0 -> False) -> False)
  -> ((v4_orders_2 esk1_0 -> False) -> False)
  -> ((v3_orders_2 esk2_0 -> False) -> False)
  -> ((v3_orders_2 esk1_0 -> False) -> False)
  -> False.
Admitted.
