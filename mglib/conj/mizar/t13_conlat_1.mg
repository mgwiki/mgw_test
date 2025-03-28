(** $I sig/MizarPreamble.mgs **)

Theorem t13_conlat_1:
 forall v2_struct_0:set -> prop,
 forall v3_conlat_1:set -> set -> set -> prop,
 forall l1_orders_2:set -> prop,
 forall v1_funct_1:set -> prop,
 forall m1_waybel_1:set -> set -> set -> prop,
 forall esk14_5:set -> set -> set -> set -> set -> set,
 forall r1_orders_2:set -> set -> set -> prop,
 forall esk12_5:set -> set -> set -> set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v5_waybel_0:set -> set -> set -> prop,
 forall k1_waybel_1:set -> set -> set -> set -> set,
 forall esk15_5:set -> set -> set -> set -> set -> set,
 forall esk13_5:set -> set -> set -> set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall v1_relat_1:set -> prop,
 forall v3_orders_2:set -> prop,
 forall r3_orders_2:set -> set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk19_2:set -> set -> set,
 forall v7_struct_0:set -> prop,
 forall esk26_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk25_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk32_1:set -> set,
 forall esk22_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk29_1:set -> set,
 forall esk21_2:set -> set -> set,
 forall esk18_1:set -> set,
 forall esk23_0:set,
 forall esk17_0:set,
 forall v4_orders_2:set -> prop,
 forall esk16_0:set,
 forall esk24_0:set,
 forall esk27_1:set -> set,
 forall esk20_2:set -> set -> set,
 forall esk3_0:set,
 forall esk28_0:set,
 forall esk31_1:set -> set,
 forall esk33_1:set -> set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk30_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall k1_xtuple_0:set -> set,
 forall k2_xtuple_0:set -> set,
 forall v1_xtuple_0:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk34_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k1_relset_1:set -> set -> set,
 forall k1_xboole_0:set,
 forall v1_partfun1:set -> set -> prop,
 forall v5_orders_2:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall k3_relat_1:set -> set -> set,
 forall r2_funct_2:set -> set -> set -> set -> prop,
 forall esk1_0:set,
 forall esk4_0:set,
 forall k1_partfun1:set -> set -> set -> set -> set -> set -> set,
 forall esk5_0:set,
 forall u1_struct_0:set -> set,
 forall esk2_0:set,
     (r2_funct_2 (u1_struct_0 esk1_0) (u1_struct_0 esk2_0) esk4_0 (k1_partfun1 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) (u1_struct_0 esk2_0) (k1_partfun1 (u1_struct_0 esk1_0) (u1_struct_0 esk2_0) (u1_struct_0 esk2_0) (u1_struct_0 esk1_0) esk4_0 esk5_0) esk4_0) -> r2_funct_2 (u1_struct_0 esk2_0) (u1_struct_0 esk1_0) esk5_0 (k1_partfun1 (u1_struct_0 esk2_0) (u1_struct_0 esk2_0) (u1_struct_0 esk2_0) (u1_struct_0 esk1_0) (k1_partfun1 (u1_struct_0 esk2_0) (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) (u1_struct_0 esk2_0) esk5_0 esk4_0) esk5_0) -> False)
  -> (forall X1 X5 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v3_conlat_1 X3 X1 X2 -> False) -> X3 = (k1_waybel_1 X1 X2 X4 X5) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X5 -> v1_funct_1 X4 -> m1_waybel_1 X3 X1 X2 -> v5_waybel_0 X5 X2 X1 -> v5_waybel_0 X4 X1 X2 -> v1_funct_2 X5 (u1_struct_0 X2) (u1_struct_0 X1) -> v1_funct_2 X4 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X1))) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> r1_orders_2 X2 (esk14_5 X1 X2 X3 X4 X5) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X2) X4 (k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X1) X5 (esk14_5 X1 X2 X3 X4 X5))) -> r1_orders_2 X1 (esk12_5 X1 X2 X3 X4 X5) (k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X1) X5 (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X2) X4 (esk12_5 X1 X2 X3 X4 X5))) -> False)
  -> (forall X5 X3 X4 X1 X2 X6, (m1_subset_1 (k1_partfun1 X1 X2 X3 X4 X5 X6) (k1_zfmisc_1 (k2_zfmisc_1 X1 X4)) -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X5 X3 X4 X1 X2 X6, (v1_funct_1 (k1_partfun1 X1 X2 X3 X4 X5 X6) -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X5 X6 X2 X3 X4, ((k1_partfun1 X2 X3 X5 X6 X1 X4) = (k3_relat_1 X1 X4) -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X5 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v3_conlat_1 X3 X1 X2 -> False) -> (m1_subset_1 (esk15_5 X1 X2 X3 X4 X5) (u1_struct_0 X2) -> False) -> X3 = (k1_waybel_1 X1 X2 X4 X5) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X5 -> v1_funct_1 X4 -> m1_waybel_1 X3 X1 X2 -> v5_waybel_0 X5 X2 X1 -> v5_waybel_0 X4 X1 X2 -> v1_funct_2 X5 (u1_struct_0 X2) (u1_struct_0 X1) -> v1_funct_2 X4 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X1))) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X5 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v3_conlat_1 X3 X1 X2 -> False) -> (m1_subset_1 (esk14_5 X1 X2 X3 X4 X5) (u1_struct_0 X2) -> False) -> X3 = (k1_waybel_1 X1 X2 X4 X5) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X5 -> v1_funct_1 X4 -> m1_waybel_1 X3 X1 X2 -> v5_waybel_0 X5 X2 X1 -> v5_waybel_0 X4 X1 X2 -> v1_funct_2 X5 (u1_struct_0 X2) (u1_struct_0 X1) -> v1_funct_2 X4 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X1))) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X5 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v3_conlat_1 X3 X1 X2 -> False) -> (m1_subset_1 (esk13_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> X3 = (k1_waybel_1 X1 X2 X4 X5) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X5 -> v1_funct_1 X4 -> m1_waybel_1 X3 X1 X2 -> v5_waybel_0 X5 X2 X1 -> v5_waybel_0 X4 X1 X2 -> v1_funct_2 X5 (u1_struct_0 X2) (u1_struct_0 X1) -> v1_funct_2 X4 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X1))) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X5 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v3_conlat_1 X3 X1 X2 -> False) -> (m1_subset_1 (esk12_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> X3 = (k1_waybel_1 X1 X2 X4 X5) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X5 -> v1_funct_1 X4 -> m1_waybel_1 X3 X1 X2 -> v5_waybel_0 X5 X2 X1 -> v5_waybel_0 X4 X1 X2 -> v1_funct_2 X5 (u1_struct_0 X2) (u1_struct_0 X1) -> v1_funct_2 X4 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X1))) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X7 X5 X6 X2 X4 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X2 (k3_funct_2 (u1_struct_0 X3) (u1_struct_0 X1) (esk11_3 X1 X3 X4) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X3) (esk10_3 X1 X3 X4) X2)) -> False) -> l1_orders_2 X3 -> l1_orders_2 X1 -> m1_waybel_1 X4 X1 X3 -> v3_conlat_1 X4 X1 X3 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X3) -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X7 X5 X6 X2 X4 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X2 (k3_funct_2 (u1_struct_0 X3) (u1_struct_0 X1) (esk10_3 X3 X1 X4) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X3) (esk11_3 X3 X1 X4) X2)) -> False) -> l1_orders_2 X3 -> l1_orders_2 X1 -> m1_waybel_1 X4 X3 X1 -> v3_conlat_1 X4 X3 X1 -> m1_subset_1 X7 (u1_struct_0 X3) -> m1_subset_1 X6 (u1_struct_0 X3) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X4 X2, (m1_waybel_1 (k1_waybel_1 X1 X2 X3 X4) X1 X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 (u1_struct_0 X2) (u1_struct_0 X1) -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X1))) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X4 X2, ((k1_waybel_1 X1 X2 X3 X4) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 (u1_struct_0 X2) (u1_struct_0 X1) -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X1))) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X3 X2, (v5_waybel_0 X3 X2 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X2) (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X1))) -> r1_orders_2 X1 (esk9_3 X2 X1 X3) (esk8_3 X2 X1 X3) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X5 X1 X2 X4 X6 X7 X3, (r1_orders_2 X3 X7 X6 -> False) -> X7 = (k1_funct_1 X1 X5) -> X6 = (k1_funct_1 X1 X4) -> l1_orders_2 X3 -> l1_orders_2 X2 -> v1_funct_1 X1 -> v5_waybel_0 X1 X2 X3 -> r1_orders_2 X2 X4 X5 -> m1_subset_1 X7 (u1_struct_0 X3) -> m1_subset_1 X6 (u1_struct_0 X3) -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> v1_funct_2 X1 (u1_struct_0 X2) (u1_struct_0 X3) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X3))) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X3, ((k1_waybel_1 X2 X3 (esk10_3 X2 X3 X1) (esk11_3 X2 X3 X1)) = X1 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> l1_orders_2 X3 -> l1_orders_2 X2 -> m1_waybel_1 X1 X2 X3 -> v3_conlat_1 X1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v5_waybel_0 X3 X1 X2 -> False) -> (r1_orders_2 X1 (esk6_3 X1 X2 X3) (esk7_3 X1 X2 X3) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X3 (esk7_3 X1 X2 X3)) = (esk9_3 X1 X2 X3) -> False) -> (v5_waybel_0 X3 X1 X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X3 (esk6_3 X1 X2 X3)) = (esk8_3 X1 X2 X3) -> False) -> (v5_waybel_0 X3 X1 X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X4 X3 X1 X2 X5, (v1_xboole_0 X5 -> False) -> (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X5 X4 -> v1_funct_2 X1 X3 X5 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X5 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> False)
  -> (forall X1 X3 X2, (v5_waybel_0 X3 X1 X2 -> False) -> (m1_subset_1 (esk9_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (v5_waybel_0 X3 X1 X2 -> False) -> (m1_subset_1 (esk8_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (v5_waybel_0 X3 X1 X2 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (v5_waybel_0 X3 X1 X2 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X4 X3 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X4 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X1 X2 X4 X5 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X5 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk11_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X1))) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_waybel_1 X3 X1 X2 -> v3_conlat_1 X3 X1 X2 -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk10_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_waybel_1 X3 X1 X2 -> v3_conlat_1 X3 X1 X2 -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_funct_2 (esk11_3 X1 X2 X3) (u1_struct_0 X2) (u1_struct_0 X1) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_waybel_1 X3 X1 X2 -> v3_conlat_1 X3 X1 X2 -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_funct_2 (esk10_3 X1 X2 X3) (u1_struct_0 X1) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_waybel_1 X3 X1 X2 -> v3_conlat_1 X3 X1 X2 -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v5_waybel_0 (esk11_3 X1 X2 X3) X2 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_waybel_1 X3 X1 X2 -> v3_conlat_1 X3 X1 X2 -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v5_waybel_0 (esk10_3 X1 X2 X3) X1 X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_waybel_1 X3 X1 X2 -> v3_conlat_1 X3 X1 X2 -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_funct_1 (esk11_3 X1 X2 X3) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_waybel_1 X3 X1 X2 -> v3_conlat_1 X3 X1 X2 -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_funct_1 (esk10_3 X1 X2 X3) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_waybel_1 X3 X1 X2 -> v3_conlat_1 X3 X1 X2 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> v5_orders_2 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X3 X2 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_orders_2 X1 X2 X3 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> r1_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_orders_2 X1 X2 X3 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> r3_orders_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> ((k1_relset_1 X2 X1) = X2 -> False) -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 (k9_xtuple_0 (k3_relat_1 X2 X3)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_relat_1 X3 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> r2_hidden (k1_funct_1 X2 X1) (k9_xtuple_0 X3) -> False)
  -> (forall X3 X2 X1, (X1 = k1_xboole_0 -> False) -> X3 = k1_xboole_0 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v1_funct_2 X2 X1 X3 -> False) -> (k1_relset_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (r2_hidden (k1_funct_1 X1 X2) (k9_xtuple_0 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X1 -> r2_hidden X2 (k9_xtuple_0 (k3_relat_1 X1 X3)) -> False)
  -> (forall X1 X2 X3, (v1_funct_2 X1 X2 X3 -> False) -> X3 = k1_xboole_0 -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> (k1_funct_1 X1 (esk34_2 X1 X2)) = (k1_funct_1 X2 (esk34_2 X1 X2)) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k9_xtuple_0 X2) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_relat_1 X3 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 (k3_relat_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k3_relat_1 X1 X2) X3) = (k1_funct_1 X2 (k1_funct_1 X1 X3)) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r3_orders_2 X1 X2 X2 -> False) -> v3_orders_2 X1 -> l1_orders_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (m1_waybel_1 (esk19_2 X1 X2) X1 X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (k1_xtuple_0 X1) (k2_xtuple_0 X1)) (k1_tarski (k1_xtuple_0 X1))) = X1 -> False) -> v1_xtuple_0 X1 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk34_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk26_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk30_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk25_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk31_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk25_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk33_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk32_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk29_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk2_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (((k1_waybel_1 esk1_0 esk2_0 esk4_0 esk5_0) = esk3_0 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk21_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 esk2_0) (u1_struct_0 esk1_0))) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 esk1_0) (u1_struct_0 esk2_0))) -> False) -> False)
  -> (forall X2 X1, ((k2_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X2 -> False) -> False)
  -> (forall X1 X2, ((k1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X1 -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk20_2 X1 X2) X1 X2 -> False) -> False)
  -> ((v1_funct_2 esk5_0 (u1_struct_0 esk2_0) (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v1_funct_2 esk4_0 (u1_struct_0 esk1_0) (u1_struct_0 esk2_0) -> False) -> False)
  -> ((v3_conlat_1 esk3_0 esk1_0 esk2_0 -> False) -> False)
  -> ((m1_waybel_1 esk3_0 esk1_0 esk2_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk21_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk20_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk20_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk27_1 X1) -> False) -> False)
  -> ((v1_xtuple_0 esk24_0 -> False) -> False)
  -> ((v1_xboole_0 esk23_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((l1_orders_2 esk16_0 -> False) -> False)
  -> ((l1_orders_2 esk2_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> ((v5_orders_2 esk2_0 -> False) -> False)
  -> ((v5_orders_2 esk1_0 -> False) -> False)
  -> ((v4_orders_2 esk2_0 -> False) -> False)
  -> ((v4_orders_2 esk1_0 -> False) -> False)
  -> ((v3_orders_2 esk2_0 -> False) -> False)
  -> ((v3_orders_2 esk1_0 -> False) -> False)
  -> False.
Admitted.
