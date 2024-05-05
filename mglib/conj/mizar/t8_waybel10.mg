(** $I sig/MizarPreamble.mgs **)

Theorem t8_waybel10:
 forall esk30_4:set -> set -> set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall l1_orders_2:set -> prop,
 forall v2_struct_0:set -> prop,
 forall l1_struct_0:set -> prop,
 forall v2_funct_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v4_yellow_0:set -> set -> prop,
 forall k5_relat_1:set -> set -> set,
 forall esk31_2:set -> set -> set,
 forall u1_orders_2:set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk23_2:set -> set -> set,
 forall v2_waybel_0:set -> set -> prop,
 forall esk9_2:set -> set -> set,
 forall v3_funct_1:set -> prop,
 forall esk25_1:set -> set,
 forall esk18_1:set -> set,
 forall esk24_1:set -> set,
 forall esk13_1:set -> set,
 forall esk27_0:set,
 forall esk21_0:set,
 forall esk16_2:set -> set -> set,
 forall esk28_2:set -> set -> set,
 forall esk12_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk11_0:set,
 forall esk10_0:set,
 forall esk15_0:set,
 forall esk22_0:set,
 forall esk14_0:set,
 forall esk17_2:set -> set -> set,
 forall esk29_0:set,
 forall v2_funcop_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk26_1:set -> set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk19_1:set -> set,
 forall esk20_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_waybel_0:set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk7_2:set -> set -> set,
 forall g1_orders_2:set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall k1_relset_1:set -> set -> set,
 forall k1_xboole_0:set,
 forall v1_partfun1:set -> set -> prop,
 forall k10_xtuple_0:set -> set,
 forall k9_xtuple_0:set -> set,
 forall esk35_2:set -> set -> set,
 forall esk34_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall esk33_2:set -> set -> set,
 forall esk32_2:set -> set -> set,
 forall k2_relset_1:set -> set -> set,
 forall k5_yellow_0:set -> set -> set,
 forall v1_orders_2:set -> prop,
 forall k5_relset_1:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall m1_yellow_0:set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k1_yellow_2:set -> set -> set -> set,
 forall esk5_0:set,
 forall k2_funct_1:set -> set,
 forall k2_tmap_1:set -> set -> set -> set -> set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
     ((k2_tmap_1 esk2_0 esk1_0 esk5_0 (k1_yellow_2 esk3_0 esk2_0 (k2_tmap_1 esk1_0 esk2_0 esk4_0 esk3_0))) = (k2_funct_1 (k2_tmap_1 esk1_0 esk2_0 esk4_0 esk3_0)) -> v1_funct_1 (k2_tmap_1 esk2_0 esk1_0 esk5_0 (k1_yellow_2 esk3_0 esk2_0 (k2_tmap_1 esk1_0 esk2_0 esk4_0 esk3_0))) -> v1_funct_2 (k2_tmap_1 esk2_0 esk1_0 esk5_0 (k1_yellow_2 esk3_0 esk2_0 (k2_tmap_1 esk1_0 esk2_0 esk4_0 esk3_0))) (u1_struct_0 (k1_yellow_2 esk3_0 esk2_0 (k2_tmap_1 esk1_0 esk2_0 esk4_0 esk3_0))) (u1_struct_0 esk3_0) -> m1_subset_1 (k2_tmap_1 esk2_0 esk1_0 esk5_0 (k1_yellow_2 esk3_0 esk2_0 (k2_tmap_1 esk1_0 esk2_0 esk4_0 esk3_0))) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 (k1_yellow_2 esk3_0 esk2_0 (k2_tmap_1 esk1_0 esk2_0 esk4_0 esk3_0))) (u1_struct_0 esk3_0))) -> False)
  -> (forall X1 X4 X3 X2, ((k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X2) X3 (esk30_4 X1 X2 X3 X4)) = X4 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 (k1_yellow_2 X1 X2 X3)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk30_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 (k1_yellow_2 X1 X2 X3)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k2_tmap_1 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X4) (u1_struct_0 X2))) -> False) -> v1_funct_1 X3 -> l1_struct_0 X4 -> l1_struct_0 X2 -> l1_struct_0 X1 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k1_funct_1 (k2_tmap_1 X3 X4 X5 X2) X1) = (k1_funct_1 X5 X1) -> False) -> l1_orders_2 X4 -> l1_orders_2 X3 -> v1_funct_1 X5 -> m1_yellow_0 X2 X3 -> r2_hidden X1 (u1_struct_0 X2) -> v1_funct_2 X5 (u1_struct_0 X3) (u1_struct_0 X4) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X3) (u1_struct_0 X4))) -> False)
  -> (forall X4 X1 X2 X3, (v1_funct_2 (k2_tmap_1 X1 X2 X3 X4) (u1_struct_0 X4) (u1_struct_0 X2) -> False) -> v1_funct_1 X3 -> l1_struct_0 X4 -> l1_struct_0 X2 -> l1_struct_0 X1 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X4 X3 X2, ((k5_relset_1 (u1_struct_0 X1) (u1_struct_0 X2) X3 (u1_struct_0 X4)) = (k2_tmap_1 X1 X2 X3 X4) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> m1_yellow_0 X4 X1 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X4 X3 X2, (v2_funct_1 (k2_tmap_1 X1 X2 X3 X4) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v2_funct_1 X3 -> m1_yellow_0 X4 X1 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X4 X1 X2 X3, (v1_funct_1 (k2_tmap_1 X1 X2 X3 X4) -> False) -> v1_funct_1 X3 -> l1_struct_0 X4 -> l1_struct_0 X2 -> l1_struct_0 X1 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k5_relset_1 X2 X3 X1 X4) (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v2_struct_0 (k1_yellow_2 X1 X2 X3) -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v4_yellow_0 (k1_yellow_2 X1 X2 X3) X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v4_yellow_0 (k1_yellow_2 X1 X2 X3) X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_yellow_0 (k1_yellow_2 X1 X2 X3) X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_orders_2 (k1_yellow_2 X1 X2 X3) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_orders_2 (k1_yellow_2 X1 X2 X3) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, ((k1_yellow_2 X1 X2 X3) = (k5_yellow_0 X2 (k2_relset_1 (u1_struct_0 X2) X3)) -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X4 X1 X2 X3, ((k5_relset_1 X2 X3 X1 X4) = (k5_relat_1 X1 X4) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> (k1_funct_1 X1 (esk33_2 X1 X2)) = (esk32_2 X1 X2) -> (k1_funct_1 X2 (esk34_2 X1 X2)) = (esk35_2 X1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r2_hidden (esk33_2 X1 X2) (k9_xtuple_0 X1) -> r2_hidden (esk34_2 X1 X2) (k10_xtuple_0 X1) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> ((k1_funct_1 X1 (esk35_2 X1 X2)) = (esk34_2 X1 X2) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> (k1_funct_1 X1 (esk33_2 X1 X2)) = (esk32_2 X1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r2_hidden (esk33_2 X1 X2) (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> ((k1_funct_1 X2 (esk32_2 X1 X2)) = (esk33_2 X1 X2) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> (k1_funct_1 X2 (esk34_2 X1 X2)) = (esk35_2 X1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r2_hidden (esk34_2 X1 X2) (k10_xtuple_0 X1) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> (r2_hidden (esk35_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> (k1_funct_1 X1 (esk33_2 X1 X2)) = (esk32_2 X1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r2_hidden (esk33_2 X1 X2) (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> (r2_hidden (esk32_2 X1 X2) (k10_xtuple_0 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> (k1_funct_1 X2 (esk34_2 X1 X2)) = (esk35_2 X1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r2_hidden (esk34_2 X1 X2) (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> ((k1_relset_1 X2 X1) = X2 -> False) -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X2 X1, (X1 = k1_xboole_0 -> False) -> X3 = k1_xboole_0 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v1_funct_2 X2 X1 X3 -> False) -> (k1_relset_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (v1_funct_2 X1 X2 X3 -> False) -> X3 = k1_xboole_0 -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk6_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> (k1_funct_1 X1 (esk31_2 X1 X2)) = (k1_funct_1 X2 (esk31_2 X1 X2)) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk6_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> ((k1_funct_1 X2 (esk32_2 X1 X2)) = (esk33_2 X1 X2) -> False) -> ((k1_funct_1 X1 (esk35_2 X1 X2)) = (esk34_2 X1 X2) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X1 X3) = (g1_orders_2 X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_orders_2 X3 X1) = (g1_orders_2 X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk7_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> ((k1_funct_1 X1 (esk35_2 X1 X2)) = (esk34_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k10_xtuple_0 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> ((k1_funct_1 X2 (esk32_2 X1 X2)) = (esk33_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> (r2_hidden (esk32_2 X1 X2) (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk35_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> v1_relat_1 X1 -> r1_tarski (k10_xtuple_0 X1) X3 -> r1_tarski (k9_xtuple_0 X1) X2 -> False)
  -> (forall X1 X2, (v1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (l1_orders_2 (g1_orders_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1 X3, ((u1_struct_0 X1) = X3 -> False) -> X1 = (k5_yellow_0 X2 X3) -> l1_orders_2 X2 -> v1_orders_2 X1 -> m1_yellow_0 X1 X2 -> v4_yellow_0 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (X1 = (k5_yellow_0 X3 X2) -> False) -> (u1_struct_0 X1) = X2 -> l1_orders_2 X3 -> v1_orders_2 X1 -> m1_yellow_0 X1 X3 -> v4_yellow_0 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X1, (m1_subset_1 (u1_orders_2 X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 (k9_xtuple_0 X2) -> False) -> X4 = (k2_funct_1 X2) -> X1 = (k1_funct_1 X4 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> v2_funct_1 X2 -> v1_relat_1 X4 -> v1_relat_1 X2 -> r2_hidden X3 (k10_xtuple_0 X2) -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 (k10_xtuple_0 X2) -> False) -> X4 = (k2_funct_1 X2) -> X1 = (k1_funct_1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> v2_funct_1 X2 -> v1_relat_1 X4 -> v1_relat_1 X2 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (X1 = (k1_funct_1 X2 X3) -> False) -> X2 = (k2_funct_1 X4) -> X3 = (k1_funct_1 X4 X1) -> v1_funct_1 X4 -> v1_funct_1 X2 -> v2_funct_1 X4 -> v1_relat_1 X4 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 X4) -> False)
  -> (forall X4 X2 X3 X1, (X1 = (k1_funct_1 X2 X3) -> False) -> X4 = (k2_funct_1 X2) -> X3 = (k1_funct_1 X4 X1) -> v1_funct_1 X4 -> v1_funct_1 X2 -> v2_funct_1 X2 -> v1_relat_1 X4 -> v1_relat_1 X2 -> r2_hidden X1 (k10_xtuple_0 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k5_relat_1 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k9_xtuple_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> l1_orders_2 X1 -> v2_struct_0 (k5_yellow_0 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk8_2 X1 X2)) = (esk7_2 X1 X2) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (m1_yellow_0 X1 X2 -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> r1_tarski (u1_struct_0 X1) (u1_struct_0 X2) -> r1_tarski (u1_orders_2 X1) (u1_orders_2 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v4_yellow_0 (k5_yellow_0 X1 X2) X1 -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> (r2_hidden (esk8_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk23_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v4_yellow_0 (k5_yellow_0 X1 X2) X1 -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_yellow_0 (k5_yellow_0 X1 X2) X1 -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k9_xtuple_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_orders_2 (k5_yellow_0 X1 X2) -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk31_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_orders_2 (k5_yellow_0 X1 X2) -> False) -> l1_orders_2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v2_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v1_waybel_0 X1 X2 -> False) -> l1_orders_2 X2 -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v4_funct_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v4_funct_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r1_tarski (u1_orders_2 X1) (u1_orders_2 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_yellow_0 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski (u1_struct_0 X1) (u1_struct_0 X2) -> False) -> l1_orders_2 X2 -> l1_orders_2 X1 -> m1_yellow_0 X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, ((k9_xtuple_0 X1) = (k10_xtuple_0 X2) -> False) -> X1 = (k2_funct_1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X2 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v3_funct_1 (k5_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_funcop_1 (k5_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (v1_funcop_1 X1 -> False) -> v1_funct_1 X1 -> v4_funct_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k2_relset_1 X2 X1) = (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v4_relat_1 (esk23_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_partfun1 (esk23_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v5_relat_1 (esk23_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k5_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_orders_2 (u1_struct_0 X1) (u1_orders_2 X1)) = X1 -> False) -> l1_orders_2 X1 -> v1_orders_2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k10_xtuple_0 (k2_funct_1 X1)) = (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, ((k9_xtuple_0 (k2_funct_1 X1)) = (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (l1_orders_2 X2 -> False) -> l1_orders_2 X1 -> m1_yellow_0 X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_yellow_0 (esk26_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_yellow_0 (esk26_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v2_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk20_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk25_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_orders_2 X1 -> v2_struct_0 (esk26_1 X1) -> False)
  -> (forall X1, (v4_yellow_0 (esk24_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v2_waybel_0 (esk18_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_waybel_0 (esk18_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (m1_yellow_0 (esk24_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (m1_yellow_0 (esk13_1 X1) X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk19_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_orders_2 (esk26_1 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_orders_2 (esk24_1 X1) -> False) -> l1_orders_2 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_orders_2 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v3_funct_1 esk27_0 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk3_0 -> False)
  -> (v2_struct_0 esk2_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk17_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 esk2_0) (u1_struct_0 esk1_0))) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 esk1_0) (u1_struct_0 esk2_0))) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk16_2 X1 X2) X1 X2 -> False) -> False)
  -> ((v1_funct_2 esk5_0 (u1_struct_0 esk2_0) (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v1_funct_2 esk4_0 (u1_struct_0 esk1_0) (u1_struct_0 esk2_0) -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk28_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk17_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk28_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk17_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_yellow_0 esk3_0 esk1_0 -> False) -> False)
  -> ((v3_funct_1 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_funcop_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v4_funct_1 esk29_0 -> False) -> False)
  -> ((l1_struct_0 esk11_0 -> False) -> False)
  -> ((v2_funct_1 esk22_0 -> False) -> False)
  -> ((v2_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((l1_orders_2 esk10_0 -> False) -> False)
  -> ((l1_orders_2 esk2_0 -> False) -> False)
  -> ((l1_orders_2 esk1_0 -> False) -> False)
  -> (((k2_funct_1 esk4_0) = esk5_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
