(** $I sig/MizarPreamble.mgs **)

Theorem t15_compts_1:
 forall k8_relset_1:set -> set -> set -> set -> set,
 forall l1_struct_0:set -> prop,
 forall k8_relat_1:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v1_finset_1:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall v1_relat_1:set -> prop,
 forall k1_funct_3:set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall v2_tops_1:set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk22_1:set -> set,
 forall k2_struct_0:set -> set,
 forall esk24_1:set -> set,
 forall v5_finset_1:set -> prop,
 forall esk30_1:set -> set,
 forall esk26_1:set -> set,
 forall esk17_1:set -> set,
 forall v1_tops_1:set -> set -> prop,
 forall esk21_1:set -> set,
 forall esk32_0:set,
 forall esk20_0:set,
 forall esk11_0:set,
 forall esk10_1:set -> set,
 forall esk14_0:set,
 forall esk7_0:set,
 forall esk8_0:set,
 forall o_0_0_xboole_0:set,
 forall esk9_1:set -> set,
 forall esk18_1:set -> set,
 forall esk25_2:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall esk19_0:set,
 forall esk31_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall v6_pre_topc:set -> prop,
 forall v2_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk13_1:set -> set,
 forall esk23_1:set -> set,
 forall esk29_1:set -> set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk27_1:set -> set,
 forall esk15_1:set -> set,
 forall esk16_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk28_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k2_relset_1:set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall k3_tarski:set -> set,
 forall k1_relset_1:set -> set -> set,
 forall k1_xboole_0:set,
 forall esk6_2:set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall m1_setfam_1:set -> set -> prop,
 forall v2_compts_1:set -> set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall k2_funct_3:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall k7_relset_1:set -> set -> set -> set -> set,
 forall v1_tops_2:set -> set -> prop,
 forall l1_pre_topc:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v5_pre_topc:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall k7_relat_1:set -> set -> set,
 forall k3_funct_3:set -> set,
 forall v2_struct_0:set -> prop,
     (forall X1 X5 X3 X4 X2, (v2_struct_0 X2 -> False) -> (v1_tops_2 X5 X1 -> False) -> X5 = (k7_relat_1 (k3_funct_3 X3) X4) -> l1_pre_topc X2 -> l1_pre_topc X1 -> v1_funct_1 X3 -> v1_tops_2 X4 X2 -> v5_pre_topc X3 X1 X2 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k8_relset_1 X2 X3 X1 X4) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k7_relset_1 X2 X3 X1 X4) (k1_zfmisc_1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (k7_relat_1 (k3_funct_3 X3) X4) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> v1_funct_1 X3 -> l1_struct_0 X2 -> l1_struct_0 X1 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X2))) -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (k2_funct_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 X2))) -> False) -> v1_funct_1 X3 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_2 (k2_funct_3 X1 X2 X3) (k1_zfmisc_1 X1) (k1_zfmisc_1 X2) -> False) -> v1_funct_1 X3 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (esk5_3 X1 X2 X3) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> v2_compts_1 X2 X1 -> m1_setfam_1 X3 X2 -> v1_tops_2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X4 X1 X2 X3, ((k8_relset_1 X2 X3 X1 X4) = (k8_relat_1 X1 X4) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X1 X2 X3, ((k7_relset_1 X2 X3 X1 X4) = (k7_relat_1 X1 X4) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (r1_tarski (esk5_3 X1 X2 X3) X3 -> False) -> l1_pre_topc X1 -> v2_compts_1 X2 X1 -> m1_setfam_1 X3 X2 -> v1_tops_2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X2 X3 X1, (m1_setfam_1 (esk5_3 X1 X2 X3) X2 -> False) -> l1_pre_topc X1 -> v2_compts_1 X2 X1 -> m1_setfam_1 X3 X2 -> v1_tops_2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X2 X3 X1, (v1_finset_1 (esk5_3 X1 X2 X3) -> False) -> l1_pre_topc X1 -> v2_compts_1 X2 X1 -> m1_setfam_1 X3 X2 -> v1_tops_2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (k2_funct_3 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X2 X3 X1, ((k2_funct_3 X3 X1 X2) = (k1_funct_3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v2_compts_1 X3 X2 -> False) -> l1_pre_topc X2 -> v1_finset_1 X1 -> m1_setfam_1 X1 X3 -> r1_tarski X1 (esk6_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X3 X2 X1, (v1_finset_1 X1 -> False) -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> ((k1_relset_1 X2 X1) = X2 -> False) -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (X1 = k1_xboole_0 -> False) -> X3 = k1_xboole_0 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v1_funct_2 X2 X1 X3 -> False) -> (k1_relset_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X2 X3, (v1_funct_2 X1 X2 X3 -> False) -> X3 = k1_xboole_0 -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v2_compts_1 X2 X1 -> False) -> (m1_subset_1 (esk6_2 X1 X2) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (r1_tarski X2 (k8_relat_1 X1 (k7_relat_1 X1 X2)) -> False) -> v1_relat_1 X1 -> r1_tarski X2 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, ((k3_tarski (k7_relat_1 (k3_funct_3 X1) X2)) = (k8_relat_1 X1 (k3_tarski X2)) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r1_tarski X2 (k1_zfmisc_1 (k10_xtuple_0 X1)) -> False)
  -> (forall X2 X1, ((k3_tarski (k7_relat_1 (k1_funct_3 X1) X2)) = (k7_relat_1 X1 (k3_tarski X2)) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r1_tarski X2 (k1_zfmisc_1 (k9_xtuple_0 X1)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k7_relat_1 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k9_xtuple_0 X1)) -> False)
  -> (forall X2 X1, (v2_compts_1 X2 X1 -> False) -> (v1_tops_2 (esk6_2 X1 X2) X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_compts_1 X2 X1 -> False) -> (m1_setfam_1 (esk6_2 X1 X2) X2 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (r1_tarski (k7_relat_1 X1 (k8_relat_1 X1 X2)) X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski (k7_relat_1 (k3_funct_3 X1) X2) (k8_relat_1 (k1_funct_3 X1) X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X3 X1, (r1_tarski (k8_relat_1 X1 X2) (k8_relat_1 X1 X3) -> False) -> v1_relat_1 X1 -> r1_tarski X2 X3 -> False)
  -> (forall X2 X3 X1, (r1_tarski (k7_relat_1 X1 X2) (k7_relat_1 X1 X3) -> False) -> v1_relat_1 X1 -> r1_tarski X2 X3 -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_compts_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 (k8_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_finset_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k7_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk28_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk28_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, l1_struct_0 X1 -> v1_subset_1 (k2_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k2_relset_1 X2 X1) = (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_setfam_1 X2 X1 -> False) -> r1_tarski X1 (k3_tarski X2) -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (k2_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_zfmisc_1 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X2 (k3_tarski X1) -> False) -> m1_setfam_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk16_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (k2_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_tops_1 (esk24_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_tops_1 (k2_struct_0 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_tops_1 (esk27_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_finset_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_relat_1 (k3_funct_3 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k1_funct_3 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k10_xtuple_0 X1) -> False) -> v1_finset_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k9_xtuple_0 X1) -> False) -> v1_finset_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k3_tarski X1) -> False) -> v1_finset_1 X1 -> v5_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k2_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_funct_1 (k3_funct_3 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k1_funct_3 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk15_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk30_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk29_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v6_pre_topc X1 -> False) -> l1_pre_topc X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_struct_0 X1) = (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v2_compts_1 (k7_relset_1 (u1_struct_0 esk1_0) (u1_struct_0 esk3_0) esk4_0 esk2_0) esk3_0 -> False)
  -> (forall X1, v1_subset_1 (esk21_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk32_0 -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk3_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk12_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 esk1_0) (u1_struct_0 esk3_0))) -> False) -> False)
  -> ((v1_funct_2 esk4_0 (u1_struct_0 esk1_0) (u1_struct_0 esk3_0) -> False) -> False)
  -> ((v5_pre_topc esk4_0 esk1_0 esk3_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk12_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_setfam_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> (((k2_relset_1 (u1_struct_0 esk3_0) esk4_0) = (k2_struct_0 esk3_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v2_compts_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk18_1 X1) -> False) -> False)
  -> ((v2_finset_1 esk32_0 -> False) -> False)
  -> ((v5_finset_1 esk31_0 -> False) -> False)
  -> ((v1_relat_1 esk32_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_finset_1 esk31_0 -> False) -> False)
  -> ((v1_finset_1 esk20_0 -> False) -> False)
  -> ((v1_finset_1 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk8_0 -> False) -> False)
  -> ((v1_funct_1 esk32_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((l1_pre_topc esk7_0 -> False) -> False)
  -> ((l1_pre_topc esk3_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
