(** $I sig/MizarPreamble.mgs **)

Theorem t43_tdlat_1:
 forall v1_xboole_0:set -> prop,
 forall k2_binop_1:set -> set -> set -> set -> set -> set -> set,
 forall k1_domain_1:set -> set -> set -> set -> set,
 forall k5_relat_1:set -> set -> set,
 forall k1_tdlat_1:set -> set,
 forall v1_relat_1:set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk5_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk24_2:set -> set -> set,
 forall a_1_0_tdlat_1:set -> set,
 forall v4_tops_1:set -> set -> prop,
 forall esk7_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk20_1:set -> set,
 forall esk12_1:set -> set,
 forall esk18_1:set -> set,
 forall v2_relat_1:set -> prop,
 forall esk1_0:set,
 forall esk10_2:set -> set -> set,
 forall esk4_1:set -> set,
 forall esk13_0:set,
 forall esk2_0:set,
 forall o_0_0_xboole_0:set,
 forall esk3_0:set,
 forall esk14_1:set -> set,
 forall esk16_2:set -> set -> set,
 forall esk9_0:set,
 forall esk17_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk11_1:set -> set,
 forall v3_relat_1:set -> prop,
 forall esk19_1:set -> set,
 forall esk8_1:set -> set,
 forall esk15_1:set -> set,
 forall esk21_1:set -> set,
 forall k1_realset1:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall v6_tops_1:set -> set -> prop,
 forall a_1_4_tdlat_1:set -> set,
 forall v3_pre_topc:set -> set -> prop,
 forall v4_pre_topc:set -> set -> prop,
 forall v2_tops_1:set -> set -> prop,
 forall v3_tops_1:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall k2_tarski:set -> set -> set,
 forall k1_tarski:set -> set,
 forall v2_pre_topc:set -> prop,
 forall u1_struct_0:set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall l1_pre_topc:set -> prop,
 forall k9_tdlat_1:set -> set,
 forall k11_tdlat_1:set -> set,
 forall k3_tdlat_1:set -> set,
 forall k1_xboole_0:set,
 forall r1_tarski:set -> set -> prop,
 forall k2_partfun1:set -> set -> set -> set -> set,
 forall k5_binop_1:set -> set -> set -> set -> set,
 forall esk22_5:set -> set -> set -> set -> set -> set,
 forall esk23_5:set -> set -> set -> set -> set -> set,
 forall k1_binop_1:set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall r2_funct_2:set -> set -> set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
     (forall X1 X4 X2 X3 X5, (r2_funct_2 (k2_zfmisc_1 X2 X3) X4 X1 X5 -> False) -> (k1_binop_1 X1 (esk22_5 X2 X3 X4 X1 X5) (esk23_5 X2 X3 X4 X1 X5)) = (k1_binop_1 X5 (esk22_5 X2 X3 X4 X1 X5) (esk23_5 X2 X3 X4 X1 X5)) -> v1_funct_1 X5 -> v1_funct_1 X1 -> v1_funct_2 X5 (k2_zfmisc_1 X2 X3) X4 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X3) X4 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X1 X6 X4 X5 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_binop_1 X1 X2 X4 X3 X5 X6) X4 -> False) -> v1_funct_1 X3 -> m1_subset_1 X6 X2 -> m1_subset_1 X5 X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X2) X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X4)) -> False)
  -> (forall X1 X6 X4 X5 X3 X2, ((k2_binop_1 X1 X2 X4 X3 X5 X6) = (k1_binop_1 X3 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> m1_subset_1 X6 X2 -> m1_subset_1 X5 X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X2) X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X4)) -> False)
  -> (forall X4 X3 X1 X2 X5, (r2_funct_2 (k2_zfmisc_1 X1 X2) X3 X4 X5 -> False) -> (m1_subset_1 (esk23_5 X1 X2 X3 X4 X5) X2 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_2 X5 (k2_zfmisc_1 X1 X2) X3 -> v1_funct_2 X4 (k2_zfmisc_1 X1 X2) X3 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X3)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X3)) -> False)
  -> (forall X4 X3 X1 X2 X5, (r2_funct_2 (k2_zfmisc_1 X1 X2) X3 X4 X5 -> False) -> (m1_subset_1 (esk22_5 X1 X2 X3 X4 X5) X1 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_2 X5 (k2_zfmisc_1 X1 X2) X3 -> v1_funct_2 X4 (k2_zfmisc_1 X1 X2) X3 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X3)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X3)) -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X4 X3 X1, (m1_subset_1 (k5_binop_1 X2 X1 X3 X4) X2 -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X4 X1, (m1_subset_1 (k2_partfun1 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> False) -> X1 = k1_xboole_0 -> v1_funct_1 X3 -> r1_tarski X4 X1 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (X2 = k1_xboole_0 -> False) -> (m1_subset_1 (k2_partfun1 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> False) -> v1_funct_1 X3 -> r1_tarski X4 X1 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X4 X1, (v1_funct_2 (k2_partfun1 X1 X2 X3 X4) X4 X2 -> False) -> X1 = k1_xboole_0 -> v1_funct_1 X3 -> r1_tarski X4 X1 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (X2 = k1_xboole_0 -> False) -> (v1_funct_2 (k2_partfun1 X1 X2 X3 X4) X4 X2 -> False) -> v1_funct_1 X3 -> r1_tarski X4 X1 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X4 X3 X1, ((k5_binop_1 X2 X1 X3 X4) = (k1_binop_1 X1 X3 X4) -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X3 X2 X4 X1, (v1_funct_1 (k2_partfun1 X1 X2 X3 X4) -> False) -> X1 = k1_xboole_0 -> v1_funct_1 X3 -> r1_tarski X4 X1 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (X2 = k1_xboole_0 -> False) -> (v1_funct_1 (k2_partfun1 X1 X2 X3 X4) -> False) -> v1_funct_1 X3 -> r1_tarski X4 X1 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X2 X1 X3, (m1_subset_1 (k2_partfun1 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X2 X1 X3, (v1_funct_1 (k2_partfun1 X1 X2 X3 X4) -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_domain_1 X1 X2 X3 X4) (k2_zfmisc_1 X1 X2) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X3 X2 X1, ((k5_binop_1 (k9_tdlat_1 X1) (k11_tdlat_1 X1) X2 X3) = (k1_binop_1 (k3_tdlat_1 X1) X2 X3) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m2_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) (k9_tdlat_1 X1) -> m2_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) (k9_tdlat_1 X1) -> False)
  -> (forall X4 X3 X2 X1, ((k2_partfun1 X2 X3 X1 X4) = (k5_relat_1 X1 X4) -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X4 X3 X2, ((k1_domain_1 X1 X2 X3 X4) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X1, (m1_subset_1 (k3_tdlat_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k1_tdlat_1 X1) (k1_tdlat_1 X1)) (k1_tdlat_1 X1))) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (k11_tdlat_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k9_tdlat_1 X1) (k9_tdlat_1 X1)) (k9_tdlat_1 X1))) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v1_funct_2 (k3_tdlat_1 X1) (k2_zfmisc_1 (k1_tdlat_1 X1) (k1_tdlat_1 X1)) (k1_tdlat_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_funct_2 (k11_tdlat_1 X1) (k2_zfmisc_1 (k9_tdlat_1 X1) (k9_tdlat_1 X1)) (k9_tdlat_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk5_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk24_2 X3 X2) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 (a_1_4_tdlat_1 X2) -> False) -> X1 = X3 -> l1_pre_topc X2 -> v6_tops_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 (a_1_0_tdlat_1 X2) -> False) -> X1 = X3 -> l1_pre_topc X2 -> v4_tops_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk7_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_1_4_tdlat_1 X2) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk6_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_1_0_tdlat_1 X2) -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 (k5_relat_1 X1 X3) X2) = (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X2 X3 -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v6_tops_1 (esk7_2 X1 X2) X2 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_1_4_tdlat_1 X2) -> False)
  -> (forall X1 X2, (v4_tops_1 (esk6_2 X1 X2) X2 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_1_0_tdlat_1 X2) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (m1_subset_1 (k1_tdlat_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (k9_tdlat_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X3 X1, (v5_relat_1 (k5_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v4_relat_1 (k5_relat_1 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v4_relat_1 (k5_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk24_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k5_relat_1 (k5_relat_1 X1 X2) X2) = (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k5_relat_1 X1 (k2_zfmisc_1 X2 X2)) = (k1_realset1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, ((esk7_2 X1 X2) = X1 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_1_4_tdlat_1 X2) -> False)
  -> (forall X1 X2, ((esk6_2 X1 X2) = X1 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_1_0_tdlat_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k5_relat_1 X1 X2) = X1 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_realset1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v3_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_realset1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_tops_1 (esk21_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk20_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk15_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk15_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk12_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk8_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (k1_tdlat_1 X1) -> False)
  -> (forall X1, v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (k9_tdlat_1 X1) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_tops_1 (esk19_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_funct_1 (k3_tdlat_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_funct_1 (k11_tdlat_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk11_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k9_tdlat_1 X1) = (a_1_4_tdlat_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, ((k1_tdlat_1 X1) = (a_1_0_tdlat_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k1_realset1 (k3_tdlat_1 esk1_0) (k9_tdlat_1 esk1_0)) = (k11_tdlat_1 esk1_0) -> False)
  -> (forall X1, v1_subset_1 (esk17_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk10_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk10_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk10_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk10_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk10_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk4_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk14_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk3_0 -> False) -> False)
  -> ((v2_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((l1_pre_topc esk2_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
