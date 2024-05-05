(** $I sig/MizarPreamble.mgs **)

Theorem t24_connsp_1:
 forall v4_pre_topc:set -> set -> prop,
 forall k1_pre_topc:set -> set -> set,
 forall v1_pre_topc:set -> prop,
 forall g1_pre_topc:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk28_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk16_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk15_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall esk23_1:set -> set,
 forall k1_xboole_0:set,
 forall esk29_1:set -> set,
 forall esk25_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk21_1:set -> set,
 forall v2_relat_1:set -> prop,
 forall esk22_1:set -> set,
 forall esk20_0:set,
 forall esk19_1:set -> set,
 forall esk18_0:set,
 forall o_0_0_xboole_0:set,
 forall esk10_0:set,
 forall esk5_0:set,
 forall esk11_0:set,
 forall esk4_0:set,
 forall esk9_0:set,
 forall esk14_0:set,
 forall esk7_1:set -> set,
 forall esk17_0:set,
 forall esk12_0:set,
 forall v3_relat_1:set -> prop,
 forall v6_pre_topc:set -> prop,
 forall esk6_1:set -> set,
 forall esk13_1:set -> set,
 forall esk27_1:set -> set,
 forall esk26_1:set -> set,
 forall v1_relat_1:set -> prop,
 forall esk24_1:set -> set,
 forall esk8_1:set -> set,
 forall esk30_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall u1_pre_topc:set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v2_struct_0:set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall m1_pre_topc:set -> set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall esk31_3:set -> set -> set -> set,
 forall v3_pre_topc:set -> set -> prop,
 forall k2_struct_0:set -> set,
 forall k7_subset_1:set -> set -> set -> set,
 forall l1_pre_topc:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall r1_connsp_1:set -> set -> set -> prop,
 forall v1_connsp_1:set -> prop,
 forall v2_pre_topc:set -> prop,
 forall k4_subset_1:set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall v2_connsp_1:set -> set -> prop,
     (forall X4 X2 X3 X1, (v2_connsp_1 (k4_subset_1 (u1_struct_0 X1) X2 X3) X1 -> False) -> (k7_subset_1 (u1_struct_0 X1) (k2_struct_0 X1) X2) = (k4_subset_1 (u1_struct_0 X1) X3 X4) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_connsp_1 X1 -> v2_connsp_1 X2 X1 -> r1_connsp_1 X1 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v2_connsp_1 (k4_subset_1 (u1_struct_0 X1) X2 X3) X1 -> False) -> (k7_subset_1 (u1_struct_0 X1) (k2_struct_0 X1) X2) = (k4_subset_1 (u1_struct_0 X1) X4 X3) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_connsp_1 X1 -> v2_connsp_1 X2 X1 -> r1_connsp_1 X1 X4 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (r1_connsp_1 X2 (k7_subset_1 (u1_struct_0 X2) X1 X3) (k7_subset_1 (u1_struct_0 X2) X3 X1) -> False) -> l1_pre_topc X2 -> v3_pre_topc X3 X2 -> v3_pre_topc X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (r1_connsp_1 X2 (k7_subset_1 (u1_struct_0 X2) X1 X3) (k7_subset_1 (u1_struct_0 X2) X3 X1) -> False) -> l1_pre_topc X2 -> v4_pre_topc X3 X2 -> v4_pre_topc X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((k9_subset_1 (u1_struct_0 X1) (esk31_3 X2 X1 X3) (k2_struct_0 X1)) = X3 -> False) -> l1_pre_topc X2 -> v4_pre_topc X3 X1 -> m1_pre_topc X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X4 X3, (v4_pre_topc X4 X3 -> False) -> (k9_subset_1 (u1_struct_0 X3) X1 (k2_struct_0 X3)) = X4 -> l1_pre_topc X2 -> v4_pre_topc X1 X2 -> m1_pre_topc X3 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (r1_connsp_1 X1 X3 X2 -> False) -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (esk31_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> v4_pre_topc X3 X2 -> m1_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (esk31_3 X1 X2 X3) X1 -> False) -> l1_pre_topc X1 -> v4_pre_topc X3 X2 -> m1_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3 X4, (v2_connsp_1 X3 X4 -> False) -> X1 = X3 -> v2_pre_topc X2 -> l1_pre_topc X2 -> v2_connsp_1 X1 X2 -> m1_pre_topc X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2 X3 X4, (v2_connsp_1 X3 X4 -> False) -> X1 = X3 -> v2_pre_topc X4 -> l1_pre_topc X4 -> v2_connsp_1 X1 X2 -> m1_pre_topc X2 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v2_connsp_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_connsp_1 (k1_pre_topc X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, ((k2_struct_0 X1) = X3 -> False) -> X1 = (k1_pre_topc X2 X3) -> l1_pre_topc X2 -> v1_pre_topc X1 -> m1_pre_topc X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> l1_pre_topc X1 -> v2_struct_0 (k1_pre_topc X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (X1 = (k1_pre_topc X3 X2) -> False) -> (k2_struct_0 X1) = X2 -> l1_pre_topc X3 -> v1_pre_topc X1 -> m1_pre_topc X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X1 X2, (v1_connsp_1 (k1_pre_topc X2 X1) -> False) -> l1_pre_topc X2 -> v2_connsp_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v2_struct_0 (g1_pre_topc X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_pre_topc (k1_pre_topc X1 X2) X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_pre_topc (k1_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_pre_topc X1 X3) = (g1_pre_topc X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_pre_topc X3 X1) = (g1_pre_topc X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> v2_struct_0 (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 (k1_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_pre_topc (k1_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_pre_topc (k1_pre_topc X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_pre_topc (k1_pre_topc X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_pre_topc (k1_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (v1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (l1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1, (m1_subset_1 (u1_pre_topc X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v1_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, l1_struct_0 X1 -> v1_subset_1 (k2_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (k2_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) = X1 -> False) -> l1_pre_topc X1 -> v1_pre_topc X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v2_pre_topc X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk30_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = X1 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k4_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (v2_connsp_1 esk2_0 esk1_0 -> v2_connsp_1 esk3_0 esk1_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk30_1 X1) -> False)
  -> (forall X1, (v3_pre_topc (esk8_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk26_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk28_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (l1_pre_topc X2 -> False) -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_pre_topc (esk23_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (u1_pre_topc X1) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk16_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (k2_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> v2_struct_0 (esk23_1 X1) -> False)
  -> (forall X1, (m1_pre_topc (esk21_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk6_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk25_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k2_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_pre_topc (esk26_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (esk26_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk15_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (esk23_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk29_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v6_pre_topc X1 -> False) -> l1_pre_topc X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_pre_topc (esk21_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_struct_0 X1) = (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk22_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk17_0 -> False)
  -> (forall X1 X2, ((k4_xboole_0 (k2_xboole_0 X1 X2) (k3_xboole_0 X1 X2)) = (k2_xboole_0 (k4_xboole_0 X1 X2) (k4_xboole_0 X2 X1)) -> False) -> False)
  -> ((v2_connsp_1 (k9_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0) esk1_0 -> False) -> False)
  -> ((v2_connsp_1 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0) esk1_0 -> False) -> False)
  -> (forall X1 X2, ((k2_xboole_0 (k3_xboole_0 X1 X2) (k4_xboole_0 X1 X2)) = X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((v4_pre_topc esk3_0 esk1_0 -> False) -> False)
  -> ((v4_pre_topc esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> ((v2_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_struct_0 esk10_0 -> False) -> False)
  -> ((v2_struct_0 esk9_0 -> False) -> False)
  -> ((l1_struct_0 esk5_0 -> False) -> False)
  -> ((v1_pre_topc esk17_0 -> False) -> False)
  -> ((v1_pre_topc esk11_0 -> False) -> False)
  -> ((v1_pre_topc esk10_0 -> False) -> False)
  -> ((v1_pre_topc esk9_0 -> False) -> False)
  -> ((l1_pre_topc esk17_0 -> False) -> False)
  -> ((l1_pre_topc esk11_0 -> False) -> False)
  -> ((l1_pre_topc esk10_0 -> False) -> False)
  -> ((l1_pre_topc esk9_0 -> False) -> False)
  -> ((l1_pre_topc esk4_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk17_0 -> False) -> False)
  -> ((v2_pre_topc esk10_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
