(** $I sig/MizarPreamble.mgs **)

Theorem t54_tsep_1:
 forall v2_pre_topc:set -> prop,
 forall r1_connsp_1:set -> set -> set -> prop,
 forall l1_pre_topc:set -> prop,
 forall esk21_3:set -> set -> set -> set,
 forall esk22_3:set -> set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall k7_subset_1:set -> set -> set -> set,
 forall esk5_0:set,
 forall esk20_3:set -> set -> set -> set,
 forall k3_subset_1:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall k5_subset_1:set -> set -> set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall l1_struct_0:set -> prop,
 forall k2_struct_0:set -> set,
 forall esk18_1:set -> set,
 forall esk13_1:set -> set,
 forall esk10_1:set -> set,
 forall esk15_1:set -> set,
 forall k1_struct_0:set -> set,
 forall esk12_0:set,
 forall esk7_0:set,
 forall esk8_0:set,
 forall esk9_1:set -> set,
 forall esk14_0:set,
 forall k1_xboole_0:set,
 forall esk16_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk11_1:set -> set,
 forall esk17_1:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v2_tops_1:set -> set -> prop,
 forall v3_tops_1:set -> set -> prop,
 forall v1_tops_1:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall esk19_3:set -> set -> set -> set,
 forall esk4_0:set,
 forall esk6_0:set,
 forall v4_pre_topc:set -> set -> prop,
 forall v3_pre_topc:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall r2_tsep_1:set -> set -> set -> prop,
 forall k4_subset_1:set -> set -> set -> set,
 forall esk1_0:set,
 forall u1_struct_0:set -> set,
     (forall X1 X3 X2, (k4_subset_1 (u1_struct_0 esk1_0) (k4_subset_1 (u1_struct_0 esk1_0) X1 X2) X3) = (u1_struct_0 esk1_0) -> v4_pre_topc X2 esk1_0 -> v4_pre_topc X1 esk1_0 -> v3_pre_topc X3 esk1_0 -> r2_tsep_1 esk1_0 esk2_0 esk3_0 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> r1_tarski (k9_subset_1 (u1_struct_0 esk1_0) X2 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0)) esk3_0 -> r1_tarski (k9_subset_1 (u1_struct_0 esk1_0) X1 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0)) esk2_0 -> r1_tarski (k9_subset_1 (u1_struct_0 esk1_0) X3 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0)) (k9_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0) -> False)
  -> (forall X3 X2 X1, (r1_xboole_0 (k9_subset_1 (u1_struct_0 X1) (esk21_3 X1 X2 X3) (esk22_3 X1 X2 X3)) (k4_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X5 X4 X2, (r1_connsp_1 X2 X4 X5 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_tarski X5 X3 -> r1_tarski X4 X1 -> v4_pre_topc X3 X2 -> v4_pre_topc X1 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> r1_xboole_0 (k9_subset_1 (u1_struct_0 X2) X1 X3) (k4_subset_1 (u1_struct_0 X2) X4 X5) -> False)
  -> (forall X3 X2 X1, (r2_tsep_1 X1 X2 X3 -> False) -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r1_connsp_1 X1 (k7_subset_1 (u1_struct_0 X1) X2 X3) (k7_subset_1 (u1_struct_0 X1) X3 X2) -> False)
  -> ((r2_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> (r1_tarski (k9_subset_1 (u1_struct_0 esk1_0) esk6_0 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0)) (k9_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0) -> False) -> False)
  -> (forall X2 X3 X1, (r1_connsp_1 X1 (k7_subset_1 (u1_struct_0 X1) X2 X3) (k7_subset_1 (u1_struct_0 X1) X3 X2) -> False) -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X5 X4 X2, (r1_connsp_1 X2 X4 X5 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_tarski X5 X3 -> r1_tarski X4 X1 -> v4_pre_topc X3 X2 -> v4_pre_topc X1 X2 -> r1_xboole_0 X3 X4 -> r1_xboole_0 X1 X5 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> ((r2_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> (r1_tarski (k9_subset_1 (u1_struct_0 esk1_0) esk5_0 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0)) esk3_0 -> False) -> False)
  -> ((r2_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> (r1_tarski (k9_subset_1 (u1_struct_0 esk1_0) esk4_0 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0)) esk2_0 -> False) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk22_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk21_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk20_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk19_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r1_xboole_0 (esk20_3 X1 X2 X3) X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r1_xboole_0 (esk19_3 X1 X2 X3) X3 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v4_pre_topc (esk22_3 X1 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v4_pre_topc (esk21_3 X1 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v4_pre_topc (esk20_3 X1 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v4_pre_topc (esk19_3 X1 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 (esk22_3 X2 X3 X1) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_connsp_1 X2 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 (esk21_3 X2 X1 X3) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_connsp_1 X2 X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 (esk20_3 X2 X3 X1) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_connsp_1 X2 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 (esk19_3 X2 X1 X3) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_connsp_1 X2 X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 (k3_subset_1 X2 X1) X3) = (k3_subset_1 X2 (k7_subset_1 X2 X1 X3)) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, (r1_connsp_1 X1 X3 X2 -> False) -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (r2_tsep_1 X1 X3 X2 -> False) -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (((k4_subset_1 (u1_struct_0 esk1_0) (k4_subset_1 (u1_struct_0 esk1_0) esk4_0 esk5_0) esk6_0) = (u1_struct_0 esk1_0) -> False) -> (r2_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k5_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k5_subset_1 X2 X1 X3) = (k2_xboole_0 (k4_xboole_0 X1 X3) (k4_xboole_0 X3 X1)) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (r1_tarski X3 X2 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r1_tarski (k3_subset_1 X1 X2) (k3_subset_1 X1 X3) -> False)
  -> (forall X3 X2 X1, ((k5_subset_1 X2 X1 X3) = (k5_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k4_subset_1 (u1_struct_0 X1) X2 (k3_subset_1 (u1_struct_0 X1) X2)) = (k2_struct_0 X1) -> False) -> l1_struct_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (r1_tarski (k3_subset_1 X3 X2) (k3_subset_1 X3 X1) -> False) -> r1_tarski X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_tops_1 (k3_subset_1 (u1_struct_0 X1) X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc (k3_subset_1 (u1_struct_0 X1) X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc (k3_subset_1 (u1_struct_0 X1) X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X2 X1, (r1_tarski (k4_xboole_0 X1 X4) (k4_xboole_0 X2 X3) -> False) -> r1_tarski X3 X4 -> r1_tarski X1 X2 -> False)
  -> (forall X4 X3 X2 X1, (r1_tarski (k3_xboole_0 X1 X3) (k3_xboole_0 X2 X4) -> False) -> r1_tarski X3 X4 -> r1_tarski X1 X2 -> False)
  -> (forall X4 X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) (k2_xboole_0 X2 X4) -> False) -> r1_tarski X3 X4 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r1_tarski (k4_xboole_0 X1 X2) X3 -> False) -> r1_tarski X1 (k2_xboole_0 X2 X3) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k3_xboole_0 X1 X3) (k3_xboole_0 X2 X3) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) X2 -> False) -> r1_tarski X3 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_subset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> ((r2_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> (m1_subset_1 esk6_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((r2_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> (m1_subset_1 esk5_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((r2_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> (m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 (k3_subset_1 X2 X1)) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> ((v3_pre_topc esk6_0 esk1_0 -> False) -> (r2_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((v4_pre_topc esk5_0 esk1_0 -> False) -> (r2_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((v4_pre_topc esk4_0 esk1_0 -> False) -> (r2_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 X1) = (k4_xboole_0 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, l1_struct_0 X1 -> v1_subset_1 (k2_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (k2_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k1_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (k4_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k4_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1, (v3_tops_1 (esk18_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk13_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk11_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk10_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk17_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk13_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_tops_1 (esk15_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_tops_1 (k2_struct_0 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_tops_1 (esk16_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 (k1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_struct_0 X1) = (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, ((k1_struct_0 X1) = k1_xboole_0 -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (forall X1 X2, ((k4_xboole_0 (k2_xboole_0 X1 X2) (k3_xboole_0 X1 X2)) = (k2_xboole_0 (k4_xboole_0 X1 X2) (k4_xboole_0 X2 X1)) -> False) -> False)
  -> (forall X1 X2, ((k4_xboole_0 (k2_xboole_0 X1 X2) (k3_xboole_0 X1 X2)) = (k2_xboole_0 (k4_xboole_0 X1 X2) (k4_xboole_0 X2 X1)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 (k4_xboole_0 X1 X2) (k4_xboole_0 X2 X1)) = (k2_xboole_0 (k4_xboole_0 X2 X1) (k4_xboole_0 X1 X2)) -> False) -> False)
  -> (forall X2 X3 X1, ((k4_xboole_0 (k3_xboole_0 X1 X2) (k3_xboole_0 X1 X3)) = (k3_xboole_0 X1 (k4_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k3_xboole_0 X1 X2) (k3_xboole_0 X1 X3)) = (k3_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X3 X1, ((k3_xboole_0 (k3_xboole_0 X1 X2) X3) = (k3_xboole_0 X1 (k3_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k2_xboole_0 X1 X2) X3) = (k2_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X3 X1, ((k4_xboole_0 (k3_xboole_0 X1 X2) X3) = (k3_xboole_0 X1 (k4_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 (k4_xboole_0 X1 k1_xboole_0) (k4_xboole_0 k1_xboole_0 X1)) = X1 -> False) -> False)
  -> (forall X1 X2, ((k4_xboole_0 X1 (k3_xboole_0 X1 X2)) = (k4_xboole_0 X1 X2) -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 (k4_xboole_0 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (r1_tarski (k3_xboole_0 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_pre_topc esk7_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> False.
Admitted.
