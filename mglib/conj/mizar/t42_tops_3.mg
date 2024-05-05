(** $I sig/MizarPreamble.mgs **)

Theorem t42_tops_3:
 forall r1_xboole_0:set -> set -> prop,
 forall esk22_2:set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall esk4_1:set -> set,
 forall v1_tops_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall k1_struct_0:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk18_1:set -> set,
 forall esk20_1:set -> set,
 forall esk12_1:set -> set,
 forall esk8_1:set -> set,
 forall esk14_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk16_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk6_0:set,
 forall esk5_0:set,
 forall o_0_0_xboole_0:set,
 forall esk7_1:set -> set,
 forall v6_pre_topc:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk15_1:set -> set,
 forall esk10_1:set -> set,
 forall esk11_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk9_1:set -> set,
 forall esk17_1:set -> set,
 forall esk13_1:set -> set,
 forall esk19_1:set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall v2_tops_1:set -> set -> prop,
 forall l1_struct_0:set -> prop,
 forall k7_subset_1:set -> set -> set -> set,
 forall k2_struct_0:set -> set,
 forall k3_subset_1:set -> set -> set,
 forall esk2_0:set,
 forall k4_subset_1:set -> set -> set -> set,
 forall esk3_0:set,
 forall v1_tops_3:set -> set -> prop,
 forall esk1_0:set,
 forall v4_pre_topc:set -> set -> prop,
 forall k3_xboole_0:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v2_struct_0:set -> prop,
 forall v2_pre_topc:set -> prop,
 forall v3_pre_topc:set -> set -> prop,
 forall v3_tops_1:set -> set -> prop,
 forall l1_pre_topc:set -> prop,
 forall esk21_3:set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_xboole_0:set,
     (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk21_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v2_struct_0 X1 -> False) -> (v3_pre_topc (esk21_3 X1 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v2_struct_0 X1 -> False) -> (r1_tarski (esk21_3 X1 X2 X3) X3 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> (v2_struct_0 X2 -> False) -> (r1_xboole_0 X1 (esk21_3 X2 X1 X3) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v3_pre_topc X3 X2 -> v3_tops_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v2_struct_0 X1 -> False) -> (esk21_3 X1 X2 X3) = k1_xboole_0 -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (v2_struct_0 X2 -> False) -> (v3_tops_1 X3 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v3_pre_topc X1 X2 -> r1_xboole_0 X3 X1 -> r1_tarski X1 (esk22_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (X1 = (u1_struct_0 esk1_0) -> False) -> (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 X1) = (u1_struct_0 esk1_0) -> v4_pre_topc X1 esk1_0 -> r1_tarski esk3_0 X1 -> v1_tops_3 esk2_0 esk1_0 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (r1_tarski X3 X2 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r1_tarski (k3_subset_1 X1 X2) (k3_subset_1 X1 X3) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (X1 = (k2_struct_0 X2) -> False) -> (k7_subset_1 (u1_struct_0 X2) (k2_struct_0 X2) X1) = k1_xboole_0 -> l1_struct_0 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_tops_3 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> v3_tops_1 (k3_subset_1 (u1_struct_0 X1) X2) X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (r1_tarski (k3_subset_1 X3 X2) (k3_subset_1 X3 X1) -> False) -> r1_tarski X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v3_tops_1 (k3_subset_1 (u1_struct_0 X2) X1) X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v1_tops_3 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v3_tops_1 X2 X1 -> False) -> (m1_subset_1 (esk22_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (X1 = (u1_struct_0 esk1_0) -> False) -> ((k4_subset_1 (u1_struct_0 esk1_0) esk2_0 (esk4_1 X1)) = (u1_struct_0 esk1_0) -> False) -> (v1_tops_3 esk2_0 esk1_0 -> False) -> v4_pre_topc X1 esk1_0 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_tops_1 (k3_subset_1 (u1_struct_0 X1) X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc (k3_subset_1 (u1_struct_0 X1) X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc (k3_subset_1 (u1_struct_0 X1) X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k7_subset_1 (u1_struct_0 X1) (k2_struct_0 X1) X2) = k1_xboole_0 -> False) -> X2 = (k2_struct_0 X1) -> l1_struct_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v3_tops_1 X2 X1 -> False) -> (v3_pre_topc (esk22_2 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (X1 = (u1_struct_0 esk1_0) -> False) -> (v1_tops_3 esk2_0 esk1_0 -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> v4_pre_topc X1 esk1_0 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v3_tops_1 X2 X1 -> False) -> (esk22_2 X1 X2) = k1_xboole_0 -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (X2 = (k2_struct_0 X1) -> False) -> (k3_subset_1 (u1_struct_0 X1) X2) = (k1_struct_0 X1) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (X1 = (u1_struct_0 esk1_0) -> False) -> (r1_tarski X1 (esk4_1 X1) -> False) -> (v1_tops_3 esk2_0 esk1_0 -> False) -> v4_pre_topc X1 esk1_0 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X1, (X1 = (u1_struct_0 esk1_0) -> False) -> (v1_tops_3 esk2_0 esk1_0 -> False) -> (v4_pre_topc (esk4_1 X1) esk1_0 -> False) -> v4_pre_topc X1 esk1_0 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X2 X1, (X2 = (u1_struct_0 X1) -> False) -> (k3_subset_1 (u1_struct_0 X1) X2) = k1_xboole_0 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, ((k3_subset_1 (u1_struct_0 X2) X1) = (k1_struct_0 X2) -> False) -> X1 = (k2_struct_0 X2) -> l1_pre_topc X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1, (X1 = (u1_struct_0 esk1_0) -> False) -> (v1_tops_3 esk2_0 esk1_0 -> False) -> (esk4_1 X1) = (u1_struct_0 esk1_0) -> v4_pre_topc X1 esk1_0 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, ((k3_subset_1 (u1_struct_0 X2) X1) = k1_xboole_0 -> False) -> X1 = (u1_struct_0 X2) -> l1_pre_topc X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_subset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 (k3_subset_1 X2 X1)) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 X1) = (k4_xboole_0 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tops_1 (esk18_1 X1) X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tops_1 (k2_struct_0 X1) X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk10_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, l1_struct_0 X1 -> v1_subset_1 (k2_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (k2_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k1_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> v1_tops_3 esk2_0 esk1_0 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_pre_topc (esk13_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk19_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk13_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v3_tops_1 (esk20_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk12_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk9_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk8_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk17_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk12_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> ((v4_pre_topc esk3_0 esk1_0 -> False) -> v1_tops_3 esk2_0 esk1_0 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk11_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk14_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk10_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (k2_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_tops_1 (esk15_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_tops_1 (k2_struct_0 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_tops_1 (esk16_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k2_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> ((u1_struct_0 esk1_0) = esk3_0 -> v1_tops_3 esk2_0 esk1_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk10_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v6_pre_topc X1 -> False) -> v2_struct_0 X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_struct_0 X1) = (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, ((k1_struct_0 X1) = k1_xboole_0 -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X2 X3 X1, ((k3_xboole_0 (k4_xboole_0 X1 X2) (k4_xboole_0 X1 X3)) = (k4_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk6_0 -> False) -> False)
  -> ((l1_pre_topc esk5_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
