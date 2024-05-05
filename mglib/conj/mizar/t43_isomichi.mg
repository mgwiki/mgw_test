(** $I sig/MizarPreamble.mgs **)

Theorem t43_isomichi:
 forall l1_pre_topc:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v2_pre_topc:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v3_isomichi:set -> set -> prop,
 forall k3_xboole_0:set -> set -> set,
 forall v4_pre_topc:set -> set -> prop,
 forall v3_pre_topc:set -> set -> prop,
 forall v6_tops_1:set -> set -> prop,
 forall esk13_1:set -> set,
 forall esk11_1:set -> set,
 forall esk9_1:set -> set,
 forall esk7_1:set -> set,
 forall esk6_1:set -> set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall l1_struct_0:set -> prop,
 forall esk8_1:set -> set,
 forall esk10_1:set -> set,
 forall esk12_1:set -> set,
 forall v1_decomp_1:set -> set -> prop,
 forall v5_isomichi:set -> set -> prop,
 forall v4_isomichi:set -> set -> prop,
 forall v1_isomichi:set -> set -> prop,
 forall v2_isomichi:set -> set -> prop,
 forall v4_tops_1:set -> set -> prop,
 forall v5_tops_1:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall esk1_0:set,
 forall k1_tops_1:set -> set -> set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall u1_struct_0:set -> set,
 forall k4_subset_1:set -> set -> set -> set,
 forall k2_pre_topc:set -> set -> set,
     ((k9_subset_1 (u1_struct_0 esk1_0) (k1_tops_1 esk1_0 (k2_pre_topc esk1_0 esk2_0)) (k1_tops_1 esk1_0 (k2_pre_topc esk1_0 esk3_0))) = (k1_tops_1 esk1_0 (k2_pre_topc esk1_0 (k9_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0))) -> (k4_subset_1 (u1_struct_0 esk1_0) (k2_pre_topc esk1_0 (k1_tops_1 esk1_0 esk2_0)) (k2_pre_topc esk1_0 (k1_tops_1 esk1_0 esk3_0))) = (k2_pre_topc esk1_0 (k1_tops_1 esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0))) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 (u1_struct_0 X1) (k1_tops_1 X1 (k2_pre_topc X1 (k1_tops_1 X1 X2))) (k1_tops_1 X1 (k2_pre_topc X1 (k1_tops_1 X1 X3)))) = (k1_tops_1 X1 (k2_pre_topc X1 (k1_tops_1 X1 (k9_subset_1 (u1_struct_0 X1) X2 X3)))) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 (u1_struct_0 X1) (k2_pre_topc X1 (k1_tops_1 X1 (k2_pre_topc X1 X2))) (k2_pre_topc X1 (k1_tops_1 X1 (k2_pre_topc X1 X3)))) = (k2_pre_topc X1 (k1_tops_1 X1 (k2_pre_topc X1 (k4_subset_1 (u1_struct_0 X1) X2 X3)))) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (r1_tarski (k4_subset_1 (u1_struct_0 X1) (k1_tops_1 X1 X2) (k1_tops_1 X1 X3)) (k1_tops_1 X1 (k4_subset_1 (u1_struct_0 X1) X2 X3)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (r1_tarski (k2_pre_topc X1 (k9_subset_1 (u1_struct_0 X1) X2 X3)) (k9_subset_1 (u1_struct_0 X1) (k2_pre_topc X1 X2) (k2_pre_topc X1 X3)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 (u1_struct_0 X1) (k1_tops_1 X1 X2) (k1_tops_1 X1 X3)) = (k1_tops_1 X1 (k9_subset_1 (u1_struct_0 X1) X2 X3)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 (u1_struct_0 X1) (k2_pre_topc X1 X2) (k2_pre_topc X1 X3)) = (k2_pre_topc X1 (k4_subset_1 (u1_struct_0 X1) X2 X3)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k1_tops_1 X1 (k2_pre_topc X1 (k1_tops_1 X1 X2))) = (k1_tops_1 X1 (k2_pre_topc X1 X2)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_isomichi X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k2_pre_topc X1 (k1_tops_1 X1 (k2_pre_topc X1 X2))) = (k2_pre_topc X1 (k1_tops_1 X1 X2)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_isomichi X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k1_tops_1 X1 X2) (k1_tops_1 X1 X3) -> False) -> l1_pre_topc X1 -> r1_tarski X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_pre_topc X1 X2) (k2_pre_topc X1 X3) -> False) -> l1_pre_topc X1 -> r1_tarski X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v5_tops_1 (k2_pre_topc X1 (k1_tops_1 X1 X2)) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v6_tops_1 (k1_tops_1 X1 (k2_pre_topc X1 X2)) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v5_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_tops_1 X2 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v6_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v4_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_isomichi X2 X1 -> v2_isomichi X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_tops_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_pre_topc X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k1_tops_1 X1 (k1_tops_1 X1 X2)) = (k1_tops_1 X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k2_pre_topc X1 (k2_pre_topc X1 X2)) = (k2_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, v2_pre_topc X2 -> l1_pre_topc X2 -> v4_isomichi X1 X2 -> v5_isomichi X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, v2_pre_topc X2 -> l1_pre_topc X2 -> v4_isomichi X1 X2 -> v5_isomichi X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, v2_pre_topc X2 -> l1_pre_topc X2 -> v3_isomichi X1 X2 -> v5_isomichi X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, v2_pre_topc X2 -> l1_pre_topc X2 -> v3_isomichi X1 X2 -> v5_isomichi X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, v2_pre_topc X2 -> l1_pre_topc X2 -> v3_isomichi X1 X2 -> v4_isomichi X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, v2_pre_topc X2 -> l1_pre_topc X2 -> v3_isomichi X1 X2 -> v4_isomichi X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v4_pre_topc (k2_pre_topc X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc (k1_tops_1 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_decomp_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_isomichi X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v2_isomichi X1 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v4_tops_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_isomichi X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_decomp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v1_isomichi X1 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v4_tops_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v1_isomichi X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v4_pre_topc X1 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v5_tops_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v5_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v4_tops_1 X1 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v5_tops_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v4_tops_1 X1 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v6_tops_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v3_pre_topc X1 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v6_tops_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v6_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_isomichi X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_isomichi X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_isomichi X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_isomichi X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (r1_tarski (k1_tops_1 X1 X2) X2 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (r1_tarski X2 (k2_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v2_isomichi (esk9_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_isomichi (esk9_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk12_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk10_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v5_tops_1 (esk11_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v6_tops_1 (esk11_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_tops_1 (esk9_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk10_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk8_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk7_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_isomichi (esk13_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v3_isomichi esk3_0 esk1_0 -> False) -> False)
  -> ((v3_isomichi esk2_0 esk1_0 -> False) -> False)
  -> ((l1_struct_0 esk5_0 -> False) -> False)
  -> ((l1_pre_topc esk4_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> False.
Admitted.
