(** $I sig/MizarPreamble.mgs **)

Theorem t17_decomp_1:
 forall k3_xboole_0:set -> set -> set,
 forall esk3_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v3_decomp_1:set -> set -> prop,
 forall k2_decomp_1:set -> set -> set,
 forall v4_pre_topc:set -> set -> prop,
 forall v2_pre_topc:set -> prop,
 forall v3_pre_topc:set -> set -> prop,
 forall v3_tops_1:set -> set -> prop,
 forall v2_tops_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall a_1_3_decomp_1:set -> set,
 forall esk20_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall k9_decomp_1:set -> set,
 forall k10_decomp_1:set -> set,
 forall esk18_1:set -> set,
 forall esk12_1:set -> set,
 forall esk17_1:set -> set,
 forall esk16_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk15_1:set -> set,
 forall esk6_1:set -> set,
 forall esk4_0:set,
 forall esk5_0:set,
 forall esk13_1:set -> set,
 forall esk1_0:set,
 forall esk11_1:set -> set,
 forall esk10_1:set -> set,
 forall esk14_1:set -> set,
 forall esk19_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall k20_decomp_1:set -> set,
 forall esk2_2:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall a_1_4_decomp_1:set -> set,
 forall esk7_2:set -> set -> set,
 forall a_1_14_decomp_1:set -> set,
 forall k5_decomp_1:set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall k1_decomp_1:set -> set -> set,
 forall k4_decomp_1:set -> set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall l1_pre_topc:set -> prop,
 forall k4_subset_1:set -> set -> set -> set,
 forall k1_tops_1:set -> set -> set,
 forall k2_pre_topc:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v4_decomp_1:set -> set -> prop,
     (forall X1 X2, (v4_decomp_1 X1 X2 -> False) -> l1_pre_topc X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> r1_tarski X1 (k4_subset_1 (u1_struct_0 X2) (k2_pre_topc X2 (k1_tops_1 X2 X1)) (k1_tops_1 X2 (k2_pre_topc X2 X1))) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk3_3 X1 X2 X3) X3 -> r2_hidden (esk3_3 X1 X2 X3) X2 -> r2_hidden (esk3_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 (k4_subset_1 (u1_struct_0 X2) (k2_pre_topc X2 (k1_tops_1 X2 X1)) (k1_tops_1 X2 (k2_pre_topc X2 X1))) -> False) -> l1_pre_topc X2 -> v4_decomp_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v3_decomp_1 X1 X2 -> False) -> l1_pre_topc X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> r1_tarski X1 (k2_pre_topc X2 (k1_tops_1 X2 (k2_pre_topc X2 X1))) -> False)
  -> (forall X2 X1, ((k9_subset_1 (u1_struct_0 X1) X2 (k2_pre_topc X1 (k1_tops_1 X1 (k2_pre_topc X1 X2)))) = (k4_decomp_1 X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k2_pre_topc X1 (k1_tops_1 X1 (k2_pre_topc X1 (k1_tops_1 X1 X2)))) = (k2_pre_topc X1 (k1_tops_1 X1 X2)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_pre_topc X2 (k1_tops_1 X2 (k2_pre_topc X2 X1))) -> False) -> l1_pre_topc X2 -> v3_decomp_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X2 X1, ((k9_subset_1 (u1_struct_0 X1) X2 (k1_tops_1 X1 (k2_pre_topc X1 X2))) = (k2_decomp_1 X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k9_subset_1 (u1_struct_0 X1) X2 (k2_pre_topc X1 (k1_tops_1 X1 X2))) = (k1_decomp_1 X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k1_tops_1 X1 X2) (k1_tops_1 X1 X3) -> False) -> l1_pre_topc X1 -> r1_tarski X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_pre_topc X1 X2) (k2_pre_topc X1 X3) -> False) -> l1_pre_topc X1 -> r1_tarski X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k4_subset_1 (u1_struct_0 X1) (k1_decomp_1 X1 X2) (k2_decomp_1 X1 X2)) = (k5_decomp_1 X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 (a_1_14_decomp_1 X2) -> False) -> X1 = X3 -> (k4_decomp_1 X2 X1) = (k5_decomp_1 X2 X1) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k4_decomp_1 X1 (esk7_2 X2 X1)) = (k5_decomp_1 X1 (esk7_2 X2 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_hidden X2 (a_1_14_decomp_1 X1) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k4_decomp_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_tops_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_pre_topc X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_decomp_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_decomp_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_decomp_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 (a_1_4_decomp_1 X2) -> False) -> X1 = X3 -> v2_pre_topc X2 -> l1_pre_topc X2 -> v3_decomp_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 (a_1_3_decomp_1 X2) -> False) -> X1 = X3 -> v2_pre_topc X2 -> l1_pre_topc X2 -> v4_decomp_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, ((k1_tops_1 X1 (k1_tops_1 X1 X2)) = (k1_tops_1 X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k2_pre_topc X1 (k2_pre_topc X1 X2)) = (k2_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_tops_1 X1 X2) -> False) -> l1_pre_topc X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk20_2 X3 X2) -> False)
  -> (forall X2 X1, (v4_pre_topc (k2_pre_topc X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc (k1_tops_1 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk9_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_1_4_decomp_1 X2) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk8_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_1_3_decomp_1 X2) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk7_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_1_14_decomp_1 X2) -> False)
  -> (forall X1 X2, (v4_decomp_1 X1 X2 -> False) -> (k5_decomp_1 X2 X1) = X1 -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v3_decomp_1 X1 X2 -> False) -> (k4_decomp_1 X2 X1) = X1 -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, ((k4_decomp_1 X2 X1) = X1 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v3_decomp_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, ((k5_decomp_1 X2 X1) = X1 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v4_decomp_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (r1_tarski (k1_tops_1 X1 X2) X2 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (r1_tarski X2 (k2_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v4_decomp_1 (esk8_2 X1 X2) X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_1_3_decomp_1 X2) -> False)
  -> (forall X1 X2, (v3_decomp_1 (esk9_2 X1 X2) X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_1_4_decomp_1 X2) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) X2 -> False) -> r1_tarski X3 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk2_2 X1 X2) X2 -> False)
  -> (forall X1, (m1_subset_1 (k9_decomp_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (k20_decomp_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (k10_decomp_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk20_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, ((esk9_2 X1 X2) = X1 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_1_4_decomp_1 X2) -> False)
  -> (forall X1 X2, ((esk8_2 X1 X2) = X1 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_1_3_decomp_1 X2) -> False)
  -> (forall X1 X2, ((esk7_2 X1 X2) = X1 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_1_14_decomp_1 X2) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk2_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_tops_1 (esk19_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk18_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk14_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk14_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk12_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk10_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v2_tops_1 (esk17_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k20_decomp_1 X1) = (a_1_14_decomp_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, ((k10_decomp_1 X1) = (a_1_4_decomp_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, ((k9_decomp_1 X1) = (a_1_3_decomp_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk11_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> ((k9_subset_1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) (k10_decomp_1 esk1_0) (k20_decomp_1 esk1_0)) = (k9_decomp_1 esk1_0) -> False)
  -> (forall X1, v1_subset_1 (esk15_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk13_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk5_0 -> False) -> False)
  -> ((l1_pre_topc esk4_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> False.
Admitted.
