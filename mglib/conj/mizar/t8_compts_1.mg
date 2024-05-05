(** $I sig/MizarPreamble.mgs **)

Theorem t8_compts_1:
 forall k2_xboole_0:set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk8_3:set -> set -> set -> set,
 forall v2_compts_1:set -> set -> prop,
 forall v1_tops_2:set -> set -> prop,
 forall m1_setfam_1:set -> set -> prop,
 forall l1_pre_topc:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk3_2:set -> set -> set,
 forall v1_compts_1:set -> prop,
 forall k4_subset_1:set -> set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk4_1:set -> set,
 forall k3_subset_1:set -> set -> set,
 forall k2_struct_0:set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk5_2:set -> set -> set,
 forall k6_domain_1:set -> set -> set,
 forall k3_tarski:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk22_1:set -> set,
 forall v5_finset_1:set -> prop,
 forall esk25_1:set -> set,
 forall esk21_1:set -> set,
 forall esk15_1:set -> set,
 forall v1_tops_1:set -> set -> prop,
 forall k1_xboole_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk19_0:set,
 forall esk13_1:set -> set,
 forall esk11_0:set,
 forall esk16_0:set,
 forall esk10_0:set,
 forall o_0_0_xboole_0:set,
 forall esk12_1:set -> set,
 forall esk18_1:set -> set,
 forall esk14_0:set,
 forall esk27_0:set,
 forall esk20_1:set -> set,
 forall esk17_1:set -> set,
 forall esk23_1:set -> set,
 forall esk26_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk24_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall v2_tops_1:set -> set -> prop,
 forall v4_pre_topc:set -> set -> prop,
 forall v3_pre_topc:set -> set -> prop,
 forall esk9_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k5_setfam_1:set -> set -> set,
 forall k7_subset_1:set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall u1_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall l1_struct_0:set -> prop,
     (forall X2 X3 X1, (r1_tarski (k7_subset_1 (u1_struct_0 X1) (k5_setfam_1 (u1_struct_0 X1) X2) (k5_setfam_1 (u1_struct_0 X1) X3)) (k5_setfam_1 (u1_struct_0 X1) (k7_subset_1 (k1_zfmisc_1 (u1_struct_0 X1)) X2 X3)) -> False) -> l1_struct_0 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (esk8_3 X1 X2 X3) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> v2_compts_1 X2 X1 -> m1_setfam_1 X3 X2 -> v1_tops_2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (m1_setfam_1 (esk8_3 X1 X2 X3) X2 -> False) -> l1_pre_topc X1 -> v2_compts_1 X2 X1 -> m1_setfam_1 X3 X2 -> v1_tops_2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X2 X3 X1, (r1_tarski (esk8_3 X1 X2 X3) X3 -> False) -> l1_pre_topc X1 -> v2_compts_1 X2 X1 -> m1_setfam_1 X3 X2 -> v1_tops_2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X2 X3 X1, (v1_finset_1 (esk8_3 X1 X2 X3) -> False) -> l1_pre_topc X1 -> v2_compts_1 X2 X1 -> m1_setfam_1 X3 X2 -> v1_tops_2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X1 X3 X2, (v2_compts_1 X3 X2 -> False) -> l1_pre_topc X2 -> v1_finset_1 X1 -> m1_setfam_1 X1 X3 -> r1_tarski X1 (esk9_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk3_2 X1 X2) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> v1_compts_1 X1 -> v1_tops_2 X2 X1 -> m1_setfam_1 X2 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X1 X3 X2, (v3_pre_topc X3 X2 -> False) -> l1_pre_topc X2 -> r2_hidden X3 X1 -> v1_tops_2 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X2 X1, (m1_setfam_1 (esk3_2 X1 X2) (u1_struct_0 X1) -> False) -> l1_pre_topc X1 -> v1_compts_1 X1 -> v1_tops_2 X2 X1 -> m1_setfam_1 X2 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X2 X1, (r1_tarski (esk3_2 X1 X2) X2 -> False) -> l1_pre_topc X1 -> v1_compts_1 X1 -> v1_tops_2 X2 X1 -> m1_setfam_1 X2 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 (esk3_2 X1 X2) -> False) -> l1_pre_topc X1 -> v1_compts_1 X1 -> v1_tops_2 X2 X1 -> m1_setfam_1 X2 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X2 X1, (v1_tops_2 X2 X1 -> False) -> l1_pre_topc X1 -> v3_pre_topc (esk6_2 X1 X2) X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_compts_1 X2 -> False) -> l1_pre_topc X2 -> v1_finset_1 X1 -> r1_tarski X1 (esk4_1 X2) -> m1_setfam_1 X1 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X2 X1, (v1_tops_2 X2 X1 -> False) -> (m1_subset_1 (esk6_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X2 X1, ((k4_subset_1 (u1_struct_0 X1) X2 (k3_subset_1 (u1_struct_0 X1) X2)) = (k2_struct_0 X1) -> False) -> l1_struct_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v2_compts_1 X2 X1 -> False) -> (m1_subset_1 (esk9_2 X1 X2) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> v3_pre_topc (k3_subset_1 (u1_struct_0 X1) X2) X1 -> False)
  -> (forall X2 X1, (v1_tops_2 X2 X1 -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X1 X2, (v3_pre_topc (k3_subset_1 (u1_struct_0 X2) X1) X2 -> False) -> l1_pre_topc X2 -> v4_pre_topc X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v2_compts_1 X2 X1 -> False) -> (v1_tops_2 (esk9_2 X1 X2) X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_compts_1 X2 X1 -> False) -> (m1_setfam_1 (esk9_2 X1 X2) X2 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk5_2 X1 X2) = X1 -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (m1_setfam_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = X2 -> False) -> m1_setfam_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k4_xboole_0 X1 X3) (k4_xboole_0 X2 X3) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) (k2_xboole_0 X2 X3) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_compts_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_subset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_compts_1 X1 -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k6_domain_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 (k3_subset_1 X2 X1)) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk5_2 X1 X2) = X1 -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 X1) = (k4_xboole_0 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, l1_struct_0 X1 -> v1_subset_1 (k2_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (m1_setfam_1 X2 X1 -> False) -> r1_tarski X1 (k3_tarski X2) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (k2_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, ((k6_domain_1 X1 X2) = (k1_tarski X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v5_finset_1 (k2_xboole_0 X1 X2) -> False) -> v5_finset_1 X2 -> v5_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_xboole_0 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X2 (k3_tarski X1) -> False) -> m1_setfam_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_compts_1 X1 -> False) -> (m1_setfam_1 (esk4_1 X1) (u1_struct_0 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k4_xboole_0 X1 X2) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_compts_1 X1 -> False) -> (v1_tops_2 (esk4_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_tops_1 (esk22_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_tops_1 (k2_struct_0 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_tops_1 (esk24_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (k3_tarski X1) -> False) -> v1_finset_1 X1 -> v5_finset_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk26_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk25_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v5_finset_1 (k1_tarski X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_struct_0 X1) = (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk20_1 X1) X1 -> False)
  -> (v2_compts_1 esk2_0 esk1_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (forall X2 X1, ((k2_xboole_0 (k3_tarski X1) (k3_tarski X2)) = (k3_tarski (k2_xboole_0 X1 X2)) -> False) -> False)
  -> (forall X1 X2, ((k4_xboole_0 (k2_xboole_0 X1 X2) X2) = (k4_xboole_0 X1 X2) -> False) -> False)
  -> (forall X1 X2, (r1_tarski (k4_xboole_0 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_setfam_1 (esk12_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((v4_pre_topc esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, ((k3_tarski (k1_tarski X1)) = X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (k1_tarski X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk18_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk11_0 -> False) -> False)
  -> ((v5_finset_1 esk27_0 -> False) -> False)
  -> ((v1_finset_1 esk27_0 -> False) -> False)
  -> ((v1_finset_1 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_compts_1 esk1_0 -> False) -> False)
  -> ((l1_pre_topc esk10_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
