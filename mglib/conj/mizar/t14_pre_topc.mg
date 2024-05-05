(** $I sig/MizarPreamble.mgs **)

Theorem t14_pre_topc:
 forall esk24_2:set -> set -> set,
 forall l1_pre_topc:set -> prop,
 forall k7_subset_1:set -> set -> set -> set,
 forall k2_struct_0:set -> set,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v2_pre_topc:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall l1_struct_0:set -> prop,
 forall esk7_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk25_2:set -> set -> set,
 forall esk23_1:set -> set,
 forall k1_struct_0:set -> set,
 forall esk17_1:set -> set,
 forall esk21_1:set -> set,
 forall esk20_0:set,
 forall esk19_1:set -> set,
 forall esk15_0:set,
 forall esk14_0:set,
 forall esk18_0:set,
 forall esk16_1:set -> set,
 forall esk22_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk9_2:set -> set -> set,
 forall k6_setfam_1:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall k1_setfam_1:set -> set,
 forall k1_xboole_0:set,
 forall v3_pre_topc:set -> set -> prop,
 forall v4_pre_topc:set -> set -> prop,
 forall k5_setfam_1:set -> set -> set,
 forall esk3_1:set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall esk5_1:set -> set,
 forall esk4_1:set -> set,
 forall u1_pre_topc:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk13_3:set -> set -> set -> set,
 forall k4_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk13_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk13_3 X1 X2 X3) X3 -> r2_hidden (esk13_3 X1 X2 X3) X1 -> False)
  -> (forall X3 X2 X1, (r2_hidden X2 (esk24_2 X1 X3) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> r2_hidden (k7_subset_1 (u1_struct_0 X1) (k2_struct_0 X1) X2) X3 -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k5_setfam_1 (u1_struct_0 X1) (esk3_1 X1)) (u1_pre_topc X1) -> r2_hidden (k9_subset_1 (u1_struct_0 X1) (esk4_1 X1) (esk5_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (m1_subset_1 (esk3_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k9_subset_1 (u1_struct_0 X1) (esk4_1 X1) (esk5_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X1 X3 X2, (r2_hidden (k7_subset_1 (u1_struct_0 X2) (k2_struct_0 X2) X1) X3 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (esk24_2 X2 X3) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r1_tarski (esk3_1 X1) (u1_pre_topc X1) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k9_subset_1 (u1_struct_0 X1) (esk4_1 X1) (esk5_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X2 X3 X1, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk13_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk13_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden (k9_subset_1 (u1_struct_0 X2) X1 X3) (u1_pre_topc X2) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X3 (u1_pre_topc X2) -> r2_hidden X1 (u1_pre_topc X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> v3_pre_topc (k7_subset_1 (u1_struct_0 X1) (k2_struct_0 X1) X2) X1 -> False)
  -> (forall X2 X1, ((k7_subset_1 (u1_struct_0 X1) (k2_struct_0 X1) (k7_subset_1 (u1_struct_0 X1) (k2_struct_0 X1) X2)) = X2 -> False) -> l1_struct_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk13_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk13_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X2, (v3_pre_topc (k7_subset_1 (u1_struct_0 X2) (k2_struct_0 X2) X1) X2 -> False) -> l1_pre_topc X2 -> v4_pre_topc X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X3 = (k1_setfam_1 X2) -> r2_hidden X1 (esk6_3 X2 X3 X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (m1_subset_1 (esk5_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k5_setfam_1 (u1_struct_0 X1) (esk3_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k5_setfam_1 (u1_struct_0 X1) (esk3_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X1 X2, (r2_hidden (k5_setfam_1 (u1_struct_0 X2) X1) (u1_pre_topc X2) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_tarski X1 (u1_pre_topc X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk5_1 X1) (u1_pre_topc X1) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k5_setfam_1 (u1_struct_0 X1) (esk3_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk4_1 X1) (u1_pre_topc X1) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k5_setfam_1 (u1_struct_0 X1) (esk3_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk24_2 X1 X2) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> r2_hidden (esk7_2 X1 X2) (esk8_2 X1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (m1_subset_1 (esk5_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> (m1_subset_1 (esk3_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> (m1_subset_1 (esk3_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk11_2 X1 X2) X3 -> r2_hidden (esk11_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk10_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk10_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden X3 X2 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> X2 = (k1_setfam_1 X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk5_1 X1) (u1_pre_topc X1) -> False) -> (m1_subset_1 (esk3_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk4_1 X1) (u1_pre_topc X1) -> False) -> (m1_subset_1 (esk3_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> r2_hidden (esk25_2 X1 X2) X2 -> r2_hidden (esk25_2 X1 X2) X1 -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r1_tarski (esk3_1 X1) (u1_pre_topc X1) -> False) -> (m1_subset_1 (esk5_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r1_tarski (esk3_1 X1) (u1_pre_topc X1) -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> (r2_hidden (esk11_2 X1 X2) (esk12_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X1 -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X3 -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> r2_hidden X3 X1 -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk5_1 X1) (u1_pre_topc X1) -> False) -> (r1_tarski (esk3_1 X1) (u1_pre_topc X1) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk4_1 X1) (u1_pre_topc X1) -> False) -> (r1_tarski (esk3_1 X1) (u1_pre_topc X1) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1 X2, (v3_pre_topc X1 X2 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (u1_pre_topc X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (r2_hidden X1 (u1_pre_topc X2) -> False) -> l1_pre_topc X2 -> v3_pre_topc X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k6_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> (r2_hidden (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk25_2 X1 X2) X2 -> False) -> (r2_hidden (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k4_xboole_0 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v4_pre_topc X1 esk1_0 -> False) -> r2_hidden X1 esk2_0 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X1, (m1_subset_1 (u1_pre_topc X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k1_setfam_1 X4) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, ((k6_setfam_1 X2 X1) = (k1_setfam_1 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k4_xboole_0 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k4_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, l1_struct_0 X1 -> v1_subset_1 (k2_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (k2_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k1_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v4_pre_topc (esk23_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (u1_pre_topc X1) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 (k1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_struct_0 X1) = (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> X2 = k1_xboole_0 -> X1 = (k1_setfam_1 X2) -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, ((k1_struct_0 X1) = k1_xboole_0 -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = (k1_setfam_1 X2) -> False) -> X2 = k1_xboole_0 -> X1 = k1_xboole_0 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v4_pre_topc (k6_setfam_1 (u1_struct_0 esk1_0) esk2_0) esk1_0 -> False)
  -> (forall X1, v1_subset_1 (esk21_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 esk1_0))) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_pre_topc esk14_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> False.
Admitted.
