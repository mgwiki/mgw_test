(** $I sig/MizarPreamble.mgs **)

Theorem t20_pre_topc:
 forall v3_pre_topc:set -> set -> prop,
 forall r1_xboole_0:set -> set -> prop,
 forall esk12_3:set -> set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k4_subset_1:set -> set -> set -> set,
 forall k3_tarski:set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall l1_struct_0:set -> prop,
 forall k1_struct_0:set -> set,
 forall k1_xboole_0:set,
 forall esk21_1:set -> set,
 forall esk20_1:set -> set,
 forall esk19_0:set,
 forall esk15_1:set -> set,
 forall esk17_0:set,
 forall esk13_0:set,
 forall esk14_0:set,
 forall esk18_1:set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk16_1:set -> set,
 forall esk7_2:set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall esk4_1:set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall esk6_1:set -> set,
 forall esk5_1:set -> set,
 forall u1_pre_topc:set -> set,
 forall v2_pre_topc:set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall u1_struct_0:set -> set,
 forall esk10_4:set -> set -> set -> set -> set,
 forall l1_pre_topc:set -> prop,
 forall k2_pre_topc:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X2 X1 X4 X3, (r2_hidden X4 X3 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> X3 = (k2_pre_topc X1 X2) -> l1_pre_topc X1 -> r2_hidden X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X4 X3, (r2_hidden X4 X3 -> False) -> (v3_pre_topc (esk10_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k2_pre_topc X1 X2) -> l1_pre_topc X1 -> r2_hidden X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 (esk10_4 X2 X3 X4 X1) -> False) -> X4 = (k2_pre_topc X2 X3) -> l1_pre_topc X2 -> r2_hidden X1 (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2 X4 X3, (r2_hidden X4 X3 -> False) -> (r1_xboole_0 X1 (esk10_4 X2 X1 X3 X4) -> False) -> X3 = (k2_pre_topc X2 X1) -> l1_pre_topc X2 -> r2_hidden X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk9_3 X1 X2 X3) X3 -> r2_hidden (esk9_3 X1 X2 X3) X2 -> r2_hidden (esk9_3 X1 X2 X3) X1 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_pre_topc X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) (esk12_3 X1 X2 X3) -> False) -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r2_hidden (esk11_3 X1 X2 X3) X3 -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k2_pre_topc X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X3 -> False) -> l1_pre_topc X1 -> v3_pre_topc X4 X1 -> r1_xboole_0 X2 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r2_hidden (esk11_3 X1 X2 X3) X4 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_pre_topc X1 X2) -> False) -> (m1_subset_1 (esk12_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r2_hidden (esk11_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_pre_topc X1 X2) -> False) -> (v3_pre_topc (esk12_3 X1 X2 X3) X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r2_hidden (esk11_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X1 X2, (X3 = (k2_pre_topc X2 X1) -> False) -> (r1_xboole_0 X1 (esk12_3 X2 X1 X3) -> False) -> l1_pre_topc X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden (esk11_3 X2 X1 X3) X3 -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k5_setfam_1 (u1_struct_0 X1) (esk4_1 X1)) (u1_pre_topc X1) -> r2_hidden (k9_subset_1 (u1_struct_0 X1) (esk5_1 X1) (esk6_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k9_subset_1 (u1_struct_0 X1) (esk5_1 X1) (esk6_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r1_tarski (esk4_1 X1) (u1_pre_topc X1) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k9_subset_1 (u1_struct_0 X1) (esk5_1 X1) (esk6_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X1 X3 X2, (r2_hidden (k9_subset_1 (u1_struct_0 X2) X1 X3) (u1_pre_topc X2) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X3 (u1_pre_topc X2) -> r2_hidden X1 (u1_pre_topc X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X4 X5 X2, X2 = (k2_pre_topc X4 X5) -> l1_pre_topc X4 -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> v3_pre_topc X3 X4 -> r1_xboole_0 X5 X3 -> r2_hidden X1 (u1_struct_0 X4) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X4)) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_pre_topc X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (m1_subset_1 (esk6_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k5_setfam_1 (u1_struct_0 X1) (esk4_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (m1_subset_1 (esk5_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k5_setfam_1 (u1_struct_0 X1) (esk4_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_pre_topc X1 X2) (k2_pre_topc X1 X3) -> False) -> l1_pre_topc X1 -> r1_tarski X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (r2_hidden (k5_setfam_1 (u1_struct_0 X2) X1) (u1_pre_topc X2) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_tarski X1 (u1_pre_topc X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk6_1 X1) (u1_pre_topc X1) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k5_setfam_1 (u1_struct_0 X1) (esk4_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk5_1 X1) (u1_pre_topc X1) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> r2_hidden (k5_setfam_1 (u1_struct_0 X1) (esk4_1 X1)) (u1_pre_topc X1) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (m1_subset_1 (esk6_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (m1_subset_1 (esk5_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk6_1 X1) (u1_pre_topc X1) -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk5_1 X1) (u1_pre_topc X1) -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r1_tarski (esk4_1 X1) (u1_pre_topc X1) -> False) -> (m1_subset_1 (esk6_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r1_tarski (esk4_1 X1) (u1_pre_topc X1) -> False) -> (m1_subset_1 (esk5_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_pre_topc X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k2_pre_topc X1 (k2_pre_topc X1 X2)) = (k2_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk6_1 X1) (u1_pre_topc X1) -> False) -> (r1_tarski (esk4_1 X1) (u1_pre_topc X1) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1, (v2_pre_topc X1 -> False) -> (r2_hidden (esk5_1 X1) (u1_pre_topc X1) -> False) -> (r1_tarski (esk4_1 X1) (u1_pre_topc X1) -> False) -> l1_pre_topc X1 -> r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False)
  -> (forall X1 X2, (v3_pre_topc X1 X2 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (u1_pre_topc X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (r2_hidden X1 (u1_pre_topc X2) -> False) -> l1_pre_topc X2 -> v3_pre_topc X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) X2 -> False) -> r1_tarski X3 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (u1_pre_topc X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (k1_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (r2_hidden (u1_struct_0 X1) (u1_pre_topc X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (u1_pre_topc X1) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v1_xboole_0 (k1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, ((k1_struct_0 X1) = k1_xboole_0 -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k4_subset_1 (u1_struct_0 esk1_0) (k2_pre_topc esk1_0 esk2_0) (k2_pre_topc esk1_0 esk3_0)) = (k2_pre_topc esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0)) -> False)
  -> (forall X1, v1_subset_1 (esk20_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k3_xboole_0 X1 X2) (k3_xboole_0 X1 X3)) = (k3_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X3 X1, ((k3_xboole_0 (k3_xboole_0 X1 X2) X3) = (k3_xboole_0 X1 (k3_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk18_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_pre_topc esk13_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> False.
Admitted.
