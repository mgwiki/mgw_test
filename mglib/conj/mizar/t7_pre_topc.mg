(** $I sig/MizarPreamble.mgs **)

Theorem t7_pre_topc:
 forall esk7_2:set -> set -> set,
 forall v1_pre_topc:set -> prop,
 forall k1_pre_topc:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall g1_pre_topc:set -> set -> set,
 forall v2_pre_topc:set -> prop,
 forall esk20_1:set -> set,
 forall esk19_1:set -> set,
 forall esk17_1:set -> set,
 forall k1_xboole_0:set,
 forall esk18_1:set -> set,
 forall esk16_0:set,
 forall esk11_1:set -> set,
 forall esk9_0:set,
 forall esk8_0:set,
 forall esk12_0:set,
 forall esk14_0:set,
 forall esk15_1:set -> set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk10_1:set -> set,
 forall esk13_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall k2_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall u1_pre_topc:set -> set,
 forall l1_pre_topc:set -> prop,
 forall m1_pre_topc:set -> set -> prop,
     (forall X3 X2 X1, (m1_pre_topc X2 X1 -> False) -> (esk6_2 X1 X2) = (k9_subset_1 (u1_struct_0 X2) X3 (k2_struct_0 X2)) -> l1_pre_topc X2 -> l1_pre_topc X1 -> r2_hidden X3 (u1_pre_topc X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> r1_tarski (k2_struct_0 X2) (k2_struct_0 X1) -> r2_hidden (esk6_2 X1 X2) (u1_pre_topc X2) -> False)
  -> (forall X1 X2 X3 X4, (r2_hidden X3 (u1_pre_topc X4) -> False) -> X3 = (k9_subset_1 (u1_struct_0 X4) X1 (k2_struct_0 X4)) -> l1_pre_topc X4 -> l1_pre_topc X2 -> m1_pre_topc X4 X2 -> r2_hidden X1 (u1_pre_topc X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1 X3, ((k9_subset_1 (u1_struct_0 X2) (esk5_3 X3 X2 X1) (k2_struct_0 X2)) = X1 -> False) -> l1_pre_topc X3 -> l1_pre_topc X2 -> m1_pre_topc X2 X3 -> r2_hidden X1 (u1_pre_topc X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (esk5_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> r2_hidden X3 (u1_pre_topc X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (r2_hidden (esk5_3 X1 X2 X3) (u1_pre_topc X1) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> r2_hidden X3 (u1_pre_topc X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, ((k9_subset_1 (u1_struct_0 X2) (esk7_2 X1 X2) (k2_struct_0 X2)) = (esk6_2 X1 X2) -> False) -> (m1_pre_topc X2 X1 -> False) -> (r2_hidden (esk6_2 X1 X2) (u1_pre_topc X2) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> r1_tarski (k2_struct_0 X2) (k2_struct_0 X1) -> False)
  -> (forall X1 X2, (m1_pre_topc X2 X1 -> False) -> (r2_hidden (esk6_2 X1 X2) (u1_pre_topc X2) -> False) -> (m1_subset_1 (esk7_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> r1_tarski (k2_struct_0 X2) (k2_struct_0 X1) -> False)
  -> (forall X1 X2, (m1_pre_topc X2 X1 -> False) -> (r2_hidden (esk6_2 X1 X2) (u1_pre_topc X2) -> False) -> (r2_hidden (esk7_2 X1 X2) (u1_pre_topc X1) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> r1_tarski (k2_struct_0 X2) (k2_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (m1_pre_topc X2 X1 -> False) -> (m1_subset_1 (esk6_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> r1_tarski (k2_struct_0 X2) (k2_struct_0 X1) -> False)
  -> (forall X2 X1 X3, ((k2_struct_0 X1) = X3 -> False) -> X1 = (k1_pre_topc X2 X3) -> l1_pre_topc X2 -> v1_pre_topc X1 -> m1_pre_topc X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (X1 = (k1_pre_topc X3 X2) -> False) -> (k2_struct_0 X1) = X2 -> l1_pre_topc X3 -> v1_pre_topc X1 -> m1_pre_topc X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_pre_topc (k1_pre_topc X1 X2) X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_pre_topc X1 X3) = (g1_pre_topc X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_pre_topc X3 X1) = (g1_pre_topc X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X2 X1, (v1_pre_topc (k1_pre_topc X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_pre_topc (k1_pre_topc X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_pre_topc (k1_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (l1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1, (m1_subset_1 (u1_pre_topc X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r1_tarski (k2_struct_0 X1) (k2_struct_0 X2) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> m1_pre_topc X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, l1_struct_0 X1 -> v1_subset_1 (k2_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (k2_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) = X1 -> False) -> l1_pre_topc X1 -> v1_pre_topc X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v2_pre_topc X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = X1 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (m1_pre_topc (esk20_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1 X2, (l1_pre_topc X2 -> False) -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (u1_pre_topc X1) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (m1_pre_topc (esk17_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk10_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_pre_topc (esk20_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (esk20_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v1_pre_topc (esk17_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_struct_0 X1) = (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k1_pre_topc (k1_pre_topc esk1_0 esk3_0) esk4_0) = (k1_pre_topc esk1_0 esk2_0) -> False)
  -> (forall X1, v1_subset_1 (esk18_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 (k1_pre_topc esk1_0 esk3_0))) -> False) -> False)
  -> (forall X2 X3 X1, ((k3_xboole_0 (k3_xboole_0 X1 X2) X3) = (k3_xboole_0 X1 (k3_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((r1_tarski esk2_0 esk3_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk15_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_pre_topc esk12_0 -> False) -> False)
  -> ((l1_pre_topc esk12_0 -> False) -> False)
  -> ((l1_pre_topc esk8_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> ((esk4_0 = esk2_0 -> False) -> False)
  -> False.
Admitted.
