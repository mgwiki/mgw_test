(** $I sig/MizarPreamble.mgs **)

Theorem t21_ff_siec:
 forall l1_petri:set -> prop,
 forall v1_net_1:set -> prop,
 forall k1_net_1:set -> set,
 forall k5_relat_1:set -> set -> set,
 forall u1_struct_0:set -> set,
 forall u2_petri:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v8_relat_2:set -> prop,
 forall v2_relat_2:set -> prop,
 forall v1_partit_2:set -> prop,
 forall esk3_0:set,
 forall esk7_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk5_1:set -> set,
 forall esk8_2:set -> set -> set,
 forall esk6_0:set,
 forall l1_struct_0:set -> prop,
 forall l5_struct_0:set -> prop,
 forall v5_relat_2:set -> prop,
 forall v3_relat_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v2_relat_1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall u1_petri:set -> set,
 forall u4_struct_0:set -> set,
 forall k4_relat_1:set -> set,
 forall k2_net_1:set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall k2_relat_1:set -> set,
 forall k10_ff_siec:set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall k1_xboole_0:set,
 forall k3_relat_1:set -> set -> set,
 forall esk1_0:set,
 forall k9_ff_siec:set -> set,
     ((k3_relat_1 (k9_ff_siec esk1_0) (k9_ff_siec esk1_0)) = (k9_ff_siec esk1_0) -> (k3_relat_1 (k4_xboole_0 (k9_ff_siec esk1_0) (k4_relat_1 (k2_net_1 esk1_0))) (k9_ff_siec esk1_0)) = k1_xboole_0 -> (k2_xboole_0 (k2_xboole_0 (k9_ff_siec esk1_0) (k2_relat_1 (k9_ff_siec esk1_0))) (k4_relat_1 (k2_net_1 esk1_0))) = (k2_xboole_0 (k10_ff_siec esk1_0) (k2_relat_1 (k10_ff_siec esk1_0))) -> False)
  -> (forall X1, ((k2_xboole_0 (k2_xboole_0 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1))) (k4_relat_1 (u1_struct_0 X1))) = (k9_ff_siec X1) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k4_xboole_0 (k2_xboole_0 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) (k4_relat_1 (u4_struct_0 X1))) (k4_relat_1 (k2_net_1 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k4_xboole_0 (k2_xboole_0 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) (k4_relat_1 (u1_struct_0 X1))) (k4_relat_1 (k2_net_1 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k4_xboole_0 (k2_xboole_0 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) (k4_relat_1 (u4_struct_0 X1))) (k4_relat_1 (k2_net_1 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k4_xboole_0 (k2_xboole_0 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) (k4_relat_1 (u1_struct_0 X1))) (k4_relat_1 (k2_net_1 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k2_xboole_0 (k2_relat_1 (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1))) (k2_relat_1 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)))) = (k2_relat_1 (k1_net_1 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k2_xboole_0 (k2_relat_1 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1))) (k2_relat_1 (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)))) = (k2_relat_1 (k1_net_1 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k4_xboole_0 (k2_xboole_0 (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) (k4_relat_1 (u4_struct_0 X1))) (k4_relat_1 (k2_net_1 X1))) = (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k4_xboole_0 (k2_xboole_0 (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) (k4_relat_1 (u1_struct_0 X1))) (k4_relat_1 (k2_net_1 X1))) = (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k4_xboole_0 (k2_xboole_0 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) (k4_relat_1 (u4_struct_0 X1))) (k4_relat_1 (k2_net_1 X1))) = (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k4_xboole_0 (k2_xboole_0 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) (k4_relat_1 (u1_struct_0 X1))) (k4_relat_1 (k2_net_1 X1))) = (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) (k4_relat_1 (u1_struct_0 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) (k4_relat_1 (u4_struct_0 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) (k4_relat_1 (u4_struct_0 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k4_relat_1 (u4_struct_0 X1)) (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k4_relat_1 (u1_struct_0 X1)) (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, (m1_subset_1 (u2_petri X1) (k1_zfmisc_1 (k2_zfmisc_1 (u4_struct_0 X1) (u1_struct_0 X1))) -> False) -> l1_petri X1 -> False)
  -> (forall X1, (m1_subset_1 (u1_petri X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u4_struct_0 X1))) -> False) -> l1_petri X1 -> False)
  -> (forall X1, ((k2_xboole_0 (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1))) = (k1_net_1 X1) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k2_xboole_0 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1))) = (k1_net_1 X1) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1 X2 X3, ((k2_xboole_0 (k3_relat_1 X1 X3) (k3_relat_1 X2 X3)) = (k3_relat_1 (k2_xboole_0 X1 X2) X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2 X3, ((k2_xboole_0 (k3_relat_1 X1 X2) (k3_relat_1 X1 X3)) = (k3_relat_1 X1 (k2_xboole_0 X2 X3)) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) (k4_relat_1 (u1_struct_0 X1))) = (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) (k4_relat_1 (u4_struct_0 X1))) = (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) (k4_relat_1 (u4_struct_0 X1))) = (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k4_relat_1 (u4_struct_0 X1)) (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1))) = (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k4_relat_1 (u1_struct_0 X1)) (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1))) = (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) (k4_relat_1 (u4_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) (k4_relat_1 (u1_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k4_relat_1 (u4_struct_0 X1)) (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k4_relat_1 (u1_struct_0 X1)) (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k2_relat_1 (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u1_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k2_relat_1 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1))) = (k5_relat_1 (k2_relat_1 (k1_net_1 X1)) (u4_struct_0 X1)) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1)) (k4_relat_1 (u4_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1)) (k4_relat_1 (u1_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k4_relat_1 (u4_struct_0 X1)) (k5_relat_1 (k1_net_1 X1) (u1_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, ((k3_relat_1 (k4_relat_1 (u1_struct_0 X1)) (k5_relat_1 (k1_net_1 X1) (u4_struct_0 X1))) = k1_xboole_0 -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k2_xboole_0 (k2_relat_1 X1) (k2_relat_1 X2)) = (k2_relat_1 (k2_xboole_0 X1 X2)) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v5_relat_1 (k5_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v4_relat_1 (k5_relat_1 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v4_relat_1 (k5_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k5_relat_1 (k5_relat_1 X1 X2) X2) = (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1, ((k2_xboole_0 (k1_net_1 X1) (k4_relat_1 (k2_net_1 X1))) = (k10_ff_siec X1) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1 X2, (v2_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (r1_tarski (k4_relat_1 X1) (k4_relat_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k5_relat_1 X1 X2) = X1 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v3_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((k2_xboole_0 (u1_petri X1) (u2_petri X1)) = (k1_net_1 X1) -> False) -> l1_petri X1 -> False)
  -> (forall X1, ((k2_xboole_0 (u1_struct_0 X1) (u4_struct_0 X1)) = (k2_net_1 X1) -> False) -> l1_petri X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k4_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_relat_1 (k10_ff_siec X1) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, (v1_relat_1 (k9_ff_siec X1) -> False) -> v1_net_1 X1 -> l1_petri X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v5_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, ((k2_relat_1 (k2_relat_1 X1)) = X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k1_net_1 X1) -> False) -> l1_petri X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_relat_1 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k2_relat_1 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (l5_struct_0 X1 -> False) -> l1_petri X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk6_0 -> False)
  -> (forall X2 X1 X3, ((k2_xboole_0 (k2_xboole_0 X1 X3) (k2_xboole_0 X2 X3)) = (k2_xboole_0 (k2_xboole_0 X1 X2) X3) -> False) -> False)
  -> (forall X2 X1 X3, ((k2_xboole_0 (k4_xboole_0 X1 X3) (k4_xboole_0 X2 X3)) = (k4_xboole_0 (k2_xboole_0 X1 X2) X3) -> False) -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k2_xboole_0 X1 X2) X3) = (k2_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk8_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk8_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X1, ((k3_relat_1 (k4_relat_1 X1) (k4_relat_1 X1)) = (k4_relat_1 X1) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk8_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_relat_1 (k4_relat_1 X1)) = (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_partit_2 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk3_0 -> False) -> False)
  -> ((l5_struct_0 esk4_0 -> False) -> False)
  -> ((v2_relat_1 esk7_0 -> False) -> False)
  -> ((v1_relat_1 esk7_0 -> False) -> False)
  -> ((v1_relat_1 esk6_0 -> False) -> False)
  -> ((l1_petri esk2_0 -> False) -> False)
  -> ((l1_petri esk1_0 -> False) -> False)
  -> ((v1_net_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
