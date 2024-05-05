(** $I sig/MizarPreamble.mgs **)

Theorem t20_connsp_1:
 forall k1_struct_0:set -> set,
 forall k2_struct_0:set -> set,
 forall v1_connsp_1:set -> prop,
 forall r1_xboole_0:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall esk6_1:set -> set,
 forall esk5_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk11_1:set -> set,
 forall v2_relat_1:set -> prop,
 forall esk10_0:set,
 forall esk13_0:set,
 forall o_0_0_xboole_0:set,
 forall esk7_0:set,
 forall esk12_0:set,
 forall esk8_0:set,
 forall esk9_1:set -> set,
 forall esk14_1:set -> set,
 forall esk15_0:set,
 forall esk16_1:set -> set,
 forall k1_xboole_0:set,
 forall v3_relat_1:set -> prop,
 forall esk17_1:set -> set,
 forall v1_relat_1:set -> prop,
 forall esk18_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v4_pre_topc:set -> set -> prop,
 forall k7_subset_1:set -> set -> set -> set,
 forall esk20_2:set -> set -> set,
 forall esk19_2:set -> set -> set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall l1_pre_topc:set -> prop,
 forall r1_connsp_1:set -> set -> set -> prop,
 forall k4_subset_1:set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v2_connsp_1:set -> set -> prop,
 forall v2_pre_topc:set -> prop,
 forall r1_tarski:set -> set -> prop,
     (forall X3 X1 X2 X4, (r1_tarski X2 X4 -> False) -> (r1_tarski X2 X3 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_connsp_1 X2 X1 -> r1_connsp_1 X1 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> r1_tarski X2 (k4_subset_1 (u1_struct_0 X1) X3 X4) -> False)
  -> (forall X3 X4 X2 X1, (r1_connsp_1 X1 X2 (k4_subset_1 (u1_struct_0 X1) X3 X4) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X4 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X5 X4 X1, (r1_connsp_1 X1 X4 X5 -> False) -> l1_pre_topc X1 -> r1_tarski X5 X3 -> r1_tarski X4 X2 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X4 X2, (X4 = (k1_struct_0 X2) -> False) -> (X3 = (k1_struct_0 X2) -> False) -> X1 = (k4_subset_1 (u1_struct_0 X2) X3 X4) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v2_connsp_1 X1 X2 -> r1_connsp_1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (v2_connsp_1 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk3_0) esk1_0 -> v2_connsp_1 (k4_subset_1 (u1_struct_0 esk1_0) esk2_0 esk4_0) esk1_0 -> False)
  -> (forall X2 X3 X1, (X3 = (k1_struct_0 X1) -> False) -> (X2 = (k1_struct_0 X1) -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (k2_struct_0 X1) -> l1_pre_topc X1 -> v1_connsp_1 X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (r1_connsp_1 X1 X3 X2 -> False) -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X3, (r1_xboole_0 X2 X3 -> False) -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, ((k4_subset_1 (u1_struct_0 X2) (esk19_2 X2 X1) (esk20_2 X2 X1)) = X1 -> False) -> (v2_connsp_1 X1 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v2_connsp_1 X2 X1 -> False) -> (r1_connsp_1 X1 (esk19_2 X1 X2) (esk20_2 X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v2_connsp_1 X2 X1 -> False) -> (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_connsp_1 X2 X1 -> False) -> (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v2_connsp_1 X2 X1 -> False) -> (esk20_2 X1 X2) = (k1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_connsp_1 X2 X1 -> False) -> (esk19_2 X1 X2) = (k1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 X2 -> False) -> r1_xboole_0 X1 X3 -> r1_tarski X1 (k2_xboole_0 X2 X3) -> False)
  -> (forall X1, ((k4_subset_1 (u1_struct_0 X1) (esk5_1 X1) (esk6_1 X1)) = (k2_struct_0 X1) -> False) -> (v1_connsp_1 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (v1_connsp_1 X1 -> False) -> (r1_connsp_1 X1 (esk5_1 X1) (esk6_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 (k4_xboole_0 X2 X1)) = X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, (v1_connsp_1 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_connsp_1 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, l1_struct_0 X1 -> v1_subset_1 (k2_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (k1_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (m1_subset_1 (k2_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k4_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v4_pre_topc (esk18_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_connsp_1 X1 -> False) -> (esk6_1 X1) = (k1_struct_0 X1) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_connsp_1 X1 -> False) -> (esk5_1 X1) = (k1_struct_0 X1) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk11_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_struct_0 X1) = (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k1_struct_0 X1) = k1_xboole_0 -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk16_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (((k7_subset_1 (u1_struct_0 esk1_0) (k2_struct_0 esk1_0) esk2_0) = (k4_subset_1 (u1_struct_0 esk1_0) esk3_0 esk4_0) -> False) -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k2_xboole_0 X1 X2) X3) = (k2_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> ((r1_connsp_1 esk1_0 esk3_0 esk4_0 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((v2_connsp_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk14_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk8_0 -> False) -> False)
  -> ((v2_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_connsp_1 esk1_0 -> False) -> False)
  -> ((l1_pre_topc esk7_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
