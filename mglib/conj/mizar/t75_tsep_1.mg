(** $I sig/MizarPreamble.mgs **)

Theorem t75_tsep_1:
 forall r1_tarski:set -> set -> prop,
 forall v4_pre_topc:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall esk4_0:set,
 forall esk5_0:set,
 forall k3_xboole_0:set -> set -> set,
 forall v1_pre_topc:set -> prop,
 forall esk35_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall g1_pre_topc:set -> set -> set,
 forall l1_struct_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk32_1:set -> set,
 forall esk34_1:set -> set,
 forall esk23_1:set -> set,
 forall esk12_1:set -> set,
 forall esk28_1:set -> set,
 forall esk21_1:set -> set,
 forall k1_xboole_0:set,
 forall esk15_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk10_1:set -> set,
 forall v6_pre_topc:set -> prop,
 forall esk24_0:set,
 forall esk22_0:set,
 forall esk11_1:set -> set,
 forall esk14_0:set,
 forall esk8_0:set,
 forall esk13_0:set,
 forall esk16_0:set,
 forall esk9_0:set,
 forall esk18_0:set,
 forall esk25_1:set -> set,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk27_1:set -> set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk29_1:set -> set,
 forall esk30_1:set -> set,
 forall esk19_1:set -> set,
 forall esk20_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk17_1:set -> set,
 forall esk31_1:set -> set,
 forall esk26_1:set -> set,
 forall esk33_1:set -> set,
 forall u1_pre_topc:set -> set,
 forall v2_tops_1:set -> set -> prop,
 forall v3_tops_1:set -> set -> prop,
 forall v3_pre_topc:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall esk3_0:set,
 forall k2_tsep_1:set -> set -> set -> set,
 forall k1_tsep_1:set -> set -> set -> set,
 forall r1_tsep_1:set -> set -> prop,
 forall r3_tsep_1:set -> set -> set -> prop,
 forall esk2_0:set,
 forall v1_borsuk_1:set -> set -> prop,
 forall m1_pre_topc:set -> set -> prop,
 forall esk1_0:set,
 forall v2_struct_0:set -> prop,
 forall r1_xboole_0:set -> set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall esk37_3:set -> set -> set -> set,
 forall esk36_3:set -> set -> set -> set,
 forall k4_subset_1:set -> set -> set -> set,
 forall l1_pre_topc:set -> prop,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall r1_connsp_1:set -> set -> set -> prop,
 forall v2_pre_topc:set -> prop,
     (forall X3 X2 X1, (r1_xboole_0 (k9_subset_1 (u1_struct_0 X1) (esk36_3 X1 X2 X3) (esk37_3 X1 X2 X3)) (k4_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X5 X4 X2, (r1_connsp_1 X2 X4 X5 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v4_pre_topc X3 X2 -> v4_pre_topc X1 X2 -> r1_tarski X5 X3 -> r1_tarski X4 X1 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> r1_xboole_0 (k9_subset_1 (u1_struct_0 X2) X1 X3) (k4_subset_1 (u1_struct_0 X2) X4 X5) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> m1_pre_topc X2 esk1_0 -> m1_pre_topc X1 esk1_0 -> v1_borsuk_1 X2 esk1_0 -> v1_borsuk_1 X1 esk1_0 -> m1_pre_topc esk2_0 X1 -> m1_pre_topc esk3_0 X2 -> r3_tsep_1 esk1_0 esk2_0 esk3_0 -> r1_tsep_1 (k2_tsep_1 esk1_0 X1 X2) (k1_tsep_1 esk1_0 esk2_0 esk3_0) -> False)
  -> (forall X3 X2 X1, (r3_tsep_1 X1 X2 X3 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> r1_connsp_1 X1 (esk6_3 X1 X2 X3) (esk7_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk37_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk36_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v4_pre_topc (esk37_3 X1 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v4_pre_topc (esk36_3 X1 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 (esk37_3 X2 X3 X1) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_connsp_1 X2 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 (esk36_3 X2 X1 X3) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_connsp_1 X2 X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X5 X4 X1, (r1_connsp_1 X1 X4 X5 -> False) -> X5 = (u1_struct_0 X3) -> X4 = (u1_struct_0 X2) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> r3_tsep_1 X1 X2 X3 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> ((r1_tsep_1 esk4_0 esk5_0 -> False) -> (r3_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> (r1_tsep_1 (k2_tsep_1 esk1_0 esk4_0 esk5_0) (k1_tsep_1 esk1_0 esk2_0 esk3_0) -> False) -> False)
  -> (forall X2 X3 X1, (r1_connsp_1 X1 X3 X2 -> False) -> l1_pre_topc X1 -> r1_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (r3_tsep_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X3 X1, (r3_tsep_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> v2_struct_0 (k1_tsep_1 X1 X2 X3) -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> v2_struct_0 (k2_tsep_1 X1 X2 X3) -> False)
  -> (forall X2 X3 X4 X1, ((u1_struct_0 X1) = (k3_xboole_0 (u1_struct_0 X3) (u1_struct_0 X4)) -> False) -> (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (r1_tsep_1 X3 X4 -> False) -> X1 = (k2_tsep_1 X2 X3 X4) -> l1_pre_topc X2 -> v1_pre_topc X1 -> m1_pre_topc X4 X2 -> m1_pre_topc X3 X2 -> m1_pre_topc X1 X2 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> r1_tsep_1 X1 X2 -> m1_pre_topc X2 esk1_0 -> m1_pre_topc X1 esk1_0 -> v1_borsuk_1 X2 esk1_0 -> v1_borsuk_1 X1 esk1_0 -> m1_pre_topc esk2_0 X1 -> m1_pre_topc esk3_0 X2 -> r3_tsep_1 esk1_0 esk2_0 esk3_0 -> False)
  -> (forall X3 X1 X2 X4, (X1 = (k2_tsep_1 X4 X2 X3) -> False) -> (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (r1_tsep_1 X2 X3 -> False) -> (u1_struct_0 X1) = (k3_xboole_0 (u1_struct_0 X2) (u1_struct_0 X3)) -> l1_pre_topc X4 -> v1_pre_topc X1 -> m1_pre_topc X3 X4 -> m1_pre_topc X2 X4 -> m1_pre_topc X1 X4 -> False)
  -> (forall X2 X3 X4 X1, ((u1_struct_0 X1) = (k2_xboole_0 (u1_struct_0 X3) (u1_struct_0 X4)) -> False) -> (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> X1 = (k1_tsep_1 X2 X3 X4) -> l1_pre_topc X2 -> v1_pre_topc X1 -> m1_pre_topc X4 X2 -> m1_pre_topc X3 X2 -> m1_pre_topc X1 X2 -> False)
  -> (forall X3 X1 X2 X4, (X1 = (k1_tsep_1 X4 X2 X3) -> False) -> (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (u1_struct_0 X1) = (k2_xboole_0 (u1_struct_0 X2) (u1_struct_0 X3)) -> l1_pre_topc X4 -> v1_pre_topc X1 -> m1_pre_topc X3 X4 -> m1_pre_topc X2 X4 -> m1_pre_topc X1 X4 -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r3_tsep_1 X1 X3 X2 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> r3_tsep_1 X1 X2 X3 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_pre_topc (k1_tsep_1 X1 X2 X3) X1 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_pre_topc (k2_tsep_1 X1 X2 X3) X1 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_pre_topc (k1_tsep_1 X1 X2 X3) -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_pre_topc (k2_tsep_1 X1 X2 X3) -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1 X3, ((k1_tsep_1 X1 X2 X3) = (k1_tsep_1 X1 X3 X2) -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, ((esk7_3 X1 X2 X3) = (u1_struct_0 X3) -> False) -> (r3_tsep_1 X1 X2 X3 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X3 X1, ((esk6_3 X1 X2 X3) = (u1_struct_0 X2) -> False) -> (r3_tsep_1 X1 X2 X3 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_struct_0 (esk35_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_borsuk_1 (esk35_2 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_pre_topc (esk35_2 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v4_pre_topc X3 X2 -> False) -> X3 = (u1_struct_0 X1) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_pre_topc X1 X2 -> v1_borsuk_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (v1_borsuk_1 X1 X2 -> False) -> X3 = (u1_struct_0 X1) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_pre_topc X1 X2 -> v4_pre_topc X3 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, ((u1_struct_0 (esk35_2 X2 X1)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v4_pre_topc X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_pre_topc (esk35_2 X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (m1_pre_topc X1 X2 -> False) -> v2_pre_topc X3 -> l1_pre_topc X3 -> m1_pre_topc X2 X3 -> m1_pre_topc X1 X3 -> r1_tarski (u1_struct_0 X1) (u1_struct_0 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (r1_tarski (u1_struct_0 X1) (u1_struct_0 X2) -> False) -> v2_pre_topc X3 -> l1_pre_topc X3 -> m1_pre_topc X2 X3 -> m1_pre_topc X1 X3 -> m1_pre_topc X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v2_struct_0 (g1_pre_topc X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_pre_topc X1 X3) = (g1_pre_topc X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_pre_topc X3 X1) = (g1_pre_topc X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> v2_struct_0 (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (v1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (l1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (r1_tsep_1 X1 X2 -> False) -> l1_struct_0 X2 -> l1_struct_0 X1 -> r1_xboole_0 (u1_struct_0 X1) (u1_struct_0 X2) -> False)
  -> (forall X1, (m1_subset_1 (u1_pre_topc X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v1_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (u1_struct_0 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1 X2, (r1_xboole_0 (u1_struct_0 X1) (u1_struct_0 X2) -> False) -> l1_struct_0 X2 -> l1_struct_0 X1 -> r1_tsep_1 X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> ((v1_borsuk_1 esk5_0 esk1_0 -> False) -> (r3_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((v1_borsuk_1 esk4_0 esk1_0 -> False) -> (r3_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m1_pre_topc esk5_0 esk1_0 -> False) -> (r3_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m1_pre_topc esk4_0 esk1_0 -> False) -> (r3_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m1_pre_topc esk3_0 esk5_0 -> False) -> (r3_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m1_pre_topc esk2_0 esk4_0 -> False) -> (r3_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> ((r3_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> v2_struct_0 esk5_0 -> False)
  -> ((r3_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> v2_struct_0 esk4_0 -> False)
  -> (forall X1, (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_tsep_1 X2 X1 -> False) -> l1_struct_0 X2 -> l1_struct_0 X1 -> r1_tsep_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tops_1 (esk32_1 X1) X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) = X1 -> False) -> l1_pre_topc X1 -> v1_pre_topc X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v2_pre_topc X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk33_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk26_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_pre_topc (esk26_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_borsuk_1 (esk21_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_pre_topc (esk21_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk33_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk32_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_struct_0 (esk21_1 X1) -> False)
  -> (forall X1, (v3_tops_1 (esk34_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk31_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk23_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk23_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk17_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk12_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_borsuk_1 (esk15_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk29_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk15_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (l1_pre_topc X2 -> False) -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_pre_topc (esk27_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (u1_pre_topc X1) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (esk21_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_pre_topc (esk21_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk20_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk28_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> v2_struct_0 (esk27_1 X1) -> False)
  -> (forall X1, (v2_tops_1 (esk30_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk25_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk10_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_pre_topc (esk29_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_pre_topc (esk15_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (esk29_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (esk15_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk19_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (esk27_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> r1_tarski X1 k1_xboole_0 -> False)
  -> (forall X1, (v6_pre_topc X1 -> False) -> v2_struct_0 X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_pre_topc (esk25_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk22_0 -> False)
  -> (v2_struct_0 esk3_0 -> False)
  -> (v2_struct_0 esk2_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (r1_xboole_0 X1 k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((m1_pre_topc esk3_0 esk1_0 -> False) -> False)
  -> ((m1_pre_topc esk2_0 esk1_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk9_0 -> False) -> False)
  -> ((v1_pre_topc esk22_0 -> False) -> False)
  -> ((v1_pre_topc esk16_0 -> False) -> False)
  -> ((v1_pre_topc esk14_0 -> False) -> False)
  -> ((v1_pre_topc esk13_0 -> False) -> False)
  -> ((l1_pre_topc esk22_0 -> False) -> False)
  -> ((l1_pre_topc esk16_0 -> False) -> False)
  -> ((l1_pre_topc esk14_0 -> False) -> False)
  -> ((l1_pre_topc esk13_0 -> False) -> False)
  -> ((l1_pre_topc esk8_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk22_0 -> False) -> False)
  -> ((v2_pre_topc esk14_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> ((v2_struct_0 esk14_0 -> False) -> False)
  -> ((v2_struct_0 esk13_0 -> False) -> False)
  -> False.
Admitted.
