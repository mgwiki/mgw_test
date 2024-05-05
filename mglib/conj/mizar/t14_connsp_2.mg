(** $I sig/MizarPreamble.mgs **)

Theorem t14_connsp_2:
 forall esk2_0:set,
 forall esk3_0:set,
 forall r2_hidden:set -> set -> prop,
 forall k1_connsp_1:set -> set -> set,
 forall k1_tops_1:set -> set -> set,
 forall esk1_0:set,
 forall r1_connsp_2:set -> set -> prop,
 forall esk45_3:set -> set -> set -> set,
 forall esk4_1:set -> set,
 forall v2_connsp_1:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall esk43_2:set -> set -> set,
 forall v3_tops_1:set -> set -> prop,
 forall v2_tops_1:set -> set -> prop,
 forall v4_pre_topc:set -> set -> prop,
 forall k2_struct_0:set -> set,
 forall v1_pre_topc:set -> prop,
 forall g1_pre_topc:set -> set -> set,
 forall esk40_1:set -> set,
 forall esk29_1:set -> set,
 forall esk37_1:set -> set,
 forall esk19_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk22_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk21_1:set -> set,
 forall esk33_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk34_1:set -> set,
 forall esk35_1:set -> set,
 forall esk18_1:set -> set,
 forall esk27_1:set -> set,
 forall v6_pre_topc:set -> prop,
 forall esk24_1:set -> set,
 forall esk15_0:set,
 forall esk20_0:set,
 forall esk8_0:set,
 forall esk14_0:set,
 forall esk17_0:set,
 forall esk9_0:set,
 forall esk12_1:set -> set,
 forall esk23_0:set,
 forall esk26_0:set,
 forall esk28_1:set -> set,
 forall esk11_1:set -> set,
 forall v1_tops_1:set -> set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk32_1:set -> set,
 forall esk38_1:set -> set,
 forall k1_xboole_0:set,
 forall esk30_1:set -> set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk16_1:set -> set,
 forall esk36_1:set -> set,
 forall esk31_1:set -> set,
 forall esk13_1:set -> set,
 forall esk25_1:set -> set,
 forall esk41_1:set -> set,
 forall esk39_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall u1_pre_topc:set -> set,
 forall esk10_2:set -> set -> set,
 forall esk44_2:set -> set -> set,
 forall esk42_2:set -> set -> set,
 forall m1_pre_topc:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall v3_connsp_1:set -> set -> prop,
 forall r3_connsp_1:set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v2_pre_topc:set -> prop,
 forall v3_pre_topc:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k1_pre_topc:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall l1_pre_topc:set -> prop,
 forall m1_connsp_2:set -> set -> set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X2 X4 X3 X6 X5 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_connsp_2 X5 X1 X6 -> False) -> X4 = X5 -> X3 = X6 -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_connsp_2 X4 (k1_pre_topc X1 X2) X3 -> m1_subset_1 X3 (u1_struct_0 (k1_pre_topc X1 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 (k1_pre_topc X1 X2))) -> False)
  -> (forall X2 X5 X6 X3 X4 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_connsp_2 X4 (k1_pre_topc X1 X2) X3 -> False) -> X4 = X5 -> X3 = X6 -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_connsp_2 X5 X1 X6 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (u1_struct_0 (k1_pre_topc X1 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 (k1_pre_topc X1 X2))) -> False)
  -> (forall X1 X4 X3 X2, (r3_connsp_1 X2 X3 X4 -> False) -> X1 = X4 -> l1_pre_topc X2 -> v3_connsp_1 X1 (k1_pre_topc X2 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 (k1_pre_topc X2 X3))) -> False)
  -> (forall X1, X1 = esk2_0 -> r1_connsp_2 esk1_0 esk2_0 -> m1_subset_1 X1 (u1_struct_0 (k1_pre_topc esk1_0 esk3_0)) -> r2_hidden esk2_0 (k1_tops_1 (k1_pre_topc esk1_0 esk3_0) (k1_connsp_1 (k1_pre_topc esk1_0 esk3_0) X1)) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (esk7_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 (k1_pre_topc X1 X2))) -> False) -> l1_pre_topc X1 -> r3_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_connsp_2 X4 X1 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_2 X1 X2 -> r2_hidden X2 X4 -> m1_connsp_2 X3 X1 X2 -> r3_connsp_1 X1 X3 X4 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_connsp_2 (esk5_3 X1 X2 X3) X1 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_2 X1 X2 -> m1_connsp_2 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_connsp_2 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> v1_xboole_0 (esk45_3 X1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk5_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_2 X1 X2 -> m1_connsp_2 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r1_connsp_2 esk1_0 esk2_0 -> False) -> (r2_hidden esk2_0 (k1_tops_1 (k1_pre_topc esk1_0 X1) (k1_connsp_1 (k1_pre_topc esk1_0 X1) (esk4_1 X1))) -> False) -> v3_pre_topc X1 esk1_0 -> r2_hidden esk2_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_connsp_2 (esk45_3 X1 X2 X3) X1 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_connsp_2 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_connsp_1 (esk7_3 X1 X2 X3) (k1_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> r3_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (esk5_3 X1 X2 X3) X3 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_2 X1 X2 -> m1_connsp_2 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v2_connsp_1 (esk5_3 X1 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_connsp_2 X1 X2 -> m1_connsp_2 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk45_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_connsp_2 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (esk45_3 X1 X2 X3) X3 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_connsp_2 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (v3_pre_topc (esk45_3 X1 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_connsp_2 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (r1_connsp_2 X2 X3 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v2_connsp_1 X1 X2 -> m1_connsp_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X2) -> r1_tarski X1 (esk6_2 X2 X3) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, ((esk7_3 X1 X2 X3) = X3 -> False) -> l1_pre_topc X1 -> r3_connsp_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (k1_tops_1 X2 X1) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_connsp_2 X1 X2 X3 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_connsp_2 X3 X2 X1 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> r2_hidden X1 (k1_tops_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X3 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_connsp_2 X2 X1 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_connsp_2 X2 X1 X3 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> r2_hidden X3 X2 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r1_connsp_2 X1 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_connsp_2 (esk43_2 X1 X2) X1 X2 -> False)
  -> (forall X1 X2 X3 X4, (v2_connsp_1 X3 X4 -> False) -> X1 = X3 -> v2_pre_topc X2 -> l1_pre_topc X2 -> v2_connsp_1 X1 X2 -> m1_pre_topc X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2 X3 X4, (v2_connsp_1 X3 X4 -> False) -> X1 = X3 -> v2_pre_topc X4 -> l1_pre_topc X4 -> v2_connsp_1 X1 X2 -> m1_pre_topc X2 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r1_connsp_2 X1 X2 -> False) -> (r3_connsp_1 X1 (esk42_2 X1 X2) (esk43_2 X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r1_connsp_2 esk1_0 esk2_0 -> False) -> (m1_subset_1 (esk4_1 X1) (u1_struct_0 (k1_pre_topc esk1_0 X1)) -> False) -> v3_pre_topc X1 esk1_0 -> r2_hidden esk2_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_connsp_2 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r1_connsp_2 X1 X2 -> False) -> (m1_connsp_2 (esk42_2 X1 X2) X1 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r1_connsp_2 X1 X2 -> False) -> (m1_connsp_2 (esk6_2 X1 X2) X1 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (v3_connsp_1 X3 X2 -> False) -> X3 = (k1_connsp_1 X2 X1) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk44_2 X1 X2) (u1_struct_0 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_connsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, ((k1_connsp_1 X2 (esk44_2 X2 X1)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v3_connsp_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_connsp_2 (esk10_2 X1 X2) X1 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r1_connsp_2 X1 X2 -> False) -> (m1_subset_1 (esk43_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r1_connsp_2 X1 X2 -> False) -> (m1_subset_1 (esk42_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r1_connsp_2 X1 X2 -> False) -> (m1_subset_1 (esk6_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3, ((k2_struct_0 X1) = X3 -> False) -> X1 = (k1_pre_topc X2 X3) -> l1_pre_topc X2 -> v1_pre_topc X1 -> m1_pre_topc X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_tops_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> l1_pre_topc X1 -> v2_struct_0 (k1_pre_topc X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, ((k1_tops_1 X1 (k1_tops_1 X1 X2)) = (k1_tops_1 X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (X1 = (k1_pre_topc X3 X2) -> False) -> (k2_struct_0 X1) = X2 -> l1_pre_topc X3 -> v1_pre_topc X1 -> m1_pre_topc X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_tops_1 X1 X2) -> False) -> l1_pre_topc X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc (k1_tops_1 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (r1_connsp_2 X2 X1 -> False) -> (r2_hidden X1 (esk43_2 X2 X1) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v2_struct_0 (g1_pre_topc X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1, ((esk4_1 X1) = esk2_0 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_connsp_2 esk1_0 esk2_0 -> False) -> v3_pre_topc X1 esk1_0 -> r2_hidden esk2_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_connsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> v3_connsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (k1_connsp_1 X1 X2) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (m1_pre_topc (k1_pre_topc X1 X2) X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_pre_topc (k1_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_connsp_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_pre_topc X1 X3) = (g1_pre_topc X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_pre_topc X3 X1) = (g1_pre_topc X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> v2_struct_0 (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False)
  -> (forall X2 X1, (v1_pre_topc (k1_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_pre_topc (k1_pre_topc X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_pre_topc (k1_pre_topc X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 (k1_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_connsp_1 X2 X1 -> False) -> l1_pre_topc X1 -> v3_connsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v2_connsp_1 (k1_connsp_1 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X2 (k1_connsp_1 X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v1_pre_topc (k1_pre_topc X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (v1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (l1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_connsp_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (m1_subset_1 (u1_pre_topc X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v1_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk40_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk39_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk41_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tops_1 (esk39_1 X1) X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tops_1 (k2_struct_0 X1) X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, l1_struct_0 X1 -> v1_subset_1 (k2_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (k2_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> r1_connsp_2 esk1_0 esk2_0 -> False)
  -> (forall X1, ((g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) = X1 -> False) -> l1_pre_topc X1 -> v1_pre_topc X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v2_pre_topc X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk40_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk29_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_pre_topc (esk29_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk40_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk39_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v3_tops_1 (esk41_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk37_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk25_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk34_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk25_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk19_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk13_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (l1_pre_topc X2 -> False) -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_pre_topc (esk30_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk38_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (u1_pre_topc X1) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> ((r2_hidden esk2_0 esk3_0 -> False) -> r1_connsp_2 esk1_0 esk2_0 -> False)
  -> ((v3_pre_topc esk3_0 esk1_0 -> False) -> r1_connsp_2 esk1_0 esk2_0 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk22_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (k2_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> v2_struct_0 (esk30_1 X1) -> False)
  -> (forall X1, (v1_tops_1 (esk33_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_tops_1 (k2_struct_0 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_tops_1 (esk36_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk27_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk11_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_pre_topc (esk34_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 (k2_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_pre_topc (esk34_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (v1_xboole_0 esk3_0 -> r1_connsp_2 esk1_0 esk2_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk21_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (esk30_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk38_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk35_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v6_pre_topc X1 -> False) -> v2_struct_0 X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_pre_topc (esk27_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 (esk16_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_struct_0 X1) = (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk28_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk23_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk24_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk9_0 -> False) -> False)
  -> ((v1_pre_topc esk23_0 -> False) -> False)
  -> ((v1_pre_topc esk17_0 -> False) -> False)
  -> ((v1_pre_topc esk15_0 -> False) -> False)
  -> ((v1_pre_topc esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_pre_topc esk23_0 -> False) -> False)
  -> ((l1_pre_topc esk17_0 -> False) -> False)
  -> ((l1_pre_topc esk15_0 -> False) -> False)
  -> ((l1_pre_topc esk14_0 -> False) -> False)
  -> ((l1_pre_topc esk8_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk23_0 -> False) -> False)
  -> ((v2_pre_topc esk15_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> ((v2_struct_0 esk15_0 -> False) -> False)
  -> ((v2_struct_0 esk14_0 -> False) -> False)
  -> False.
Admitted.
