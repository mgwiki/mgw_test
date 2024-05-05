(** $I sig/MizarPreamble.mgs **)

Theorem t87_tsep_1:
 forall v3_pre_topc:set -> set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall v4_pre_topc:set -> set -> prop,
 forall m1_pre_topc:set -> set -> prop,
 forall r4_tsep_1:set -> set -> set -> prop,
 forall k2_tsep_1:set -> set -> set -> set,
 forall v1_tsep_1:set -> set -> prop,
 forall v1_borsuk_1:set -> set -> prop,
 forall esk2_0:set,
 forall esk3_0:set,
 forall k1_tsep_1:set -> set -> set -> set,
 forall esk1_0:set,
 forall esk7_3:set -> set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall v1_pre_topc:set -> prop,
 forall r1_tsep_1:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall esk38_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk36_1:set -> set,
 forall esk29_1:set -> set,
 forall esk34_1:set -> set,
 forall esk18_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk22_1:set -> set,
 forall esk21_1:set -> set,
 forall esk33_1:set -> set,
 forall esk23_1:set -> set,
 forall esk16_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall esk30_1:set -> set,
 forall k1_xboole_0:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk28_1:set -> set,
 forall v6_pre_topc:set -> prop,
 forall esk12_1:set -> set,
 forall esk15_0:set,
 forall esk9_0:set,
 forall esk14_0:set,
 forall esk17_0:set,
 forall esk10_0:set,
 forall esk20_0:set,
 forall esk24_0:set,
 forall esk27_0:set,
 forall esk11_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk32_1:set -> set,
 forall esk19_1:set -> set,
 forall esk26_1:set -> set,
 forall esk31_1:set -> set,
 forall esk13_1:set -> set,
 forall esk25_1:set -> set,
 forall esk37_1:set -> set,
 forall esk35_1:set -> set,
 forall u1_pre_topc:set -> set,
 forall g1_pre_topc:set -> set -> set,
 forall v2_tops_1:set -> set -> prop,
 forall v3_tops_1:set -> set -> prop,
 forall esk39_2:set -> set -> set,
 forall esk6_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall v1_xboole_0:set -> prop,
 forall esk42_3:set -> set -> set -> set,
 forall esk40_3:set -> set -> set -> set,
 forall esk41_3:set -> set -> set -> set,
 forall esk45_3:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall l1_pre_topc:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall r2_tsep_1:set -> set -> set -> prop,
 forall v2_pre_topc:set -> prop,
 forall v2_struct_0:set -> prop,
 forall esk44_3:set -> set -> set -> set,
 forall esk43_3:set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall k4_subset_1:set -> set -> set -> set,
     (forall X2 X3 X1, ((k4_subset_1 (u1_struct_0 X1) (esk43_3 X1 X2 X3) (esk44_3 X1 X2 X3)) = (k4_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> ((k4_subset_1 (u1_struct_0 X1) (k4_subset_1 (u1_struct_0 X1) (esk43_3 X1 X2 X3) (esk44_3 X1 X2 X3)) (esk45_3 X1 X2 X3)) = (k4_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X5 X6 X4 X1 X3 X2, (v2_struct_0 X2 -> False) -> (r2_tsep_1 X2 X5 X6 -> False) -> (k4_subset_1 (u1_struct_0 X2) X5 X6) = (u1_struct_0 X2) -> (k4_subset_1 (u1_struct_0 X2) X5 X6) = (k4_subset_1 (u1_struct_0 X2) (k4_subset_1 (u1_struct_0 X2) X1 X3) X4) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v3_pre_topc X4 X2 -> v4_pre_topc X3 X2 -> v4_pre_topc X1 X2 -> r1_tarski X3 X6 -> r1_tarski X1 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> r1_tarski X4 (k9_subset_1 (u1_struct_0 X2) X5 X6) -> False)
  -> (forall X2 X3 X1, ((k4_subset_1 (u1_struct_0 X1) (k4_subset_1 (u1_struct_0 X1) (esk40_3 X1 X2 X3) (esk41_3 X1 X2 X3)) (esk42_3 X1 X2 X3)) = (k4_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, ((k4_subset_1 (u1_struct_0 X1) (esk43_3 X1 X2 X3) (esk44_3 X1 X2 X3)) = (k4_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (r1_tarski (esk45_3 X1 X2 X3) (k9_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, ((k4_subset_1 (u1_struct_0 X1) (esk43_3 X1 X2 X3) (esk44_3 X1 X2 X3)) = (k4_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> v1_xboole_0 (esk45_3 X1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, ((k4_subset_1 (u1_struct_0 X1) (esk43_3 X1 X2 X3) (esk44_3 X1 X2 X3)) = (k4_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (m1_subset_1 (esk45_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, ((k4_subset_1 (u1_struct_0 X1) (esk43_3 X1 X2 X3) (esk44_3 X1 X2 X3)) = (k4_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (v3_pre_topc (esk45_3 X1 X2 X3) X1 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (k1_tsep_1 esk1_0 (k1_tsep_1 esk1_0 X2 X3) X1) = esk1_0 -> m1_pre_topc X3 esk1_0 -> m1_pre_topc X3 esk3_0 -> m1_pre_topc X2 esk1_0 -> m1_pre_topc X2 esk2_0 -> m1_pre_topc X1 esk1_0 -> v1_borsuk_1 X3 esk1_0 -> v1_borsuk_1 X2 esk1_0 -> v1_tsep_1 X1 esk1_0 -> r4_tsep_1 esk1_0 esk2_0 esk3_0 -> m1_pre_topc X1 (k2_tsep_1 esk1_0 esk2_0 esk3_0) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (esk42_3 X1 X2 X3) (k9_subset_1 (u1_struct_0 X1) X2 X3) -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r4_tsep_1 X1 X2 X3 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> r2_tsep_1 X1 (esk7_3 X1 X2 X3) (esk8_3 X1 X2 X3) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> v1_xboole_0 (esk44_3 X1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> v1_xboole_0 (esk43_3 X1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (m1_subset_1 (esk44_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (m1_subset_1 (esk43_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (r1_tarski (esk44_3 X1 X2 X3) X3 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (r1_tarski (esk43_3 X1 X2 X3) X2 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (v4_pre_topc (esk44_3 X1 X2 X3) X1 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (v4_pre_topc (esk43_3 X1 X2 X3) X1 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk42_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk41_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk40_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (esk41_3 X1 X2 X3) X3 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (esk40_3 X1 X2 X3) X2 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk41_3 X1 X2 X3) X1 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk40_3 X1 X2 X3) X1 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v3_pre_topc (esk42_3 X1 X2 X3) X1 -> False) -> (k4_subset_1 (u1_struct_0 X1) X2 X3) = (u1_struct_0 X1) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X5 X4 X1, (r2_tsep_1 X1 X4 X5 -> False) -> X5 = (u1_struct_0 X3) -> X4 = (u1_struct_0 X2) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> r4_tsep_1 X1 X2 X3 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (k1_tsep_1 esk1_0 X1 X2) = esk1_0 -> m1_pre_topc X2 esk1_0 -> m1_pre_topc X2 esk3_0 -> m1_pre_topc X1 esk1_0 -> m1_pre_topc X1 esk2_0 -> v1_borsuk_1 X2 esk1_0 -> v1_borsuk_1 X1 esk1_0 -> r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False)
  -> (((k1_tsep_1 esk1_0 esk4_0 esk5_0) = esk1_0 -> False) -> ((k1_tsep_1 esk1_0 (k1_tsep_1 esk1_0 esk4_0 esk5_0) esk6_0) = esk1_0 -> False) -> (m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> (forall X2 X3 X1, (r2_tsep_1 X1 X3 X2 -> False) -> l1_pre_topc X1 -> r2_tsep_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (r4_tsep_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk8_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X3 X1, (r4_tsep_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> v2_struct_0 (k2_tsep_1 X1 X2 X3) -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> v2_struct_0 (k1_tsep_1 X1 X2 X3) -> False)
  -> (((k1_tsep_1 esk1_0 esk4_0 esk5_0) = esk1_0 -> False) -> (m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> (m1_pre_topc esk6_0 (k2_tsep_1 esk1_0 esk2_0 esk3_0) -> False) -> False)
  -> (forall X2 X3 X4 X1, ((u1_struct_0 X1) = (k3_xboole_0 (u1_struct_0 X3) (u1_struct_0 X4)) -> False) -> (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (r1_tsep_1 X3 X4 -> False) -> X1 = (k2_tsep_1 X2 X3 X4) -> l1_pre_topc X2 -> v1_pre_topc X1 -> m1_pre_topc X4 X2 -> m1_pre_topc X3 X2 -> m1_pre_topc X1 X2 -> False)
  -> (forall X3 X1 X2 X4, (X1 = (k2_tsep_1 X4 X2 X3) -> False) -> (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (r1_tsep_1 X2 X3 -> False) -> (u1_struct_0 X1) = (k3_xboole_0 (u1_struct_0 X2) (u1_struct_0 X3)) -> l1_pre_topc X4 -> v1_pre_topc X1 -> m1_pre_topc X3 X4 -> m1_pre_topc X2 X4 -> m1_pre_topc X1 X4 -> False)
  -> (forall X2 X3 X4 X1, ((u1_struct_0 X1) = (k2_xboole_0 (u1_struct_0 X3) (u1_struct_0 X4)) -> False) -> (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> X1 = (k1_tsep_1 X2 X3 X4) -> l1_pre_topc X2 -> v1_pre_topc X1 -> m1_pre_topc X4 X2 -> m1_pre_topc X3 X2 -> m1_pre_topc X1 X2 -> False)
  -> (forall X3 X1 X2 X4, (X1 = (k1_tsep_1 X4 X2 X3) -> False) -> (v2_struct_0 X4 -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (u1_struct_0 X1) = (k2_xboole_0 (u1_struct_0 X2) (u1_struct_0 X3)) -> l1_pre_topc X4 -> v1_pre_topc X1 -> m1_pre_topc X3 X4 -> m1_pre_topc X2 X4 -> m1_pre_topc X1 X4 -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r4_tsep_1 X1 X3 X2 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> r4_tsep_1 X1 X2 X3 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_pre_topc (k2_tsep_1 X1 X2 X3) X1 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (m1_pre_topc (k1_tsep_1 X1 X2 X3) X1 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_pre_topc (k2_tsep_1 X1 X2 X3) -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_pre_topc (k1_tsep_1 X1 X2 X3) -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1 X3, ((k1_tsep_1 X1 X2 X3) = (k1_tsep_1 X1 X3 X2) -> False) -> (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, ((esk8_3 X1 X2 X3) = (u1_struct_0 X3) -> False) -> (r4_tsep_1 X1 X2 X3 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X3 X1, ((esk7_3 X1 X2 X3) = (u1_struct_0 X2) -> False) -> (r4_tsep_1 X1 X2 X3 -> False) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (r4_tsep_1 X1 X2 X3 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X3 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_struct_0 (esk38_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v2_struct_0 (esk39_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_tsep_1 (esk39_2 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_borsuk_1 (esk38_2 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_pre_topc (esk39_2 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_pre_topc (esk38_2 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (((k1_tsep_1 esk1_0 esk4_0 esk5_0) = esk1_0 -> False) -> (m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (v1_tsep_1 esk6_0 esk1_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> (((k1_tsep_1 esk1_0 esk4_0 esk5_0) = esk1_0 -> False) -> (m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (m1_pre_topc esk6_0 esk1_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> (forall X1 X3 X2, (v4_pre_topc X3 X2 -> False) -> X3 = (u1_struct_0 X1) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_pre_topc X1 X2 -> v1_borsuk_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v3_pre_topc X3 X2 -> False) -> X3 = (u1_struct_0 X1) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_pre_topc X1 X2 -> v1_tsep_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (v1_tsep_1 X1 X2 -> False) -> X3 = (u1_struct_0 X1) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_pre_topc X1 X2 -> v3_pre_topc X3 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (v1_borsuk_1 X1 X2 -> False) -> X3 = (u1_struct_0 X1) -> v2_pre_topc X2 -> l1_pre_topc X2 -> m1_pre_topc X1 X2 -> v4_pre_topc X3 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, ((u1_struct_0 (esk39_2 X2 X1)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v3_pre_topc X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, ((u1_struct_0 (esk38_2 X2 X1)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v4_pre_topc X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_pre_topc (esk39_2 X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_pre_topc (esk38_2 X1 X2) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (((k1_tsep_1 esk1_0 esk4_0 esk5_0) = esk1_0 -> False) -> (m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> v2_struct_0 esk6_0 -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, ((g1_pre_topc (u1_struct_0 X2) (u1_pre_topc X2)) = (g1_pre_topc (u1_struct_0 X3) (u1_pre_topc X3)) -> False) -> (u1_struct_0 X2) = (u1_struct_0 X3) -> l1_pre_topc X1 -> m1_pre_topc X3 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X3 X1 X2, (m1_pre_topc X1 X2 -> False) -> v2_pre_topc X3 -> l1_pre_topc X3 -> m1_pre_topc X2 X3 -> m1_pre_topc X1 X3 -> r1_tarski (u1_struct_0 X1) (u1_struct_0 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (r1_tarski (u1_struct_0 X1) (u1_struct_0 X2) -> False) -> v2_pre_topc X3 -> l1_pre_topc X3 -> m1_pre_topc X2 X3 -> m1_pre_topc X1 X3 -> m1_pre_topc X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v2_struct_0 (g1_pre_topc X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_pre_topc X1 X3) = (g1_pre_topc X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_pre_topc X3 X1) = (g1_pre_topc X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> v2_struct_0 (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False)
  -> (m1_pre_topc esk3_0 esk2_0 -> r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False)
  -> (m1_pre_topc esk2_0 esk3_0 -> r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> ((m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (v1_borsuk_1 esk5_0 esk1_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (v1_borsuk_1 esk4_0 esk1_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (m1_pre_topc esk5_0 esk3_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (m1_pre_topc esk5_0 esk1_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (m1_pre_topc esk4_0 esk2_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (m1_pre_topc esk4_0 esk1_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> (forall X1 X2, (v1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (l1_pre_topc (g1_pre_topc X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> ((m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> v2_struct_0 esk5_0 -> False)
  -> ((m1_pre_topc esk2_0 esk3_0 -> False) -> (m1_pre_topc esk3_0 esk2_0 -> False) -> (r4_tsep_1 esk1_0 esk2_0 esk3_0 -> False) -> v2_struct_0 esk4_0 -> False)
  -> (forall X1, (m1_subset_1 (u1_pre_topc X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v1_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (u1_struct_0 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_tsep_1 X2 X1 -> False) -> l1_struct_0 X2 -> l1_struct_0 X1 -> r1_tsep_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tops_1 (esk35_1 X1) X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_pre_topc (u1_struct_0 X1) (u1_pre_topc X1)) = X1 -> False) -> l1_pre_topc X1 -> v1_pre_topc X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v2_pre_topc X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk36_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk29_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_pre_topc (esk29_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_tsep_1 (esk26_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_borsuk_1 (esk23_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_pre_topc (esk26_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_pre_topc (esk23_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk36_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk35_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_struct_0 (esk26_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_struct_0 (esk23_1 X1) -> False)
  -> (forall X1, (v3_tops_1 (esk37_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk34_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk25_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk25_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk18_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk13_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_tsep_1 (esk19_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_borsuk_1 (esk16_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk32_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk19_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk16_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (l1_pre_topc X2 -> False) -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_pre_topc (esk30_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (u1_pre_topc X1) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (esk26_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (esk23_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_pre_topc (esk26_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_pre_topc (esk23_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk22_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> v2_struct_0 (esk30_1 X1) -> False)
  -> (forall X1, (v2_tops_1 (esk33_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk28_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk11_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_pre_topc (esk32_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_pre_topc (esk19_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_pre_topc (esk16_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (esk32_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (esk19_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_pre_topc (esk16_1 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk21_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_pre_topc (esk30_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v6_pre_topc X1 -> False) -> v2_struct_0 X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_pre_topc (esk28_1 X1) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_tsep_1 esk2_0 esk3_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk24_0 -> False)
  -> (v2_struct_0 esk3_0 -> False)
  -> (v2_struct_0 esk2_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (((k1_tsep_1 esk1_0 esk2_0 esk3_0) = esk1_0 -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski k1_xboole_0 X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((m1_pre_topc esk3_0 esk1_0 -> False) -> False)
  -> ((m1_pre_topc esk2_0 esk1_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((v1_pre_topc esk24_0 -> False) -> False)
  -> ((v1_pre_topc esk17_0 -> False) -> False)
  -> ((v1_pre_topc esk15_0 -> False) -> False)
  -> ((v1_pre_topc esk14_0 -> False) -> False)
  -> ((l1_pre_topc esk24_0 -> False) -> False)
  -> ((l1_pre_topc esk17_0 -> False) -> False)
  -> ((l1_pre_topc esk15_0 -> False) -> False)
  -> ((l1_pre_topc esk14_0 -> False) -> False)
  -> ((l1_pre_topc esk9_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk24_0 -> False) -> False)
  -> ((v2_pre_topc esk15_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> ((v2_struct_0 esk15_0 -> False) -> False)
  -> ((v2_struct_0 esk14_0 -> False) -> False)
  -> False.
Admitted.
