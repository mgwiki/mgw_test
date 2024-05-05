(** $I sig/MizarPreamble.mgs **)

Theorem t7_topgen_1:
 forall k2_tops_1:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall v4_pre_topc:set -> set -> prop,
 forall k4_subset_1:set -> set -> set -> set,
 forall v3_tops_1:set -> set -> prop,
 forall v2_tops_1:set -> set -> prop,
 forall esk7_2:set -> set -> set,
 forall esk16_1:set -> set,
 forall esk20_1:set -> set,
 forall esk18_1:set -> set,
 forall k1_xboole_0:set,
 forall l1_struct_0:set -> prop,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk15_1:set -> set,
 forall esk10_0:set,
 forall esk12_0:set,
 forall esk9_0:set,
 forall o_0_0_xboole_0:set,
 forall esk11_1:set -> set,
 forall esk17_1:set -> set,
 forall v3_ordinal1:set -> prop,
 forall esk19_1:set -> set,
 forall v3_card_1:set -> set -> prop,
 forall v1_card_1:set -> prop,
 forall esk13_1:set -> set,
 forall esk14_1:set -> set,
 forall esk21_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v3_pre_topc:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall k1_topgen_1:set -> set -> set,
 forall l1_pre_topc:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v2_pre_topc:set -> prop,
 forall esk4_4:set -> set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
     (forall X4 X1 X2 X3, (m1_subset_1 (esk4_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> X3 = (k1_topgen_1 X1 X2) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_hidden X4 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X1 X2 X3 X4, ((k2_tops_1 X2 (esk4_4 X2 X3 X4 X1)) = X1 -> False) -> X4 = (k1_topgen_1 X2 X3) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 X4 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X4 X1 X2 X3, (r2_hidden (esk4_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k1_topgen_1 X1 X2) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_hidden X4 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k1_topgen_1 X1 X2) -> False) -> (esk5_3 X1 X2 X3) = (k2_tops_1 X1 X4) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r2_hidden X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_topgen_1 X1 X2) -> False) -> ((k2_tops_1 X1 (esk6_3 X1 X2 X3)) = (esk5_3 X1 X2 X3) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_topgen_1 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_topgen_1 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X2 -> False)
  -> (forall X4 X2 X1 X3 X5, (r2_hidden X3 X5 -> False) -> X5 = (k1_topgen_1 X2 X4) -> X3 = (k2_tops_1 X2 X1) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_topgen_1 X1 X2) -> False) -> (m1_subset_1 (esk5_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X2 X3 X1, (r1_tarski (k1_topgen_1 X1 X2) (k1_topgen_1 X1 X3) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> r1_tarski X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k2_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_topgen_1 X1 X2) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v3_tops_1 (k2_tops_1 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_tops_1 (k2_tops_1 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tops_1 X2 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_tops_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc (k2_tops_1 X1 X2) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) X2 -> False) -> r1_tarski X3 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v4_pre_topc (esk16_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_tops_1 (esk21_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk16_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk14_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_card_1 (esk19_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v2_tops_1 (esk20_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k4_subset_1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) (k1_topgen_1 esk1_0 esk2_0) (k1_topgen_1 esk1_0 esk3_0)) = (k1_topgen_1 esk1_0 (k4_subset_1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) esk2_0 esk3_0)) -> False)
  -> (forall X1, v1_subset_1 (esk17_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 esk1_0))) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 esk1_0))) -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk15_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_card_1 esk12_0 -> False) -> False)
  -> ((l1_pre_topc esk9_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
