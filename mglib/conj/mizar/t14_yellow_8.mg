(** $I sig/MizarPreamble.mgs **)

Theorem t14_yellow_8:
 forall v3_pre_topc:set -> set -> prop,
 forall v1_yellow_8:set -> set -> set -> prop,
 forall esk7_4:set -> set -> set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall v1_tops_2:set -> set -> prop,
 forall esk10_3:set -> set -> set -> set,
 forall esk20_2:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall esk36_2:set -> set -> set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk3_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk22_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk21_1:set -> set,
 forall esk32_1:set -> set,
 forall v5_finset_1:set -> prop,
 forall k1_xboole_0:set,
 forall esk34_1:set -> set,
 forall esk31_1:set -> set,
 forall esk23_1:set -> set,
 forall v6_pre_topc:set -> prop,
 forall esk28_1:set -> set,
 forall esk24_0:set,
 forall esk26_0:set,
 forall esk25_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk14_0:set,
 forall esk13_0:set,
 forall esk19_0:set,
 forall esk15_1:set -> set,
 forall esk17_0:set,
 forall esk35_0:set,
 forall v3_finsub_1:set -> prop,
 forall v1_finsub_1:set -> prop,
 forall v4_finsub_1:set -> prop,
 forall esk27_1:set -> set,
 forall v2_setfam_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall esk30_1:set -> set,
 forall esk33_1:set -> set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk29_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk9_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v2_tops_1:set -> set -> prop,
 forall esk11_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall u1_pre_topc:set -> set,
 forall v1_cantor_1:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall k8_setfam_1:set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall k1_cantor_1:set -> set -> set,
 forall esk4_4:set -> set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall u1_struct_0:set -> set,
 forall esk16_4:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_3_3_yellow_8:set -> set -> set -> set,
 forall l1_pre_topc:set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk16_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_pre_topc X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_3_yellow_8 X2 X3 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk16_4 X1 X2 X3 X4) X3 -> False) -> l1_pre_topc X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_3_yellow_8 X2 X3 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (r1_tarski (esk16_4 X1 X2 X3 X4) X4 -> False) -> l1_pre_topc X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_3_yellow_8 X2 X3 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk7_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> r2_hidden X2 X4 -> v3_pre_topc X4 X1 -> v1_yellow_8 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r2_hidden (esk7_4 X1 X2 X3 X4) X3 -> False) -> l1_pre_topc X1 -> r2_hidden X2 X4 -> v3_pre_topc X4 X1 -> v1_yellow_8 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (esk7_4 X1 X2 X3 X4) X4 -> False) -> l1_pre_topc X1 -> r2_hidden X2 X4 -> v3_pre_topc X4 X1 -> v1_yellow_8 X3 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (esk4_4 X1 X2 X3 X4) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> X3 = (k1_cantor_1 X1 X2) -> r2_hidden X4 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2 X3 X4, ((k5_setfam_1 X2 (esk4_4 X2 X3 X4 X1)) = X1 -> False) -> X4 = (k1_cantor_1 X2 X3) -> r2_hidden X1 X4 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X4 X1 X2 X3, (r1_tarski (esk4_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k1_cantor_1 X1 X2) -> r2_hidden X4 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X4 X2, ((esk16_4 X1 X2 X3 X4) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_pre_topc X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_3_yellow_8 X2 X3 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (v1_yellow_8 X3 X2 X4 -> False) -> l1_pre_topc X2 -> r2_hidden X1 X3 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> r1_tarski X1 (esk8_3 X2 X4 X3) -> r2_hidden X4 (k8_setfam_1 (u1_struct_0 X2) X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k1_cantor_1 X1 X2) -> False) -> (esk5_3 X1 X2 X3) = (k5_setfam_1 X1 X4) -> r1_tarski X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X1 X2, (X3 = (k1_cantor_1 X1 X2) -> False) -> ((k5_setfam_1 X1 (esk6_3 X1 X2 X3)) = (esk5_3 X1 X2 X3) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (v1_yellow_8 X3 X1 X2 -> False) -> (m1_subset_1 (esk8_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_hidden X2 (k8_setfam_1 (u1_struct_0 X1) X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (v1_yellow_8 X3 X1 X2 -> False) -> (v3_pre_topc (esk8_3 X1 X2 X3) X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_hidden X2 (k8_setfam_1 (u1_struct_0 X1) X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (v1_yellow_8 X3 X2 X1 -> False) -> (r2_hidden X1 (esk8_3 X2 X1 X3) -> False) -> l1_pre_topc X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> r2_hidden X1 (k8_setfam_1 (u1_struct_0 X2) X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X3 X1 X2, (X3 = (k1_cantor_1 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X4 X5 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_3_3_yellow_8 X2 X4 X5) -> False) -> X1 = X3 -> l1_pre_topc X2 -> r1_tarski X1 X5 -> r2_hidden X1 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X3 X1 X2, (X3 = (k1_cantor_1 X1 X2) -> False) -> (r1_tarski (esk6_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X3 X4 X2, (v2_struct_0 X2 -> False) -> (v3_pre_topc X1 X2 -> False) -> l1_pre_topc X2 -> v1_tops_2 X3 X2 -> r2_hidden X1 X3 -> v1_yellow_8 X3 X2 X4 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X2 X1 X3 X4, (v2_struct_0 X4 -> False) -> (r2_hidden X1 X2 -> False) -> l1_pre_topc X4 -> v1_tops_2 X3 X4 -> r2_hidden X2 X3 -> v1_yellow_8 X3 X4 X1 -> m1_subset_1 X1 (u1_struct_0 X4) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X4))) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X1 (k8_setfam_1 (u1_struct_0 X2) X3) -> False) -> l1_pre_topc X2 -> v1_yellow_8 X3 X2 X1 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X3 X2 X1 X4 X5, (r2_hidden X4 X5 -> False) -> X5 = (k1_cantor_1 X2 X3) -> X4 = (k5_setfam_1 X2 X1) -> r1_tarski X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X1 X2, (X3 = (k1_cantor_1 X1 X2) -> False) -> (m1_subset_1 (esk5_3 X1 X2 X3) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, (v1_cantor_1 X2 X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> r1_tarski (u1_pre_topc X1) (k1_cantor_1 (u1_struct_0 X1) X2) -> False)
  -> (forall X1 X2, (r1_tarski (u1_pre_topc X2) (k1_cantor_1 (u1_struct_0 X2) X1) -> False) -> l1_pre_topc X2 -> v1_cantor_1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk11_2 X1 X2) X3 -> r2_hidden (esk11_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk10_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk10_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2, (v1_tops_2 X1 X2 -> False) -> l1_pre_topc X2 -> r1_tarski X1 (u1_pre_topc X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X1 X2, (r1_tarski X1 (u1_pre_topc X2) -> False) -> l1_pre_topc X2 -> v1_tops_2 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X2))) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_yellow_8 (esk20_2 X1 X2) X1 X2 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> (r2_hidden (esk11_2 X1 X2) (esk12_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_cantor_1 X2 X1) (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk36_2 X3 X2) -> False)
  -> (forall X1 X2, (v3_pre_topc X1 X2 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (u1_pre_topc X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (v1_tops_2 esk2_0 esk1_0 -> v1_cantor_1 esk2_0 esk1_0 -> m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 esk1_0))) -> False)
  -> (forall X1 X2, (r2_hidden X1 (u1_pre_topc X2) -> False) -> l1_pre_topc X2 -> v3_pre_topc X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1, (v1_yellow_8 (esk3_1 X1) esk1_0 X1 -> False) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> (r2_hidden (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_tops_2 (esk20_2 X1 X2) X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (m1_subset_1 (esk3_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 esk1_0))) -> False) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X1, (m1_subset_1 (u1_pre_topc X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk36_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v1_tops_2 (esk3_1 X1) esk1_0 -> False) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> False)
  -> (forall X1, (r1_tarski (esk3_1 X1) esk2_0 -> False) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> False)
  -> (forall X1, (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk22_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_tops_1 (esk32_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_setfam_1 X1 -> False) -> (m1_subset_1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (k3_tarski X1) -> False) -> v1_finset_1 X1 -> v5_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk21_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk34_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk33_1 X1) -> False)
  -> (forall X1, (v2_setfam_1 X1 -> False) -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v6_pre_topc X1 -> False) -> v2_struct_0 X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v4_finsub_1 X1 -> False) -> v1_finsub_1 X1 -> v3_finsub_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk31_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v2_setfam_1 X1 -> False)
  -> (forall X1, (v2_setfam_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk28_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v2_setfam_1 esk24_0 -> False)
  -> (v1_xboole_0 esk35_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 esk1_0))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> ((r1_tarski esk2_0 (u1_pre_topc esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk25_1 X1) -> False) -> False)
  -> ((v5_finset_1 esk35_0 -> False) -> False)
  -> ((v1_xboole_0 esk19_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_finset_1 esk35_0 -> False) -> False)
  -> ((v1_finset_1 esk17_0 -> False) -> False)
  -> ((l1_struct_0 esk14_0 -> False) -> False)
  -> ((l1_pre_topc esk13_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
