(** $I sig/MizarPreamble.mgs **)

Theorem t55_tex_4:
 forall a_2_12_tex_4:set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k2_tex_4:set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall a_2_4_tex_4:set -> set -> set,
 forall v3_tops_1:set -> set -> prop,
 forall v2_tops_1:set -> set -> prop,
 forall v4_pre_topc:set -> set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall l1_struct_0:set -> prop,
 forall k5_setfam_1:set -> set -> set,
 forall esk36_1:set -> set,
 forall esk38_1:set -> set,
 forall esk21_1:set -> set,
 forall esk11_1:set -> set,
 forall k2_struct_0:set -> set,
 forall esk18_1:set -> set,
 forall esk17_1:set -> set,
 forall esk30_1:set -> set,
 forall v2_tdlat_3:set -> prop,
 forall esk20_1:set -> set,
 forall esk35_1:set -> set,
 forall esk13_1:set -> set,
 forall esk28_1:set -> set,
 forall v1_tops_1:set -> set -> prop,
 forall esk24_1:set -> set,
 forall esk23_0:set,
 forall esk16_0:set,
 forall o_0_0_xboole_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk15_0:set,
 forall esk6_1:set -> set,
 forall esk19_1:set -> set,
 forall esk22_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v6_pre_topc:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk12_1:set -> set,
 forall esk31_1:set -> set,
 forall v1_tdlat_3:set -> prop,
 forall esk33_1:set -> set,
 forall esk27_1:set -> set,
 forall esk25_1:set -> set,
 forall esk32_1:set -> set,
 forall esk14_1:set -> set,
 forall esk34_1:set -> set,
 forall esk29_1:set -> set,
 forall esk26_1:set -> set,
 forall esk37_1:set -> set,
 forall esk3_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall esk39_2:set -> set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v7_struct_0:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall k1_tex_4:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall k1_setfam_1:set -> set,
 forall k3_tex_4:set -> set -> set,
 forall k1_xboole_0:set,
 forall v1_tex_4:set -> set -> prop,
 forall esk10_3:set -> set -> set -> set,
 forall a_2_8_tex_4:set -> set -> set,
 forall v3_pre_topc:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall u1_struct_0:set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall l1_pre_topc:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall a_2_15_tex_4:set -> set -> set,
 forall v2_pre_topc:set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk8_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_2_15_tex_4 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_2_12_tex_4 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (v3_pre_topc (esk8_3 X1 X2 X3) X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_2_15_tex_4 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2 X3, (v2_struct_0 X3 -> False) -> (r1_tarski X1 (esk8_3 X2 X3 X1) -> False) -> v2_pre_topc X3 -> l1_pre_topc X3 -> r2_hidden X2 (a_2_15_tex_4 X3 X1) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk10_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_2_8_tex_4 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((k2_tex_4 X2 (esk10_3 X1 X2 X3)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_2_8_tex_4 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v3_pre_topc (esk7_3 X1 X2 X3) X2 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_2_12_tex_4 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_2_8_tex_4 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1 X3, (v2_struct_0 X3 -> False) -> (r1_tarski X1 (esk7_3 X2 X3 X1) -> False) -> l1_pre_topc X3 -> r2_hidden X2 (a_2_12_tex_4 X3 X1) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X3 X1 X2, (m1_subset_1 (esk9_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_pre_topc X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (a_2_4_tex_4 X2 X3) -> False)
  -> (forall X3 X1 X2, (v1_tex_4 (esk9_3 X1 X2 X3) X2 -> False) -> l1_pre_topc X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (a_2_4_tex_4 X2 X3) -> False)
  -> (forall X1 X2 X3, (r2_hidden X1 (esk9_3 X2 X3 X1) -> False) -> l1_pre_topc X3 -> m1_subset_1 X1 (u1_struct_0 X3) -> r2_hidden X2 (a_2_4_tex_4 X3 X1) -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_15_tex_4 X2 X4) -> False) -> X1 = X3 -> v2_pre_topc X2 -> l1_pre_topc X2 -> r1_tarski X4 X1 -> v3_pre_topc X1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_12_tex_4 X2 X4) -> False) -> X1 = X3 -> l1_pre_topc X2 -> r1_tarski X4 X1 -> v3_pre_topc X1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, ((esk8_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 (a_2_15_tex_4 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_8_tex_4 X2 X4) -> False) -> X3 = (k2_tex_4 X2 X1) -> l1_pre_topc X2 -> r2_hidden X1 X4 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((esk7_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_pre_topc X2 -> r2_hidden X1 (a_2_12_tex_4 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2 X4 X3, (r2_hidden X3 (a_2_4_tex_4 X2 X4) -> False) -> X1 = X3 -> l1_pre_topc X2 -> r2_hidden X4 X1 -> v1_tex_4 X1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, ((a_2_12_tex_4 X1 X2) = k1_xboole_0 -> False) -> (v2_struct_0 X1 -> False) -> (r1_tarski (k3_tex_4 X1 X2) (k1_setfam_1 (a_2_12_tex_4 X1 X2)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, ((esk9_3 X1 X2 X3) = X1 -> False) -> l1_pre_topc X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (a_2_4_tex_4 X2 X3) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_subset_1 X2 (u1_struct_0 X1) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> v1_subset_1 (k3_tex_4 X1 X2) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_tex_4 X1 X2) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k3_tex_4 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> l1_struct_0 X2 -> v13_struct_0 X2 np__1 -> v1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v1_zfmisc_1 X2 -> False) -> l1_pre_topc X1 -> v1_zfmisc_1 (k3_tex_4 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> l1_pre_topc X1 -> v1_xboole_0 (k3_tex_4 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk39_2 X3 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 X1 -> False) -> (v1_subset_1 X1 (u1_struct_0 X2) -> False) -> l1_struct_0 X2 -> v13_struct_0 X2 np__1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, ((k3_tarski (a_2_8_tex_4 X1 X2)) = (k3_tex_4 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 (k3_tex_4 X1 X2) -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k5_setfam_1 (u1_struct_0 X1) (k1_tex_4 X1 X2)) = (k2_tex_4 X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_tex_4 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, (v7_struct_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_subset_1 X1 (u1_struct_0 X2) -> False) -> l1_struct_0 X2 -> v1_zfmisc_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v7_struct_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_subset_1 X1 (u1_struct_0 X2) -> False) -> l1_struct_0 X2 -> v1_zfmisc_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 (k2_tex_4 X1 X2) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 (k1_tex_4 X1 X2) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk3_2 X1 X2) X2 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k1_tex_4 X1 X2) = (a_2_4_tex_4 X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 X2 -> False) -> (v1_subset_1 X1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 X2 -> False) -> (v1_subset_1 X1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (r2_hidden (esk39_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk3_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_subset_1 (esk29_1 X1) (u1_struct_0 X1) -> False)
  -> (forall X1, (m1_subset_1 (esk38_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tops_1 (esk36_1 X1) X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tops_1 (k2_struct_0 X1) X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, l1_struct_0 X1 -> v1_subset_1 (k2_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (k2_struct_0 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk37_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk26_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_pre_topc (esk26_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_tdlat_3 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v1_tdlat_3 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_subset_1 (esk32_1 X1) (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_subset_1 (esk25_1 X1) (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_tdlat_3 X1 -> v2_tdlat_3 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_subset_1 (esk20_1 X1) X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk37_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk36_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v3_tops_1 (esk38_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk34_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk21_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk21_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk14_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk11_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (k2_struct_0 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_tdlat_3 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_tdlat_3 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk29_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk18_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk32_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk25_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (k2_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_tops_1 (esk30_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v1_tops_1 (k2_struct_0 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_tops_1 (esk33_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k2_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk32_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk25_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk17_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk35_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk20_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk12_1 X1) -> False)
  -> (forall X1, (v6_pre_topc X1 -> False) -> v2_struct_0 X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_struct_0 X1) = (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_zfmisc_1 (esk13_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk31_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_tarski (k3_tex_4 esk1_0 esk2_0) (k1_setfam_1 (a_2_15_tex_4 esk1_0 esk2_0)) -> False)
  -> (forall X1, v1_subset_1 (esk24_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_zfmisc_1 esk23_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> ((v1_zfmisc_1 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk5_0 -> False) -> False)
  -> ((l1_pre_topc esk4_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
