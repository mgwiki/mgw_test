(** $I sig/MizarPreamble.mgs **)

Theorem t17_tsp_2:
 forall v2_struct_0:set -> prop,
 forall v2_pre_topc:set -> prop,
 forall v2_tsp_2:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_pre_topc:set -> set -> prop,
 forall l1_pre_topc:set -> prop,
 forall u1_struct_0:set -> set,
 forall k3_tex_4:set -> set -> set,
 forall k8_subset_1:set -> set -> set -> set,
 forall v4_pre_topc:set -> set -> prop,
 forall esk10_3:set -> set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall v3_pre_topc:set -> set -> prop,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall k2_tex_4:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_tex_2:set -> set -> prop,
 forall v1_tsep_1:set -> set -> prop,
 forall esk34_1:set -> set,
 forall esk26_1:set -> set,
 forall esk35_1:set -> set,
 forall esk23_1:set -> set,
 forall esk16_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk21_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk20_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v2_tdlat_3:set -> prop,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall esk29_1:set -> set,
 forall esk17_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk25_1:set -> set,
 forall esk19_0:set,
 forall esk13_0:set,
 forall esk12_0:set,
 forall esk15_1:set -> set,
 forall esk22_1:set -> set,
 forall esk24_0:set,
 forall esk14_1:set -> set,
 forall esk28_1:set -> set,
 forall esk32_1:set -> set,
 forall k1_xboole_0:set,
 forall v1_tdlat_3:set -> prop,
 forall v3_tdlat_3:set -> prop,
 forall esk30_1:set -> set,
 forall k1_tarski:set -> set,
 forall esk27_1:set -> set,
 forall esk18_1:set -> set,
 forall esk31_1:set -> set,
 forall esk33_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk4_0:set,
 forall v6_pre_topc:set -> prop,
 forall esk8_2:set -> set -> set,
 forall v1_tex_3:set -> set -> prop,
 forall v1_borsuk_1:set -> set -> prop,
 forall v2_tops_1:set -> set -> prop,
 forall v3_tops_1:set -> set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v1_tsp_2:set -> set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall k4_tex_4:set -> set -> set,
 forall k6_domain_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk9_3 X1 X2 X3) X3 -> r2_hidden (esk9_3 X1 X2 X3) X2 -> r2_hidden (esk9_3 X1 X2 X3) X1 -> False)
  -> (forall X4 X3 X2 X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc X3 X4 -> False) -> X2 = X3 -> X3 = (k8_subset_1 (u1_struct_0 X1) (k3_tex_4 X1 X2) (u1_struct_0 X4)) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tsp_2 X4 X1 -> m1_pre_topc X4 X1 -> v4_pre_topc (k3_tex_4 X1 X2) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (v1_tsp_2 X3 X2 -> False) -> (k9_subset_1 (u1_struct_0 X2) X3 (k4_tex_4 X2 (esk11_2 X2 X3))) = (k6_domain_1 (u1_struct_0 X2) X1) -> v2_pre_topc X2 -> l1_pre_topc X2 -> r2_hidden X1 X3 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, ((k9_subset_1 (u1_struct_0 X1) X2 (k4_tex_4 X1 X3)) = (k6_domain_1 (u1_struct_0 X1) (esk10_3 X1 X2 X3)) -> False) -> (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_tsp_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (m1_pre_topc X2 X1 -> False) -> (k8_subset_1 (u1_struct_0 X1) X3 (u1_struct_0 X2)) = (esk6_2 X1 X2) -> l1_pre_topc X2 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc (esk6_2 X1 X2) X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> r1_tarski (u1_struct_0 X2) (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X4 X2, (X1 = (k8_subset_1 (u1_struct_0 X2) (k3_tex_4 X2 X3) (u1_struct_0 X4)) -> False) -> (v2_struct_0 X2 -> False) -> X1 = X3 -> v2_pre_topc X2 -> l1_pre_topc X2 -> v2_tsp_2 X4 X2 -> m1_pre_topc X4 X2 -> v4_pre_topc X1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X4)) -> False)
  -> (forall X2 X1 X3, ((k8_subset_1 (u1_struct_0 X2) (esk5_3 X2 X3 X1) (u1_struct_0 X3)) = X1 -> False) -> l1_pre_topc X3 -> l1_pre_topc X2 -> m1_pre_topc X3 X2 -> v4_pre_topc X1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X1 X2 X3 X4, (v4_pre_topc X3 X4 -> False) -> X3 = (k8_subset_1 (u1_struct_0 X2) X1 (u1_struct_0 X4)) -> l1_pre_topc X4 -> l1_pre_topc X2 -> m1_pre_topc X4 X2 -> v4_pre_topc X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k3_tex_4 X1 X2) = (k3_tex_4 X1 X3) -> False) -> (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> r1_tarski X3 (k3_tex_4 X1 X2) -> r1_tarski X2 (k3_tex_4 X1 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk10_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_tsp_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (esk5_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> v4_pre_topc X3 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_tsp_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (k3_tex_4 X1 X2) (k3_tex_4 X1 X3) -> False) -> l1_pre_topc X1 -> r1_tarski X2 (k3_tex_4 X1 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X4 X3 X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (k3_tex_4 X1 X2) X1 -> False) -> X2 = X3 -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tsp_2 X4 X1 -> m1_pre_topc X4 X1 -> v4_pre_topc X3 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X4)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v4_pre_topc (esk5_3 X1 X2 X3) X1 -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> v4_pre_topc X3 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, ((k8_subset_1 (u1_struct_0 X1) (esk7_2 X1 X2) (u1_struct_0 X2)) = (esk6_2 X1 X2) -> False) -> (m1_pre_topc X2 X1 -> False) -> (v4_pre_topc (esk6_2 X1 X2) X2 -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> r1_tarski (u1_struct_0 X2) (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (k3_tex_4 X1 X2) (k3_tex_4 X1 X3) -> False) -> l1_pre_topc X1 -> r1_tarski X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v3_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X3 X1 -> v3_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_pre_topc (k3_xboole_0 X2 X3) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X3 X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (k3_tex_4 esk1_0 esk3_0) = esk3_0 -> X1 = (k8_subset_1 (u1_struct_0 esk1_0) esk3_0 (u1_struct_0 esk2_0)) -> v4_pre_topc X1 esk2_0 -> v4_pre_topc esk3_0 esk1_0 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk2_0)) -> False)
  -> (forall X1 X2, (m1_pre_topc X2 X1 -> False) -> (v4_pre_topc (esk6_2 X1 X2) X2 -> False) -> (m1_subset_1 (esk7_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> r1_tarski (u1_struct_0 X2) (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, ((k2_tex_4 X2 X1) = (k2_tex_4 X2 X3) -> False) -> (v2_struct_0 X2 -> False) -> l1_pre_topc X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r2_hidden X1 (k2_tex_4 X2 X3) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X2 (k2_tex_4 X1 X3) -> False) -> (k2_tex_4 X1 X2) = (k2_tex_4 X1 X3) -> l1_pre_topc X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k8_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (m1_pre_topc X2 X1 -> False) -> (v4_pre_topc (esk6_2 X1 X2) X2 -> False) -> (v4_pre_topc (esk7_2 X1 X2) X1 -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> r1_tarski (u1_struct_0 X2) (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k8_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (v1_tsp_2 X3 X2 -> False) -> X3 = (u1_struct_0 X1) -> l1_pre_topc X2 -> v2_tsp_2 X1 X2 -> m1_pre_topc X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (v2_tsp_2 X3 X2 -> False) -> X1 = (u1_struct_0 X3) -> l1_pre_topc X2 -> m1_pre_topc X3 X2 -> v1_tsp_2 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_tsp_2 X2 X1 -> False) -> (m1_subset_1 (esk11_2 X1 X2) (u1_struct_0 X1) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (m1_pre_topc X2 X1 -> False) -> (m1_subset_1 (esk6_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> r1_tarski (u1_struct_0 X2) (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> v2_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (k6_domain_1 (u1_struct_0 X1) X2) (k2_tex_4 X1 X2) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k3_tex_4 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_pre_topc X2 X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k3_tex_4 X1 (k6_domain_1 (u1_struct_0 X1) X2)) = (k2_tex_4 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tsp_2 X2 X1 -> m1_pre_topc X2 X1 -> v1_tex_2 X2 X1 -> v1_tsep_1 X2 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tsp_2 X2 X1 -> m1_pre_topc X2 X1 -> v1_tex_2 X2 X1 -> v1_tsep_1 X2 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tsp_2 X2 X1 -> m1_pre_topc X2 X1 -> v1_tex_2 X2 X1 -> v1_tsep_1 X2 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tsp_2 X2 X1 -> m1_pre_topc X2 X1 -> v1_tex_2 X2 X1 -> v1_borsuk_1 X2 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tsp_2 X2 X1 -> m1_pre_topc X2 X1 -> v1_tex_2 X2 X1 -> v1_borsuk_1 X2 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tsp_2 X2 X1 -> m1_pre_topc X2 X1 -> v1_tex_2 X2 X1 -> v1_borsuk_1 X2 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k4_tex_4 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k3_tex_4 X1 X2) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v4_pre_topc X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v3_tops_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k3_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (k4_tex_4 X1 X2) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_tex_4 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k8_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v3_tops_1 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v3_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v4_pre_topc X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v2_tops_1 X2 X1 -> False) -> l1_pre_topc X1 -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k4_tex_4 X1 X2) = (k2_tex_4 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_tex_3 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tsp_2 X2 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v1_tex_3 X2 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tsp_2 X2 X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk8_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k6_domain_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v6_pre_topc X2 -> False) -> (v1_tex_2 X1 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v6_pre_topc X1 -> m1_pre_topc X1 X2 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v6_pre_topc X2 -> False) -> (v1_tex_2 X1 X2 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v6_pre_topc X1 -> m1_pre_topc X1 X2 -> False)
  -> (((k8_subset_1 (u1_struct_0 esk1_0) esk3_0 (u1_struct_0 esk2_0)) = esk4_0 -> False) -> (v4_pre_topc esk3_0 esk1_0 -> False) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m1_subset_1 (u1_struct_0 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v6_pre_topc X1 -> False) -> l1_pre_topc X2 -> v2_tsp_2 X1 X2 -> m1_pre_topc X1 X2 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v6_pre_topc X1 -> False) -> l1_pre_topc X2 -> v2_tsp_2 X1 X2 -> m1_pre_topc X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski (u1_struct_0 X1) (u1_struct_0 X2) -> False) -> l1_pre_topc X2 -> l1_pre_topc X1 -> m1_pre_topc X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v6_pre_topc X1 -> False) -> v2_pre_topc X2 -> l1_pre_topc X2 -> v6_pre_topc X2 -> m1_pre_topc X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk8_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v2_tops_1 (esk33_1 X1) X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r2_hidden X1 X2 -> False) -> r1_tarski (k1_tarski X1) X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_pre_topc X1 -> False)
  -> (forall X2 X1, ((k6_domain_1 X1 X2) = (k1_tarski X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski (k1_tarski X1) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v2_pre_topc X2 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_pre_topc (esk26_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk34_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v4_pre_topc (esk26_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_tdlat_3 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v6_pre_topc X1 -> v3_tdlat_3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_tdlat_3 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v6_pre_topc X1 -> v3_tdlat_3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_tdlat_3 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v6_pre_topc X1 -> v3_tdlat_3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v6_pre_topc X1 -> v2_tdlat_3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v6_pre_topc X1 -> v2_tdlat_3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v7_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v6_pre_topc X1 -> v2_tdlat_3 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> ((v4_pre_topc esk3_0 esk1_0 -> False) -> (m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 esk2_0)) -> False) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk34_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk33_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v3_tops_1 (esk35_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk23_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk18_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v3_pre_topc (esk16_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk31_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v4_pre_topc (esk23_1 X1) X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (l1_pre_topc X2 -> False) -> l1_pre_topc X1 -> m1_pre_topc X2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_pre_topc X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_tdlat_3 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_pre_topc X1 -> False) -> v2_pre_topc X1 -> l1_pre_topc X1 -> v1_tdlat_3 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk21_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_tops_1 (esk30_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (m1_pre_topc (esk14_1 X1) X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v6_pre_topc X1 -> False) -> l1_pre_topc X1 -> v7_struct_0 X1 -> False)
  -> ((v4_pre_topc esk3_0 esk1_0 -> False) -> (v4_pre_topc esk4_0 esk2_0 -> False) -> False)
  -> (((k3_tex_4 esk1_0 esk3_0) = esk3_0 -> False) -> (v4_pre_topc esk3_0 esk1_0 -> False) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk20_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk32_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v6_pre_topc X1 -> False) -> v2_struct_0 X1 -> l1_pre_topc X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk29_1 X1) -> False) -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_pre_topc X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk25_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1 X2, (r1_tarski (k3_xboole_0 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((m1_pre_topc esk2_0 esk1_0 -> False) -> False)
  -> ((v2_tsp_2 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk22_1 X1) -> False) -> False)
  -> ((v1_xboole_0 esk19_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk13_0 -> False) -> False)
  -> ((l1_pre_topc esk12_0 -> False) -> False)
  -> ((l1_pre_topc esk1_0 -> False) -> False)
  -> ((v2_pre_topc esk1_0 -> False) -> False)
  -> False.
Admitted.
