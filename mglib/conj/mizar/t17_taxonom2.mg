(** $I sig/MizarPreamble.mgs **)

Theorem t17_taxonom2:
 forall k3_tarski:set -> set,
 forall esk7_2:set -> set -> set,
 forall esk28_1:set -> set,
 forall esk31_2:set -> set -> set,
 forall v6_ordinal1:set -> prop,
 forall r1_xboole_0:set -> set -> prop,
 forall r3_xboole_0:set -> set -> prop,
 forall esk11_1:set -> set,
 forall esk12_1:set -> set,
 forall esk16_1:set -> set,
 forall esk23_1:set -> set,
 forall esk5_1:set -> set,
 forall esk22_1:set -> set,
 forall esk25_1:set -> set,
 forall esk19_1:set -> set,
 forall esk13_1:set -> set,
 forall esk17_0:set,
 forall esk15_1:set -> set,
 forall esk14_1:set -> set,
 forall esk20_0:set,
 forall esk21_1:set -> set,
 forall esk18_1:set -> set,
 forall v1_setfam_1:set -> prop,
 forall esk24_1:set -> set,
 forall esk10_1:set -> set,
 forall esk9_1:set -> set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk4_2:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk8_2:set -> set -> set,
 forall esk30_1:set -> set,
 forall esk29_2:set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall esk26_3:set -> set -> set -> set,
 forall k1_xboole_0:set,
 forall r2_hidden:set -> set -> prop,
 forall v4_taxonom2:set -> prop,
 forall m1_taxonom2:set -> set -> prop,
 forall v3_abian:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v6_taxonom2:set -> set -> prop,
 forall v5_taxonom2:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall esk27_4:set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall m1_eqrel_1:set -> set -> prop,
     (forall X2 X3 X4 X1, (m1_eqrel_1 X4 X1 -> False) -> (r2_hidden k1_xboole_0 X2 -> False) -> (m1_subset_1 (esk27_4 X1 X2 X3 X4) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> v4_taxonom2 X4 -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v6_taxonom2 X2 X1 -> r2_hidden X3 X4 -> r1_tarski X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X3 X4 X1, (m1_eqrel_1 X4 X1 -> False) -> (r2_hidden k1_xboole_0 X2 -> False) -> (r1_tarski (esk27_4 X1 X2 X3 X4) X2 -> False) -> v4_taxonom2 X4 -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v6_taxonom2 X2 X1 -> r2_hidden X3 X4 -> r1_tarski X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (m1_eqrel_1 X1 X2 -> False) -> (r2_hidden k1_xboole_0 X3 -> False) -> (r1_tarski X1 (esk27_4 X2 X3 X4 X1) -> False) -> v4_taxonom2 X1 -> v5_taxonom2 X3 X2 -> m1_taxonom2 X3 X2 -> v6_taxonom2 X3 X2 -> r2_hidden X4 X1 -> r1_tarski X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> v3_abian X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X1 X4 X2, (m1_eqrel_1 X4 X2 -> False) -> (r2_hidden k1_xboole_0 X3 -> False) -> (r2_hidden X1 (esk27_4 X2 X3 X1 X4) -> False) -> v4_taxonom2 X4 -> v5_taxonom2 X3 X2 -> m1_taxonom2 X3 X2 -> v6_taxonom2 X3 X2 -> r2_hidden X1 X4 -> r1_tarski X4 X3 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> v3_abian X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X3 X4 X1, (m1_eqrel_1 X4 X1 -> False) -> (r2_hidden k1_xboole_0 X2 -> False) -> (v4_taxonom2 (esk27_4 X1 X2 X3 X4) -> False) -> v4_taxonom2 X4 -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v6_taxonom2 X2 X1 -> r2_hidden X3 X4 -> r1_tarski X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X4 X1 X2, (m1_eqrel_1 X1 X2 -> False) -> (r2_hidden k1_xboole_0 X3 -> False) -> (esk27_4 X2 X3 X4 X1) = X1 -> v4_taxonom2 X1 -> v5_taxonom2 X3 X2 -> m1_taxonom2 X3 X2 -> v6_taxonom2 X3 X2 -> r2_hidden X4 X1 -> r1_tarski X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> v3_abian X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X4 X3 X1, (r2_hidden X1 (esk26_3 X2 X4 X3) -> False) -> v4_taxonom2 X1 -> v5_taxonom2 X4 X2 -> m1_taxonom2 X4 X2 -> r2_hidden X3 X1 -> r1_tarski X1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> v3_abian X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> v5_taxonom2 X3 X2 -> m1_taxonom2 X3 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> v3_abian X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (esk26_3 X2 X3 X4) -> False)
  -> (forall X3 X4 X1 X2, (r1_tarski X1 X2 -> False) -> v5_taxonom2 X2 X3 -> m1_taxonom2 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r2_hidden X1 (esk26_3 X3 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> v5_taxonom2 X4 X3 -> m1_taxonom2 X4 X3 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> v3_abian X4 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r2_hidden X2 (esk26_3 X3 X4 X1) -> False)
  -> (forall X2 X3 X4 X1, (v4_taxonom2 X1 -> False) -> v5_taxonom2 X3 X2 -> m1_taxonom2 X3 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> v3_abian X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (esk26_3 X2 X3 X4) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk7_2 X1 X2) X3 -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk6_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X3 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk30_1 X2) -> False) -> r2_hidden X3 X2 -> r2_hidden X1 X2 -> r1_tarski (esk30_1 X2) X1 -> r1_tarski (esk29_2 X2 X3) X3 -> False)
  -> (forall X1 X3 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk30_1 X2) -> False) -> (r2_hidden (esk29_2 X2 X3) (esk28_1 X2) -> False) -> r2_hidden X3 X2 -> r2_hidden X1 X2 -> r1_tarski (esk30_1 X2) X1 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> (r2_hidden (esk7_2 X1 X2) (esk8_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk30_1 X1) X1 -> False) -> r2_hidden X2 X1 -> r1_tarski (esk29_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk4_2 X1 X2) = X1 -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk30_1 X1) X1 -> False) -> (r2_hidden (esk29_2 X1 X2) (esk28_1 X1) -> False) -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> (r2_hidden (esk8_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski (k3_tarski X1) X2 -> False) -> r1_tarski (esk31_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk30_1 X2) -> False) -> (r1_tarski (esk28_1 X2) X2 -> False) -> r2_hidden X1 X2 -> r1_tarski (esk30_1 X2) X1 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk30_1 X2) -> False) -> (v6_ordinal1 (esk28_1 X2) -> False) -> r2_hidden X1 X2 -> r1_tarski (esk30_1 X2) X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (r1_xboole_0 X2 X3 -> False) -> v4_taxonom2 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2 X3, (r3_xboole_0 X2 X3 -> False) -> v6_ordinal1 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, m1_eqrel_1 X1 esk1_0 -> r1_tarski X1 esk2_0 -> r2_hidden esk3_0 X1 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk4_2 X1 X2) = X1 -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (r1_tarski (k3_tarski X1) X2 -> False) -> (r2_hidden (esk31_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_taxonom2 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X2 X1 -> False) -> (r1_tarski X1 X2 -> False) -> r3_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden X1 X2 -> False) -> r1_tarski (k1_tarski X1) X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> r3_xboole_0 (esk11_1 X1) (esk12_1 X1) -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> r1_xboole_0 (esk9_1 X1) (esk10_1 X1) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski (k1_tarski X1) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk30_1 X1) X1 -> False) -> (r1_tarski (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X1 X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X2 X1 -> False) -> r3_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X2 X1 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (v6_ordinal1 (esk28_1 X1) -> False) -> (r2_hidden (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> (r2_hidden (esk12_1 X1) X1 -> False) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> (r2_hidden (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> (r2_hidden (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> (r2_hidden (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> (esk10_1 X1) = (esk9_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk21_1 X1) X1 -> False)
  -> (r2_hidden k1_xboole_0 esk2_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1, (v3_abian (esk25_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((v3_abian esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_taxonom2 (esk25_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_taxonom2 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_taxonom2 (esk25_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> (forall X1, (r3_xboole_0 X1 X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((r2_hidden esk3_0 esk2_0 -> False) -> False)
  -> ((v6_taxonom2 esk2_0 esk1_0 -> False) -> False)
  -> ((m1_taxonom2 esk2_0 esk1_0 -> False) -> False)
  -> ((v5_taxonom2 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v4_taxonom2 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v4_taxonom2 (k1_tarski X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> ((v1_xboole_0 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
