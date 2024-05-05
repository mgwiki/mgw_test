(** $I sig/MizarPreamble.mgs **)

Theorem t15_taxonom2:
 forall r1_xboole_0:set -> set -> prop,
 forall esk18_2:set -> set -> set,
 forall esk19_2:set -> set -> set,
 forall esk1_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk13_2:set -> set -> set,
 forall v3_taxonom2:set -> prop,
 forall r3_xboole_0:set -> set -> prop,
 forall esk39_2:set -> set -> set,
 forall esk8_1:set -> set,
 forall esk9_1:set -> set,
 forall esk27_1:set -> set,
 forall v1_setfam_1:set -> prop,
 forall esk29_1:set -> set,
 forall esk31_0:set,
 forall esk33_1:set -> set,
 forall esk30_1:set -> set,
 forall esk25_1:set -> set,
 forall esk26_1:set -> set,
 forall esk28_0:set,
 forall esk24_1:set -> set,
 forall esk36_1:set -> set,
 forall esk32_1:set -> set,
 forall esk6_1:set -> set,
 forall esk34_1:set -> set,
 forall esk35_1:set -> set,
 forall esk16_1:set -> set,
 forall esk15_1:set -> set,
 forall esk23_1:set -> set,
 forall esk22_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk7_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall esk21_2:set -> set -> set,
 forall m1_eqrel_1:set -> set -> prop,
 forall esk11_2:set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk20_3:set -> set -> set -> set,
 forall k1_setfam_1:set -> set,
 forall v6_taxonom2:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk37_3:set -> set -> set -> set,
 forall v3_abian:set -> set -> prop,
 forall m1_taxonom2:set -> set -> prop,
 forall v4_taxonom2:set -> prop,
 forall esk38_3:set -> set -> set -> set,
 forall k3_tarski:set -> set,
 forall k1_tarski:set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall k1_xboole_0:set,
 forall m1_subset_1:set -> set -> prop,
 forall esk17_4:set -> set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v5_taxonom2:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
     (forall X1 X2 X4 X3, (r2_hidden X4 X3 -> False) -> (m1_subset_1 (esk17_4 X1 X2 X3 X4) (k1_zfmisc_1 X1) -> False) -> v5_taxonom2 X2 X1 -> r2_hidden X3 X2 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2 X4 X3, (r2_hidden X4 X3 -> False) -> (r2_hidden (esk17_4 X1 X2 X3 X4) X2 -> False) -> v5_taxonom2 X2 X1 -> r2_hidden X3 X2 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 (esk17_4 X2 X3 X4 X1) -> False) -> v5_taxonom2 X3 X2 -> r2_hidden X4 X3 -> m1_subset_1 X1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X3 X4 X1, (r2_hidden X4 X1 -> False) -> (r1_xboole_0 X1 (esk17_4 X2 X3 X1 X4) -> False) -> v5_taxonom2 X3 X2 -> r2_hidden X1 X3 -> m1_subset_1 X4 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (X1 = k1_xboole_0 -> False) -> (k3_tarski (k2_xboole_0 X2 (k1_tarski X1))) = (k5_setfam_1 X3 X2) -> v4_taxonom2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r1_xboole_0 X1 (esk38_3 X3 X1 X2) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (m1_subset_1 (k2_xboole_0 X1 (k1_tarski X2)) (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False) -> v4_taxonom2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r1_xboole_0 X2 (esk38_3 X3 X2 X1) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v4_taxonom2 (k2_xboole_0 X1 (k1_tarski X2)) -> False) -> v4_taxonom2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r1_xboole_0 X2 (esk38_3 X3 X2 X1) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk38_3 X3 X1 X2) X2 -> False) -> (k3_tarski (k2_xboole_0 X2 (k1_tarski X1))) = (k5_setfam_1 X3 X2) -> v4_taxonom2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> v5_taxonom2 X2 X3 -> m1_taxonom2 X2 X3 -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r2_hidden X1 (esk37_3 X3 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> v5_taxonom2 X4 X3 -> m1_taxonom2 X4 X3 -> v3_abian X4 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r2_hidden X2 (esk37_3 X3 X4 X1) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk38_3 X3 X2 X1) X1 -> False) -> (m1_subset_1 (k2_xboole_0 X1 (k1_tarski X2)) (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False) -> v4_taxonom2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden X1 (esk37_3 X4 X2 X3) -> False) -> v5_taxonom2 X2 X4 -> m1_taxonom2 X2 X4 -> r2_hidden X3 X1 -> r2_hidden X1 X2 -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X4)) -> False)
  -> (forall X3 X2 X1, (v4_taxonom2 (k2_xboole_0 X1 (k1_tarski X2)) -> False) -> (r2_hidden (esk38_3 X3 X2 X1) X1 -> False) -> v4_taxonom2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1 X3 X2, (v5_taxonom2 X3 X2 -> False) -> r2_hidden X1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> r2_hidden (esk19_2 X2 X3) X1 -> r1_xboole_0 (esk18_2 X2 X3) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> (r1_tarski (esk20_3 X1 X2 X3) (k1_setfam_1 X3) -> False) -> v6_ordinal1 X3 -> v6_taxonom2 X2 X1 -> r1_tarski X3 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> (r2_hidden (esk20_3 X1 X2 X3) X2 -> False) -> v6_ordinal1 X3 -> v6_taxonom2 X2 X1 -> r1_tarski X3 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, ((esk10_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r1_xboole_0 (esk10_2 X1 X2) (esk11_2 X1 X2) -> False)
  -> (forall X1, ((k5_setfam_1 esk1_0 esk4_0) = (k5_setfam_1 esk1_0 X1) -> False) -> v4_taxonom2 X1 -> r1_tarski X1 esk2_0 -> r2_hidden esk3_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> r1_tarski (k5_setfam_1 esk1_0 esk4_0) (k5_setfam_1 esk1_0 X1) -> False)
  -> (forall X1 X2 X3, (v6_taxonom2 X2 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> r1_tarski X1 (k1_setfam_1 (esk21_2 X3 X2)) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> (r1_xboole_0 X4 X1 -> False) -> r2_hidden X4 X3 -> r2_hidden X1 X3 -> m1_eqrel_1 X3 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, (v5_taxonom2 X2 X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden (esk19_2 X1 X2) (esk18_2 X1 X2) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk13_2 X1 X2) X3 -> r2_hidden (esk13_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk12_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk12_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2, ((esk10_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk11_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, ((esk10_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> (esk11_2 X1 X2) = (esk10_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, ((esk10_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk10_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X3 X1, X1 = k1_xboole_0 -> r2_hidden X1 X2 -> m1_eqrel_1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = X2 -> False) -> v3_abian X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, (v5_taxonom2 X2 X1 -> False) -> (m1_subset_1 (esk18_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk13_2 X1 X2) X2 -> False) -> (r2_hidden (esk13_2 X1 X2) (esk14_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (v6_taxonom2 X2 X1 -> False) -> (r1_tarski (esk21_2 X1 X2) X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (v5_taxonom2 X2 X1 -> False) -> (m1_subset_1 (esk19_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (v5_taxonom2 X2 X1 -> False) -> (r2_hidden (esk18_2 X1 X2) X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, (v6_taxonom2 X2 X1 -> False) -> (v6_ordinal1 (esk21_2 X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X3 X2, (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (r1_xboole_0 X2 X3 -> False) -> v3_taxonom2 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk5_2 X1 X2) = X1 -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1 X2, ((k5_setfam_1 X1 X2) = X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (v6_taxonom2 X2 X1 -> False) -> (esk21_2 X1 X2) = k1_xboole_0 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk13_2 X1 X2) X2 -> False) -> (r2_hidden (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) X2 -> False) -> r1_tarski X3 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v3_taxonom2 X1 -> False) -> m1_taxonom2 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (m1_taxonom2 X1 X2 -> False) -> v3_taxonom2 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (r1_xboole_0 X2 X3 -> False) -> v4_taxonom2 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X1 X2 X3, (r3_xboole_0 X2 X3 -> False) -> v6_ordinal1 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk5_2 X1 X2) = X1 -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_taxonom2 X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk39_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk39_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (r1_tarski X2 X1 -> False) -> (r1_tarski X1 X2 -> False) -> r3_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski (k3_tarski X1) (k3_tarski X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> r3_xboole_0 (esk22_1 X1) (esk23_1 X1) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> r1_xboole_0 (esk8_1 X1) (esk9_1 X1) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> r1_tarski (esk9_1 X1) (esk8_1 X1) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> r1_tarski (esk8_1 X1) (esk9_1 X1) -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> r1_xboole_0 (esk15_1 X1) (esk16_1 X1) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski (k1_setfam_1 X2) X1 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X1 = (k1_tarski X2) -> False) -> r1_tarski X1 (k1_tarski X2) -> False)
  -> (forall X2 X1, (r3_xboole_0 X1 X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X2 X1 -> False) -> r3_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X2 X1 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 (k1_tarski X2) -> False) -> X1 = (k1_tarski X2) -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> (r2_hidden (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> (r2_hidden (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> (r2_hidden (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> (r2_hidden (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk35_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> (r2_hidden (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> (r2_hidden (esk15_1 X1) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 (k1_tarski X2) -> False) -> X1 = k1_xboole_0 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk34_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v4_taxonom2 X1 -> False) -> (esk16_1 X1) = (esk15_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk29_1 X1) -> False) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk32_1 X1) X1 -> False)
  -> (m1_eqrel_1 esk4_0 esk1_0 -> False)
  -> (r2_hidden k1_xboole_0 esk2_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1, (v3_abian (esk36_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> False) -> False)
  -> ((v3_abian esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_taxonom2 (esk36_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_taxonom2 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_taxonom2 (esk36_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r3_xboole_0 X1 X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((m1_eqrel_1 k1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((r1_tarski esk4_0 esk2_0 -> False) -> False)
  -> ((r2_hidden esk3_0 esk4_0 -> False) -> False)
  -> ((v6_taxonom2 esk2_0 esk1_0 -> False) -> False)
  -> ((m1_taxonom2 esk2_0 esk1_0 -> False) -> False)
  -> ((v5_taxonom2 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v4_taxonom2 (esk33_1 X1) -> False) -> False)
  -> (((k1_zfmisc_1 k1_xboole_0) = (k1_tarski k1_xboole_0) -> False) -> False)
  -> ((v1_xboole_0 esk28_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v4_taxonom2 esk4_0 -> False) -> False)
  -> False.
Admitted.
