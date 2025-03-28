(** $I sig/MizarPreamble.mgs **)

Theorem t19_toler_1:
 forall esk6_3:set -> set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall esk31_4:set -> set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk30_3:set -> set -> set -> set,
 forall esk21_2:set -> set -> set,
 forall esk17_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall esk12_2:set -> set -> set,
 forall k1_xboole_0:set,
 forall esk33_2:set -> set -> set,
 forall esk34_1:set -> set,
 forall esk32_1:set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk13_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall r3_xboole_0:set -> set -> prop,
 forall esk14_1:set -> set,
 forall esk15_1:set -> set,
 forall esk29_1:set -> set,
 forall v8_relat_2:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v7_relat_2:set -> prop,
 forall v5_relat_2:set -> prop,
 forall v2_relat_2:set -> prop,
 forall esk26_0:set,
 forall esk19_2:set -> set -> set,
 forall esk27_2:set -> set -> set,
 forall esk25_1:set -> set,
 forall o_1_0_toler_1:set -> set,
 forall esk24_0:set,
 forall esk22_0:set,
 forall esk16_1:set -> set,
 forall esk23_1:set -> set,
 forall esk18_0:set,
 forall esk28_1:set -> set,
 forall v4_relat_2:set -> prop,
 forall v6_relat_2:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk20_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk9_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk11_3:set -> set -> set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk10_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall v1_relat_2:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall m1_toler_1:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall esk7_4:set -> set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall v1_toler_1:set -> set -> set -> prop,
 forall v3_relat_2:set -> prop,
 forall r2_hidden:set -> set -> prop,
     (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> v1_relat_2 X3 -> v3_relat_2 X3 -> v1_partfun1 X3 X2 -> r2_hidden X1 X2 -> m1_toler_1 X4 X2 X3 -> v1_toler_1 X4 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k2_tarski (k2_tarski X1 (esk7_4 X2 X3 X4 X1)) (k1_tarski X1)) X3 -> False)
  -> (forall X3 X1 X2, (m1_toler_1 X3 X1 X2 -> False) -> v1_relat_2 X2 -> v3_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> r2_hidden (k2_tarski (k2_tarski (esk5_3 X1 X2 X3) (esk6_3 X1 X2 X3)) (k1_tarski (esk5_3 X1 X2 X3))) X2 -> False)
  -> (forall X1 X4 X3 X2, (v1_toler_1 X2 X3 X4 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk8_3 X3 X4 X2) X1) (k1_tarski (esk8_3 X3 X4 X2))) X4 -> False) -> v1_relat_2 X4 -> v3_relat_2 X4 -> v1_partfun1 X4 X3 -> r2_hidden X1 X2 -> m1_toler_1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X4 X2 X3, (r1_tarski X1 (esk31_4 X2 X3 X1 X4) -> False) -> v1_relat_2 X3 -> v3_relat_2 X3 -> v1_partfun1 X3 X2 -> m1_toler_1 X1 X2 X3 -> r2_hidden X4 (esk30_3 X2 X3 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1 X4 X3, (r2_hidden X4 X3 -> False) -> (r2_hidden (esk7_4 X1 X2 X3 X4) X3 -> False) -> v1_relat_2 X2 -> v3_relat_2 X2 -> v1_partfun1 X2 X1 -> r2_hidden X4 X1 -> m1_toler_1 X3 X1 X2 -> v1_toler_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X4 X1 X2 X3, ((esk31_4 X2 X3 X4 X1) = X1 -> False) -> v1_relat_2 X3 -> v3_relat_2 X3 -> v1_partfun1 X3 X2 -> m1_toler_1 X4 X2 X3 -> r2_hidden X1 (esk30_3 X2 X3 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X4 X5 X3 X2 X1, (r2_hidden X1 (esk30_3 X2 X3 X5) -> False) -> X1 = X4 -> v1_relat_2 X3 -> v3_relat_2 X3 -> v1_partfun1 X3 X2 -> r1_tarski X5 X4 -> m1_toler_1 X5 X2 X3 -> m1_toler_1 X1 X2 X3 -> r2_hidden X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X1 X2, (v1_toler_1 X3 X1 X2 -> False) -> v1_relat_2 X2 -> v3_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_toler_1 X3 X1 X2 -> r2_hidden (esk8_3 X1 X2 X3) X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X4 X3 X2 X1, (m1_toler_1 X1 X2 X3 -> False) -> v1_relat_2 X3 -> v3_relat_2 X3 -> v1_partfun1 X3 X2 -> m1_toler_1 X4 X2 X3 -> r2_hidden X1 (esk30_3 X2 X3 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 (k1_zfmisc_1 X2) -> False) -> v1_relat_2 X3 -> v3_relat_2 X3 -> v1_partfun1 X3 X2 -> m1_toler_1 X4 X2 X3 -> r2_hidden X1 (esk30_3 X2 X3 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X1 X2, (v1_toler_1 X3 X1 X2 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> v1_relat_2 X2 -> v3_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_toler_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X4 X3 X1, (r2_hidden (k2_tarski (k2_tarski X4 X3) (k1_tarski X4)) X1 -> False) -> v3_relat_2 X1 -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk10_3 X1 X2 X3) X3 -> r2_hidden (esk10_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk10_3 X1 X2 X3) X3 -> r2_hidden (esk10_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X1 X4 X5 X3, (r2_hidden (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) X3 -> False) -> v1_relat_2 X3 -> v3_relat_2 X3 -> v1_partfun1 X3 X2 -> r2_hidden X5 X1 -> r2_hidden X4 X1 -> m1_toler_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X1 X2, (m1_toler_1 X3 X1 X2 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> v1_relat_2 X2 -> v3_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X1 X2, (m1_toler_1 X3 X1 X2 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> v1_relat_2 X2 -> v3_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> v1_relat_2 X2 -> v1_partfun1 X2 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> r2_hidden (k2_tarski (k2_tarski X1 X1) (k1_tarski X1)) X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden (k2_tarski (k2_tarski X1 X1) (k1_tarski X1)) X3 -> False) -> v1_relat_2 X3 -> v1_partfun1 X3 X2 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X3 X2, (r1_tarski X3 X2 -> False) -> v1_relat_2 X1 -> v3_relat_2 X1 -> v1_partfun1 X1 X2 -> m1_toler_1 X3 X2 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X2, (v1_toler_1 (esk21_2 X1 X2) X1 X2 -> False) -> v1_relat_2 X2 -> v3_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (m1_toler_1 (esk21_2 X1 X2) X1 X2 -> False) -> v1_relat_2 X2 -> v3_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1, (m1_toler_1 (esk17_2 X2 X1) X2 X1 -> False) -> v1_relat_2 X1 -> v3_relat_2 X1 -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1, r1_tarski esk3_0 X1 -> m1_toler_1 X1 esk1_0 esk2_0 -> v1_toler_1 X1 esk1_0 esk2_0 -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk12_2 X1 X2) X3 -> r2_hidden (esk12_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk11_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk11_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X3 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk34_1 X2) -> False) -> r2_hidden X3 X2 -> r2_hidden X1 X2 -> r1_tarski (esk34_1 X2) X1 -> r1_tarski (esk33_2 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk34_1 X2) -> False) -> (r2_hidden (esk33_2 X2 X3) (esk32_1 X2) -> False) -> r2_hidden X3 X2 -> r2_hidden X1 X2 -> r1_tarski (esk34_1 X2) X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> (r2_hidden (esk12_2 X1 X2) (esk13_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk34_1 X1) X1 -> False) -> r2_hidden X2 X1 -> r1_tarski (esk33_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk4_2 X1 X2) = X1 -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk34_1 X1) X1 -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_1 X1) -> False) -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> (r2_hidden (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) X2 -> False) -> r1_tarski X3 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk34_1 X2) -> False) -> (r1_tarski (esk32_1 X2) X2 -> False) -> r2_hidden X1 X2 -> r1_tarski (esk34_1 X2) X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk34_1 X2) -> False) -> (v6_ordinal1 (esk32_1 X2) -> False) -> r2_hidden X1 X2 -> r1_tarski (esk34_1 X2) X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2 X3, (r3_xboole_0 X2 X3 -> False) -> v6_ordinal1 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk4_2 X1 X2) = X1 -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (r1_tarski X2 X1 -> False) -> (r1_tarski X1 X2 -> False) -> r3_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski (k3_tarski X1) (k3_tarski X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden X1 X2 -> False) -> r1_tarski (k1_tarski X1) X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> r3_xboole_0 (esk14_1 X1) (esk15_1 X1) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski (k1_tarski X1) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r1_tarski (esk32_1 X1) X1 -> False) -> (r2_hidden (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X1 X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X2 X1 -> False) -> r3_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X2 X1 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (v6_ordinal1 (esk32_1 X1) -> False) -> (r2_hidden (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v3_relat_2 X1 -> v1_relat_1 X1 -> v8_relat_2 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> (r2_hidden (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> (r2_hidden (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v6_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v5_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk28_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0)) -> False) -> False)
  -> ((m1_toler_1 esk3_0 esk1_0 esk2_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk27_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk27_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (o_1_0_toler_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r3_xboole_0 X1 X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((v1_partfun1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, ((k3_tarski (k1_zfmisc_1 X1)) = X1 -> False) -> False)
  -> (forall X1, (v8_relat_2 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_2 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk25_1 X1) -> False) -> False)
  -> (forall X1, (v3_relat_2 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_2 (esk23_1 X1) -> False) -> False)
  -> ((v2_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v3_relat_2 esk2_0 -> False) -> False)
  -> ((v1_relat_2 esk2_0 -> False) -> False)
  -> False.
Admitted.
