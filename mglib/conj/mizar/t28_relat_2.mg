(** $I sig/MizarPreamble.mgs **)

Theorem t28_relat_2:
 forall k4_xboole_0:set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall esk1_0:set,
 forall v6_relat_2:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k1_relat_1:set -> set,
 forall r6_relat_2:set -> set -> prop,
 forall esk12_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v3_relat_2:set -> prop,
 forall v2_relat_2:set -> prop,
 forall v4_relat_2:set -> prop,
 forall v8_relat_2:set -> prop,
 forall v2_relat_1:set -> prop,
 forall k1_xboole_0:set,
 forall esk17_0:set,
 forall esk16_1:set -> set,
 forall esk18_0:set,
 forall esk19_0:set,
 forall esk21_2:set -> set -> set,
 forall esk20_0:set,
 forall v7_relat_2:set -> prop,
 forall v3_relat_1:set -> prop,
 forall k10_xtuple_0:set -> set,
 forall k9_xtuple_0:set -> set,
 forall v5_relat_2:set -> prop,
 forall v1_relat_2:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk9_2:set -> set -> set,
 forall esk3_2:set -> set -> set,
 forall esk2_2:set -> set -> set,
 forall k4_relat_1:set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall esk14_2:set -> set -> set,
 forall esk15_2:set -> set -> set,
 forall k2_relat_1:set -> set,
 forall esk5_4:set -> set -> set -> set -> set,
 forall esk4_4:set -> set -> set -> set -> set,
 forall k4_tarski:set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X3 X2 X4 X1, ((k4_tarski (esk4_4 X2 X3 X4 X1) (esk5_4 X2 X3 X4 X1)) = X1 -> False) -> X4 = (k2_zfmisc_1 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk5_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk4_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk11_3 X1 X2 X3) X3 -> r2_hidden (esk11_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X2, (X2 = (k2_relat_1 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> r2_hidden (k4_tarski (esk14_2 X1 X2) (esk15_2 X1 X2)) X2 -> r2_hidden (k4_tarski (esk15_2 X1 X2) (esk14_2 X1 X2)) X1 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> ((k4_tarski (esk7_3 X1 X2 X3) (esk8_3 X1 X2 X3)) = (esk6_3 X1 X2 X3) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk10_3 X1 X2 X3) X3 -> r2_hidden (esk10_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk10_3 X1 X2 X3) X3 -> r2_hidden (esk10_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X5 X4 X1 X2 X3, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (esk6_3 X1 X2 X3) = (k4_tarski X4 X5) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden (esk6_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X2, (X2 = (k4_relat_1 X1) -> False) -> (esk2_2 X1 X2) = (esk3_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden (esk2_2 X1 X2) X1 -> r2_hidden (k4_tarski (esk2_2 X1 X2) (esk3_2 X1 X2)) X2 -> False)
  -> (forall X2 X3 X1, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk11_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X1, (X2 = (k2_relat_1 X1) -> False) -> (r2_hidden (k4_tarski (esk14_2 X1 X2) (esk15_2 X1 X2)) X2 -> False) -> (r2_hidden (k4_tarski (esk15_2 X1 X2) (esk14_2 X1 X2)) X1 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (v6_relat_2 esk1_0 -> r1_tarski (k4_xboole_0 (k2_zfmisc_1 (k1_relat_1 esk1_0) (k1_relat_1 esk1_0)) (k4_relat_1 (k1_relat_1 esk1_0))) (k2_xboole_0 esk1_0 (k2_relat_1 esk1_0)) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k4_tarski (esk13_2 X1 X2) (esk12_2 X1 X2)) X1 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k4_tarski (esk12_2 X1 X2) (esk13_2 X1 X2)) X1 -> False)
  -> (forall X1 X2, (X2 = (k4_relat_1 X1) -> False) -> (r2_hidden (esk2_2 X1 X2) X1 -> False) -> (r2_hidden (k4_tarski (esk2_2 X1 X2) (esk3_2 X1 X2)) X2 -> False) -> v1_relat_1 X2 -> False)
  -> (forall X1 X2, (X2 = (k4_relat_1 X1) -> False) -> ((esk2_2 X1 X2) = (esk3_2 X1 X2) -> False) -> (r2_hidden (k4_tarski (esk2_2 X1 X2) (esk3_2 X1 X2)) X2 -> False) -> v1_relat_1 X2 -> False)
  -> ((v6_relat_2 esk1_0 -> False) -> (r1_tarski (k4_xboole_0 (k2_zfmisc_1 (k1_relat_1 esk1_0) (k1_relat_1 esk1_0)) (k4_relat_1 (k1_relat_1 esk1_0))) (k2_xboole_0 esk1_0 (k2_relat_1 esk1_0)) -> False) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (r2_hidden (k4_tarski X4 X3) X1 -> False) -> (r2_hidden (k4_tarski X3 X4) X1 -> False) -> v1_relat_1 X1 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> r6_relat_2 X1 X2 -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden (k4_tarski X2 X1) X4 -> False) -> X3 = (k2_relat_1 X4) -> v1_relat_1 X4 -> v1_relat_1 X3 -> r2_hidden (k4_tarski X1 X2) X3 -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden (k4_tarski X2 X1) X4 -> False) -> X4 = (k2_relat_1 X3) -> v1_relat_1 X4 -> v1_relat_1 X3 -> r2_hidden (k4_tarski X1 X2) X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k4_tarski X1 X3) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k4_tarski X3 X1) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k4_tarski X1 X3) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X4 X2 X1 X3 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k2_zfmisc_1 X2 X4) -> X5 = (k4_tarski X1 X3) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> X4 = (k4_relat_1 X2) -> v1_relat_1 X4 -> r2_hidden (k4_tarski X1 X3) X4 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden (k4_tarski X1 X3) X4 -> False) -> X1 = X3 -> X4 = (k4_relat_1 X2) -> v1_relat_1 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X4 X3 X1 X2, (X1 = X2 -> False) -> X3 = (k4_relat_1 X4) -> v1_relat_1 X3 -> r2_hidden (k4_tarski X1 X2) X3 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k4_xboole_0 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k4_xboole_0 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> (esk13_2 X1 X2) = (esk12_2 X1 X2) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> (r2_hidden (esk13_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k4_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X1 X2, (v3_relat_2 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v3_relat_2 X2 -> v3_relat_2 X1 -> False)
  -> (forall X1 X2, (v3_relat_2 (k4_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v3_relat_2 X2 -> v3_relat_2 X1 -> False)
  -> (forall X1 X2, (v2_relat_2 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_2 X2 -> v2_relat_2 X1 -> False)
  -> (forall X1 X2, (v1_relat_2 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_relat_2 X2 -> v1_relat_2 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (v5_relat_2 (k4_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_2 X1 -> False)
  -> (forall X2 X1, (v4_relat_2 (k4_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_2 X1 -> False)
  -> (forall X2 X1, (v2_relat_2 (k4_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_2 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v6_relat_2 X1 -> False) -> v1_relat_1 X1 -> r6_relat_2 X1 (k1_relat_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1, ((k2_xboole_0 (k9_xtuple_0 X1) (k10_xtuple_0 X1)) = (k1_relat_1 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k4_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (r6_relat_2 X1 (k1_relat_1 X1) -> False) -> v1_relat_1 X1 -> v6_relat_2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v5_relat_2 X1 -> False) -> v1_relat_1 X1 -> v2_relat_2 X1 -> v8_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_relat_1 X1 -> v3_relat_2 X1 -> v8_relat_2 X1 -> False)
  -> (forall X1, (v8_relat_2 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v8_relat_2 X1 -> False)
  -> (forall X1, (v5_relat_2 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v5_relat_2 X1 -> False)
  -> (forall X1, (v4_relat_2 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v4_relat_2 X1 -> False)
  -> (forall X1, (v3_relat_2 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v3_relat_2 X1 -> False)
  -> (forall X1, (v2_relat_2 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v2_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_2 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v1_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v8_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v5_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v4_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v3_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v2_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> v1_relat_2 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_relat_2 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_relat_2 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_relat_2 X1 -> False) -> v1_relat_1 X1 -> v5_relat_2 X1 -> False)
  -> (forall X1, (v4_relat_2 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_2 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_relat_2 X1 -> False) -> v1_relat_1 X1 -> v5_relat_2 X1 -> False)
  -> (forall X1, (v2_relat_2 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_relat_2 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_relat_1 (k2_relat_1 X1)) = X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k2_relat_1 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_relat_1 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_relat_1 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (forall X2 X1, (v5_relat_1 (esk21_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_relat_1 (k4_relat_1 X1)) = (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k10_xtuple_0 (k4_relat_1 X1)) = X1 -> False) -> False)
  -> (forall X1, ((k9_xtuple_0 (k4_relat_1 X1)) = X1 -> False) -> False)
  -> (forall X1, (v8_relat_2 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_2 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v3_relat_2 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> ((v2_relat_1 esk19_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
