(** $I sig/MizarPreamble.mgs **)

Theorem t39_sysrel:
 forall esk15_3:set -> set -> set -> set,
 forall k4_relat_1:set -> set,
 forall esk3_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall k1_xboole_0:set,
 forall esk2_0:set,
 forall v5_relat_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v3_relat_1:set -> prop,
 forall esk17_0:set,
 forall esk21_2:set -> set -> set,
 forall esk16_1:set -> set,
 forall esk18_0:set,
 forall o_0_0_xboole_0:set,
 forall esk19_0:set,
 forall esk20_0:set,
 forall v2_relat_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk1_0:set,
 forall k1_sysrel:set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall k6_subset_1:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall esk9_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk13_3:set -> set -> set -> set,
 forall esk14_3:set -> set -> set -> set,
 forall k3_relat_1:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k1_tarski:set -> set,
 forall esk12_5:set -> set -> set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X2 X1 X4 X5 X3, (r2_hidden (k2_tarski (k2_tarski (esk12_5 X1 X2 X3 X4 X5) X5) (k1_tarski (esk12_5 X1 X2 X3 X4 X5))) X2 -> False) -> X3 = (k3_relat_1 X1 X2) -> v1_relat_1 X3 -> r2_hidden (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) X3 -> False)
  -> (forall X3 X2 X1 X5 X4, (r2_hidden (k2_tarski (k2_tarski X1 (esk12_5 X2 X3 X4 X1 X5)) (k1_tarski X1)) X2 -> False) -> X4 = (k3_relat_1 X2 X3) -> v1_relat_1 X4 -> r2_hidden (k2_tarski (k2_tarski X1 X5) (k1_tarski X1)) X4 -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X3 -> r2_hidden (k2_tarski (k2_tarski X4 (esk14_3 X1 X2 X3)) (k1_tarski X4)) X2 -> r2_hidden (k2_tarski (k2_tarski (esk13_3 X1 X2 X3) X4) (k1_tarski (esk13_3 X1 X2 X3))) X1 -> r2_hidden (k2_tarski (k2_tarski (esk13_3 X1 X2 X3) (esk14_3 X1 X2 X3)) (k1_tarski (esk13_3 X1 X2 X3))) X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k3_relat_1 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk13_3 X1 X2 X3) (esk14_3 X1 X2 X3)) (k1_tarski (esk13_3 X1 X2 X3))) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk15_3 X1 X2 X3) (esk14_3 X1 X2 X3)) (k1_tarski (esk15_3 X1 X2 X3))) X2 -> False) -> v1_relat_1 X3 -> False)
  -> (forall X1 X2 X3, (X3 = (k3_relat_1 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk13_3 X1 X2 X3) (esk14_3 X1 X2 X3)) (k1_tarski (esk13_3 X1 X2 X3))) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk13_3 X1 X2 X3) (esk15_3 X1 X2 X3)) (k1_tarski (esk13_3 X1 X2 X3))) X1 -> False) -> v1_relat_1 X3 -> False)
  -> (forall X1 X2, (X2 = (k4_relat_1 X1) -> False) -> (esk3_2 X1 X2) = (esk4_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden (esk3_2 X1 X2) X1 -> r2_hidden (k2_tarski (k2_tarski (esk3_2 X1 X2) (esk4_2 X1 X2)) (k1_tarski (esk3_2 X1 X2))) X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk8_2 X1 X2) (esk9_2 X1 X2)) (k1_tarski (esk8_2 X1 X2))) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk10_3 X1 X2 X3) X3 -> r2_hidden (esk10_3 X1 X2 X3) X2 -> r2_hidden (esk10_3 X1 X2 X3) X1 -> False)
  -> (forall X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski X1 (esk5_3 X3 X2 X1)) (k1_tarski X1)) X3 -> False) -> X2 = (k9_xtuple_0 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, (X2 = (k9_xtuple_0 X1) -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> r2_hidden (k2_tarski (k2_tarski (esk6_2 X1 X2) X3) (k1_tarski (esk6_2 X1 X2))) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk11_3 X1 X2 X3) X3 -> r2_hidden (esk11_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X2, (X2 = (k4_relat_1 X1) -> False) -> (r2_hidden (esk3_2 X1 X2) X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk3_2 X1 X2) (esk4_2 X1 X2)) (k1_tarski (esk3_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> False)
  -> (forall X5 X3 X2 X1 X4 X6, (r2_hidden (k2_tarski (k2_tarski X1 X4) (k1_tarski X1)) X6 -> False) -> X6 = (k3_relat_1 X3 X5) -> v1_relat_1 X6 -> r2_hidden (k2_tarski (k2_tarski X2 X4) (k1_tarski X2)) X5 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False)
  -> (forall X1 X2, (X2 = (k9_xtuple_0 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk6_2 X1 X2) (esk7_2 X1 X2)) (k1_tarski (esk6_2 X1 X2))) X1 -> False) -> False)
  -> (forall X1 X2, (X2 = (k4_relat_1 X1) -> False) -> ((esk3_2 X1 X2) = (esk4_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk3_2 X1 X2) (esk4_2 X1 X2)) (k1_tarski (esk3_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk8_2 X1 X2) (esk9_2 X1 X2)) (k1_tarski (esk8_2 X1 X2))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk11_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X4 X2, (r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X2 -> False) -> v1_relat_1 X1 -> r1_tarski X1 X2 -> r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk11_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X1, ((k3_relat_1 (k6_subset_1 X1 (k4_relat_1 (k9_xtuple_0 X1))) X2) = k1_xboole_0 -> False) -> (k3_relat_1 X1 X2) = X2 -> (k3_relat_1 (k6_subset_1 X1 (k4_relat_1 (k9_xtuple_0 X1))) X1) = k1_xboole_0 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, ((k3_relat_1 X1 (k6_subset_1 X2 (k4_relat_1 (k9_xtuple_0 X2)))) = k1_xboole_0 -> False) -> (k3_relat_1 X1 X2) = X1 -> (k3_relat_1 X2 (k6_subset_1 X2 (k4_relat_1 (k9_xtuple_0 X2)))) = k1_xboole_0 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> X4 = (k4_relat_1 X2) -> v1_relat_1 X4 -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) X4 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k9_xtuple_0 X3) -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False)
  -> (forall X4 X3 X1 X2, (X1 = X2 -> False) -> X3 = (k4_relat_1 X4) -> v1_relat_1 X3 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) X4 -> False) -> X1 = X3 -> X4 = (k4_relat_1 X2) -> v1_relat_1 X4 -> r2_hidden X1 X2 -> False)
  -> (((k3_relat_1 esk2_0 (k6_subset_1 esk2_0 (k4_relat_1 (k9_xtuple_0 esk2_0)))) = k1_xboole_0 -> False) -> ((k3_relat_1 (k6_subset_1 esk2_0 (k4_relat_1 (k9_xtuple_0 esk2_0))) esk2_0) = k1_xboole_0 -> False) -> False)
  -> (((k3_relat_1 (k6_subset_1 esk2_0 (k4_relat_1 (k9_xtuple_0 esk2_0))) esk2_0) = k1_xboole_0 -> False) -> r1_tarski (k1_sysrel esk1_0) (k1_sysrel esk2_0) -> False)
  -> (((k3_relat_1 esk2_0 (k6_subset_1 esk2_0 (k4_relat_1 (k9_xtuple_0 esk2_0)))) = k1_xboole_0 -> False) -> r1_tarski (k1_sysrel esk1_0) (k1_sysrel esk2_0) -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k6_subset_1 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (((k3_relat_1 esk1_0 esk2_0) = esk1_0 -> False) -> ((k3_relat_1 (k6_subset_1 esk2_0 (k4_relat_1 (k9_xtuple_0 esk2_0))) esk2_0) = k1_xboole_0 -> False) -> False)
  -> (((k3_relat_1 esk2_0 esk1_0) = esk1_0 -> False) -> ((k3_relat_1 esk2_0 (k6_subset_1 esk2_0 (k4_relat_1 (k9_xtuple_0 esk2_0)))) = k1_xboole_0 -> False) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k6_subset_1 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k6_subset_1 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2, (v2_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (((k3_relat_1 esk2_0 esk1_0) = esk1_0 -> False) -> r1_tarski (k1_sysrel esk1_0) (k1_sysrel esk2_0) -> False)
  -> (((k3_relat_1 esk1_0 esk2_0) = esk1_0 -> False) -> r1_tarski (k1_sysrel esk1_0) (k1_sysrel esk2_0) -> False)
  -> (forall X1, ((k3_xboole_0 X1 (k4_relat_1 (k9_xtuple_0 X1))) = (k1_sysrel X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k6_subset_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (((k3_relat_1 esk1_0 esk2_0) = esk1_0 -> False) -> ((k3_relat_1 esk2_0 esk1_0) = esk1_0 -> False) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 (k1_sysrel X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (r1_tarski (k1_sysrel esk1_0) (k1_sysrel esk2_0) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk21_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k9_xtuple_0 (k4_relat_1 X1)) = X1 -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> ((v2_relat_1 esk19_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
