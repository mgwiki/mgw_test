(** $I sig/MizarPreamble.mgs **)

Theorem t20_transgeo:
 forall esk5_3:set -> set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall r1_transgeo:set -> set -> set -> prop,
 forall epred1_3:set -> set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk26_2:set -> set -> set,
 forall v3_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk29_0:set,
 forall esk21_2:set -> set -> set,
 forall esk19_2:set -> set -> set,
 forall esk24_1:set -> set,
 forall esk17_1:set -> set,
 forall esk18_0:set,
 forall esk22_0:set,
 forall esk23_0:set,
 forall esk28_2:set -> set -> set,
 forall esk20_2:set -> set -> set,
 forall esk25_0:set,
 forall esk27_0:set,
 forall k1_xboole_0:set,
 forall r1_tarski:set -> set -> prop,
 forall v4_funct_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v2_funct_2:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk12_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall r3_relat_2:set -> set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk8_3:set -> set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk7_4:set -> set -> set -> set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall r2_transgeo:set -> set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k4_tarski:set -> set -> set,
 forall esk13_3:set -> set -> set -> set,
 forall esk14_3:set -> set -> set -> set,
 forall esk15_3:set -> set -> set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall v3_funct_2:set -> set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> r2_hidden (k4_tarski (k4_tarski (esk13_3 X1 X2 X3) (esk14_3 X1 X2 X3)) (k4_tarski (esk15_3 X1 X2 X3) (esk16_3 X1 X2 X3))) X3 -> r2_hidden (k4_tarski (k4_tarski (k3_funct_2 X1 X1 X2 (esk13_3 X1 X2 X3)) (k3_funct_2 X1 X1 X2 (esk14_3 X1 X2 X3))) (k4_tarski (k3_funct_2 X1 X1 X2 (esk15_3 X1 X2 X3)) (k3_funct_2 X1 X1 X2 (esk16_3 X1 X2 X3)))) X3 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> (r2_hidden (k4_tarski (k4_tarski (esk13_3 X1 X2 X3) (esk14_3 X1 X2 X3)) (k4_tarski (esk15_3 X1 X2 X3) (esk16_3 X1 X2 X3))) X3 -> False) -> (r2_hidden (k4_tarski (k4_tarski (k3_funct_2 X1 X1 X2 (esk13_3 X1 X2 X3)) (k3_funct_2 X1 X1 X2 (esk14_3 X1 X2 X3))) (k4_tarski (k3_funct_2 X1 X1 X2 (esk15_3 X1 X2 X3)) (k3_funct_2 X1 X1 X2 (esk16_3 X1 X2 X3)))) X3 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X7 X4 X3 X6 X5 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k4_tarski (k4_tarski X3 X4) (k4_tarski X5 X6)) X7 -> False) -> v1_funct_1 X2 -> m1_subset_1 X6 X1 -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> r2_transgeo X1 X2 X7 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> r2_hidden (k4_tarski (k4_tarski (k3_funct_2 X1 X1 X2 X3) (k3_funct_2 X1 X1 X2 X4)) (k4_tarski (k3_funct_2 X1 X1 X2 X5) (k3_funct_2 X1 X1 X2 X6))) X7 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_transgeo X1 X2 X3 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> r2_hidden (k4_tarski (k4_tarski (esk4_3 X1 X2 X3) (esk5_3 X1 X2 X3)) (k4_tarski (k3_funct_2 X1 X1 X2 (esk4_3 X1 X2 X3)) (k3_funct_2 X1 X1 X2 (esk5_3 X1 X2 X3)))) X3 -> False)
  -> (forall X7 X3 X1 X5 X2 X4 X6, (v1_xboole_0 X6 -> False) -> (r2_hidden (k4_tarski (k4_tarski (k3_funct_2 X6 X6 X7 X1) (k3_funct_2 X6 X6 X7 X2)) (k4_tarski (k3_funct_2 X6 X6 X7 X3) (k3_funct_2 X6 X6 X7 X4))) X5 -> False) -> v1_funct_1 X7 -> m1_subset_1 X4 X6 -> m1_subset_1 X3 X6 -> m1_subset_1 X2 X6 -> m1_subset_1 X1 X6 -> v1_funct_2 X7 X6 X6 -> v3_funct_2 X7 X6 X6 -> r2_transgeo X6 X7 X5 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 X6 X6)) -> r2_hidden (k4_tarski (k4_tarski X1 X2) (k4_tarski X3 X4)) X5 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X6 X6) (k2_zfmisc_1 X6 X6))) -> False)
  -> (forall X2 X4 X3 X5 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k4_tarski (k4_tarski X4 X5) (k4_tarski (k3_funct_2 X1 X1 X2 X4) (k3_funct_2 X1 X1 X2 X5))) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> r1_transgeo X1 X2 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X3 X2 X4 X1, ((k4_tarski (esk6_4 X2 X3 X4 X1) (esk7_4 X2 X3 X4 X1)) = X1 -> False) -> X4 = (k2_zfmisc_1 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk16_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk15_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk14_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk13_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk5_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk4_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X8 X5 X4 X7 X6 X9 X2 X1 X3, (X1 = X3 -> False) -> (r2_hidden (k4_tarski (k4_tarski X4 X5) (k4_tarski X6 X7)) X8 -> False) -> m1_subset_1 X7 X2 -> m1_subset_1 X6 X2 -> m1_subset_1 X5 X2 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> epred1_3 X2 X9 X8 -> r2_hidden (k4_tarski (k4_tarski X4 X5) (k4_tarski X1 X3)) X8 -> r2_hidden (k4_tarski (k4_tarski X1 X3) (k4_tarski X6 X7)) X8 -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk7_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk6_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> ((k4_tarski (esk9_3 X1 X2 X3) (esk10_3 X1 X2 X3)) = (esk8_3 X1 X2 X3) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X5 X4 X1 X2 X3, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (esk8_3 X1 X2 X3) = (k4_tarski X4 X5) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden (esk8_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (k1_funct_1 X1 X3) = (k1_funct_1 X1 X4) -> v1_funct_1 X1 -> v2_funct_1 X1 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X6 X1 X4 X3 X5, (r2_hidden (k4_tarski (k4_tarski X1 X1) (k4_tarski X3 X4)) X5 -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> epred1_3 X2 X6 X5 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X1, (r3_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k4_tarski (esk12_2 X1 X2) (esk11_2 X1 X2)) X1 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v2_funct_2 X1 X2 -> False) -> v1_funct_1 X1 -> v3_funct_2 X1 X3 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v3_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v3_funct_2 X1 X2 X3 -> False) -> v1_funct_1 X1 -> v2_funct_1 X1 -> v2_funct_2 X1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X4 X1, (r2_hidden (k4_tarski X4 X3) X1 -> False) -> v1_relat_1 X1 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> r3_relat_2 X1 X2 -> r2_hidden (k4_tarski X3 X4) X1 -> False)
  -> (forall X2 X1, (r3_relat_2 X1 X2 -> False) -> (r2_hidden (k4_tarski (esk11_2 X1 X2) (esk12_2 X1 X2)) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X2 X3, (r1_transgeo X1 X2 X3 -> False) -> epred1_3 X1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (r3_relat_2 X1 (k2_zfmisc_1 X2 X2) -> False) -> epred1_3 X2 X3 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X2 X1 X3 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k2_zfmisc_1 X2 X4) -> X5 = (k4_tarski X1 X3) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r3_relat_2 X1 X2 -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r3_relat_2 X1 X2 -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk26_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk26_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk26_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk26_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk26_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_transgeo esk1_0 esk2_0 esk3_0 -> False)
  -> (v3_funct_1 esk27_0 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0) (k2_zfmisc_1 esk1_0 esk1_0))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk21_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk19_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> (forall X1, (v3_funct_2 (esk24_1 X1) X1 X1 -> False) -> False)
  -> (forall X1, (v1_funct_2 (esk24_1 X1) X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0)) -> False) -> False)
  -> ((epred1_3 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((v3_funct_2 esk2_0 esk1_0 esk1_0 -> False) -> False)
  -> ((v1_funct_2 esk2_0 esk1_0 esk1_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk28_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk21_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk20_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk28_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk20_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk24_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk29_0 -> False) -> False)
  -> ((v2_funct_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
