(** $I sig/MizarPreamble.mgs **)

Theorem t21_transgeo:
 forall esk6_3:set -> set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall r1_transgeo:set -> set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall k1_xboole_0:set,
 forall v1_relat_1:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v4_funct_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v3_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk23_0:set,
 forall esk15_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall esk18_1:set -> set,
 forall esk17_0:set,
 forall esk16_0:set,
 forall esk12_0:set,
 forall esk11_1:set -> set,
 forall esk22_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk19_0:set,
 forall esk21_0:set,
 forall esk20_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall v2_funct_1:set -> prop,
 forall k2_funct_1:set -> set,
 forall v2_funct_2:set -> set -> prop,
 forall k3_relat_1:set -> set -> set,
 forall k1_transgeo:set -> set -> set -> set,
 forall k2_transgeo:set -> set -> set -> set,
 forall k2_funct_2:set -> set -> set,
 forall r2_transgeo:set -> set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k4_tarski:set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall v3_funct_2:set -> set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> r2_hidden (k4_tarski (k4_tarski (esk7_3 X1 X2 X3) (esk8_3 X1 X2 X3)) (k4_tarski (esk9_3 X1 X2 X3) (esk10_3 X1 X2 X3))) X3 -> r2_hidden (k4_tarski (k4_tarski (k3_funct_2 X1 X1 X2 (esk7_3 X1 X2 X3)) (k3_funct_2 X1 X1 X2 (esk8_3 X1 X2 X3))) (k4_tarski (k3_funct_2 X1 X1 X2 (esk9_3 X1 X2 X3)) (k3_funct_2 X1 X1 X2 (esk10_3 X1 X2 X3)))) X3 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> (r2_hidden (k4_tarski (k4_tarski (esk7_3 X1 X2 X3) (esk8_3 X1 X2 X3)) (k4_tarski (esk9_3 X1 X2 X3) (esk10_3 X1 X2 X3))) X3 -> False) -> (r2_hidden (k4_tarski (k4_tarski (k3_funct_2 X1 X1 X2 (esk7_3 X1 X2 X3)) (k3_funct_2 X1 X1 X2 (esk8_3 X1 X2 X3))) (k4_tarski (k3_funct_2 X1 X1 X2 (esk9_3 X1 X2 X3)) (k3_funct_2 X1 X1 X2 (esk10_3 X1 X2 X3)))) X3 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X7 X4 X3 X6 X5 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k4_tarski (k4_tarski X3 X4) (k4_tarski X5 X6)) X7 -> False) -> v1_funct_1 X2 -> m1_subset_1 X6 X1 -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> r2_transgeo X1 X2 X7 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> r2_hidden (k4_tarski (k4_tarski (k3_funct_2 X1 X1 X2 X3) (k3_funct_2 X1 X1 X2 X4)) (k4_tarski (k3_funct_2 X1 X1 X2 X5) (k3_funct_2 X1 X1 X2 X6))) X7 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_transgeo X1 X2 X3 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> r2_hidden (k4_tarski (k4_tarski (esk5_3 X1 X2 X3) (esk6_3 X1 X2 X3)) (k4_tarski (k3_funct_2 X1 X1 X2 (esk5_3 X1 X2 X3)) (k3_funct_2 X1 X1 X2 (esk6_3 X1 X2 X3)))) X3 -> False)
  -> (forall X7 X3 X1 X5 X2 X4 X6, (v1_xboole_0 X6 -> False) -> (r2_hidden (k4_tarski (k4_tarski (k3_funct_2 X6 X6 X7 X1) (k3_funct_2 X6 X6 X7 X2)) (k4_tarski (k3_funct_2 X6 X6 X7 X3) (k3_funct_2 X6 X6 X7 X4))) X5 -> False) -> v1_funct_1 X7 -> m1_subset_1 X4 X6 -> m1_subset_1 X3 X6 -> m1_subset_1 X2 X6 -> m1_subset_1 X1 X6 -> v1_funct_2 X7 X6 X6 -> v3_funct_2 X7 X6 X6 -> r2_transgeo X6 X7 X5 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 X6 X6)) -> r2_hidden (k4_tarski (k4_tarski X1 X2) (k4_tarski X3 X4)) X5 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X6 X6) (k2_zfmisc_1 X6 X6))) -> False)
  -> (forall X2 X4 X3 X5 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k4_tarski (k4_tarski X4 X5) (k4_tarski (k3_funct_2 X1 X1 X2 X4) (k3_funct_2 X1 X1 X2 X5))) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> r1_transgeo X1 X2 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X1 X2 X4) = X3 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 X1 (k2_funct_2 X1 X2) X3) = X4 -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X1 (k2_funct_2 X1 X2) X4) = X3 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 X1 X2 X3) = X4 -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk10_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk9_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk8_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_transgeo X1 X2 X3 -> False) -> (m1_subset_1 (esk5_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X3 X2 X1, ((k1_transgeo X1 (k2_funct_2 X1 X3) (k1_transgeo X1 X2 X3)) = (k2_transgeo X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_transgeo X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (k1_transgeo X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v3_funct_2 (k2_transgeo X1 X2 X3) X1 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k2_transgeo X1 X2 X3) X1 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1 X3, (v3_funct_2 (k1_transgeo X1 X2 X3) X1 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1 X3, (v1_funct_2 (k1_transgeo X1 X2 X3) X1 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k2_transgeo X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1 X3, (v1_funct_1 (k1_transgeo X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X3 X2, (v3_funct_2 (k3_relat_1 X1 X2) X3 X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X3 X3 -> v3_funct_2 X2 X3 X3 -> v3_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X3 X3 -> v3_funct_2 X2 X3 X3 -> v3_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X2 X3, ((k1_transgeo X2 X1 X3) = (k3_relat_1 X1 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_funct_2 X3 X2 X2 -> v1_funct_2 X1 X2 X2 -> v3_funct_2 X3 X2 X2 -> v3_funct_2 X1 X2 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X3 X3 -> v3_funct_2 X2 X3 X3 -> v3_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X4 X3 X1 X2 X5, (v1_xboole_0 X5 -> False) -> (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X5 X4 -> v1_funct_2 X1 X3 X5 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X5 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X4 X3 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X4 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X1 X2 X4 X5 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X5 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X2, (m1_subset_1 (k2_funct_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (v3_funct_2 (k2_funct_2 X1 X2) X1 X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X2, (v1_funct_2 (k2_funct_2 X1 X2) X1 X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X3 X2, (v2_funct_2 (k3_relat_1 X1 X2) X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_2 X2 X3 -> v2_funct_2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X5 X4 X2 X3, (X3 = k1_xboole_0 -> False) -> ((k1_funct_1 (k3_relat_1 X1 X4) X5) = (k1_funct_1 X4 (k1_funct_1 X1 X5)) -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X4 -> r2_hidden X5 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_funct_2 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_2 X2 X3 -> v2_funct_2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X2 X1, ((k2_funct_2 X2 X1) = (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X2 -> v3_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v2_funct_2 X1 X2 -> False) -> v1_funct_1 X1 -> v3_funct_2 X1 X3 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v3_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v3_funct_2 X1 X2 X3 -> False) -> v1_funct_1 X1 -> v2_funct_1 X1 -> v2_funct_2 X1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v2_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk20_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk20_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v2_funct_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_transgeo esk1_0 (k2_transgeo esk1_0 esk2_0 esk3_0) esk4_0 -> False)
  -> (v3_funct_1 esk21_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0) (k2_zfmisc_1 esk1_0 esk1_0))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk15_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk14_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk13_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> (forall X1, (v3_funct_2 (esk18_1 X1) X1 X1 -> False) -> False)
  -> (forall X1, (v1_funct_2 (esk18_1 X1) X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0)) -> False) -> False)
  -> ((r2_transgeo esk1_0 esk3_0 esk4_0 -> False) -> False)
  -> ((r1_transgeo esk1_0 esk2_0 esk4_0 -> False) -> False)
  -> ((v3_funct_2 esk3_0 esk1_0 esk1_0 -> False) -> False)
  -> ((v3_funct_2 esk2_0 esk1_0 esk1_0 -> False) -> False)
  -> ((v1_funct_2 esk3_0 esk1_0 esk1_0 -> False) -> False)
  -> ((v1_funct_2 esk2_0 esk1_0 esk1_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk22_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk15_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk14_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk13_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk22_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk18_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk23_0 -> False) -> False)
  -> ((v2_funct_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
