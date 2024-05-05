(** $I sig/MizarPreamble.mgs **)

Theorem t12_substlat:
 forall esk8_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk29_2:set -> set -> set,
 forall v4_funct_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk19_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_finset_1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk28_0:set,
 forall esk26_0:set,
 forall esk22_0:set,
 forall esk6_1:set -> set,
 forall esk20_0:set,
 forall esk18_0:set,
 forall o_0_0_xboole_0:set,
 forall esk16_0:set,
 forall esk21_2:set -> set -> set,
 forall esk15_0:set,
 forall esk23_0:set,
 forall esk27_0:set,
 forall esk24_0:set,
 forall esk17_2:set -> set -> set,
 forall k1_xboole_0:set,
 forall v3_finsub_1:set -> prop,
 forall v1_finsub_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk25_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v5_finset_1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v4_finsub_1:set -> prop,
 forall k1_finsub_1:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk30_4:set -> set -> set -> set -> set,
 forall k3_substlat:set -> set -> set -> set,
 forall esk14_4:set -> set -> set -> set -> set,
 forall esk12_4:set -> set -> set -> set -> set,
 forall esk10_4:set -> set -> set -> set -> set,
 forall esk11_4:set -> set -> set -> set -> set,
 forall esk9_4:set -> set -> set -> set -> set,
 forall k1_substlat:set -> set -> set,
 forall v1_finset_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k5_finsub_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k4_partfun1:set -> set -> set,
 forall esk13_5:set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_3_0_substlat:set -> set -> set -> set,
     (forall X5 X4 X3 X2 X1, (r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> False) -> X1 = X5 -> (esk13_5 X1 X2 X3 X4 X5) = X5 -> v1_finset_1 X5 -> m1_subset_1 X5 (k4_partfun1 X2 X3) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r1_tarski (esk13_5 X1 X2 X3 X4 X5) X5 -> r2_hidden (esk13_5 X1 X2 X3 X4 X5) X4 -> False)
  -> (forall X5 X4 X3 X2 X1, ((esk13_5 X1 X2 X3 X4 X5) = X5 -> False) -> (r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> False) -> (r2_hidden (esk13_5 X1 X2 X3 X4 X5) X4 -> False) -> X1 = X5 -> v1_finset_1 X5 -> m1_subset_1 X5 (k4_partfun1 X2 X3) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X5 X4 X3 X2 X1, ((esk13_5 X1 X2 X3 X4 X5) = X5 -> False) -> (r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> False) -> (r1_tarski (esk13_5 X1 X2 X3 X4 X5) X5 -> False) -> X1 = X5 -> v1_finset_1 X5 -> m1_subset_1 X5 (k4_partfun1 X2 X3) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X5 X4 X3 X2 X1, (r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> False) -> (m1_subset_1 (esk13_5 X1 X2 X3 X4 X5) (k4_partfun1 X2 X3) -> False) -> X1 = X5 -> v1_finset_1 X5 -> m1_subset_1 X5 (k4_partfun1 X2 X3) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r1_tarski (esk10_4 X1 X2 X3 X4) (esk11_4 X1 X2 X3 X4) -> False) -> X1 = X4 -> v1_finset_1 (esk9_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> X1 = X4 -> (esk11_4 X1 X2 X3 X4) = (esk10_4 X1 X2 X3 X4) -> v1_finset_1 (esk9_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False) -> (r1_tarski (esk10_4 X1 X2 X3 X4) (esk11_4 X1 X2 X3 X4) -> False) -> X1 = X4 -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (m1_subset_1 (esk11_4 X1 X2 X3 X4) (k4_partfun1 X2 X3) -> False) -> X1 = X4 -> v1_finset_1 (esk9_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) (k4_partfun1 X2 X3) -> False) -> X1 = X4 -> v1_finset_1 (esk9_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> X1 = X4 -> v1_finset_1 (esk9_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X4 -> False) -> X1 = X4 -> v1_finset_1 (esk9_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False) -> X1 = X4 -> (esk11_4 X1 X2 X3 X4) = (esk10_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X5 X4 X3 X1 X2, (X1 = (esk12_4 X3 X4 X5 X2) -> False) -> r2_hidden X1 X2 -> m1_subset_1 X1 (k4_partfun1 X4 X5) -> r2_hidden X3 (a_3_0_substlat X4 X5 X2) -> m1_subset_1 X2 (k5_finsub_1 (k4_partfun1 X4 X5)) -> r1_tarski X1 (esk12_4 X3 X4 X5 X2) -> False)
  -> (forall X5 X2 X3 X4 X1, (r1_tarski X1 (esk12_4 X2 X3 X4 X5) -> False) -> X1 = (esk12_4 X2 X3 X4 X5) -> m1_subset_1 X1 (k4_partfun1 X3 X4) -> r2_hidden X2 (a_3_0_substlat X3 X4 X5) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X3 X4)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False) -> (m1_subset_1 (esk11_4 X1 X2 X3 X4) (k4_partfun1 X2 X3) -> False) -> X1 = X4 -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) (k4_partfun1 X2 X3) -> False) -> X1 = X4 -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> X1 = X4 -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X4 -> False) -> X1 = X4 -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X1 X2 X3 X4, (r1_tarski X3 X4 -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X1 X2)) -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> r2_hidden (esk14_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X1 X4 X2 X3, (m1_subset_1 (esk12_4 X1 X2 X3 X4) (k4_partfun1 X2 X3) -> False) -> r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X1 X4 X2 X3, (v1_finset_1 (esk12_4 X1 X2 X3 X4) -> False) -> r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X5 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> X1 = (esk12_4 X3 X4 X5 X2) -> m1_subset_1 X1 (k4_partfun1 X4 X5) -> r2_hidden X3 (a_3_0_substlat X4 X5 X2) -> m1_subset_1 X2 (k5_finsub_1 (k4_partfun1 X4 X5)) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden X4 (k3_substlat X1 X2 X3) -> False) -> (r2_hidden (esk30_4 X1 X2 X3 X4) X3 -> False) -> v1_finset_1 X4 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden X4 (k3_substlat X1 X2 X3) -> False) -> (r1_tarski (esk30_4 X1 X2 X3 X4) X4 -> False) -> v1_finset_1 X4 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X3 X1 X2 X4, (v1_finset_1 (esk30_4 X1 X2 X3 X4) -> False) -> (r2_hidden X4 (k3_substlat X1 X2 X3) -> False) -> v1_finset_1 X4 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X2 X1 X3 X4, (r1_tarski X3 X4 -> False) -> (r2_hidden (esk14_4 X1 X2 X3 X4) X3 -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X1 X2)) -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden X4 (k3_substlat X1 X2 X3) -> False) -> (esk30_4 X1 X2 X3 X4) = X4 -> v1_finset_1 X4 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X5 X2 X3 X1 X4, (X1 = X4 -> False) -> r1_tarski X1 X4 -> m1_subset_1 X4 (k4_partfun1 X2 X3) -> m1_subset_1 X1 (k4_partfun1 X2 X3) -> r2_hidden X5 (k1_substlat X2 X3) -> r2_hidden X4 (esk8_3 X5 X2 X3) -> r2_hidden X1 (esk8_3 X5 X2 X3) -> False)
  -> (forall X1 X4 X2 X3, ((esk12_4 X1 X2 X3 X4) = X1 -> False) -> r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X2 X3, (m2_subset_1 (k3_substlat X2 X3 X1) (k5_finsub_1 (k4_partfun1 X2 X3)) (k1_substlat X2 X3) -> False) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X5 X4 X2 X1 X3, (X1 = X3 -> False) -> r1_tarski X1 X3 -> r2_hidden X1 X2 -> r2_hidden X3 (k3_substlat X4 X5 X2) -> m1_subset_1 X2 (k5_finsub_1 (k4_partfun1 X4 X5)) -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden X1 (k3_substlat X3 X4 X2) -> m1_subset_1 X2 (k5_finsub_1 (k4_partfun1 X3 X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_finset_1 X1 -> False) -> r2_hidden X2 (k1_substlat X3 X4) -> r2_hidden X1 (esk8_3 X2 X3 X4) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (esk8_3 X1 X2 X3) (k5_finsub_1 (k4_partfun1 X2 X3)) -> False) -> r2_hidden X1 (k1_substlat X2 X3) -> False)
  -> (forall X1 X2 X3, ((k3_substlat X2 X3 X1) = (a_3_0_substlat X2 X3 X1) -> False) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_finsub_1 X1 X2 X3) X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X2 X1, ((k1_finsub_1 X1 X2 X3) = (k1_finsub_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k1_finsub_1 X1 X2 X3) = (k2_xboole_0 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk7_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, ((esk8_3 X1 X2 X3) = X1 -> False) -> r2_hidden X1 (k1_substlat X2 X3) -> False)
  -> (forall X3 X1 X2, ((k1_finsub_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk29_2 X3 X2) -> False)
  -> (forall X1 X3 X2 X4, (v1_finset_1 X4 -> False) -> r2_hidden X4 X1 -> r2_hidden X1 (k1_substlat X2 X3) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X3 X1, (v4_funct_1 X1 -> False) -> m1_subset_1 X1 (k1_substlat X2 X3) -> False)
  -> (forall X2 X3 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k1_substlat X2 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk29_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v5_finset_1 (k2_xboole_0 X1 X2) -> False) -> v5_finset_1 X2 -> v5_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_xboole_0 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk25_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_finsub_1 X1 -> False) -> v1_finsub_1 X1 -> v3_finsub_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk25_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_tarski (k3_substlat esk1_0 esk2_0 (k1_finsub_1 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) esk3_0 esk4_0)) (k1_finsub_1 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) (k3_substlat esk1_0 esk2_0 esk3_0) esk4_0) -> False)
  -> (forall X1 X2, v1_xboole_0 (esk17_2 X1 X2) -> False)
  -> (forall X1 X2, v1_xboole_0 (k1_substlat X1 X2) -> False)
  -> (forall X1 X2, v1_xboole_0 (k4_partfun1 X1 X2) -> False)
  -> (forall X1, v1_xboole_0 (k5_finsub_1 X1) -> False)
  -> (v3_funct_1 esk24_0 -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (forall X1 X2, (m1_subset_1 (k1_substlat X1 X2) (k1_zfmisc_1 (k5_finsub_1 (k4_partfun1 X1 X2))) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk21_2 X1 X2) (k4_partfun1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk17_2 X1 X2) (k1_substlat X1 X2) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) -> False) -> False)
  -> (forall X1 X2, (v4_funct_1 (k4_partfun1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> ((v2_finset_1 esk28_0 -> False) -> False)
  -> ((v5_finset_1 esk27_0 -> False) -> False)
  -> ((v4_funct_1 esk26_0 -> False) -> False)
  -> ((v2_funct_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk28_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk28_0 -> False) -> False)
  -> ((v1_funct_1 esk24_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_finset_1 esk27_0 -> False) -> False)
  -> ((v1_finset_1 esk23_0 -> False) -> False)
  -> ((v1_finset_1 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
