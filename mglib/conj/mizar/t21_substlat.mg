(** $I sig/MizarPreamble.mgs **)

Theorem t21_substlat:
 forall esk9_5:set -> set -> set -> set -> set -> set,
 forall esk8_5:set -> set -> set -> set -> set -> set,
 forall a_4_0_substlat:set -> set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk10_4:set -> set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k4_subset_1:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk32_2:set -> set -> set,
 forall k1_funct_4:set -> set -> set,
 forall esk24_2:set -> set -> set,
 forall v4_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk26_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall v1_finsub_1:set -> prop,
 forall v3_finsub_1:set -> prop,
 forall k1_xboole_0:set,
 forall esk23_0:set,
 forall esk28_0:set,
 forall esk20_0:set,
 forall esk11_0:set,
 forall esk13_2:set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall esk25_2:set -> set -> set,
 forall esk12_0:set,
 forall o_0_0_xboole_0:set,
 forall esk15_0:set,
 forall esk17_0:set,
 forall esk7_1:set -> set,
 forall esk22_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk19_0:set,
 forall esk27_0:set,
 forall esk29_0:set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk5_0:set,
 forall esk2_0:set,
 forall v2_finset_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall esk16_1:set -> set,
 forall v5_finset_1:set -> prop,
 forall esk21_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall v4_finsub_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk6_2:set -> set -> set,
 forall r1_partfun1:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k5_finsub_1:set -> set,
 forall k4_partfun1:set -> set -> set,
 forall k4_substlat:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall esk30_5:set -> set -> set -> set -> set -> set,
 forall esk31_5:set -> set -> set -> set -> set -> set,
     (forall X4 X1 X3 X2 X5, ((k2_xboole_0 (esk30_5 X2 X3 X4 X5 X1) (esk31_5 X2 X3 X4 X5 X1)) = X1 -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (k4_substlat X2 X3 X4 X5) -> False)
  -> (forall X4 X1 X3 X2 X5, ((k2_xboole_0 (esk8_5 X1 X2 X3 X4 X5) (esk9_5 X1 X2 X3 X4 X5)) = X1 -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X4 X1 X3 X2 X5, (r1_partfun1 (esk8_5 X1 X2 X3 X4 X5) (esk9_5 X1 X2 X3 X4 X5) -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X4 X1 X3 X2 X5, (m1_subset_1 (esk9_5 X1 X2 X3 X4 X5) (k4_partfun1 X2 X3) -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X4 X1 X3 X2 X5, (m1_subset_1 (esk8_5 X1 X2 X3 X4 X5) (k4_partfun1 X2 X3) -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X3 X5 X2 X1 X4, (r2_hidden (esk31_5 X1 X2 X3 X4 X5) X4 -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X1 X2)) -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> r2_hidden X5 (k4_substlat X1 X2 X3 X4) -> False)
  -> (forall X3 X5 X2 X1 X4, (r2_hidden (esk30_5 X1 X2 X3 X4 X5) X3 -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X1 X2)) -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> r2_hidden X5 (k4_substlat X1 X2 X3 X4) -> False)
  -> (forall X4 X1 X3 X2 X5, (r2_hidden (esk9_5 X1 X2 X3 X4 X5) X5 -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X4 X1 X3 X2 X5, (r2_hidden (esk8_5 X1 X2 X3 X4 X5) X4 -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X1 X2 X3 X4, (r1_tarski X3 X4 -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X1 X2)) -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> r2_hidden (esk10_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X4 X1 X3 X6 X7 X2 X5, (r2_hidden X5 (a_4_0_substlat X2 X3 X6 X7) -> False) -> X5 = (k2_xboole_0 X1 X4) -> r2_hidden X4 X7 -> r2_hidden X1 X6 -> r1_partfun1 X1 X4 -> m1_subset_1 X4 (k4_partfun1 X2 X3) -> m1_subset_1 X1 (k4_partfun1 X2 X3) -> m1_subset_1 X7 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X6 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k4_substlat X2 X3 X1 X4) (k5_finsub_1 (k4_partfun1 X2 X3)) -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X2 X1 X3 X4, (r1_tarski X3 X4 -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X3 -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X1 X2)) -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X4 X1 X2 X3, ((a_4_0_substlat X2 X3 X1 X4) = (k4_substlat X2 X3 X1 X4) -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X1 X2 X3, ((k4_substlat X2 X3 X1 X4) = (k4_substlat X2 X3 X4 X1) -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (X2 = (k5_finsub_1 X1) -> False) -> v4_finsub_1 X2 -> v1_finset_1 (esk6_2 X1 X2) -> r2_hidden (esk6_2 X1 X2) X2 -> r1_tarski (esk6_2 X1 X2) X1 -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (r2_hidden X1 (k4_partfun1 X2 X3) -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> r2_hidden X1 (k4_partfun1 X2 X3) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk32_2 X3 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X3 X1 X2, (r1_partfun1 X1 X2 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_tarski X2 X3 -> r1_tarski X1 X3 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (X2 = (k5_finsub_1 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r1_tarski (esk6_2 X1 X2) X1 -> False) -> v4_finsub_1 X2 -> False)
  -> (forall X1 X2, (r1_partfun1 X1 X2 -> False) -> (k1_funct_4 X1 X2) = (k2_xboole_0 X1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) X2 -> False) -> r1_tarski X3 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (X2 = (k5_finsub_1 X1) -> False) -> (v1_finset_1 (esk6_2 X1 X2) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> v4_finsub_1 X2 -> False)
  -> (forall X1 X2, ((k1_funct_4 X1 X2) = (k2_xboole_0 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 (k1_funct_4 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X3 X1, (v1_funct_1 X1 -> False) -> r2_hidden X1 (k4_partfun1 X2 X3) -> False)
  -> (forall X1 X2, (r1_partfun1 X2 X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk32_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k5_finsub_1 X2) -> v1_finset_1 X1 -> v4_finsub_1 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk21_2 X1 X2) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 X2 -> False) -> X3 = (k5_finsub_1 X2) -> v4_finsub_1 X3 -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk24_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk21_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk24_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v5_finset_1 (k2_xboole_0 X1 X2) -> False) -> v5_finset_1 X2 -> v5_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_xboole_0 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_zfmisc_1 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_funct_4 X1 X1) = X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_partfun1 X1 X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v1_finset_1 X1 -> False) -> X2 = (k5_finsub_1 X3) -> v4_finsub_1 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk24_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk24_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk24_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk26_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_finsub_1 X1 -> False) -> v1_finsub_1 X1 -> v3_finsub_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk16_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k4_substlat esk1_0 esk2_0 (k4_substlat esk1_0 esk2_0 esk3_0 esk4_0) esk5_0) = (k4_substlat esk1_0 esk2_0 esk3_0 (k4_substlat esk1_0 esk2_0 esk4_0 esk5_0)) -> False)
  -> (forall X1 X2, v1_xboole_0 (k4_partfun1 X1 X2) -> False)
  -> (forall X1, v1_xboole_0 (k5_finsub_1 X1) -> False)
  -> (v3_funct_1 esk23_0 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk14_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k2_xboole_0 X1 X2) X3) = (k2_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk18_2 X1 X2) (k4_partfun1 X1 X2) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk22_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk14_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk13_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk22_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v4_funct_1 (k4_partfun1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> ((v2_finset_1 esk29_0 -> False) -> False)
  -> ((v4_funct_1 esk27_0 -> False) -> False)
  -> ((v5_finset_1 esk28_0 -> False) -> False)
  -> ((v2_funct_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_finset_1 esk28_0 -> False) -> False)
  -> ((v1_finset_1 esk20_0 -> False) -> False)
  -> ((v1_finset_1 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
