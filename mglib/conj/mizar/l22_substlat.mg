(** $I sig/MizarPreamble.mgs **)

Theorem l22_substlat:
 forall esk16_5:set -> set -> set -> set -> set -> set,
 forall esk15_5:set -> set -> set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall a_4_0_substlat:set -> set -> set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k4_subset_1:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk28_2:set -> set -> set,
 forall v4_funct_1:set -> prop,
 forall esk23_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_finset_1:set -> prop,
 forall esk21_2:set -> set -> set,
 forall esk30_0:set,
 forall esk35_0:set,
 forall esk27_0:set,
 forall esk17_0:set,
 forall esk19_2:set -> set -> set,
 forall esk29_2:set -> set -> set,
 forall esk7_1:set -> set,
 forall esk24_0:set,
 forall o_0_0_xboole_0:set,
 forall esk22_0:set,
 forall esk18_0:set,
 forall esk32_2:set -> set -> set,
 forall esk25_2:set -> set -> set,
 forall esk20_2:set -> set -> set,
 forall esk26_0:set,
 forall esk34_0:set,
 forall esk36_0:set,
 forall k1_xboole_0:set,
 forall v3_finsub_1:set -> prop,
 forall v1_finsub_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk33_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v5_finset_1:set -> prop,
 forall esk31_2:set -> set -> set,
 forall k1_funct_4:set -> set -> set,
 forall esk38_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall v4_finsub_1:set -> prop,
 forall esk6_2:set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall r1_relset_1:set -> set -> set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk37_4:set -> set -> set -> set -> set,
 forall esk5_0:set,
 forall esk1_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall k3_substlat:set -> set -> set -> set,
 forall esk2_0:set,
 forall k4_substlat:set -> set -> set -> set -> set,
 forall esk13_4:set -> set -> set -> set -> set,
 forall esk11_4:set -> set -> set -> set -> set,
 forall esk12_4:set -> set -> set -> set -> set,
 forall esk10_4:set -> set -> set -> set -> set,
 forall k1_substlat:set -> set -> set,
 forall r1_partfun1:set -> set -> prop,
 forall v1_finset_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k5_finsub_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k4_partfun1:set -> set -> set,
 forall esk14_5:set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_3_0_substlat:set -> set -> set -> set,
     (forall X5 X4 X3 X2 X1, (r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> False) -> X1 = X5 -> (esk14_5 X1 X2 X3 X4 X5) = X5 -> v1_finset_1 X5 -> m1_subset_1 X5 (k4_partfun1 X2 X3) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden (esk14_5 X1 X2 X3 X4 X5) X4 -> r1_tarski (esk14_5 X1 X2 X3 X4 X5) X5 -> False)
  -> (forall X4 X1 X3 X2 X5, ((k2_xboole_0 (esk15_5 X1 X2 X3 X4 X5) (esk16_5 X1 X2 X3 X4 X5)) = X1 -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X4 X1 X3 X2 X5, (r1_partfun1 (esk15_5 X1 X2 X3 X4 X5) (esk16_5 X1 X2 X3 X4 X5) -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X5 X4 X3 X2 X1, ((esk14_5 X1 X2 X3 X4 X5) = X5 -> False) -> (r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> False) -> (r1_tarski (esk14_5 X1 X2 X3 X4 X5) X5 -> False) -> X1 = X5 -> v1_finset_1 X5 -> m1_subset_1 X5 (k4_partfun1 X2 X3) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X5 X4 X3 X2 X1, ((esk14_5 X1 X2 X3 X4 X5) = X5 -> False) -> (r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> False) -> (r2_hidden (esk14_5 X1 X2 X3 X4 X5) X4 -> False) -> X1 = X5 -> v1_finset_1 X5 -> m1_subset_1 X5 (k4_partfun1 X2 X3) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X1 X3 X2 X5, (m1_subset_1 (esk16_5 X1 X2 X3 X4 X5) (k4_partfun1 X2 X3) -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X4 X1 X3 X2 X5, (m1_subset_1 (esk15_5 X1 X2 X3 X4 X5) (k4_partfun1 X2 X3) -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X4 X1 X3 X2 X5, (r2_hidden (esk16_5 X1 X2 X3 X4 X5) X5 -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X4 X1 X3 X2 X5, (r2_hidden (esk15_5 X1 X2 X3 X4 X5) X4 -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (a_4_0_substlat X2 X3 X4 X5) -> False)
  -> (forall X5 X4 X3 X2 X1, (r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> False) -> (m1_subset_1 (esk14_5 X1 X2 X3 X4 X5) (k4_partfun1 X2 X3) -> False) -> X1 = X5 -> v1_finset_1 X5 -> m1_subset_1 X5 (k4_partfun1 X2 X3) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r1_tarski (esk11_4 X1 X2 X3 X4) (esk12_4 X1 X2 X3 X4) -> False) -> X1 = X4 -> v1_finset_1 (esk10_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> X1 = X4 -> (esk12_4 X1 X2 X3 X4) = (esk11_4 X1 X2 X3 X4) -> v1_finset_1 (esk10_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X4 -> False) -> (r1_tarski (esk11_4 X1 X2 X3 X4) (esk12_4 X1 X2 X3 X4) -> False) -> X1 = X4 -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (m1_subset_1 (esk12_4 X1 X2 X3 X4) (k4_partfun1 X2 X3) -> False) -> X1 = X4 -> v1_finset_1 (esk10_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (m1_subset_1 (esk11_4 X1 X2 X3 X4) (k4_partfun1 X2 X3) -> False) -> X1 = X4 -> v1_finset_1 (esk10_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk12_4 X1 X2 X3 X4) X4 -> False) -> X1 = X4 -> v1_finset_1 (esk10_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> X1 = X4 -> v1_finset_1 (esk10_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X4 -> False) -> X1 = X4 -> (esk12_4 X1 X2 X3 X4) = (esk11_4 X1 X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X5 X4 X3 X1 X2, (X1 = (esk13_4 X3 X4 X5 X2) -> False) -> r2_hidden X1 X2 -> m1_subset_1 X1 (k4_partfun1 X4 X5) -> r2_hidden X3 (a_3_0_substlat X4 X5 X2) -> m1_subset_1 X2 (k5_finsub_1 (k4_partfun1 X4 X5)) -> r1_tarski X1 (esk13_4 X3 X4 X5 X2) -> False)
  -> (forall X5 X2 X3 X4 X1, (r1_tarski X1 (esk13_4 X2 X3 X4 X5) -> False) -> X1 = (esk13_4 X2 X3 X4 X5) -> m1_subset_1 X1 (k4_partfun1 X3 X4) -> r2_hidden X2 (a_3_0_substlat X3 X4 X5) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X3 X4)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X4 -> False) -> (m1_subset_1 (esk12_4 X1 X2 X3 X4) (k4_partfun1 X2 X3) -> False) -> X1 = X4 -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X4 -> False) -> (m1_subset_1 (esk11_4 X1 X2 X3 X4) (k4_partfun1 X2 X3) -> False) -> X1 = X4 -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk12_4 X1 X2 X3 X4) X4 -> False) -> X1 = X4 -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k1_substlat X2 X3) -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> X1 = X4 -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X1, v1_finset_1 X1 -> r1_tarski X1 esk5_0 -> r2_hidden X1 (k4_substlat esk1_0 esk2_0 (k3_substlat esk1_0 esk2_0 esk3_0) esk4_0) -> False)
  -> (forall X4 X1 X3 X6 X7 X2 X5, (r2_hidden X5 (a_4_0_substlat X2 X3 X6 X7) -> False) -> X5 = (k2_xboole_0 X1 X4) -> r2_hidden X4 X7 -> r2_hidden X1 X6 -> r1_partfun1 X1 X4 -> m1_subset_1 X4 (k4_partfun1 X2 X3) -> m1_subset_1 X1 (k4_partfun1 X2 X3) -> m1_subset_1 X7 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X6 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X1 X4 X2 X3, (m1_subset_1 (esk13_4 X1 X2 X3 X4) (k4_partfun1 X2 X3) -> False) -> r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X1 X4 X2 X3, (v1_finset_1 (esk13_4 X1 X2 X3 X4) -> False) -> r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k4_substlat X2 X3 X1 X4) (k5_finsub_1 (k4_partfun1 X2 X3)) -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X5 X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> X1 = (esk13_4 X3 X4 X5 X2) -> m1_subset_1 X1 (k4_partfun1 X4 X5) -> r2_hidden X3 (a_3_0_substlat X4 X5 X2) -> m1_subset_1 X2 (k5_finsub_1 (k4_partfun1 X4 X5)) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden (esk37_4 X1 X2 X3 X4) (k3_substlat X1 X2 X3) -> False) -> v1_finset_1 X4 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X4 X1 X2 X3, ((a_4_0_substlat X2 X3 X1 X4) = (k4_substlat X2 X3 X1 X4) -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X1 X2 X3 X4 X5, (r1_partfun1 X4 X5 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X5 -> r1_partfun1 X1 X5 -> r1_relset_1 X2 X3 X4 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2 X4, (r1_tarski (esk37_4 X1 X2 X3 X4) X4 -> False) -> v1_finset_1 X4 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X5 X2 X3 X1 X4, (X1 = X4 -> False) -> r1_tarski X1 X4 -> m1_subset_1 X4 (k4_partfun1 X2 X3) -> m1_subset_1 X1 (k4_partfun1 X2 X3) -> r2_hidden X5 (k1_substlat X2 X3) -> r2_hidden X4 (esk9_3 X5 X2 X3) -> r2_hidden X1 (esk9_3 X5 X2 X3) -> False)
  -> (forall X1 X4 X2 X3, ((esk13_4 X1 X2 X3 X4) = X1 -> False) -> r2_hidden X1 (a_3_0_substlat X2 X3 X4) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X2 X1 X3 X4, (r1_tarski X3 X4 -> False) -> r1_relset_1 X1 X2 X3 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X3 X1 X2, (r1_relset_1 X3 X4 X1 X2 -> False) -> r1_tarski X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X1 X2 X3, (r1_relset_1 X2 X3 X1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (m2_subset_1 (k3_substlat X2 X3 X1) (k5_finsub_1 (k4_partfun1 X2 X3)) (k1_substlat X2 X3) -> False) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X2 X4 X3 X1, (v1_finset_1 X1 -> False) -> r2_hidden X2 (k1_substlat X3 X4) -> r2_hidden X1 (esk9_3 X2 X3 X4) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (esk9_3 X1 X2 X3) (k5_finsub_1 (k4_partfun1 X2 X3)) -> False) -> r2_hidden X1 (k1_substlat X2 X3) -> False)
  -> (forall X1 X2 X3, ((k3_substlat X2 X3 X1) = (a_3_0_substlat X2 X3 X1) -> False) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (X2 = (k5_finsub_1 X1) -> False) -> v4_finsub_1 X2 -> v1_finset_1 (esk6_2 X1 X2) -> r2_hidden (esk6_2 X1 X2) X2 -> r1_tarski (esk6_2 X1 X2) X1 -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (r2_hidden X1 (k4_partfun1 X2 X3) -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> r2_hidden X1 (k4_partfun1 X2 X3) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk8_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, ((esk9_3 X1 X2 X3) = X1 -> False) -> r2_hidden X1 (k1_substlat X2 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk38_2 X3 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (X2 = (k5_finsub_1 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r1_tarski (esk6_2 X1 X2) X1 -> False) -> v4_finsub_1 X2 -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) (k2_xboole_0 X2 X3) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r1_partfun1 X1 X2 -> False) -> (k1_funct_4 X1 X2) = (k2_xboole_0 X1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k5_finsub_1 X1) -> False) -> (v1_finset_1 (esk6_2 X1 X2) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> v4_finsub_1 X2 -> False)
  -> (forall X1 X2, ((k1_funct_4 X1 X2) = (k2_xboole_0 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 (k1_funct_4 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X3 X1, (v4_funct_1 X1 -> False) -> m1_subset_1 X1 (k1_substlat X2 X3) -> False)
  -> (forall X2 X3 X1, (v1_funct_1 X1 -> False) -> r2_hidden X1 (k4_partfun1 X2 X3) -> False)
  -> (forall X2 X3 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k1_substlat X2 X3) -> False)
  -> (forall X1 X2, (r1_partfun1 X2 X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk38_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k5_finsub_1 X2) -> v1_finset_1 X1 -> v4_finsub_1 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk31_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk28_2 X1 X2) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 X2 -> False) -> X3 = (k5_finsub_1 X2) -> v4_finsub_1 X3 -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk31_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk28_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk31_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk28_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v5_finset_1 (k2_xboole_0 X1 X2) -> False) -> v5_finset_1 X2 -> v5_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_xboole_0 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_zfmisc_1 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_funct_4 X1 X1) = X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_partfun1 X1 X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v1_finset_1 X1 -> False) -> X2 = (k5_finsub_1 X3) -> v4_finsub_1 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk31_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk31_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk31_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> v1_finset_1 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk33_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_finsub_1 X1 -> False) -> v1_finsub_1 X1 -> v3_finsub_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk33_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (esk21_2 X1 X2) -> False)
  -> (forall X1 X2, v1_xboole_0 (k1_substlat X1 X2) -> False)
  -> (forall X1 X2, v1_xboole_0 (k4_partfun1 X1 X2) -> False)
  -> (forall X1, v1_xboole_0 (k5_finsub_1 X1) -> False)
  -> (v3_funct_1 esk30_0 -> False)
  -> (v1_xboole_0 esk36_0 -> False)
  -> (v1_xboole_0 esk35_0 -> False)
  -> (v1_xboole_0 esk34_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> ((r2_hidden esk5_0 (k4_substlat esk1_0 esk2_0 esk3_0 esk4_0) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k1_substlat X1 X2) (k1_zfmisc_1 (k5_finsub_1 (k4_partfun1 X1 X2))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk25_2 X1 X2) (k4_partfun1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk21_2 X1 X2) (k1_substlat X1 X2) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk32_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk29_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk20_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk32_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk29_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk20_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v4_funct_1 (k4_partfun1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk32_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk29_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk32_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk29_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk29_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> ((v2_finset_1 esk36_0 -> False) -> False)
  -> ((v5_finset_1 esk35_0 -> False) -> False)
  -> ((v4_funct_1 esk34_0 -> False) -> False)
  -> ((v2_funct_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk36_0 -> False) -> False)
  -> ((v1_relat_1 esk30_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk36_0 -> False) -> False)
  -> ((v1_funct_1 esk30_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk24_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_finset_1 esk35_0 -> False) -> False)
  -> ((v1_finset_1 esk27_0 -> False) -> False)
  -> ((v1_finset_1 esk17_0 -> False) -> False)
  -> ((v1_finset_1 esk5_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
