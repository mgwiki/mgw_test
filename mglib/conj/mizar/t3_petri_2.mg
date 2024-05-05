(** $I sig/MizarPreamble.mgs **)

Theorem t3_petri_2:
 forall k2_partfun1:set -> set -> set -> set -> set,
 forall esk11_5:set -> set -> set -> set -> set -> set,
 forall a_4_2_petri_2:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk10_5:set -> set -> set -> set -> set -> set,
 forall a_4_0_petri_2:set -> set -> set -> set -> set,
 forall k9_funct_2:set -> set -> set,
 forall k5_relat_1:set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall v1_finset_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk46_2:set -> set -> set,
 forall m1_funct_2:set -> set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall k1_funct_2:set -> set -> set,
 forall esk37_1:set -> set,
 forall esk22_1:set -> set,
 forall esk41_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk44_0:set,
 forall esk42_0:set,
 forall esk28_0:set,
 forall esk21_0:set,
 forall esk13_0:set,
 forall esk18_2:set -> set -> set,
 forall esk15_2:set -> set -> set,
 forall esk35_2:set -> set -> set,
 forall esk25_1:set -> set,
 forall esk9_1:set -> set,
 forall esk29_0:set,
 forall esk23_0:set,
 forall esk20_0:set,
 forall esk14_0:set,
 forall esk24_0:set,
 forall esk45_1:set -> set,
 forall esk31_2:set -> set -> set,
 forall esk39_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall esk16_2:set -> set -> set,
 forall esk2_0:set,
 forall esk27_0:set,
 forall esk17_0:set,
 forall esk26_0:set,
 forall esk33_0:set,
 forall esk43_0:set,
 forall esk36_0:set,
 forall esk32_1:set -> set,
 forall k1_xboole_0:set,
 forall v2_finset_1:set -> prop,
 forall esk7_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall esk40_1:set -> set,
 forall esk19_1:set -> set,
 forall esk34_1:set -> set,
 forall v5_finset_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall esk38_2:set -> set -> set,
 forall v4_funct_1:set -> prop,
 forall esk30_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k1_petri_2:set -> set -> set -> set -> set,
 forall a_4_3_petri_2:set -> set -> set -> set -> set,
 forall esk12_5:set -> set -> set -> set -> set -> set,
 forall esk6_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall esk5_0:set,
 forall esk3_0:set,
 forall v1_funct_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall r1_funct_2:set -> set -> set -> set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X1 X3 X4 X6 X5 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_funct_2 X4 X1 X6 X2 X5 X3 -> False) -> v1_funct_1 X5 -> v1_funct_1 X3 -> v1_funct_2 X5 X6 X2 -> v1_funct_2 X3 X4 X1 -> r1_funct_2 X4 X1 X6 X2 X3 X5 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X6 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 X1)) -> False)
  -> (forall X4 X3 X1 X2 X5 X6, (X5 = X6 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_2 X6 X3 X4 -> v1_funct_2 X5 X1 X2 -> r1_funct_2 X1 X2 X3 X4 X5 X6 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (esk5_0 = esk3_0 -> r1_funct_2 esk3_0 esk1_0 esk5_0 esk1_0 esk4_0 esk6_0 -> False)
  -> (forall X4 X5 X3 X1 X2 X6, (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (r1_funct_2 X3 X4 X5 X6 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X5 X6 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X1 X5 X3 X6 X4 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_funct_2 X4 X1 X6 X2 X3 X3 -> False) -> v1_funct_1 X5 -> v1_funct_1 X3 -> v1_funct_2 X5 X6 X2 -> v1_funct_2 X3 X4 X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X6 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 X1)) -> False)
  -> (forall X5 X1 X3 X4 X2, ((k2_partfun1 X1 X2 (esk11_5 X3 X2 X1 X4 X5) X4) = X5 -> False) -> (v1_zfmisc_1 X2 -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X3 (a_4_2_petri_2 X2 X1 X4 X5) -> False)
  -> (forall X5 X3 X1 X4 X2, ((k2_partfun1 X1 X2 (esk12_5 X3 X2 X1 X4 X5) X4) = X5 -> False) -> (v1_zfmisc_1 X2 -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X3 (a_4_3_petri_2 X2 X1 X4 X5) -> False)
  -> (forall X5 X3 X1 X4 X2, ((k2_partfun1 X1 X2 (esk10_5 X3 X2 X1 X4 X5) X4) = X5 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X3 (a_4_0_petri_2 X2 X1 X4 X5) -> False)
  -> (forall X5 X3 X1 X4 X2, (v1_zfmisc_1 X2 -> False) -> (m1_subset_1 (esk11_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_2_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X3 X1 X4 X2, (v1_zfmisc_1 X2 -> False) -> (v1_funct_2 (esk11_5 X1 X2 X3 X4 X5) X3 X2 -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_2_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X1 X3 X4 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk10_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_0_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X1 X3 X4 X2, (v1_zfmisc_1 X2 -> False) -> (m1_subset_1 (esk12_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_3_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X1 X3 X4 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_2 (esk10_5 X1 X2 X3 X4 X5) X3 X2 -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_0_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X1 X3 X4 X2, (v1_zfmisc_1 X2 -> False) -> (v1_funct_2 (esk12_5 X1 X2 X3 X4 X5) X3 X2 -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_3_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X3 X1 X4 X2, (v1_zfmisc_1 X2 -> False) -> (v1_funct_1 (esk11_5 X1 X2 X3 X4 X5) -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_2_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X1 X3 X4 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk10_5 X1 X2 X3 X4 X5) -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_0_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X1 X3 X4 X2, (v1_zfmisc_1 X2 -> False) -> (v1_funct_1 (esk12_5 X1 X2 X3 X4 X5) -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_3_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X3 X1 X4 X2, ((esk11_5 X1 X2 X3 X4 X5) = X1 -> False) -> (v1_zfmisc_1 X2 -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_2_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X1 X3 X4 X2, ((esk12_5 X1 X2 X3 X4 X5) = X1 -> False) -> (v1_zfmisc_1 X2 -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_3_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X5 X1 X3 X4 X2, ((esk10_5 X1 X2 X3 X4 X5) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> r2_hidden X1 (a_4_0_petri_2 X2 X3 X4 X5) -> False)
  -> (forall X4 X6 X5 X2 X1 X3, (v1_zfmisc_1 X3 -> False) -> (r2_hidden X4 (a_4_2_petri_2 X3 X2 X5 X6) -> False) -> X1 = X4 -> (k2_partfun1 X2 X3 X1 X5) = X6 -> v1_funct_1 X6 -> v1_funct_1 X1 -> v1_funct_2 X6 X5 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X5 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X6 X5 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X4 (a_4_0_petri_2 X3 X2 X5 X6) -> False) -> X1 = X4 -> (k2_partfun1 X2 X3 X1 X5) = X6 -> v1_funct_1 X6 -> v1_funct_1 X1 -> v1_funct_2 X6 X5 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X5 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X6 X5 X2 X1 X3, (v1_zfmisc_1 X3 -> False) -> (r2_hidden X4 (a_4_3_petri_2 X3 X2 X5 X6) -> False) -> X1 = X4 -> (k2_partfun1 X2 X3 X1 X5) = X6 -> v1_funct_1 X6 -> v1_funct_1 X1 -> v1_funct_2 X6 X5 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X5 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X5 X3 X6 X2 X4, (X2 = X4 -> False) -> (v1_zfmisc_1 X1 -> False) -> (a_4_2_petri_2 X1 X3 X2 X5) = (a_4_2_petri_2 X1 X3 X4 X6) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_2 X6 X4 X1 -> v1_funct_2 X5 X2 X1 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X4 X1)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_funct_1 X4 -> v1_funct_2 X4 X3 X1 -> v1_xboole_0 (k1_petri_2 X1 X2 X3 X4) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_petri_2 X1 X2 X3 X4) (k1_zfmisc_1 (k9_funct_2 X2 X1)) -> False) -> v1_funct_1 X4 -> v1_funct_2 X4 X3 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X3 X4 X1, ((a_4_0_petri_2 X1 X4 X3 X2) = (k1_petri_2 X1 X4 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> r1_tarski X3 X4 -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X4 X2 X1 X3, (m1_subset_1 (k2_partfun1 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X2 X1 X3, (v1_funct_1 (k2_partfun1 X1 X2 X3 X4) -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X3 X2 X1, ((k2_partfun1 X2 X3 X1 X4) = (k5_relat_1 X1 X4) -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_finset_1 X1 -> False) -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk46_2 X3 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X3 X2 X1, v1_xboole_0 X1 -> m1_funct_2 X1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v4_funct_1 X1 -> False) -> m1_funct_2 X1 X2 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_funct_2 (k9_funct_2 X2 X1) X2 X1 -> False) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X3 X1, (v5_relat_1 (k5_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v4_relat_1 (k5_relat_1 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v4_relat_1 (k5_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk46_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k5_relat_1 (k5_relat_1 X1 X2) X2) = (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk38_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk30_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k1_funct_2 X2 X1) -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k5_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk38_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk30_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk38_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk30_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k5_relat_1 X1 X2) = X1 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v3_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_finset_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k5_relat_1 X1 X2) -> False) -> v1_finset_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_zfmisc_1 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k5_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k5_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_xboole_0 (k1_funct_2 X1 X2) -> False) -> v1_xboole_0 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk38_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk30_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk38_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk38_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk30_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k2_zfmisc_1 X2 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, ((k9_funct_2 X2 X1) = (k1_funct_2 X2 X1) -> False) -> (v1_xboole_0 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk41_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk40_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_zfmisc_1 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_zfmisc_1 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk37_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk41_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk40_1 X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk37_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk41_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_funct_2 X1 X1) -> False)
  -> (forall X1, v1_subset_1 (esk32_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk36_0 -> False)
  -> (v1_xboole_0 esk44_0 -> False)
  -> (v1_xboole_0 esk43_0 -> False)
  -> (v1_xboole_0 esk42_0 -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_zfmisc_1 esk27_0 -> False)
  -> (v1_zfmisc_1 esk1_0 -> False)
  -> (((k1_petri_2 esk1_0 esk2_0 esk5_0 esk6_0) = (k1_petri_2 esk1_0 esk2_0 esk3_0 esk4_0) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk18_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk15_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_funct_2 (esk8_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk15_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m1_subset_1 esk6_0 (k1_zfmisc_1 (k2_zfmisc_1 esk5_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 esk3_0 esk1_0)) -> False) -> False)
  -> ((v1_funct_2 esk6_0 esk5_0 esk1_0 -> False) -> False)
  -> ((v1_funct_2 esk4_0 esk3_0 esk1_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk39_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk35_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk31_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk18_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk15_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk39_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk35_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk31_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk18_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_funct_1 (k1_funct_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk39_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk35_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk31_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk35_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk39_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk35_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk45_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((r1_tarski esk5_0 esk2_0 -> False) -> False)
  -> ((r1_tarski esk3_0 esk2_0 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk45_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk45_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk25_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk45_1 X1) -> False) -> False)
  -> ((v2_finset_1 esk44_0 -> False) -> False)
  -> ((v4_funct_1 esk42_0 -> False) -> False)
  -> ((v5_finset_1 esk43_0 -> False) -> False)
  -> ((v2_relat_1 esk33_0 -> False) -> False)
  -> ((v2_relat_1 esk29_0 -> False) -> False)
  -> ((v2_relat_1 esk24_0 -> False) -> False)
  -> ((v2_funct_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk44_0 -> False) -> False)
  -> ((v1_relat_1 esk36_0 -> False) -> False)
  -> ((v1_relat_1 esk33_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk28_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_finset_1 esk43_0 -> False) -> False)
  -> ((v1_finset_1 esk28_0 -> False) -> False)
  -> ((v1_finset_1 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk44_0 -> False) -> False)
  -> ((v1_funct_1 esk36_0 -> False) -> False)
  -> ((v1_funct_1 esk33_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk28_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk6_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_zfmisc_1 esk21_0 -> False) -> False)
  -> False.
Admitted.
