(** $I sig/MizarPreamble.mgs **)

Theorem t5_heyting2:
 forall r1_partfun1:set -> set -> prop,
 forall k3_substlat:set -> set -> set -> set,
 forall v1_finset_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk41_4:set -> set -> set -> set -> set,
 forall k1_substlat:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall r1_heyting1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_relat_1:set -> prop,
 forall esk3_0:set,
 forall esk5_1:set -> set,
 forall esk33_1:set -> set,
 forall esk31_1:set -> set,
 forall esk21_1:set -> set,
 forall esk14_1:set -> set,
 forall v2_pre_poly:set -> prop,
 forall v2_funct_1:set -> prop,
 forall v2_finset_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall k1_xboole_0:set,
 forall esk15_2:set -> set -> set,
 forall esk19_1:set -> set,
 forall esk38_0:set,
 forall esk36_0:set,
 forall esk28_0:set,
 forall esk24_0:set,
 forall esk10_0:set,
 forall esk23_2:set -> set -> set,
 forall esk22_1:set -> set,
 forall esk8_1:set -> set,
 forall esk20_0:set,
 forall esk18_0:set,
 forall esk11_0:set,
 forall o_0_0_xboole_0:set,
 forall esk16_0:set,
 forall esk35_0:set,
 forall esk26_0:set,
 forall esk13_1:set -> set,
 forall esk12_0:set,
 forall esk25_0:set,
 forall esk34_0:set,
 forall esk37_0:set,
 forall esk30_0:set,
 forall esk27_1:set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall v3_finsub_1:set -> prop,
 forall v1_finsub_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v1_pre_poly:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall esk17_1:set -> set,
 forall esk29_1:set -> set,
 forall esk32_1:set -> set,
 forall esk4_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall v5_finset_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk6_2:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall esk9_2:set -> set -> set,
 forall v4_finsub_1:set -> prop,
 forall esk7_2:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k5_finsub_1:set -> set,
 forall k4_partfun1:set -> set -> set,
 forall k4_substlat:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall esk39_5:set -> set -> set -> set -> set -> set,
 forall esk40_5:set -> set -> set -> set -> set -> set,
     (forall X4 X1 X3 X2 X5, ((k2_xboole_0 (esk39_5 X2 X3 X4 X5 X1) (esk40_5 X2 X3 X4 X5 X1)) = X1 -> False) -> m1_subset_1 X5 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> r2_hidden X1 (k4_substlat X2 X3 X4 X5) -> False)
  -> (forall X3 X5 X2 X1 X4, (r2_hidden (esk40_5 X1 X2 X3 X4 X5) X4 -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X1 X2)) -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> r2_hidden X5 (k4_substlat X1 X2 X3 X4) -> False)
  -> (forall X3 X5 X2 X1 X4, (r2_hidden (esk39_5 X1 X2 X3 X4 X5) X3 -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X1 X2)) -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> r2_hidden X5 (k4_substlat X1 X2 X3 X4) -> False)
  -> (forall X1 X5 X3 X2 X6 X4, (r2_hidden (k2_xboole_0 X5 X6) (k4_substlat X2 X3 X1 X4) -> False) -> r2_hidden X6 X4 -> r2_hidden X5 X1 -> r1_partfun1 X5 X6 -> m1_subset_1 X6 (k4_partfun1 X2 X3) -> m1_subset_1 X5 (k4_partfun1 X2 X3) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k4_substlat X2 X3 X1 X4) (k5_finsub_1 (k4_partfun1 X2 X3)) -> False) -> m1_subset_1 X4 (k5_finsub_1 (k4_partfun1 X2 X3)) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden X4 (k3_substlat X1 X2 X3) -> False) -> (r1_tarski (esk41_4 X1 X2 X3 X4) X4 -> False) -> v1_finset_1 X4 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden X4 (k3_substlat X1 X2 X3) -> False) -> (r2_hidden (esk41_4 X1 X2 X3 X4) X3 -> False) -> v1_finset_1 X4 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X3 X1 X2 X4, (v1_finset_1 (esk41_4 X1 X2 X3 X4) -> False) -> (r2_hidden X4 (k3_substlat X1 X2 X3) -> False) -> v1_finset_1 X4 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden X4 (k3_substlat X1 X2 X3) -> False) -> (esk41_4 X1 X2 X3 X4) = X4 -> v1_finset_1 X4 -> r2_hidden X4 X3 -> m1_subset_1 X3 (k5_finsub_1 (k4_partfun1 X1 X2)) -> False)
  -> (forall X1 X2 X3, (m2_subset_1 (k3_substlat X2 X3 X1) (k5_finsub_1 (k4_partfun1 X2 X3)) (k1_substlat X2 X3) -> False) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X2 X5 X4 X1 X3, (X1 = X3 -> False) -> r2_hidden X1 X2 -> r1_tarski X1 X3 -> r2_hidden X3 (k3_substlat X4 X5 X2) -> m1_subset_1 X2 (k5_finsub_1 (k4_partfun1 X4 X5)) -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden X1 (k3_substlat X3 X4 X2) -> m1_subset_1 X2 (k5_finsub_1 (k4_partfun1 X3 X4)) -> False)
  -> (forall X1 X3 X2, ((k3_substlat X2 X3 X1) = X1 -> False) -> m2_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) (k1_substlat X2 X3) -> False)
  -> (forall X1 X2 X3, (r1_tarski (k3_substlat X2 X3 X1) X1 -> False) -> m1_subset_1 X1 (k5_finsub_1 (k4_partfun1 X2 X3)) -> False)
  -> (forall X1 X2, (X2 = (k5_finsub_1 X1) -> False) -> v4_finsub_1 X2 -> v1_finset_1 (esk7_2 X1 X2) -> r2_hidden (esk7_2 X1 X2) X2 -> r1_tarski (esk7_2 X1 X2) X1 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_tarski X2 X3 -> False) -> r1_heyting1 X1 X2 X3 -> m1_subset_1 X3 (k5_finsub_1 X1) -> m1_subset_1 X2 (k5_finsub_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r1_heyting1 X3 X1 X2 -> False) -> r1_tarski X1 X2 -> m1_subset_1 X2 (k5_finsub_1 X3) -> m1_subset_1 X1 (k5_finsub_1 X3) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_heyting1 X1 X2 X2 -> False) -> m1_subset_1 X3 (k5_finsub_1 X1) -> m1_subset_1 X2 (k5_finsub_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk9_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (X2 = (k5_finsub_1 X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> (r1_tarski (esk7_2 X1 X2) X1 -> False) -> v4_finsub_1 X2 -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 X1 -> False) -> r2_hidden X1 X2 -> r2_hidden X2 (k1_substlat X3 X4) -> False)
  -> (forall X2 X4 X3 X1, (v1_funct_1 X1 -> False) -> r2_hidden X1 X2 -> r2_hidden X2 (k1_substlat X3 X4) -> False)
  -> (forall X2 X4 X3 X1, (v1_finset_1 X1 -> False) -> r2_hidden X1 X2 -> r2_hidden X2 (k1_substlat X3 X4) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 X3 -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k5_finsub_1 X2)) -> False)
  -> (forall X1 X2, (X2 = (k5_finsub_1 X1) -> False) -> (v1_finset_1 (esk7_2 X1 X2) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> v4_finsub_1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X3 X1, (v4_funct_1 X1 -> False) -> m1_subset_1 X1 (k1_substlat X2 X3) -> False)
  -> (forall X2 X3 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k1_substlat X2 X3) -> False)
  -> (forall X1 X2, (r1_partfun1 X1 X2 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r1_partfun1 X2 X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k5_finsub_1 X2) -> v1_finset_1 X1 -> v4_finsub_1 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 X2 -> False) -> X3 = (k5_finsub_1 X2) -> v4_finsub_1 X3 -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, (X1 = X2 -> False) -> X1 = (k2_xboole_0 X2 X3) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v5_finset_1 (k2_xboole_0 X1 X2) -> False) -> v5_finset_1 X2 -> v5_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_xboole_0 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_partfun1 X1 X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v1_finset_1 X1 -> False) -> X2 = (k5_finsub_1 X3) -> v4_finsub_1 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (r1_tarski (esk5_1 X1) X1 -> False) -> r2_hidden X1 esk3_0 -> False)
  -> (forall X1, (r2_hidden (esk5_1 X1) esk4_0 -> False) -> r2_hidden X1 esk3_0 -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_pre_poly X1 -> False) -> v1_finset_1 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_pre_poly X1 -> False)
  -> (forall X1, (v1_pre_poly X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk33_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk32_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk14_1 X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_finsub_1 X1 -> False) -> v1_finsub_1 X1 -> v3_finsub_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk33_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk31_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk21_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k3_substlat esk1_0 esk2_0 (k4_substlat esk1_0 esk2_0 esk3_0 esk4_0)) = esk3_0 -> False)
  -> (forall X1 X2, v1_xboole_0 (esk15_2 X1 X2) -> False)
  -> (forall X1 X2, v1_xboole_0 (k1_substlat X1 X2) -> False)
  -> (forall X1 X2, v1_xboole_0 (k4_partfun1 X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk27_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k5_finsub_1 X1) -> False)
  -> (v3_funct_1 esk30_0 -> False)
  -> (v1_xboole_0 esk38_0 -> False)
  -> (v1_xboole_0 esk37_0 -> False)
  -> (v1_xboole_0 esk36_0 -> False)
  -> (v1_xboole_0 esk34_0 -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (forall X1 X2, (m1_subset_1 (k1_substlat X1 X2) (k1_zfmisc_1 (k5_finsub_1 (k4_partfun1 X1 X2))) -> False) -> False)
  -> ((m2_subset_1 esk4_0 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) (k1_substlat esk1_0 esk2_0) -> False) -> False)
  -> ((m2_subset_1 esk3_0 (k5_finsub_1 (k4_partfun1 esk1_0 esk2_0)) (k1_substlat esk1_0 esk2_0) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk23_2 X1 X2) (k4_partfun1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk15_2 X1 X2) (k1_substlat X1 X2) -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (k5_finsub_1 X1)) -> False) -> False)
  -> (forall X1 X2, (v4_funct_1 (k4_partfun1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 (esk13_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk13_1 X1) -> False) -> False)
  -> ((v2_finset_1 esk38_0 -> False) -> False)
  -> ((v5_finset_1 esk36_0 -> False) -> False)
  -> ((v2_relat_1 esk28_0 -> False) -> False)
  -> ((v2_relat_1 esk26_0 -> False) -> False)
  -> ((v2_relat_1 esk20_0 -> False) -> False)
  -> ((v1_pre_poly esk35_0 -> False) -> False)
  -> ((v4_funct_1 esk37_0 -> False) -> False)
  -> ((v4_funct_1 esk34_0 -> False) -> False)
  -> ((v2_funct_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk38_0 -> False) -> False)
  -> ((v1_relat_1 esk35_0 -> False) -> False)
  -> ((v1_relat_1 esk30_0 -> False) -> False)
  -> ((v1_relat_1 esk28_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_funct_1 esk38_0 -> False) -> False)
  -> ((v1_funct_1 esk35_0 -> False) -> False)
  -> ((v1_funct_1 esk30_0 -> False) -> False)
  -> ((v1_funct_1 esk28_0 -> False) -> False)
  -> ((v1_funct_1 esk26_0 -> False) -> False)
  -> ((v1_funct_1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk11_0 -> False) -> False)
  -> ((v1_finset_1 esk37_0 -> False) -> False)
  -> ((v1_finset_1 esk36_0 -> False) -> False)
  -> ((v1_finset_1 esk25_0 -> False) -> False)
  -> ((v1_finset_1 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
