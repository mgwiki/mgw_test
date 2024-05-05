(** $I sig/MizarPreamble.mgs **)

Theorem t19_functor0:
 forall m2_pboole:set -> set -> set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk11_4:set -> set -> set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall esk15_3:set -> set -> set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall v2_relat_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk42_1:set -> set,
 forall esk38_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_funcop_1:set -> prop,
 forall esk34_1:set -> set,
 forall esk39_0:set,
 forall esk36_0:set,
 forall esk21_0:set,
 forall esk19_2:set -> set -> set,
 forall esk33_2:set -> set -> set,
 forall esk28_1:set -> set,
 forall esk35_1:set -> set,
 forall esk26_1:set -> set,
 forall esk45_1:set -> set,
 forall esk14_1:set -> set,
 forall esk27_0:set,
 forall esk17_0:set,
 forall o_0_0_xboole_0:set,
 forall esk16_0:set,
 forall esk30_0:set,
 forall esk25_0:set,
 forall esk20_1:set -> set,
 forall esk32_1:set -> set,
 forall esk37_1:set -> set,
 forall esk41_2:set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall esk22_2:set -> set -> set,
 forall esk24_0:set,
 forall esk43_0:set,
 forall esk10_0:set,
 forall esk9_0:set,
 forall esk23_1:set -> set,
 forall esk40_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk44_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall k1_relset_1:set -> set -> set,
 forall esk29_2:set -> set -> set,
 forall esk31_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall k9_xtuple_0:set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall k8_pboole:set -> set -> set,
 forall esk13_5:set -> set -> set -> set -> set -> set,
 forall m1_functor0:set -> set -> set -> set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall k4_relset_1:set -> set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk1_0:set,
 forall k3_relat_1:set -> set -> set,
 forall esk4_0:set,
 forall esk7_0:set,
 forall k1_partfun1:set -> set -> set -> set -> set -> set -> set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk5_0:set,
 forall esk8_0:set,
 forall esk6_0:set,
 forall k1_funct_1:set -> set -> set,
 forall k1_xboole_0:set,
     (forall X1, ((k1_funct_1 esk6_0 X1) = k1_xboole_0 -> False) -> ((k1_funct_1 (k3_relat_1 (k1_partfun1 esk1_0 esk2_0 esk2_0 esk3_0 esk4_0 esk5_0) esk8_0) X1) = k1_xboole_0 -> False) -> (k1_funct_1 (k3_relat_1 esk4_0 esk7_0) X1) = k1_xboole_0 -> r2_hidden X1 esk1_0 -> False)
  -> (forall X3 X2 X1 X4, (m2_pboole X1 X2 X3 X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> v1_funct_1 (k1_funct_1 X1 (esk11_4 X2 X3 X4 X1)) -> v1_funct_2 (k1_funct_1 X1 (esk11_4 X2 X3 X4 X1)) (k1_funct_1 X3 (esk11_4 X2 X3 X4 X1)) (k1_funct_1 X4 (esk11_4 X2 X3 X4 X1)) -> m1_subset_1 (k1_funct_1 X1 (esk11_4 X2 X3 X4 X1)) (k1_zfmisc_1 (k2_zfmisc_1 (k1_funct_1 X3 (esk11_4 X2 X3 X4 X1)) (k1_funct_1 X4 (esk11_4 X2 X3 X4 X1)))) -> False)
  -> (forall X5 X2 X3 X4 X1, (v1_funct_2 (k4_relset_1 X1 X2 X2 X3 X4 X5) X1 X3 -> False) -> X1 = k1_xboole_0 -> v1_funct_2 X5 X2 X3 -> v1_funct_2 X4 X1 X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X5 X3 X2 X4 X1, (v1_funct_2 (k4_relset_1 X2 X3 X3 X1 X4 X5) X2 X1 -> False) -> X1 = k1_xboole_0 -> v1_funct_2 X5 X3 X1 -> v1_funct_2 X4 X2 X3 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X5 X3 X2 X4 X1, (X1 = k1_xboole_0 -> False) -> (v1_funct_2 (k4_relset_1 X2 X1 X1 X3 X4 X5) X2 X3 -> False) -> v1_funct_2 X5 X1 X3 -> v1_funct_2 X4 X2 X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X1)) -> False)
  -> (forall X5 X3 X4 X1 X2 X6, (m1_subset_1 (k1_partfun1 X1 X2 X3 X4 X5 X6) (k1_zfmisc_1 (k2_zfmisc_1 X1 X4)) -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X5 X6 X1 X2 X3, (m1_subset_1 (k4_relset_1 X2 X3 X5 X6 X1 X4) (k1_zfmisc_1 (k2_zfmisc_1 X2 X6)) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X5 X3 X4 X1 X2 X6, (v1_funct_1 (k1_partfun1 X1 X2 X3 X4 X5 X6) -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X5 X6 X4 X2 X3, (v1_xboole_0 X3 -> False) -> (m2_pboole X1 X2 X5 (k3_relat_1 X4 X6) -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X6 -> v1_relat_1 X5 -> v1_relat_1 X1 -> v4_relat_1 X6 X3 -> v4_relat_1 X5 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X6 X3 -> v1_partfun1 X5 X2 -> v1_partfun1 X1 X2 -> v1_funct_2 X4 X2 X3 -> m1_functor0 X1 X2 X3 X4 X5 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X6 X4 X3 X5 X1 X2, (v1_partfun1 X1 X2 -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_relat_1 X6 -> v1_relat_1 X5 -> v4_relat_1 X6 X3 -> v4_relat_1 X5 X2 -> v1_partfun1 X6 X3 -> v1_partfun1 X5 X2 -> v1_funct_2 X4 X2 X3 -> m1_functor0 X1 X2 X3 X4 X5 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X6 X4 X3 X5 X1 X2, (v4_relat_1 X1 X2 -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_relat_1 X6 -> v1_relat_1 X5 -> v4_relat_1 X6 X3 -> v4_relat_1 X5 X2 -> v1_partfun1 X6 X3 -> v1_partfun1 X5 X2 -> v1_funct_2 X4 X2 X3 -> m1_functor0 X1 X2 X3 X4 X5 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X5 X1 X2 X3 X4 X6, (v1_funcop_1 X6 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X5 -> v1_relat_1 X4 -> v4_relat_1 X5 X3 -> v4_relat_1 X4 X2 -> v1_partfun1 X5 X3 -> v1_partfun1 X4 X2 -> v1_funct_2 X1 X2 X3 -> m1_functor0 X6 X2 X3 X1 X4 X5 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X6 X4 X2 X3 X5 X1, (v1_relat_1 X1 -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_relat_1 X6 -> v1_relat_1 X5 -> v4_relat_1 X6 X3 -> v4_relat_1 X5 X2 -> v1_partfun1 X6 X3 -> v1_partfun1 X5 X2 -> v1_funct_2 X4 X2 X3 -> m1_functor0 X1 X2 X3 X4 X5 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X6 X4 X2 X3 X5 X1, (v1_funct_1 X1 -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_relat_1 X6 -> v1_relat_1 X5 -> v4_relat_1 X6 X3 -> v4_relat_1 X5 X2 -> v1_partfun1 X6 X3 -> v1_partfun1 X5 X2 -> v1_funct_2 X4 X2 X3 -> m1_functor0 X1 X2 X3 X4 X5 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X3 X2 X1 X5, (m1_functor0 (esk13_5 X2 X3 X1 X4 X5) X2 X3 X1 X4 X5 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X5 -> v1_relat_1 X4 -> v4_relat_1 X5 X3 -> v4_relat_1 X4 X2 -> v1_partfun1 X5 X3 -> v1_partfun1 X4 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X5 X3 X2 X1 X4 X6, (v1_xboole_0 X6 -> False) -> (m1_functor0 X1 X2 X6 X4 X3 X5 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X5 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X5 X6 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X5 X6 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> v1_funct_2 X4 X2 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X6)) -> m2_pboole X1 X2 X3 (k3_relat_1 X4 X5) -> False)
  -> (forall X1 X5 X6 X2 X3 X4, ((k1_partfun1 X2 X3 X5 X6 X1 X4) = (k3_relat_1 X1 X4) -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X5 X6 X1 X2 X3, ((k4_relset_1 X2 X3 X5 X6 X1 X4) = (k3_relat_1 X1 X4) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X3, (X1 = (k8_pboole X2 X3) -> False) -> (k9_xtuple_0 X1) = (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> (k3_relat_1 (k1_funct_1 X2 (esk12_3 X2 X3 X1)) (k1_funct_1 X3 (esk12_3 X2 X3 X1))) = (k1_funct_1 X1 (esk12_3 X2 X3 X1)) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X3 -> v1_funcop_1 X2 -> False)
  -> (forall X3 X1 X2 X4, (m2_pboole X4 X1 X2 X3 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v4_relat_1 X4 X1 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X4 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X5 X4 X3 X1 X2, (m1_subset_1 (k1_funct_1 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 (k1_funct_1 X3 X2) (k1_funct_1 X4 X2))) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X4 X5 -> v4_relat_1 X3 X5 -> v4_relat_1 X1 X5 -> v1_partfun1 X4 X5 -> v1_partfun1 X3 X5 -> v1_partfun1 X1 X5 -> r2_hidden X2 X5 -> m2_pboole X1 X5 X3 X4 -> False)
  -> (forall X5 X4 X3 X1 X2, (v1_funct_2 (k1_funct_1 X1 X2) (k1_funct_1 X3 X2) (k1_funct_1 X4 X2) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X4 X5 -> v4_relat_1 X3 X5 -> v4_relat_1 X1 X5 -> v1_partfun1 X4 X5 -> v1_partfun1 X3 X5 -> v1_partfun1 X1 X5 -> r2_hidden X2 X5 -> m2_pboole X1 X5 X3 X4 -> False)
  -> (forall X5 X3 X4 X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X5 -> v1_relat_1 X4 -> v1_relat_1 X1 -> v4_relat_1 X5 X3 -> v4_relat_1 X4 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X5 X3 -> v1_partfun1 X4 X3 -> v1_partfun1 X1 X3 -> r2_hidden X2 X3 -> m2_pboole X1 X3 X4 X5 -> False)
  -> (forall X4 X3 X1 X2, (v1_partfun1 X1 X2 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X4 X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X3 X2 X1 X4, (v1_funcop_1 X4 -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> m2_pboole X4 X2 X1 X3 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v1_funct_1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X4 X3 X1 X2 X5, (v1_xboole_0 X5 -> False) -> (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X5 X4 -> v1_funct_2 X1 X3 X5 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X5 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> False)
  -> (forall X1 X4 X3 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X4 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X1 X2 X3, (m2_pboole (esk15_3 X2 X1 X3) X2 X1 X3 -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2 X4 X5 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X5 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X3 X1 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_partfun1 (k3_relat_1 X1 X2) X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X4 -> v1_partfun1 X2 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X3 X1 X2 X4, (v1_xboole_0 X4 -> False) -> (v4_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X4 -> v1_partfun1 X2 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X3 -> v1_partfun1 X2 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X3 -> v1_partfun1 X2 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X1 X3, (X3 = (k8_pboole X1 X2) -> False) -> (r2_hidden (esk12_3 X1 X2 X3) (k9_xtuple_0 X3) -> False) -> (k9_xtuple_0 X3) = (k3_xboole_0 (k9_xtuple_0 X1) (k9_xtuple_0 X2)) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X3 X4 X2, ((k1_funct_1 X2 X1) = (k3_relat_1 (k1_funct_1 X3 X1) (k1_funct_1 X4 X1)) -> False) -> X2 = (k8_pboole X3 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funcop_1 X4 -> v1_funcop_1 X3 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_partfun1 (k8_pboole X1 X2) X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k8_pboole X1 X2) X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> v1_relat_1 X2 -> v2_relat_1 X2 -> m1_subset_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> v1_xboole_0 (k1_funct_1 X2 X3) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X3, ((k9_xtuple_0 X1) = (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> False) -> X1 = (k8_pboole X2 X3) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X3 -> v1_funcop_1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk29_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v2_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_funcop_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_partfun1 X2 X1 -> False) -> (k1_relset_1 X1 X2) = X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X1 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v1_funcop_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk31_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (v2_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk31_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk31_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_funcop_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk44_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 (esk44_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk44_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v5_relat_1 (esk29_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_partfun1 (esk29_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v4_relat_1 (esk29_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk31_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk31_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk44_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk44_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (esk29_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk29_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk42_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk40_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk38_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk38_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk42_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk40_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk40_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (m1_functor0 (k8_pboole esk9_0 esk10_0) esk1_0 esk3_0 (k1_partfun1 esk1_0 esk2_0 esk2_0 esk3_0 esk4_0 esk5_0) esk6_0 esk8_0 -> False)
  -> (forall X1, v1_subset_1 (esk34_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk39_0 -> False)
  -> (v1_xboole_0 esk43_0 -> False)
  -> (v1_xboole_0 esk36_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk3_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> ((m1_functor0 esk10_0 esk1_0 esk3_0 (k1_partfun1 esk1_0 esk2_0 esk2_0 esk3_0 esk4_0 esk5_0) (k3_relat_1 esk4_0 esk7_0) esk8_0 -> False) -> False)
  -> ((m1_functor0 esk9_0 esk1_0 esk2_0 esk4_0 esk6_0 esk7_0 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk22_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk18_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk18_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (k2_zfmisc_1 esk2_0 esk3_0)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk2_0)) -> False) -> False)
  -> ((v1_funct_2 esk5_0 esk2_0 esk3_0 -> False) -> False)
  -> ((v1_funct_2 esk4_0 esk1_0 esk2_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk41_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk33_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk22_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk18_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk41_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk33_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk22_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk18_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk41_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk33_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk41_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk37_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk35_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk45_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk37_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk35_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((v1_partfun1 esk8_0 esk3_0 -> False) -> False)
  -> ((v1_partfun1 esk7_0 esk2_0 -> False) -> False)
  -> ((v1_partfun1 esk6_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk8_0 esk3_0 -> False) -> False)
  -> ((v4_relat_1 esk7_0 esk2_0 -> False) -> False)
  -> ((v4_relat_1 esk6_0 esk1_0 -> False) -> False)
  -> (forall X1, (v3_relat_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk45_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v1_funcop_1 (esk37_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk45_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk37_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk20_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk45_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk37_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk20_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk28_1 X1) -> False) -> False)
  -> ((v3_funct_1 esk24_0 -> False) -> False)
  -> ((v2_funct_1 esk25_0 -> False) -> False)
  -> ((v2_relat_1 esk36_0 -> False) -> False)
  -> ((v2_relat_1 esk30_0 -> False) -> False)
  -> ((v2_relat_1 esk27_0 -> False) -> False)
  -> ((v1_funcop_1 esk16_0 -> False) -> False)
  -> ((v4_funct_1 esk43_0 -> False) -> False)
  -> ((v1_relat_1 esk39_0 -> False) -> False)
  -> ((v1_relat_1 esk36_0 -> False) -> False)
  -> ((v1_relat_1 esk30_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk8_0 -> False) -> False)
  -> ((v1_relat_1 esk7_0 -> False) -> False)
  -> ((v1_relat_1 esk6_0 -> False) -> False)
  -> ((v1_funct_1 esk39_0 -> False) -> False)
  -> ((v1_funct_1 esk36_0 -> False) -> False)
  -> ((v1_funct_1 esk30_0 -> False) -> False)
  -> ((v1_funct_1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk24_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk8_0 -> False) -> False)
  -> ((v1_funct_1 esk7_0 -> False) -> False)
  -> ((v1_funct_1 esk6_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
