(** $I sig/MizarPreamble.mgs **)

Theorem l4_functor3:
 forall k4_relset_1:set -> set -> set -> set -> set -> set -> set,
 forall k6_partfun1:set -> set,
 forall r2_relset_1:set -> set -> set -> set -> prop,
 forall k8_pboole:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k9_xtuple_0:set -> set,
 forall esk41_3:set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall r6_pboole:set -> set -> set -> prop,
 forall v2_relat_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk39_2:set -> set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk37_1:set -> set,
 forall esk33_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_funcop_1:set -> prop,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk5_0:set,
 forall esk6_0:set,
 forall esk38_0:set,
 forall esk24_0:set,
 forall esk15_0:set,
 forall esk4_0:set,
 forall esk13_2:set -> set -> set,
 forall esk28_2:set -> set -> set,
 forall esk30_1:set -> set,
 forall esk21_1:set -> set,
 forall esk40_1:set -> set,
 forall esk9_1:set -> set,
 forall esk20_0:set,
 forall esk26_0:set,
 forall esk11_0:set,
 forall esk18_0:set,
 forall esk12_0:set,
 forall esk22_0:set,
 forall esk14_1:set -> set,
 forall esk27_1:set -> set,
 forall esk32_1:set -> set,
 forall esk23_1:set -> set,
 forall esk36_2:set -> set -> set,
 forall esk16_2:set -> set -> set,
 forall esk19_0:set,
 forall esk31_0:set,
 forall esk34_0:set,
 forall esk29_1:set -> set,
 forall esk17_1:set -> set,
 forall esk35_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk25_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall k1_xboole_0:set,
 forall v1_xboole_0:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall esk8_3:set -> set -> set -> set,
 forall k2_msualg_3:set -> set -> set,
 forall k3_relat_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk7_4:set -> set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall m2_pboole:set -> set -> set -> set -> prop,
     (forall X3 X2 X1 X4, (m2_pboole X1 X2 X3 X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> v1_funct_1 (k1_funct_1 X1 (esk7_4 X2 X3 X4 X1)) -> v1_funct_2 (k1_funct_1 X1 (esk7_4 X2 X3 X4 X1)) (k1_funct_1 X3 (esk7_4 X2 X3 X4 X1)) (k1_funct_1 X4 (esk7_4 X2 X3 X4 X1)) -> m1_subset_1 (k1_funct_1 X1 (esk7_4 X2 X3 X4 X1)) (k1_zfmisc_1 (k2_zfmisc_1 (k1_funct_1 X3 (esk7_4 X2 X3 X4 X1)) (k1_funct_1 X4 (esk7_4 X2 X3 X4 X1)))) -> False)
  -> (forall X3 X1 X2, (r2_relset_1 X1 X2 (k4_relset_1 X1 X1 X1 X2 (k6_partfun1 X1) X3) X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X1 X2, (r2_relset_1 X1 X2 (k4_relset_1 X1 X2 X2 X2 X3 (k6_partfun1 X2)) X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X5 X6 X1 X2 X3, (m1_subset_1 (k4_relset_1 X2 X3 X5 X6 X1 X4) (k1_zfmisc_1 (k2_zfmisc_1 X2 X6)) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X5 X6 X1 X2 X3, ((k4_relset_1 X2 X3 X5 X6 X1 X4) = (k3_relat_1 X1 X4) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X7 X5 X2 X6 X1 X3 X4, ((k3_relat_1 (k1_funct_1 X3 X1) (k1_funct_1 X4 X1)) = (k1_funct_1 (k8_pboole X3 X4) X1) -> False) -> v1_funct_1 X7 -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_relat_1 X7 -> v1_relat_1 X6 -> v1_relat_1 X5 -> v4_relat_1 X7 X2 -> v4_relat_1 X6 X2 -> v4_relat_1 X5 X2 -> v1_partfun1 X7 X2 -> v1_partfun1 X6 X2 -> v1_partfun1 X5 X2 -> r2_hidden X1 X2 -> m2_pboole X4 X2 X5 X6 -> m2_pboole X3 X2 X7 X5 -> False)
  -> (forall X1 X2 X3, (X1 = (k2_msualg_3 X2 X3) -> False) -> (k1_funct_1 X1 (esk8_3 X2 X3 X1)) = (k6_partfun1 (k1_funct_1 X3 (esk8_3 X2 X3 X1))) -> v1_funct_1 X3 -> v1_relat_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X3 -> False)
  -> (forall X6 X4 X5 X1 X2 X3, ((k9_xtuple_0 (k8_pboole X1 X2)) = X3 -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_relat_1 X6 -> v1_relat_1 X5 -> v1_relat_1 X4 -> v4_relat_1 X6 X3 -> v4_relat_1 X5 X3 -> v4_relat_1 X4 X3 -> v1_partfun1 X6 X3 -> v1_partfun1 X5 X3 -> v1_partfun1 X4 X3 -> m2_pboole X2 X3 X4 X5 -> m2_pboole X1 X3 X6 X4 -> False)
  -> (forall X3 X1 X2 X4, (m2_pboole X4 X1 X2 X3 -> False) -> (r2_hidden (esk7_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v4_relat_1 X4 X1 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X4 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X5 X4 X3 X1 X2, (m1_subset_1 (k1_funct_1 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 (k1_funct_1 X3 X2) (k1_funct_1 X4 X2))) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X4 X5 -> v4_relat_1 X3 X5 -> v4_relat_1 X1 X5 -> v1_partfun1 X4 X5 -> v1_partfun1 X3 X5 -> v1_partfun1 X1 X5 -> r2_hidden X2 X5 -> m2_pboole X1 X5 X3 X4 -> False)
  -> (forall X4 X1 X2 X3, (r2_relset_1 X2 X3 X4 X1 -> False) -> r2_relset_1 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X5 X4 X3 X1 X2, (v1_funct_2 (k1_funct_1 X1 X2) (k1_funct_1 X3 X2) (k1_funct_1 X4 X2) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X4 X5 -> v4_relat_1 X3 X5 -> v4_relat_1 X1 X5 -> v1_partfun1 X4 X5 -> v1_partfun1 X3 X5 -> v1_partfun1 X1 X5 -> r2_hidden X2 X5 -> m2_pboole X1 X5 X3 X4 -> False)
  -> (forall X5 X3 X4 X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X5 -> v1_relat_1 X4 -> v1_relat_1 X1 -> v4_relat_1 X5 X3 -> v4_relat_1 X4 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X5 X3 -> v1_partfun1 X4 X3 -> v1_partfun1 X1 X3 -> r2_hidden X2 X3 -> m2_pboole X1 X3 X4 X5 -> False)
  -> (forall X2 X1 X3 X4, (X3 = X4 -> False) -> r2_relset_1 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X1 X2, (X3 = (k2_msualg_3 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X2 -> v1_relat_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m2_pboole X3 X1 X2 X2 -> False)
  -> (forall X2 X1 X3 X4, ((k1_funct_1 X1 X4) = (k6_partfun1 (k1_funct_1 X3 X4)) -> False) -> X1 = (k2_msualg_3 X2 X3) -> v1_funct_1 X3 -> v1_relat_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> r2_hidden X4 X2 -> m2_pboole X1 X2 X3 X3 -> False)
  -> (forall X4 X3 X1 X2, (v1_partfun1 X1 X2 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X4 X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X3 X2 X1 X4, (v1_funcop_1 X4 -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> m2_pboole X4 X2 X1 X3 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v1_funct_1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> (k1_funct_1 X1 (esk41_3 X2 X1 X3)) = (k1_funct_1 X3 (esk41_3 X2 X1 X3)) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X4 X3 X1 X2 X5, (v1_xboole_0 X5 -> False) -> (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X5 X4 -> v1_funct_2 X1 X3 X5 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X5 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> False)
  -> (forall X1 X4 X3 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X4 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X3 X1 X2, (r2_relset_1 X3 X4 X1 X2 -> False) -> X1 = X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_relset_1 X2 X3 X1 X1 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (m2_pboole (esk10_3 X2 X1 X3) X2 X1 X3 -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2 X4 X5 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X5 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X2 X1, (m2_pboole (k2_msualg_3 X2 X1) X2 X1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X5 X4 X2 X3, (X3 = k1_xboole_0 -> False) -> ((k1_funct_1 (k3_relat_1 X1 X4) X5) = (k1_funct_1 X4 (k1_funct_1 X1 X5)) -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X4 -> r2_hidden X5 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_partfun1 (k3_relat_1 X1 X2) X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X4 -> v1_partfun1 X2 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X3 X1 X2 X4, (v1_xboole_0 X4 -> False) -> (v4_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X4 -> v1_partfun1 X2 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X3 -> v1_partfun1 X2 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X3 -> v1_partfun1 X2 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X1 X4 X2 X3, (X3 = k1_xboole_0 -> False) -> (r2_hidden (k1_funct_1 X1 X4) X3 -> False) -> v1_funct_1 X1 -> r2_hidden X4 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (r6_pboole X2 X3 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r6_pboole X2 X1 X3 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (r2_hidden (esk41_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> r6_pboole X1 X2 X3 -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (r6_pboole X3 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (r6_pboole X2 X1 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v1_partfun1 (k8_pboole X1 X2) X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k8_pboole X1 X2) X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k8_pboole X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> v1_relat_1 X2 -> v2_relat_1 X2 -> m1_subset_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> v1_xboole_0 (k1_funct_1 X2 X3) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk25_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
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
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (v2_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_funcop_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk39_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 (esk39_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk39_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_partfun1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
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
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk39_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk39_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk33_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk37_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk35_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k6_partfun1 X1) -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r6_pboole esk1_0 (k8_pboole esk6_0 (k3_relat_1 esk3_0 (k2_msualg_3 esk2_0 esk5_0))) esk6_0 -> False)
  -> (forall X1, v1_subset_1 (esk29_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk34_0 -> False)
  -> (v1_xboole_0 esk38_0 -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> ((m2_pboole esk6_0 esk1_0 esk4_0 (k3_relat_1 esk3_0 esk5_0) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk13_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k6_partfun1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk2_0)) -> False) -> False)
  -> ((v1_funct_2 esk3_0 esk1_0 esk2_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk36_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk28_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk13_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk36_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk28_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk36_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk36_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk40_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v1_partfun1 esk5_0 esk2_0 -> False) -> False)
  -> ((v1_partfun1 esk4_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk5_0 esk2_0 -> False) -> False)
  -> ((v4_relat_1 esk4_0 esk1_0 -> False) -> False)
  -> (forall X1, ((k9_xtuple_0 (k6_partfun1 X1)) = X1 -> False) -> False)
  -> (forall X1, (v2_funct_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v3_relat_1 (esk21_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk40_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v1_funcop_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk40_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk21_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk14_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk40_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk21_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk14_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk23_1 X1) -> False) -> False)
  -> ((v3_funct_1 esk19_0 -> False) -> False)
  -> ((v2_funct_1 esk20_0 -> False) -> False)
  -> ((v2_relat_1 esk31_0 -> False) -> False)
  -> ((v2_relat_1 esk26_0 -> False) -> False)
  -> ((v2_relat_1 esk22_0 -> False) -> False)
  -> ((v1_funcop_1 esk11_0 -> False) -> False)
  -> ((v4_funct_1 esk38_0 -> False) -> False)
  -> ((v1_relat_1 esk34_0 -> False) -> False)
  -> ((v1_relat_1 esk31_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_relat_1 esk5_0 -> False) -> False)
  -> ((v1_relat_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk34_0 -> False) -> False)
  -> ((v1_funct_1 esk31_0 -> False) -> False)
  -> ((v1_funct_1 esk26_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk19_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk11_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
