(** $I sig/MizarPreamble.mgs **)

Theorem t90_funct_2:
 forall v1_funct_2:set -> set -> set -> prop,
 forall esk8_5:set -> set -> set -> set -> set -> set,
 forall k5_partfun1:set -> set -> set -> set,
 forall r1_partfun1:set -> set -> prop,
 forall esk10_4:set -> set -> set -> set -> set,
 forall r1_relset_1:set -> set -> set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk6_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall esk24_2:set -> set -> set,
 forall esk37_2:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk32_1:set -> set,
 forall esk28_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall esk26_1:set -> set,
 forall esk29_0:set,
 forall esk27_0:set,
 forall esk15_0:set,
 forall esk16_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall esk31_2:set -> set -> set,
 forall esk21_1:set -> set,
 forall esk11_1:set -> set,
 forall esk23_0:set,
 forall esk19_0:set,
 forall esk18_0:set,
 forall o_0_0_xboole_0:set,
 forall esk12_0:set,
 forall esk20_0:set,
 forall esk34_1:set -> set,
 forall esk25_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk22_0:set,
 forall esk33_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall v3_funct_1:set -> prop,
 forall esk17_1:set -> set,
 forall esk30_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk5_2:set -> set -> set,
 forall v2_relat_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall k1_xboole_0:set,
 forall k9_xtuple_0:set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk9_4:set -> set -> set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_relset_1:set -> set -> set,
 forall esk35_4:set -> set -> set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk36_4:set -> set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
     (forall X2 X1 X4 X5 X3, ((k1_funct_1 (esk36_4 X2 X4 X3 X5) X1) = (k1_funct_1 X3 X1) -> False) -> v1_funct_1 X3 -> r2_hidden X1 X2 -> r2_hidden X1 (k1_relset_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> r2_hidden (esk35_4 X2 X4 X3 X5) (k1_relset_1 X2 X3) -> r2_hidden (k1_funct_1 X3 (esk35_4 X2 X4 X3 X5)) X4 -> False)
  -> (forall X4 X5 X2 X3 X1, ((k1_funct_1 (esk36_4 X2 X4 X3 X5) X1) = X5 -> False) -> (r2_hidden X1 (k1_relset_1 X2 X3) -> False) -> v1_funct_1 X3 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> r2_hidden (esk35_4 X2 X4 X3 X5) (k1_relset_1 X2 X3) -> r2_hidden (k1_funct_1 X3 (esk35_4 X2 X4 X3 X5)) X4 -> False)
  -> (forall X1 X2 X4 X3, (m1_subset_1 (esk36_4 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> r2_hidden (esk35_4 X1 X2 X3 X4) (k1_relset_1 X1 X3) -> r2_hidden (k1_funct_1 X3 (esk35_4 X1 X2 X3 X4)) X2 -> False)
  -> (forall X1 X2 X4 X3, (v1_funct_2 (esk36_4 X1 X2 X3 X4) X1 X2 -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> r2_hidden (esk35_4 X1 X2 X3 X4) (k1_relset_1 X1 X3) -> r2_hidden (k1_funct_1 X3 (esk35_4 X1 X2 X3 X4)) X2 -> False)
  -> (forall X1 X2 X4 X3, (v1_funct_1 (esk36_4 X1 X2 X3 X4) -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> r2_hidden (esk35_4 X1 X2 X3 X4) (k1_relset_1 X1 X3) -> r2_hidden (k1_funct_1 X3 (esk35_4 X1 X2 X3 X4)) X2 -> False)
  -> (forall X5 X3 X2 X1 X4, (m1_subset_1 (esk8_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> X4 = (k5_partfun1 X1 X2 X3) -> v1_funct_1 X3 -> r2_hidden X5 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X5 X3 X2 X1 X4, (v1_partfun1 (esk8_5 X1 X2 X3 X4 X5) X1 -> False) -> X4 = (k5_partfun1 X1 X2 X3) -> v1_funct_1 X3 -> r2_hidden X5 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X5 X1 X3 X2 X4, (r1_partfun1 X1 (esk8_5 X2 X3 X1 X4 X5) -> False) -> X4 = (k5_partfun1 X2 X3 X1) -> v1_funct_1 X1 -> r2_hidden X5 X4 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X5 X3 X2 X1 X4, (v1_funct_1 (esk8_5 X1 X2 X3 X4 X5) -> False) -> X4 = (k5_partfun1 X1 X2 X3) -> v1_funct_1 X3 -> r2_hidden X5 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X5 X1 X2 X3, ((k1_funct_1 (esk36_4 X2 X4 X3 X5) X1) = (k1_funct_1 X3 X1) -> False) -> v1_funct_1 X3 -> r2_hidden X5 X4 -> r2_hidden X1 X2 -> r2_hidden X1 (k1_relset_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> r2_hidden (k1_funct_1 X3 (esk35_4 X2 X4 X3 X5)) X4 -> False)
  -> (forall X5 X4 X2 X3 X1, ((k1_funct_1 (esk36_4 X2 X4 X3 X5) X1) = X5 -> False) -> (r2_hidden X1 (k1_relset_1 X2 X3) -> False) -> v1_funct_1 X3 -> r2_hidden X5 X4 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> r2_hidden (k1_funct_1 X3 (esk35_4 X2 X4 X3 X5)) X4 -> False)
  -> (forall X2 X4 X1 X3, (m1_subset_1 (esk36_4 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> v1_funct_1 X3 -> r2_hidden X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> r2_hidden (k1_funct_1 X3 (esk35_4 X1 X2 X3 X4)) X2 -> False)
  -> (forall X2 X4 X1 X3, (v1_funct_2 (esk36_4 X1 X2 X3 X4) X1 X2 -> False) -> v1_funct_1 X3 -> r2_hidden X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> r2_hidden (k1_funct_1 X3 (esk35_4 X1 X2 X3 X4)) X2 -> False)
  -> (forall X2 X4 X1 X3, (v1_funct_1 (esk36_4 X1 X2 X3 X4) -> False) -> v1_funct_1 X3 -> r2_hidden X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> r2_hidden (k1_funct_1 X3 (esk35_4 X1 X2 X3 X4)) X2 -> False)
  -> (forall X5 X3 X2 X1 X4, (X4 = (k5_partfun1 X1 X2 X3) -> False) -> X5 = (esk9_4 X1 X2 X3 X4) -> v1_funct_1 X5 -> v1_funct_1 X3 -> v1_partfun1 X5 X1 -> r1_partfun1 X3 X5 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X5 X3 X2 X1 X4, ((esk8_5 X1 X2 X3 X4 X5) = X5 -> False) -> X4 = (k5_partfun1 X1 X2 X3) -> v1_funct_1 X3 -> r2_hidden X5 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X5 X4 X3 X2, ((k1_funct_1 (esk36_4 X2 X4 X3 X5) X1) = (k1_funct_1 X3 X1) -> False) -> (r2_hidden (esk35_4 X2 X4 X3 X5) (k1_relset_1 X2 X3) -> False) -> v1_funct_1 X3 -> r2_hidden X5 X4 -> r2_hidden X1 X2 -> r2_hidden X1 (k1_relset_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> False)
  -> (forall X4 X2 X1 X3, (X4 = (k5_partfun1 X1 X2 X3) -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X5 X2 X3 X1, ((k1_funct_1 (esk36_4 X2 X4 X3 X5) X1) = X5 -> False) -> (r2_hidden X1 (k1_relset_1 X2 X3) -> False) -> (r2_hidden (esk35_4 X2 X4 X3 X5) (k1_relset_1 X2 X3) -> False) -> v1_funct_1 X3 -> r2_hidden X5 X4 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden (esk35_4 X1 X2 X3 X4) (k1_relset_1 X1 X3) -> False) -> (m1_subset_1 (esk36_4 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> v1_funct_1 X3 -> r2_hidden X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X5 X2 X1 X4 X3, ((k1_funct_1 (esk36_4 X2 X4 X3 X5) X1) = (k1_funct_1 X3 X1) -> False) -> (r2_hidden (esk35_4 X2 X4 X3 X5) X2 -> False) -> v1_funct_1 X3 -> r2_hidden X1 X2 -> r2_hidden X1 (k1_relset_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> False)
  -> (forall X2 X4 X1 X3, (v1_funct_2 (esk36_4 X1 X2 X3 X4) X1 X2 -> False) -> (r2_hidden (esk35_4 X1 X2 X3 X4) (k1_relset_1 X1 X3) -> False) -> v1_funct_1 X3 -> r2_hidden X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X5 X2 X3 X1, ((k1_funct_1 (esk36_4 X2 X4 X3 X5) X1) = X5 -> False) -> (r2_hidden X1 (k1_relset_1 X2 X3) -> False) -> (r2_hidden (esk35_4 X2 X4 X3 X5) X2 -> False) -> v1_funct_1 X3 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> False)
  -> (forall X4 X2 X1 X3, (r2_hidden (esk35_4 X1 X2 X3 X4) X1 -> False) -> (m1_subset_1 (esk36_4 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X2 X1 X3, (X4 = (k5_partfun1 X1 X2 X3) -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False) -> (v1_partfun1 (esk10_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k5_partfun1 X2 X3 X1) -> False) -> (r1_partfun1 X1 (esk10_4 X2 X3 X1 X4) -> False) -> (r2_hidden (esk9_4 X2 X3 X1 X4) X4 -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X2 X1 X3, (X4 = (k5_partfun1 X1 X2 X3) -> False) -> (v1_funct_1 (esk10_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X2 X1 X3, (X4 = (k5_partfun1 X1 X2 X3) -> False) -> ((esk9_4 X1 X2 X3 X4) = (esk10_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X4 -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X2 X1 X3, (r2_hidden (esk35_4 X1 X2 X3 X4) X1 -> False) -> (v1_funct_2 (esk36_4 X1 X2 X3 X4) X1 X2 -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X4 X1 X3, (v1_funct_1 (esk36_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk35_4 X1 X2 X3 X4) (k1_relset_1 X1 X3) -> False) -> v1_funct_1 X3 -> r2_hidden X4 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X4 X2 X1 X3, (v1_funct_1 (esk36_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk35_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X3 X2 X4, (r1_relset_1 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> r1_tarski (k1_relset_1 X2 X4) (k1_relset_1 X2 X1) -> r1_tarski (k5_partfun1 X2 X3 X1) (k5_partfun1 X2 X3 X4) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X2 -> r2_hidden (esk7_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X1 X3 X4, (r1_tarski X3 X4 -> False) -> r1_relset_1 X1 X2 X3 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X3 X2 X5 X4 X6, (r2_hidden X4 X6 -> False) -> X1 = X4 -> X6 = (k5_partfun1 X2 X3 X5) -> v1_funct_1 X5 -> v1_funct_1 X1 -> v1_partfun1 X1 X2 -> r1_partfun1 X5 X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X3 X1 X2, (r1_relset_1 X3 X4 X1 X2 -> False) -> r1_tarski X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X1 X2 X3, (r1_relset_1 X2 X3 X1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1 X4, (r1_partfun1 X1 X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X4 -> r2_hidden X4 (k5_partfun1 X2 X3 X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_xboole_0 (k5_partfun1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_xboole_0 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> ((k1_relset_1 X2 X1) = X2 -> False) -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X2 X1, (X1 = k1_xboole_0 -> False) -> X3 = k1_xboole_0 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v1_funct_2 X2 X1 X3 -> False) -> (k1_relset_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X1 X3) = (k1_funct_1 X2 X3) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_partfun1 X1 X2 -> r2_hidden X3 (k3_xboole_0 (k9_xtuple_0 X1) (k9_xtuple_0 X2)) -> False)
  -> (forall X1 X2 X3, (v1_funct_2 X1 X2 X3 -> False) -> X3 = k1_xboole_0 -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (r1_partfun1 X1 X2 -> False) -> (k1_funct_1 X1 (esk6_2 X1 X2)) = (k1_funct_1 X2 (esk6_2 X1 X2)) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X2, (r1_partfun1 X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) (k3_xboole_0 (k9_xtuple_0 X1) (k9_xtuple_0 X2)) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (r2_hidden (k1_funct_1 X1 X3) X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r1_partfun1 X2 X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk5_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk24_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk24_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X1 = (k1_tarski X2) -> False) -> (r2_hidden (esk37_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 (k3_xboole_0 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_partfun1 X1 X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk24_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk24_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X1 = (k1_tarski X2) -> False) -> (esk37_2 X1 X2) = X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk32_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk30_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_relset_1 esk1_0 esk2_0 esk4_0 esk3_0 -> False)
  -> (forall X1, v1_subset_1 (esk26_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (k1_tarski X1) = esk2_0 -> False)
  -> (v3_funct_1 esk29_0 -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> ((r1_tarski (k5_partfun1 esk1_0 esk2_0 esk3_0) (k5_partfun1 esk1_0 esk2_0 esk4_0) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk14_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk13_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk2_0)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk31_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk14_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk13_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk31_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk31_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk31_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk21_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk34_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk33_0 -> False) -> False)
  -> ((v2_relat_1 esk27_0 -> False) -> False)
  -> ((v2_relat_1 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk20_0 -> False) -> False)
  -> ((v2_funct_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk19_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
