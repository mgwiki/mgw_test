(** $I sig/MizarPreamble.mgs **)

Theorem t38_partfun1:
 forall k2_funct_1:set -> set,
 forall esk31_2:set -> set -> set,
 forall esk32_2:set -> set -> set,
 forall v2_funct_1:set -> prop,
 forall esk33_2:set -> set -> set,
 forall esk34_2:set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall k5_relat_1:set -> set -> set,
 forall k6_relat_1:set -> set -> set,
 forall v4_funct_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall esk26_1:set -> set,
 forall esk22_1:set -> set,
 forall k1_xboole_0:set,
 forall esk20_1:set -> set,
 forall esk23_0:set,
 forall esk21_0:set,
 forall esk10_0:set,
 forall esk9_2:set -> set -> set,
 forall esk19_2:set -> set -> set,
 forall esk28_1:set -> set,
 forall esk15_0:set,
 forall o_0_0_xboole_0:set,
 forall esk14_0:set,
 forall esk8_0:set,
 forall esk13_0:set,
 forall esk18_0:set,
 forall esk7_1:set -> set,
 forall esk16_1:set -> set,
 forall esk25_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall esk17_0:set,
 forall esk27_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk12_1:set -> set,
 forall esk24_1:set -> set,
 forall v1_setfam_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v2_relat_1:set -> prop,
 forall k3_relat_1:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk29_2:set -> set -> set,
 forall esk30_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k9_xtuple_0:set -> set,
 forall v1_relat_1:set -> prop,
 forall k1_relset_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall k3_partfun1:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
     (forall X2 X3 X4 X1, ((k1_funct_1 (k3_partfun1 X1 X3 X4) X2) = (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X2 (k1_relset_1 X3 (k3_partfun1 X1 X3 X4)) -> False)
  -> (forall X4 X2 X1 X3, (r2_hidden (k1_funct_1 X1 X2) X3 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X2 (k1_relset_1 X4 (k3_partfun1 X1 X4 X3)) -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 (k9_xtuple_0 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k1_relset_1 X3 (k3_partfun1 X2 X3 X4)) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> r2_hidden X1 (k1_relset_1 X2 (k3_partfun1 X3 X2 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_hidden X1 (k1_relset_1 X3 (k3_partfun1 X2 X3 X4)) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> r2_hidden X1 (k9_xtuple_0 X2) -> r2_hidden (k1_funct_1 X2 X1) X4 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> (k1_funct_1 X1 (esk32_2 X1 X2)) = (esk31_2 X1 X2) -> (k1_funct_1 X2 (esk33_2 X1 X2)) = (esk34_2 X1 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 X1) -> r2_hidden (esk33_2 X1 X2) (k10_xtuple_0 X1) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X3 X1 X2, (r1_tarski (k1_relset_1 X1 (k3_partfun1 X2 X1 X3)) (k9_xtuple_0 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> ((k1_funct_1 X1 (esk34_2 X1 X2)) = (esk33_2 X1 X2) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> (k1_funct_1 X1 (esk32_2 X1 X2)) = (esk31_2 X1 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> ((k1_funct_1 X2 (esk31_2 X1 X2)) = (esk32_2 X1 X2) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> (k1_funct_1 X2 (esk33_2 X1 X2)) = (esk34_2 X1 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> r2_hidden (esk33_2 X1 X2) (k10_xtuple_0 X1) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> (r2_hidden (esk34_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> (k1_funct_1 X1 (esk32_2 X1 X2)) = (esk31_2 X1 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> (r2_hidden (esk31_2 X1 X2) (k10_xtuple_0 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> (k1_funct_1 X2 (esk33_2 X1 X2)) = (esk34_2 X1 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> r2_hidden (esk33_2 X1 X2) (k10_xtuple_0 X1) -> False)
  -> (forall X2 X3 X1, (r1_tarski (k10_xtuple_0 (k3_partfun1 X1 X2 X3)) (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k3_partfun1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk4_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> (k1_funct_1 X1 (esk30_2 X1 X2)) = (k1_funct_1 X2 (esk30_2 X1 X2)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk4_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> ((k1_funct_1 X2 (esk31_2 X1 X2)) = (esk32_2 X1 X2) -> False) -> ((k1_funct_1 X1 (esk34_2 X1 X2)) = (esk33_2 X1 X2) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk5_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> ((k1_funct_1 X1 (esk34_2 X1 X2)) = (esk33_2 X1 X2) -> False) -> (r2_hidden (esk31_2 X1 X2) (k10_xtuple_0 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> ((k1_funct_1 X2 (esk31_2 X1 X2)) = (esk32_2 X1 X2) -> False) -> (r2_hidden (esk34_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_1 X1) -> False) -> (r2_hidden (esk31_2 X1 X2) (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk34_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X2) = (k10_xtuple_0 X1) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (v2_funct_1 (k3_partfun1 X1 X2 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> r2_hidden (esk29_2 X1 X2) X2 -> r2_hidden (esk29_2 X1 X2) X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k3_partfun1 X1 X2 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 (k9_xtuple_0 X2) -> False) -> X4 = (k2_funct_1 X2) -> X1 = (k1_funct_1 X4 X3) -> v1_relat_1 X4 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X2 -> v2_funct_1 X2 -> r2_hidden X3 (k10_xtuple_0 X2) -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 (k10_xtuple_0 X2) -> False) -> X4 = (k2_funct_1 X2) -> X1 = (k1_funct_1 X2 X3) -> v1_relat_1 X4 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X2 -> v2_funct_1 X2 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (X1 = (k1_funct_1 X2 X3) -> False) -> X2 = (k2_funct_1 X4) -> X3 = (k1_funct_1 X4 X1) -> v1_relat_1 X4 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X2 -> v2_funct_1 X4 -> r2_hidden X1 (k9_xtuple_0 X4) -> False)
  -> (forall X4 X2 X3 X1, (X1 = (k1_funct_1 X2 X3) -> False) -> X4 = (k2_funct_1 X2) -> X3 = (k1_funct_1 X4 X1) -> v1_relat_1 X4 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X2 -> v2_funct_1 X2 -> r2_hidden X1 (k10_xtuple_0 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k5_relat_1 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k9_xtuple_0 X1)) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk6_2 X1 X2)) = (esk5_2 X1 X2) -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, ((k5_relat_1 (k6_relat_1 X3 X1) X2) = (k3_partfun1 X1 X2 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, ((k1_funct_1 (k3_relat_1 X2 (k2_funct_1 X2)) X1) = X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> (r2_hidden (esk6_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, ((k1_funct_1 (k2_funct_1 X2) (k1_funct_1 X2 X1)) = X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k9_xtuple_0 X1)) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk30_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk29_2 X1 X2) X2 -> False) -> (r2_hidden (esk29_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v2_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X2 X3 X1, (v5_relat_1 (k5_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k6_relat_1 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k6_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v5_relat_1 X2 X3 -> False)
  -> (forall X2 X3 X1, (v4_relat_1 (k5_relat_1 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v4_relat_1 (k5_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k6_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v4_relat_1 X2 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k5_relat_1 (k5_relat_1 X1 X2) X2) = (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k6_relat_1 X2 (k6_relat_1 X2 X1)) = (k6_relat_1 X2 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v1_relat_1 (k6_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v1_relat_1 (k6_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v4_relat_1 X2 X3 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, ((k9_xtuple_0 X1) = (k10_xtuple_0 X2) -> False) -> X1 = (k2_funct_1 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X2 -> False)
  -> (forall X1 X2, (v2_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k5_relat_1 X1 X2) = X1 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k6_relat_1 X2 X1) = X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v3_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k6_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k6_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k6_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k6_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k6_relat_1 X2 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k10_xtuple_0 (k2_funct_1 X1)) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, ((k9_xtuple_0 (k2_funct_1 X1)) = (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_setfam_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 (k2_funct_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, ((k6_relat_1 (k10_xtuple_0 X1) X1) = X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1, ((k5_relat_1 X1 (k9_xtuple_0 X1)) = X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk26_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk12_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_funct_1 (k3_partfun1 esk3_0 esk1_0 esk2_0)) = (k3_partfun1 (k2_funct_1 esk3_0) esk2_0 esk1_0) -> False)
  -> (forall X1, v1_subset_1 (esk20_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk23_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk11_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk9_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk11_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk9_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk9_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk9_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk16_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk28_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk27_0 -> False) -> False)
  -> ((v2_relat_1 esk21_0 -> False) -> False)
  -> ((v2_relat_1 esk18_0 -> False) -> False)
  -> ((v2_relat_1 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_funct_1 esk14_0 -> False) -> False)
  -> ((v2_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk8_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> ((v1_relat_1 esk8_0 -> False) -> False)
  -> ((v1_relat_1 esk3_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
