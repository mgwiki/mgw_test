(** $I sig/MizarPreamble.mgs **)

Theorem t16_yellow20:
 forall k1_yellow20:set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall esk13_3:set -> set -> set -> set,
 forall esk15_3:set -> set -> set -> set,
 forall esk9_0:set,
 forall esk10_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall k1_relset_1:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v2_relat_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk27_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk41_2:set -> set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk39_1:set -> set,
 forall esk35_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_funcop_1:set -> prop,
 forall k1_xboole_0:set,
 forall esk31_1:set -> set,
 forall esk36_0:set,
 forall esk33_0:set,
 forall esk19_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk38_2:set -> set -> set,
 forall esk26_1:set -> set,
 forall esk34_1:set -> set,
 forall esk29_1:set -> set,
 forall esk18_1:set -> set,
 forall esk25_0:set,
 forall esk16_0:set,
 forall esk17_0:set,
 forall o_0_0_xboole_0:set,
 forall esk28_0:set,
 forall esk23_0:set,
 forall esk42_1:set -> set,
 forall esk24_1:set -> set,
 forall esk32_1:set -> set,
 forall esk14_1:set -> set,
 forall esk30_2:set -> set -> set,
 forall esk20_2:set -> set -> set,
 forall esk5_0:set,
 forall esk6_0:set,
 forall esk22_0:set,
 forall esk40_0:set,
 forall esk8_0:set,
 forall esk7_0:set,
 forall v2_funct_1:set -> prop,
 forall esk21_1:set -> set,
 forall esk37_1:set -> set,
 forall v4_funct_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall r1_partfun1:set -> set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk11_4:set -> set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall m2_pboole:set -> set -> set -> set -> prop,
     (forall X3 X2 X1 X4, (m2_pboole X1 X2 X3 X4 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> v1_funct_1 (k1_funct_1 X1 (esk11_4 X2 X3 X4 X1)) -> v1_funct_2 (k1_funct_1 X1 (esk11_4 X2 X3 X4 X1)) (k1_funct_1 X3 (esk11_4 X2 X3 X4 X1)) (k1_funct_1 X4 (esk11_4 X2 X3 X4 X1)) -> m1_subset_1 (k1_funct_1 X1 (esk11_4 X2 X3 X4 X1)) (k1_zfmisc_1 (k2_zfmisc_1 (k1_funct_1 X3 (esk11_4 X2 X3 X4 X1)) (k1_funct_1 X4 (esk11_4 X2 X3 X4 X1)))) -> False)
  -> (forall X2 X1 X3, (X1 = (k1_yellow20 X2 X3) -> False) -> (k9_xtuple_0 X1) = (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> (k3_xboole_0 (k1_funct_1 X2 (esk12_3 X2 X3 X1)) (k1_funct_1 X3 (esk12_3 X2 X3 X1))) = (k1_funct_1 X1 (esk12_3 X2 X3 X1)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X3 X1 X2 X4, (m2_pboole X4 X1 X2 X3 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X1 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X4 X1 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X4 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X5 X4 X3 X1 X2, (m1_subset_1 (k1_funct_1 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 (k1_funct_1 X3 X2) (k1_funct_1 X4 X2))) -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X4 X5 -> v4_relat_1 X3 X5 -> v4_relat_1 X1 X5 -> v1_partfun1 X4 X5 -> v1_partfun1 X3 X5 -> v1_partfun1 X1 X5 -> r2_hidden X2 X5 -> m2_pboole X1 X5 X3 X4 -> False)
  -> (forall X3 X1 X2 X6 X5 X4, (m1_subset_1 (k9_subset_1 (k2_zfmisc_1 X1 X2) X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 (k3_xboole_0 X5 X1) (k3_xboole_0 X6 X2))) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> r1_partfun1 X3 X4 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X5 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> False)
  -> (forall X5 X4 X3 X1 X2, (v1_funct_2 (k1_funct_1 X1 X2) (k1_funct_1 X3 X2) (k1_funct_1 X4 X2) -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X4 X5 -> v4_relat_1 X3 X5 -> v4_relat_1 X1 X5 -> v1_partfun1 X4 X5 -> v1_partfun1 X3 X5 -> v1_partfun1 X1 X5 -> r2_hidden X2 X5 -> m2_pboole X1 X5 X3 X4 -> False)
  -> (forall X3 X1 X2 X6 X5 X4, (v1_funct_2 (k9_subset_1 (k2_zfmisc_1 X1 X2) X3 X4) (k3_xboole_0 X5 X1) (k3_xboole_0 X6 X2) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> r1_partfun1 X3 X4 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X5 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> False)
  -> (forall X5 X3 X4 X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X5 -> v1_relat_1 X4 -> v1_relat_1 X1 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X1 -> v4_relat_1 X5 X3 -> v4_relat_1 X4 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X5 X3 -> v1_partfun1 X4 X3 -> v1_partfun1 X1 X3 -> r2_hidden X2 X3 -> m2_pboole X1 X3 X4 X5 -> False)
  -> (forall X5 X6 X4 X3 X1 X2, (v1_funct_1 (k9_subset_1 (k2_zfmisc_1 X1 X2) X3 X4) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> r1_partfun1 X3 X4 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X5 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk13_3 X1 X2 X3) X3 -> r2_hidden (esk13_3 X1 X2 X3) X2 -> r2_hidden (esk13_3 X1 X2 X3) X1 -> False)
  -> (forall X4 X3 X1 X2, (v1_partfun1 X1 X2 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X4 X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X3 X2 X1 X4, (v1_funcop_1 X4 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> m2_pboole X4 X2 X1 X3 -> False)
  -> (forall X4 X2 X3 X1, (v1_funct_1 X1 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 X1 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X1 X2 X3, (m2_pboole (esk15_3 X2 X1 X3) X2 X1 X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X1 X3, (X3 = (k1_yellow20 X1 X2) -> False) -> (r2_hidden (esk12_3 X1 X2 X3) (k3_xboole_0 (k9_xtuple_0 X1) (k9_xtuple_0 X2)) -> False) -> (k9_xtuple_0 X3) = (k3_xboole_0 (k9_xtuple_0 X1) (k9_xtuple_0 X2)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk13_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk13_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk13_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk13_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X2 X3 X4, ((k1_funct_1 X4 X1) = (k3_xboole_0 (k1_funct_1 X2 X1) (k1_funct_1 X3 X1)) -> False) -> X4 = (k1_yellow20 X2 X3) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v1_partfun1 (k1_yellow20 X1 X2) (k3_xboole_0 X3 X4) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X4 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X4 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1 X3 X4 X2, (v4_relat_1 (k1_yellow20 X1 X2) (k3_xboole_0 X3 X4) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X4 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X4 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1, (r1_partfun1 (k1_funct_1 esk9_0 X1) (k1_funct_1 esk10_0 X1) -> False) -> r2_hidden X1 (k1_relset_1 esk1_0 esk9_0) -> r2_hidden X1 (k1_relset_1 esk2_0 esk10_0) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k1_yellow20 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X4 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X4 -> False)
  -> (forall X3 X4 X2 X1, (v1_relat_1 (k1_yellow20 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X4 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X4 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m1_subset_1 X3 X1 -> v1_xboole_0 (k1_funct_1 X2 X3) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk27_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, ((k9_xtuple_0 X1) = (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> False) -> X1 = (k1_yellow20 X2 X3) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_partfun1 X2 X1 -> False) -> (k1_relset_1 X1 X2) = X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X1 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (r1_partfun1 X2 X1 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_yellow20 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_yellow20 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, ((k1_yellow20 X1 X2) = (k1_yellow20 X2 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk41_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 (esk41_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk41_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v5_relat_1 (esk27_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_partfun1 (esk27_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v4_relat_1 (esk27_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_partfun1 X1 X1 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk41_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk41_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk39_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk35_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk39_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk37_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk37_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (m2_pboole (k1_yellow20 esk9_0 esk10_0) (k3_xboole_0 esk1_0 esk2_0) esk7_0 esk8_0 -> False)
  -> (forall X1, v1_subset_1 (esk31_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk36_0 -> False)
  -> (v1_xboole_0 esk40_0 -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> ((m2_pboole esk10_0 esk2_0 esk5_0 esk6_0 -> False) -> False)
  -> ((m2_pboole esk9_0 esk1_0 esk3_0 esk4_0 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk38_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk30_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk20_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk38_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk30_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk20_2 X1 X2) X1 -> False) -> False)
  -> ((v1_partfun1 esk8_0 (k3_xboole_0 esk1_0 esk2_0) -> False) -> False)
  -> ((v1_partfun1 esk7_0 (k3_xboole_0 esk1_0 esk2_0) -> False) -> False)
  -> ((v4_relat_1 esk8_0 (k3_xboole_0 esk1_0 esk2_0) -> False) -> False)
  -> ((v4_relat_1 esk7_0 (k3_xboole_0 esk1_0 esk2_0) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk38_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk38_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk30_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk42_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((v1_partfun1 esk6_0 esk2_0 -> False) -> False)
  -> ((v1_partfun1 esk5_0 esk2_0 -> False) -> False)
  -> ((v1_partfun1 esk4_0 esk1_0 -> False) -> False)
  -> ((v1_partfun1 esk3_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk6_0 esk2_0 -> False) -> False)
  -> ((v4_relat_1 esk5_0 esk2_0 -> False) -> False)
  -> ((v4_relat_1 esk4_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk3_0 esk1_0 -> False) -> False)
  -> (((k1_yellow20 esk4_0 esk6_0) = esk8_0 -> False) -> False)
  -> (((k1_yellow20 esk3_0 esk5_0) = esk7_0 -> False) -> False)
  -> (forall X1, (v3_relat_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk42_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk29_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_funcop_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk42_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk29_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk42_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk29_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk18_1 X1) -> False) -> False)
  -> ((v3_funct_1 esk22_0 -> False) -> False)
  -> ((v2_funct_1 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk33_0 -> False) -> False)
  -> ((v2_relat_1 esk28_0 -> False) -> False)
  -> ((v2_relat_1 esk25_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_funcop_1 esk16_0 -> False) -> False)
  -> ((v4_funct_1 esk40_0 -> False) -> False)
  -> ((v1_funct_1 esk36_0 -> False) -> False)
  -> ((v1_funct_1 esk33_0 -> False) -> False)
  -> ((v1_funct_1 esk28_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk8_0 -> False) -> False)
  -> ((v1_funct_1 esk7_0 -> False) -> False)
  -> ((v1_funct_1 esk6_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_relat_1 esk36_0 -> False) -> False)
  -> ((v1_relat_1 esk33_0 -> False) -> False)
  -> ((v1_relat_1 esk28_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk8_0 -> False) -> False)
  -> ((v1_relat_1 esk7_0 -> False) -> False)
  -> ((v1_relat_1 esk6_0 -> False) -> False)
  -> ((v1_relat_1 esk5_0 -> False) -> False)
  -> ((v1_relat_1 esk4_0 -> False) -> False)
  -> ((v1_relat_1 esk3_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
