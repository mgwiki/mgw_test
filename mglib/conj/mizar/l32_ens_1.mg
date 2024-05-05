(** $I sig/MizarPreamble.mgs **)

Theorem l32_ens_1:
 forall v1_funct_2:set -> set -> set -> prop,
 forall k1_ens_1:set -> set,
 forall k2_ens_1:set -> set,
 forall a_3_0_ens_1:set -> set -> set -> set,
 forall k2_xtuple_0:set -> set,
 forall k3_ens_1:set -> set -> set,
 forall k4_ens_1:set -> set -> set,
 forall a_1_2_ens_1:set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk28_2:set -> set -> set,
 forall esk36_1:set -> set,
 forall esk32_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall k3_tarski:set -> set,
 forall v3_relat_1:set -> prop,
 forall esk30_1:set -> set,
 forall esk37_0:set,
 forall esk26_0:set,
 forall esk17_2:set -> set -> set,
 forall esk35_2:set -> set -> set,
 forall esk38_1:set -> set,
 forall esk22_0:set,
 forall esk24_0:set,
 forall esk15_0:set,
 forall esk21_0:set,
 forall esk23_0:set,
 forall esk27_0:set,
 forall esk7_1:set -> set,
 forall esk25_1:set -> set,
 forall esk29_2:set -> set -> set,
 forall esk16_2:set -> set -> set,
 forall esk19_2:set -> set -> set,
 forall esk18_0:set,
 forall esk31_0:set,
 forall esk33_0:set,
 forall esk1_0:set,
 forall esk5_0:set,
 forall esk6_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall v2_relat_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall esk20_1:set -> set,
 forall esk34_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall k1_xtuple_0:set -> set,
 forall v1_xtuple_0:set -> prop,
 forall esk10_2:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall k1_funct_2:set -> set -> set,
 forall a_1_0_ens_1:set -> set,
 forall esk40_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk39_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall esk14_4:set -> set -> set -> set -> set,
 forall k1_xboole_0:set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k2_tarski:set -> set -> set,
 forall k1_domain_1:set -> set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall k7_ens_1:set -> set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X1 X2 X3 X4, (v1_xboole_0 X4 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X3 X4 -> m1_subset_1 X2 X4 -> r2_hidden (k2_tarski (k2_tarski (k1_domain_1 X4 X4 X2 X3) X1) (k1_tarski (k1_domain_1 X4 X4 X2 X3))) (k7_ens_1 X4 X2 X3) -> False)
  -> (forall X1 X2 X3 X4, (v1_xboole_0 X4 -> False) -> (v1_funct_2 X1 X2 X3 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X3 X4 -> m1_subset_1 X2 X4 -> r2_hidden (k2_tarski (k2_tarski (k1_domain_1 X4 X4 X2 X3) X1) (k1_tarski (k1_domain_1 X4 X4 X2 X3))) (k7_ens_1 X4 X2 X3) -> False)
  -> (forall X3 X4 X1 X2, (X2 = k1_xboole_0 -> False) -> (v1_xboole_0 X3 -> False) -> X1 = k1_xboole_0 -> v1_funct_1 X4 -> v1_relat_1 X4 -> m1_subset_1 X2 X3 -> m1_subset_1 X1 X3 -> r2_hidden (k2_tarski (k2_tarski (k1_domain_1 X3 X3 X2 X1) X4) (k1_tarski (k1_domain_1 X3 X3 X2 X1))) (k7_ens_1 X3 X2 X1) -> False)
  -> (forall X3 X4 X5 X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X3 (a_3_0_ens_1 X2 X4 X5) -> False) -> X3 = (k1_domain_1 (k2_zfmisc_1 X2 X2) (k1_ens_1 X2) (k1_domain_1 X2 X2 X4 X5) X1) -> m1_subset_1 X5 X2 -> m1_subset_1 X4 X2 -> m1_subset_1 X1 (k1_ens_1 X2) -> r2_hidden (k1_domain_1 (k2_zfmisc_1 X2 X2) (k1_ens_1 X2) (k1_domain_1 X2 X2 X4 X5) X1) (k2_ens_1 X2) -> False)
  -> (forall X3 X4 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k1_domain_1 (k2_zfmisc_1 X1 X1) (k1_ens_1 X1) (k1_domain_1 X1 X1 X2 X3) (esk14_4 X4 X1 X2 X3)) (k2_ens_1 X1) -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> r2_hidden X4 (a_3_0_ens_1 X1 X2 X3) -> False)
  -> (forall X2 X1, ((k2_tarski (k2_tarski (k1_domain_1 X1 X1 (k3_ens_1 X1 X2) (k4_ens_1 X1 X2)) (k2_xtuple_0 X2)) (k1_tarski (k1_domain_1 X1 X1 (k3_ens_1 X1 X2) (k4_ens_1 X1 X2)))) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 (k2_ens_1 X1) -> False)
  -> (forall X3 X4 X2 X1, ((k2_tarski (k2_tarski (k1_domain_1 X1 X1 X2 X3) (k2_xtuple_0 X4)) (k1_tarski (k1_domain_1 X1 X1 X2 X3))) = X4 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> m1_subset_1 X4 (k2_ens_1 X1) -> r2_hidden X4 (k7_ens_1 X1 X2 X3) -> False)
  -> (forall X1 X3 X4 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden (k1_domain_1 (k2_zfmisc_1 X2 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) (k1_domain_1 X2 X2 X1 X3) X4) (k7_ens_1 X2 X1 X3) -> False) -> X1 = k1_xboole_0 -> v1_funct_1 X4 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> v1_funct_2 X4 X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X3 X4 X1, (X1 = k1_xboole_0 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (k1_domain_1 (k2_zfmisc_1 X2 X2) (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) (k1_domain_1 X2 X2 X3 X1) X4) (k7_ens_1 X2 X3 X1) -> False) -> v1_funct_1 X4 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> v1_funct_2 X4 X3 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X5 X4 X3 X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X5 (a_1_2_ens_1 X2) -> False) -> X1 = k1_xboole_0 -> X5 = (k1_domain_1 (k2_zfmisc_1 X2 X2) (k1_ens_1 X2) (k1_domain_1 X2 X2 X1 X3) X4) -> v1_funct_1 X4 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> v1_funct_2 X4 X1 X3 -> m1_subset_1 X4 (k1_ens_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X4 X2 X5 X1, (X1 = k1_xboole_0 -> False) -> (v1_xboole_0 X3 -> False) -> (r2_hidden X5 (a_1_2_ens_1 X3) -> False) -> X5 = (k1_domain_1 (k2_zfmisc_1 X3 X3) (k1_ens_1 X3) (k1_domain_1 X3 X3 X2 X1) X4) -> v1_funct_1 X4 -> m1_subset_1 X2 X3 -> m1_subset_1 X1 X3 -> v1_funct_2 X4 X2 X1 -> m1_subset_1 X4 (k1_ens_1 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X1)) -> False)
  -> (forall X4 X1 X3 X2, ((k1_domain_1 (k2_zfmisc_1 X2 X2) (k1_ens_1 X2) (k1_domain_1 X2 X2 X3 X4) (esk14_4 X1 X2 X3 X4)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> r2_hidden X1 (a_3_0_ens_1 X2 X3 X4) -> False)
  -> (forall X3 X4 X5 X6 X1 X2, (X1 = X2 -> False) -> (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) X4) (k1_tarski (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)))) = (k2_tarski (k2_tarski (k2_tarski (k2_tarski X2 X5) (k1_tarski X2)) X6) (k1_tarski (k2_tarski (k2_tarski X2 X5) (k1_tarski X2)))) -> False)
  -> (forall X3 X4 X5 X6 X1 X2, (X1 = X2 -> False) -> (k2_tarski (k2_tarski (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) X4) (k1_tarski (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)))) = (k2_tarski (k2_tarski (k2_tarski (k2_tarski X5 X2) (k1_tarski X5)) X6) (k1_tarski (k2_tarski (k2_tarski X5 X2) (k1_tarski X5)))) -> False)
  -> (forall X1 X2, ((k1_domain_1 (k2_zfmisc_1 X2 X2) (k1_ens_1 X2) (k1_domain_1 X2 X2 (esk11_2 X1 X2) (esk12_2 X1 X2)) (esk13_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> r2_hidden X1 (a_1_2_ens_1 X2) -> False)
  -> (forall X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk14_4 X1 X2 X3 X4) (k1_ens_1 X2) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> r2_hidden X1 (a_3_0_ens_1 X2 X3 X4) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_domain_1 X1 X2 X3 X4) (k2_zfmisc_1 X1 X2) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X1 X4 X3 X2, ((k1_domain_1 X1 X2 X3 X4) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 (esk11_2 X1 X2) (esk12_2 X1 X2))) -> False) -> r2_hidden X1 (a_1_2_ens_1 X2) -> False)
  -> (forall X4 X2 X1 X3, ((k4_ens_1 X1 X2) = X3 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 (k2_ens_1 X1) -> r2_hidden X2 (k7_ens_1 X1 X4 X3) -> False)
  -> (forall X4 X2 X1 X3, ((k3_ens_1 X1 X2) = X3 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 (k2_ens_1 X1) -> r2_hidden X2 (k7_ens_1 X1 X3 X4) -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X2 (k7_ens_1 X1 X3 X4) -> False) -> (k3_ens_1 X1 X2) = X3 -> (k4_ens_1 X1 X2) = X4 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 (k2_ens_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_tarski (k7_ens_1 X1 X2 X3) (k2_ens_1 X1) -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_2 (esk13_2 X1 X2) (esk11_2 X1 X2) (esk12_2 X1 X2) -> False) -> r2_hidden X1 (a_1_2_ens_1 X2) -> False)
  -> (forall X2 X3 X1, ((k7_ens_1 X1 X2 X3) = (a_3_0_ens_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> r2_hidden (esk39_2 X1 X2) X2 -> r2_hidden (esk39_2 X1 X2) X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk8_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk40_2 X3 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2, ((k1_funct_2 (esk9_2 X1 X2) (esk10_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> r2_hidden X1 (a_1_0_ens_1 X2) -> False)
  -> (forall X4 X3 X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X4 (a_1_0_ens_1 X2) -> False) -> X4 = (k1_funct_2 X1 X3) -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (k1_xtuple_0 X1) (k2_xtuple_0 X1)) (k1_tarski (k1_xtuple_0 X1))) = X1 -> False) -> v1_xtuple_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk13_2 X1 X2) (k1_ens_1 X2) -> False) -> r2_hidden X1 (a_1_2_ens_1 X2) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk39_2 X1 X2) X2 -> False) -> (r2_hidden (esk39_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k4_ens_1 X1 X2) X1 -> False) -> m1_subset_1 X2 (k2_ens_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_ens_1 X1 X2) X1 -> False) -> m1_subset_1 X2 (k2_ens_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk12_2 X1 X2) X2 -> False) -> r2_hidden X1 (a_1_2_ens_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk11_2 X1 X2) X2 -> False) -> r2_hidden X1 (a_1_2_ens_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk10_2 X1 X2) X2 -> False) -> r2_hidden X1 (a_1_0_ens_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk9_2 X1 X2) X2 -> False) -> r2_hidden X1 (a_1_0_ens_1 X2) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, ((esk11_2 X1 X2) = k1_xboole_0 -> False) -> (v1_xboole_0 X2 -> False) -> (esk12_2 X1 X2) = k1_xboole_0 -> r2_hidden X1 (a_1_2_ens_1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_tarski (k2_ens_1 X2) (k2_ens_1 X1) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk13_2 X1 X2) -> False) -> r2_hidden X1 (a_1_2_ens_1 X2) -> False)
  -> (forall X2 X1, (r2_hidden (esk40_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k4_ens_1 X1 X2) = (k2_xtuple_0 (k1_xtuple_0 X2)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 (k2_ens_1 X1) -> False)
  -> (forall X2 X1, ((k3_ens_1 X1 X2) = (k1_xtuple_0 (k1_xtuple_0 X2)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 (k2_ens_1 X1) -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k1_funct_2 X2 X1) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk28_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk28_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (k2_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k2_ens_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (k2_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k2_ens_1 X2) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_xboole_0 (k1_funct_2 X1 X2) -> False) -> v1_xboole_0 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk36_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk34_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_ens_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k1_ens_1 X1) -> False)
  -> (forall X1, ((k3_tarski (a_1_0_ens_1 X1)) = (k1_ens_1 X1) -> False) -> (v1_xboole_0 X1 -> False) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v4_funct_1 (k1_ens_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, ((k2_ens_1 X1) = (a_1_2_ens_1 X1) -> False) -> (v1_xboole_0 X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k7_ens_1 esk2_0 esk3_0 esk4_0) = (k7_ens_1 esk1_0 esk5_0 esk6_0) -> False)
  -> (forall X1, v1_xboole_0 (k1_funct_2 X1 X1) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk30_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk33_0 -> False)
  -> (v1_xboole_0 esk37_0 -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk17_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, ((k2_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X2 -> False) -> False)
  -> (forall X1 X2, ((k1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X1 -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk16_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m2_subset_1 esk4_0 esk1_0 esk2_0 -> False) -> False)
  -> ((m2_subset_1 esk3_0 esk1_0 esk2_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk35_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk29_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk17_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk35_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk29_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk17_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_funct_1 (k1_funct_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk35_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk29_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk35_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk38_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk6_0 esk1_0 -> False) -> False)
  -> ((m1_subset_1 esk5_0 esk1_0 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk38_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk38_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk38_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk25_1 X1) -> False) -> False)
  -> ((v1_xtuple_0 esk22_0 -> False) -> False)
  -> ((v4_funct_1 esk37_0 -> False) -> False)
  -> ((v2_relat_1 esk31_0 -> False) -> False)
  -> ((v2_relat_1 esk27_0 -> False) -> False)
  -> ((v2_relat_1 esk24_0 -> False) -> False)
  -> ((v2_funct_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk33_0 -> False) -> False)
  -> ((v1_relat_1 esk31_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_funct_1 esk33_0 -> False) -> False)
  -> ((v1_funct_1 esk31_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((esk4_0 = esk6_0 -> False) -> False)
  -> ((esk5_0 = esk3_0 -> False) -> False)
  -> False.
Admitted.
