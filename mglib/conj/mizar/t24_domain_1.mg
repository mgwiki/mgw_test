(** $I sig/MizarPreamble.mgs **)

Theorem t24_domain_1:
 forall v2_xtuple_0:set -> prop,
 forall k2_xtuple_0:set -> set,
 forall k1_xtuple_0:set -> set,
 forall k2_mcart_1:set -> set -> set -> set -> set,
 forall v1_xtuple_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk7_2:set -> set -> set,
 forall esk21_1:set -> set,
 forall v3_relat_1:set -> prop,
 forall esk18_0:set,
 forall esk17_1:set -> set,
 forall esk15_0:set,
 forall esk14_0:set,
 forall o_0_0_xboole_0:set,
 forall esk19_0:set,
 forall esk16_0:set,
 forall esk8_1:set -> set,
 forall esk12_0:set,
 forall esk20_1:set -> set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk6_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall v2_relat_1:set -> prop,
 forall esk13_1:set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall k1_xboole_0:set,
 forall esk22_2:set -> set -> set,
 forall k1_mcart_1:set -> set -> set -> set -> set,
 forall k3_mcart_1:set -> set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k3_zfmisc_1:set -> set -> set -> set,
 forall k9_mcart_1:set -> set -> set -> set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall a_6_0_domain_1:set -> set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k4_domain_1:set -> set -> set -> set -> set -> set -> set,
 forall esk9_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall esk10_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall esk11_7:set -> set -> set -> set -> set -> set -> set -> set,
     (forall X3 X7 X5 X1 X6 X2 X4, ((k4_domain_1 X2 X3 X4 (esk9_7 X1 X2 X3 X4 X5 X6 X7) (esk10_7 X1 X2 X3 X4 X5 X6 X7) (esk11_7 X1 X2 X3 X4 X5 X6 X7)) = X1 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X4) -> m1_subset_1 X6 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_6_0_domain_1 X2 X3 X4 X5 X6 X7) -> False)
  -> (forall X3 X7 X5 X1 X6 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk11_7 X1 X2 X3 X4 X5 X6 X7) X7 -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X4) -> m1_subset_1 X6 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_6_0_domain_1 X2 X3 X4 X5 X6 X7) -> False)
  -> (forall X3 X7 X5 X1 X6 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk10_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X4) -> m1_subset_1 X6 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_6_0_domain_1 X2 X3 X4 X5 X6 X7) -> False)
  -> (forall X3 X7 X5 X1 X6 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk9_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X4) -> m1_subset_1 X6 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_6_0_domain_1 X2 X3 X4 X5 X6 X7) -> False)
  -> (forall X3 X7 X5 X1 X6 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk11_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X4) -> m1_subset_1 X6 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_6_0_domain_1 X2 X3 X4 X5 X6 X7) -> False)
  -> (forall X3 X7 X5 X1 X6 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk10_7 X1 X2 X3 X4 X5 X6 X7) X3 -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X4) -> m1_subset_1 X6 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_6_0_domain_1 X2 X3 X4 X5 X6 X7) -> False)
  -> (forall X3 X7 X5 X1 X6 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk9_7 X1 X2 X3 X4 X5 X6 X7) X2 -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X4) -> m1_subset_1 X6 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_6_0_domain_1 X2 X3 X4 X5 X6 X7) -> False)
  -> (forall X4 X7 X10 X9 X8 X1 X3 X5 X2 X6, (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden X7 (a_6_0_domain_1 X2 X4 X6 X8 X9 X10) -> False) -> X7 = (k4_domain_1 X2 X4 X6 X1 X3 X5) -> m1_subset_1 X5 X6 -> m1_subset_1 X3 X4 -> m1_subset_1 X1 X2 -> r2_hidden X5 X10 -> r2_hidden X3 X9 -> r2_hidden X1 X8 -> m1_subset_1 X10 (k1_zfmisc_1 X6) -> m1_subset_1 X9 (k1_zfmisc_1 X4) -> m1_subset_1 X8 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3 X4 X5 X6, (m1_subset_1 (k9_mcart_1 X2 X4 X6 X1 X3 X5) (k1_zfmisc_1 (k3_zfmisc_1 X2 X4 X6)) -> False) -> m1_subset_1 X5 (k1_zfmisc_1 X6) -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X6 X5 X4 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k4_domain_1 X1 X2 X3 X4 X5 X6) (k3_zfmisc_1 X1 X2 X3) -> False) -> m1_subset_1 X6 X3 -> m1_subset_1 X5 X2 -> m1_subset_1 X4 X1 -> False)
  -> (forall X2 X6 X5 X4 X1 X3, ((k4_domain_1 X1 X2 X3 X4 X5 X6) = (k2_tarski (k2_tarski (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) X6) (k1_tarski (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)))) -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X6 X3 -> m1_subset_1 X5 X2 -> m1_subset_1 X4 X1 -> False)
  -> (forall X1 X2 X3 X4 X5 X6, ((k9_mcart_1 X2 X4 X6 X1 X3 X5) = (k3_zfmisc_1 X1 X3 X5) -> False) -> m1_subset_1 X5 (k1_zfmisc_1 X6) -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X4 X5 X6 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) X4) (k1_tarski (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)))) (k3_zfmisc_1 X2 X5 X6) -> False)
  -> (forall X3 X4 X5 X6 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) X4) (k1_tarski (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)))) (k3_zfmisc_1 X5 X2 X6) -> False)
  -> (forall X3 X4 X5 X6 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1) (k1_tarski (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)))) (k3_zfmisc_1 X5 X6 X2) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (k2_tarski (k2_tarski (k1_xtuple_0 (k1_xtuple_0 X1)) (k2_xtuple_0 (k1_xtuple_0 X1))) (k1_tarski (k1_xtuple_0 (k1_xtuple_0 X1)))) (k2_xtuple_0 X1)) (k1_tarski (k2_tarski (k2_tarski (k1_xtuple_0 (k1_xtuple_0 X1)) (k2_xtuple_0 (k1_xtuple_0 X1))) (k1_tarski (k1_xtuple_0 (k1_xtuple_0 X1)))))) = X1 -> False) -> v2_xtuple_0 X1 -> False)
  -> (forall X6 X3 X1 X4 X2 X5 X7, (v1_xboole_0 X7 -> False) -> (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (k3_mcart_1 X1 X2 X3 X4) X5 -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X2) -> m1_subset_1 X6 (k1_zfmisc_1 X1) -> m1_subset_1 X5 (k1_zfmisc_1 X3) -> m1_subset_1 X4 (k3_zfmisc_1 X1 X2 X3) -> r2_hidden X4 (k3_zfmisc_1 X6 X7 X5) -> False)
  -> (forall X6 X3 X1 X4 X2 X5 X7, (v1_xboole_0 X7 -> False) -> (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (k2_mcart_1 X1 X2 X3 X4) X5 -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X1) -> m1_subset_1 X5 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k3_zfmisc_1 X1 X2 X3) -> r2_hidden X4 (k3_zfmisc_1 X6 X5 X7) -> False)
  -> (forall X6 X3 X1 X4 X2 X5 X7, (v1_xboole_0 X7 -> False) -> (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (k1_mcart_1 X1 X2 X3 X4) X5 -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 X1) -> m1_subset_1 X4 (k3_zfmisc_1 X1 X2 X3) -> r2_hidden X4 (k3_zfmisc_1 X5 X6 X7) -> False)
  -> (forall X1 X2 X3 X4 X5 X6, (r2_hidden (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) X5) (k1_tarski (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)))) (k3_zfmisc_1 X2 X4 X6) -> False) -> r2_hidden X5 X6 -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_mcart_1 X1 X2 X3 X4) X3 -> False) -> m1_subset_1 X4 (k3_zfmisc_1 X1 X2 X3) -> False)
  -> (forall X2 X4 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_mcart_1 X1 X2 X3 X4) X2 -> False) -> m1_subset_1 X4 (k3_zfmisc_1 X1 X2 X3) -> False)
  -> (forall X2 X4 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_mcart_1 X1 X2 X3 X4) X1 -> False) -> m1_subset_1 X4 (k3_zfmisc_1 X1 X2 X3) -> False)
  -> (forall X2 X4 X1 X3, ((k2_mcart_1 X1 X2 X3 X4) = (k2_xtuple_0 (k1_xtuple_0 X4)) -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 (k3_zfmisc_1 X1 X2 X3) -> False)
  -> (forall X2 X4 X1 X3, ((k1_mcart_1 X1 X2 X3 X4) = (k1_xtuple_0 (k1_xtuple_0 X4)) -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 (k3_zfmisc_1 X1 X2 X3) -> False)
  -> (forall X2 X4 X1 X3, ((k3_mcart_1 X1 X2 X3 X4) = (k2_xtuple_0 X4) -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 (k3_zfmisc_1 X1 X2 X3) -> False)
  -> (forall X2 X4 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xtuple_0 X4 -> False) -> m1_subset_1 X4 (k3_zfmisc_1 X1 X2 X3) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k3_zfmisc_1 X1 X2 X3) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk22_2 X3 X2) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (k1_xtuple_0 X1) (k2_xtuple_0 X1)) (k1_tarski (k1_xtuple_0 X1))) = X1 -> False) -> v1_xtuple_0 X1 -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> (X2 = k1_xboole_0 -> False) -> (X1 = k1_xboole_0 -> False) -> (k3_zfmisc_1 X1 X2 X3) = k1_xboole_0 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk22_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1, ((k3_zfmisc_1 X1 X2 X3) = k1_xboole_0 -> False) -> X1 = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, ((k3_zfmisc_1 X2 X1 X3) = k1_xboole_0 -> False) -> X1 = k1_xboole_0 -> False)
  -> (forall X3 X2 X1, ((k3_zfmisc_1 X2 X3 X1) = k1_xboole_0 -> False) -> X1 = k1_xboole_0 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xtuple_0 X1 -> False) -> v2_xtuple_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((a_6_0_domain_1 esk1_0 esk2_0 esk3_0 esk4_0 esk5_0 esk6_0) = (k9_mcart_1 esk1_0 esk2_0 esk3_0 esk4_0 esk5_0 esk6_0) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk20_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 esk3_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X3 X1, ((k2_xtuple_0 (k1_xtuple_0 (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3) (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)))))) = X2 -> False) -> False)
  -> (forall X1 X3 X2, ((k1_xtuple_0 (k1_xtuple_0 (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3) (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)))))) = X1 -> False) -> False)
  -> (forall X3 X1 X2, ((k2_xtuple_0 (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3) (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))))) = X3 -> False) -> False)
  -> (forall X3 X2 X1, (v2_xtuple_0 (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3) (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)))) -> False) -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, ((k2_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X2 -> False) -> False)
  -> (forall X1 X2, ((k1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X1 -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk6_0 (k1_zfmisc_1 esk3_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 esk2_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk17_1 X1) -> False) -> False)
  -> ((v2_relat_1 esk16_0 -> False) -> False)
  -> ((v1_xtuple_0 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v2_xtuple_0 esk19_0 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
