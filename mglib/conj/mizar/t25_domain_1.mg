(** $I sig/MizarPreamble.mgs **)

Theorem t25_domain_1:
 forall k6_xtuple_0:set -> set -> set -> set -> set,
 forall k6_mcart_1:set -> set -> set -> set -> set -> set,
 forall k4_mcart_1:set -> set -> set -> set -> set -> set,
 forall v3_xtuple_0:set -> prop,
 forall k1_xboole_0:set,
 forall esk26_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk9_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall esk16_1:set -> set,
 forall v2_relat_1:set -> prop,
 forall esk21_0:set,
 forall esk20_1:set -> set,
 forall esk19_0:set,
 forall esk18_0:set,
 forall esk17_0:set,
 forall o_0_0_xboole_0:set,
 forall esk22_0:set,
 forall esk24_0:set,
 forall esk10_1:set -> set,
 forall esk15_0:set,
 forall esk23_1:set -> set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk5_0:set,
 forall esk8_0:set,
 forall esk7_0:set,
 forall esk6_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall v2_xtuple_0:set -> prop,
 forall v3_relat_1:set -> prop,
 forall esk25_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall k1_tarski:set -> set,
 forall k2_tarski:set -> set -> set,
 forall v1_xtuple_0:set -> prop,
 forall k1_xtuple_0:set -> set,
 forall k2_xtuple_0:set -> set,
 forall k5_mcart_1:set -> set -> set -> set -> set -> set,
 forall k7_mcart_1:set -> set -> set -> set -> set -> set,
 forall k4_zfmisc_1:set -> set -> set -> set -> set,
 forall k10_mcart_1:set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall esk11_9:set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall esk14_9:set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall esk13_9:set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall esk12_9:set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall k5_domain_1:set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_8_0_domain_1:set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
     (forall X4 X2 X8 X6 X1 X7 X9 X3 X5, ((k5_domain_1 X2 X3 X4 X5 (esk11_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) (esk12_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) (esk13_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) (esk14_9 X1 X2 X3 X4 X5 X6 X7 X8 X9)) = X1 -> False) -> (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X5) -> m1_subset_1 X8 (k1_zfmisc_1 X4) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_8_0_domain_1 X2 X3 X4 X5 X6 X7 X8 X9) -> False)
  -> (forall X4 X2 X8 X6 X1 X7 X9 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk14_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) X9 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X5) -> m1_subset_1 X8 (k1_zfmisc_1 X4) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_8_0_domain_1 X2 X3 X4 X5 X6 X7 X8 X9) -> False)
  -> (forall X4 X2 X8 X6 X1 X7 X9 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk13_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) X8 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X5) -> m1_subset_1 X8 (k1_zfmisc_1 X4) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_8_0_domain_1 X2 X3 X4 X5 X6 X7 X8 X9) -> False)
  -> (forall X4 X2 X8 X6 X1 X7 X9 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk12_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) X7 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X5) -> m1_subset_1 X8 (k1_zfmisc_1 X4) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_8_0_domain_1 X2 X3 X4 X5 X6 X7 X8 X9) -> False)
  -> (forall X4 X2 X8 X6 X1 X7 X9 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk11_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) X6 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X5) -> m1_subset_1 X8 (k1_zfmisc_1 X4) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_8_0_domain_1 X2 X3 X4 X5 X6 X7 X8 X9) -> False)
  -> (forall X4 X2 X8 X6 X1 X7 X9 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk14_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) X5 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X5) -> m1_subset_1 X8 (k1_zfmisc_1 X4) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_8_0_domain_1 X2 X3 X4 X5 X6 X7 X8 X9) -> False)
  -> (forall X4 X2 X8 X6 X1 X7 X9 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk13_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) X4 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X5) -> m1_subset_1 X8 (k1_zfmisc_1 X4) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_8_0_domain_1 X2 X3 X4 X5 X6 X7 X8 X9) -> False)
  -> (forall X4 X2 X8 X6 X1 X7 X9 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk12_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) X3 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X5) -> m1_subset_1 X8 (k1_zfmisc_1 X4) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_8_0_domain_1 X2 X3 X4 X5 X6 X7 X8 X9) -> False)
  -> (forall X4 X2 X8 X6 X1 X7 X9 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk11_9 X1 X2 X3 X4 X5 X6 X7 X8 X9) X2 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X5) -> m1_subset_1 X8 (k1_zfmisc_1 X4) -> m1_subset_1 X7 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_8_0_domain_1 X2 X3 X4 X5 X6 X7 X8 X9) -> False)
  -> (forall X6 X2 X1 X7 X5 X3 X11 X12 X13 X10 X9 X4 X8, (v1_xboole_0 X8 -> False) -> (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden X9 (a_8_0_domain_1 X2 X4 X6 X8 X10 X11 X12 X13) -> False) -> X9 = (k5_domain_1 X2 X4 X6 X8 X1 X3 X5 X7) -> m1_subset_1 X7 X8 -> m1_subset_1 X5 X6 -> m1_subset_1 X3 X4 -> m1_subset_1 X1 X2 -> r2_hidden X7 X13 -> r2_hidden X5 X12 -> r2_hidden X3 X11 -> r2_hidden X1 X10 -> m1_subset_1 X13 (k1_zfmisc_1 X8) -> m1_subset_1 X12 (k1_zfmisc_1 X6) -> m1_subset_1 X11 (k1_zfmisc_1 X4) -> m1_subset_1 X10 (k1_zfmisc_1 X2) -> False)
  -> (forall X6 X5 X4 X3 X2 X1 X7 X8, (m1_subset_1 (k10_mcart_1 X2 X4 X6 X8 X1 X3 X5 X7) (k1_zfmisc_1 (k4_zfmisc_1 X2 X4 X6 X8)) -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X8) -> m1_subset_1 X5 (k1_zfmisc_1 X6) -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X7 X6 X5 X8 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k5_domain_1 X1 X2 X3 X4 X5 X6 X7 X8) (k4_zfmisc_1 X1 X2 X3 X4) -> False) -> m1_subset_1 X8 X4 -> m1_subset_1 X7 X3 -> m1_subset_1 X6 X2 -> m1_subset_1 X5 X1 -> False)
  -> (forall X6 X5 X4 X3 X2 X1 X7 X8, ((k10_mcart_1 X2 X4 X6 X8 X1 X3 X5 X7) = (k4_zfmisc_1 X1 X3 X5 X7) -> False) -> m1_subset_1 X7 (k1_zfmisc_1 X8) -> m1_subset_1 X5 (k1_zfmisc_1 X6) -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X7 X6 X5 X8 X2 X4, ((k5_domain_1 X1 X2 X3 X4 X5 X6 X7 X8) = (k6_xtuple_0 X5 X6 X7 X8) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X8 X4 -> m1_subset_1 X7 X3 -> m1_subset_1 X6 X2 -> m1_subset_1 X5 X1 -> False)
  -> (forall X8 X6 X3 X1 X5 X2 X4 X7 X9, (v1_xboole_0 X9 -> False) -> (v1_xboole_0 X8 -> False) -> (v1_xboole_0 X7 -> False) -> (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (k7_mcart_1 X1 X2 X3 X4 X5) X6 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X3) -> m1_subset_1 X8 (k1_zfmisc_1 X2) -> m1_subset_1 X7 (k1_zfmisc_1 X1) -> m1_subset_1 X6 (k1_zfmisc_1 X4) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> r2_hidden X5 (k4_zfmisc_1 X7 X8 X9 X6) -> False)
  -> (forall X8 X6 X3 X1 X5 X2 X4 X7 X9, (v1_xboole_0 X9 -> False) -> (v1_xboole_0 X8 -> False) -> (v1_xboole_0 X7 -> False) -> (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (k6_mcart_1 X1 X2 X3 X4 X5) X6 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X4) -> m1_subset_1 X8 (k1_zfmisc_1 X2) -> m1_subset_1 X7 (k1_zfmisc_1 X1) -> m1_subset_1 X6 (k1_zfmisc_1 X3) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> r2_hidden X5 (k4_zfmisc_1 X7 X8 X6 X9) -> False)
  -> (forall X8 X6 X3 X1 X5 X2 X4 X7 X9, (v1_xboole_0 X9 -> False) -> (v1_xboole_0 X8 -> False) -> (v1_xboole_0 X7 -> False) -> (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (k5_mcart_1 X1 X2 X3 X4 X5) X6 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X4) -> m1_subset_1 X8 (k1_zfmisc_1 X3) -> m1_subset_1 X7 (k1_zfmisc_1 X1) -> m1_subset_1 X6 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> r2_hidden X5 (k4_zfmisc_1 X7 X6 X8 X9) -> False)
  -> (forall X8 X6 X3 X1 X5 X2 X4 X7 X9, (v1_xboole_0 X9 -> False) -> (v1_xboole_0 X8 -> False) -> (v1_xboole_0 X7 -> False) -> (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (k4_mcart_1 X1 X2 X3 X4 X5) X6 -> False) -> m1_subset_1 X9 (k1_zfmisc_1 X4) -> m1_subset_1 X8 (k1_zfmisc_1 X3) -> m1_subset_1 X7 (k1_zfmisc_1 X2) -> m1_subset_1 X6 (k1_zfmisc_1 X1) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> r2_hidden X5 (k4_zfmisc_1 X6 X7 X8 X9) -> False)
  -> (forall X3 X1 X5 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k7_mcart_1 X1 X2 X3 X4 X5) X4 -> False) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> False)
  -> (forall X3 X1 X5 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k6_mcart_1 X1 X2 X3 X4 X5) X3 -> False) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> False)
  -> (forall X3 X1 X5 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k5_mcart_1 X1 X2 X3 X4 X5) X2 -> False) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> False)
  -> (forall X3 X1 X5 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k4_mcart_1 X1 X2 X3 X4 X5) X1 -> False) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> False)
  -> (forall X3 X1 X5 X2 X4, ((k5_mcart_1 X1 X2 X3 X4 X5) = (k2_xtuple_0 (k1_xtuple_0 (k1_xtuple_0 X5))) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> False)
  -> (forall X3 X1 X5 X2 X4, ((k4_mcart_1 X1 X2 X3 X4 X5) = (k1_xtuple_0 (k1_xtuple_0 (k1_xtuple_0 X5))) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> False)
  -> (forall X3 X1 X5 X2 X4, ((k6_mcart_1 X1 X2 X3 X4 X5) = (k2_xtuple_0 (k1_xtuple_0 X5)) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> False)
  -> (forall X3 X1 X5 X2 X4, ((k7_mcart_1 X1 X2 X3 X4 X5) = (k2_xtuple_0 X5) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> False)
  -> (forall X5 X4 X3 X8 X7 X6 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k6_xtuple_0 X1 X3 X4 X5) (k4_zfmisc_1 X2 X6 X7 X8) -> False)
  -> (forall X3 X5 X4 X6 X8 X7 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k6_xtuple_0 X3 X1 X4 X5) (k4_zfmisc_1 X6 X2 X7 X8) -> False)
  -> (forall X3 X5 X4 X6 X8 X7 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k6_xtuple_0 X3 X4 X1 X5) (k4_zfmisc_1 X6 X7 X2 X8) -> False)
  -> (forall X3 X5 X4 X6 X8 X7 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k6_xtuple_0 X3 X4 X5 X1) (k4_zfmisc_1 X6 X7 X8 X2) -> False)
  -> (forall X6 X5 X4 X3 X2 X1 X7 X8, (r2_hidden (k6_xtuple_0 X1 X3 X5 X7) (k4_zfmisc_1 X2 X4 X6 X8) -> False) -> r2_hidden X7 X8 -> r2_hidden X5 X6 -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X1 X5 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v3_xtuple_0 X5 -> False) -> m1_subset_1 X5 (k4_zfmisc_1 X1 X2 X3 X4) -> False)
  -> (forall X3 X1 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k4_zfmisc_1 X1 X2 X3 X4) -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> (X3 = k1_xboole_0 -> False) -> (X2 = k1_xboole_0 -> False) -> (X1 = k1_xboole_0 -> False) -> (k4_zfmisc_1 X1 X2 X3 X4) = k1_xboole_0 -> False)
  -> (forall X1, ((k6_xtuple_0 (k1_xtuple_0 (k1_xtuple_0 (k1_xtuple_0 X1))) (k2_xtuple_0 (k1_xtuple_0 (k1_xtuple_0 X1))) (k2_xtuple_0 (k1_xtuple_0 X1)) (k2_xtuple_0 X1)) = X1 -> False) -> v3_xtuple_0 X1 -> False)
  -> (forall X2 X3 X4 X1, ((k4_zfmisc_1 X1 X2 X3 X4) = k1_xboole_0 -> False) -> X1 = k1_xboole_0 -> False)
  -> (forall X3 X4 X2 X1, ((k4_zfmisc_1 X2 X1 X3 X4) = k1_xboole_0 -> False) -> X1 = k1_xboole_0 -> False)
  -> (forall X3 X4 X2 X1, ((k4_zfmisc_1 X2 X3 X1 X4) = k1_xboole_0 -> False) -> X1 = k1_xboole_0 -> False)
  -> (forall X3 X4 X2 X1, ((k4_zfmisc_1 X2 X3 X4 X1) = k1_xboole_0 -> False) -> X1 = k1_xboole_0 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk26_2 X3 X2) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (k1_xtuple_0 X1) (k2_xtuple_0 X1)) (k1_tarski (k1_xtuple_0 X1))) = X1 -> False) -> v1_xtuple_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk26_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk25_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xtuple_0 X1 -> False) -> v2_xtuple_0 X1 -> False)
  -> (forall X1, (v2_xtuple_0 X1 -> False) -> v3_xtuple_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((a_8_0_domain_1 esk1_0 esk2_0 esk3_0 esk4_0 esk5_0 esk6_0 esk7_0 esk8_0) = (k10_mcart_1 esk1_0 esk2_0 esk3_0 esk4_0 esk5_0 esk6_0 esk7_0 esk8_0) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk23_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk4_0 -> False)
  -> (v1_xboole_0 esk3_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X3 X4 X1, ((k2_tarski (k2_tarski (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3) (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)))) X4) (k1_tarski (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3) (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)))))) = (k6_xtuple_0 X1 X2 X3 X4) -> False) -> False)
  -> (forall X2 X1 X4 X3, ((k2_xtuple_0 (k1_xtuple_0 (k1_xtuple_0 (k6_xtuple_0 X1 X2 X3 X4)))) = X2 -> False) -> False)
  -> (forall X1 X4 X3 X2, ((k1_xtuple_0 (k1_xtuple_0 (k1_xtuple_0 (k6_xtuple_0 X1 X2 X3 X4)))) = X1 -> False) -> False)
  -> (forall X2 X3 X1, ((k2_xtuple_0 (k1_xtuple_0 (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3) (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)))))) = X2 -> False) -> False)
  -> (forall X3 X2 X4 X1, ((k2_xtuple_0 (k1_xtuple_0 (k6_xtuple_0 X1 X2 X3 X4))) = X3 -> False) -> False)
  -> (forall X3 X1 X2, ((k2_xtuple_0 (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3) (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))))) = X3 -> False) -> False)
  -> (forall X3 X2 X1, (v2_xtuple_0 (k2_tarski (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3) (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)))) -> False) -> False)
  -> (forall X4 X1 X3 X2, ((k2_xtuple_0 (k6_xtuple_0 X1 X2 X3 X4)) = X4 -> False) -> False)
  -> (forall X2 X3 X4 X1, (v3_xtuple_0 (k6_xtuple_0 X1 X2 X3 X4) -> False) -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, ((k2_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X2 -> False) -> False)
  -> (forall X1 X2, ((k1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X1 -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk8_0 (k1_zfmisc_1 esk4_0) -> False) -> False)
  -> ((m1_subset_1 esk7_0 (k1_zfmisc_1 esk3_0) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (k1_zfmisc_1 esk2_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk20_1 X1) -> False) -> False)
  -> ((v2_relat_1 esk19_0 -> False) -> False)
  -> ((v3_xtuple_0 esk24_0 -> False) -> False)
  -> ((v1_xtuple_0 esk18_0 -> False) -> False)
  -> ((v2_xtuple_0 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
