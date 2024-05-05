(** $I sig/MizarPreamble.mgs **)

Theorem t4_arytm_3:
 forall esk21_0:set,
 forall r1_tarski:set -> set -> prop,
 forall k4_ordinal1:set,
 forall epred1_0:prop,
 forall k9_ordinal3:set -> set -> set,
 forall esk23_2:set -> set -> set,
 forall esk24_2:set -> set -> set,
 forall r1_arytm_3:set -> set -> prop,
 forall esk20_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall v7_ordinal1:set -> prop,
 forall esk22_0:set,
 forall np__1:set,
 forall esk3_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall v1_ordinal1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk9_1:set -> set,
 forall esk13_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall esk12_1:set -> set,
 forall esk10_0:set,
 forall esk8_0:set,
 forall esk15_0:set,
 forall v2_xxreal_0:set -> prop,
 forall esk6_1:set -> set,
 forall esk11_0:set,
 forall esk17_0:set,
 forall esk14_1:set -> set,
 forall v5_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk16_1:set -> set,
 forall esk5_2:set -> set -> set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk19_2:set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall esk25_2:set -> set -> set,
 forall k11_ordinal2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall r1_ordinal1:set -> set -> prop,
 forall v3_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X4 X1 X3 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden (k11_ordinal2 X3 X1) (k11_ordinal2 X4 X2) -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X3 X4 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal1 X1 X3 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 (k11_ordinal2 X1 X2) (k11_ordinal2 X3 X2) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden (k11_ordinal2 X3 X1) (k11_ordinal2 X4 X2) -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> ((k9_ordinal3 (esk23_2 X1 X2) (esk24_2 X1 X2)) = X1 -> False) -> (r1_ordinal1 esk21_0 X1 -> False) -> epred1_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> ((k9_ordinal3 (esk23_2 X2 X1) (esk25_2 X2 X1)) = X1 -> False) -> (r1_ordinal1 esk21_0 X2 -> False) -> epred1_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> r2_hidden X2 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal1 esk21_0 X1 -> False) -> (r1_arytm_3 (esk24_2 X1 X2) (esk25_2 X1 X2) -> False) -> epred1_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> ((k9_ordinal3 (esk18_2 X1 X2) (esk19_2 X1 X2)) = X1 -> False) -> (epred1_0 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> ((k9_ordinal3 (esk18_2 X2 X1) (esk20_2 X2 X1)) = X1 -> False) -> (epred1_0 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> r2_hidden X2 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (epred1_0 -> False) -> (r1_arytm_3 (esk19_2 X1 X2) (esk20_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk7_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (k9_ordinal3 X1 X2) = esk21_0 -> (k9_ordinal3 X1 X3) = esk22_0 -> epred1_0 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_arytm_3 X2 X3 -> False)
  -> (forall X3 X2 X1, (k9_ordinal3 X1 X2) = esk1_0 -> (k9_ordinal3 X1 X3) = esk2_0 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_arytm_3 X2 X3 -> False)
  -> (forall X2 X5 X4 X1 X3, (X3 = np__1 -> False) -> X2 = (k11_ordinal2 X3 X5) -> X1 = (k11_ordinal2 X3 X4) -> v3_ordinal1 X5 -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal1 esk21_0 X1 -> False) -> (v7_ordinal1 (esk25_2 X1 X2) -> False) -> epred1_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal1 esk21_0 X1 -> False) -> (v7_ordinal1 (esk24_2 X1 X2) -> False) -> epred1_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal1 esk21_0 X1 -> False) -> (v7_ordinal1 (esk23_2 X1 X2) -> False) -> epred1_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal1 esk21_0 X1 -> False) -> (v3_ordinal1 (esk25_2 X1 X2) -> False) -> epred1_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal1 esk21_0 X1 -> False) -> (v3_ordinal1 (esk24_2 X1 X2) -> False) -> epred1_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal1 esk21_0 X1 -> False) -> (v3_ordinal1 (esk23_2 X1 X2) -> False) -> epred1_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X1 X2 X3, ((k11_ordinal2 (k11_ordinal2 X1 X2) X3) = (k11_ordinal2 X1 (k11_ordinal2 X2 X3)) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k11_ordinal2 (esk3_2 X1 X2) (esk4_2 X1 X2)) = X1 -> False) -> (r1_arytm_3 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k11_ordinal2 (esk3_2 X2 X1) (esk5_2 X2 X1)) = X1 -> False) -> (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (epred1_0 -> False) -> (v7_ordinal1 (esk20_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (epred1_0 -> False) -> (v7_ordinal1 (esk19_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (epred1_0 -> False) -> (v7_ordinal1 (esk18_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (epred1_0 -> False) -> (v3_ordinal1 (esk20_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (epred1_0 -> False) -> (v3_ordinal1 (esk19_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (epred1_0 -> False) -> (v3_ordinal1 (esk18_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v1_ordinal1 X1 -> r2_hidden X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (v3_ordinal1 (esk5_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (v3_ordinal1 (esk4_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (v3_ordinal1 (esk3_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k9_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k9_ordinal3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal1 X1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal1 X1 (k11_ordinal2 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (esk3_2 X1 X2) = np__1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> (r2_hidden X2 X1 -> False) -> (r2_hidden X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, r2_hidden X1 X2 -> r1_tarski X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk9_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v3_ordinal1 X1 -> r2_hidden X1 np__1 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk9_1 X1) -> False)
  -> (forall X1, ((k11_ordinal2 np__1 X1) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 X1 np__1) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (r2_hidden X1 k4_ordinal1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 k1_xboole_0 X1) = k1_xboole_0 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 X1 k1_xboole_0) = k1_xboole_0 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> ((r1_tarski esk22_0 esk21_0 -> False) -> epred1_0 -> False)
  -> ((r2_hidden esk21_0 k4_ordinal1 -> False) -> epred1_0 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((v3_ordinal1 esk22_0 -> False) -> epred1_0 -> False)
  -> ((v3_ordinal1 esk21_0 -> False) -> epred1_0 -> False)
  -> (esk21_0 = k1_xboole_0 -> epred1_0 -> False)
  -> (k1_xboole_0 = esk1_0 -> k1_xboole_0 = esk2_0 -> False)
  -> (forall X1, v1_subset_1 (esk14_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk12_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xboole_0 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_ordinal1 esk11_0 -> False) -> False)
  -> ((v7_ordinal1 esk17_0 -> False) -> False)
  -> ((v7_ordinal1 esk15_0 -> False) -> False)
  -> ((v7_ordinal1 esk2_0 -> False) -> False)
  -> ((v7_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk8_0 -> False) -> False)
  -> ((v3_ordinal1 esk2_0 -> False) -> False)
  -> ((v3_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> False.
Admitted.
