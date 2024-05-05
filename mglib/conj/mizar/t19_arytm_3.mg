(** $I sig/MizarPreamble.mgs **)

Theorem t19_arytm_3:
 forall k9_ordinal3:set -> set -> set,
 forall k6_ordinal3:set -> set -> set,
 forall esk3_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall k1_xboole_0:set,
 forall k2_arytm_3:set -> set -> set,
 forall v6_ordinal1:set -> prop,
 forall esk18_1:set -> set,
 forall esk15_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall esk14_1:set -> set,
 forall esk12_0:set,
 forall esk10_0:set,
 forall esk17_0:set,
 forall v2_xxreal_0:set -> prop,
 forall esk8_1:set -> set,
 forall esk13_0:set,
 forall esk19_0:set,
 forall esk16_1:set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall v5_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall esk11_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k11_ordinal2:set -> set -> set,
 forall r1_arytm_3:set -> set -> prop,
 forall np__1:set,
 forall esk9_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall r2_arytm_3:set -> set -> prop,
 forall esk7_3:set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k4_ordinal1:set,
 forall k3_arytm_3:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k3_arytm_3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X2 -> r2_arytm_3 X3 X1 -> m1_subset_1 X3 k4_ordinal1 -> r2_arytm_3 (esk7_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_arytm_3 X1 X2) -> False) -> (r2_arytm_3 (esk7_3 X1 X2 X3) X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X2 -> r2_arytm_3 X3 X1 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_arytm_3 X1 X2) -> False) -> (r2_arytm_3 (esk7_3 X1 X2 X3) X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X2 -> r2_arytm_3 X3 X1 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_arytm_3 X1 X2) -> False) -> (v7_ordinal1 (esk7_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X2 -> r2_arytm_3 X3 X1 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_arytm_3 X1 X2) -> False) -> (v3_ordinal1 (esk7_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X2 -> r2_arytm_3 X3 X1 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X3 X2 X1 X4, (r2_arytm_3 X1 X4 -> False) -> X4 = (k3_arytm_3 X2 X3) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X1 X3 -> r2_arytm_3 X1 X2 -> m1_subset_1 X4 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk9_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X5 X4 X1 X3, (X3 = np__1 -> False) -> X2 = (k11_ordinal2 X3 X5) -> X1 = (k11_ordinal2 X3 X4) -> v3_ordinal1 X5 -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X1 X2, (r2_arytm_3 X2 X1 -> False) -> (k9_ordinal3 X2 (k6_ordinal3 X1 X2)) = X1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_hidden X1 k4_ordinal1 -> False) -> (v1_xboole_0 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 (k11_ordinal2 X1 X2) -> False)
  -> (forall X2 X1, (r2_hidden X1 k4_ordinal1 -> False) -> (v1_xboole_0 (k11_ordinal2 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 (k11_ordinal2 X2 X1) -> False)
  -> (forall X1 X2 X3, ((k11_ordinal2 (k11_ordinal2 X1 X2) X3) = (k11_ordinal2 X1 (k11_ordinal2 X2 X3)) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k11_ordinal2 (esk3_2 X1 X2) (esk4_2 X1 X2)) = X1 -> False) -> (r1_arytm_3 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k11_ordinal2 (esk3_2 X2 X1) (esk5_2 X2 X1)) = X1 -> False) -> (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 (k6_ordinal3 X2 X1)) = X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X1 X2 -> False)
  -> (forall X3 X1 X2, (r2_arytm_3 X1 X2 -> False) -> X1 = (k3_arytm_3 X2 X3) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X3 X1 X2, (r2_arytm_3 X1 X2 -> False) -> X1 = (k3_arytm_3 X3 X2) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1 X2, ((k11_ordinal2 X2 (esk6_2 X2 X1)) = X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_arytm_3 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> (X2 = k1_xboole_0 -> False) -> (k11_ordinal2 X1 X2) = (k11_ordinal2 X3 X2) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (m1_subset_1 (k2_arytm_3 X1 X2) k4_ordinal1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (m1_subset_1 (k3_arytm_3 X1 X2) k4_ordinal1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (esk6_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_arytm_3 X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_arytm_3 X3 X2 -> False) -> X2 = (k11_ordinal2 X3 X1) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (v3_ordinal1 (esk5_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (v3_ordinal1 (esk4_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (v3_ordinal1 (esk3_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 (k6_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k9_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k6_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> ((k6_ordinal3 (k11_ordinal2 X2 X1) X1) = X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k9_ordinal3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k2_arytm_3 X1 X2) = (k2_arytm_3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k3_arytm_3 X1 X2) = (k3_arytm_3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (esk3_2 X1 X2) = np__1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k6_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = np__1 -> False) -> (k11_ordinal2 X1 X2) = np__1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = np__1 -> False) -> (k11_ordinal2 X2 X1) = np__1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_arytm_3 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k3_arytm_3 X1 k1_xboole_0) = X1 -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X1, ((k2_arytm_3 X1 k1_xboole_0) = k1_xboole_0 -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk11_1 X1) -> False)
  -> (forall X1, ((k11_ordinal2 np__1 X1) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 X1 np__1) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (r1_arytm_3 np__1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 k1_xboole_0 X1) = k1_xboole_0 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (k1_xboole_0 = esk1_0 -> k1_xboole_0 = esk2_0 -> False)
  -> (r1_arytm_3 (k6_ordinal3 esk1_0 (k3_arytm_3 esk1_0 esk2_0)) (k6_ordinal3 esk2_0 (k3_arytm_3 esk1_0 esk2_0)) -> False)
  -> (forall X1, v1_subset_1 (esk16_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk14_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xboole_0 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk13_0 -> False) -> False)
  -> ((v1_ordinal1 esk13_0 -> False) -> False)
  -> ((v7_ordinal1 esk19_0 -> False) -> False)
  -> ((v7_ordinal1 esk17_0 -> False) -> False)
  -> ((v7_ordinal1 esk2_0 -> False) -> False)
  -> ((v7_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 esk2_0 -> False) -> False)
  -> ((v3_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> False.
Admitted.
