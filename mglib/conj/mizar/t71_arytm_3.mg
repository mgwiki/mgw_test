(** $I sig/MizarPreamble.mgs **)

Theorem t71_arytm_3:
 forall k3_arytm_3:set -> set -> set,
 forall k4_ordinal1:set,
 forall esk4_3:set -> set -> set -> set,
 forall r2_arytm_3:set -> set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall r1_arytm_3:set -> set -> prop,
 forall a_0_0_arytm_3:set,
 forall esk7_2:set -> set -> set,
 forall esk23_2:set -> set -> set,
 forall a_0_1_arytm_3:set,
 forall np__1:set,
 forall v1_subset_1:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk13_1:set -> set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall esk2_0:set,
 forall esk18_0:set,
 forall esk11_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall esk1_0:set,
 forall esk6_1:set -> set,
 forall k11_arytm_3:set,
 forall v2_xxreal_0:set -> prop,
 forall esk14_0:set,
 forall esk12_0:set,
 forall esk20_0:set,
 forall esk15_0:set,
 forall esk17_1:set -> set,
 forall k6_subset_1:set -> set -> set,
 forall esk16_0:set,
 forall esk22_0:set,
 forall esk19_1:set -> set,
 forall esk21_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall k10_ordinal2:set -> set -> set,
 forall esk3_2:set -> set -> set,
 forall esk10_1:set -> set,
 forall esk8_1:set -> set,
 forall esk9_1:set -> set,
 forall k11_ordinal2:set -> set -> set,
 forall k5_ordinal3:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k2_tarski:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k9_arytm_3:set -> set -> set,
 forall k9_ordinal3:set -> set -> set,
 forall k7_arytm_3:set -> set,
 forall k6_arytm_3:set -> set,
 forall k8_ordinal3:set -> set -> set,
 forall k8_arytm_3:set -> set -> set,
 forall k5_arytm_3:set,
 forall m1_subset_1:set -> set -> prop,
     (forall X2 X1, ((k8_arytm_3 (k8_ordinal3 (k9_ordinal3 (k6_arytm_3 X1) (k7_arytm_3 X2)) (k9_ordinal3 (k6_arytm_3 X2) (k7_arytm_3 X1))) (k9_ordinal3 (k7_arytm_3 X1) (k7_arytm_3 X2))) = (k9_arytm_3 X1 X2) -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_arytm_3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X2 -> r2_arytm_3 X3 X1 -> m1_subset_1 X3 k4_ordinal1 -> r2_arytm_3 (esk4_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_arytm_3 X1 X2) -> False) -> (r2_arytm_3 (esk4_3 X1 X2 X3) X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X2 -> r2_arytm_3 X3 X1 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_arytm_3 X1 X2) -> False) -> (r2_arytm_3 (esk4_3 X1 X2 X3) X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X2 -> r2_arytm_3 X3 X1 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_arytm_3 X1 X2) -> False) -> (v7_ordinal1 (esk4_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X2 -> r2_arytm_3 X3 X1 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_arytm_3 X1 X2) -> False) -> (v3_ordinal1 (esk4_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X2 -> r2_arytm_3 X3 X1 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X2 X1, ((k2_tarski (k2_tarski (esk5_2 X1 X2) X2) (k1_tarski (esk5_2 X1 X2))) = X1 -> False) -> (r2_hidden X1 k4_ordinal1 -> False) -> X2 = (k7_arytm_3 X1) -> m1_subset_1 X2 k4_ordinal1 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X3 a_0_0_arytm_3 -> False) -> X3 = (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> r1_arytm_3 X1 X2 -> m1_subset_1 X2 k4_ordinal1 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (X3 = (k7_arytm_3 X2) -> False) -> (r2_hidden X2 k4_ordinal1 -> False) -> X2 = (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> m1_subset_1 X3 k4_ordinal1 -> m1_subset_1 X2 k5_arytm_3 -> False)
  -> (forall X3 X2 X1 X4, (r2_arytm_3 X1 X4 -> False) -> X4 = (k3_arytm_3 X2 X3) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X1 X3 -> r2_arytm_3 X1 X2 -> m1_subset_1 X4 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X4 X3, (X3 = k1_xboole_0 -> False) -> (X2 = k1_xboole_0 -> False) -> ((k8_arytm_3 X1 X3) = (k8_arytm_3 X4 X2) -> False) -> (k9_ordinal3 X1 X2) = (k9_ordinal3 X3 X4) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X4 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X3 X1 X4, (X4 = k1_xboole_0 -> False) -> (X2 = k1_xboole_0 -> False) -> ((k9_ordinal3 X1 X4) = (k9_ordinal3 X2 X3) -> False) -> (k8_arytm_3 X1 X2) = (k8_arytm_3 X3 X4) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X4 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, ((k5_ordinal3 (k11_ordinal2 X1 X2) (k11_ordinal2 X3 X2)) = (k11_ordinal2 (k5_ordinal3 X1 X3) X2) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk7_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk23_2 X3 X2) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk8_1 X1) (esk9_1 X1)) (k1_tarski (esk8_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1 X2, (r2_hidden X2 a_0_1_arytm_3 -> False) -> X2 = (k2_tarski (k2_tarski X1 np__1) (k1_tarski X1)) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (r2_hidden X1 k4_ordinal1 -> False) -> (v7_ordinal1 (esk5_2 X1 X2) -> False) -> X2 = (k7_arytm_3 X1) -> m1_subset_1 X2 k4_ordinal1 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r2_hidden X1 k4_ordinal1 -> False) -> (v3_ordinal1 (esk5_2 X1 X2) -> False) -> X2 = (k7_arytm_3 X1) -> m1_subset_1 X2 k4_ordinal1 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk10_1 X1) np__1) (k1_tarski (esk10_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X3 X1 X2, (r2_arytm_3 X1 X2 -> False) -> X1 = (k3_arytm_3 X2 X3) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X3 X1 X2, (r2_arytm_3 X1 X2 -> False) -> X1 = (k3_arytm_3 X3 X2) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k9_arytm_3 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X2, ((k11_ordinal2 X2 (esk3_2 X2 X1)) = X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_arytm_3 X2 X1 -> False)
  -> (forall X2 X1, (X1 = np__1 -> False) -> X1 = (k7_arytm_3 X2) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k4_ordinal1 -> r2_hidden X2 k4_ordinal1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k9_arytm_3 X1 X2) = (k9_arytm_3 X2 X1) -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (X1 = (k7_arytm_3 X2) -> False) -> X1 = np__1 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k4_ordinal1 -> r2_hidden X2 k4_ordinal1 -> False)
  -> (forall X1 X2, (m1_subset_1 (k8_arytm_3 X1 X2) k5_arytm_3 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (m1_subset_1 (k3_arytm_3 X1 X2) k4_ordinal1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (esk3_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_arytm_3 X1 X2 -> False)
  -> (forall X1 X2, (r1_arytm_3 X1 X2 -> False) -> (k3_arytm_3 X1 X2) = np__1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k3_arytm_3 X1 X2) = np__1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk23_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_arytm_3 X3 X2 -> False) -> X2 = (k11_ordinal2 X3 X1) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 (k5_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k5_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k9_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k8_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, ((k8_ordinal3 X1 X2) = (k10_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k9_ordinal3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k8_ordinal3 X1 X2) = (k8_ordinal3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k3_arytm_3 X1 X2) = (k3_arytm_3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k5_ordinal3 (k10_ordinal2 X1 X2) X1) = X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X1, ((k8_arytm_3 (k6_arytm_3 X1) (k7_arytm_3 X1)) = X1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (r1_arytm_3 (esk8_1 X1) (esk9_1 X1) -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (r1_arytm_3 (k6_arytm_3 X1) (k7_arytm_3 X1) -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k5_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k8_arytm_3 X1 np__1) = X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, ((k8_arytm_3 k1_xboole_0 X1) = k1_xboole_0 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (X1 = k1_xboole_0 -> False) -> (k11_ordinal2 X1 X2) = k1_xboole_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (k7_arytm_3 X1) k4_ordinal1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (k6_arytm_3 X1) k4_ordinal1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_arytm_3 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (esk9_1 X1) = k1_xboole_0 -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (k7_arytm_3 X1) = k1_xboole_0 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, ((k11_ordinal2 np__1 X1) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 X1 np__1) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk19_1 X1) X1 -> False)
  -> (r2_hidden esk2_0 k4_ordinal1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k5_arytm_3 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((r2_hidden (k9_arytm_3 esk1_0 esk2_0) k4_ordinal1 -> False) -> False)
  -> (((k2_xboole_0 (k6_subset_1 a_0_0_arytm_3 a_0_1_arytm_3) k4_ordinal1) = k5_arytm_3 -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((r2_hidden esk1_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 esk15_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk11_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk2_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk1_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 k11_arytm_3 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk17_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xboole_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk16_0 -> False) -> False)
  -> ((v1_ordinal1 esk16_0 -> False) -> False)
  -> ((v7_ordinal1 esk22_0 -> False) -> False)
  -> ((v7_ordinal1 esk20_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((k1_xboole_0 = k11_arytm_3 -> False) -> False)
  -> False.
Admitted.