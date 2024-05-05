(** $I sig/MizarPreamble.mgs **)

Theorem t91_arytm_3:
 forall k2_tarski:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk11_2:set -> set -> set,
 forall esk29_1:set -> set,
 forall esk28_1:set -> set,
 forall esk31_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall r3_arytm_3:set -> set -> prop,
 forall a_0_1_arytm_3:set,
 forall esk8_2:set -> set -> set,
 forall k10_ordinal2:set -> set -> set,
 forall k5_ordinal3:set -> set -> set,
 forall v7_ordinal1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk18_1:set -> set,
 forall v5_ordinal1:set -> prop,
 forall esk24_1:set -> set,
 forall esk23_0:set,
 forall esk15_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall esk22_1:set -> set,
 forall esk20_0:set,
 forall k11_arytm_3:set,
 forall esk17_0:set,
 forall esk25_0:set,
 forall esk19_0:set,
 forall esk16_0:set,
 forall v2_xxreal_0:set -> prop,
 forall esk10_1:set -> set,
 forall k6_subset_1:set -> set -> set,
 forall esk21_0:set,
 forall esk27_0:set,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall esk26_1:set -> set,
 forall esk30_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk3_1:set -> set,
 forall v4_ordinal1:set -> prop,
 forall esk2_1:set -> set,
 forall esk1_0:set,
 forall esk14_1:set -> set,
 forall esk5_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk12_1:set -> set,
 forall esk13_1:set -> set,
 forall k11_ordinal2:set -> set -> set,
 forall np__1:set,
 forall v3_ordinal1:set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall r1_ordinal1:set -> set -> prop,
 forall a_0_0_arytm_3:set,
 forall r1_arytm_3:set -> set -> prop,
 forall k4_ordinal1:set,
 forall k1_tarski:set -> set,
 forall k1_xboole_0:set,
 forall k9_arytm_3:set -> set -> set,
 forall k9_ordinal3:set -> set -> set,
 forall k7_arytm_3:set -> set,
 forall k6_arytm_3:set -> set,
 forall k8_ordinal3:set -> set -> set,
 forall k8_arytm_3:set -> set -> set,
 forall k5_arytm_3:set,
 forall m1_subset_1:set -> set -> prop,
     (forall X2 X1, ((k8_arytm_3 (k8_ordinal3 (k9_ordinal3 (k6_arytm_3 X1) (k7_arytm_3 X2)) (k9_ordinal3 (k6_arytm_3 X2) (k7_arytm_3 X1))) (k9_ordinal3 (k7_arytm_3 X1) (k7_arytm_3 X2))) = (k9_arytm_3 X1 X2) -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> (esk9_3 X1 X2 X3) = X1 -> r2_hidden (esk9_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> (esk9_3 X1 X2 X3) = X2 -> r2_hidden (esk9_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> ((esk9_3 X1 X2 X3) = X2 -> False) -> ((esk9_3 X1 X2 X3) = X1 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X3 a_0_0_arytm_3 -> False) -> X3 = (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> r1_arytm_3 X1 X2 -> m1_subset_1 X2 k4_ordinal1 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk11_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk28_1 X1) (esk29_1 X1)) (k1_tarski (esk28_1 X1))) = X1 -> False) -> (r2_hidden X1 k4_ordinal1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X2)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk31_2 X3 X2) -> False)
  -> (forall X2 X5 X4 X1 X3, (X3 = np__1 -> False) -> X2 = (k11_ordinal2 X3 X5) -> X1 = (k11_ordinal2 X3 X4) -> v3_ordinal1 X5 -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X2 X1, ((k9_arytm_3 X2 (esk4_2 X2 X1)) = X1 -> False) -> r3_arytm_3 X2 X1 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk12_1 X1) (esk13_1 X1)) (k1_tarski (esk12_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1 X2, (r2_hidden X2 a_0_1_arytm_3 -> False) -> X2 = (k2_tarski (k2_tarski X1 np__1) (k1_tarski X1)) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk4_2 X1 X2) k5_arytm_3 -> False) -> r3_arytm_3 X1 X2 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X3 X2, (r3_arytm_3 X3 X2 -> False) -> X2 = (k9_arytm_3 X3 X1) -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, ((k11_ordinal2 (esk6_2 X1 X2) (esk7_2 X1 X2)) = X1 -> False) -> (r1_arytm_3 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k11_ordinal2 (esk6_2 X2 X1) (esk8_2 X2 X1)) = X1 -> False) -> (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk5_2 X1 X2) = X1 -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X2)) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk14_1 X1) np__1) (k1_tarski (esk14_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X2 X1 X3, (X2 = (k10_ordinal2 X3 X1) -> False) -> X1 = (k5_ordinal3 X2 X3) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X3 X2 -> False)
  -> (forall X2 X1 X3, (X3 = (k5_ordinal3 X1 X2) -> False) -> X1 = (k10_ordinal2 X2 X3) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X2 X1 -> False)
  -> (forall X1 X2, ((k8_ordinal3 X1 X2) = (k9_arytm_3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 (k9_arytm_3 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1, m1_subset_1 X1 k5_arytm_3 -> r2_hidden X1 esk1_0 -> r3_arytm_3 (esk2_1 X1) X1 -> False)
  -> (forall X2 X1, (r3_arytm_3 X2 X1 -> False) -> (r3_arytm_3 X1 X2 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k9_arytm_3 X1 X2) = (k9_arytm_3 X2 X1) -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (X1 = k4_ordinal1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden k1_xboole_0 X1 -> r1_tarski X1 (esk3_1 X1) -> False)
  -> (forall X1 X2, (m1_subset_1 (k8_arytm_3 X1 X2) k5_arytm_3 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk31_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal1 X3 X2 -> False) -> X1 = (k5_ordinal3 X2 X3) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk5_2 X1 X2) = X1 -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> False)
  -> (forall X1, (r2_hidden X1 k4_ordinal1 -> False) -> (r1_arytm_3 (esk28_1 X1) (esk29_1 X1) -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (r2_hidden (esk2_1 X1) esk1_0 -> False) -> m1_subset_1 X1 k5_arytm_3 -> r2_hidden X1 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk2_1 X1) k5_arytm_3 -> False) -> m1_subset_1 X1 k5_arytm_3 -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (v3_ordinal1 (esk8_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (v3_ordinal1 (esk7_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (v3_ordinal1 (esk6_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 (k5_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k5_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k9_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k8_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k8_ordinal3 X1 X2) = (k10_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k9_ordinal3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k8_ordinal3 X1 X2) = (k8_ordinal3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1, (X1 = k4_ordinal1 -> False) -> (r2_hidden k1_xboole_0 (esk3_1 X1) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden k1_xboole_0 X1 -> False)
  -> (forall X1 X2, X2 = (k2_xboole_0 X1 (k1_tarski X1)) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> False)
  -> (forall X1 X3 X2, (X1 = (k5_ordinal3 X2 X3) -> False) -> (r1_ordinal1 X3 X2 -> False) -> X1 = k1_xboole_0 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, (r2_hidden X1 k4_ordinal1 -> False) -> (m1_subset_1 (esk29_1 X1) k4_ordinal1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (r2_hidden X1 k4_ordinal1 -> False) -> (m1_subset_1 (esk28_1 X1) k4_ordinal1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r1_tarski X2 X1 -> False) -> X2 = k4_ordinal1 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden k1_xboole_0 X1 -> False)
  -> (forall X1 X2, (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_arytm_3 X1 X2 -> False) -> (esk6_2 X1 X2) = np__1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k2_xboole_0 (esk30_1 X1) (k1_tarski (esk30_1 X1))) = X1 -> False) -> (v4_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> (X1 = X3 -> False) -> X2 = (k2_tarski X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (r1_arytm_3 (esk12_1 X1) (esk13_1 X1) -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (X1 = k4_ordinal1 -> False) -> (v4_ordinal1 (esk3_1 X1) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden k1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k4_ordinal1 -> False) -> (v3_ordinal1 (esk3_1 X1) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden k1_xboole_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, r2_hidden X1 X2 -> r1_tarski X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k5_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X2 X4) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X4 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (r2_hidden X1 k4_ordinal1 -> False) -> (esk29_1 X1) = np__1 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (r2_hidden X1 k4_ordinal1 -> False) -> (esk29_1 X1) = k1_xboole_0 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (k7_arytm_3 X1) k4_ordinal1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (k6_arytm_3 X1) k4_ordinal1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (X1 = np__1 -> False) -> v3_ordinal1 X1 -> r1_arytm_3 k1_xboole_0 X1 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (esk13_1 X1) = k1_xboole_0 -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> r2_hidden X1 k4_ordinal1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v3_ordinal1 (esk30_1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden k1_xboole_0 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, ((k11_ordinal2 np__1 X1) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 X1 np__1) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (r2_hidden X1 k4_ordinal1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (r2_hidden k1_xboole_0 X1 -> False) -> X1 = k4_ordinal1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> X1 = k4_ordinal1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> X1 = k4_ordinal1 -> False)
  -> (forall X1, v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk24_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k5_arytm_3 -> False)
  -> (forall X1, (r2_hidden X1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (((k2_xboole_0 (k6_subset_1 a_0_0_arytm_3 a_0_1_arytm_3) k4_ordinal1) = k5_arytm_3 -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk1_0 (k1_zfmisc_1 k5_arytm_3) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((r1_tarski k4_ordinal1 k5_arytm_3 -> False) -> False)
  -> ((r2_hidden esk1_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk20_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk15_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 k11_arytm_3 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk22_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v4_ordinal1 esk17_0 -> False) -> False)
  -> ((v2_ordinal1 esk21_0 -> False) -> False)
  -> ((v2_ordinal1 esk17_0 -> False) -> False)
  -> ((v1_ordinal1 esk21_0 -> False) -> False)
  -> ((v1_ordinal1 esk17_0 -> False) -> False)
  -> ((v7_ordinal1 esk27_0 -> False) -> False)
  -> ((v7_ordinal1 esk25_0 -> False) -> False)
  -> ((v3_ordinal1 esk21_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v3_ordinal1 esk15_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 esk19_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((k11_arytm_3 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
