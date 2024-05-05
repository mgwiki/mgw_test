(** $I sig/MizarPreamble.mgs **)

Theorem t8_arytm_2:
 forall k6_subset_1:set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall a_0_0_arytm_2:set,
 forall esk16_2:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k5_arytm_3:set,
 forall r3_arytm_3:set -> set -> prop,
 forall esk15_2:set -> set -> set,
 forall k7_subset_1:set -> set -> set -> set,
 forall k1_xboole_0:set,
 forall k2_tarski:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k4_ordinal1:set,
 forall r1_arytm_3:set -> set -> prop,
 forall a_0_0_arytm_3:set,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk14_2:set -> set -> set,
 forall esk18_1:set -> set,
 forall esk17_1:set -> set,
 forall esk22_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk19_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk5_1:set -> set,
 forall esk4_1:set -> set,
 forall esk7_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall esk36_1:set -> set,
 forall esk34_1:set -> set,
 forall esk33_0:set,
 forall esk26_0:set,
 forall k1_arytm_2:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall esk30_0:set,
 forall v2_xxreal_0:set -> prop,
 forall esk29_0:set,
 forall esk35_0:set,
 forall esk27_0:set,
 forall o_0_0_xboole_0:set,
 forall esk3_0:set,
 forall esk11_1:set -> set,
 forall esk32_1:set -> set,
 forall esk31_0:set,
 forall esk37_0:set,
 forall v5_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall esk28_1:set -> set,
 forall esk20_1:set -> set,
 forall a_0_2_arytm_2:set,
 forall k11_arytm_3:set,
 forall v3_ordinal1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk38_2:set -> set -> set,
 forall np__1:set,
 forall a_0_1_arytm_3:set,
 forall esk39_2:set -> set -> set,
 forall esk21_2:set -> set -> set,
 forall a_1_0_arytm_2:set -> set,
 forall esk25_2:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall esk13_1:set -> set,
 forall epred1_2:set -> set -> prop,
 forall esk41_2:set -> set -> set,
 forall esk40_2:set -> set -> set,
 forall k8_subset_1:set -> set -> set -> set,
 forall esk24_2:set -> set -> set,
 forall esk23_2:set -> set -> set,
 forall r1_arytm_2:set -> set -> prop,
 forall k2_arytm_2:set,
 forall a_1_1_arytm_2:set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk9_3 X1 X2 X3) X3 -> r2_hidden (esk9_3 X1 X2 X3) X2 -> r2_hidden (esk9_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk10_3 X1 X2 X3) X3 -> r2_hidden (esk10_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk10_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r3_arytm_3 X3 (esk15_2 X1 X2) -> False) -> (r3_arytm_3 (esk16_2 X1 X2) (esk15_2 X1 X2) -> False) -> X1 = X2 -> r2_hidden X3 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r3_arytm_3 X3 (esk15_2 X1 X2) -> False) -> X1 = X2 -> r2_hidden X3 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> r2_hidden (esk16_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r3_arytm_3 X3 (esk15_2 X1 X2) -> False) -> (m1_subset_1 (esk16_2 X1 X2) k5_arytm_3 -> False) -> X1 = X2 -> r2_hidden X3 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X1 X2, r2_hidden X1 (a_1_1_arytm_2 X2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> r1_arytm_2 (esk23_2 X1 X2) (esk24_2 X1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k8_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X5 X2 X1 X3 X4, (r1_arytm_2 X3 X4 -> False) -> (r2_hidden X2 (a_1_1_arytm_2 X5) -> False) -> X1 = X4 -> X1 = X2 -> r2_hidden X3 X5 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X1 k5_arytm_3 -> m1_subset_1 X5 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X2 X1, (r3_arytm_3 (esk40_2 X1 X2) (esk41_2 X1 X2) -> False) -> r1_arytm_2 X2 X1 -> epred1_2 X2 X1 -> r2_hidden X2 k5_arytm_3 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X3 a_0_0_arytm_3 -> False) -> X3 = (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> r1_arytm_3 X1 X2 -> m1_subset_1 X2 k4_ordinal1 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1 X3 X4, (r1_arytm_2 X3 X4 -> False) -> X2 = X4 -> X1 = X3 -> r3_arytm_3 X1 X2 -> epred1_2 X3 X4 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r2_hidden X4 k5_arytm_3 -> r2_hidden X3 k5_arytm_3 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k8_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 (esk13_1 X3) -> False) -> r3_arytm_3 X1 X2 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r2_hidden X3 a_0_0_arytm_2 -> r2_hidden X2 (esk13_1 X3) -> False)
  -> (forall X1 X2, m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 a_0_0_arytm_2 -> r2_hidden X2 (esk13_1 X1) -> r3_arytm_3 (esk14_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3 X4, (r3_arytm_3 X3 X4 -> False) -> X2 = X4 -> X1 = X3 -> r1_arytm_2 X1 X2 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1 X3 X4, (r1_arytm_2 X3 X4 -> False) -> X2 = X4 -> X1 = X3 -> r3_arytm_3 X1 X2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk41_2 X1 X2) k5_arytm_3 -> False) -> r1_arytm_2 X2 X1 -> epred1_2 X2 X1 -> r2_hidden X2 k5_arytm_3 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk40_2 X1 X2) k5_arytm_3 -> False) -> r1_arytm_2 X2 X1 -> epred1_2 X2 X1 -> r2_hidden X2 k5_arytm_3 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk12_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (r1_arytm_2 X1 X3 -> False) -> r1_arytm_2 X2 X3 -> r1_arytm_2 X1 X2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1 X2, (r2_hidden (esk14_2 X1 X2) (esk13_1 X1) -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 a_0_0_arytm_2 -> r2_hidden X2 (esk13_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r1_arytm_2 X2 X1 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> r1_arytm_2 (esk25_2 X1 X2) X1 -> False)
  -> (forall X1 X2, (r1_arytm_2 X1 X2 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> r1_arytm_2 X1 (esk25_2 X2 X1) -> False)
  -> (forall X2 X1, m1_subset_1 X1 k5_arytm_3 -> r2_hidden X2 (a_1_0_arytm_2 X1) -> r3_arytm_3 X1 (esk21_2 X2 X1) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk14_2 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 a_0_0_arytm_2 -> r2_hidden X2 (esk13_1 X1) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk39_2 X3 X2) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk17_1 X1) (esk18_1 X1)) (k1_tarski (esk17_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1 X2, (r2_hidden X2 a_0_1_arytm_3 -> False) -> X2 = (k2_tarski (k2_tarski X1 np__1) (k1_tarski X1)) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (r2_hidden X1 k5_arytm_3 -> False) -> r2_hidden X2 X1 -> r1_arytm_2 X1 X2 -> epred1_2 X1 X2 -> r2_hidden X2 k5_arytm_3 -> False)
  -> (forall X2 X1, ((esk41_2 X1 X2) = X1 -> False) -> r1_arytm_2 X2 X1 -> epred1_2 X2 X1 -> r2_hidden X2 k5_arytm_3 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X2 X1, ((esk40_2 X2 X1) = X1 -> False) -> r1_arytm_2 X1 X2 -> epred1_2 X1 X2 -> r2_hidden X2 k5_arytm_3 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k6_subset_1 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k3_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (r2_hidden (esk23_2 X1 X2) X2 -> False) -> r2_hidden X1 (a_1_1_arytm_2 X2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk24_2 X1 X2) k2_arytm_2 -> False) -> r2_hidden X1 (a_1_1_arytm_2 X2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk23_2 X1 X2) k2_arytm_2 -> False) -> r2_hidden X1 (a_1_1_arytm_2 X2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk22_2 X1 X2) k5_arytm_3 -> False) -> r2_hidden X1 (a_1_1_arytm_2 X2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r2_hidden (esk38_2 X1 X2) X2 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden X1 (k6_subset_1 X2 (k1_tarski X3)) -> False)
  -> (forall X1 X2, (r1_arytm_2 X1 X2 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> r2_hidden X2 esk2_0 -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, (r1_arytm_2 X2 X1 -> False) -> (r2_hidden (esk25_2 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1, (r1_arytm_2 X2 X1 -> False) -> (m1_subset_1 (esk25_2 X1 X2) k2_arytm_2 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1 X2, (r1_arytm_2 X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> r2_hidden X1 X2 -> epred1_2 X1 X2 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (r2_hidden X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> r1_arytm_2 X1 X2 -> epred1_2 X1 X2 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk6_2 X1 X2) = X1 -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (m1_subset_1 (esk21_2 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 (a_1_0_arytm_2 X2) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk19_1 X1) np__1) (k1_tarski (esk19_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X1 X2, ((esk24_2 X1 X2) = (esk22_2 X1 X2) -> False) -> r2_hidden X1 (a_1_1_arytm_2 X2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X2 X1, ((k8_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, X1 = X2 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> (r2_hidden X1 k5_arytm_3 -> False) -> r1_arytm_2 X1 X2 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> (r2_hidden X1 k5_arytm_3 -> False) -> r1_arytm_2 X1 X2 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (r1_arytm_2 X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> (r2_hidden X1 k5_arytm_3 -> False) -> r1_tarski X1 X2 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (r1_arytm_2 X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> (r2_hidden X1 k5_arytm_3 -> False) -> r1_tarski X1 X2 -> epred1_2 X1 X2 -> False)
  -> (forall X1, m1_subset_1 X1 k2_arytm_2 -> r1_arytm_2 X1 (esk5_1 X1) -> r1_arytm_2 (esk4_1 X1) X1 -> False)
  -> (forall X1 X2, (r2_hidden X1 X2 -> False) -> (r1_arytm_2 X2 X1 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> epred1_2 X2 X1 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r2_hidden (esk15_2 X1 X2) X2 -> False) -> X1 = X2 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (m1_subset_1 (esk15_2 X1 X2) k5_arytm_3 -> False) -> X1 = X2 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X2 X3 X1, (r3_arytm_3 X3 X1 -> False) -> (r2_hidden X2 (a_1_0_arytm_2 X3) -> False) -> X1 = X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> (r2_hidden X1 (k6_subset_1 X2 (k1_tarski X3)) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k6_subset_1 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, ((esk22_2 X1 X2) = X1 -> False) -> r2_hidden X1 (a_1_1_arytm_2 X2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (m1_subset_1 (esk38_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r3_arytm_3 X2 X1 -> False) -> (r3_arytm_3 X1 X2 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r1_arytm_2 X2 X1 -> False) -> (r1_arytm_2 X1 X2 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k6_subset_1 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, ((esk21_2 X1 X2) = X1 -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 (a_1_0_arytm_2 X2) -> False)
  -> (forall X2 X1, (r2_hidden (esk39_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k6_subset_1 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk6_2 X1 X2) = X1 -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X1, (r1_arytm_3 (esk17_1 X1) (esk18_1 X1) -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k3_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 k5_arytm_3) -> False) -> r2_hidden X1 a_0_0_arytm_2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = k11_arytm_3 -> False) -> (r2_hidden X2 a_0_2_arytm_2 -> False) -> X2 = (a_1_0_arytm_2 X1) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (r2_hidden (esk5_1 X1) esk2_0 -> False) -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1, (r2_hidden (esk4_1 X1) esk1_0 -> False) -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) k5_arytm_3 -> False) -> r2_hidden X1 a_0_2_arytm_2 -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) k2_arytm_2 -> False) -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1, (m1_subset_1 (esk4_1 X1) k2_arytm_2 -> False) -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (r3_arytm_3 k11_arytm_3 X1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, ((a_1_0_arytm_2 (esk20_1 X1)) = X1 -> False) -> r2_hidden X1 a_0_2_arytm_2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (esk20_1 X1) = k11_arytm_3 -> r2_hidden X1 a_0_2_arytm_2 -> False)
  -> (forall X1, (esk18_1 X1) = k1_xboole_0 -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, ((esk13_1 X1) = X1 -> False) -> r2_hidden X1 a_0_0_arytm_2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk36_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, X1 = k5_arytm_3 -> r2_hidden X1 k2_arytm_2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk28_1 X1) -> False)
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
  -> (forall X1, v1_subset_1 (esk34_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk37_0 -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k1_arytm_2 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k5_arytm_3 -> False)
  -> (v1_xboole_0 k2_arytm_2 -> False)
  -> ((r1_tarski (k7_subset_1 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 a_0_2_arytm_2) k2_arytm_2 -> False) -> False)
  -> (((k8_subset_1 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 k5_arytm_3) = (k1_tarski k11_arytm_3) -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((r1_tarski k2_arytm_2 (k2_xboole_0 k5_arytm_3 a_0_0_arytm_2) -> False) -> False)
  -> (((k2_xboole_0 (k6_subset_1 a_0_0_arytm_3 a_0_1_arytm_3) k4_ordinal1) = k5_arytm_3 -> False) -> False)
  -> (((k6_subset_1 (k2_xboole_0 k5_arytm_3 k1_arytm_2) a_0_2_arytm_2) = k2_arytm_2 -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 k1_arytm_2 (k1_zfmisc_1 (k1_zfmisc_1 k5_arytm_3)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 k2_arytm_2) -> False) -> False)
  -> ((m1_subset_1 esk1_0 (k1_zfmisc_1 k2_arytm_2) -> False) -> False)
  -> (((k6_subset_1 a_0_0_arytm_2 (k1_tarski k5_arytm_3)) = k1_arytm_2 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((r1_tarski k5_arytm_3 k2_arytm_2 -> False) -> False)
  -> ((r2_hidden esk3_0 esk2_0 -> False) -> False)
  -> ((m1_subset_1 esk30_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk26_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk3_0 k2_arytm_2 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k11_arytm_3 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk32_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xboole_0 esk30_0 -> False) -> False)
  -> ((v1_xboole_0 esk29_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk31_0 -> False) -> False)
  -> ((v1_ordinal1 esk31_0 -> False) -> False)
  -> ((v7_ordinal1 esk37_0 -> False) -> False)
  -> ((v7_ordinal1 esk35_0 -> False) -> False)
  -> ((v3_ordinal1 esk31_0 -> False) -> False)
  -> ((v3_ordinal1 esk27_0 -> False) -> False)
  -> ((v3_ordinal1 esk26_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((k11_arytm_3 = k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
