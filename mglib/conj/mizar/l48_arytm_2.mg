(** $I sig/MizarPreamble.mgs **)

Theorem l48_arytm_2:
 forall k2_xboole_0:set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk29_3:set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall a_0_0_arytm_2:set,
 forall esk11_2:set -> set -> set,
 forall k5_arytm_3:set,
 forall r3_arytm_3:set -> set -> prop,
 forall esk10_2:set -> set -> set,
 forall k1_xboole_0:set,
 forall k2_tarski:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k4_ordinal1:set,
 forall r1_arytm_3:set -> set -> prop,
 forall a_0_0_arytm_3:set,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk8_1:set -> set,
 forall k2_arytm_2:set,
 forall esk7_2:set -> set -> set,
 forall esk13_1:set -> set,
 forall esk12_1:set -> set,
 forall esk3_2:set -> set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall v1_subset_1:set -> set -> prop,
 forall v3_ordinal1:set -> prop,
 forall k11_arytm_3:set,
 forall a_0_2_arytm_2:set,
 forall esk15_1:set -> set,
 forall v7_ordinal1:set -> prop,
 forall esk27_1:set -> set,
 forall esk25_1:set -> set,
 forall esk28_0:set,
 forall esk22_0:set,
 forall v2_xxreal_0:set -> prop,
 forall esk20_0:set,
 forall esk26_0:set,
 forall esk18_0:set,
 forall o_0_0_xboole_0:set,
 forall esk21_0:set,
 forall esk6_1:set -> set,
 forall esk23_1:set -> set,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall k1_arytm_2:set,
 forall esk17_0:set,
 forall esk24_0:set,
 forall v5_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall esk19_1:set -> set,
 forall v6_ordinal1:set -> prop,
 forall esk31_2:set -> set -> set,
 forall esk14_1:set -> set,
 forall np__1:set,
 forall a_0_1_arytm_3:set,
 forall esk30_2:set -> set -> set,
 forall esk16_2:set -> set -> set,
 forall a_1_0_arytm_2:set -> set,
 forall esk32_2:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall r1_arytm_2:set -> set -> prop,
 forall epred1_2:set -> set -> prop,
 forall esk34_2:set -> set -> set,
 forall esk33_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall k6_subset_1:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> r2_hidden (esk4_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> r2_hidden (esk4_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk5_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X2 X3, (r1_tarski X2 X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r2_hidden (esk29_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X2 X3, (r1_tarski X2 X3 -> False) -> (r2_hidden (esk29_3 X1 X2 X3) X2 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2 X3, (r1_tarski X2 X3 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r3_arytm_3 X3 (esk10_2 X1 X2) -> False) -> (r3_arytm_3 (esk11_2 X1 X2) (esk10_2 X1 X2) -> False) -> X1 = X2 -> r2_hidden X3 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r3_arytm_3 X3 (esk10_2 X1 X2) -> False) -> X1 = X2 -> r2_hidden X3 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> r2_hidden (esk11_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r3_arytm_3 X3 (esk10_2 X1 X2) -> False) -> (m1_subset_1 (esk11_2 X1 X2) k5_arytm_3 -> False) -> X1 = X2 -> r2_hidden X3 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X2 X1, (r3_arytm_3 (esk33_2 X1 X2) (esk34_2 X1 X2) -> False) -> r1_arytm_2 X2 X1 -> epred1_2 X2 X1 -> r2_hidden X2 k5_arytm_3 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X3 a_0_0_arytm_3 -> False) -> X3 = (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> r1_arytm_3 X1 X2 -> m1_subset_1 X2 k4_ordinal1 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1 X3 X4, (r1_arytm_2 X3 X4 -> False) -> X2 = X4 -> X1 = X3 -> r3_arytm_3 X1 X2 -> epred1_2 X3 X4 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r2_hidden X4 k5_arytm_3 -> r2_hidden X3 k5_arytm_3 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 (esk8_1 X3) -> False) -> r3_arytm_3 X1 X2 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r2_hidden X3 a_0_0_arytm_2 -> r2_hidden X2 (esk8_1 X3) -> False)
  -> (forall X1 X2, m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 a_0_0_arytm_2 -> r2_hidden X2 (esk8_1 X1) -> r3_arytm_3 (esk9_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3 X4, (r3_arytm_3 X3 X4 -> False) -> X2 = X4 -> X1 = X3 -> r1_arytm_2 X1 X2 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1 X3 X4, (r1_arytm_2 X3 X4 -> False) -> X2 = X4 -> X1 = X3 -> r3_arytm_3 X1 X2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk34_2 X1 X2) k5_arytm_3 -> False) -> r1_arytm_2 X2 X1 -> epred1_2 X2 X1 -> r2_hidden X2 k5_arytm_3 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk33_2 X1 X2) k5_arytm_3 -> False) -> r1_arytm_2 X2 X1 -> epred1_2 X2 X1 -> r2_hidden X2 k5_arytm_3 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk7_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r2_hidden (esk9_2 X1 X2) (esk8_1 X1) -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 a_0_0_arytm_2 -> r2_hidden X2 (esk8_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r3_arytm_3 X2 X1 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 (esk32_2 X1 X2) X1 -> False)
  -> (forall X1 X2, (r3_arytm_3 X1 X2 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 X1 (esk32_2 X2 X1) -> False)
  -> (forall X2 X1, m1_subset_1 X1 k5_arytm_3 -> r2_hidden X2 (a_1_0_arytm_2 X1) -> r3_arytm_3 X1 (esk16_2 X2 X1) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk9_2 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 a_0_0_arytm_2 -> r2_hidden X2 (esk8_1 X1) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk30_2 X3 X2) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk12_1 X1) (esk13_1 X1)) (k1_tarski (esk12_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1 X2, (r2_hidden X2 a_0_1_arytm_3 -> False) -> X2 = (k2_tarski (k2_tarski X1 np__1) (k1_tarski X1)) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (r2_hidden X1 k5_arytm_3 -> False) -> r1_arytm_2 X1 X2 -> r2_hidden X2 X1 -> epred1_2 X1 X2 -> r2_hidden X2 k5_arytm_3 -> False)
  -> (forall X2 X1, ((esk34_2 X1 X2) = X1 -> False) -> r1_arytm_2 X2 X1 -> epred1_2 X2 X1 -> r2_hidden X2 k5_arytm_3 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X2 X1, ((esk33_2 X2 X1) = X1 -> False) -> r1_arytm_2 X1 X2 -> epred1_2 X1 X2 -> r2_hidden X2 k5_arytm_3 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r3_arytm_3 X2 X1 -> False) -> (m1_subset_1 (esk32_2 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (r2_hidden X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> r1_arytm_2 X1 X2 -> epred1_2 X1 X2 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (r1_arytm_2 X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> r2_hidden X1 X2 -> epred1_2 X1 X2 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (m1_subset_1 (esk16_2 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 (a_1_0_arytm_2 X2) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk14_1 X1) np__1) (k1_tarski (esk14_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> (r2_hidden X1 k5_arytm_3 -> False) -> r1_arytm_2 X1 X2 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> (r2_hidden X1 k5_arytm_3 -> False) -> r1_arytm_2 X1 X2 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (r1_arytm_2 X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> (r2_hidden X1 k5_arytm_3 -> False) -> r1_tarski X1 X2 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (r1_arytm_2 X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> (r2_hidden X1 k5_arytm_3 -> False) -> r1_tarski X1 X2 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (r1_arytm_2 X2 X1 -> False) -> (r2_hidden X1 X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> epred1_2 X2 X1 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> X1 = X2 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X2 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (m1_subset_1 (esk10_2 X1 X2) k5_arytm_3 -> False) -> X1 = X2 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X2 X3 X1, (r3_arytm_3 X3 X1 -> False) -> (r2_hidden X2 (a_1_0_arytm_2 X3) -> False) -> X1 = X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk3_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k6_subset_1 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden (esk31_2 X1 X2) X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (m1_subset_1 (esk31_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r3_arytm_3 X2 X1 -> False) -> (r3_arytm_3 X1 X2 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r1_arytm_2 X2 X1 -> False) -> (r1_arytm_2 X1 X2 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k6_subset_1 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, ((esk16_2 X1 X2) = X1 -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 (a_1_0_arytm_2 X2) -> False)
  -> (forall X1, (r1_arytm_2 X1 esk1_0 -> False) -> (r1_arytm_2 esk2_0 X1 -> False) -> m1_subset_1 X1 k2_arytm_2 -> r2_hidden X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r2_hidden (esk30_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k6_subset_1 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk3_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (r1_arytm_3 (esk12_1 X1) (esk13_1 X1) -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) (k1_zfmisc_1 k5_arytm_3) -> False) -> r2_hidden X1 a_0_0_arytm_2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = k11_arytm_3 -> False) -> (r2_hidden X2 a_0_2_arytm_2 -> False) -> X2 = (a_1_0_arytm_2 X1) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) k5_arytm_3 -> False) -> r2_hidden X1 a_0_2_arytm_2 -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (r3_arytm_3 k11_arytm_3 X1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, ((a_1_0_arytm_2 (esk15_1 X1)) = X1 -> False) -> r2_hidden X1 a_0_2_arytm_2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (esk15_1 X1) = k11_arytm_3 -> r2_hidden X1 a_0_2_arytm_2 -> False)
  -> (forall X1, (esk13_1 X1) = k1_xboole_0 -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, ((esk8_1 X1) = X1 -> False) -> r2_hidden X1 a_0_0_arytm_2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
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
  -> (forall X1, v1_subset_1 (esk25_1 X1) X1 -> False)
  -> (r1_arytm_2 esk2_0 esk1_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k1_arytm_2 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k5_arytm_3 -> False)
  -> (v1_xboole_0 k2_arytm_2 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((r1_tarski k2_arytm_2 (k2_xboole_0 k5_arytm_3 a_0_0_arytm_2) -> False) -> False)
  -> (((k2_xboole_0 (k6_subset_1 a_0_0_arytm_3 a_0_1_arytm_3) k4_ordinal1) = k5_arytm_3 -> False) -> False)
  -> (((k6_subset_1 (k2_xboole_0 k5_arytm_3 k1_arytm_2) a_0_2_arytm_2) = k2_arytm_2 -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 k1_arytm_2 (k1_zfmisc_1 (k1_zfmisc_1 k5_arytm_3)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (((k6_subset_1 a_0_0_arytm_2 (k1_tarski k5_arytm_3)) = k1_arytm_2 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((r1_tarski k5_arytm_3 k2_arytm_2 -> False) -> False)
  -> ((m1_subset_1 esk21_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk17_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk2_0 k2_arytm_2 -> False) -> False)
  -> ((m1_subset_1 esk1_0 k2_arytm_2 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k11_arytm_3 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk23_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk22_0 -> False) -> False)
  -> ((v1_ordinal1 esk22_0 -> False) -> False)
  -> ((v7_ordinal1 esk28_0 -> False) -> False)
  -> ((v7_ordinal1 esk26_0 -> False) -> False)
  -> ((v3_ordinal1 esk22_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((k11_arytm_3 = k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
