(** $I sig/MizarPreamble.mgs **)

Theorem t21_arytm_2:
 forall k6_arytm_2:set -> set -> set,
 forall esk3_2:set -> set -> set,
 forall k2_arytm_2:set,
 forall k3_arytm_2:set -> set,
 forall k8_arytm_3:set -> set -> set,
 forall k6_arytm_3:set -> set,
 forall k7_arytm_3:set -> set,
 forall k9_ordinal3:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall k11_arytm_3:set,
 forall esk11_1:set -> set,
 forall esk10_1:set -> set,
 forall esk12_1:set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall k2_xboole_0:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall a_0_2_arytm_2:set,
 forall esk13_1:set -> set,
 forall esk20_1:set -> set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall esk29_0:set,
 forall esk23_0:set,
 forall k6_subset_1:set -> set -> set,
 forall esk24_1:set -> set,
 forall esk4_1:set -> set,
 forall v2_xxreal_0:set -> prop,
 forall esk21_0:set,
 forall esk27_0:set,
 forall esk19_0:set,
 forall o_0_0_xboole_0:set,
 forall esk22_0:set,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall esk18_0:set,
 forall esk25_0:set,
 forall esk26_1:set -> set,
 forall esk28_1:set -> set,
 forall v6_ordinal1:set -> prop,
 forall k11_ordinal2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall np__1:set,
 forall a_0_1_arytm_3:set,
 forall esk30_2:set -> set -> set,
 forall k8_arytm_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk32_2:set -> set -> set,
 forall esk6_1:set -> set,
 forall esk36_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall a_0_0_arytm_3:set,
 forall r1_arytm_3:set -> set -> prop,
 forall k4_ordinal1:set,
 forall k1_tarski:set -> set,
 forall k2_tarski:set -> set -> set,
 forall k1_xboole_0:set,
 forall a_1_0_arytm_2:set -> set,
 forall esk17_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall a_0_0_arytm_2:set,
 forall esk31_3:set -> set -> set -> set,
 forall a_2_2_arytm_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_arytm_2:set,
 forall k1_zfmisc_1:set -> set,
 forall k10_arytm_3:set -> set -> set,
 forall esk15_3:set -> set -> set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall esk34_2:set -> set -> set,
 forall esk33_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k5_arytm_3:set,
 forall m1_subset_1:set -> set -> prop,
 forall r3_arytm_3:set -> set -> prop,
 forall epred1_2:set -> set -> prop,
 forall esk35_3:set -> set -> set -> set,
 forall k4_arytm_2:set -> set,
     (forall X4 X3 X2 X1, (X2 = (k4_arytm_2 X1) -> False) -> (r2_hidden (esk33_3 X1 X2 X4) X1 -> False) -> (r2_hidden (esk35_3 X1 X2 X3) X1 -> False) -> X2 = X3 -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> r3_arytm_3 X4 (esk33_3 X1 X2 X4) -> r3_arytm_3 X3 (esk35_3 X1 X2 X3) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k4_arytm_2 X1) -> False) -> (r3_arytm_3 X3 (esk35_3 X1 X2 X3) -> False) -> (r2_hidden (esk33_3 X1 X2 X4) X1 -> False) -> X2 = X3 -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> r3_arytm_3 X4 (esk33_3 X1 X2 X4) -> r2_hidden (esk35_3 X1 X2 X3) X1 -> False)
  -> (forall X4 X3 X2 X1, (X2 = (k4_arytm_2 X1) -> False) -> (r3_arytm_3 X4 (esk33_3 X1 X2 X4) -> False) -> (r2_hidden (esk35_3 X1 X2 X3) X1 -> False) -> X2 = X3 -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> r3_arytm_3 X3 (esk35_3 X1 X2 X3) -> r2_hidden (esk33_3 X1 X2 X4) X1 -> False)
  -> (forall X4 X3 X2 X1, (X2 = (k4_arytm_2 X1) -> False) -> (r3_arytm_3 X4 (esk33_3 X1 X2 X4) -> False) -> (r3_arytm_3 X3 (esk35_3 X1 X2 X3) -> False) -> X2 = X3 -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> r2_hidden (esk33_3 X1 X2 X4) X1 -> r2_hidden (esk35_3 X1 X2 X3) X1 -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k4_arytm_2 X1) -> False) -> (r2_hidden (esk35_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X4) k5_arytm_3 -> False) -> X2 = X3 -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> r3_arytm_3 X3 (esk35_3 X1 X2 X3) -> False)
  -> (forall X4 X3 X2 X1, (X2 = (k4_arytm_2 X1) -> False) -> (r2_hidden (esk33_3 X1 X2 X4) X1 -> False) -> (m1_subset_1 (esk35_3 X1 X2 X3) k5_arytm_3 -> False) -> X2 = X3 -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> r3_arytm_3 X4 (esk33_3 X1 X2 X4) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k4_arytm_2 X1) -> False) -> (r3_arytm_3 X3 (esk35_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk33_3 X1 X2 X4) k5_arytm_3 -> False) -> X2 = X3 -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> r2_hidden (esk35_3 X1 X2 X3) X1 -> False)
  -> (forall X4 X3 X2 X1, (X2 = (k4_arytm_2 X1) -> False) -> (r3_arytm_3 X4 (esk33_3 X1 X2 X4) -> False) -> (m1_subset_1 (esk35_3 X1 X2 X3) k5_arytm_3 -> False) -> X2 = X3 -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> r2_hidden (esk33_3 X1 X2 X4) X1 -> False)
  -> (forall X1 X3 X4 X2, (r2_hidden (esk33_3 X2 X3 X4) X2 -> False) -> X3 = (k4_arytm_2 X2) -> r2_hidden X1 X2 -> epred1_2 X3 X2 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 (esk34_2 X2 X3) X1 -> r3_arytm_3 X4 (esk33_3 X2 X3 X4) -> False)
  -> (forall X1 X3 X2 X4, (r3_arytm_3 X4 (esk33_3 X2 X3 X4) -> False) -> X3 = (k4_arytm_2 X2) -> r2_hidden X1 X2 -> epred1_2 X3 X2 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 (esk34_2 X2 X3) X1 -> r2_hidden (esk33_3 X2 X3 X4) X2 -> False)
  -> (forall X1 X3 X2, ((k10_arytm_3 (esk15_3 X1 X2 X3) (esk16_3 X1 X2 X3)) = X1 -> False) -> r2_hidden X1 (a_2_2_arytm_2 X2 X3) -> m2_subset_1 X3 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> m2_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X2 X4 X3 X1, (r2_hidden X3 X1 -> False) -> (r3_arytm_3 (esk34_2 X1 X2) X3 -> False) -> (r2_hidden (esk33_3 X1 X2 X4) X1 -> False) -> X2 = (k4_arytm_2 X1) -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> r3_arytm_3 X4 (esk33_3 X1 X2 X4) -> False)
  -> (forall X2 X4 X3 X1, (r2_hidden X3 X1 -> False) -> (r3_arytm_3 (esk34_2 X1 X2) X3 -> False) -> (r3_arytm_3 X4 (esk33_3 X1 X2 X4) -> False) -> X2 = (k4_arytm_2 X1) -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> r2_hidden (esk33_3 X1 X2 X4) X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk34_2 X1 X2) k5_arytm_3 -> False) -> (r2_hidden (esk33_3 X1 X2 X3) X1 -> False) -> X2 = (k4_arytm_2 X1) -> epred1_2 X2 X1 -> m1_subset_1 X3 k5_arytm_3 -> r3_arytm_3 X3 (esk33_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (r3_arytm_3 X3 (esk33_3 X1 X2 X3) -> False) -> (m1_subset_1 (esk34_2 X1 X2) k5_arytm_3 -> False) -> X2 = (k4_arytm_2 X1) -> epred1_2 X2 X1 -> m1_subset_1 X3 k5_arytm_3 -> r2_hidden (esk33_3 X1 X2 X3) X1 -> False)
  -> (forall X3 X2 X1, ((esk34_2 X2 X1) = X1 -> False) -> (r2_hidden (esk33_3 X2 X1 X3) X2 -> False) -> X1 = (k4_arytm_2 X2) -> epred1_2 X1 X2 -> m1_subset_1 X3 k5_arytm_3 -> r3_arytm_3 X3 (esk33_3 X2 X1 X3) -> False)
  -> (forall X3 X2 X1, ((esk34_2 X2 X1) = X1 -> False) -> (r3_arytm_3 X3 (esk33_3 X2 X1 X3) -> False) -> X1 = (k4_arytm_2 X2) -> epred1_2 X1 X2 -> m1_subset_1 X3 k5_arytm_3 -> r2_hidden (esk33_3 X2 X1 X3) X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden (esk16_3 X1 X2 X3) X3 -> False) -> r2_hidden X1 (a_2_2_arytm_2 X2 X3) -> m2_subset_1 X3 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> m2_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X1 X3 X2, (r2_hidden (esk15_3 X1 X2 X3) X2 -> False) -> r2_hidden X1 (a_2_2_arytm_2 X2 X3) -> m2_subset_1 X3 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> m2_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (esk16_3 X1 X2 X3) k5_arytm_3 -> False) -> r2_hidden X1 (a_2_2_arytm_2 X2 X3) -> m2_subset_1 X3 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> m2_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (esk15_3 X1 X2 X3) k5_arytm_3 -> False) -> r2_hidden X1 (a_2_2_arytm_2 X2 X3) -> m2_subset_1 X3 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> m2_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X2 X1 X4 X5 X3, (r2_hidden X3 (a_2_2_arytm_2 X4 X5) -> False) -> X3 = (k10_arytm_3 X1 X2) -> r2_hidden X2 X5 -> r2_hidden X1 X4 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> m2_subset_1 X5 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> m2_subset_1 X4 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X4 X3 X2 X1, (X2 = (k4_arytm_2 X1) -> False) -> (m1_subset_1 (esk33_3 X1 X2 X4) k5_arytm_3 -> False) -> (m1_subset_1 (esk35_3 X1 X2 X3) k5_arytm_3 -> False) -> X2 = X3 -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> False)
  -> (forall X1 X2 X3 X4, (m1_subset_1 (esk33_3 X2 X3 X4) k5_arytm_3 -> False) -> X3 = (k4_arytm_2 X2) -> r2_hidden X1 X2 -> epred1_2 X3 X2 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 (esk34_2 X2 X3) X1 -> False)
  -> (forall X2 X1 X3, ((k10_arytm_3 X2 (esk31_3 X1 X2 X3)) = X1 -> False) -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 X1 (k10_arytm_3 X2 X3) -> False)
  -> (forall X2 X4 X3 X1, (r2_hidden X3 X1 -> False) -> (r3_arytm_3 (esk34_2 X1 X2) X3 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X4) k5_arytm_3 -> False) -> X2 = (k4_arytm_2 X1) -> epred1_2 X2 X1 -> m1_subset_1 X4 k5_arytm_3 -> m1_subset_1 X3 k5_arytm_3 -> False)
  -> (forall X2 X1 X3, (r3_arytm_3 (esk31_3 X1 X2 X3) X3 -> False) -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 X1 (k10_arytm_3 X2 X3) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk31_3 X1 X2 X3) k5_arytm_3 -> False) -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 X1 (k10_arytm_3 X2 X3) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk34_2 X1 X2) k5_arytm_3 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) k5_arytm_3 -> False) -> X2 = (k4_arytm_2 X1) -> epred1_2 X2 X1 -> m1_subset_1 X3 k5_arytm_3 -> False)
  -> (forall X2 X1, ((a_2_2_arytm_2 X1 X2) = (k6_arytm_2 X1 X2) -> False) -> m2_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> m2_subset_1 X1 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r3_arytm_3 X3 (esk8_2 X1 X2) -> False) -> (r3_arytm_3 (esk9_2 X1 X2) (esk8_2 X1 X2) -> False) -> X1 = X2 -> r2_hidden X3 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r3_arytm_3 X3 (esk8_2 X1 X2) -> False) -> X1 = X2 -> r2_hidden X3 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1, ((esk34_2 X2 X1) = X1 -> False) -> (m1_subset_1 (esk33_3 X2 X1 X3) k5_arytm_3 -> False) -> X1 = (k4_arytm_2 X2) -> epred1_2 X1 X2 -> m1_subset_1 X3 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk3_2 X1 X2) k5_arytm_3 -> False) -> X2 = (k3_arytm_2 X1) -> m1_subset_1 X1 k2_arytm_2 -> r2_hidden X1 k5_arytm_3 -> m2_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 X2 (esk17_2 X2 X1) -> r3_arytm_3 X1 (esk17_2 X2 X1) -> False)
  -> (forall X2 X1, ((k8_arytm_3 (k9_ordinal3 (k6_arytm_3 X1) (k6_arytm_3 X2)) (k9_ordinal3 (k7_arytm_3 X1) (k7_arytm_3 X2))) = (k10_arytm_3 X1 X2) -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X2, ((a_1_0_arytm_2 (esk3_2 X2 X1)) = X1 -> False) -> X1 = (k3_arytm_2 X2) -> m1_subset_1 X2 k2_arytm_2 -> r2_hidden X2 k5_arytm_3 -> m2_subset_1 X1 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_arytm_2 X2) -> False) -> X1 = X2 -> X3 = (a_1_0_arytm_2 X1) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k5_arytm_3 -> r2_hidden X2 k5_arytm_3 -> m2_subset_1 X3 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r3_arytm_3 X3 (esk8_2 X1 X2) -> False) -> (m1_subset_1 (esk9_2 X1 X2) k5_arytm_3 -> False) -> X1 = X2 -> r2_hidden X3 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X2 X1, ((esk3_2 X1 X2) = X1 -> False) -> X2 = (k3_arytm_2 X1) -> m1_subset_1 X1 k2_arytm_2 -> r2_hidden X1 k5_arytm_3 -> m2_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X3 a_0_0_arytm_3 -> False) -> X3 = (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> r1_arytm_3 X1 X2 -> m1_subset_1 X2 k4_ordinal1 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X3 X1 X2, (r3_arytm_3 (k10_arytm_3 X1 X3) (k10_arytm_3 X2 X3) -> False) -> r3_arytm_3 X1 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (X1 = X2 -> False) -> X1 = (k4_arytm_2 X2) -> r2_hidden X3 X2 -> epred1_2 X1 X2 -> m1_subset_1 X3 k5_arytm_3 -> r3_arytm_3 (esk36_2 X2 X1) X3 -> False)
  -> (forall X3 X1 X2, (X1 = (k4_arytm_2 X2) -> False) -> X1 = X2 -> r2_hidden X3 X2 -> epred1_2 X1 X2 -> m1_subset_1 X3 k5_arytm_3 -> r3_arytm_3 (esk36_2 X2 X1) X3 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 (esk6_1 X3) -> False) -> r3_arytm_3 X1 X2 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r2_hidden X3 a_0_0_arytm_2 -> r2_hidden X2 (esk6_1 X3) -> False)
  -> (forall X1 X2, m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 a_0_0_arytm_2 -> r2_hidden X2 (esk6_1 X1) -> r3_arytm_3 (esk7_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> X1 = (k3_arytm_2 X2) -> m1_subset_1 X2 k2_arytm_2 -> m2_subset_1 X1 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X1 X2, (X1 = (k3_arytm_2 X2) -> False) -> (r2_hidden X2 k5_arytm_3 -> False) -> X1 = X2 -> m1_subset_1 X2 k2_arytm_2 -> m2_subset_1 X1 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> (r3_arytm_3 X2 (esk17_2 X1 X2) -> False) -> (r3_arytm_3 X1 (esk17_2 X1 X2) -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m2_subset_1 X1 (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False)
  -> (forall X2 X1, (m2_subset_1 (k6_arytm_2 X1 X2) (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False) -> m1_subset_1 X2 k1_arytm_2 -> m1_subset_1 X1 k1_arytm_2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk5_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, (r3_arytm_3 X1 X2 -> False) -> r3_arytm_3 X3 X2 -> r3_arytm_3 X1 X3 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X3 X2, (r3_arytm_3 X3 X2 -> False) -> r3_arytm_3 X3 X1 -> r3_arytm_3 X1 X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (r2_hidden (esk7_2 X1 X2) (esk6_1 X1) -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 a_0_0_arytm_2 -> r2_hidden X2 (esk6_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r3_arytm_3 X2 X1 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 (esk32_2 X1 X2) X1 -> False)
  -> (forall X1 X2, (r3_arytm_3 X1 X2 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> r3_arytm_3 X1 (esk32_2 X2 X1) -> False)
  -> (forall X2 X1, m1_subset_1 X1 k5_arytm_3 -> r2_hidden X2 (a_1_0_arytm_2 X1) -> r3_arytm_3 X1 (esk14_2 X2 X1) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk7_2 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 a_0_0_arytm_2 -> r2_hidden X2 (esk6_1 X1) -> False)
  -> (forall X2 X1, ((k4_arytm_2 (k6_arytm_2 (k3_arytm_2 X1) (k3_arytm_2 X2))) = (k8_arytm_2 X1 X2) -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (X1 = k11_arytm_3 -> False) -> (k10_arytm_3 X1 X2) = (k10_arytm_3 X1 X3) -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk30_2 X3 X2) -> False)
  -> (forall X3 X1 X2, (X1 = X2 -> False) -> (r2_hidden X3 X2 -> False) -> (r3_arytm_3 (esk36_2 X2 X1) X3 -> False) -> X1 = (k4_arytm_2 X2) -> epred1_2 X1 X2 -> m1_subset_1 X3 k5_arytm_3 -> False)
  -> (forall X3 X1 X2, (X1 = (k4_arytm_2 X2) -> False) -> (r2_hidden X3 X2 -> False) -> (r3_arytm_3 (esk36_2 X2 X1) X3 -> False) -> X1 = X2 -> epred1_2 X1 X2 -> m1_subset_1 X3 k5_arytm_3 -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk10_1 X1) (esk11_1 X1)) (k1_tarski (esk10_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1 X2, (r2_hidden X2 a_0_1_arytm_3 -> False) -> X2 = (k2_tarski (k2_tarski X1 np__1) (k1_tarski X1)) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (r3_arytm_3 X2 X1 -> False) -> (m1_subset_1 (esk32_2 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (m1_subset_1 (esk14_2 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 (a_1_0_arytm_2 X2) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk12_1 X1) np__1) (k1_tarski (esk12_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r3_arytm_3 X2 X1 -> r3_arytm_3 X1 X2 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, esk1_0 = X1 -> esk2_0 = X2 -> (k8_arytm_2 esk1_0 esk2_0) = (k10_arytm_3 X1 X2) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> X1 = X2 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X2 X1, (r2_hidden X1 a_0_0_arytm_2 -> False) -> (m1_subset_1 (esk8_2 X1 X2) k5_arytm_3 -> False) -> X1 = X2 -> m1_subset_1 X2 (k1_zfmisc_1 k5_arytm_3) -> False)
  -> (forall X1, (m2_subset_1 (k3_arytm_2 X1) (k1_zfmisc_1 k5_arytm_3) k1_arytm_2 -> False) -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> (m1_subset_1 (esk17_2 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 (k10_arytm_3 X1 X2) k5_arytm_3 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_arytm_2 X1 X2) k2_arytm_2 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X3 X1, (r3_arytm_3 X3 X1 -> False) -> (r2_hidden X2 (a_1_0_arytm_2 X3) -> False) -> X1 = X2 -> m1_subset_1 X3 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> (m1_subset_1 (esk36_2 X2 X1) k5_arytm_3 -> False) -> X1 = (k4_arytm_2 X2) -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, (X1 = (k4_arytm_2 X2) -> False) -> (m1_subset_1 (esk36_2 X2 X1) k5_arytm_3 -> False) -> X1 = X2 -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, (r3_arytm_3 X2 X1 -> False) -> (r3_arytm_3 X1 X2 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (r3_arytm_3 X2 X1 -> False) -> (r3_arytm_3 X1 X2 -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k6_arytm_2 X1 X2) = (k6_arytm_2 X2 X1) -> False) -> m1_subset_1 X2 k1_arytm_2 -> m1_subset_1 X1 k1_arytm_2 -> False)
  -> (forall X2 X1, ((k10_arytm_3 X1 X2) = (k10_arytm_3 X2 X1) -> False) -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, ((k8_arytm_2 X1 X2) = (k8_arytm_2 X2 X1) -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1 X2, ((esk14_2 X1 X2) = X1 -> False) -> m1_subset_1 X2 k5_arytm_3 -> r2_hidden X1 (a_1_0_arytm_2 X2) -> False)
  -> (forall X1 X2, (m1_subset_1 (k8_arytm_3 X1 X2) k5_arytm_3 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk30_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v7_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k9_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (r3_arytm_3 X2 X1 -> False) -> X1 = X2 -> m1_subset_1 X2 k5_arytm_3 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k8_arytm_2 X1 X2) = k11_arytm_3 -> False) -> X1 = k11_arytm_3 -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k9_ordinal3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X1, (r1_arytm_3 (esk10_1 X1) (esk11_1 X1) -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) (k1_zfmisc_1 k5_arytm_3) -> False) -> r2_hidden X1 a_0_0_arytm_2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = k11_arytm_3 -> False) -> (r2_hidden X2 a_0_2_arytm_2 -> False) -> X2 = (a_1_0_arytm_2 X1) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) k5_arytm_3 -> False) -> r2_hidden X1 a_0_2_arytm_2 -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (k4_arytm_2 X1) k2_arytm_2 -> False) -> m1_subset_1 X1 k1_arytm_2 -> False)
  -> (forall X1, (m1_subset_1 (k7_arytm_3 X1) k4_ordinal1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (k6_arytm_3 X1) k4_ordinal1 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, ((k10_arytm_3 X1 k11_arytm_3) = k11_arytm_3 -> False) -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X1 k5_arytm_3 -> False)
  -> (forall X1, ((a_1_0_arytm_2 (esk13_1 X1)) = X1 -> False) -> r2_hidden X1 a_0_2_arytm_2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (esk13_1 X1) = k11_arytm_3 -> r2_hidden X1 a_0_2_arytm_2 -> False)
  -> (forall X1, (esk11_1 X1) = k1_xboole_0 -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, ((esk6_1 X1) = X1 -> False) -> r2_hidden X1 a_0_0_arytm_2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_1 X1) -> False)
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
  -> (forall X1, v1_subset_1 (esk26_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k1_arytm_2 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k5_arytm_3 -> False)
  -> (v1_xboole_0 k2_arytm_2 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (((k2_xboole_0 (k6_subset_1 a_0_0_arytm_3 a_0_1_arytm_3) k4_ordinal1) = k5_arytm_3 -> False) -> False)
  -> (((k6_subset_1 (k2_xboole_0 k5_arytm_3 k1_arytm_2) a_0_2_arytm_2) = k2_arytm_2 -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 k1_arytm_2 (k1_zfmisc_1 (k1_zfmisc_1 k5_arytm_3)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk4_1 X1) X1 -> False) -> False)
  -> (((k6_subset_1 a_0_0_arytm_2 (k1_tarski k5_arytm_3)) = k1_arytm_2 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((r2_hidden esk2_0 k5_arytm_3 -> False) -> False)
  -> ((r2_hidden esk1_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk22_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk18_0 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 esk2_0 k2_arytm_2 -> False) -> False)
  -> ((m1_subset_1 esk1_0 k2_arytm_2 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k11_arytm_3 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk24_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xboole_0 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk23_0 -> False) -> False)
  -> ((v1_ordinal1 esk23_0 -> False) -> False)
  -> ((v7_ordinal1 esk29_0 -> False) -> False)
  -> ((v7_ordinal1 esk27_0 -> False) -> False)
  -> ((v3_ordinal1 esk23_0 -> False) -> False)
  -> ((v3_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((k11_arytm_3 = k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
