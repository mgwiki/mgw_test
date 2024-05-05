(** $I sig/MizarPreamble.mgs **)

Theorem t19_card_lar:
 forall esk9_3:set -> set -> set -> set,
 forall k8_subset_1:set -> set -> set -> set,
 forall k3_ordinal2:set -> set,
 forall a_2_0_card_lar:set -> set -> set,
 forall r1_ordinal1:set -> set -> prop,
 forall esk2_0:set,
 forall r3_card_lar:set -> set -> prop,
 forall esk1_0:set,
 forall esk3_2:set -> set -> set,
 forall r2_card_lar:set -> set -> prop,
 forall esk29_2:set -> set -> set,
 forall esk30_2:set -> set -> set,
 forall k2_card_lar:set -> set -> set,
 forall esk27_2:set -> set -> set,
 forall r1_card_lar:set -> set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v4_card_3:set -> prop,
 forall esk26_1:set -> set,
 forall v1_card_1:set -> prop,
 forall v3_card_1:set -> set -> prop,
 forall esk23_1:set -> set,
 forall k4_ordinal1:set,
 forall k1_xboole_0:set,
 forall v2_card_1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v5_card_3:set -> prop,
 forall esk17_0:set,
 forall esk19_0:set,
 forall esk12_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall esk7_1:set -> set,
 forall v2_xxreal_0:set -> prop,
 forall esk24_0:set,
 forall esk22_0:set,
 forall esk14_0:set,
 forall esk15_0:set,
 forall esk11_0:set,
 forall esk16_0:set,
 forall esk20_0:set,
 forall esk18_0:set,
 forall esk25_0:set,
 forall esk13_0:set,
 forall v5_ordinal1:set -> prop,
 forall v1_card_5:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall np__1:set,
 forall esk21_1:set -> set,
 forall esk4_1:set -> set,
 forall o_1_0_card_lar:set -> set,
 forall v6_ordinal1:set -> prop,
 forall esk5_2:set -> set -> set,
 forall v1_ordinal1:set -> prop,
 forall esk8_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk28_1:set -> set,
 forall esk33_2:set -> set -> set,
 forall esk32_3:set -> set -> set -> set,
 forall v1_card_lar:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk31_3:set -> set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk10_4:set -> set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall a_3_2_card_lar:set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v4_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v1_finset_1:set -> prop,
     (forall X2 X4 X1 X3, (v1_finset_1 X3 -> False) -> (r2_hidden X1 (k2_xboole_0 (esk10_4 X2 X3 X4 X1) (k1_tarski (esk10_4 X2 X3 X4 X1))) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> r2_hidden X2 (a_3_2_card_lar X3 X4 X1) -> False)
  -> (forall X4 X1 X3 X2, ((k2_xboole_0 (esk10_4 X1 X2 X3 X4) (k1_tarski (esk10_4 X1 X2 X3 X4))) = X1 -> False) -> (v1_finset_1 X2 -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_2_card_lar X2 X3 X4) -> False)
  -> (forall X4 X1 X3 X2, (v1_finset_1 X2 -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X3 -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_2_card_lar X2 X3 X4) -> False)
  -> (forall X4 X1 X3 X2, (v1_finset_1 X2 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) X2 -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_2_card_lar X2 X3 X4) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X2 -> r2_hidden (esk6_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, ((k3_ordinal2 (k8_subset_1 X1 X2 (esk9_3 X3 X1 X2))) = (esk9_3 X3 X1 X2) -> False) -> (v1_finset_1 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r2_hidden X3 (a_2_0_card_lar X1 X2) -> False)
  -> (forall X1 X2 X3, ((k3_ordinal2 (k8_subset_1 X1 X2 X3)) = X3 -> False) -> (v1_finset_1 X3 -> False) -> (v1_finset_1 X1 -> False) -> (r1_tarski (k8_subset_1 X1 X2 X3) (esk31_3 X1 X3 X2) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X3 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X4 X5 X1 X2, (v1_finset_1 X2 -> False) -> (r2_hidden X3 (a_3_2_card_lar X2 X4 X5) -> False) -> X3 = (k2_xboole_0 X1 (k1_tarski X1)) -> v3_ordinal1 X5 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X1 X2 -> r2_hidden X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> r2_hidden X5 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1 X4 X3 X2, (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (r2_hidden X3 (a_2_0_card_lar X2 X4) -> False) -> X1 = X3 -> (k3_ordinal2 (k8_subset_1 X2 X4 X1)) = X1 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> v4_ordinal1 X1 -> m1_subset_1 X1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, ((k3_ordinal2 (k8_subset_1 X1 X3 X2)) = X2 -> False) -> (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (r2_hidden (esk31_3 X1 X2 X3) X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> v4_ordinal1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, ((k3_ordinal2 (k8_subset_1 X1 X3 X2)) = X2 -> False) -> (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (v3_ordinal1 (esk31_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> v4_ordinal1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, (v1_finset_1 X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> v1_finset_1 (esk9_3 X1 X2 X3) -> r2_hidden X1 (a_2_0_card_lar X2 X3) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X3 X1 X2, (v1_finset_1 X2 -> False) -> (m1_subset_1 (esk9_3 X1 X2 X3) X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_2_0_card_lar X2 X3) -> False)
  -> (forall X3 X1 X2, (v1_finset_1 X2 -> False) -> (v4_ordinal1 (esk9_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_2_0_card_lar X2 X3) -> False)
  -> (forall X3 X2 X1, (v1_finset_1 X1 -> False) -> (r2_hidden (esk32_3 X1 X2 X3) X2 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> v1_card_lar X2 X1 -> r2_hidden X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, (v1_finset_1 X2 -> False) -> (r1_ordinal1 X1 (esk32_3 X2 X3 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> v1_card_lar X3 X2 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_finset_1 X1 -> False) -> (v3_ordinal1 (esk32_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> v1_card_lar X2 X1 -> r2_hidden X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v3_ordinal1 X1 -> r2_hidden X1 esk1_0 -> r3_card_lar esk1_0 (a_3_2_card_lar esk1_0 esk2_0 X1) -> False)
  -> (forall X3 X1 X2, ((esk9_3 X1 X2 X3) = X1 -> False) -> (v1_finset_1 X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_2_0_card_lar X2 X3) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k8_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (v1_finset_1 X3 -> False) -> (v1_card_lar X2 X3 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> r1_ordinal1 (esk33_2 X3 X2) X1 -> False)
  -> (forall X1 X2, ((k3_ordinal2 (k3_xboole_0 X1 (esk3_2 X2 X1))) = (esk3_2 X2 X1) -> False) -> (v1_finset_1 X2 -> False) -> (r2_card_lar X2 X1 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> r2_hidden (k2_xboole_0 (esk28_1 X1) (k1_tarski (esk28_1 X1))) X1 -> False)
  -> (forall X1 X3 X2, (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (r2_hidden X1 X3 -> False) -> (k3_ordinal2 (k3_xboole_0 X3 X1)) = X1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> v4_ordinal1 X1 -> r2_hidden X1 X2 -> r2_card_lar X2 X3 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k8_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v1_finset_1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> v1_card_lar X3 X2 -> r2_hidden X1 X2 -> r1_tarski X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk8_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r2_card_lar X1 X2 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r1_tarski X2 X1 -> r2_hidden (esk3_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r2_hidden X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X2)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk29_2 X3 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v1_card_lar X2 X1 -> False) -> (r2_hidden (esk33_2 X1 X2) X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v1_card_lar X2 X1 -> False) -> (r2_hidden (esk30_2 X1 X2) X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v1_card_lar X1 X2 -> False) -> (r1_tarski X1 (esk30_2 X2 X1) -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r2_card_lar X1 X2 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r1_tarski X2 X1 -> v1_finset_1 (esk3_2 X1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k3_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (k2_card_lar X1 X2) (k1_zfmisc_1 X1) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r2_hidden (k2_xboole_0 X2 (k1_tarski X2)) X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r2_card_lar X1 X2 -> False) -> (r2_hidden (esk3_2 X1 X2) X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r1_tarski X2 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v1_card_lar X2 X1 -> False) -> (v3_ordinal1 (esk33_2 X1 X2) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v1_card_lar X2 X1 -> False) -> (v3_ordinal1 (esk30_2 X1 X2) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X2)) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X2 X1, ((k8_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r2_card_lar X1 X2 -> False) -> (v4_ordinal1 (esk3_2 X1 X2) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r1_tarski X2 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r2_card_lar X1 X2 -> False) -> (v3_ordinal1 (esk3_2 X1 X2) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r1_tarski X2 X1 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v1_ordinal1 X1 -> r2_hidden X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk27_2 X1 X2) X2 -> False) -> v3_ordinal1 X1 -> r2_hidden X1 (k3_ordinal2 X2) -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 (esk27_2 X1 X2) -> False) -> v3_ordinal1 X1 -> r2_hidden X1 (k3_ordinal2 X2) -> False)
  -> (forall X2 X1, ((k2_card_lar X1 X2) = (a_2_0_card_lar X1 X2) -> False) -> (v1_finset_1 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, ((k3_ordinal2 X1) = X2 -> False) -> (v1_finset_1 X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> v1_card_lar X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r3_card_lar X1 X2 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r1_card_lar X1 X2 -> r2_card_lar X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v1_card_lar X1 X2 -> False) -> (k3_ordinal2 X1) = X2 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v3_ordinal1 (esk27_2 X1 X2) -> False) -> v3_ordinal1 X1 -> r2_hidden X1 (k3_ordinal2 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (r2_hidden X2 X1 -> False) -> v1_ordinal1 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X3 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (r1_card_lar X2 X1 -> False) -> (k3_ordinal2 X1) = X2 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk29_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r2_card_lar X1 X2 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r3_card_lar X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r1_card_lar X1 X2 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r3_card_lar X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> r2_card_lar X2 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> r1_card_lar X2 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk5_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k3_ordinal2 X1) = X2 -> False) -> (v1_finset_1 X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> r1_card_lar X2 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = X2 -> False) -> ((k2_xboole_0 X1 X2) = X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k3_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X2 X1 -> False) -> v1_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, (v4_card_3 X2 -> False) -> v4_card_3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (o_1_0_card_lar X1) X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> r1_tarski (esk4_1 X1) X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (r2_hidden (esk28_1 X1) X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk23_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> (r2_hidden (esk4_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk26_1 X1) np__1 -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v4_card_3 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v1_finset_1 X1 -> False) -> v3_ordinal1 X1 -> v1_card_1 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v3_ordinal1 (esk28_1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk21_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_3 X1 -> False) -> v4_card_3 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v1_finset_1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_finset_1 X1 -> v5_card_3 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v5_card_3 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (v1_card_lar (k2_card_lar esk1_0 esk2_0) esk1_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v4_card_3 esk13_0 -> False)
  -> (v2_card_1 esk17_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_finset_1 esk20_0 -> False)
  -> (v1_finset_1 esk17_0 -> False)
  -> (v1_finset_1 esk13_0 -> False)
  -> (v1_finset_1 esk12_0 -> False)
  -> (v1_finset_1 esk1_0 -> False)
  -> (v1_finset_1 k4_ordinal1 -> False)
  -> (forall X1, (r2_hidden X1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_card_1 (k1_tarski X1) np__1 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((v1_card_lar esk2_0 esk1_0 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> (forall X1, (v3_ordinal1 (k3_ordinal2 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_card_5 esk13_0 -> False) -> False)
  -> ((v5_card_3 esk24_0 -> False) -> False)
  -> ((v5_card_3 k4_ordinal1 -> False) -> False)
  -> ((v2_card_1 k4_ordinal1 -> False) -> False)
  -> ((v7_ordinal1 esk25_0 -> False) -> False)
  -> ((v7_ordinal1 esk22_0 -> False) -> False)
  -> ((v2_ordinal1 esk18_0 -> False) -> False)
  -> ((v2_ordinal1 esk17_0 -> False) -> False)
  -> ((v2_ordinal1 esk16_0 -> False) -> False)
  -> ((v2_ordinal1 esk13_0 -> False) -> False)
  -> ((v2_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_ordinal1 esk18_0 -> False) -> False)
  -> ((v1_ordinal1 esk17_0 -> False) -> False)
  -> ((v1_ordinal1 esk16_0 -> False) -> False)
  -> ((v1_ordinal1 esk13_0 -> False) -> False)
  -> ((v1_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_card_1 esk17_0 -> False) -> False)
  -> ((v1_card_1 esk16_0 -> False) -> False)
  -> ((v1_card_1 esk13_0 -> False) -> False)
  -> ((v1_card_1 esk12_0 -> False) -> False)
  -> ((v1_card_1 esk11_0 -> False) -> False)
  -> ((v1_card_1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_finset_1 esk16_0 -> False) -> False)
  -> ((v4_ordinal1 esk13_0 -> False) -> False)
  -> ((v4_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> False.
Admitted.
