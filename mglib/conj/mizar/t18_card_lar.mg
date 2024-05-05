(** $I sig/MizarPreamble.mgs **)

Theorem t18_card_lar:
 forall k2_xboole_0:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall k2_card_lar:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v2_card_lar:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk24_2:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall r1_ordinal1:set -> set -> prop,
 forall v4_card_3:set -> prop,
 forall esk22_1:set -> set,
 forall v1_card_1:set -> prop,
 forall v3_card_1:set -> set -> prop,
 forall esk19_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_card_5:set -> prop,
 forall esk13_0:set,
 forall esk15_0:set,
 forall esk8_0:set,
 forall esk4_1:set -> set,
 forall esk12_0:set,
 forall esk7_0:set,
 forall esk11_0:set,
 forall esk10_0:set,
 forall esk18_0:set,
 forall esk20_0:set,
 forall v2_xxreal_0:set -> prop,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall esk16_0:set,
 forall esk14_0:set,
 forall esk21_0:set,
 forall esk9_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v5_ordinal1:set -> prop,
 forall v5_card_3:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v2_card_1:set -> prop,
 forall k1_xboole_0:set,
 forall k4_ordinal1:set,
 forall np__1:set,
 forall esk17_1:set -> set,
 forall v6_ordinal1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall esk5_2:set -> set -> set,
 forall esk23_1:set -> set,
 forall esk3_2:set -> set -> set,
 forall esk25_3:set -> set -> set -> set,
 forall v1_finset_1:set -> prop,
 forall v4_ordinal1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall a_2_0_card_lar:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v3_ordinal1:set -> prop,
 forall k3_ordinal2:set -> set,
 forall k8_subset_1:set -> set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
     (forall X2 X3 X1, ((k3_ordinal2 (k8_subset_1 X1 X2 (esk6_3 X3 X1 X2))) = (esk6_3 X3 X1 X2) -> False) -> (v1_finset_1 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r2_hidden X3 (a_2_0_card_lar X1 X2) -> False)
  -> (forall X3 X4 X2 X1, (v1_finset_1 X1 -> False) -> (r1_tarski (k9_subset_1 X1 X2 (k2_card_lar X1 X4)) (k2_xboole_0 X3 (k1_tarski X3)) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> r1_tarski (k8_subset_1 X1 X4 X2) X3 -> False)
  -> (forall X1 X2 X3, ((k3_ordinal2 (k8_subset_1 X1 X2 X3)) = X3 -> False) -> (v1_finset_1 X3 -> False) -> (v1_finset_1 X1 -> False) -> (r1_tarski (k8_subset_1 X1 X2 X3) (esk25_3 X1 X3 X2) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X3 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_finset_1 X3 -> False) -> (v1_finset_1 X2 -> False) -> (r2_hidden X3 X1 -> False) -> (k3_ordinal2 (k8_subset_1 X2 X1 X3)) = X3 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v4_ordinal1 X3 -> v4_ordinal1 X2 -> v2_card_lar X1 X2 -> r2_hidden X3 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X4 X3 X2, (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (r2_hidden X3 (a_2_0_card_lar X2 X4) -> False) -> X1 = X3 -> (k3_ordinal2 (k8_subset_1 X2 X4 X1)) = X1 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> v4_ordinal1 X1 -> m1_subset_1 X1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, ((k3_ordinal2 (k8_subset_1 X1 X3 X2)) = X2 -> False) -> (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (r2_hidden (esk25_3 X1 X2 X3) X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> v4_ordinal1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, ((k3_ordinal2 (k8_subset_1 X1 X3 X2)) = X2 -> False) -> (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (v3_ordinal1 (esk25_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> v4_ordinal1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, (v1_finset_1 X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> v1_finset_1 (esk6_3 X1 X2 X3) -> r2_hidden X1 (a_2_0_card_lar X2 X3) -> False)
  -> (forall X2 X1, ((k3_ordinal2 (k8_subset_1 X1 X2 (esk3_2 X1 X2))) = (esk3_2 X1 X2) -> False) -> (v1_finset_1 X1 -> False) -> (v2_card_lar X2 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, (v1_finset_1 X2 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_2_0_card_lar X2 X3) -> False)
  -> (forall X3 X1 X2, (v1_finset_1 X2 -> False) -> (v4_ordinal1 (esk6_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_2_0_card_lar X2 X3) -> False)
  -> (forall X3 X1 X2, ((esk6_3 X1 X2 X3) = X1 -> False) -> (v1_finset_1 X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_2_0_card_lar X2 X3) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k8_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> r2_hidden (k2_xboole_0 (esk23_1 X1) (k1_tarski (esk23_1 X1))) X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k8_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v2_card_lar X2 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r2_hidden (esk3_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk5_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v2_card_lar X2 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> v1_finset_1 (esk3_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk24_2 X3 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v2_card_lar X2 X1 -> False) -> (r2_hidden (esk3_2 X1 X2) X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k3_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (k2_card_lar X1 X2) (k1_zfmisc_1 X1) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r2_hidden (k2_xboole_0 X2 (k1_tarski X2)) X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v2_card_lar X2 X1 -> False) -> (v4_ordinal1 (esk3_2 X1 X2) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v2_card_lar X2 X1 -> False) -> (v3_ordinal1 (esk3_2 X1 X2) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k8_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k2_card_lar X1 X2) = (a_2_0_card_lar X1 X2) -> False) -> (v1_finset_1 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk24_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_ordinal1 (k3_ordinal2 X1) (k3_ordinal2 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k3_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v4_card_3 X2 -> False) -> v4_card_3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (r2_hidden (esk23_1 X1) X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk19_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk22_1 X1) np__1 -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v4_card_3 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v1_finset_1 X1 -> False) -> v3_ordinal1 X1 -> v1_card_1 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v3_ordinal1 (esk23_1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk17_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_3 X1 -> False) -> v4_card_3 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v1_finset_1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_finset_1 X1 -> v5_card_3 X1 -> False)
  -> (forall X1, ((k3_ordinal2 X1) = X1 -> False) -> v3_ordinal1 X1 -> False)
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
  -> (v2_card_lar (k2_card_lar esk1_0 esk2_0) esk1_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v4_card_3 esk9_0 -> False)
  -> (v2_card_1 esk13_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_finset_1 esk16_0 -> False)
  -> (v1_finset_1 esk13_0 -> False)
  -> (v1_finset_1 esk9_0 -> False)
  -> (v1_finset_1 esk8_0 -> False)
  -> (v1_finset_1 esk1_0 -> False)
  -> (v1_finset_1 k4_ordinal1 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk4_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_card_1 (k1_tarski X1) np__1 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> (forall X1, (v3_ordinal1 (k3_ordinal2 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_card_5 esk9_0 -> False) -> False)
  -> ((v5_card_3 esk20_0 -> False) -> False)
  -> ((v5_card_3 k4_ordinal1 -> False) -> False)
  -> ((v2_card_1 k4_ordinal1 -> False) -> False)
  -> ((v7_ordinal1 esk21_0 -> False) -> False)
  -> ((v7_ordinal1 esk18_0 -> False) -> False)
  -> ((v2_ordinal1 esk14_0 -> False) -> False)
  -> ((v2_ordinal1 esk13_0 -> False) -> False)
  -> ((v2_ordinal1 esk12_0 -> False) -> False)
  -> ((v2_ordinal1 esk9_0 -> False) -> False)
  -> ((v2_ordinal1 esk8_0 -> False) -> False)
  -> ((v1_ordinal1 esk14_0 -> False) -> False)
  -> ((v1_ordinal1 esk13_0 -> False) -> False)
  -> ((v1_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_ordinal1 esk9_0 -> False) -> False)
  -> ((v1_ordinal1 esk8_0 -> False) -> False)
  -> ((v1_card_1 esk13_0 -> False) -> False)
  -> ((v1_card_1 esk12_0 -> False) -> False)
  -> ((v1_card_1 esk9_0 -> False) -> False)
  -> ((v1_card_1 esk8_0 -> False) -> False)
  -> ((v1_card_1 esk7_0 -> False) -> False)
  -> ((v1_card_1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_finset_1 esk12_0 -> False) -> False)
  -> ((v4_ordinal1 esk9_0 -> False) -> False)
  -> ((v4_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 esk9_0 -> False) -> False)
  -> ((v3_ordinal1 esk8_0 -> False) -> False)
  -> ((v3_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> False.
Admitted.
