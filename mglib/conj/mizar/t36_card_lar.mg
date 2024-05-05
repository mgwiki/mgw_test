(** $I sig/MizarPreamble.mgs **)

Theorem t36_card_lar:
 forall r1_ordinal1:set -> set -> prop,
 forall k4_classes1:set -> set,
 forall k1_tarski:set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk29_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k6_classes1:set -> set,
 forall esk32_2:set -> set -> set,
 forall k1_xboole_0:set,
 forall esk31_2:set -> set -> set,
 forall esk30_2:set -> set -> set,
 forall v1_ordinal1:set -> prop,
 forall esk9_2:set -> set -> set,
 forall v7_ordinal1:set -> prop,
 forall v4_card_3:set -> prop,
 forall esk18_1:set -> set,
 forall v6_card_fil:set -> prop,
 forall esk19_1:set -> set,
 forall v1_classes2:set -> prop,
 forall esk28_1:set -> set,
 forall np__1:set,
 forall k4_ordinal1:set,
 forall v1_card_5:set -> prop,
 forall v5_card_fil:set -> prop,
 forall v5_card_3:set -> prop,
 forall esk17_0:set,
 forall esk21_0:set,
 forall esk13_0:set,
 forall esk22_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall v2_xxreal_0:set -> prop,
 forall esk24_0:set,
 forall esk16_0:set,
 forall esk14_0:set,
 forall esk15_0:set,
 forall esk10_0:set,
 forall esk26_0:set,
 forall esk7_1:set -> set,
 forall esk11_0:set,
 forall esk12_0:set,
 forall esk20_0:set,
 forall esk27_0:set,
 forall esk1_0:set,
 forall v5_ordinal1:set -> prop,
 forall v2_card_1:set -> prop,
 forall v4_card_fil:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk25_1:set -> set,
 forall v3_card_1:set -> set -> prop,
 forall esk23_1:set -> set,
 forall esk2_1:set -> set,
 forall esk3_1:set -> set,
 forall r2_wellord2:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall r2_xboole_0:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall a_1_4_card_lar:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k1_card_5:set -> set,
 forall k1_card_1:set -> set,
 forall v1_card_1:set -> prop,
 forall v1_classes1:set -> prop,
 forall esk4_1:set -> set,
 forall r2_tarski:set -> set -> prop,
 forall esk5_1:set -> set,
 forall v2_classes1:set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk34_2:set -> set -> set,
 forall esk33_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_card_lar:set -> set -> prop,
 forall v4_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v1_finset_1:set -> prop,
     (forall X3 X2 X1, (v1_finset_1 X1 -> False) -> (r2_hidden (esk33_3 X1 X2 X3) X2 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X3 X1 -> v1_card_lar X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, (v1_finset_1 X2 -> False) -> (r1_ordinal1 X1 (esk33_3 X2 X3 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> r2_hidden X1 X2 -> v1_card_lar X3 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_finset_1 X1 -> False) -> (v3_ordinal1 (esk33_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X3 X1 -> v1_card_lar X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r2_hidden X1 (k4_classes1 X2) -> False) -> v3_ordinal1 X2 -> r2_hidden (k1_zfmisc_1 X1) (k4_classes1 (k2_xboole_0 X2 (k1_tarski X2))) -> False)
  -> (forall X2 X1 X3, (v1_finset_1 X3 -> False) -> (v1_card_lar X2 X3 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> r1_ordinal1 (esk34_2 X3 X2) X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> r2_hidden (k2_xboole_0 (esk29_1 X1) (k1_tarski (esk29_1 X1))) X1 -> False)
  -> (forall X1 X2, (r2_hidden (k1_zfmisc_1 X1) (k4_classes1 (k2_xboole_0 X2 (k1_tarski X2))) -> False) -> v3_ordinal1 X2 -> r2_hidden X1 (k4_classes1 X2) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (r1_ordinal1 (k6_classes1 X1) X2 -> False) -> v3_ordinal1 X2 -> r2_hidden (k6_classes1 (esk32_2 X1 X2)) X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk8_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 (k4_classes1 (esk31_2 X2 X1)) -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> r2_hidden X1 (k4_classes1 X2) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk30_2 X3 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v1_card_lar X2 X1 -> False) -> (r2_hidden (esk34_2 X1 X2) X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X3 (k4_classes1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> r2_hidden X1 X2 -> r2_hidden X3 (k4_classes1 X1) -> False)
  -> (forall X1 X2, (r2_hidden (k2_xboole_0 X2 (k1_tarski X2)) X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v1_card_lar X2 X1 -> False) -> (v3_ordinal1 (esk34_2 X1 X2) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> v1_classes1 X1 -> r2_tarski (esk5_1 X1) X1 -> r2_hidden (k1_zfmisc_1 (esk4_1 X1)) X1 -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> v1_classes1 X1 -> r2_hidden (esk5_1 X1) X1 -> r2_hidden (k1_zfmisc_1 (esk4_1 X1)) X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r1_ordinal1 (k1_card_5 X1) (k1_card_1 X2) -> False) -> v1_card_1 X1 -> v1_card_lar X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk31_2 X1 X2) X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 (k4_classes1 X1) -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> (r1_tarski (esk5_1 X1) X1 -> False) -> v1_classes1 X1 -> r2_hidden (k1_zfmisc_1 (esk4_1 X1)) X1 -> False)
  -> (forall X1 X3 X2, (r2_hidden (k6_classes1 X3) X2 -> False) -> v3_ordinal1 X2 -> r2_hidden X3 X1 -> r1_ordinal1 (k6_classes1 X1) X2 -> False)
  -> (forall X3 X2 X1, (r2_hidden X2 (k4_classes1 X1) -> False) -> v3_ordinal1 X1 -> r1_tarski X2 X3 -> r2_hidden X3 (k4_classes1 X1) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v1_ordinal1 X1 -> r2_hidden X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X3 (a_1_4_card_lar X2) -> False) -> X3 = (k6_classes1 X1) -> r2_hidden X1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (v3_ordinal1 (esk31_2 X1 X2) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 (k4_classes1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk9_2 X1 X2) X2 -> False) -> r2_hidden X1 (a_1_4_card_lar X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X2 -> False) -> r2_hidden X1 (a_1_4_card_lar X2) -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r1_ordinal1 (k6_classes1 X1) X2 -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> v3_ordinal1 X2 -> False)
  -> (forall X1 X2, ((k6_classes1 (esk9_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> r2_hidden X1 (a_1_4_card_lar X2) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> v1_classes1 X1 -> r2_hidden X2 X1 -> r1_tarski X3 X2 -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> (r2_hidden (esk4_1 X1) X1 -> False) -> v1_classes1 X1 -> r2_tarski (esk5_1 X1) X1 -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> (r2_hidden (esk4_1 X1) X1 -> False) -> v1_classes1 X1 -> r2_hidden (esk5_1 X1) X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk30_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r2_hidden (k6_classes1 X1) X2 -> False) -> v3_ordinal1 X2 -> r2_hidden X1 (k4_classes1 X2) -> False)
  -> (forall X1 X2, (r2_hidden X1 (k4_classes1 X2) -> False) -> v3_ordinal1 X2 -> r2_hidden (k6_classes1 X1) X2 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r2_hidden X1 X2 -> False) -> (r2_tarski X1 X2 -> False) -> v2_classes1 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> (r2_hidden (esk4_1 X1) X1 -> False) -> (r1_tarski (esk5_1 X1) X1 -> False) -> v1_classes1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r2_hidden X1 X2 -> False) -> v3_ordinal1 X2 -> v1_ordinal1 X1 -> r2_xboole_0 X1 X2 -> False)
  -> (forall X1 X2, (r2_hidden (k1_zfmisc_1 X1) X2 -> False) -> v2_classes1 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_ordinal1 (k1_card_1 X1) (k1_card_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_xboole_0 X2 X1 -> r2_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_card_3 X2 -> False) -> v4_card_3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r1_ordinal1 (k1_card_1 (a_1_4_card_lar X1)) (k1_card_1 X1) -> False) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_hidden X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> (r2_xboole_0 X1 X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> r2_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X2 X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (r2_tarski X1 X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (m1_subset_1 (esk18_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> r2_hidden (esk3_1 X1) X1 -> False)
  -> (forall X1, ((k1_card_1 (k4_classes1 X1)) = X1 -> False) -> (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> v1_card_1 X1 -> v6_card_fil X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> v1_card_1 X1 -> v1_finset_1 (esk18_1 X1) -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (r2_hidden (esk29_1 X1) X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) X1 -> False) -> v1_classes2 X1 -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> (r1_tarski (esk3_1 X1) (esk2_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, ((k1_card_1 X1) = (k1_card_1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_classes2 X1 -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_card_1 X1 -> v1_finset_1 (k1_card_5 X1) -> False)
  -> (forall X1, (v3_card_1 (esk25_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (r1_tarski X1 (k4_classes1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> (k1_card_1 X1) = (k1_card_1 X2) -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v2_ordinal1 (esk18_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v1_ordinal1 (esk18_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v3_ordinal1 (esk18_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v1_card_1 (esk18_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X2 X1, X1 = X2 -> r2_xboole_0 X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_finset_1 X1 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> (r2_hidden (esk2_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_5 X1 -> False) -> (k1_card_5 X1) = X1 -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, ((k1_card_5 X1) = X1 -> False) -> (v1_finset_1 X1 -> False) -> v1_card_1 X1 -> v1_card_5 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk28_1 X1) np__1 -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_fil X1 -> False) -> v1_card_1 X1 -> v6_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> v4_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> v6_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v5_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v4_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v4_card_3 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_fil X1 -> False) -> v1_card_1 X1 -> v6_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_ordinal1 X1 -> False) -> v1_card_1 X1 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v3_ordinal1 (esk29_1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_1 (k1_card_5 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k1_card_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk23_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_card_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_finset_1 X1 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_classes2 X1 -> False) -> v2_classes1 X1 -> v1_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 (k4_classes1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k1_card_1 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_card_1 (k1_card_5 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_card_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_3 X1 -> False) -> v4_card_3 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> (forall X1, v1_finset_1 X1 -> v5_card_3 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v1_classes2 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> v2_classes1 X1 -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> v2_classes1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> v1_classes2 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v5_card_3 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1, r2_xboole_0 X1 X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v2_classes1 (k4_classes1 esk1_0) -> False)
  -> (v2_card_1 esk17_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v4_card_3 esk12_0 -> False)
  -> (v4_card_3 esk1_0 -> False)
  -> (v1_finset_1 esk22_0 -> False)
  -> (v1_finset_1 esk17_0 -> False)
  -> (v1_finset_1 esk12_0 -> False)
  -> (v1_finset_1 esk11_0 -> False)
  -> (v1_finset_1 esk1_0 -> False)
  -> (v1_finset_1 k4_ordinal1 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_card_1 (k1_tarski X1) np__1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k1_card_1 (k1_card_1 X1)) = (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (r2_wellord2 X1 X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> (forall X1, (v3_ordinal1 (k6_classes1 X1) -> False) -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v5_card_3 esk26_0 -> False) -> False)
  -> ((v5_card_3 k4_ordinal1 -> False) -> False)
  -> ((v7_ordinal1 esk27_0 -> False) -> False)
  -> ((v7_ordinal1 esk24_0 -> False) -> False)
  -> ((v1_classes2 esk13_0 -> False) -> False)
  -> ((v1_card_5 esk12_0 -> False) -> False)
  -> ((v2_card_1 k4_ordinal1 -> False) -> False)
  -> ((v2_ordinal1 esk20_0 -> False) -> False)
  -> ((v2_ordinal1 esk17_0 -> False) -> False)
  -> ((v2_ordinal1 esk16_0 -> False) -> False)
  -> ((v2_ordinal1 esk12_0 -> False) -> False)
  -> ((v2_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_ordinal1 esk20_0 -> False) -> False)
  -> ((v1_ordinal1 esk17_0 -> False) -> False)
  -> ((v1_ordinal1 esk16_0 -> False) -> False)
  -> ((v1_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_ordinal1 esk11_0 -> False) -> False)
  -> ((v4_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk20_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v6_card_fil esk1_0 -> False) -> False)
  -> ((v1_card_1 esk17_0 -> False) -> False)
  -> ((v1_card_1 esk16_0 -> False) -> False)
  -> ((v1_card_1 esk12_0 -> False) -> False)
  -> ((v1_card_1 esk11_0 -> False) -> False)
  -> ((v1_card_1 esk10_0 -> False) -> False)
  -> ((v1_card_1 esk1_0 -> False) -> False)
  -> ((v1_card_1 k4_ordinal1 -> False) -> False)
  -> ((v1_finset_1 esk16_0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> False.
Admitted.
