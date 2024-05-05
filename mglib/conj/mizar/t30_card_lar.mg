(** $I sig/MizarPreamble.mgs **)

Theorem t30_card_lar:
 forall k4_xboole_0:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall v1_finset_1:set -> prop,
 forall v4_ordinal1:set -> prop,
 forall v2_card_lar:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_card_lar:set -> set -> prop,
 forall r4_card_lar:set -> set -> prop,
 forall v3_ordinal1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall esk27_1:set -> set,
 forall k1_tarski:set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall r1_ordinal1:set -> set -> prop,
 forall k3_card_2:set -> set -> set,
 forall np__2:set,
 forall esk2_1:set -> set,
 forall v5_card_fil:set -> prop,
 forall v6_card_fil:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v5_card_lar:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk17_1:set -> set,
 forall esk26_1:set -> set,
 forall np__1:set,
 forall v2_ordinal1:set -> prop,
 forall k4_ordinal1:set,
 forall k1_xboole_0:set,
 forall v1_card_5:set -> prop,
 forall v2_card_1:set -> prop,
 forall v5_card_3:set -> prop,
 forall esk16_0:set,
 forall esk19_0:set,
 forall esk12_0:set,
 forall esk1_0:set,
 forall esk11_0:set,
 forall esk7_1:set -> set,
 forall esk22_0:set,
 forall esk10_0:set,
 forall esk14_0:set,
 forall esk13_0:set,
 forall esk15_0:set,
 forall esk24_0:set,
 forall v2_xxreal_0:set -> prop,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall esk20_0:set,
 forall esk18_0:set,
 forall esk25_0:set,
 forall v5_ordinal1:set -> prop,
 forall v4_card_fil:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk3_1:set -> set,
 forall esk23_1:set -> set,
 forall v3_card_1:set -> set -> prop,
 forall esk21_1:set -> set,
 forall v7_ordinal1:set -> prop,
 forall v4_card_3:set -> prop,
 forall a_1_2_card_lar:set -> set,
 forall esk9_2:set -> set -> set,
 forall v1_card_1:set -> prop,
 forall esk28_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk4_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> r2_hidden (esk4_3 X1 X2 X3) X2 -> r2_hidden (esk4_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk5_3 X1 X2 X3) X2 -> False)
  -> (forall X3 X1 X2, (v1_finset_1 X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> r4_card_lar X2 X3 -> v2_card_lar X1 X2 -> v1_card_lar X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> v1_xboole_0 (k9_subset_1 X2 X3 X1) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r4_card_lar X1 X2 -> False) -> (v1_xboole_0 (k9_subset_1 X1 X2 (esk6_2 X1 X2)) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r1_tarski X2 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> r2_hidden (k2_xboole_0 (esk27_1 X1) (k1_tarski (esk27_1 X1))) X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk8_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X2)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk28_2 X3 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r4_card_lar X1 X2 -> False) -> (m1_subset_1 (esk6_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r1_tarski X2 X1 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (r2_hidden (k2_xboole_0 X2 (k1_tarski X2)) X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r4_card_lar X1 X2 -> False) -> (v1_card_lar (esk6_2 X1 X2) X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r1_tarski X2 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r4_card_lar X1 X2 -> False) -> (v2_card_lar (esk6_2 X1 X2) X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r1_tarski X2 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> v1_card_1 X2 -> v1_finset_1 (esk9_2 X1 X2) -> r2_hidden X1 (a_1_2_card_lar X2) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_fil X1 -> False) -> v1_card_1 X1 -> r2_hidden (k3_card_2 np__2 (esk2_1 X1)) X1 -> False)
  -> (forall X1 X2, (r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X2)) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v1_card_lar (k4_xboole_0 X1 X2) X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (v2_card_lar (k4_xboole_0 X1 X2) X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> (m1_subset_1 (esk9_2 X1 X2) X2 -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_2_card_lar X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> (r2_hidden (k3_card_2 np__2 X2) X1 -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> v5_card_fil X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X3 X2, (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (v4_card_3 X2 -> False) -> (r2_hidden X3 (a_1_2_card_lar X2) -> False) -> X1 = X3 -> v1_card_1 X2 -> v1_card_1 X1 -> v6_card_fil X1 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> (v6_card_fil (esk9_2 X1 X2) -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_2_card_lar X2) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> (v1_card_1 (esk9_2 X1 X2) -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_2_card_lar X2) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k4_xboole_0 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> v1_finset_1 (k3_card_2 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k4_xboole_0 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, (r2_hidden X2 X1 -> False) -> v1_ordinal1 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X3 -> False)
  -> (forall X1 X2, ((esk9_2 X1 X2) = X1 -> False) -> (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_2_card_lar X2) -> False)
  -> (forall X2 X1, (r2_hidden (esk28_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k4_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> r4_card_lar X2 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (v1_card_1 (k3_card_2 X1 X2) -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v5_card_lar X1 -> False) -> v1_card_1 X1 -> r4_card_lar X1 (a_1_2_card_lar X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k3_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_card_1 (k3_card_2 X1 X2) -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (r4_card_lar X1 (a_1_2_card_lar X1) -> False) -> v1_card_1 X1 -> v5_card_lar X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_card_3 X2 -> False) -> v4_card_3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_hidden X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_fil X1 -> False) -> (r2_hidden (esk2_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (m1_subset_1 (esk17_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> v1_card_1 X1 -> v1_finset_1 (esk17_1 X1) -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (r2_hidden (esk27_1 X1) X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk23_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_fil X1 -> False) -> (v1_card_1 (esk2_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v2_ordinal1 (esk17_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v1_ordinal1 (esk17_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v3_ordinal1 (esk17_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v1_card_1 (esk17_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_finset_1 X1 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk3_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk26_1 X1) np__1 -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> v6_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> v4_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v4_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v5_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v4_card_3 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_fil X1 -> False) -> v1_card_1 X1 -> v6_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_ordinal1 X1 -> False) -> v1_card_1 X1 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_fil X1 -> False) -> v1_card_1 X1 -> v6_card_fil X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v3_ordinal1 (esk27_1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk21_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_finset_1 X1 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_3 X1 -> False) -> v4_card_3 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_finset_1 X1 -> v5_card_3 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v5_card_3 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v2_card_1 esk16_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 np__2 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v5_card_fil esk1_0 -> False)
  -> (v4_card_3 esk12_0 -> False)
  -> (v4_card_3 esk1_0 -> False)
  -> (v1_finset_1 esk20_0 -> False)
  -> (v1_finset_1 esk16_0 -> False)
  -> (v1_finset_1 esk12_0 -> False)
  -> (v1_finset_1 esk11_0 -> False)
  -> (v1_finset_1 esk1_0 -> False)
  -> (v1_finset_1 k4_ordinal1 -> False)
  -> ((m2_subset_1 np__2 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k4_xboole_0 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_card_1 (k1_tarski X1) np__1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((m1_subset_1 np__2 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__2 k5_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((v2_xxreal_0 np__2 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v5_card_3 esk24_0 -> False) -> False)
  -> ((v5_card_3 k4_ordinal1 -> False) -> False)
  -> ((v7_ordinal1 esk25_0 -> False) -> False)
  -> ((v7_ordinal1 esk22_0 -> False) -> False)
  -> ((v1_card_5 esk12_0 -> False) -> False)
  -> ((v2_card_1 k4_ordinal1 -> False) -> False)
  -> ((v2_ordinal1 esk18_0 -> False) -> False)
  -> ((v2_ordinal1 esk16_0 -> False) -> False)
  -> ((v2_ordinal1 esk15_0 -> False) -> False)
  -> ((v2_ordinal1 esk12_0 -> False) -> False)
  -> ((v2_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_ordinal1 esk18_0 -> False) -> False)
  -> ((v1_ordinal1 esk16_0 -> False) -> False)
  -> ((v1_ordinal1 esk15_0 -> False) -> False)
  -> ((v1_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_ordinal1 esk11_0 -> False) -> False)
  -> ((v4_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v3_ordinal1 esk15_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v5_card_lar esk1_0 -> False) -> False)
  -> ((v1_card_1 esk16_0 -> False) -> False)
  -> ((v1_card_1 esk15_0 -> False) -> False)
  -> ((v1_card_1 esk12_0 -> False) -> False)
  -> ((v1_card_1 esk11_0 -> False) -> False)
  -> ((v1_card_1 esk10_0 -> False) -> False)
  -> ((v1_card_1 esk1_0 -> False) -> False)
  -> ((v1_card_1 k4_ordinal1 -> False) -> False)
  -> ((v1_finset_1 esk15_0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> False.
Admitted.
