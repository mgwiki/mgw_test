(** $I sig/MizarPreamble.mgs **)

Theorem t9_card_lar:
 forall a_3_0_card_lar:set -> set -> set -> set,
 forall esk8_4:set -> set -> set -> set -> set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk5_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk23_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v4_card_3:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall esk16_0:set,
 forall esk17_0:set,
 forall esk7_1:set -> set,
 forall esk13_0:set,
 forall esk10_0:set,
 forall esk12_0:set,
 forall esk14_0:set,
 forall esk19_0:set,
 forall esk21_0:set,
 forall esk11_0:set,
 forall esk15_0:set,
 forall esk22_0:set,
 forall v5_ordinal1:set -> prop,
 forall v5_card_3:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall esk20_1:set -> set,
 forall v3_card_1:set -> set -> prop,
 forall v1_card_1:set -> prop,
 forall esk18_1:set -> set,
 forall v6_ordinal1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk4_3:set -> set -> set -> set,
 forall k1_xboole_0:set,
 forall esk24_3:set -> set -> set -> set,
 forall v1_card_lar:set -> set -> prop,
 forall k1_setfam_1:set -> set,
 forall k2_ordinal1:set -> set,
 forall k1_card_lar:set -> set -> set -> set,
 forall esk9_4:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_3_1_card_lar:set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v4_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v1_finset_1:set -> prop,
     (forall X4 X1 X3 X2, (v1_finset_1 X2 -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X3 -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_1_card_lar X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v1_finset_1 X2 -> False) -> (r2_hidden (esk8_4 X1 X2 X3 X4) X4 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_0_card_lar X2 X3 X4) -> False)
  -> (forall X4 X1 X3 X2, (v1_finset_1 X2 -> False) -> (m1_subset_1 (esk9_4 X1 X2 X3 X4) X2 -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_1_card_lar X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v1_finset_1 X2 -> False) -> (m1_subset_1 (esk8_4 X1 X2 X3 X4) X2 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_0_card_lar X2 X3 X4) -> False)
  -> (forall X2 X4 X1 X3, (v1_finset_1 X3 -> False) -> (r2_hidden X1 (esk9_4 X2 X3 X4 X1) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> r2_hidden X2 (a_3_1_card_lar X3 X4 X1) -> False)
  -> (forall X2 X4 X1 X3, (v1_finset_1 X3 -> False) -> (r2_hidden X1 (esk8_4 X2 X3 X1 X4) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> r2_hidden X2 (a_3_0_card_lar X3 X1 X4) -> False)
  -> (forall X4 X1 X3 X2, ((esk9_4 X1 X2 X3 X4) = X1 -> False) -> (v1_finset_1 X2 -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_1_card_lar X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, ((esk8_4 X1 X2 X3 X4) = X1 -> False) -> (v1_finset_1 X2 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_0_card_lar X2 X3 X4) -> False)
  -> (forall X3 X2 X1, ((k1_setfam_1 (k2_ordinal1 (a_3_1_card_lar X1 X2 X3))) = (k1_card_lar X1 X2 X3) -> False) -> (v1_finset_1 X1 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> v1_card_lar X2 X1 -> r2_hidden X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (r2_hidden esk2_0 (k1_card_lar esk1_0 esk3_0 esk2_0) -> r2_hidden (k1_card_lar esk1_0 esk3_0 esk2_0) esk3_0 -> False)
  -> (forall X2 X3 X1, (v1_finset_1 X1 -> False) -> (r2_hidden (esk24_3 X1 X2 X3) (a_3_0_card_lar X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> v1_card_lar X3 X1 -> r2_hidden X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X4 X3, (v1_finset_1 X3 -> False) -> (r2_hidden X1 X2 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X3) -> r2_hidden X2 (a_3_0_card_lar X3 X1 X4) -> False)
  -> (forall X2 X1 X4 X3, (v1_finset_1 X3 -> False) -> (r2_hidden X1 X2 -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v4_ordinal1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> r2_hidden X1 (a_3_0_card_lar X3 X4 X2) -> False)
  -> (forall X3 X5 X4 X1 X2, (v1_finset_1 X2 -> False) -> (r2_hidden X3 (a_3_0_card_lar X2 X5 X4) -> False) -> X1 = X3 -> v3_ordinal1 X5 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X1 X2 -> r2_hidden X5 X1 -> r2_hidden X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X4 X5 X1 X2, (v1_finset_1 X2 -> False) -> (r2_hidden X3 (a_3_1_card_lar X2 X4 X5) -> False) -> X1 = X3 -> v3_ordinal1 X5 -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> m1_subset_1 X1 X2 -> r2_hidden X5 X1 -> r2_hidden X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk24_3 X1 X2 X3) X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> v1_card_lar X3 X1 -> r2_hidden X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X3 = (k1_setfam_1 X2) -> r2_hidden X1 (esk4_3 X2 X3 X1) -> False)
  -> (forall X2 X3 X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (a_3_0_card_lar X1 X2 X3) (k1_zfmisc_1 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (k1_card_lar X1 X2 X3) X2 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> r2_hidden (esk5_2 X1 X2) X2 -> r2_hidden (esk5_2 X1 X2) (esk6_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden X3 X2 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X1 -> False) -> X2 = (k1_setfam_1 X1) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk5_2 X1 X2) X3 -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> r2_hidden X3 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk23_2 X3 X2) -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> v1_xboole_0 X2 -> v1_card_lar X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k1_setfam_1 X4) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk23_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_card_3 X2 -> False) -> v4_card_3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, ((k2_ordinal1 X2) = X2 -> False) -> v3_ordinal1 X1 -> r1_tarski X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_card_1 (esk20_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v1_finset_1 X1 -> False) -> v3_ordinal1 X1 -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk18_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_3 X1 -> False) -> v4_card_3 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v1_finset_1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_finset_1 X1 -> v5_card_3 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> X2 = k1_xboole_0 -> X1 = (k1_setfam_1 X2) -> False)
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
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X2 X1, (X1 = (k1_setfam_1 X2) -> False) -> X2 = k1_xboole_0 -> X1 = k1_xboole_0 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_finset_1 esk17_0 -> False)
  -> (v1_finset_1 esk11_0 -> False)
  -> (v1_finset_1 esk1_0 -> False)
  -> (forall X1, (v3_ordinal1 (k1_setfam_1 (k2_ordinal1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((r2_hidden esk2_0 esk1_0 -> False) -> False)
  -> ((v1_card_lar esk3_0 esk1_0 -> False) -> False)
  -> ((v5_card_3 esk21_0 -> False) -> False)
  -> ((v7_ordinal1 esk22_0 -> False) -> False)
  -> ((v7_ordinal1 esk19_0 -> False) -> False)
  -> ((v2_ordinal1 esk15_0 -> False) -> False)
  -> ((v2_ordinal1 esk14_0 -> False) -> False)
  -> ((v2_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_ordinal1 esk15_0 -> False) -> False)
  -> ((v1_ordinal1 esk14_0 -> False) -> False)
  -> ((v1_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_card_1 esk14_0 -> False) -> False)
  -> ((v1_card_1 esk11_0 -> False) -> False)
  -> ((v1_card_1 esk10_0 -> False) -> False)
  -> ((v1_finset_1 esk14_0 -> False) -> False)
  -> ((v4_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 esk15_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk2_0 -> False) -> False)
  -> ((v3_ordinal1 esk1_0 -> False) -> False)
  -> False.
Admitted.
