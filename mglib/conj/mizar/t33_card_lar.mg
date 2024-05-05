(** $I sig/MizarPreamble.mgs **)

Theorem t33_card_lar:
 forall r2_hidden:set -> set -> prop,
 forall k1_card_5:set -> set,
 forall esk3_2:set -> set -> set,
 forall r2_ordinal2:set -> set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall esk4_2:set -> set -> set,
 forall esk22_1:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall r2_xboole_0:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk12_1:set -> set,
 forall esk16_1:set -> set,
 forall v2_ordinal1:set -> prop,
 forall v4_ordinal1:set -> prop,
 forall v5_card_3:set -> prop,
 forall esk20_0:set,
 forall esk13_0:set,
 forall esk8_0:set,
 forall esk10_0:set,
 forall esk9_0:set,
 forall esk7_0:set,
 forall esk11_0:set,
 forall esk17_0:set,
 forall esk19_0:set,
 forall esk5_1:set -> set,
 forall esk15_0:set,
 forall esk14_0:set,
 forall v5_ordinal1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall esk18_1:set -> set,
 forall v3_card_1:set -> set -> prop,
 forall v4_card_3:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk6_2:set -> set -> set,
 forall a_1_3_card_lar:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k3_ordinal2:set -> set,
 forall esk21_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall k2_card_2:set -> set -> set,
 forall esk23_3:set -> set -> set -> set,
 forall r1_ordinal1:set -> set -> prop,
 forall k1_card_1:set -> set,
 forall v1_card_1:set -> prop,
     (forall X1 X3 X2, (r1_ordinal1 (k1_card_1 (k3_tarski X3)) (k2_card_2 X1 X2) -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> r1_ordinal1 (k1_card_1 X3) X1 -> r1_ordinal1 (k1_card_1 (esk23_3 X1 X2 X3)) X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden (esk23_3 X1 X2 X3) X3 -> False) -> (r1_ordinal1 (k1_card_1 (k3_tarski X3)) (k2_card_2 X1 X2) -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> r1_ordinal1 (k1_card_1 X3) X1 -> False)
  -> (forall X3 X1 X2 X4, (r1_ordinal1 (k2_card_2 X1 X2) (k2_card_2 X3 X4) -> False) -> v1_card_1 X4 -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r1_ordinal1 X2 X3 -> r1_ordinal1 X1 X4 -> False)
  -> (forall X3 X1 X2 X4, (r1_ordinal1 (k2_card_2 X1 X2) (k2_card_2 X3 X4) -> False) -> v1_card_1 X4 -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r1_ordinal1 X2 X4 -> r1_ordinal1 X1 X3 -> False)
  -> (forall X3 X1 X2 X4, (r1_ordinal1 (k2_card_2 X1 X2) (k2_card_2 X3 X4) -> False) -> v1_card_1 X4 -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r2_hidden X1 X3 -> r1_ordinal1 X2 X4 -> False)
  -> (forall X3 X1 X2 X4, (r1_ordinal1 (k2_card_2 X1 X2) (k2_card_2 X3 X4) -> False) -> v1_card_1 X4 -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r2_hidden X1 X4 -> r1_ordinal1 X2 X3 -> False)
  -> (forall X3 X1 X2 X4, (r1_ordinal1 (k2_card_2 X1 X2) (k2_card_2 X3 X4) -> False) -> v1_card_1 X4 -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r2_hidden X2 X3 -> r1_ordinal1 X1 X4 -> False)
  -> (forall X3 X1 X2 X4, (r1_ordinal1 (k2_card_2 X1 X2) (k2_card_2 X3 X4) -> False) -> v1_card_1 X4 -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r2_hidden X2 X3 -> r2_hidden X1 X4 -> False)
  -> (forall X3 X1 X2 X4, (r1_ordinal1 (k2_card_2 X1 X2) (k2_card_2 X3 X4) -> False) -> v1_card_1 X4 -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r2_hidden X2 X4 -> r1_ordinal1 X1 X3 -> False)
  -> (forall X3 X1 X2 X4, (r1_ordinal1 (k2_card_2 X1 X2) (k2_card_2 X3 X4) -> False) -> v1_card_1 X4 -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r2_hidden X2 X4 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden (k2_card_2 X1 X2) (k2_card_2 X3 X4) -> False) -> v1_card_1 X4 -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r2_hidden X2 X3 -> r2_hidden X1 X4 -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden (k2_card_2 X1 X2) (k2_card_2 X3 X4) -> False) -> v1_card_1 X4 -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r2_hidden X2 X4 -> r2_hidden X1 X3 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk21_2 X3 X2) -> False)
  -> (forall X1 X2, (X1 = (k1_card_5 X2) -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> r2_ordinal2 X2 X1 -> r1_ordinal1 X1 (esk3_2 X2 X1) -> False)
  -> (forall X1 X2, (r2_hidden (k3_ordinal2 X1) X2 -> False) -> v1_card_1 X2 -> r1_tarski X1 X2 -> r2_hidden (k1_card_1 X1) (k1_card_5 X2) -> False)
  -> (forall X1 X2, (r2_hidden (k3_tarski X1) X2 -> False) -> v1_card_1 X2 -> r1_tarski X1 X2 -> r2_hidden (k1_card_1 X1) (k1_card_5 X2) -> False)
  -> (forall X1 X2, (X2 = (k1_card_5 X1) -> False) -> (r2_ordinal2 X1 (esk3_2 X1 X2) -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> r2_ordinal2 X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v1_ordinal1 X1 -> r2_hidden X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X3 (a_1_3_card_lar X2) -> False) -> X3 = (k1_card_1 X1) -> r2_hidden X1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk6_2 X1 X2) X2 -> False) -> r2_hidden X1 (a_1_3_card_lar X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> r2_hidden X1 (a_1_3_card_lar X2) -> False)
  -> (forall X1 X2, (X2 = (k1_card_5 X1) -> False) -> (v1_card_1 (esk3_2 X1 X2) -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> r2_ordinal2 X1 X2 -> False)
  -> (forall X1 X2, (v1_card_1 (k3_tarski X2) -> False) -> v1_card_1 X1 -> r2_hidden X1 X2 -> r1_tarski (esk22_1 X2) X1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> v1_finset_1 (k2_card_2 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, ((k1_card_1 (esk6_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> r2_hidden X1 (a_1_3_card_lar X2) -> False)
  -> (forall X2 X3 X1, (r1_ordinal1 X3 X1 -> False) -> X3 = (k1_card_5 X2) -> v1_card_1 X3 -> v1_card_1 X2 -> v1_card_1 X1 -> r2_ordinal2 X2 X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk21_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk4_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (v1_card_1 (k2_card_2 X1 X2) -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r2_hidden X1 X2 -> False) -> v3_ordinal1 X2 -> v1_ordinal1 X1 -> r2_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_xboole_0 X2 X1 -> r2_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_card_1 (k2_card_2 X1 X2) -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> False)
  -> (forall X1 X2, (v4_card_3 X2 -> False) -> v4_card_3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r1_ordinal1 (k1_card_1 (a_1_3_card_lar X1)) (k1_card_1 X1) -> False) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_card_2 X1 X2) = (k2_card_2 X2 X1) -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> (r2_xboole_0 X1 X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (r2_hidden (k1_card_1 X1) esk2_0 -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, (r2_ordinal2 X1 X2 -> False) -> X2 = (k1_card_5 X1) -> v1_card_1 X2 -> v1_card_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (m1_subset_1 (esk12_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> v1_card_1 X1 -> v1_finset_1 (esk12_1 X1) -> False)
  -> (forall X1, (v1_card_1 (k3_tarski X1) -> False) -> (r2_hidden (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_ordinal2 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_card_1 X1 -> v1_finset_1 (k1_card_5 X1) -> False)
  -> (forall X1, (v3_card_1 (esk18_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v2_ordinal1 (esk12_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v1_ordinal1 (esk12_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v3_ordinal1 (esk12_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v1_card_1 (esk12_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, ((k2_card_2 X1 X1) = X1 -> False) -> (v1_finset_1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X2 X1, X1 = X2 -> r2_xboole_0 X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_finset_1 X1 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_ordinal1 X1 -> False) -> v1_card_1 X1 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_1 (k1_card_5 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k1_card_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk16_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_card_1 X1) -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_finset_1 X1 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k1_card_1 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k3_tarski X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 (k1_card_5 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_card_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_3 X1 -> False) -> v4_card_3 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> (forall X1, v1_finset_1 X1 -> v5_card_3 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v5_card_3 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_hidden (k1_card_1 (k3_tarski esk1_0)) esk2_0 -> False)
  -> (forall X1, r2_xboole_0 X1 X1 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_finset_1 esk15_0 -> False)
  -> (v1_finset_1 esk8_0 -> False)
  -> (v1_finset_1 esk2_0 -> False)
  -> ((r2_hidden (k1_card_1 esk1_0) (k1_card_5 esk2_0) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k1_card_1 (k1_card_1 X1)) = (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (r1_tarski k1_xboole_0 X1 -> False) -> False)
  -> (forall X1, (v3_ordinal1 (k3_ordinal2 X1) -> False) -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> ((v5_card_3 esk19_0 -> False) -> False)
  -> ((v7_ordinal1 esk20_0 -> False) -> False)
  -> ((v7_ordinal1 esk17_0 -> False) -> False)
  -> ((v2_ordinal1 esk13_0 -> False) -> False)
  -> ((v2_ordinal1 esk11_0 -> False) -> False)
  -> ((v2_ordinal1 esk8_0 -> False) -> False)
  -> ((v1_ordinal1 esk13_0 -> False) -> False)
  -> ((v1_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_ordinal1 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk9_0 -> False) -> False)
  -> ((v3_ordinal1 esk8_0 -> False) -> False)
  -> ((v1_card_1 esk11_0 -> False) -> False)
  -> ((v1_card_1 esk8_0 -> False) -> False)
  -> ((v1_card_1 esk7_0 -> False) -> False)
  -> ((v1_card_1 esk2_0 -> False) -> False)
  -> ((v1_finset_1 esk11_0 -> False) -> False)
  -> (((k3_tarski k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (((k1_card_1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
