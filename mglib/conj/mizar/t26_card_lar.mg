(** $I sig/MizarPreamble.mgs **)

Theorem t26_card_lar:
 forall v1_finset_1:set -> prop,
 forall v1_card_1:set -> prop,
 forall esk4_2:set -> set -> set,
 forall a_1_2_card_lar:set -> set,
 forall v4_card_3:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall v6_card_fil:set -> prop,
 forall v5_card_lar:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk12_1:set -> set,
 forall v3_card_1:set -> set -> prop,
 forall esk17_1:set -> set,
 forall v1_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall v2_card_1:set -> prop,
 forall v5_card_3:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall esk11_0:set,
 forall esk14_0:set,
 forall esk7_0:set,
 forall esk15_0:set,
 forall esk18_0:set,
 forall esk16_0:set,
 forall esk10_0:set,
 forall esk9_0:set,
 forall esk8_0:set,
 forall esk5_0:set,
 forall esk2_1:set -> set,
 forall esk6_0:set,
 forall esk1_0:set,
 forall esk13_0:set,
 forall esk19_0:set,
 forall v6_ordinal1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v4_card_fil:set -> prop,
 forall v5_card_fil:set -> prop,
 forall v4_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall r4_card_lar:set -> set -> prop,
 forall v4_card_lar:set -> prop,
 forall v1_card_5:set -> prop,
 forall a_1_1_card_lar:set -> set,
 forall esk3_2:set -> set -> set,
 forall esk20_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk20_2 X3 X2) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> v1_card_1 X2 -> v1_finset_1 (esk4_2 X1 X2) -> r2_hidden X1 (a_1_2_card_lar X2) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> v1_card_1 X2 -> v1_finset_1 (esk3_2 X1 X2) -> r2_hidden X1 (a_1_1_card_lar X2) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> (m1_subset_1 (esk4_2 X1 X2) X2 -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_2_card_lar X2) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> (m1_subset_1 (esk3_2 X1 X2) X2 -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_1_card_lar X2) -> False)
  -> (forall X1 X3 X2, (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (v4_card_3 X2 -> False) -> (r2_hidden X3 (a_1_2_card_lar X2) -> False) -> X1 = X3 -> v1_card_1 X2 -> v1_card_1 X1 -> v6_card_fil X1 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v1_finset_1 X2 -> False) -> (v1_finset_1 X1 -> False) -> (v4_card_3 X2 -> False) -> (r2_hidden X3 (a_1_1_card_lar X2) -> False) -> X1 = X3 -> v1_card_1 X2 -> v1_card_1 X1 -> v1_card_5 X1 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> (v6_card_fil (esk4_2 X1 X2) -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_2_card_lar X2) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> (v1_card_5 (esk3_2 X1 X2) -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_1_card_lar X2) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> (v1_card_1 (esk4_2 X1 X2) -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_2_card_lar X2) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> (v1_card_1 (esk3_2 X1 X2) -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_1_card_lar X2) -> False)
  -> (forall X1 X2, ((esk4_2 X1 X2) = X1 -> False) -> (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_2_card_lar X2) -> False)
  -> (forall X1 X2, ((esk3_2 X1 X2) = X1 -> False) -> (v1_finset_1 X2 -> False) -> (v4_card_3 X2 -> False) -> v1_card_1 X2 -> r2_hidden X1 (a_1_1_card_lar X2) -> False)
  -> (forall X2 X1, (r2_hidden (esk20_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v4_card_lar X1 -> False) -> v1_card_1 X1 -> r4_card_lar X1 (a_1_1_card_lar X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v5_card_lar X1 -> False) -> v1_card_1 X1 -> r4_card_lar X1 (a_1_2_card_lar X1) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (r4_card_lar X1 (a_1_2_card_lar X1) -> False) -> v1_card_1 X1 -> v5_card_lar X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (r4_card_lar X1 (a_1_1_card_lar X1) -> False) -> v1_card_1 X1 -> v4_card_lar X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (m1_subset_1 (esk12_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> v1_card_1 X1 -> v1_finset_1 (esk12_1 X1) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_card_1 (esk17_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v2_ordinal1 (esk12_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v1_ordinal1 (esk12_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v3_ordinal1 (esk12_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_3 X1 -> False) -> (v1_card_1 (esk12_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_finset_1 X1 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_fil X1 -> False) -> v1_card_1 X1 -> v6_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> v6_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> v4_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v5_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v4_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> v1_card_1 X1 -> v4_card_3 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_card_fil X1 -> False) -> v1_card_1 X1 -> v6_card_fil X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_ordinal1 X1 -> False) -> v1_card_1 X1 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v2_card_1 X1 -> False) -> (v1_card_5 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_finset_1 X1 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_3 X1 -> False) -> v4_card_3 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v4_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_finset_1 X1 -> v5_card_3 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v5_card_3 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v2_card_1 esk11_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 esk7_0 -> False)
  -> (v4_card_lar esk1_0 -> False)
  -> (v4_card_3 esk7_0 -> False)
  -> (v4_card_3 esk1_0 -> False)
  -> (v1_finset_1 esk15_0 -> False)
  -> (v1_finset_1 esk11_0 -> False)
  -> (v1_finset_1 esk7_0 -> False)
  -> (v1_finset_1 esk6_0 -> False)
  -> (v1_finset_1 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk2_1 X1) X1 -> False) -> False)
  -> ((v5_card_3 esk18_0 -> False) -> False)
  -> ((v7_ordinal1 esk19_0 -> False) -> False)
  -> ((v7_ordinal1 esk16_0 -> False) -> False)
  -> ((v1_card_5 esk7_0 -> False) -> False)
  -> ((v2_ordinal1 esk13_0 -> False) -> False)
  -> ((v2_ordinal1 esk11_0 -> False) -> False)
  -> ((v2_ordinal1 esk10_0 -> False) -> False)
  -> ((v2_ordinal1 esk7_0 -> False) -> False)
  -> ((v2_ordinal1 esk6_0 -> False) -> False)
  -> ((v1_ordinal1 esk13_0 -> False) -> False)
  -> ((v1_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_ordinal1 esk10_0 -> False) -> False)
  -> ((v1_ordinal1 esk7_0 -> False) -> False)
  -> ((v1_ordinal1 esk6_0 -> False) -> False)
  -> ((v1_xboole_0 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v4_ordinal1 esk7_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 esk8_0 -> False) -> False)
  -> ((v3_ordinal1 esk7_0 -> False) -> False)
  -> ((v3_ordinal1 esk6_0 -> False) -> False)
  -> ((v5_card_lar esk1_0 -> False) -> False)
  -> ((v1_card_1 esk11_0 -> False) -> False)
  -> ((v1_card_1 esk10_0 -> False) -> False)
  -> ((v1_card_1 esk7_0 -> False) -> False)
  -> ((v1_card_1 esk6_0 -> False) -> False)
  -> ((v1_card_1 esk5_0 -> False) -> False)
  -> ((v1_card_1 esk1_0 -> False) -> False)
  -> ((v1_finset_1 esk10_0 -> False) -> False)
  -> False.
Admitted.
