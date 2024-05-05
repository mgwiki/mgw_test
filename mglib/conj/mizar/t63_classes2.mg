(** $I sig/MizarPreamble.mgs **)

Theorem t63_classes2:
 forall v4_ordinal1:set -> prop,
 forall esk38_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk40_2:set -> set -> set,
 forall esk39_2:set -> set -> set,
 forall v1_ordinal1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall r2_wellord2:set -> set -> prop,
 forall esk2_1:set -> set,
 forall esk21_1:set -> set,
 forall esk29_1:set -> set,
 forall esk27_1:set -> set,
 forall esk11_1:set -> set,
 forall esk24_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk19_0:set,
 forall esk31_0:set,
 forall esk18_0:set,
 forall esk8_0:set,
 forall esk17_1:set -> set,
 forall v2_xxreal_0:set -> prop,
 forall v2_card_1:set -> prop,
 forall esk13_0:set,
 forall esk22_0:set,
 forall esk9_0:set,
 forall esk7_0:set,
 forall esk12_0:set,
 forall o_0_0_xboole_0:set,
 forall esk10_0:set,
 forall esk15_0:set,
 forall esk5_1:set -> set,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall k6_numbers:set,
 forall esk16_0:set,
 forall esk26_0:set,
 forall esk25_0:set,
 forall esk20_1:set -> set,
 forall v5_ordinal1:set -> prop,
 forall k4_ordinal1:set,
 forall v2_funct_1:set -> prop,
 forall np__1:set,
 forall esk28_1:set -> set,
 forall v3_card_1:set -> set -> prop,
 forall esk23_1:set -> set,
 forall esk30_1:set -> set,
 forall esk1_1:set -> set,
 forall v1_classes2:set -> prop,
 forall esk14_1:set -> set,
 forall v6_ordinal1:set -> prop,
 forall k1_card_1:set -> set,
 forall v1_card_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v1_classes1:set -> prop,
 forall esk3_1:set -> set,
 forall r2_tarski:set -> set -> prop,
 forall esk4_1:set -> set,
 forall v2_classes1:set -> prop,
 forall esk6_2:set -> set -> set,
 forall v3_ordinal1:set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k4_classes1:set -> set,
 forall esk35_1:set -> set,
 forall r1_ordinal1:set -> set -> prop,
 forall esk37_1:set -> set,
 forall k6_classes1:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk33_1:set -> set,
 forall esk32_1:set -> set,
 forall esk36_1:set -> set,
 forall esk34_1:set -> set,
 forall v1_finset_1:set -> prop,
 forall k1_xboole_0:set,
     (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal1 (k6_classes1 X1) (k6_classes1 (esk37_1 X2)) -> False) -> v1_finset_1 X2 -> r2_hidden X1 X2 -> r1_ordinal1 (k6_classes1 (esk33_1 X2)) (k6_classes1 (esk32_1 X2)) -> r1_ordinal1 (k6_classes1 (esk36_1 X2)) (k6_classes1 (esk34_1 X2)) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal1 (k6_classes1 X1) (k6_classes1 (esk37_1 X2)) -> False) -> v1_finset_1 X2 -> r2_hidden X1 X2 -> r1_ordinal1 (k6_classes1 (esk32_1 X2)) (k6_classes1 (esk33_1 X2)) -> r1_ordinal1 (k6_classes1 (esk36_1 X2)) (k6_classes1 (esk34_1 X2)) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal1 (k6_classes1 X1) (k6_classes1 (esk37_1 X2)) -> False) -> (r1_ordinal1 (k6_classes1 (esk36_1 X2)) (k6_classes1 (esk35_1 X2)) -> False) -> v1_finset_1 X2 -> r2_hidden X1 X2 -> r1_ordinal1 (k6_classes1 (esk33_1 X2)) (k6_classes1 (esk32_1 X2)) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal1 (k6_classes1 X1) (k6_classes1 (esk37_1 X2)) -> False) -> (r1_ordinal1 (k6_classes1 (esk36_1 X2)) (k6_classes1 (esk35_1 X2)) -> False) -> v1_finset_1 X2 -> r2_hidden X1 X2 -> r1_ordinal1 (k6_classes1 (esk32_1 X2)) (k6_classes1 (esk33_1 X2)) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal1 (k6_classes1 X1) (k6_classes1 (esk37_1 X2)) -> False) -> (r1_ordinal1 (k6_classes1 (esk35_1 X2)) (k6_classes1 (esk34_1 X2)) -> False) -> v1_finset_1 X2 -> r2_hidden X1 X2 -> r1_ordinal1 (k6_classes1 (esk33_1 X2)) (k6_classes1 (esk32_1 X2)) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal1 (k6_classes1 X1) (k6_classes1 (esk37_1 X2)) -> False) -> (r1_ordinal1 (k6_classes1 (esk35_1 X2)) (k6_classes1 (esk34_1 X2)) -> False) -> v1_finset_1 X2 -> r2_hidden X1 X2 -> r1_ordinal1 (k6_classes1 (esk32_1 X2)) (k6_classes1 (esk33_1 X2)) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk37_1 X1) X1 -> False) -> v1_finset_1 X1 -> r1_ordinal1 (k6_classes1 (esk33_1 X1)) (k6_classes1 (esk32_1 X1)) -> r1_ordinal1 (k6_classes1 (esk36_1 X1)) (k6_classes1 (esk34_1 X1)) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk37_1 X1) X1 -> False) -> v1_finset_1 X1 -> r1_ordinal1 (k6_classes1 (esk32_1 X1)) (k6_classes1 (esk33_1 X1)) -> r1_ordinal1 (k6_classes1 (esk36_1 X1)) (k6_classes1 (esk34_1 X1)) -> False)
  -> (forall X1 X2, (r2_hidden X1 (k4_classes1 X2) -> False) -> v3_ordinal1 X2 -> r2_hidden (k1_zfmisc_1 X1) (k4_classes1 (k2_xboole_0 X2 (k1_tarski X2))) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk37_1 X1) X1 -> False) -> (r1_ordinal1 (k6_classes1 (esk36_1 X1)) (k6_classes1 (esk35_1 X1)) -> False) -> v1_finset_1 X1 -> r1_ordinal1 (k6_classes1 (esk33_1 X1)) (k6_classes1 (esk32_1 X1)) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk37_1 X1) X1 -> False) -> (r1_ordinal1 (k6_classes1 (esk36_1 X1)) (k6_classes1 (esk35_1 X1)) -> False) -> v1_finset_1 X1 -> r1_ordinal1 (k6_classes1 (esk32_1 X1)) (k6_classes1 (esk33_1 X1)) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk37_1 X1) X1 -> False) -> (r1_ordinal1 (k6_classes1 (esk35_1 X1)) (k6_classes1 (esk34_1 X1)) -> False) -> v1_finset_1 X1 -> r1_ordinal1 (k6_classes1 (esk33_1 X1)) (k6_classes1 (esk32_1 X1)) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk37_1 X1) X1 -> False) -> (r1_ordinal1 (k6_classes1 (esk35_1 X1)) (k6_classes1 (esk34_1 X1)) -> False) -> v1_finset_1 X1 -> r1_ordinal1 (k6_classes1 (esk32_1 X1)) (k6_classes1 (esk33_1 X1)) -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> r2_hidden (k2_xboole_0 (esk38_1 X1) (k1_tarski (esk38_1 X1))) X1 -> False)
  -> (forall X1 X2, (r2_hidden (k1_zfmisc_1 X1) (k4_classes1 (k2_xboole_0 X2 (k1_tarski X2))) -> False) -> v3_ordinal1 X2 -> r2_hidden X1 (k4_classes1 X2) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (r1_ordinal1 (k6_classes1 X1) X2 -> False) -> v3_ordinal1 X2 -> r2_hidden (k6_classes1 (esk40_2 X1 X2)) X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk6_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 (k4_classes1 (esk39_2 X2 X1)) -> False) -> v3_ordinal1 X2 -> v4_ordinal1 X2 -> r2_hidden X1 (k4_classes1 X2) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X2)) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X3 (k4_classes1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X2 -> r2_hidden X1 X2 -> r2_hidden X3 (k4_classes1 X1) -> False)
  -> (forall X1 X2, (r2_hidden (k2_xboole_0 X2 (k1_tarski X2)) X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> v1_classes1 X1 -> r2_tarski (esk4_1 X1) X1 -> r2_hidden (k1_zfmisc_1 (esk3_1 X1)) X1 -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> v1_classes1 X1 -> r2_hidden (esk4_1 X1) X1 -> r2_hidden (k1_zfmisc_1 (esk3_1 X1)) X1 -> False)
  -> (forall X1 X2, (r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X2)) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk39_2 X1 X2) X1 -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 (k4_classes1 X1) -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> (r1_tarski (esk4_1 X1) X1 -> False) -> v1_classes1 X1 -> r2_hidden (k1_zfmisc_1 (esk3_1 X1)) X1 -> False)
  -> (forall X1 X3 X2, (r2_hidden (k6_classes1 X3) X2 -> False) -> v3_ordinal1 X2 -> r2_hidden X3 X1 -> r1_ordinal1 (k6_classes1 X1) X2 -> False)
  -> (forall X3 X2 X1, (r2_hidden X2 (k4_classes1 X1) -> False) -> v3_ordinal1 X1 -> r1_tarski X2 X3 -> r2_hidden X3 (k4_classes1 X1) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v1_ordinal1 X1 -> r2_hidden X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (v3_ordinal1 (esk39_2 X1 X2) -> False) -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> r2_hidden X2 (k4_classes1 X1) -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r1_ordinal1 (k6_classes1 X1) X2 -> False) -> (r2_hidden (esk40_2 X1 X2) X1 -> False) -> v3_ordinal1 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> v1_classes1 X1 -> r2_hidden X2 X1 -> r1_tarski X3 X2 -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> (r2_hidden (esk3_1 X1) X1 -> False) -> v1_classes1 X1 -> r2_tarski (esk4_1 X1) X1 -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> (r2_hidden (esk3_1 X1) X1 -> False) -> v1_classes1 X1 -> r2_hidden (esk4_1 X1) X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r2_hidden (k6_classes1 X1) X2 -> False) -> v3_ordinal1 X2 -> r2_hidden X1 (k4_classes1 X2) -> False)
  -> (forall X1 X2, (r2_hidden X1 (k4_classes1 X2) -> False) -> v3_ordinal1 X2 -> r2_hidden (k6_classes1 X1) X2 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r2_hidden X1 X2 -> False) -> (r2_tarski X1 X2 -> False) -> v2_classes1 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden X1 X2 -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> (r2_hidden (esk3_1 X1) X1 -> False) -> (r1_tarski (esk4_1 X1) X1 -> False) -> v1_classes1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v1_card_1 X2 -> v1_card_1 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r2_hidden (k1_zfmisc_1 X1) X2 -> False) -> v2_classes1 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_ordinal1 (k1_card_1 X1) (k1_card_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, X1 = X2 -> v1_card_1 X2 -> v1_card_1 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> r2_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X2 X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (r2_tarski X1 X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> r2_hidden (esk2_1 X1) X1 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (r2_hidden (esk38_1 X1) X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) X1 -> False) -> v1_classes2 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> (r1_tarski (esk2_1 X1) (esk1_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, ((k1_card_1 X1) = (k1_card_1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_classes2 X1 -> v1_xboole_0 (esk14_1 X1) -> False)
  -> (forall X1, (v3_card_1 (esk28_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk24_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (r1_tarski X1 (k4_classes1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> (k1_card_1 X1) = (k1_card_1 X2) -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_zfmisc_1 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_zfmisc_1 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> (r2_hidden (esk1_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk30_1 X1) np__1 -> False) -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v3_ordinal1 (esk38_1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk21_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_card_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk29_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk11_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k1_card_1 X1) -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_classes2 X1 -> False) -> v2_classes1 X1 -> v1_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_card_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (esk28_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_ordinal1 (k4_classes1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_funct_1 (esk28_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k1_card_1 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v1_classes2 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> v2_classes1 X1 -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> v2_classes1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_classes1 X1 -> False) -> v1_classes2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1, v1_subset_1 (esk20_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v2_classes1 (k4_classes1 k4_ordinal1) -> False)
  -> (v3_funct_1 esk25_0 -> False)
  -> (v1_finset_1 esk19_0 -> False)
  -> (v1_finset_1 k4_ordinal1 -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk8_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) X1 -> False) -> False)
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
  -> (forall X1, (v1_xboole_0 (esk17_1 X1) -> False) -> False)
  -> (((k1_card_1 (k4_classes1 k4_ordinal1)) = (k1_card_1 k4_ordinal1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v4_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v2_card_1 k4_ordinal1 -> False) -> False)
  -> ((v4_funct_1 esk31_0 -> False) -> False)
  -> ((v1_finset_1 esk13_0 -> False) -> False)
  -> ((v7_ordinal1 esk26_0 -> False) -> False)
  -> ((v7_ordinal1 esk22_0 -> False) -> False)
  -> ((v2_funct_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk9_0 -> False) -> False)
  -> ((v1_classes2 esk8_0 -> False) -> False)
  -> ((v2_ordinal1 esk16_0 -> False) -> False)
  -> ((v2_ordinal1 esk13_0 -> False) -> False)
  -> ((v1_ordinal1 esk16_0 -> False) -> False)
  -> ((v1_ordinal1 esk13_0 -> False) -> False)
  -> ((v1_funct_1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((v1_funct_1 esk9_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_card_1 esk13_0 -> False) -> False)
  -> ((v1_card_1 esk7_0 -> False) -> False)
  -> ((v1_card_1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> (((k1_card_1 k4_ordinal1) = k4_ordinal1 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
