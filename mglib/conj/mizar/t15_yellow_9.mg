(** $I sig/MizarPreamble.mgs **)

Theorem t15_yellow_9:
 forall r1_tarski:set -> set -> prop,
 forall esk3_4:set -> set -> set -> set -> set,
 forall k1_cantor_1:set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk11_2:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall esk46_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall esk42_1:set -> set,
 forall esk41_1:set -> set,
 forall esk34_1:set -> set,
 forall esk18_1:set -> set,
 forall v1_card_1:set -> prop,
 forall v3_card_1:set -> set -> prop,
 forall esk39_1:set -> set,
 forall np__1:set,
 forall v2_funct_1:set -> prop,
 forall k1_xboole_0:set,
 forall v2_relat_1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk27_0:set,
 forall esk45_0:set,
 forall esk43_0:set,
 forall esk32_0:set,
 forall esk26_0:set,
 forall esk17_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall v2_xxreal_0:set -> prop,
 forall esk29_0:set,
 forall esk22_0:set,
 forall esk13_0:set,
 forall esk19_0:set,
 forall o_0_0_xboole_0:set,
 forall esk16_0:set,
 forall esk20_0:set,
 forall esk15_0:set,
 forall esk33_0:set,
 forall esk24_0:set,
 forall v2_card_1:set -> prop,
 forall esk10_1:set -> set,
 forall esk25_1:set -> set,
 forall esk14_0:set,
 forall esk23_0:set,
 forall esk28_0:set,
 forall esk37_0:set,
 forall esk44_0:set,
 forall esk36_0:set,
 forall esk30_1:set -> set,
 forall v5_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v2_finset_1:set -> prop,
 forall k4_ordinal1:set,
 forall v7_ordinal1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall esk35_1:set -> set,
 forall esk21_1:set -> set,
 forall esk38_1:set -> set,
 forall esk40_1:set -> set,
 forall esk31_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v5_finset_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_3_0_yellow_9:set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk12_4:set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
     (forall X4 X1 X3 X2, (m1_subset_1 (esk12_4 X1 X2 X3 X4) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_3_0_yellow_9 X2 X3 X4) -> False)
  -> (forall X4 X1 X3 X2, (r1_tarski (esk12_4 X1 X2 X3 X4) X4 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_3_0_yellow_9 X2 X3 X4) -> False)
  -> (forall X4 X1 X3 X2, (r2_hidden (esk12_4 X1 X2 X3 X4) X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_3_0_yellow_9 X2 X3 X4) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (esk3_4 X1 X2 X3 X4) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> X3 = (k1_cantor_1 X1 X2) -> r2_hidden X4 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2 X3 X4, ((k5_setfam_1 X2 (esk3_4 X2 X3 X4 X1)) = X1 -> False) -> X4 = (k1_cantor_1 X2 X3) -> r2_hidden X1 X4 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X4 X1 X2 X3, (r1_tarski (esk3_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k1_cantor_1 X1 X2) -> r2_hidden X4 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k1_cantor_1 X1 X2) -> False) -> (esk4_3 X1 X2 X3) = (k5_setfam_1 X1 X4) -> r1_tarski X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> False)
  -> (forall X4 X1 X3 X2, ((esk12_4 X1 X2 X3 X4) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_3_0_yellow_9 X2 X3 X4) -> False)
  -> (forall X3 X1 X2, (X3 = (k1_cantor_1 X1 X2) -> False) -> ((k5_setfam_1 X1 (esk5_3 X1 X2 X3)) = (esk4_3 X1 X2 X3) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (X3 = (k1_cantor_1 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> (m1_subset_1 (esk5_3 X1 X2 X3) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (X3 = (k1_cantor_1 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> (r1_tarski (esk5_3 X1 X2 X3) X2 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1 X4 X5, (r2_hidden X4 X5 -> False) -> X5 = (k1_cantor_1 X2 X3) -> X4 = (k5_setfam_1 X2 X1) -> r1_tarski X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X5 X4 X2 X3, (r2_hidden X3 (a_3_0_yellow_9 X2 X4 X5) -> False) -> X1 = X3 -> r2_hidden X1 X4 -> r1_tarski X1 X5 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X1 X2, (X3 = (k1_cantor_1 X1 X2) -> False) -> (m1_subset_1 (esk4_3 X1 X2 X3) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk8_2 X1 X2) X3 -> r2_hidden (esk8_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk7_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk11_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> (r2_hidden (esk8_2 X1 X2) (esk9_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_cantor_1 X2 X1) (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk46_2 X3 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 (k1_cantor_1 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk46_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk42_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk40_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk41_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk38_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_card_1 (esk39_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk35_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_zfmisc_1 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_zfmisc_1 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (k3_tarski X1) -> False) -> v1_finset_1 X1 -> v5_finset_1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk41_1 X1) np__1 -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk31_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk42_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk40_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk38_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (esk39_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (esk39_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k3_tarski X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk42_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk21_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk38_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k1_cantor_1 esk1_0 (k1_cantor_1 esk1_0 esk2_0)) = (k1_cantor_1 esk1_0 esk2_0) -> False)
  -> (forall X1, v1_subset_1 (esk30_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk36_0 -> False)
  -> (v1_finset_1 esk27_0 -> False)
  -> (v1_finset_1 k4_ordinal1 -> False)
  -> (v1_xboole_0 esk45_0 -> False)
  -> (v1_xboole_0 esk44_0 -> False)
  -> (v1_xboole_0 esk43_0 -> False)
  -> (v1_xboole_0 esk37_0 -> False)
  -> (v1_xboole_0 esk32_0 -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk25_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v2_card_1 k4_ordinal1 -> False) -> False)
  -> ((v2_finset_1 esk45_0 -> False) -> False)
  -> ((v4_funct_1 esk43_0 -> False) -> False)
  -> ((v5_finset_1 esk44_0 -> False) -> False)
  -> ((v2_relat_1 esk32_0 -> False) -> False)
  -> ((v2_relat_1 esk29_0 -> False) -> False)
  -> ((v2_relat_1 esk24_0 -> False) -> False)
  -> ((v7_ordinal1 esk37_0 -> False) -> False)
  -> ((v7_ordinal1 esk33_0 -> False) -> False)
  -> ((v2_funct_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk45_0 -> False) -> False)
  -> ((v1_relat_1 esk36_0 -> False) -> False)
  -> ((v1_relat_1 esk32_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk28_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v2_ordinal1 esk23_0 -> False) -> False)
  -> ((v2_ordinal1 esk20_0 -> False) -> False)
  -> ((v1_ordinal1 esk23_0 -> False) -> False)
  -> ((v1_ordinal1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk45_0 -> False) -> False)
  -> ((v1_funct_1 esk36_0 -> False) -> False)
  -> ((v1_funct_1 esk32_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk28_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((v1_finset_1 esk44_0 -> False) -> False)
  -> ((v1_finset_1 esk28_0 -> False) -> False)
  -> ((v1_finset_1 esk20_0 -> False) -> False)
  -> ((v1_finset_1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk23_0 -> False) -> False)
  -> ((v3_ordinal1 esk20_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_card_1 esk20_0 -> False) -> False)
  -> ((v1_card_1 esk13_0 -> False) -> False)
  -> ((v1_card_1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk19_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
