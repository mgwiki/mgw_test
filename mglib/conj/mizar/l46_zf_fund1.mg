(** $I sig/MizarPreamble.mgs **)

Theorem l46_zf_fund1:
 forall v1_relat_1:set -> prop,
 forall esk5_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk9_2:set -> set -> set,
 forall v2_relat_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v2_finset_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v5_finset_1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall esk35_1:set -> set,
 forall esk18_1:set -> set,
 forall esk30_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall k4_ordinal1:set,
 forall k1_xboole_0:set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk23_0:set,
 forall esk38_0:set,
 forall esk36_0:set,
 forall esk27_0:set,
 forall esk20_0:set,
 forall esk11_0:set,
 forall v1_xtuple_0:set -> prop,
 forall esk8_1:set -> set,
 forall v2_xxreal_0:set -> prop,
 forall esk22_0:set,
 forall v2_card_1:set -> prop,
 forall esk25_0:set,
 forall esk19_0:set,
 forall esk13_0:set,
 forall o_0_0_xboole_0:set,
 forall esk12_0:set,
 forall esk10_0:set,
 forall esk17_0:set,
 forall esk15_0:set,
 forall esk28_0:set,
 forall esk21_0:set,
 forall esk29_0:set,
 forall esk16_0:set,
 forall k5_numbers:set,
 forall esk14_0:set,
 forall esk24_0:set,
 forall esk32_0:set,
 forall esk37_0:set,
 forall esk31_0:set,
 forall v1_xcmplx_0:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall k1_numbers:set,
 forall v1_xreal_0:set -> prop,
 forall v2_funct_1:set -> prop,
 forall np__1:set,
 forall esk33_1:set -> set,
 forall esk34_1:set -> set,
 forall esk26_1:set -> set,
 forall v3_ordinal1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_card_1:set -> prop,
 forall v3_card_1:set -> set -> prop,
 forall esk6_1:set -> set,
 forall v1_funct_1:set -> prop,
 forall esk7_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k2_tarski:set -> set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall k9_xtuple_0:set -> set,
     ((k2_tarski esk1_0 esk2_0) = (k9_xtuple_0 esk3_0) -> (k2_tarski (k2_tarski (k2_tarski esk1_0 (k1_funct_1 esk3_0 esk1_0)) (k1_tarski esk1_0)) (k2_tarski (k2_tarski esk2_0 (k1_funct_1 esk3_0 esk2_0)) (k1_tarski esk2_0))) = esk3_0 -> False)
  -> (((k2_tarski esk1_0 esk2_0) = (k9_xtuple_0 esk3_0) -> False) -> ((k2_tarski (k2_tarski (k2_tarski esk1_0 (k1_funct_1 esk3_0 esk1_0)) (k1_tarski esk1_0)) (k2_tarski (k2_tarski esk2_0 (k1_funct_1 esk3_0 esk2_0)) (k1_tarski esk2_0))) = esk3_0 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> (esk7_3 X1 X2 X3) = X1 -> r2_hidden (esk7_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> (esk7_3 X1 X2 X3) = X2 -> r2_hidden (esk7_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> ((esk7_3 X1 X2 X3) = X2 -> False) -> ((esk7_3 X1 X2 X3) = X1 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X2 X1, ((k2_tarski (k2_tarski (esk4_2 X1 X2) (esk5_2 X1 X2)) (k1_tarski (esk4_2 X1 X2))) = X2 -> False) -> v1_relat_1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k9_xtuple_0 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) X2 -> False)
  -> (forall X1 X3 X2, (X1 = (k1_funct_1 X2 X3) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) X2 -> False)
  -> (forall X3 X1 X2, (r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) X2 -> False) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) = (k2_tarski (k2_tarski X2 X4) (k1_tarski X2)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) = (k2_tarski (k2_tarski X4 X2) (k1_tarski X4)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk9_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> (esk6_1 X1) = (k2_tarski (k2_tarski X2 X3) (k1_tarski X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v3_card_1 (k9_xtuple_0 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v1_card_1 X1 -> v3_card_1 X2 X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> (X1 = X3 -> False) -> X2 = (k2_tarski X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v5_finset_1 (k2_tarski X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X2 X4) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X4 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_card_1 (esk33_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk30_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> (r2_hidden (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk34_1 X1) np__1 -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk26_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk35_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_tarski X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 (esk33_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (esk33_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
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
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v3_funct_1 esk31_0 -> False)
  -> (v1_finset_1 esk23_0 -> False)
  -> (v1_finset_1 k4_ordinal1 -> False)
  -> (v1_xboole_0 esk38_0 -> False)
  -> (v1_xboole_0 esk37_0 -> False)
  -> (v1_xboole_0 esk36_0 -> False)
  -> (v1_xboole_0 esk32_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (k2_tarski X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_card_1 (k1_tarski X1) np__1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> (forall X1, (v1_finset_1 (k1_tarski X1) -> False) -> False)
  -> ((v2_xxreal_0 esk22_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v2_card_1 k4_ordinal1 -> False) -> False)
  -> ((v1_xtuple_0 esk16_0 -> False) -> False)
  -> ((v2_finset_1 esk38_0 -> False) -> False)
  -> ((v4_funct_1 esk36_0 -> False) -> False)
  -> ((v5_finset_1 esk37_0 -> False) -> False)
  -> ((v1_xxreal_0 esk29_0 -> False) -> False)
  -> ((v1_xxreal_0 esk22_0 -> False) -> False)
  -> ((v2_relat_1 esk27_0 -> False) -> False)
  -> ((v2_relat_1 esk25_0 -> False) -> False)
  -> ((v2_relat_1 esk21_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk29_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk22_0 -> False) -> False)
  -> ((v7_ordinal1 esk32_0 -> False) -> False)
  -> ((v7_ordinal1 esk28_0 -> False) -> False)
  -> ((v2_funct_1 esk19_0 -> False) -> False)
  -> ((v1_xreal_0 esk29_0 -> False) -> False)
  -> ((v1_xreal_0 esk22_0 -> False) -> False)
  -> ((v1_xreal_0 esk15_0 -> False) -> False)
  -> ((v2_ordinal1 esk20_0 -> False) -> False)
  -> ((v2_ordinal1 esk17_0 -> False) -> False)
  -> ((v1_ordinal1 esk20_0 -> False) -> False)
  -> ((v1_ordinal1 esk17_0 -> False) -> False)
  -> ((v1_finset_1 esk37_0 -> False) -> False)
  -> ((v1_finset_1 esk24_0 -> False) -> False)
  -> ((v1_finset_1 esk17_0 -> False) -> False)
  -> ((v1_finset_1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk20_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_card_1 esk17_0 -> False) -> False)
  -> ((v1_card_1 esk10_0 -> False) -> False)
  -> ((v1_card_1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk29_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk38_0 -> False) -> False)
  -> ((v1_funct_1 esk31_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk24_0 -> False) -> False)
  -> ((v1_funct_1 esk19_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_relat_1 esk38_0 -> False) -> False)
  -> ((v1_relat_1 esk31_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk3_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
