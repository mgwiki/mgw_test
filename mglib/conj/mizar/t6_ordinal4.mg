(** $I sig/MizarPreamble.mgs **)

Theorem t6_ordinal4:
 forall esk27_3:set -> set -> set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk26_2:set -> set -> set,
 forall v3_card_1:set -> set -> prop,
 forall v1_card_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk18_1:set -> set,
 forall esk23_1:set -> set,
 forall np__1:set,
 forall v2_funct_1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk21_0:set,
 forall esk22_0:set,
 forall esk14_0:set,
 forall v2_xxreal_0:set -> prop,
 forall esk12_0:set,
 forall esk19_0:set,
 forall esk11_0:set,
 forall o_0_0_xboole_0:set,
 forall esk10_0:set,
 forall esk9_0:set,
 forall esk15_0:set,
 forall esk8_0:set,
 forall esk13_0:set,
 forall esk6_1:set -> set,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall np__0:set,
 forall esk16_0:set,
 forall esk25_0:set,
 forall esk17_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall v3_funct_1:set -> prop,
 forall esk20_1:set -> set,
 forall esk24_1:set -> set,
 forall esk5_1:set -> set,
 forall v6_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_ordinal2:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall k1_tarski:set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk30_2:set -> set -> set,
 forall esk31_3:set -> set -> set -> set,
 forall esk29_2:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall r1_ordinal2:set -> set -> prop,
 forall r1_ordinal1:set -> set -> prop,
 forall esk28_4:set -> set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall epred1_2:set -> set -> prop,
 forall v3_ordinal1:set -> prop,
 forall k1_xboole_0:set,
     (forall X3 X1 X2 X5 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden (k1_funct_1 X1 X2) X3 -> False) -> v3_ordinal1 X5 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> r1_ordinal2 X4 X1 -> r2_hidden X5 X4 -> r2_hidden X4 X3 -> epred1_2 X1 X4 -> r2_hidden X2 (k9_xtuple_0 X1) -> r1_ordinal1 (esk28_4 X4 X1 X5 X3) X2 -> False)
  -> (forall X1 X3 X2 X5 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 (k1_funct_1 X2 X3) -> False) -> v3_ordinal1 X5 -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> r1_ordinal2 X4 X2 -> r2_hidden X4 X5 -> r2_hidden X1 X4 -> epred1_2 X2 X4 -> r2_hidden X3 (k9_xtuple_0 X2) -> r1_ordinal1 (esk28_4 X4 X2 X1 X5) X3 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> v3_ordinal1 X3 -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> r2_hidden (esk29_2 X1 X2) (k1_funct_1 X2 (esk31_3 X1 X2 X3)) -> r2_hidden (k1_funct_1 X2 (esk31_3 X1 X2 X3)) (esk30_2 X1 X2) -> False)
  -> (forall X4 X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk28_4 X1 X2 X3 X4) (k9_xtuple_0 X2) -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> r1_ordinal2 X1 X2 -> r2_hidden X3 X1 -> r2_hidden X1 X4 -> epred1_2 X2 X1 -> False)
  -> (forall X4 X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (v3_ordinal1 (esk28_4 X1 X2 X3 X4) -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> r1_ordinal2 X1 X2 -> r2_hidden X3 X1 -> r2_hidden X1 X4 -> epred1_2 X2 X1 -> False)
  -> (forall X3 X2 X1, (r1_ordinal2 X2 X1 -> False) -> X2 = k1_xboole_0 -> (k1_funct_1 X1 (esk27_3 X2 X1 X3)) = k1_xboole_0 -> v3_ordinal1 X3 -> epred1_2 X1 X2 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X3 X1 X2, (r1_ordinal2 X1 X2 -> False) -> (r2_hidden (esk27_3 X1 X2 X3) (k9_xtuple_0 X2) -> False) -> X1 = k1_xboole_0 -> v3_ordinal1 X3 -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (r2_hidden (esk31_3 X1 X2 X3) (k9_xtuple_0 X2) -> False) -> v3_ordinal1 X3 -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2 X3, (r1_ordinal2 X2 X3 -> False) -> (r1_ordinal1 X1 (esk27_3 X2 X3 X1) -> False) -> X2 = k1_xboole_0 -> v3_ordinal1 X1 -> epred1_2 X3 X2 -> r2_hidden X1 (k9_xtuple_0 X3) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal2 X2 X3 -> False) -> (r1_ordinal1 X1 (esk31_3 X2 X3 X1) -> False) -> v3_ordinal1 X1 -> epred1_2 X3 X2 -> r2_hidden X1 (k9_xtuple_0 X3) -> False)
  -> (forall X3 X1 X2, (r1_ordinal2 X1 X2 -> False) -> (v3_ordinal1 (esk27_3 X1 X2 X3) -> False) -> X1 = k1_xboole_0 -> v3_ordinal1 X3 -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (r2_hidden (k1_funct_1 esk1_0 X2) (k1_funct_1 esk2_0 X2) -> False) -> (r1_ordinal1 (k1_funct_1 esk1_0 X1) (k1_funct_1 esk2_0 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X2 (k9_xtuple_0 esk1_0) -> r2_hidden X1 (k9_xtuple_0 esk1_0) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (v3_ordinal1 (esk31_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1 X3, ((k1_funct_1 X3 X1) = k1_xboole_0 -> False) -> X2 = k1_xboole_0 -> v3_ordinal1 X1 -> r1_ordinal2 X2 X3 -> epred1_2 X3 X2 -> r2_hidden X1 (k9_xtuple_0 X3) -> r1_ordinal1 (esk26_2 X2 X3) X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk7_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X2)) -> False)
  -> (forall X2 X1, (r2_hidden (esk26_2 X1 X2) (k9_xtuple_0 X2) -> False) -> X1 = k1_xboole_0 -> r1_ordinal2 X1 X2 -> epred1_2 X2 X1 -> False)
  -> (forall X1 X2, (r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X2)) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (r2_hidden (esk29_2 X1 X2) X1 -> False) -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (r2_hidden X1 (esk30_2 X1 X2) -> False) -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (esk26_2 X1 X2) -> False) -> X1 = k1_xboole_0 -> r1_ordinal2 X1 X2 -> epred1_2 X2 X1 -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (v3_ordinal1 (esk30_2 X1 X2) -> False) -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (v3_ordinal1 (esk29_2 X1 X2) -> False) -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> v3_ordinal1 X2 -> False)
  -> (forall X1 X2, (v3_card_1 (k9_xtuple_0 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v1_card_1 X1 -> v3_card_1 X2 X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> v1_relat_1 X2 -> v5_ordinal1 X2 -> v1_funct_1 X2 -> v1_ordinal2 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, r2_hidden X1 X2 -> r1_tarski X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = X2 -> False) -> ((k2_xboole_0 X1 X2) = X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X2 X1 -> False) -> v1_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_hidden X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> r1_tarski (esk5_1 X1) X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk23_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk20_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk24_1 X1) np__1 -> False) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden k1_xboole_0 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk18_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v1_funct_1 (esk23_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (esk23_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (r1_ordinal1 esk3_0 esk4_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_finset_1 esk17_0 -> False)
  -> (v3_funct_1 esk21_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (forall X1, (r2_hidden X1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_card_1 (k1_tarski X1) np__1 -> False) -> False)
  -> (((k2_xboole_0 np__0 (k1_tarski np__0)) = np__1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((r1_ordinal2 esk4_0 esk2_0 -> False) -> False)
  -> ((r1_ordinal2 esk3_0 esk1_0 -> False) -> False)
  -> (((k9_xtuple_0 esk2_0) = (k9_xtuple_0 esk1_0) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v4_funct_1 esk25_0 -> False) -> False)
  -> ((v1_finset_1 esk12_0 -> False) -> False)
  -> ((v7_ordinal1 esk22_0 -> False) -> False)
  -> ((v7_ordinal1 esk19_0 -> False) -> False)
  -> ((v2_funct_1 esk13_0 -> False) -> False)
  -> ((v2_ordinal1 esk14_0 -> False) -> False)
  -> ((v2_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_ordinal1 esk14_0 -> False) -> False)
  -> ((v1_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_card_1 esk12_0 -> False) -> False)
  -> ((v1_card_1 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 esk4_0 -> False) -> False)
  -> ((v3_ordinal1 esk3_0 -> False) -> False)
  -> ((v1_ordinal2 esk15_0 -> False) -> False)
  -> ((v1_ordinal2 esk2_0 -> False) -> False)
  -> ((v1_ordinal2 esk1_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((v1_funct_1 esk13_0 -> False) -> False)
  -> ((v1_funct_1 esk9_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_funct_1 esk1_0 -> False) -> False)
  -> ((v5_ordinal1 esk15_0 -> False) -> False)
  -> ((v5_ordinal1 esk2_0 -> False) -> False)
  -> ((v5_ordinal1 esk1_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk9_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
