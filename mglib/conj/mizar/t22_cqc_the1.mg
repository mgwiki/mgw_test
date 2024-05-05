(** $I sig/MizarPreamble.mgs **)

Theorem t22_cqc_the1:
 forall esk34_2:set -> set -> set,
 forall r1_xxreal_0:set -> set -> prop,
 forall k5_numbers:set,
 forall a_1_1_cqc_the1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall a_0_1_cqc_the1:set,
 forall np__9:set,
 forall v5_finset_1:set -> prop,
 forall v3_finseq_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk30_1:set -> set,
 forall v3_ordinal1:set -> prop,
 forall esk29_1:set -> set,
 forall esk27_1:set -> set,
 forall esk23_1:set -> set,
 forall esk15_1:set -> set,
 forall np__1:set,
 forall v7_ordinal1:set -> prop,
 forall k4_ordinal1:set,
 forall k1_xboole_0:set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall esk22_0:set,
 forall esk20_0:set,
 forall esk3_0:set,
 forall k2_cqc_the1:set,
 forall esk25_1:set -> set,
 forall esk31_1:set -> set,
 forall v2_card_1:set -> prop,
 forall esk8_0:set,
 forall esk4_0:set,
 forall esk9_0:set,
 forall esk12_0:set,
 forall esk10_0:set,
 forall o_0_0_xboole_0:set,
 forall esk16_0:set,
 forall esk5_0:set,
 forall esk7_0:set,
 forall esk2_0:set,
 forall esk6_0:set,
 forall esk11_0:set,
 forall esk14_0:set,
 forall esk32_0:set,
 forall esk18_0:set,
 forall esk21_0:set,
 forall esk13_1:set -> set,
 forall v5_ordinal1:set -> prop,
 forall k1_numbers:set,
 forall esk17_1:set -> set,
 forall v3_card_1:set -> set -> prop,
 forall v1_card_1:set -> prop,
 forall esk26_1:set -> set,
 forall esk19_1:set -> set,
 forall esk24_1:set -> set,
 forall esk28_1:set -> set,
 forall v1_finseq_1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v2_xxreal_0:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v3_xxreal_0:set -> prop,
 forall esk33_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk1_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk1_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk33_2 X3 X2) -> False)
  -> (forall X1 X2, (r1_xxreal_0 (esk34_2 X1 X2) X2 -> False) -> m1_subset_1 X2 k5_numbers -> r2_hidden X1 (a_1_1_cqc_the1 X2) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk34_2 X1 X2) k5_numbers -> False) -> m1_subset_1 X2 k5_numbers -> r2_hidden X1 (a_1_1_cqc_the1 X2) -> False)
  -> (forall X1 X2 X3, (r2_hidden X2 (a_1_1_cqc_the1 X3) -> False) -> X1 = X2 -> r1_xxreal_0 X1 X3 -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, ((esk34_2 X1 X2) = X1 -> False) -> m1_subset_1 X2 k5_numbers -> r2_hidden X1 (a_1_1_cqc_the1 X2) -> False)
  -> (forall X2 X1, (r2_hidden (esk33_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r2_hidden X2 a_0_1_cqc_the1 -> False) -> X1 = X2 -> m1_subset_1 X1 k5_numbers -> r1_xxreal_0 X1 np__9 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v3_xxreal_0 X2 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v3_xxreal_0 X2 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v2_xxreal_0 X1 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v2_xxreal_0 X1 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_finseq_1 X2 -> False) -> v3_finseq_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (r1_xxreal_0 (esk30_1 X1) np__9 -> False) -> r2_hidden X1 a_0_1_cqc_the1 -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) k5_numbers -> False) -> r2_hidden X1 a_0_1_cqc_the1 -> False)
  -> (forall X2 X1, (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_finseq_1 X2 -> False) -> v3_finseq_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 (a_1_1_cqc_the1 X1) -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_card_1 (esk17_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, ((esk30_1 X1) = X1 -> False) -> r2_hidden X1 a_0_1_cqc_the1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk19_1 X1) np__1 -> False) -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk29_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk28_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk26_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_finset_1 X1 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk29_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v3_finseq_1 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_finseq_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk13_1 X1) X1 -> False)
  -> (r1_xxreal_0 np__9 np__1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk3_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__9 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k2_cqc_the1 -> False)
  -> (v1_finset_1 esk32_0 -> False)
  -> (v1_finset_1 k4_ordinal1 -> False)
  -> (v1_finset_1 k2_cqc_the1 -> False)
  -> ((m2_subset_1 np__9 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk31_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((r1_xxreal_0 np__9 np__9 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__9 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((m1_subset_1 np__9 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__9 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk25_1 X1) -> False) -> False)
  -> ((v2_card_1 k4_ordinal1 -> False) -> False)
  -> ((v5_finset_1 esk21_0 -> False) -> False)
  -> ((v7_ordinal1 esk18_0 -> False) -> False)
  -> ((v7_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_finseq_1 esk20_0 -> False) -> False)
  -> ((v1_xreal_0 esk11_0 -> False) -> False)
  -> ((v1_xreal_0 esk8_0 -> False) -> False)
  -> ((v1_xreal_0 esk6_0 -> False) -> False)
  -> ((v1_xreal_0 esk4_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk8_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk6_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk4_0 -> False) -> False)
  -> ((v1_card_1 esk9_0 -> False) -> False)
  -> ((v1_card_1 esk2_0 -> False) -> False)
  -> ((v1_card_1 k4_ordinal1 -> False) -> False)
  -> ((v3_xxreal_0 esk7_0 -> False) -> False)
  -> ((v3_xxreal_0 esk6_0 -> False) -> False)
  -> ((v2_xxreal_0 esk5_0 -> False) -> False)
  -> ((v2_xxreal_0 esk4_0 -> False) -> False)
  -> ((v2_xxreal_0 np__9 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xxreal_0 esk16_0 -> False) -> False)
  -> ((v1_xxreal_0 esk12_0 -> False) -> False)
  -> ((v1_xxreal_0 esk8_0 -> False) -> False)
  -> ((v1_xxreal_0 esk7_0 -> False) -> False)
  -> ((v1_xxreal_0 esk6_0 -> False) -> False)
  -> ((v1_xxreal_0 esk5_0 -> False) -> False)
  -> ((v1_xxreal_0 esk4_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 esk3_0 -> False) -> False)
  -> ((v3_ordinal1 esk2_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v2_ordinal1 esk3_0 -> False) -> False)
  -> ((v2_ordinal1 esk2_0 -> False) -> False)
  -> ((v1_ordinal1 esk3_0 -> False) -> False)
  -> ((v1_ordinal1 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_finset_1 esk22_0 -> False) -> False)
  -> ((v1_finset_1 esk21_0 -> False) -> False)
  -> ((v1_finset_1 esk2_0 -> False) -> False)
  -> ((k2_cqc_the1 = a_0_1_cqc_the1 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> ((k1_xboole_0 = o_0_0_xboole_0 -> False) -> False)
  -> False.
Admitted.
