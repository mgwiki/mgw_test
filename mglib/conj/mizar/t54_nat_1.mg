(** $I sig/MizarPreamble.mgs **)

Theorem t54_nat_1:
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall esk7_2:set -> set -> set,
 forall a_1_5_nat_1:set -> set,
 forall a_1_4_nat_1:set -> set,
 forall esk3_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall v2_xxreal_0:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk27_1:set -> set,
 forall esk36_1:set -> set,
 forall esk29_1:set -> set,
 forall v1_card_1:set -> prop,
 forall v3_card_1:set -> set -> prop,
 forall esk32_1:set -> set,
 forall k1_ordinal1:set -> set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk24_1:set -> set,
 forall esk22_0:set,
 forall esk23_0:set,
 forall esk17_0:set,
 forall esk2_1:set -> set,
 forall esk12_0:set,
 forall esk20_0:set,
 forall esk25_0:set,
 forall esk15_0:set,
 forall esk11_0:set,
 forall esk9_0:set,
 forall o_0_0_xboole_0:set,
 forall esk28_0:set,
 forall esk14_0:set,
 forall esk26_0:set,
 forall esk31_0:set,
 forall esk30_0:set,
 forall esk21_0:set,
 forall esk16_0:set,
 forall v2_card_1:set -> prop,
 forall esk19_1:set -> set,
 forall esk10_0:set,
 forall esk18_0:set,
 forall esk33_0:set,
 forall esk1_0:set,
 forall v5_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall k4_ordinal1:set,
 forall esk13_1:set -> set,
 forall esk34_1:set -> set,
 forall esk35_1:set -> set,
 forall v3_ordinal1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v3_xxreal_0:set -> prop,
 forall esk8_2:set -> set -> set,
 forall k2_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall esk37_1:set -> set,
 forall a_1_6_nat_1:set -> set,
 forall esk38_2:set -> set -> set,
 forall a_1_0_axioms:set -> set,
 forall esk5_2:set -> set -> set,
 forall r1_xxreal_0:set -> set -> prop,
 forall np__1:set,
 forall k1_nat_1:set -> set -> set,
 forall v7_ordinal1:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall r2_hidden:set -> set -> prop,
 forall a_1_1_nat_1:set -> set,
     (forall X1 X2 X3, (r2_hidden X2 (a_1_1_nat_1 X3) -> False) -> (r1_xxreal_0 (k1_nat_1 X3 np__1) X1 -> False) -> X1 = X2 -> v7_ordinal1 X3 -> m2_subset_1 X1 k1_numbers k5_numbers -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, v7_ordinal1 X1 -> r2_hidden X2 (a_1_5_nat_1 X1) -> r1_xxreal_0 (k1_nat_1 X1 np__1) (esk7_2 X2 X1) -> False)
  -> (forall X2 X1, v7_ordinal1 X1 -> r2_hidden X2 (a_1_1_nat_1 X1) -> r1_xxreal_0 (k1_nat_1 X1 np__1) (esk5_2 X2 X1) -> False)
  -> (forall X1 X2 X3, (r2_hidden X2 (a_1_4_nat_1 X3) -> False) -> X1 = X2 -> v7_ordinal1 X3 -> r1_xxreal_0 X1 X3 -> m2_subset_1 X1 k1_numbers k5_numbers -> False)
  -> (forall X2 X3 X1, (r1_xxreal_0 X3 X1 -> False) -> (r2_hidden X2 (a_1_0_axioms X3) -> False) -> X1 = X2 -> v7_ordinal1 X3 -> m2_subset_1 X1 k1_numbers k5_numbers -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk3_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (m2_subset_1 (esk6_2 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_4_nat_1 X2) -> False)
  -> (forall X1 X2, (m2_subset_1 (esk5_2 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_1_nat_1 X2) -> False)
  -> (forall X1 X2, (m2_subset_1 (esk4_2 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_0_axioms X2) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk38_2 X3 X2) -> False)
  -> (forall X1 X2, (m2_subset_1 (k1_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1, ((a_1_5_nat_1 X1) = (a_1_6_nat_1 X1) -> False) -> (r1_xxreal_0 (esk37_1 X1) X1 -> False) -> v7_ordinal1 X1 -> r1_xxreal_0 (k1_nat_1 X1 np__1) (esk37_1 X1) -> False)
  -> (forall X2 X1, v7_ordinal1 X1 -> r2_hidden X2 (a_1_0_axioms X1) -> r1_xxreal_0 X1 (esk4_2 X2 X1) -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X1 X2 -> r1_xxreal_0 (k1_nat_1 X2 np__1) X1 -> False)
  -> (forall X1, ((a_1_5_nat_1 X1) = (a_1_6_nat_1 X1) -> False) -> (r1_xxreal_0 (k1_nat_1 X1 np__1) (esk37_1 X1) -> False) -> v7_ordinal1 X1 -> r1_xxreal_0 (esk37_1 X1) X1 -> False)
  -> (forall X1 X2 X3, (r2_hidden X2 (a_1_5_nat_1 X3) -> False) -> (r1_xxreal_0 (k1_nat_1 X3 np__1) X1 -> False) -> X1 = X2 -> v7_ordinal1 X3 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (r1_xxreal_0 (esk8_2 X1 X2) X2 -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_6_nat_1 X2) -> False)
  -> (forall X1 X2, (r1_xxreal_0 (esk6_2 X1 X2) X2 -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_4_nat_1 X2) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk8_2 X1 X2) k5_numbers -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_6_nat_1 X2) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk7_2 X1 X2) k5_numbers -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_5_nat_1 X2) -> False)
  -> (forall X1 X2 X3, (r2_hidden X2 (a_1_6_nat_1 X3) -> False) -> X1 = X2 -> v7_ordinal1 X3 -> r1_xxreal_0 X1 X3 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 (k1_nat_1 X1 np__1) X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk38_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, ((k2_xcmplx_0 X1 X2) = (k1_nat_1 X1 X2) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2, ((k1_nat_1 X1 X2) = (k1_nat_1 X2 X1) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2, ((esk8_2 X1 X2) = X1 -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_6_nat_1 X2) -> False)
  -> (forall X1 X2, ((esk7_2 X1 X2) = X1 -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_5_nat_1 X2) -> False)
  -> (forall X1 X2, ((esk6_2 X1 X2) = X1 -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_4_nat_1 X2) -> False)
  -> (forall X1 X2, ((esk5_2 X1 X2) = X1 -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_1_nat_1 X2) -> False)
  -> (forall X1 X2, ((esk4_2 X1 X2) = X1 -> False) -> v7_ordinal1 X2 -> r2_hidden X1 (a_1_0_axioms X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((a_1_5_nat_1 X1) = (a_1_6_nat_1 X1) -> False) -> (m1_subset_1 (esk37_1 X1) k5_numbers -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_card_1 (esk32_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v7_ordinal1 (k1_ordinal1 X1) -> False) -> v7_ordinal1 X1 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k1_ordinal1 X1) -> False)
  -> (forall X1, ((k1_nat_1 X1 np__1) = (k1_ordinal1 X1) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk36_1 X1) np__1 -> False) -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk27_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk35_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk34_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k1_ordinal1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, ((a_1_0_axioms X1) = X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk24_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_ordinal1 X1) -> False)
  -> ((k1_ordinal1 esk1_0) = (a_1_4_nat_1 esk1_0) -> False)
  -> (v1_finset_1 esk22_0 -> False)
  -> (v1_finset_1 k4_ordinal1 -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk2_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk17_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((m1_subset_1 esk23_0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 esk12_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> ((v2_card_1 k4_ordinal1 -> False) -> False)
  -> ((v1_finset_1 esk23_0 -> False) -> False)
  -> ((v1_finset_1 esk16_0 -> False) -> False)
  -> ((v1_finset_1 esk10_0 -> False) -> False)
  -> ((v2_xxreal_0 esk21_0 -> False) -> False)
  -> ((v2_xxreal_0 esk20_0 -> False) -> False)
  -> ((v2_xxreal_0 esk12_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xcmplx_0 esk30_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk25_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk23_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk20_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk12_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk10_0 -> False) -> False)
  -> ((v1_xxreal_0 esk31_0 -> False) -> False)
  -> ((v1_xxreal_0 esk30_0 -> False) -> False)
  -> ((v1_xxreal_0 esk26_0 -> False) -> False)
  -> ((v1_xxreal_0 esk25_0 -> False) -> False)
  -> ((v1_xxreal_0 esk23_0 -> False) -> False)
  -> ((v1_xxreal_0 esk21_0 -> False) -> False)
  -> ((v1_xxreal_0 esk20_0 -> False) -> False)
  -> ((v1_xxreal_0 esk15_0 -> False) -> False)
  -> ((v1_xxreal_0 esk12_0 -> False) -> False)
  -> ((v1_xxreal_0 esk10_0 -> False) -> False)
  -> ((v3_xxreal_0 esk26_0 -> False) -> False)
  -> ((v3_xxreal_0 esk25_0 -> False) -> False)
  -> ((v1_xreal_0 esk30_0 -> False) -> False)
  -> ((v1_xreal_0 esk25_0 -> False) -> False)
  -> ((v1_xreal_0 esk23_0 -> False) -> False)
  -> ((v1_xreal_0 esk20_0 -> False) -> False)
  -> ((v1_xreal_0 esk14_0 -> False) -> False)
  -> ((v1_xreal_0 esk12_0 -> False) -> False)
  -> ((v1_xreal_0 esk10_0 -> False) -> False)
  -> ((v2_ordinal1 esk23_0 -> False) -> False)
  -> ((v2_ordinal1 esk18_0 -> False) -> False)
  -> ((v2_ordinal1 esk16_0 -> False) -> False)
  -> ((v2_ordinal1 esk10_0 -> False) -> False)
  -> ((v1_ordinal1 esk23_0 -> False) -> False)
  -> ((v1_ordinal1 esk18_0 -> False) -> False)
  -> ((v1_ordinal1 esk16_0 -> False) -> False)
  -> ((v1_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 esk23_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_card_1 esk23_0 -> False) -> False)
  -> ((v1_card_1 esk16_0 -> False) -> False)
  -> ((v1_card_1 esk10_0 -> False) -> False)
  -> ((v1_card_1 esk9_0 -> False) -> False)
  -> ((v1_card_1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk31_0 -> False) -> False)
  -> ((v1_xboole_0 esk30_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v7_ordinal1 esk33_0 -> False) -> False)
  -> ((v7_ordinal1 esk28_0 -> False) -> False)
  -> ((v7_ordinal1 esk23_0 -> False) -> False)
  -> ((v7_ordinal1 esk10_0 -> False) -> False)
  -> ((v7_ordinal1 esk1_0 -> False) -> False)
  -> ((k1_xboole_0 = o_0_0_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
