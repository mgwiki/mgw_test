(** $I sig/MizarPreamble.mgs **)

Theorem t11_arrow:
 forall v1_relat_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v1_finset_1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall esk12_1:set -> set,
 forall v2_finset_1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall v1_int_1:set -> prop,
 forall esk21_0:set,
 forall esk15_0:set,
 forall esk7_0:set,
 forall esk9_2:set -> set -> set,
 forall esk18_0:set,
 forall esk13_0:set,
 forall esk8_0:set,
 forall esk17_0:set,
 forall esk10_0:set,
 forall esk11_0:set,
 forall esk16_0:set,
 forall esk6_1:set -> set,
 forall esk14_0:set,
 forall esk19_0:set,
 forall k1_xboole_0:set,
 forall v1_xcmplx_0:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v3_xxreal_0:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall esk20_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v5_finset_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk22_3:set -> set -> set -> set,
 forall esk4_0:set,
 forall esk5_0:set,
 forall esk1_0:set,
 forall k2_arrow:set -> set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall r1_arrow:set -> set -> set -> prop,
 forall esk32_2:set -> set -> set,
 forall esk28_2:set -> set -> set,
 forall esk33_2:set -> set -> set,
 forall esk31_2:set -> set -> set,
 forall esk29_2:set -> set -> set,
 forall esk30_2:set -> set -> set,
 forall esk26_3:set -> set -> set -> set,
 forall epred1_2:set -> set -> prop,
 forall esk27_3:set -> set -> set -> set,
 forall esk25_3:set -> set -> set -> set,
 forall k4_tarski:set -> set -> set,
 forall esk23_3:set -> set -> set -> set,
 forall esk24_3:set -> set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
     (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk24_3 X1 X2 X3) (esk23_3 X1 X2 X3)) X3 -> r2_hidden (k4_tarski (esk25_3 X1 X2 X3) (esk27_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk23_3 X1 X2 X3) (esk24_3 X1 X2 X3)) X3 -> r2_hidden (k4_tarski (esk25_3 X1 X2 X3) (esk27_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (r2_hidden (k4_tarski (esk26_3 X1 X2 X3) (esk27_3 X1 X2 X3)) X3 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk24_3 X1 X2 X3) (esk23_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (r2_hidden (k4_tarski (esk26_3 X1 X2 X3) (esk27_3 X1 X2 X3)) X3 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk23_3 X1 X2 X3) (esk24_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (r2_hidden (k4_tarski (esk25_3 X1 X2 X3) (esk26_3 X1 X2 X3)) X3 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk24_3 X1 X2 X3) (esk23_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (r2_hidden (k4_tarski (esk25_3 X1 X2 X3) (esk26_3 X1 X2 X3)) X3 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk23_3 X1 X2 X3) (esk24_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk24_3 X1 X2 X3) (esk23_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk23_3 X1 X2 X3) (esk24_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk26_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk24_3 X1 X2 X3) (esk23_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk26_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk23_3 X1 X2 X3) (esk24_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk25_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk24_3 X1 X2 X3) (esk23_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk25_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk23_3 X1 X2 X3) (esk24_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk24_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk25_3 X1 X2 X3) (esk27_3 X1 X2 X3)) X3 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk23_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk25_3 X1 X2 X3) (esk27_3 X1 X2 X3)) X3 -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk30_2 X1 X2) (esk29_2 X1 X2)) (esk28_2 X1 X2) -> r2_hidden (k4_tarski (esk31_2 X1 X2) (esk33_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk29_2 X1 X2) (esk30_2 X1 X2)) (esk28_2 X1 X2) -> r2_hidden (k4_tarski (esk31_2 X1 X2) (esk33_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk24_3 X1 X2 X3) X2 -> False) -> (r2_hidden (k4_tarski (esk26_3 X1 X2 X3) (esk27_3 X1 X2 X3)) X3 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk24_3 X1 X2 X3) X2 -> False) -> (r2_hidden (k4_tarski (esk25_3 X1 X2 X3) (esk26_3 X1 X2 X3)) X3 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk23_3 X1 X2 X3) X2 -> False) -> (r2_hidden (k4_tarski (esk26_3 X1 X2 X3) (esk27_3 X1 X2 X3)) X3 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk23_3 X1 X2 X3) X2 -> False) -> (r2_hidden (k4_tarski (esk25_3 X1 X2 X3) (esk26_3 X1 X2 X3)) X3 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (r2_hidden (k4_tarski (esk32_2 X1 X2) (esk33_2 X1 X2)) (esk28_2 X1 X2) -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk30_2 X1 X2) (esk29_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (r2_hidden (k4_tarski (esk32_2 X1 X2) (esk33_2 X1 X2)) (esk28_2 X1 X2) -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk29_2 X1 X2) (esk30_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (r2_hidden (k4_tarski (esk31_2 X1 X2) (esk32_2 X1 X2)) (esk28_2 X1 X2) -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk30_2 X1 X2) (esk29_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (r2_hidden (k4_tarski (esk31_2 X1 X2) (esk32_2 X1 X2)) (esk28_2 X1 X2) -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk29_2 X1 X2) (esk30_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk33_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk30_2 X1 X2) (esk29_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk33_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk29_2 X1 X2) (esk30_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk32_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk30_2 X1 X2) (esk29_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk32_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk29_2 X1 X2) (esk30_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk31_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk30_2 X1 X2) (esk29_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk31_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk29_2 X1 X2) (esk30_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk30_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk31_2 X1 X2) (esk33_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk29_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k4_tarski (esk31_2 X1 X2) (esk33_2 X1 X2)) (esk28_2 X1 X2) -> False)
  -> (forall X1, (r1_arrow X1 esk2_0 esk3_0 -> False) -> (r1_arrow X1 esk2_0 esk4_0 -> False) -> m1_subset_1 X1 (k2_arrow esk1_0) -> r1_arrow X1 esk3_0 esk4_0 -> r1_arrow X1 esk4_0 esk3_0 -> r1_arrow esk5_0 esk3_0 esk4_0 -> r1_arrow esk5_0 esk4_0 esk3_0 -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk30_2 X1 X2) X2 -> False) -> (r2_hidden (k4_tarski (esk32_2 X1 X2) (esk33_2 X1 X2)) (esk28_2 X1 X2) -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk30_2 X1 X2) X2 -> False) -> (r2_hidden (k4_tarski (esk31_2 X1 X2) (esk32_2 X1 X2)) (esk28_2 X1 X2) -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk29_2 X1 X2) X2 -> False) -> (r2_hidden (k4_tarski (esk32_2 X1 X2) (esk33_2 X1 X2)) (esk28_2 X1 X2) -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk29_2 X1 X2) X2 -> False) -> (r2_hidden (k4_tarski (esk31_2 X1 X2) (esk32_2 X1 X2)) (esk28_2 X1 X2) -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X4 X1 X2 X5, (epred1_2 X2 X5 -> False) -> (r2_hidden (esk28_2 X5 X2) X5 -> False) -> (r2_hidden (k4_tarski X1 X4) (esk28_2 X5 X2) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> r2_hidden (k4_tarski X3 X4) (esk28_2 X5 X2) -> r2_hidden (k4_tarski X1 X3) (esk28_2 X5 X2) -> False)
  -> (forall X1, (r1_arrow X1 esk2_0 esk3_0 -> False) -> (r1_arrow X1 esk2_0 esk4_0 -> False) -> (r1_arrow X1 esk4_0 esk3_0 -> False) -> (r1_arrow esk5_0 esk4_0 esk3_0 -> False) -> m1_subset_1 X1 (k2_arrow esk1_0) -> r1_arrow X1 esk3_0 esk4_0 -> r1_arrow esk5_0 esk3_0 esk4_0 -> False)
  -> (forall X1, (r1_arrow X1 esk2_0 esk3_0 -> False) -> (r1_arrow X1 esk2_0 esk4_0 -> False) -> (r1_arrow X1 esk3_0 esk4_0 -> False) -> (r1_arrow esk5_0 esk3_0 esk4_0 -> False) -> m1_subset_1 X1 (k2_arrow esk1_0) -> r1_arrow X1 esk4_0 esk3_0 -> r1_arrow esk5_0 esk4_0 esk3_0 -> False)
  -> (forall X5 X2 X1 X3 X4, (X3 = X4 -> False) -> (v1_xboole_0 X5 -> False) -> (r1_arrow X1 X2 X3 -> False) -> m1_subset_1 X4 X5 -> m1_subset_1 X3 X5 -> m1_subset_1 X2 X5 -> m1_subset_1 X1 (k2_arrow X5) -> r2_hidden (k4_tarski X2 X3) (esk22_3 X5 X4 X1) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk24_3 X1 X2 X3) X2 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk24_3 X1 X2 X3) X2 -> False) -> (m1_subset_1 (esk26_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk24_3 X1 X2 X3) X2 -> False) -> (m1_subset_1 (esk25_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk23_3 X1 X2 X3) X2 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk23_3 X1 X2 X3) X2 -> False) -> (m1_subset_1 (esk26_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> (m1_subset_1 (esk23_3 X1 X2 X3) X2 -> False) -> (m1_subset_1 (esk25_3 X1 X2 X3) X2 -> False) -> epred1_2 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X4 X5 X1 X2 X3, (X2 = X3 -> False) -> (v1_xboole_0 X4 -> False) -> X1 = X2 -> m1_subset_1 X3 X4 -> m1_subset_1 X2 X4 -> m1_subset_1 X1 X4 -> m1_subset_1 X5 (k2_arrow X4) -> r2_hidden (k4_tarski X1 X3) (esk22_3 X4 X2 X5) -> False)
  -> (forall X5 X3 X4 X1 X2, (X1 = X2 -> False) -> (v1_xboole_0 X5 -> False) -> (r2_hidden (k4_tarski X1 X4) (esk22_3 X5 X2 X3) -> False) -> m1_subset_1 X4 X5 -> m1_subset_1 X2 X5 -> m1_subset_1 X1 X5 -> r1_arrow X3 X1 X4 -> m1_subset_1 X3 (k2_arrow X5) -> False)
  -> (forall X1, (r1_arrow X1 esk2_0 esk3_0 -> False) -> (r1_arrow X1 esk2_0 esk4_0 -> False) -> (r1_arrow X1 esk3_0 esk4_0 -> False) -> (r1_arrow X1 esk4_0 esk3_0 -> False) -> (r1_arrow esk5_0 esk3_0 esk4_0 -> False) -> (r1_arrow esk5_0 esk4_0 esk3_0 -> False) -> m1_subset_1 X1 (k2_arrow esk1_0) -> False)
  -> (forall X1 X4 X3 X2 X5, (v1_xboole_0 X5 -> False) -> (r1_arrow X1 X4 X3 -> False) -> m1_subset_1 X4 X5 -> m1_subset_1 X3 X5 -> m1_subset_1 X2 X5 -> r1_arrow X1 X4 X2 -> r1_arrow X1 X2 X3 -> m1_subset_1 X1 (k2_arrow X5) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk30_2 X1 X2) X2 -> False) -> (m1_subset_1 (esk33_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk30_2 X1 X2) X2 -> False) -> (m1_subset_1 (esk32_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk30_2 X1 X2) X2 -> False) -> (m1_subset_1 (esk31_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk29_2 X1 X2) X2 -> False) -> (m1_subset_1 (esk33_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk29_2 X1 X2) X2 -> False) -> (m1_subset_1 (esk32_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (m1_subset_1 (esk29_2 X1 X2) X2 -> False) -> (m1_subset_1 (esk31_2 X1 X2) X2 -> False) -> r2_hidden (esk28_2 X1 X2) X1 -> m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X4 X2 X3 X5, (v1_xboole_0 X5 -> False) -> (r1_arrow X1 X4 X2 -> False) -> (r1_arrow X1 X2 X3 -> False) -> m1_subset_1 X4 X5 -> m1_subset_1 X3 X5 -> m1_subset_1 X2 X5 -> r1_arrow X1 X4 X3 -> m1_subset_1 X1 (k2_arrow X5) -> False)
  -> (forall X1 X4 X3 X2 X5, (v1_xboole_0 X5 -> False) -> (r1_arrow X1 X4 X3 -> False) -> (r1_arrow X1 X2 X4 -> False) -> m1_subset_1 X4 X5 -> m1_subset_1 X3 X5 -> m1_subset_1 X2 X5 -> r1_arrow X1 X2 X3 -> m1_subset_1 X1 (k2_arrow X5) -> False)
  -> (forall X2 X6 X3 X4 X1 X5, (r2_hidden (k4_tarski X1 X4) X5 -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> r2_hidden X5 X6 -> epred1_2 X2 X6 -> r2_hidden (k4_tarski X3 X4) X5 -> r2_hidden (k4_tarski X1 X3) X5 -> False)
  -> (forall X1 X4 X2 X3 X5, (v1_xboole_0 X5 -> False) -> (r1_arrow X1 X4 X2 -> False) -> (r1_arrow X1 X3 X4 -> False) -> (r1_arrow X1 X2 X3 -> False) -> m1_subset_1 X4 X5 -> m1_subset_1 X3 X5 -> m1_subset_1 X2 X5 -> m1_subset_1 X1 (k2_arrow X5) -> False)
  -> (forall X2 X1 X5 X3 X4, (v1_xboole_0 X4 -> False) -> (r2_hidden (k4_tarski X3 X1) (esk22_3 X4 X2 X5) -> False) -> X1 = X2 -> m1_subset_1 X3 X4 -> m1_subset_1 X2 X4 -> m1_subset_1 X1 X4 -> m1_subset_1 X5 (k2_arrow X4) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> m1_subset_1 X2 X1 -> m1_subset_1 X3 (k2_arrow X1) -> False)
  -> (forall X3 X1 X2 X4, (epred1_2 X2 X4 -> False) -> (r2_hidden (esk28_2 X4 X2) X4 -> False) -> (r2_hidden (k4_tarski X3 X1) (esk28_2 X4 X2) -> False) -> (r2_hidden (k4_tarski X1 X3) (esk28_2 X4 X2) -> False) -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_arrow X4 X3 X2 -> False) -> (r1_arrow X4 X2 X3 -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> m1_subset_1 X4 (k2_arrow X1) -> False)
  -> (forall X5 X2 X1 X3 X4, (r2_hidden (k4_tarski X3 X1) X4 -> False) -> (r2_hidden (k4_tarski X1 X3) X4 -> False) -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> r2_hidden X4 X5 -> epred1_2 X2 X5 -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden (esk28_2 X1 X2) X1 -> False) -> (m1_subset_1 (esk28_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False) -> False)
  -> (forall X3 X2 X1, (r2_hidden (k4_tarski X2 X3) X1 -> False) -> v1_relat_1 X1 -> r1_arrow X1 X2 X3 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X3, (r1_arrow X3 X1 X2 -> False) -> v1_relat_1 X3 -> r2_hidden (k4_tarski X1 X2) X3 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False) -> r2_hidden X1 X3 -> epred1_2 X2 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_zfmisc_1 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 X2 -> False) -> m1_subset_1 X2 (k2_arrow X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (X2 = (k2_arrow X1) -> False) -> (v1_xboole_0 X1 -> False) -> epred1_2 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (epred1_2 X2 X1 -> False) -> X1 = (k2_arrow X2) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk20_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk12_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_arrow X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk20_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk12_1 X1) -> False) -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_int_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk7_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (esk4_0 = esk2_0 -> False)
  -> (esk3_0 = esk2_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk9_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk9_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk9_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk9_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k2_arrow esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk4_0 esk1_0 -> False) -> False)
  -> ((m1_subset_1 esk3_0 esk1_0 -> False) -> False)
  -> ((m1_subset_1 esk2_0 esk1_0 -> False) -> False)
  -> ((v5_finset_1 esk21_0 -> False) -> False)
  -> ((v1_xxreal_0 esk18_0 -> False) -> False)
  -> ((v1_xxreal_0 esk16_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk18_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk16_0 -> False) -> False)
  -> ((v3_xxreal_0 esk16_0 -> False) -> False)
  -> ((v1_xreal_0 esk18_0 -> False) -> False)
  -> ((v1_xreal_0 esk16_0 -> False) -> False)
  -> ((v1_xreal_0 esk11_0 -> False) -> False)
  -> ((v1_int_1 esk13_0 -> False) -> False)
  -> ((v2_ordinal1 esk14_0 -> False) -> False)
  -> ((v1_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk8_0 -> False) -> False)
  -> ((v7_ordinal1 esk19_0 -> False) -> False)
  -> ((v7_ordinal1 esk17_0 -> False) -> False)
  -> ((v1_finset_1 esk21_0 -> False) -> False)
  -> ((v1_finset_1 esk7_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
