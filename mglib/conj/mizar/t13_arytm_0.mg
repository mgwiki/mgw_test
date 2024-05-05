(** $I sig/MizarPreamble.mgs **)

Theorem t13_arytm_0:
 forall esk29_3:set -> set -> set -> set,
 forall esk30_3:set -> set -> set -> set,
 forall esk31_3:set -> set -> set -> set,
 forall esk32_3:set -> set -> set -> set,
 forall epred1_2:set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall k1_numbers:set,
 forall esk24_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall a_0_1_arytm_3:set,
 forall np__1:set,
 forall v1_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v1_finset_1:set -> prop,
 forall esk19_0:set,
 forall esk22_0:set,
 forall esk17_0:set,
 forall k5_arytm_3:set,
 forall esk7_1:set -> set,
 forall c2__arytm_0:set,
 forall esk20_0:set,
 forall esk12_0:set,
 forall esk14_0:set,
 forall esk13_0:set,
 forall esk16_0:set,
 forall v2_xxreal_0:set -> prop,
 forall k5_numbers:set,
 forall esk15_0:set,
 forall esk18_0:set,
 forall esk23_0:set,
 forall esk21_0:set,
 forall v7_ordinal1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk11_1:set -> set,
 forall v4_funct_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk10_1:set -> set,
 forall esk9_1:set -> set,
 forall v3_ordinal1:set -> prop,
 forall k11_arytm_3:set,
 forall a_0_0_arytm_3:set,
 forall r1_arytm_3:set -> set -> prop,
 forall k4_ordinal1:set,
 forall k1_xboole_0:set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall esk25_3:set -> set -> set -> set,
 forall esk26_3:set -> set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall k6_subset_1:set -> set -> set,
 forall k8_arytm_2:set -> set -> set,
 forall esk27_3:set -> set -> set -> set,
 forall esk28_3:set -> set -> set -> set,
 forall k4_tarski:set -> set -> set,
 forall k2_arytm_2:set,
 forall r2_hidden:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_tarski:set -> set,
 forall epred2_3:set -> set -> set -> prop,
 forall k2_arytm_0:set -> set -> set,
 forall k6_numbers:set,
     (forall X1 X3 X2, (X2 = k6_numbers -> False) -> ((k4_tarski k6_numbers (k8_arytm_2 (esk27_3 X2 X3 X1) (esk28_3 X2 X3 X1))) = X1 -> False) -> X1 = (k2_arytm_0 X2 X3) -> r2_hidden X2 k2_arytm_2 -> epred2_3 X1 X3 X2 -> r2_hidden X3 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X1 X2 X3, (X3 = k6_numbers -> False) -> ((k4_tarski k6_numbers (k8_arytm_2 (esk30_3 X2 X3 X1) (esk29_3 X2 X3 X1))) = X1 -> False) -> X1 = (k2_arytm_0 X2 X3) -> r2_hidden X3 k2_arytm_2 -> epred2_3 X1 X3 X2 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X3 X2, ((k8_arytm_2 (esk32_3 X2 X3 X1) (esk31_3 X2 X3 X1)) = X1 -> False) -> X1 = (k2_arytm_0 X2 X3) -> epred2_3 X1 X3 X2 -> r2_hidden X3 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X1 X3, ((k8_arytm_2 (esk25_3 X2 X3 X1) (esk26_3 X2 X3 X1)) = X1 -> False) -> X1 = (k2_arytm_0 X2 X3) -> r2_hidden X3 k2_arytm_2 -> r2_hidden X2 k2_arytm_2 -> epred2_3 X1 X3 X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1, ((k4_tarski k6_numbers (esk32_3 X2 X1 X3)) = X1 -> False) -> X3 = (k2_arytm_0 X2 X1) -> epred2_3 X3 X1 X2 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X2 X1, ((k4_tarski k6_numbers (esk31_3 X1 X2 X3)) = X1 -> False) -> X3 = (k2_arytm_0 X1 X2) -> epred2_3 X3 X2 X1 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk32_3 X1 X2 X3) k2_arytm_2 -> False) -> X3 = (k2_arytm_0 X1 X2) -> epred2_3 X3 X2 X1 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk31_3 X1 X2 X3) k2_arytm_2 -> False) -> X3 = (k2_arytm_0 X1 X2) -> epred2_3 X3 X2 X1 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X1 X2 X3 X4 X5, (X5 = (k2_arytm_0 X3 X4) -> False) -> X5 = (k8_arytm_2 X2 X1) -> X4 = (k4_tarski k6_numbers X2) -> X3 = (k4_tarski k6_numbers X1) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> epred2_3 X5 X4 X3 -> r2_hidden X4 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X3 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X2 X3 X1, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk6_3 X1 X2 X3) X2 -> False)
  -> (forall X3 X1 X2, (X2 = k6_numbers -> False) -> ((k4_tarski k6_numbers (esk29_3 X1 X2 X3)) = X1 -> False) -> X3 = (k2_arytm_0 X1 X2) -> r2_hidden X2 k2_arytm_2 -> epred2_3 X3 X2 X1 -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X1 X2, (X2 = k6_numbers -> False) -> ((k4_tarski k6_numbers (esk28_3 X2 X1 X3)) = X1 -> False) -> X3 = (k2_arytm_0 X2 X1) -> r2_hidden X2 k2_arytm_2 -> epred2_3 X3 X1 X2 -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X2 X1, (X1 = k6_numbers -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) k2_arytm_2 -> False) -> X3 = (k2_arytm_0 X1 X2) -> r2_hidden X1 k2_arytm_2 -> epred2_3 X3 X2 X1 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X2 X1, (X1 = k6_numbers -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) k2_arytm_2 -> False) -> X3 = (k2_arytm_0 X1 X2) -> r2_hidden X1 k2_arytm_2 -> epred2_3 X3 X2 X1 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X1 X2, (X2 = k6_numbers -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) k2_arytm_2 -> False) -> X3 = (k2_arytm_0 X1 X2) -> r2_hidden X2 k2_arytm_2 -> epred2_3 X3 X2 X1 -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X1 X2, (X2 = k6_numbers -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) k2_arytm_2 -> False) -> X3 = (k2_arytm_0 X1 X2) -> r2_hidden X2 k2_arytm_2 -> epred2_3 X3 X2 X1 -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X5 X4 X2 X1 X3, (X3 = k6_numbers -> False) -> (X5 = (k2_arytm_0 X3 X4) -> False) -> X1 = X3 -> X4 = (k4_tarski k6_numbers X2) -> X5 = (k4_tarski k6_numbers (k8_arytm_2 X1 X2)) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> r2_hidden X3 k2_arytm_2 -> epred2_3 X5 X4 X3 -> r2_hidden X4 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X5 X3 X1 X2 X4, (X4 = k6_numbers -> False) -> (X5 = (k2_arytm_0 X3 X4) -> False) -> X2 = X4 -> X3 = (k4_tarski k6_numbers X1) -> X5 = (k4_tarski k6_numbers (k8_arytm_2 X2 X1)) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> r2_hidden X4 k2_arytm_2 -> epred2_3 X5 X4 X3 -> r2_hidden X3 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (esk26_3 X1 X2 X3) k2_arytm_2 -> False) -> X3 = (k2_arytm_0 X1 X2) -> r2_hidden X2 k2_arytm_2 -> r2_hidden X1 k2_arytm_2 -> epred2_3 X3 X2 X1 -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (esk25_3 X1 X2 X3) k2_arytm_2 -> False) -> X3 = (k2_arytm_0 X1 X2) -> r2_hidden X2 k2_arytm_2 -> r2_hidden X1 k2_arytm_2 -> epred2_3 X3 X2 X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1, (X1 = k6_numbers -> False) -> ((esk30_3 X2 X1 X3) = X1 -> False) -> X3 = (k2_arytm_0 X2 X1) -> r2_hidden X1 k2_arytm_2 -> epred2_3 X3 X1 X2 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X2 X1, (X1 = k6_numbers -> False) -> ((esk27_3 X1 X2 X3) = X1 -> False) -> X3 = (k2_arytm_0 X1 X2) -> r2_hidden X1 k2_arytm_2 -> epred2_3 X3 X2 X1 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X2 X1 X3 X4 X5, (X5 = (k2_arytm_0 X3 X4) -> False) -> X2 = X4 -> X1 = X3 -> X5 = (k8_arytm_2 X1 X2) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> r2_hidden X4 k2_arytm_2 -> r2_hidden X3 k2_arytm_2 -> epred2_3 X5 X4 X3 -> False)
  -> (forall X1 X3 X2, ((esk26_3 X2 X1 X3) = X1 -> False) -> X3 = (k2_arytm_0 X2 X1) -> r2_hidden X2 k2_arytm_2 -> r2_hidden X1 k2_arytm_2 -> epred2_3 X3 X1 X2 -> False)
  -> (forall X1 X3 X2, ((esk25_3 X1 X2 X3) = X1 -> False) -> X3 = (k2_arytm_0 X1 X2) -> r2_hidden X2 k2_arytm_2 -> r2_hidden X1 k2_arytm_2 -> epred2_3 X3 X2 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, ((k8_arytm_2 (k8_arytm_2 X1 X2) X3) = (k8_arytm_2 X1 (k8_arytm_2 X2 X3)) -> False) -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X3 X1, (X1 = k6_numbers -> False) -> X1 = (k2_arytm_0 X2 X3) -> epred1_2 X3 X2 -> epred2_3 X1 X3 X2 -> False)
  -> (forall X1 X2, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X2 X3 X1, (X1 = (k2_arytm_0 X2 X3) -> False) -> X1 = k6_numbers -> epred1_2 X3 X2 -> epred2_3 X1 X3 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk8_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k4_tarski X1 X3) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k4_tarski X3 X1) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> False)
  -> (forall X1 X2, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> False)
  -> (forall X1 X2 X3, (epred2_3 X3 X2 X1 -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X1 X2, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X1 X2, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k4_tarski X1 X3) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk24_2 X3 X2) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X3 a_0_0_arytm_3 -> False) -> X3 = (k4_tarski X1 X2) -> r1_arytm_3 X1 X2 -> m1_subset_1 X2 k4_ordinal1 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk4_2 X1 X2) = X1 -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k6_numbers -> False)
  -> (forall X1 X2, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k6_numbers -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_arytm_2 X1 X2) k2_arytm_2 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_arytm_0 X1 X2) k1_numbers -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> X1 = k6_numbers -> False)
  -> (forall X1 X2, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> X1 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> X1 = k6_numbers -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> X1 = k6_numbers -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k6_subset_1 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X2 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k6_numbers -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k6_subset_1 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k8_arytm_2 X1 X2) = (k8_arytm_2 X2 X1) -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1, ((k2_arytm_0 X1 X2) = (k2_arytm_0 X2 X1) -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2, (X2 = k11_arytm_3 -> False) -> (X1 = k11_arytm_3 -> False) -> (k8_arytm_2 X1 X2) = k11_arytm_3 -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1, (r2_hidden (esk24_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k6_subset_1 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk4_2 X1 X2) = X1 -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, ((k2_arytm_0 X1 X2) = k6_numbers -> False) -> X2 = k6_numbers -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2, (k6_subset_1 X1 (k1_tarski X2)) = X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, (r2_hidden X2 a_0_1_arytm_3 -> False) -> X2 = (k4_tarski X1 np__1) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, ((k4_tarski (esk9_1 X1) (esk10_1 X1)) = X1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (r1_arytm_3 (esk9_1 X1) (esk10_1 X1) -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (k4_tarski X1 X3) = (k4_tarski X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (k4_tarski X3 X1) = (k4_tarski X4 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, ((k4_tarski (esk11_1 X1) np__1) = X1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k2_zfmisc_1 X2 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k6_subset_1 X2 (k1_tarski X1)) = X2 -> False) -> (r2_hidden X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (esk10_1 X1) = k1_xboole_0 -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_arytm_0 (k2_arytm_0 esk1_0 esk2_0) esk3_0) = (k2_arytm_0 esk1_0 (k2_arytm_0 esk2_0 esk3_0)) -> False)
  -> (forall X1, r2_hidden (k4_tarski k11_arytm_3 X1) k2_arytm_2 -> False)
  -> (forall X1 X2, v1_xboole_0 (k4_tarski X1 X2) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v3_funct_1 esk21_0 -> False)
  -> (v1_zfmisc_1 esk19_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k2_arytm_2 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (((k6_subset_1 (k2_xboole_0 k2_arytm_2 (k2_zfmisc_1 (k1_tarski k1_xboole_0) k2_arytm_2)) (k1_tarski (k4_tarski k1_xboole_0 k1_xboole_0))) = k1_numbers -> False) -> False)
  -> (forall X2 X1 X3, ((k2_xboole_0 (k6_subset_1 X1 X3) (k6_subset_1 X2 X3)) = (k6_subset_1 (k2_xboole_0 X1 X2) X3) -> False) -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_tarski (k4_tarski X1 X2)) -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (((k2_xboole_0 (k6_subset_1 a_0_0_arytm_3 a_0_1_arytm_3) k4_ordinal1) = k5_arytm_3 -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> ((r2_hidden k11_arytm_3 (k1_tarski k11_arytm_3) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((m1_subset_1 esk3_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 esk2_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 esk1_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k11_arytm_3 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 c2__arytm_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k1_tarski X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v4_funct_1 esk23_0 -> False) -> False)
  -> ((v7_ordinal1 esk22_0 -> False) -> False)
  -> ((v7_ordinal1 esk20_0 -> False) -> False)
  -> ((v2_funct_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_zfmisc_1 esk15_0 -> False) -> False)
  -> ((v2_ordinal1 esk17_0 -> False) -> False)
  -> ((v1_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> ((k11_arytm_3 = k1_xboole_0 -> False) -> False)
  -> ((k6_numbers = c2__arytm_0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
