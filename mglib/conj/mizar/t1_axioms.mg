(** $I sig/MizarPreamble.mgs **)

Theorem t1_axioms:
 forall k3_xboole_0:set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall r1_xxreal_0:set -> set -> prop,
 forall epred2_2:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k2_arytm_2:set,
 forall r1_arytm_2:set -> set -> prop,
 forall k6_numbers:set,
 forall esk29_2:set -> set -> set,
 forall esk28_2:set -> set -> set,
 forall esk27_2:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk33_2:set -> set -> set,
 forall a_1_0_axioms:set -> set,
 forall k1_numbers:set,
 forall esk14_2:set -> set -> set,
 forall k8_subset_1:set -> set -> set -> set,
 forall k1_xboole_0:set,
 forall k4_ordinal1:set,
 forall r1_arytm_3:set -> set -> prop,
 forall a_0_0_arytm_3:set,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk10_2:set -> set -> set,
 forall esk12_1:set -> set,
 forall esk11_1:set -> set,
 forall esk13_1:set -> set,
 forall esk24_2:set -> set -> set,
 forall v1_xreal_0:set -> prop,
 forall esk4_1:set -> set,
 forall esk3_1:set -> set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk23_2:set -> set -> set,
 forall v1_xxreal_0:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall esk21_0:set,
 forall k12_arytm_3:set,
 forall k5_numbers:set,
 forall k5_arytm_3:set,
 forall esk9_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk19_0:set,
 forall esk15_0:set,
 forall k1_arytm_3:set,
 forall esk16_0:set,
 forall esk20_0:set,
 forall esk18_0:set,
 forall v2_xxreal_0:set -> prop,
 forall c1__axioms:set,
 forall k6_subset_1:set -> set -> set,
 forall esk17_0:set,
 forall v1_finset_1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall esk6_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall np__1:set,
 forall a_0_1_arytm_3:set,
 forall esk22_2:set -> set -> set,
 forall k11_arytm_3:set,
 forall k2_xxreal_0:set,
 forall k1_xxreal_0:set,
 forall esk31_2:set -> set -> set,
 forall esk30_2:set -> set -> set,
 forall esk32_2:set -> set -> set,
 forall epred1_2:set -> set -> prop,
 forall esk7_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk25_4:set -> set -> set -> set -> set,
 forall esk26_4:set -> set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X3 X4 X1 X2, ((k2_tarski (k2_tarski (esk25_4 X2 X3 X4 X1) (esk26_4 X2 X3 X4 X1)) (k1_tarski (esk25_4 X2 X3 X4 X1))) = X1 -> False) -> r2_hidden X1 X2 -> r1_tarski X2 (k2_zfmisc_1 X3 X4) -> False)
  -> (forall X2 X3 X4 X1, (r2_hidden (esk26_4 X1 X2 X3 X4) X3 -> False) -> r2_hidden X4 X1 -> r1_tarski X1 (k2_zfmisc_1 X2 X3) -> False)
  -> (forall X2 X3 X4 X1, (r2_hidden (esk25_4 X1 X2 X3 X4) X2 -> False) -> r2_hidden X4 X1 -> r1_tarski X1 (k2_zfmisc_1 X2 X3) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X2 -> r2_hidden (esk8_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk7_3 X1 X2 X3) X3 -> r2_hidden (esk7_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X4 X3 X1 X2, (r1_xxreal_0 X1 X2 -> False) -> X2 = (k2_tarski (k2_tarski k6_numbers X4) (k1_tarski k6_numbers)) -> X1 = (k2_tarski (k2_tarski k6_numbers X3) (k1_tarski k6_numbers)) -> r1_arytm_2 X4 X3 -> epred2_2 X1 X2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X3 k2_arytm_2 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X2 X1 X3 X4, (r1_xxreal_0 X3 X4 -> False) -> X4 = (k2_tarski (k2_tarski k6_numbers X2) (k1_tarski k6_numbers)) -> X3 = (k2_tarski (k2_tarski k6_numbers X1) (k1_tarski k6_numbers)) -> r1_arytm_2 X2 X1 -> epred1_2 X4 X3 -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> r2_hidden X4 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X3 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X5 X4 X2 X1 X3, (r1_arytm_2 (esk29_2 X1 X2) X3 -> False) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden X3 X2 -> m1_subset_1 X5 k2_arytm_2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X1 (k1_zfmisc_1 k2_arytm_2) -> r1_arytm_2 (esk27_2 X1 X2) (esk28_2 X1 X2) -> False)
  -> (forall X5 X4 X2 X3 X1, (r1_arytm_2 X1 (esk29_2 X2 X3) -> False) -> r2_hidden X5 X3 -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X5 k2_arytm_2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> m1_subset_1 X3 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> r1_arytm_2 (esk27_2 X2 X3) (esk28_2 X2 X3) -> False)
  -> (forall X2 X1, ((k2_tarski (k2_tarski k6_numbers (esk33_2 X2 X1)) (k1_tarski k6_numbers)) = X1 -> False) -> r1_xxreal_0 X2 X1 -> epred1_2 X1 X2 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X2 X1, ((k2_tarski (k2_tarski k6_numbers (esk32_2 X1 X2)) (k1_tarski k6_numbers)) = X1 -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X4 X5 X1 X2, (r2_hidden (esk28_2 X1 X2) X2 -> False) -> (r1_arytm_2 (esk29_2 X1 X2) X3 -> False) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden X3 X2 -> m1_subset_1 X5 k2_arytm_2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X1 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X3 X4 X5 X2 X1, (r2_hidden (esk27_2 X1 X2) X1 -> False) -> (r1_arytm_2 (esk29_2 X1 X2) X3 -> False) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden X3 X2 -> m1_subset_1 X5 k2_arytm_2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X1 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X4 X5 X2 X3 X1, (r1_arytm_2 X1 (esk29_2 X2 X3) -> False) -> (r2_hidden (esk28_2 X2 X3) X3 -> False) -> r2_hidden X5 X3 -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X5 k2_arytm_2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> m1_subset_1 X3 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X4 X5 X2 X3 X1, (r1_arytm_2 X1 (esk29_2 X2 X3) -> False) -> (r2_hidden (esk27_2 X2 X3) X2 -> False) -> r2_hidden X5 X3 -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X5 k2_arytm_2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> m1_subset_1 X3 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X4 X5 X2 X1 X3, (r1_arytm_2 (esk29_2 X1 X2) X3 -> False) -> (m1_subset_1 (esk28_2 X1 X2) k2_arytm_2 -> False) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden X3 X2 -> m1_subset_1 X5 k2_arytm_2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X1 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X4 X5 X2 X1 X3, (r1_arytm_2 (esk29_2 X1 X2) X3 -> False) -> (m1_subset_1 (esk27_2 X1 X2) k2_arytm_2 -> False) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden X3 X2 -> m1_subset_1 X5 k2_arytm_2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X1 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X4 X5 X2 X3 X1, (r1_arytm_2 X1 (esk29_2 X2 X3) -> False) -> (m1_subset_1 (esk28_2 X2 X3) k2_arytm_2 -> False) -> r2_hidden X5 X3 -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X5 k2_arytm_2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> m1_subset_1 X3 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X4 X5 X2 X3 X1, (r1_arytm_2 X1 (esk29_2 X2 X3) -> False) -> (m1_subset_1 (esk27_2 X2 X3) k2_arytm_2 -> False) -> r2_hidden X5 X3 -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> m1_subset_1 X5 k2_arytm_2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> m1_subset_1 X3 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X2, (r2_hidden (k2_tarski (k2_tarski k6_numbers (esk14_2 X1 X2)) (k1_tarski k6_numbers)) X2 -> False) -> r2_hidden X1 (a_1_0_axioms X2) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X2 X1, (r1_arytm_2 (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk29_2 X1 X2) k2_arytm_2 -> False) -> r2_hidden X3 X2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X1 (k1_zfmisc_1 k2_arytm_2) -> r1_arytm_2 (esk27_2 X1 X2) (esk28_2 X1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk33_2 X1 X2) k2_arytm_2 -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk32_2 X1 X2) k2_arytm_2 -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X1 X2 X3, (r2_hidden X2 (a_1_0_axioms X3) -> False) -> X1 = X2 -> m1_subset_1 X1 k2_arytm_2 -> m1_subset_1 X3 (k1_zfmisc_1 k1_numbers) -> r2_hidden (k2_tarski (k2_tarski k6_numbers X1) (k1_tarski k6_numbers)) X3 -> False)
  -> (forall X1 X2, (r1_xxreal_0 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> epred1_2 X1 X2 -> r2_hidden X1 k2_arytm_2 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X3 X1 X2, (r2_hidden (esk28_2 X1 X2) X2 -> False) -> (m1_subset_1 (esk29_2 X1 X2) k2_arytm_2 -> False) -> r2_hidden X3 X2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X1 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk27_2 X1 X2) X1 -> False) -> (m1_subset_1 (esk29_2 X1 X2) k2_arytm_2 -> False) -> r2_hidden X3 X2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X1 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk28_2 X1 X2) k2_arytm_2 -> False) -> (m1_subset_1 (esk29_2 X1 X2) k2_arytm_2 -> False) -> r2_hidden X3 X2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X1 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk27_2 X1 X2) k2_arytm_2 -> False) -> (m1_subset_1 (esk29_2 X1 X2) k2_arytm_2 -> False) -> r2_hidden X3 X2 -> m1_subset_1 X3 k2_arytm_2 -> m1_subset_1 X2 (k1_zfmisc_1 k2_arytm_2) -> m1_subset_1 X1 (k1_zfmisc_1 k2_arytm_2) -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k8_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (r1_arytm_2 (esk30_2 X1 X2) (esk31_2 X1 X2) -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> r2_hidden X2 k2_arytm_2 -> r2_hidden X1 k2_arytm_2 -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X3 a_0_0_arytm_3 -> False) -> X3 = (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> r1_arytm_3 X1 X2 -> m1_subset_1 X2 k4_ordinal1 -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X4 X3 X1 X2, (r1_xxreal_0 X1 X2 -> False) -> X2 = X4 -> X1 = X3 -> r1_arytm_2 X3 X4 -> epred2_2 X1 X2 -> m1_subset_1 X4 k2_arytm_2 -> m1_subset_1 X3 k2_arytm_2 -> r2_hidden X2 k2_arytm_2 -> r2_hidden X1 k2_arytm_2 -> False)
  -> (forall X2 X1 X3 X4, (r1_xxreal_0 X3 X4 -> False) -> X2 = X4 -> X1 = X3 -> r1_arytm_2 X1 X2 -> epred1_2 X4 X3 -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> r2_hidden X4 k2_arytm_2 -> r2_hidden X3 k2_arytm_2 -> False)
  -> (forall X1 X2, (X2 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> False)
  -> (forall X1 X2, (X2 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) = (k2_tarski (k2_tarski X2 X4) (k1_tarski X2)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) = (k2_tarski (k2_tarski X4 X2) (k1_tarski X4)) -> False)
  -> (forall X1, X1 = k11_arytm_3 -> r2_hidden (k2_tarski (k2_tarski k11_arytm_3 X1) (k1_tarski k11_arytm_3)) k1_numbers -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k8_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (r1_xxreal_0 X2 X1 -> False) -> epred2_2 X2 X1 -> r2_hidden X1 k2_arytm_2 -> r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk31_2 X1 X2) k2_arytm_2 -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> r2_hidden X2 k2_arytm_2 -> r2_hidden X1 k2_arytm_2 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk30_2 X1 X2) k2_arytm_2 -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> r2_hidden X2 k2_arytm_2 -> r2_hidden X1 k2_arytm_2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk10_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (X2 = k2_xxreal_0 -> False) -> (X1 = k1_xxreal_0 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> r1_xxreal_0 X2 X1 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (X2 = k2_xxreal_0 -> False) -> (X1 = k1_xxreal_0 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> r1_xxreal_0 X2 X1 -> epred1_2 X1 X2 -> False)
  -> (forall X1, (X1 = k11_arytm_3 -> False) -> (r2_hidden (k2_tarski (k2_tarski k11_arytm_3 X1) (k1_tarski k11_arytm_3)) k1_numbers -> False) -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk22_2 X3 X2) -> False)
  -> (forall X1 X2, (X2 = k2_xxreal_0 -> False) -> (X1 = k1_xxreal_0 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> r1_xxreal_0 X2 X1 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (X2 = k2_xxreal_0 -> False) -> (X1 = k1_xxreal_0 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> r1_xxreal_0 X2 X1 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (X2 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> False)
  -> (forall X1 X2, (X2 = k1_xxreal_0 -> False) -> (X1 = k2_xxreal_0 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk11_1 X1) (esk12_1 X1)) (k1_tarski (esk11_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1 X2, (r2_hidden X2 a_0_1_arytm_3 -> False) -> X2 = (k2_tarski (k2_tarski X1 np__1) (k1_tarski X1)) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X2 X1, ((esk31_2 X2 X1) = X1 -> False) -> r1_xxreal_0 X2 X1 -> epred1_2 X1 X2 -> r2_hidden X2 k2_arytm_2 -> r2_hidden X1 k2_arytm_2 -> False)
  -> (forall X2 X1, ((esk30_2 X1 X2) = X1 -> False) -> r1_xxreal_0 X1 X2 -> epred1_2 X2 X1 -> r2_hidden X2 k2_arytm_2 -> r2_hidden X1 k2_arytm_2 -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k3_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 X2 -> False) -> r1_xboole_0 X1 X3 -> r1_tarski X1 (k2_xboole_0 X2 X3) -> False)
  -> (forall X1 X2, (m1_subset_1 (esk14_2 X1 X2) k2_arytm_2 -> False) -> r2_hidden X1 (a_1_0_axioms X2) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k2_xxreal_0 -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X2 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k2_xxreal_0 -> epred1_2 X2 X1 -> False)
  -> (forall X1 X2, (r1_xxreal_0 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k2_xxreal_0 -> epred1_2 X2 X1 -> False)
  -> (forall X1 X2, (r1_xxreal_0 X1 X2 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k2_xxreal_0 -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k1_xxreal_0 -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r2_hidden X1 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k1_xxreal_0 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (r1_xxreal_0 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X1 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k1_xxreal_0 -> epred1_2 X1 X2 -> False)
  -> (forall X1 X2, (r1_xxreal_0 X2 X1 -> False) -> (r2_hidden X2 k2_arytm_2 -> False) -> (r2_hidden X2 (k2_zfmisc_1 (k1_tarski k6_numbers) k2_arytm_2) -> False) -> X1 = k1_xxreal_0 -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk5_2 X1 X2) = X1 -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (esk13_1 X1) np__1) (k1_tarski (esk13_1 X1))) = X1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X2 X1, ((k8_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, ((esk14_2 X1 X2) = X1 -> False) -> r2_hidden X1 (a_1_0_axioms X2) -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden (esk24_2 X1 X2) X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (m1_subset_1 (esk24_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v1_xreal_0 X1 -> r1_xxreal_0 X1 (esk4_1 X1) -> r1_xxreal_0 (esk3_1 X1) X1 -> False)
  -> (forall X2 X1, (r1_arytm_2 X2 X1 -> False) -> (r1_arytm_2 X1 X2 -> False) -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1 X2, (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r2_hidden X2 esk2_0 -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X2 X1, (X1 = k11_arytm_3 -> False) -> X2 = k11_arytm_3 -> r1_arytm_2 X1 X2 -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X2 X1, (r2_hidden (esk22_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk5_2 X1 X2) = X1 -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_arytm_2 X1 X2 -> False) -> X1 = k11_arytm_3 -> m1_subset_1 X2 k2_arytm_2 -> m1_subset_1 X1 k2_arytm_2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk23_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk23_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_arytm_3 X2 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_arytm_3 X1 X2 -> False)
  -> (forall X1, (r1_arytm_3 (esk11_1 X1) (esk12_1 X1) -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_1_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) k4_ordinal1 -> False) -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (epred2_2 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (esk12_1 X1) = k1_xboole_0 -> r2_hidden X1 a_0_0_arytm_3 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (r2_hidden (esk4_1 X1) esk2_0 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (r2_hidden (esk3_1 X1) esk1_0 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v1_xreal_0 (esk4_1 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 (esk3_1 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 k12_arytm_3 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k2_arytm_2 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (v1_xreal_0 k2_xxreal_0 -> False)
  -> (v1_xreal_0 k1_xxreal_0 -> False)
  -> (((k6_subset_1 (k2_xboole_0 k2_arytm_2 (k2_zfmisc_1 (k1_tarski k1_xboole_0) k2_arytm_2)) (k1_tarski (k2_tarski (k2_tarski k1_xboole_0 k1_xboole_0) (k1_tarski k1_xboole_0)))) = k1_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((r1_xboole_0 k2_arytm_2 (k2_zfmisc_1 (k1_tarski k11_arytm_3) k2_arytm_2) -> False) -> False)
  -> (forall X1 X2, (r1_tarski (k3_xboole_0 X1 X2) X1 -> False) -> False)
  -> (((k2_tarski (k2_tarski k6_numbers k1_numbers) (k1_tarski k6_numbers)) = k2_xxreal_0 -> False) -> False)
  -> (((k2_xboole_0 (k6_subset_1 a_0_0_arytm_3 a_0_1_arytm_3) k4_ordinal1) = k5_arytm_3 -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> ((r2_hidden k1_xboole_0 (k1_tarski k1_xboole_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 esk1_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((r1_tarski k2_arytm_2 k1_numbers -> False) -> False)
  -> ((r2_hidden k12_arytm_3 k2_arytm_2 -> False) -> False)
  -> ((r2_hidden k11_arytm_3 k2_arytm_2 -> False) -> False)
  -> ((m1_subset_1 k12_arytm_3 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 k11_arytm_3 k5_arytm_3 -> False) -> False)
  -> ((m1_subset_1 c1__axioms k2_arytm_2 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((v2_xxreal_0 esk18_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xxreal_0 esk20_0 -> False) -> False)
  -> ((v1_xxreal_0 esk18_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk20_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v7_ordinal1 esk21_0 -> False) -> False)
  -> ((v7_ordinal1 esk19_0 -> False) -> False)
  -> ((v2_ordinal1 esk17_0 -> False) -> False)
  -> ((v1_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v3_ordinal1 esk15_0 -> False) -> False)
  -> ((v3_ordinal1 k12_arytm_3 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_xreal_0 esk20_0 -> False) -> False)
  -> ((v1_xreal_0 esk18_0 -> False) -> False)
  -> ((v1_xreal_0 esk16_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> ((k12_arytm_3 = k1_arytm_3 -> False) -> False)
  -> ((k11_arytm_3 = k1_xboole_0 -> False) -> False)
  -> ((c1__axioms = k6_numbers -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k1_numbers = k1_xxreal_0 -> False) -> False)
  -> ((k1_xboole_0 = o_0_0_xboole_0 -> False) -> False)
  -> ((np__1 = k1_arytm_3 -> False) -> False)
  -> False.
Admitted.
