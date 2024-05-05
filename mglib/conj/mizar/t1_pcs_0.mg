(** $I sig/MizarPreamble.mgs **)

Theorem t1_pcs_0:
 forall esk7_2:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall k1_pcs_0:set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall v3_relat_2:set -> prop,
 forall esk23_1:set -> set,
 forall k1_relat_1:set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v2_relat_2:set -> prop,
 forall esk12_1:set -> set,
 forall v5_relat_2:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v4_relat_2:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk20_1:set -> set,
 forall esk10_0:set,
 forall v1_xtuple_0:set -> prop,
 forall esk19_2:set -> set -> set,
 forall esk14_0:set,
 forall esk13_0:set,
 forall o_0_0_xboole_0:set,
 forall esk16_0:set,
 forall esk9_1:set -> set,
 forall esk17_1:set -> set,
 forall esk15_1:set -> set,
 forall esk11_2:set -> set -> set,
 forall esk18_0:set,
 forall k1_xboole_0:set,
 forall v6_relat_2:set -> prop,
 forall v7_relat_2:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk21_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v1_relat_2:set -> prop,
 forall k10_xtuple_0:set -> set,
 forall esk24_1:set -> set,
 forall esk22_1:set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall v8_relat_2:set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall r8_relat_2:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k2_pcs_0:set -> set -> set -> set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall k2_tarski:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X5 X4 X6 X1 X2 X3, (r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False) -> r1_xboole_0 X4 X5 -> r2_hidden X2 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X5 X5)) -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_pcs_0 X4 X4 X5 X5 X6 X3) -> False)
  -> (forall X4 X6 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> r1_xboole_0 X4 X2 -> r2_hidden X3 X2 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_pcs_0 X4 X4 X2 X2 X5 X6) -> False)
  -> (forall X4 X5 X6 X1 X2 X3, (m1_subset_1 (k2_pcs_0 X2 X3 X5 X6 X1 X4) (k1_zfmisc_1 (k2_zfmisc_1 (k2_xboole_0 X2 X5) (k2_xboole_0 X3 X6))) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X5 X6 X1 X2 X3, ((k2_pcs_0 X2 X3 X5 X6 X1 X4) = (k2_pcs_0 X2 X3 X5 X6 X4 X1) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X5 X6 X1 X2 X3, ((k2_pcs_0 X2 X3 X5 X6 X1 X4) = (k2_xboole_0 X1 X4) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X2 X5 X6 X3 X1, ((k2_pcs_0 X2 X3 X5 X6 X1 X1) = X1 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk6_2 X1 X2) (esk8_2 X1 X2)) (k1_tarski (esk6_2 X1 X2))) X1 -> False)
  -> (forall X4 X2 X3 X5 X1, (r2_hidden (k2_tarski (k2_tarski X3 X5) (k1_tarski X3)) X1 -> False) -> v1_relat_1 X1 -> r2_hidden X5 X2 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> r8_relat_2 X1 X2 -> r2_hidden (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) X1 -> r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1 -> False)
  -> (forall X3 X2 X4 X1, (r2_hidden (k2_tarski (k2_tarski X2 X4) (k1_tarski X2)) X1 -> False) -> v8_relat_2 X1 -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1 -> r2_hidden (k2_tarski (k2_tarski X2 X3) (k1_tarski X2)) X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk7_2 X1 X2) (esk8_2 X1 X2)) (k1_tarski (esk7_2 X1 X2))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk6_2 X1 X2) (esk7_2 X1 X2)) (k1_tarski (esk6_2 X1 X2))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X1 X3 X4, (v1_partfun1 (k2_xboole_0 X1 X3) (k2_xboole_0 X2 X4) -> False) -> v1_partfun1 X3 X4 -> v1_partfun1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X2 X3, (m1_subset_1 (k1_pcs_0 X2 X3 X1) (k1_zfmisc_1 (k2_xboole_0 X2 X3)) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk22_1 X1) (esk24_1 X1)) (k1_tarski (esk22_1 X1))) X1 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X2 X4 X3 X1, (v3_relat_2 (k2_xboole_0 X1 X3) -> False) -> v3_relat_2 X3 -> v3_relat_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_2 (k2_xboole_0 X1 X3) -> False) -> v1_relat_2 X3 -> v1_relat_2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk23_1 X1) (esk24_1 X1)) (k1_tarski (esk23_1 X1))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk22_1 X1) (esk23_1 X1)) (k1_tarski (esk22_1 X1))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1 X2 X3, ((k1_pcs_0 X2 X3 X1) = (k1_relat_1 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_relat_2 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v3_relat_2 X2 -> v3_relat_2 X1 -> False)
  -> (forall X1 X2, (v2_relat_2 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_2 X2 -> v2_relat_2 X1 -> False)
  -> (forall X1 X2, (v1_relat_2 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_relat_2 X2 -> v1_relat_2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> v1_relat_1 X1 -> r8_relat_2 X1 (k1_relat_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1, ((k2_xboole_0 (k9_xtuple_0 X1) (k10_xtuple_0 X1)) = (k1_relat_1 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (r8_relat_2 X1 (k1_relat_1 X1) -> False) -> v8_relat_2 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v5_relat_2 X1 -> False) -> v8_relat_2 X1 -> v1_relat_1 X1 -> v2_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v8_relat_2 X1 -> v1_relat_1 X1 -> v3_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v8_relat_2 X1 -> v1_relat_1 X1 -> v3_relat_2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk12_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v6_relat_2 X1 -> False) -> v1_relat_1 X1 -> v7_relat_2 X1 -> False)
  -> (forall X1, (v6_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v6_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v5_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v5_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_relat_2 X1 -> False) -> v1_relat_1 X1 -> v5_relat_2 X1 -> False)
  -> (forall X1, (v4_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_2 X1 -> False) -> v1_relat_1 X1 -> v5_relat_2 X1 -> False)
  -> (forall X1, (v2_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_relat_1 X1 -> v7_relat_2 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v8_relat_2 (k2_pcs_0 esk1_0 esk1_0 esk2_0 esk2_0 esk3_0 esk4_0) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk20_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk11_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 esk2_0 esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk11_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((r1_xboole_0 esk1_0 esk2_0 -> False) -> False)
  -> (forall X1, (v4_relat_2 (esk15_1 X1) -> False) -> False)
  -> (forall X1, (v3_relat_2 (esk15_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_2 (esk15_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk15_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v8_relat_2 (esk15_1 X1) -> False) -> False)
  -> ((v1_xtuple_0 esk14_0 -> False) -> False)
  -> ((v2_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v8_relat_2 esk4_0 -> False) -> False)
  -> ((v8_relat_2 esk3_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
