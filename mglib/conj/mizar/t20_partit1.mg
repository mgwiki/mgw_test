(** $I sig/MizarPreamble.mgs **)

Theorem t20_partit1:
 forall esk11_5:set -> set -> set -> set -> set -> set,
 forall esk17_4:set -> set -> set -> set -> set,
 forall o_1_0_partit1:set -> set,
 forall a_3_1_partit1:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k1_xboole_0:set,
 forall esk9_2:set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall r1_setfam_1:set -> set -> prop,
 forall esk4_3:set -> set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall esk30_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v6_membered:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v4_membered:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v2_membered:set -> prop,
 forall esk29_1:set -> set,
 forall v1_relat_2:set -> prop,
 forall esk28_1:set -> set,
 forall v7_membered:set -> prop,
 forall esk26_0:set,
 forall esk23_0:set,
 forall esk24_1:set -> set,
 forall esk21_0:set,
 forall esk15_1:set -> set,
 forall esk16_1:set -> set,
 forall esk19_2:set -> set -> set,
 forall esk18_0:set,
 forall esk25_0:set,
 forall esk27_1:set -> set,
 forall esk22_1:set -> set,
 forall v1_setfam_1:set -> prop,
 forall esk20_1:set -> set,
 forall v1_membered:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall v3_membered:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v5_membered:set -> prop,
 forall v1_int_1:set -> prop,
 forall esk31_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall v4_relat_1:set -> set -> prop,
 forall esk14_3:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v8_relat_2:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall esk13_3:set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall k2_tarski:set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall m1_eqrel_1:set -> set -> prop,
 forall v3_relat_2:set -> prop,
 forall k4_partit1:set -> set -> set,
     (forall X4 X1 X2 X3, (X3 = (k4_partit1 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v3_relat_2 X3 -> v8_relat_2 X3 -> m1_eqrel_1 X2 X1 -> r2_hidden X4 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> r2_hidden (esk12_3 X1 X2 X3) X4 -> r2_hidden (esk13_3 X1 X2 X3) X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> r2_hidden (k2_tarski (k2_tarski (esk12_3 X1 X2 X3) (esk13_3 X1 X2 X3)) (k1_tarski (esk12_3 X1 X2 X3))) X3 -> False)
  -> (forall X3 X2 X4 X5 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk11_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 X1) -> False) -> X3 = (k4_partit1 X1 X2) -> v3_relat_2 X3 -> v8_relat_2 X3 -> m1_eqrel_1 X2 X1 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> r2_hidden (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) X3 -> False)
  -> (forall X3 X2 X4 X5 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk11_5 X1 X2 X3 X4 X5) X2 -> False) -> X3 = (k4_partit1 X1 X2) -> v3_relat_2 X3 -> v8_relat_2 X3 -> m1_eqrel_1 X2 X1 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> r2_hidden (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) X3 -> False)
  -> (forall X4 X3 X1 X5 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (esk11_5 X2 X3 X4 X1 X5) -> False) -> X4 = (k4_partit1 X2 X3) -> v3_relat_2 X4 -> v8_relat_2 X4 -> m1_eqrel_1 X3 X2 -> v1_partfun1 X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k2_tarski (k2_tarski X1 X5) (k1_tarski X1)) X4 -> False)
  -> (forall X4 X3 X5 X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (esk11_5 X2 X3 X4 X5 X1) -> False) -> X4 = (k4_partit1 X2 X3) -> v3_relat_2 X4 -> v8_relat_2 X4 -> m1_eqrel_1 X3 X2 -> v1_partfun1 X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> r2_hidden (k2_tarski (k2_tarski X5 X1) (k1_tarski X5)) X4 -> False)
  -> (forall X4 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (o_1_0_partit1 X1) (esk17_4 X2 X3 X4 X1)) (k1_tarski (o_1_0_partit1 X1))) (k4_partit1 X3 X4) -> False) -> m1_eqrel_1 X4 X3 -> r2_hidden X2 (a_3_1_partit1 X3 X4 X1) -> False)
  -> (forall X3 X2 X1, (X3 = (k4_partit1 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk13_3 X1 X2 X3) (esk14_3 X1 X2 X3) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk12_3 X1 X2 X3) (esk13_3 X1 X2 X3)) (k1_tarski (esk12_3 X1 X2 X3))) X3 -> False) -> v3_relat_2 X3 -> v8_relat_2 X3 -> m1_eqrel_1 X2 X1 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X2 X1, (X3 = (k4_partit1 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk12_3 X1 X2 X3) (esk14_3 X1 X2 X3) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk12_3 X1 X2 X3) (esk13_3 X1 X2 X3)) (k1_tarski (esk12_3 X1 X2 X3))) X3 -> False) -> v3_relat_2 X3 -> v8_relat_2 X3 -> m1_eqrel_1 X2 X1 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X2 X1, (X3 = (k4_partit1 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk14_3 X1 X2 X3) (k1_zfmisc_1 X1) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk12_3 X1 X2 X3) (esk13_3 X1 X2 X3)) (k1_tarski (esk12_3 X1 X2 X3))) X3 -> False) -> v3_relat_2 X3 -> v8_relat_2 X3 -> m1_eqrel_1 X2 X1 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X2 X1, (X3 = (k4_partit1 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk14_3 X1 X2 X3) X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk12_3 X1 X2 X3) (esk13_3 X1 X2 X3)) (k1_tarski (esk12_3 X1 X2 X3))) X3 -> False) -> v3_relat_2 X3 -> v8_relat_2 X3 -> m1_eqrel_1 X2 X1 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X1 X4 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk17_4 X1 X2 X3 X4) X2 -> False) -> m1_eqrel_1 X3 X2 -> r2_hidden X1 (a_3_1_partit1 X2 X3 X4) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk6_2 X1 X2) (esk7_2 X1 X2)) (k1_tarski (esk6_2 X1 X2))) X2 -> False)
  -> (forall X3 X1 X4 X2, ((esk17_4 X1 X2 X3 X4) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> m1_eqrel_1 X3 X2 -> r2_hidden X1 (a_3_1_partit1 X2 X3 X4) -> False)
  -> (forall X3 X5 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X3 (a_3_1_partit1 X2 X5 X4) -> False) -> X1 = X3 -> m1_eqrel_1 X5 X2 -> m1_subset_1 X1 X2 -> r2_hidden (k2_tarski (k2_tarski (o_1_0_partit1 X4) X1) (k1_tarski (o_1_0_partit1 X4))) (k4_partit1 X2 X5) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk6_2 X1 X2) (esk7_2 X1 X2)) (k1_tarski (esk6_2 X1 X2))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X6 X5 X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) X6 -> False) -> X6 = (k4_partit1 X2 X3) -> v3_relat_2 X6 -> v8_relat_2 X6 -> m1_eqrel_1 X3 X2 -> r2_hidden X5 X1 -> r2_hidden X4 X1 -> r2_hidden X1 X3 -> v1_partfun1 X6 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X3 X4 X2, (r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X2 -> False) -> v1_relat_1 X1 -> r1_tarski X1 X2 -> r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1 -> False)
  -> (forall X1 X2, ((esk9_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r1_xboole_0 (esk9_2 X1 X2) (esk10_2 X1 X2) -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> (r1_xboole_0 X4 X1 -> False) -> m1_eqrel_1 X3 X2 -> r2_hidden X4 X3 -> r2_hidden X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (r2_hidden (esk4_3 X1 X2 X3) X2 -> False) -> r1_setfam_1 X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X3 X2 X1, (r1_tarski X1 (esk4_3 X2 X3 X1) -> False) -> r1_setfam_1 X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, ((esk9_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk10_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, ((esk9_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> (esk10_2 X1 X2) = (esk9_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X2, ((esk9_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk9_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, X1 = k1_xboole_0 -> m1_eqrel_1 X2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk9_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k4_partit1 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk30_2 X3 X2) -> False)
  -> (r1_setfam_1 esk2_0 esk3_0 -> r1_tarski (k4_partit1 esk1_0 esk2_0) (k4_partit1 esk1_0 esk3_0) -> False)
  -> (forall X1 X3 X2, (r1_setfam_1 X3 X2 -> False) -> r2_hidden X1 X2 -> r1_tarski (esk5_2 X3 X2) X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, ((k5_setfam_1 X1 X2) = X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk8_2 X1 X2) X2 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 (k4_partit1 X1 X2) X1 -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> ((r1_setfam_1 esk2_0 esk3_0 -> False) -> (r1_tarski (k4_partit1 esk1_0 esk2_0) (k4_partit1 esk1_0 esk3_0) -> False) -> False)
  -> (forall X2 X1, (r2_hidden (esk30_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v8_relat_2 (k4_partit1 X1 X2) -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v3_relat_2 (k4_partit1 X1 X2) -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk31_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk31_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk8_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_setfam_1 X1 X2 -> False) -> (r2_hidden (esk5_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v6_membered (k2_tarski X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v5_membered (k2_tarski X1 X2) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (v4_membered (k2_tarski X1 X2) -> False) -> v1_rat_1 X2 -> v1_rat_1 X1 -> False)
  -> (forall X2 X1, (v3_membered (k2_tarski X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v2_membered (k2_tarski X1 X2) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (v1_membered (k2_tarski X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_relat_1 X1 -> v3_relat_2 X1 -> v8_relat_2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk28_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v6_membered (k1_tarski X1) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v5_membered (k1_tarski X1) -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v4_membered (k1_tarski X1) -> False) -> v1_rat_1 X1 -> False)
  -> (forall X1, (v3_membered (k1_tarski X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v2_membered (k1_tarski X1) -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_membered (k1_tarski X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk27_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (o_1_0_partit1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (r1_setfam_1 X1 X1 -> False) -> False)
  -> ((m1_eqrel_1 esk3_0 esk1_0 -> False) -> False)
  -> ((m1_eqrel_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk24_1 X1) -> False) -> False)
  -> ((v7_membered esk26_0 -> False) -> False)
  -> ((v6_membered esk26_0 -> False) -> False)
  -> ((v6_membered esk23_0 -> False) -> False)
  -> ((v6_membered esk18_0 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
