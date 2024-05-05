(** $I sig/MizarPreamble.mgs **)

Theorem t20_taxonom2:
 forall r1_setfam_1:set -> set -> prop,
 forall k1_xboole_0:set,
 forall v6_taxonom2:set -> set -> prop,
 forall esk48_3:set -> set -> set -> set,
 forall esk38_3:set -> set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall esk19_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall esk20_3:set -> set -> set -> set,
 forall esk55_2:set -> set -> set,
 forall esk56_1:set -> set,
 forall esk1_0:set,
 forall esk4_1:set -> set,
 forall esk3_1:set -> set,
 forall esk5_1:set -> set,
 forall esk6_1:set -> set,
 forall esk22_2:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall v3_taxonom2:set -> prop,
 forall esk14_2:set -> set -> set,
 forall r3_xboole_0:set -> set -> prop,
 forall esk53_2:set -> set -> set,
 forall esk23_1:set -> set,
 forall esk24_1:set -> set,
 forall esk36_1:set -> set,
 forall esk2_0:set,
 forall esk35_1:set -> set,
 forall esk27_1:set -> set,
 forall esk37_1:set -> set,
 forall esk25_1:set -> set,
 forall esk28_1:set -> set,
 forall esk30_0:set,
 forall esk26_1:set -> set,
 forall esk32_1:set -> set,
 forall esk33_0:set,
 forall esk34_1:set -> set,
 forall esk10_1:set -> set,
 forall esk31_1:set -> set,
 forall v1_setfam_1:set -> prop,
 forall esk29_1:set -> set,
 forall esk16_1:set -> set,
 forall esk15_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk47_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall k6_subset_1:set -> set -> set,
 forall esk54_1:set -> set,
 forall esk13_2:set -> set -> set,
 forall esk21_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall m1_taxonom1:set -> set -> prop,
 forall esk17_3:set -> set -> set -> set,
 forall esk39_2:set -> set -> set,
 forall m1_taxonom2:set -> set -> prop,
 forall esk41_3:set -> set -> set -> set,
 forall esk42_3:set -> set -> set -> set,
 forall esk40_3:set -> set -> set -> set,
 forall v3_abian:set -> set -> prop,
 forall v5_taxonom2:set -> set -> prop,
 forall esk44_4:set -> set -> set -> set -> set,
 forall esk43_3:set -> set -> set -> set,
 forall esk46_4:set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_partit1:set -> set,
 forall esk45_3:set -> set -> set -> set,
 forall esk51_3:set -> set -> set -> set,
 forall esk52_4:set -> set -> set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k7_subset_1:set -> set -> set -> set,
 forall m1_eqrel_1:set -> set -> prop,
 forall esk49_5:set -> set -> set -> set -> set -> set,
 forall esk50_6:set -> set -> set -> set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X2 X6 X1 X3 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski (esk49_5 X2 X5 X3 X4 X6) X4 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False)
  -> (forall X2 X6 X1 X4 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski (esk49_5 X2 X5 X3 X4 X6) X4 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False)
  -> (forall X2 X6 X1 X3 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_xboole_0 X4 (esk49_5 X2 X5 X3 X4 X6) -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False)
  -> (forall X2 X6 X1 X3 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski X4 (esk49_5 X2 X5 X3 X4 X6) -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False)
  -> (forall X2 X6 X1 X4 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_xboole_0 X4 (esk49_5 X2 X5 X3 X4 X6) -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False)
  -> (forall X2 X6 X1 X4 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski X4 (esk49_5 X2 X5 X3 X4 X6) -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False)
  -> (forall X2 X1 X3 X4 X6 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk49_5 X2 X5 X3 X4 X6) X6 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False)
  -> (forall X2 X1 X3 X4 X6 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk49_5 X2 X5 X3 X4 X6) X6 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False)
  -> (forall X2 X6 X1 X3 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski (esk49_5 X2 X5 X3 X4 X6) X4 -> False)
  -> (forall X2 X6 X1 X4 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski (esk49_5 X2 X5 X3 X4 X6) X4 -> False)
  -> (forall X2 X6 X1 X3 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski (esk49_5 X2 X5 X3 X4 X6) X4 -> False)
  -> (forall X2 X6 X1 X4 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski (esk49_5 X2 X5 X3 X4 X6) X4 -> False)
  -> (forall X2 X6 X1 X3 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_xboole_0 X4 (esk49_5 X2 X5 X3 X4 X6) -> False)
  -> (forall X2 X6 X1 X3 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski X4 (esk49_5 X2 X5 X3 X4 X6) -> False)
  -> (forall X2 X6 X1 X4 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_xboole_0 X4 (esk49_5 X2 X5 X3 X4 X6) -> False)
  -> (forall X2 X6 X1 X4 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski X4 (esk49_5 X2 X5 X3 X4 X6) -> False)
  -> (forall X2 X6 X1 X3 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_xboole_0 X4 (esk49_5 X2 X5 X3 X4 X6) -> False)
  -> (forall X2 X6 X1 X3 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski X4 (esk49_5 X2 X5 X3 X4 X6) -> False)
  -> (forall X2 X6 X1 X4 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_xboole_0 X4 (esk49_5 X2 X5 X3 X4 X6) -> False)
  -> (forall X2 X6 X1 X4 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> r1_tarski X4 (esk49_5 X2 X5 X3 X4 X6) -> False)
  -> (forall X2 X1 X3 X4 X6 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk49_5 X2 X5 X3 X4 X6) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> False)
  -> (forall X2 X1 X3 X4 X6 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk49_5 X2 X5 X3 X4 X6) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_tarski (esk50_6 X2 X5 X3 X4 X6 X1) X4 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> False)
  -> (forall X2 X1 X3 X4 X6 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk49_5 X2 X5 X3 X4 X6) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X2 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> False)
  -> (forall X2 X1 X3 X4 X6 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk49_5 X2 X5 X3 X4 X6) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X6 -> False) -> (r2_hidden (esk50_6 X2 X5 X3 X4 X6 X1) X1 -> False) -> (r1_setfam_1 (k2_xboole_0 X1 (k7_subset_1 (k1_zfmisc_1 X2) X3 (k1_tarski X4))) X3 -> False) -> r2_hidden X5 X6 -> r2_hidden X4 X3 -> r1_tarski X5 X4 -> m1_eqrel_1 X6 X2 -> m1_eqrel_1 X3 X2 -> False)
  -> (forall X2 X3 X7 X4 X6 X1 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> r1_tarski (esk51_3 X2 X5 X3) X5 -> r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> r2_hidden (esk52_4 X2 X5 X3 X6) X3 -> r1_xboole_0 (esk52_4 X2 X5 X3 X6) X5 -> False)
  -> (forall X2 X3 X7 X4 X6 X1 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> r1_xboole_0 X5 (esk51_3 X2 X5 X3) -> r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> r2_hidden (esk52_4 X2 X5 X3 X6) X3 -> r1_xboole_0 (esk52_4 X2 X5 X3 X6) X5 -> False)
  -> (forall X2 X3 X7 X4 X6 X1 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> r1_tarski X5 (esk51_3 X2 X5 X3) -> r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> r2_hidden (esk52_4 X2 X5 X3 X6) X3 -> r1_xboole_0 (esk52_4 X2 X5 X3 X6) X5 -> False)
  -> (forall X2 X1 X6 X4 X7 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk51_3 X2 X5 X3) X3 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> r2_hidden (esk52_4 X2 X5 X3 X6) X3 -> r1_xboole_0 (esk52_4 X2 X5 X3 X6) X5 -> False)
  -> (forall X2 X4 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> r1_tarski (esk51_3 X3 X2 X4) X2 -> r2_hidden (esk52_4 X3 X2 X4 X1) X4 -> r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> r1_xboole_0 (esk52_4 X3 X2 X4 X1) X2 -> False)
  -> (forall X2 X4 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> r1_xboole_0 X2 (esk51_3 X3 X2 X4) -> r2_hidden (esk52_4 X3 X2 X4 X1) X4 -> r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> r1_xboole_0 (esk52_4 X3 X2 X4 X1) X2 -> False)
  -> (forall X2 X4 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> r1_tarski X2 (esk51_3 X3 X2 X4) -> r2_hidden (esk52_4 X3 X2 X4 X1) X4 -> r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> r1_xboole_0 (esk52_4 X3 X2 X4 X1) X2 -> False)
  -> (forall X3 X5 X2 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> r1_tarski (esk51_3 X4 X3 X1) X3 -> r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> r2_hidden (esk52_4 X4 X3 X1 X2) X1 -> r1_xboole_0 (esk52_4 X4 X3 X1 X2) X3 -> False)
  -> (forall X3 X5 X2 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> r1_xboole_0 X3 (esk51_3 X4 X3 X1) -> r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> r2_hidden (esk52_4 X4 X3 X1 X2) X1 -> r1_xboole_0 (esk52_4 X4 X3 X1 X2) X3 -> False)
  -> (forall X3 X5 X2 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> r1_tarski X3 (esk51_3 X4 X3 X1) -> r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> r2_hidden (esk52_4 X4 X3 X1 X2) X1 -> r1_xboole_0 (esk52_4 X4 X3 X1 X2) X3 -> False)
  -> (forall X2 X1 X5 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk51_3 X3 X2 X4) X4 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> r2_hidden (esk52_4 X3 X2 X4 X1) X4 -> r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> r1_xboole_0 (esk52_4 X3 X2 X4 X1) X2 -> False)
  -> (forall X3 X2 X5 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r2_hidden (esk51_3 X4 X3 X1) X1 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> r2_hidden (esk52_4 X4 X3 X1 X2) X1 -> r1_xboole_0 (esk52_4 X4 X3 X1 X2) X3 -> False)
  -> (forall X2 X3 X7 X4 X6 X1 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> False) -> (r1_xboole_0 (esk52_4 X2 X5 X3 X6) X5 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> r1_tarski (esk51_3 X2 X5 X3) X5 -> False)
  -> (forall X2 X3 X7 X4 X6 X1 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X3 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> r1_tarski (esk51_3 X2 X5 X3) X5 -> False)
  -> (forall X2 X3 X7 X4 X6 X1 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> False) -> (r1_xboole_0 (esk52_4 X2 X5 X3 X6) X5 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> r1_xboole_0 X5 (esk51_3 X2 X5 X3) -> False)
  -> (forall X2 X3 X7 X4 X6 X1 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> False) -> (r1_xboole_0 (esk52_4 X2 X5 X3 X6) X5 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> r1_tarski X5 (esk51_3 X2 X5 X3) -> False)
  -> (forall X2 X3 X7 X4 X6 X1 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X3 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> r1_xboole_0 X5 (esk51_3 X2 X5 X3) -> False)
  -> (forall X2 X3 X7 X4 X6 X1 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X3 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> r1_tarski X5 (esk51_3 X2 X5 X3) -> False)
  -> (forall X2 X1 X6 X4 X7 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk51_3 X2 X5 X3) X3 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> False) -> (r1_xboole_0 (esk52_4 X2 X5 X3 X6) X5 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1 X6 X4 X7 X3 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk51_3 X2 X5 X3) X3 -> False) -> (r1_setfam_1 (k2_xboole_0 X6 (k1_tarski X5)) X1 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X6 -> False) -> (r2_hidden (esk52_4 X2 X5 X3 X6) X3 -> False) -> r2_hidden X7 X3 -> r2_hidden X4 X1 -> r1_tarski X7 X5 -> r1_tarski X5 X4 -> r1_tarski X5 X2 -> r1_setfam_1 X3 X1 -> m1_eqrel_1 X3 X2 -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X4 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> False) -> (r1_xboole_0 (esk52_4 X3 X2 X4 X1) X2 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> r1_tarski (esk51_3 X3 X2 X4) X2 -> False)
  -> (forall X2 X4 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X4 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> r1_tarski (esk51_3 X3 X2 X4) X2 -> False)
  -> (forall X2 X4 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> False) -> (r1_xboole_0 (esk52_4 X3 X2 X4 X1) X2 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> r1_xboole_0 X2 (esk51_3 X3 X2 X4) -> False)
  -> (forall X2 X4 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> False) -> (r1_xboole_0 (esk52_4 X3 X2 X4 X1) X2 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> r1_tarski X2 (esk51_3 X3 X2 X4) -> False)
  -> (forall X2 X4 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X4 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> r1_xboole_0 X2 (esk51_3 X3 X2 X4) -> False)
  -> (forall X2 X4 X5 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X4 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> r1_tarski X2 (esk51_3 X3 X2 X4) -> False)
  -> (forall X3 X5 X2 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> False) -> (r1_xboole_0 (esk52_4 X4 X3 X1 X2) X3 -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> r1_tarski (esk51_3 X4 X3 X1) X3 -> False)
  -> (forall X3 X5 X2 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X1 -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> r1_tarski (esk51_3 X4 X3 X1) X3 -> False)
  -> (forall X3 X5 X2 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> False) -> (r1_xboole_0 (esk52_4 X4 X3 X1 X2) X3 -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> r1_xboole_0 X3 (esk51_3 X4 X3 X1) -> False)
  -> (forall X3 X5 X2 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> False) -> (r1_xboole_0 (esk52_4 X4 X3 X1 X2) X3 -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> r1_tarski X3 (esk51_3 X4 X3 X1) -> False)
  -> (forall X3 X5 X2 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X1 -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> r1_xboole_0 X3 (esk51_3 X4 X3 X1) -> False)
  -> (forall X3 X5 X2 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X1 -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> r1_tarski X3 (esk51_3 X4 X3 X1) -> False)
  -> (forall X2 X1 X5 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk51_3 X3 X2 X4) X4 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> False) -> (r1_xboole_0 (esk52_4 X3 X2 X4 X1) X2 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> False)
  -> (forall X2 X1 X5 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk51_3 X3 X2 X4) X4 -> False) -> (m1_eqrel_1 (k2_xboole_0 X1 (k1_tarski X2)) X3 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X4 -> False) -> (r2_hidden (esk52_4 X3 X2 X4 X1) X1 -> False) -> r2_hidden X5 X4 -> r1_tarski X5 X2 -> r1_tarski X2 X3 -> m1_eqrel_1 X4 X3 -> False)
  -> (forall X3 X2 X5 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r2_hidden (esk51_3 X4 X3 X1) X1 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> False) -> (r1_xboole_0 (esk52_4 X4 X3 X1 X2) X3 -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> False)
  -> (forall X3 X2 X5 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r2_hidden (esk51_3 X4 X3 X1) X1 -> False) -> (r1_setfam_1 X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X2 -> False) -> (r2_hidden (esk52_4 X4 X3 X1 X2) X1 -> False) -> r2_hidden X5 X1 -> r1_tarski X5 X3 -> r1_tarski X3 X4 -> m1_eqrel_1 X1 X4 -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_tarski (esk46_4 X1 X2 X3 X4) X3 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> r2_hidden X4 (esk45_3 X1 X2 X3) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk46_4 X1 X2 X3 X4) X4 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> r2_hidden X4 (esk45_3 X1 X2 X3) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk44_4 X1 X2 X3 X4) X4 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> r2_hidden X4 (esk43_3 X1 X2 X3) -> False)
  -> (forall X3 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_tarski X1 (esk44_4 X2 X3 X1 X4) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> r2_hidden X4 (esk43_3 X2 X3 X1) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X3 (esk39_2 X1 X2) -> False) -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden X3 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_tarski (esk40_3 X1 X2 X3) X2 -> r1_setfam_1 (esk42_3 X1 X2 X3) (esk41_3 X1 X2 X3) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X3 (esk39_2 X1 X2) -> False) -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden X3 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_tarski (esk40_3 X1 X2 X3) X2 -> r1_setfam_1 (esk41_3 X1 X2 X3) (esk42_3 X1 X2 X3) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X3 (esk39_2 X1 X2) -> False) -> (r2_hidden (esk40_3 X1 X2 X3) X3 -> False) -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden X3 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_setfam_1 (esk42_3 X1 X2 X3) (esk41_3 X1 X2 X3) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X3 (esk39_2 X1 X2) -> False) -> (r2_hidden (esk40_3 X1 X2 X3) X3 -> False) -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden X3 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_setfam_1 (esk41_3 X1 X2 X3) (esk42_3 X1 X2 X3) -> False)
  -> (forall X3 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (esk46_4 X2 X3 X1 X4) = X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> r2_hidden X4 (esk45_3 X2 X3 X1) -> False)
  -> (forall X3 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (esk44_4 X2 X3 X1 X4) = X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X2)) -> r2_hidden X4 (esk43_3 X2 X3 X1) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X3 (esk39_2 X1 X2) -> False) -> (r2_hidden (esk42_3 X1 X2 X3) X3 -> False) -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden X3 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_tarski (esk40_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X3 (esk39_2 X1 X2) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) X3 -> False) -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden X3 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_tarski (esk40_3 X1 X2 X3) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X3 (esk39_2 X1 X2) -> False) -> (r2_hidden (esk40_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk42_3 X1 X2 X3) X3 -> False) -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden X3 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden X3 (esk39_2 X1 X2) -> False) -> (r2_hidden (esk40_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk41_3 X1 X2 X3) X3 -> False) -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden X3 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk17_3 X1 X2 X3) X3 -> r2_hidden (esk17_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk17_3 X1 X2 X3) X3 -> r2_hidden (esk17_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk17_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk17_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk17_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden k1_xboole_0 X2 -> False) -> (m1_eqrel_1 (esk48_3 X1 X2 X3) X1 -> False) -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v6_taxonom2 X2 X1 -> r2_hidden X3 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X3 X2, (r2_hidden k1_xboole_0 X2 -> False) -> (r1_tarski (esk48_3 X1 X2 X3) X2 -> False) -> v5_taxonom2 X2 X1 -> m1_taxonom2 X2 X1 -> v6_taxonom2 X2 X1 -> r2_hidden X3 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1 X3, (r2_hidden k1_xboole_0 X3 -> False) -> (r2_hidden X1 (esk48_3 X2 X3 X1) -> False) -> v5_taxonom2 X3 X2 -> m1_taxonom2 X3 X2 -> v6_taxonom2 X3 X2 -> r2_hidden X1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> v3_abian X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X3)) -> r2_hidden X1 (esk45_3 X3 X2 X4) -> False)
  -> (forall X2 X1 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X3)) -> r2_hidden X1 (esk43_3 X3 X2 X4) -> False)
  -> (forall X5 X2 X1 X3 X4, (X3 = X4 -> False) -> (v1_xboole_0 X5 -> False) -> (r2_hidden X1 (esk45_3 X5 X2 X4) -> False) -> r2_hidden X3 X1 -> r2_hidden X1 X2 -> r1_tarski X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X5)) -> False)
  -> (forall X5 X2 X1 X3 X4, (X3 = X4 -> False) -> (v1_xboole_0 X5 -> False) -> (r2_hidden X1 (esk43_3 X5 X2 X4) -> False) -> r2_hidden X3 X1 -> r2_hidden X1 X2 -> r1_tarski X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X5)) -> False)
  -> (forall X1 X3 X5 X2 X4, (v1_xboole_0 X4 -> False) -> (r1_setfam_1 X3 X1 -> False) -> (r1_setfam_1 X1 X3 -> False) -> v5_taxonom2 X5 X4 -> m1_taxonom2 X5 X4 -> r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X2 (esk39_2 X4 X5) -> v3_abian X5 (k1_zfmisc_1 (k1_zfmisc_1 X4)) -> False)
  -> (forall X2 X1 X4 X3, (v1_xboole_0 X3 -> False) -> (r1_tarski X1 X2 -> False) -> m1_eqrel_1 X4 X3 -> r2_hidden X1 (esk38_3 X3 X4 X2) -> False)
  -> (forall X2 X1 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 X2 -> False) -> m1_eqrel_1 X2 X3 -> r2_hidden X1 (esk38_3 X3 X2 X4) -> False)
  -> (forall X1 X2, ((esk18_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r1_xboole_0 (esk18_2 X1 X2) (esk19_2 X1 X2) -> False)
  -> (forall X3 X1 X2 X4, (v1_xboole_0 X4 -> False) -> (r1_tarski X1 X3 -> False) -> v5_taxonom2 X3 X4 -> m1_taxonom2 X3 X4 -> r2_hidden X1 X2 -> r2_hidden X2 (esk39_2 X4 X3) -> v3_abian X3 (k1_zfmisc_1 (k1_zfmisc_1 X4)) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> (r1_xboole_0 X4 X1 -> False) -> r2_hidden X4 X3 -> r2_hidden X1 X3 -> m1_eqrel_1 X3 X2 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r1_setfam_1 X4 X3 -> False) -> (r1_setfam_1 X3 X4 -> False) -> r2_hidden X4 X1 -> r2_hidden X3 X1 -> m1_taxonom1 X1 X2 -> m1_eqrel_1 X4 X2 -> m1_eqrel_1 X3 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_partit1 X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k1_zfmisc_1 (k1_partit1 X2)) -> False) -> v5_taxonom2 X3 X2 -> m1_taxonom2 X3 X2 -> r2_hidden X1 (esk39_2 X2 X3) -> v3_abian X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3 X4, (v1_xboole_0 X4 -> False) -> (r2_hidden X1 (esk38_3 X4 X2 X3) -> False) -> r2_hidden X1 X2 -> r1_tarski X1 X3 -> m1_eqrel_1 X2 X4 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_taxonom1 X2 X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_setfam_1 (esk9_2 X1 X2) (esk8_2 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_taxonom1 X2 X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> r1_setfam_1 (esk8_2 X1 X2) (esk9_2 X1 X2) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk11_3 X1 X2 X3) X2 -> False) -> r2_hidden X3 X1 -> r1_setfam_1 X1 X2 -> False)
  -> (forall X1 X3 X2, (r1_tarski X1 (esk11_3 X2 X3 X1) -> False) -> r2_hidden X1 X2 -> r1_setfam_1 X2 X3 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk21_2 X1 X2) X3 -> r2_hidden (esk21_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk20_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk20_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2, ((esk18_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, ((esk18_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (k5_setfam_1 X1 X2) = X1 -> (esk19_2 X1 X2) = (esk18_2 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X3 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk56_1 X2) -> False) -> r2_hidden X3 X2 -> r2_hidden X1 X2 -> r1_tarski (esk56_1 X2) X1 -> r1_tarski (esk55_2 X2 X3) X3 -> False)
  -> (forall X1 X2, ((esk18_2 X1 X2) = k1_xboole_0 -> False) -> (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk19_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (m1_subset_1 (esk18_2 X1 X2) (k1_zfmisc_1 X1) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (X2 = (k1_partit1 X1) -> False) -> r2_hidden (esk13_2 X1 X2) X2 -> m1_eqrel_1 (esk13_2 X1 X2) X1 -> False)
  -> (forall X2 X3 X1, X1 = k1_xboole_0 -> r2_hidden X1 X2 -> m1_eqrel_1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X3)) -> False)
  -> (forall X1 X3 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk56_1 X2) -> False) -> (r2_hidden (esk55_2 X2 X3) (esk54_1 X2) -> False) -> r2_hidden X3 X2 -> r2_hidden X1 X2 -> r1_tarski (esk56_1 X2) X1 -> False)
  -> (forall X1 X2, (m1_eqrel_1 X2 X1 -> False) -> (r2_hidden (esk18_2 X1 X2) X2 -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = X2 -> False) -> v3_abian X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_setfam_1 (esk5_1 X1) X2 -> False) -> r2_hidden X2 X1 -> r1_tarski X1 (k1_partit1 esk1_0) -> r1_setfam_1 (esk4_1 X1) (esk3_1 X1) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_setfam_1 (esk5_1 X1) X2 -> False) -> r2_hidden X2 X1 -> r1_tarski X1 (k1_partit1 esk1_0) -> r1_setfam_1 (esk3_1 X1) (esk4_1 X1) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_setfam_1 X1 (esk6_1 X2) -> False) -> r2_hidden X1 X2 -> r1_tarski X2 (k1_partit1 esk1_0) -> r1_setfam_1 (esk4_1 X2) (esk3_1 X2) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_setfam_1 X1 (esk6_1 X2) -> False) -> r2_hidden X1 X2 -> r1_tarski X2 (k1_partit1 esk1_0) -> r1_setfam_1 (esk3_1 X2) (esk4_1 X2) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk21_2 X1 X2) X2 -> False) -> (r2_hidden (esk21_2 X1 X2) (esk22_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_taxonom1 X2 X1 -> False) -> (m1_eqrel_1 (esk9_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_taxonom1 X2 X1 -> False) -> (m1_eqrel_1 (esk8_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_taxonom1 X2 X1 -> False) -> (r2_hidden (esk9_2 X1 X2) X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_taxonom1 X2 X1 -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk56_1 X1) X1 -> False) -> r2_hidden X2 X1 -> r1_tarski (esk55_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (v3_abian X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> (k5_setfam_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k6_subset_1 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (r1_setfam_1 X3 X2 -> False) -> r2_hidden X1 X2 -> r1_tarski (esk12_2 X3 X2) X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X3 X2, (r1_tarski X3 X2 -> False) -> (r1_tarski X2 X3 -> False) -> (r1_xboole_0 X2 X3 -> False) -> v3_taxonom2 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk4_1 X1) X1 -> False) -> (r1_setfam_1 (esk5_1 X1) X2 -> False) -> r2_hidden X2 X1 -> r1_tarski X1 (k1_partit1 esk1_0) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk3_1 X1) X1 -> False) -> (r1_setfam_1 (esk5_1 X1) X2 -> False) -> r2_hidden X2 X1 -> r1_tarski X1 (k1_partit1 esk1_0) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_setfam_1 X1 (esk6_1 X2) -> False) -> (r2_hidden (esk4_1 X2) X2 -> False) -> r2_hidden X1 X2 -> r1_tarski X2 (k1_partit1 esk1_0) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_setfam_1 X1 (esk6_1 X2) -> False) -> (r2_hidden (esk3_1 X2) X2 -> False) -> r2_hidden X1 X2 -> r1_tarski X2 (k1_partit1 esk1_0) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk7_2 X1 X2) = X1 -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk6_1 X1) X1 -> False) -> r1_tarski X1 (k1_partit1 esk1_0) -> r1_setfam_1 (esk4_1 X1) (esk3_1 X1) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk6_1 X1) X1 -> False) -> r1_tarski X1 (k1_partit1 esk1_0) -> r1_setfam_1 (esk3_1 X1) (esk4_1 X1) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> r1_tarski X1 (k1_partit1 esk1_0) -> r1_setfam_1 (esk4_1 X1) (esk3_1 X1) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> r1_tarski X1 (k1_partit1 esk1_0) -> r1_setfam_1 (esk3_1 X1) (esk4_1 X1) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk56_1 X1) X1 -> False) -> (r2_hidden (esk55_2 X1 X2) (esk54_1 X1) -> False) -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, ((k5_setfam_1 X1 X2) = X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk21_2 X1 X2) X2 -> False) -> (r2_hidden (esk22_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (X2 = (k1_partit1 X1) -> False) -> (r2_hidden (esk13_2 X1 X2) X2 -> False) -> (m1_eqrel_1 (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) X2 -> False) -> r1_tarski X3 X2 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk47_2 X3 X2) -> False) -> r2_hidden X1 X2 -> r1_xboole_0 X1 X3 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk56_1 X2) -> False) -> (r1_tarski (esk54_1 X2) X2 -> False) -> r2_hidden X1 X2 -> r1_tarski (esk56_1 X2) X1 -> False)
  -> (forall X2 X1, (v3_taxonom2 X1 -> False) -> m1_taxonom2 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk14_2 X1 X2) X2 -> False)
  -> (forall X3 X1 X2, (r1_xboole_0 X1 X2 -> False) -> r2_hidden X1 (esk47_2 X2 X3) -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden X1 (esk47_2 X3 X2) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_taxonom2 X1 X2 -> False) -> v3_taxonom2 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (X1 = (esk56_1 X2) -> False) -> (v6_ordinal1 (esk54_1 X2) -> False) -> r2_hidden X1 X2 -> r1_tarski (esk56_1 X2) X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk4_1 X1) X1 -> False) -> (r2_hidden (esk6_1 X1) X1 -> False) -> r1_tarski X1 (k1_partit1 esk1_0) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk4_1 X1) X1 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> r1_tarski X1 (k1_partit1 esk1_0) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk3_1 X1) X1 -> False) -> (r2_hidden (esk6_1 X1) X1 -> False) -> r1_tarski X1 (k1_partit1 esk1_0) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk3_1 X1) X1 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> r1_tarski X1 (k1_partit1 esk1_0) -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X1 X2 X3, (r3_xboole_0 X2 X3 -> False) -> v6_ordinal1 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk7_2 X1 X2) = X1 -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False) -> m1_taxonom1 X2 X1 -> False)
  -> (forall X2 X1 X3, (r1_setfam_1 X1 X3 -> False) -> r1_setfam_1 X2 X3 -> r1_setfam_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_taxonom2 X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk53_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk53_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (r1_setfam_1 X1 X2 -> False) -> (r2_hidden (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (r1_tarski X2 X1 -> False) -> (r1_tarski X1 X2 -> False) -> r3_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> r1_tarski X1 X2 -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> r3_xboole_0 (esk23_1 X1) (esk24_1 X1) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> r1_xboole_0 (esk15_1 X1) (esk16_1 X1) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> r1_tarski (esk16_1 X1) (esk15_1 X1) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> r1_tarski (esk15_1 X1) (esk16_1 X1) -> False)
  -> (forall X2 X1 X3, (m1_eqrel_1 X1 X3 -> False) -> X2 = (k1_partit1 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k1_partit1 X2) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk56_1 X1) X1 -> False) -> (r1_tarski (esk54_1 X1) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X1 X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X2 X1 -> False) -> r3_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X2 X1 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (v6_ordinal1 (esk54_1 X1) -> False) -> (r2_hidden (esk56_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (k3_tarski X1) = esk2_0 -> m1_taxonom1 X1 esk1_0 -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> (r2_hidden (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> (r2_hidden (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> (r2_hidden (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_taxonom2 X1 -> False) -> (r2_hidden (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk36_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk35_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk31_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_taxonom1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk35_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk31_1 X1) -> False) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk34_1 X1) X1 -> False)
  -> (r2_hidden k1_xboole_0 esk2_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1, (v3_abian (esk37_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((v3_abian esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk25_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_taxonom2 (esk37_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_taxonom2 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_taxonom2 (esk37_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r3_xboole_0 X1 X1 -> False) -> False)
  -> (forall X1, (r1_setfam_1 X1 X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski k1_xboole_0 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((v6_taxonom2 esk2_0 esk1_0 -> False) -> False)
  -> ((m1_taxonom2 esk2_0 esk1_0 -> False) -> False)
  -> ((v5_taxonom2 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk32_1 X1) -> False) -> False)
  -> ((v1_xboole_0 esk30_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> (((k3_tarski k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
