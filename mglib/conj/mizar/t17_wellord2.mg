(** $I sig/MizarPreamble.mgs **)

Theorem t17_wellord2:
 forall k1_funct_1:set -> set -> set,
 forall v2_funct_1:set -> prop,
 forall esk14_2:set -> set -> set,
 forall r2_wellord1:set -> set -> prop,
 forall v2_wellord1:set -> prop,
 forall r2_wellord2:set -> set -> prop,
 forall esk9_2:set -> set -> set,
 forall esk29_1:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall v4_funct_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall esk27_1:set -> set,
 forall esk28_1:set -> set,
 forall v1_ordinal1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall esk26_0:set,
 forall esk22_0:set,
 forall esk17_0:set,
 forall esk13_1:set -> set,
 forall esk23_0:set,
 forall esk21_0:set,
 forall esk18_0:set,
 forall esk16_0:set,
 forall o_0_0_xboole_0:set,
 forall esk15_0:set,
 forall esk20_0:set,
 forall esk19_0:set,
 forall esk25_0:set,
 forall esk24_0:set,
 forall v7_ordinal1:set -> prop,
 forall esk1_0:set,
 forall v5_ordinal1:set -> prop,
 forall v1_setfam_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk5_1:set -> set,
 forall v6_ordinal1:set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall v4_relat_2:set -> prop,
 forall v1_wellord1:set -> prop,
 forall v8_relat_2:set -> prop,
 forall v6_relat_2:set -> prop,
 forall v1_relat_2:set -> prop,
 forall r1_ordinal1:set -> set -> prop,
 forall esk30_1:set -> set,
 forall v3_ordinal1:set -> prop,
 forall esk12_2:set -> set -> set,
 forall esk10_1:set -> set,
 forall esk11_1:set -> set,
 forall r2_tarski:set -> set -> prop,
 forall k2_wellord1:set -> set -> set,
 forall esk2_2:set -> set -> set,
 forall v2_relat_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall v1_funct_1:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall k1_relat_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk3_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k2_tarski:set -> set -> set,
 forall k1_tarski:set -> set,
 forall v1_relat_1:set -> prop,
 forall k1_wellord2:set -> set,
     (forall X1 X2, (X2 = (k1_wellord2 X1) -> False) -> (k1_relat_1 X2) = X1 -> v1_relat_1 X2 -> r1_tarski (esk3_2 X1 X2) (esk4_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski (esk3_2 X1 X2) (esk4_2 X1 X2)) (k1_tarski (esk3_2 X1 X2))) X2 -> False)
  -> (forall X1 X2, (X2 = (k1_wellord2 X1) -> False) -> (r1_tarski (esk3_2 X1 X2) (esk4_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk3_2 X1 X2) (esk4_2 X1 X2)) (k1_tarski (esk3_2 X1 X2))) X2 -> False) -> (k1_relat_1 X2) = X1 -> v1_relat_1 X2 -> False)
  -> (forall X4 X3 X1 X2, (r1_tarski X1 X2 -> False) -> X3 = (k1_wellord2 X4) -> v1_relat_1 X3 -> r2_hidden X2 X4 -> r2_hidden X1 X4 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False)
  -> (forall X4 X1 X2 X3, (r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False) -> X3 = (k1_wellord2 X4) -> v1_relat_1 X3 -> r2_hidden X2 X4 -> r2_hidden X1 X4 -> r1_tarski X1 X2 -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk6_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk6_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk7_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (k1_funct_1 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden X2 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk8_2 X1 X2)) = (esk7_2 X1 X2) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> (r2_hidden (esk8_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk2_2 X1 X2) = X1 -> r2_hidden (esk2_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (r2_wellord1 (esk14_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v2_wellord1 X2 -> r2_wellord2 X1 (k1_relat_1 X2) -> False)
  -> (forall X2 X1, ((k1_relat_1 (k2_wellord1 X1 X2)) = X2 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> r1_tarski X2 (k1_relat_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (esk14_2 X1 X2) -> False) -> v1_relat_1 X2 -> v2_wellord1 X2 -> r2_wellord2 X1 (k1_relat_1 X2) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 (esk29_1 X2) -> False) -> r1_tarski X3 X1 -> r2_hidden X1 (esk29_1 X2) -> False)
  -> (forall X2 X1, (r2_hidden X1 (esk29_1 X2) -> False) -> (r2_tarski X1 (esk29_1 X2) -> False) -> r1_tarski X1 (esk29_1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (X2 = (k1_wellord2 X1) -> False) -> (r2_hidden (esk4_2 X1 X2) X1 -> False) -> (k1_relat_1 X2) = X1 -> v1_relat_1 X2 -> False)
  -> (forall X1 X2, (X2 = (k1_wellord2 X1) -> False) -> (r2_hidden (esk3_2 X1 X2) X1 -> False) -> (k1_relat_1 X2) = X1 -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 (k2_zfmisc_1 X2 X2)) = (k2_wellord1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k1_relat_1 (k2_wellord1 X1 X2)) = X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk2_2 X1 X2) = X1 -> False) -> (r2_hidden (esk2_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v2_wellord1 (k2_wellord1 X1 X2) -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((k1_funct_1 X1 (esk11_1 X1)) = (k1_funct_1 X1 (esk10_1 X1)) -> False) -> (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (r2_hidden (k1_zfmisc_1 X1) (esk29_1 X2) -> False) -> r2_hidden X1 (esk29_1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk12_2 X1 X2)) = X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, ((k10_xtuple_0 (esk12_2 X1 X2)) = X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v3_ordinal1 (esk30_1 X1) -> r1_tarski (esk30_1 X1) X1 -> False)
  -> (forall X2 X1, (v2_funct_1 (esk12_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 (esk12_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (esk12_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1 X2 X3, (r2_wellord2 X2 X3 -> False) -> (k10_xtuple_0 X1) = X3 -> (k9_xtuple_0 X1) = X2 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r2_hidden X1 (esk27_1 X2) -> False) -> v3_ordinal1 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_wellord1 X1 -> False) -> v1_relat_1 X1 -> v1_relat_2 X1 -> v4_relat_2 X1 -> v6_relat_2 X1 -> v8_relat_2 X1 -> v1_wellord1 X1 -> False)
  -> (forall X2 X1, ((k1_funct_1 (esk28_1 X2) X1) = (k1_tarski X1) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (r2_hidden X1 X2 -> False) -> r2_hidden X1 (esk27_1 X2) -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r2_hidden (esk11_1 X1) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r2_hidden (esk10_1 X1) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v2_wellord1 (k2_wellord1 X1 X2) -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X2 X1 -> False) -> v1_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski (k1_tarski X1) (k1_tarski X2) -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, ((k2_xboole_0 (k9_xtuple_0 X1) (k10_xtuple_0 X1)) = (k1_relat_1 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_wellord1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r2_tarski X1 X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> r2_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X2 X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> r1_tarski (esk5_1 X1) X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 X1 -> False) -> r2_hidden X1 (esk27_1 X2) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_setfam_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (esk11_1 X1) = (esk10_1 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, v1_relat_1 X1 -> r2_wellord1 X1 esk1_0 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> (r2_hidden (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X2 X1, ((k1_relat_1 X1) = X2 -> False) -> X1 = (k1_wellord2 X2) -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_wellord1 X1 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1, (v6_relat_2 X1 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1, (v4_relat_2 X1 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v1_wellord1 (k1_wellord2 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v6_relat_2 (k1_wellord2 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 (k1_wellord2 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k1_wellord2 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v3_funct_1 esk24_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (r2_hidden X1 (esk29_1 X1) -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r2_wellord2 X1 X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k9_xtuple_0 (esk28_1 X1)) = X1 -> False) -> False)
  -> (forall X1, (v8_relat_2 (k1_wellord2 X1) -> False) -> False)
  -> (forall X1, (v4_relat_2 (k1_wellord2 X1) -> False) -> False)
  -> (forall X1, (v1_relat_2 (k1_wellord2 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k1_wellord2 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k1_wellord2 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k1_wellord2 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k1_wellord2 X1) -> False) -> False)
  -> ((v4_funct_1 esk26_0 -> False) -> False)
  -> ((v7_ordinal1 esk25_0 -> False) -> False)
  -> ((v7_ordinal1 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk22_0 -> False) -> False)
  -> ((v2_relat_1 esk21_0 -> False) -> False)
  -> ((v2_relat_1 esk20_0 -> False) -> False)
  -> ((v2_funct_1 esk18_0 -> False) -> False)
  -> ((v2_ordinal1 esk19_0 -> False) -> False)
  -> ((v1_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk24_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
