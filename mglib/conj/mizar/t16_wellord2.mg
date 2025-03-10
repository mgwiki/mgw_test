(** $I sig/MizarPreamble.mgs **)

Theorem t16_wellord2:
 forall r1_relat_2:set -> set -> prop,
 forall esk3_2:set -> set -> set,
 forall k1_xboole_0:set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall k1_wellord1:set -> set -> set,
 forall r1_wellord1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall r2_wellord1:set -> set -> prop,
 forall esk4_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_relat_2:set -> prop,
 forall v6_relat_2:set -> prop,
 forall v8_relat_2:set -> prop,
 forall v1_wellord1:set -> prop,
 forall v4_relat_2:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall esk25_0:set,
 forall esk26_0:set,
 forall esk20_0:set,
 forall esk15_1:set -> set,
 forall esk21_0:set,
 forall esk16_0:set,
 forall o_0_0_xboole_0:set,
 forall esk17_0:set,
 forall esk19_0:set,
 forall esk22_0:set,
 forall esk24_0:set,
 forall esk18_0:set,
 forall esk23_0:set,
 forall esk27_0:set,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall v1_setfam_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall k10_xtuple_0:set -> set,
 forall k9_xtuple_0:set -> set,
 forall v6_ordinal1:set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall k8_relat_1:set -> set -> set,
 forall esk28_2:set -> set -> set,
 forall k10_relat_1:set -> set -> set,
 forall k6_subset_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v2_wellord1:set -> prop,
 forall esk2_0:set,
 forall esk1_0:set,
 forall k2_wellord1:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall k1_relat_1:set -> set,
 forall esk8_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall r4_relat_2:set -> set -> prop,
 forall esk13_2:set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall r8_relat_2:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k2_tarski:set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall k1_tarski:set -> set,
 forall r6_relat_2:set -> set -> prop,
     (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk11_2 X1 X2) (esk10_2 X1 X2)) (k1_tarski (esk11_2 X1 X2))) X1 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk10_2 X1 X2) (esk11_2 X1 X2)) (k1_tarski (esk10_2 X1 X2))) X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk12_2 X1 X2) (esk14_2 X1 X2)) (k1_tarski (esk12_2 X1 X2))) X1 -> False)
  -> (forall X2 X1, (r1_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk3_2 X1 X2) (esk3_2 X1 X2)) (k1_tarski (esk3_2 X1 X2))) X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk9_3 X1 X2 X3) X3 -> r2_hidden (esk9_3 X1 X2 X3) X2 -> r2_hidden (esk9_3 X1 X2 X3) X1 -> False)
  -> (forall X4 X2 X3 X5 X1, (r2_hidden (k2_tarski (k2_tarski X3 X5) (k1_tarski X3)) X1 -> False) -> v1_relat_1 X1 -> r2_hidden X5 X2 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> r8_relat_2 X1 X2 -> r2_hidden (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) X1 -> r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk13_2 X1 X2) (esk14_2 X1 X2)) (k1_tarski (esk13_2 X1 X2))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk12_2 X1 X2) (esk13_2 X1 X2)) (k1_tarski (esk12_2 X1 X2))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk8_2 X1 X2) (esk7_2 X1 X2)) (k1_tarski (esk8_2 X1 X2))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk7_2 X1 X2) (esk8_2 X1 X2)) (k1_tarski (esk7_2 X1 X2))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_relat_1 X1 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> r4_relat_2 X1 X2 -> r2_hidden (k2_tarski (k2_tarski X4 X3) (k1_tarski X4)) X1 -> r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1 -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (r1_xboole_0 (k1_wellord1 X1 (esk5_3 X1 X2 X3)) X3 -> False) -> v1_relat_1 X1 -> r1_tarski X3 X2 -> r1_wellord1 X1 X2 -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (r2_hidden (k2_tarski (k2_tarski X4 X3) (k1_tarski X4)) X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1 -> False) -> v1_relat_1 X1 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> r6_relat_2 X1 X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X3 X1 X2, (X1 = X2 -> False) -> (r2_hidden X1 (k1_wellord1 X3 X2) -> False) -> v1_relat_1 X3 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k1_relat_1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) X2 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k1_relat_1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) X2 -> False)
  -> (forall X1 X2 X3, (r1_wellord1 X2 X3 -> False) -> v1_relat_1 X2 -> r2_hidden X1 (esk6_2 X2 X3) -> r1_xboole_0 (k1_wellord1 X2 X1) (esk6_2 X2 X3) -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> v1_relat_1 X1 -> r1_tarski X3 X2 -> r1_wellord1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False) -> v1_relat_1 X3 -> r2_hidden X1 (k1_wellord1 X3 X2) -> False)
  -> (forall X2 X3 X1, (r2_hidden (k2_tarski (k2_tarski X3 X3) (k1_tarski X3)) X1 -> False) -> v1_relat_1 X1 -> r2_hidden X3 X2 -> r1_relat_2 X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord1 X1 X2 -> False) -> v1_relat_1 X1 -> r1_relat_2 X1 X2 -> r1_wellord1 X1 X2 -> r4_relat_2 X1 X2 -> r8_relat_2 X1 X2 -> r6_relat_2 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski (k1_relat_1 (k2_wellord1 X1 X2)) (k1_relat_1 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski (k1_relat_1 (k2_wellord1 X1 X2)) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> ((k1_relat_1 (k2_wellord1 esk2_0 esk1_0)) = esk1_0 -> v2_wellord1 (k2_wellord1 esk2_0 esk1_0) -> False)
  -> (forall X3 X1 X2, X1 = X2 -> v1_relat_1 X3 -> r2_hidden X1 (k1_wellord1 X3 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X2 X1, ((k6_subset_1 (k10_relat_1 X1 X2) (k1_tarski X2)) = (k1_wellord1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> (esk11_2 X1 X2) = (esk10_2 X1 X2) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> (esk8_2 X1 X2) = (esk7_2 X1 X2) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (esk13_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_wellord1 X1 X2 -> False) -> (r1_tarski (esk6_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_relat_2 X1 X2 -> False) -> (r2_hidden (esk3_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 (k2_zfmisc_1 X2 X2)) = (k2_wellord1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk28_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk28_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk4_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v2_wellord1 X1 -> False) -> v1_relat_1 X1 -> v1_relat_2 X1 -> v4_relat_2 X1 -> v6_relat_2 X1 -> v8_relat_2 X1 -> v1_wellord1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k8_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k8_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (r1_wellord1 X1 X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (r1_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (r1_wellord1 X1 X2 -> False) -> (esk6_2 X1 X2) = k1_xboole_0 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_wellord1 X1 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 (k1_relat_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, ((k8_relat_1 X1 (k1_tarski X2)) = (k10_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1, ((k2_xboole_0 (k9_xtuple_0 X1) (k10_xtuple_0 X1)) = (k1_relat_1 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k6_subset_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_wellord1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (r2_wellord1 X1 (k1_relat_1 X1) -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_setfam_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_wellord1 X1 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1, (v8_relat_2 X1 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1, (v6_relat_2 X1 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1, (v4_relat_2 X1 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_relat_1 X1 -> v2_wellord1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
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
  -> (v3_funct_1 esk25_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((r2_wellord1 esk2_0 esk1_0 -> False) -> False)
  -> ((v4_funct_1 esk27_0 -> False) -> False)
  -> ((v7_ordinal1 esk26_0 -> False) -> False)
  -> ((v7_ordinal1 esk24_0 -> False) -> False)
  -> ((v2_relat_1 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk22_0 -> False) -> False)
  -> ((v2_relat_1 esk21_0 -> False) -> False)
  -> ((v2_funct_1 esk19_0 -> False) -> False)
  -> ((v2_ordinal1 esk20_0 -> False) -> False)
  -> ((v1_ordinal1 esk20_0 -> False) -> False)
  -> ((v3_ordinal1 esk20_0 -> False) -> False)
  -> ((v3_ordinal1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk19_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
