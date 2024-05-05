(** $I sig/MizarPreamble.mgs **)

Theorem t8_zf_colla:
 forall k1_funct_1:set -> set -> set,
 forall esk23_1:set -> set,
 forall v1_relat_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall esk25_2:set -> set -> set,
 forall esk3_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk4_2:set -> set -> set,
 forall esk28_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_ordinal1:set -> prop,
 forall v6_membered:set -> prop,
 forall v4_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk26_1:set -> set,
 forall esk27_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v1_int_1:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall v2_funct_1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v7_membered:set -> prop,
 forall k1_xboole_0:set,
 forall esk20_0:set,
 forall esk16_0:set,
 forall esk14_0:set,
 forall esk9_0:set,
 forall esk7_1:set -> set,
 forall esk8_0:set,
 forall esk17_0:set,
 forall esk11_0:set,
 forall o_0_0_xboole_0:set,
 forall esk10_0:set,
 forall esk12_0:set,
 forall esk13_0:set,
 forall esk15_0:set,
 forall esk19_0:set,
 forall esk18_0:set,
 forall esk1_0:set,
 forall v5_ordinal1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk2_1:set -> set,
 forall v1_membered:set -> prop,
 forall v3_membered:set -> prop,
 forall v5_membered:set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk6_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall esk24_2:set -> set -> set,
 forall r1_ordinal1:set -> set -> prop,
 forall esk22_3:set -> set -> set -> set,
 forall v3_ordinal1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk21_1:set -> set,
 forall k1_zf_colla:set -> set -> set,
 forall v1_xboole_0:set -> prop,
     (forall X1 X2 X5 X4 X3, (v1_xboole_0 X3 -> False) -> (r1_ordinal1 (esk24_2 X3 X2) X1 -> False) -> (r2_hidden (esk21_1 X3) (k1_zf_colla X3 (esk22_3 X3 X4 X5)) -> False) -> X4 = X5 -> v3_ordinal1 X5 -> v3_ordinal1 X1 -> r2_hidden X2 X3 -> r2_hidden X2 (k1_zf_colla X3 X1) -> r2_hidden (esk21_1 X3) (k1_zf_colla X3 X5) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k1_zf_colla X2 (esk24_2 X2 X1)) -> False) -> (r2_hidden (esk21_1 X2) (k1_zf_colla X2 (esk22_3 X2 X3 X4)) -> False) -> X3 = X4 -> v3_ordinal1 X4 -> r2_hidden X1 X2 -> r2_hidden (esk21_1 X2) (k1_zf_colla X2 X4) -> False)
  -> (forall X1 X2 X4 X5 X3, (v1_xboole_0 X3 -> False) -> (r1_ordinal1 (esk24_2 X3 X2) X1 -> False) -> X4 = X5 -> v3_ordinal1 X4 -> v3_ordinal1 X1 -> r2_hidden X2 X3 -> r2_hidden X2 (k1_zf_colla X3 X1) -> r1_ordinal1 X4 (esk22_3 X3 X5 X4) -> r2_hidden (esk21_1 X3) (k1_zf_colla X3 X4) -> False)
  -> (forall X4 X3 X2 X1, ((k1_funct_1 (esk23_1 X1) X2) = (esk24_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk21_1 X1) (k1_zf_colla X1 (esk22_3 X1 X3 X4)) -> False) -> X3 = X4 -> v3_ordinal1 X4 -> r2_hidden X2 X1 -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X4) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (v3_ordinal1 (esk24_2 X1 X2) -> False) -> (r2_hidden (esk21_1 X1) (k1_zf_colla X1 (esk22_3 X1 X3 X4)) -> False) -> X3 = X4 -> v3_ordinal1 X4 -> r2_hidden X2 X1 -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X4) -> False)
  -> (forall X1 X3 X4 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k1_zf_colla X2 (esk24_2 X2 X1)) -> False) -> X3 = X4 -> v3_ordinal1 X3 -> r2_hidden X1 X2 -> r1_ordinal1 X3 (esk22_3 X2 X4 X3) -> r2_hidden (esk21_1 X2) (k1_zf_colla X2 X3) -> False)
  -> (forall X2 X3 X1, ((k9_xtuple_0 (esk23_1 X1)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk21_1 X1) (k1_zf_colla X1 (esk22_3 X1 X2 X3)) -> False) -> X2 = X3 -> v3_ordinal1 X3 -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X3) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk23_1 X1) -> False) -> (r2_hidden (esk21_1 X1) (k1_zf_colla X1 (esk22_3 X1 X2 X3)) -> False) -> X2 = X3 -> v3_ordinal1 X3 -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X3) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk23_1 X1) -> False) -> (r2_hidden (esk21_1 X1) (k1_zf_colla X1 (esk22_3 X1 X2 X3)) -> False) -> X2 = X3 -> v3_ordinal1 X3 -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X3) -> False)
  -> (forall X3 X4 X2 X1, ((k1_funct_1 (esk23_1 X1) X2) = (esk24_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> X3 = X4 -> v3_ordinal1 X3 -> r2_hidden X2 X1 -> r1_ordinal1 X3 (esk22_3 X1 X4 X3) -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X3) -> False)
  -> (forall X5 X4 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v3_ordinal1 (esk22_3 X3 X4 X5) -> False) -> (r1_ordinal1 (esk24_2 X3 X2) X1 -> False) -> X4 = X5 -> v3_ordinal1 X5 -> v3_ordinal1 X1 -> r2_hidden X2 X3 -> r2_hidden X2 (k1_zf_colla X3 X1) -> r2_hidden (esk21_1 X3) (k1_zf_colla X3 X5) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v3_ordinal1 (esk24_2 X1 X2) -> False) -> X3 = X4 -> v3_ordinal1 X3 -> r2_hidden X2 X1 -> r1_ordinal1 X3 (esk22_3 X1 X4 X3) -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X3) -> False)
  -> (forall X4 X3 X1 X2, (v1_xboole_0 X2 -> False) -> (v3_ordinal1 (esk22_3 X2 X3 X4) -> False) -> (r2_hidden X1 (k1_zf_colla X2 (esk24_2 X2 X1)) -> False) -> X3 = X4 -> v3_ordinal1 X4 -> r2_hidden X1 X2 -> r2_hidden (esk21_1 X2) (k1_zf_colla X2 X4) -> False)
  -> (forall X2 X3 X1, ((k9_xtuple_0 (esk23_1 X1)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> X2 = X3 -> v3_ordinal1 X2 -> r1_ordinal1 X2 (esk22_3 X1 X3 X2) -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk23_1 X1) -> False) -> X2 = X3 -> v3_ordinal1 X2 -> r1_ordinal1 X2 (esk22_3 X1 X3 X2) -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk23_1 X1) -> False) -> X2 = X3 -> v3_ordinal1 X2 -> r1_ordinal1 X2 (esk22_3 X1 X3 X2) -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X2) -> False)
  -> (forall X3 X4 X2 X1, ((k1_funct_1 (esk23_1 X1) X2) = (esk24_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (v3_ordinal1 (esk22_3 X1 X3 X4) -> False) -> X3 = X4 -> v3_ordinal1 X4 -> r2_hidden X2 X1 -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X4) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v3_ordinal1 (esk24_2 X1 X2) -> False) -> (v3_ordinal1 (esk22_3 X1 X3 X4) -> False) -> X3 = X4 -> v3_ordinal1 X4 -> r2_hidden X2 X1 -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X4) -> False)
  -> (forall X2 X3 X1, ((k9_xtuple_0 (esk23_1 X1)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v3_ordinal1 (esk22_3 X1 X2 X3) -> False) -> X2 = X3 -> v3_ordinal1 X3 -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X3) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk23_1 X1) -> False) -> (v3_ordinal1 (esk22_3 X1 X2 X3) -> False) -> X2 = X3 -> v3_ordinal1 X3 -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X3) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk23_1 X1) -> False) -> (v3_ordinal1 (esk22_3 X1 X2 X3) -> False) -> X2 = X3 -> v3_ordinal1 X3 -> r2_hidden (esk21_1 X1) (k1_zf_colla X1 X3) -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (r1_ordinal1 (esk25_2 X3 X2) X1 -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X1 -> m1_subset_1 X2 X3 -> r2_hidden X2 (k1_zf_colla X3 X4) -> r2_hidden X2 (k1_zf_colla X3 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k1_zf_colla X2 (esk25_2 X2 X1)) -> False) -> v3_ordinal1 X3 -> m1_subset_1 X1 X2 -> r2_hidden X1 (k1_zf_colla X2 X3) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk3_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk3_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk4_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk21_1 X3) X3 -> False) -> (r1_ordinal1 (esk24_2 X3 X2) X1 -> False) -> v3_ordinal1 X1 -> r2_hidden X2 X3 -> r2_hidden X2 (k1_zf_colla X3 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden (esk21_1 X2) X2 -> False) -> (r2_hidden X1 (k1_zf_colla X2 (esk24_2 X2 X1)) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v3_ordinal1 (esk25_2 X1 X2) -> False) -> v3_ordinal1 X3 -> m1_subset_1 X2 X1 -> r2_hidden X2 (k1_zf_colla X1 X3) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 (k1_zf_colla X2 (esk28_2 X2 X1)) -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk5_2 X1 X2)) = (esk4_2 X1 X2) -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_tarski (k1_zf_colla X1 X2) (k1_zf_colla X1 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> r1_ordinal1 X2 X3 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> (r2_hidden (esk5_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, ((k1_funct_1 (esk23_1 X1) X2) = (esk24_2 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk21_1 X1) X1 -> False) -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v3_ordinal1 (esk24_2 X1 X2) -> False) -> (r2_hidden (esk21_1 X1) X1 -> False) -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v3_ordinal1 (esk28_2 X1 X2) -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r1_tarski (k1_zf_colla X1 X2) X1 -> False) -> v3_ordinal1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X2 X1 -> False) -> v1_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (r1_tarski X1 (esk27_1 X1) -> False) -> (r2_hidden (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 (esk27_1 X1) -> False) -> v3_ordinal1 (esk26_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> r1_tarski (esk2_1 X1) X1 -> False)
  -> (forall X1, ((k9_xtuple_0 (esk23_1 X1)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk23_1 X1) -> False) -> (r2_hidden (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk23_1 X1) -> False) -> (r2_hidden (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (esk27_1 X1) -> False) -> (r2_hidden (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (k1_zf_colla esk1_0 X1) = esk1_0 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (esk27_1 X1) -> False) -> v3_ordinal1 (esk26_1 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> (r2_hidden (esk2_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v3_funct_1 esk18_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v4_funct_1 esk20_0 -> False) -> False)
  -> ((v2_funct_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk8_0 -> False) -> False)
  -> ((v7_membered esk16_0 -> False) -> False)
  -> ((v2_ordinal1 esk14_0 -> False) -> False)
  -> ((v1_ordinal1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk8_0 -> False) -> False)
  -> ((v7_ordinal1 esk19_0 -> False) -> False)
  -> ((v7_ordinal1 esk17_0 -> False) -> False)
  -> ((v6_membered esk16_0 -> False) -> False)
  -> ((v6_membered esk13_0 -> False) -> False)
  -> ((v6_membered esk9_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
