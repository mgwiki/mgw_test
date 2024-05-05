(** $I sig/MizarPreamble.mgs **)

Theorem t8_ordinal4:
 forall esk31_3:set -> set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk5_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall k8_ordinal2:set -> set,
 forall esk28_2:set -> set -> set,
 forall k3_ordinal2:set -> set,
 forall v3_card_1:set -> set -> prop,
 forall v1_card_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk1_0:set,
 forall esk26_1:set -> set,
 forall esk22_1:set -> set,
 forall esk23_0:set,
 forall esk24_0:set,
 forall esk16_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall esk7_1:set -> set,
 forall esk15_0:set,
 forall esk11_0:set,
 forall esk9_0:set,
 forall o_0_0_xboole_0:set,
 forall esk17_0:set,
 forall esk10_0:set,
 forall esk13_0:set,
 forall esk12_0:set,
 forall esk21_0:set,
 forall esk14_0:set,
 forall v2_xxreal_0:set -> prop,
 forall esk18_0:set,
 forall esk27_0:set,
 forall esk19_0:set,
 forall v2_ordinal1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall np__1:set,
 forall esk25_1:set -> set,
 forall esk20_1:set -> set,
 forall v1_finset_1:set -> prop,
 forall k4_ordinal2:set -> set,
 forall v6_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk29_1:set -> set,
 forall v4_ordinal1:set -> prop,
 forall esk30_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall esk3_1:set -> set,
 forall esk2_1:set -> set,
 forall v1_ordinal2:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall v2_ordinal2:set -> prop,
 forall esk34_2:set -> set -> set,
 forall esk35_3:set -> set -> set -> set,
 forall esk33_2:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall r1_ordinal2:set -> set -> prop,
 forall r1_ordinal1:set -> set -> prop,
 forall esk32_4:set -> set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall epred1_2:set -> set -> prop,
 forall v3_ordinal1:set -> prop,
 forall k1_xboole_0:set,
     (forall X3 X1 X2 X5 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden (k1_funct_1 X1 X2) X3 -> False) -> v3_ordinal1 X5 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> r1_ordinal2 X4 X1 -> r2_hidden X5 X4 -> r2_hidden X4 X3 -> epred1_2 X1 X4 -> r2_hidden X2 (k9_xtuple_0 X1) -> r1_ordinal1 (esk32_4 X4 X1 X5 X3) X2 -> False)
  -> (forall X1 X3 X2 X5 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 (k1_funct_1 X2 X3) -> False) -> v3_ordinal1 X5 -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> r1_ordinal2 X4 X2 -> r2_hidden X4 X5 -> r2_hidden X1 X4 -> epred1_2 X2 X4 -> r2_hidden X3 (k9_xtuple_0 X2) -> r1_ordinal1 (esk32_4 X4 X2 X1 X5) X3 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> v3_ordinal1 X3 -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> r2_hidden (esk33_2 X1 X2) (k1_funct_1 X2 (esk35_3 X1 X2 X3)) -> r2_hidden (k1_funct_1 X2 (esk35_3 X1 X2 X3)) (esk34_2 X1 X2) -> False)
  -> (forall X4 X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) (k9_xtuple_0 X2) -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> r1_ordinal2 X1 X2 -> r2_hidden X3 X1 -> r2_hidden X1 X4 -> epred1_2 X2 X1 -> False)
  -> (forall X4 X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (v3_ordinal1 (esk32_4 X1 X2 X3 X4) -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> r1_ordinal2 X1 X2 -> r2_hidden X3 X1 -> r2_hidden X1 X4 -> epred1_2 X2 X1 -> False)
  -> (forall X3 X2 X1, (r1_ordinal2 X2 X1 -> False) -> X2 = k1_xboole_0 -> (k1_funct_1 X1 (esk31_3 X2 X1 X3)) = k1_xboole_0 -> v3_ordinal1 X3 -> epred1_2 X1 X2 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X3 X1 X2, (r1_ordinal2 X1 X2 -> False) -> (r2_hidden (esk31_3 X1 X2 X3) (k9_xtuple_0 X2) -> False) -> X1 = k1_xboole_0 -> v3_ordinal1 X3 -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (r2_hidden (esk35_3 X1 X2 X3) (k9_xtuple_0 X2) -> False) -> v3_ordinal1 X3 -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2 X3, (r1_ordinal2 X2 X3 -> False) -> (r1_ordinal1 X1 (esk31_3 X2 X3 X1) -> False) -> X2 = k1_xboole_0 -> v3_ordinal1 X1 -> epred1_2 X3 X2 -> r2_hidden X1 (k9_xtuple_0 X3) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r1_ordinal2 X2 X3 -> False) -> (r1_ordinal1 X1 (esk35_3 X2 X3 X1) -> False) -> v3_ordinal1 X1 -> epred1_2 X3 X2 -> r2_hidden X1 (k9_xtuple_0 X3) -> False)
  -> (forall X3 X1 X2, (r1_ordinal2 X1 X2 -> False) -> (v3_ordinal1 (esk31_3 X1 X2 X3) -> False) -> X1 = k1_xboole_0 -> v3_ordinal1 X3 -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (v3_ordinal1 (esk35_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X1, (v2_ordinal2 X1 -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> r2_hidden (k1_funct_1 X1 (esk2_1 X1)) (k1_funct_1 X1 (esk3_1 X1)) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk4_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X3 X2 X1, (r2_hidden (k1_funct_1 X1 X2) (k1_funct_1 X1 X3) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> v2_ordinal2 X1 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> r2_hidden X2 X3 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk4_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1 X3, ((k1_funct_1 X3 X1) = k1_xboole_0 -> False) -> X2 = k1_xboole_0 -> v3_ordinal1 X1 -> r1_ordinal2 X2 X3 -> epred1_2 X3 X2 -> r2_hidden X1 (k9_xtuple_0 X3) -> r1_ordinal1 (esk30_2 X2 X3) X1 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk5_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> r2_hidden (k2_xboole_0 (esk29_1 X1) (k1_tarski (esk29_1 X1))) X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk8_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk6_2 X1 X2)) = (esk5_2 X1 X2) -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> (r2_hidden (esk6_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (r2_hidden (k2_xboole_0 X2 (k1_tarski X2)) X1 -> False) -> v4_ordinal1 X1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk30_2 X1 X2) (k9_xtuple_0 X2) -> False) -> X1 = k1_xboole_0 -> r1_ordinal2 X1 X2 -> epred1_2 X2 X1 -> False)
  -> (forall X3 X1 X2, (X1 = (k8_ordinal2 X2) -> False) -> v1_relat_1 X2 -> v5_ordinal1 X2 -> v1_funct_1 X2 -> v1_ordinal2 X2 -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> r1_ordinal2 X3 X2 -> r1_ordinal2 X1 X2 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X3 X1 X2, (r1_ordinal2 X1 X2 -> False) -> X1 = (k8_ordinal2 X2) -> v1_relat_1 X2 -> v5_ordinal1 X2 -> v1_funct_1 X2 -> v1_ordinal2 X2 -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> r1_ordinal2 X3 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v1_ordinal1 X1 -> r2_hidden X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk28_2 X1 X2) X2 -> False) -> v3_ordinal1 X1 -> r2_hidden X1 (k3_ordinal2 X2) -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 (esk28_2 X1 X2) -> False) -> v3_ordinal1 X1 -> r2_hidden X1 (k3_ordinal2 X2) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (r2_hidden (esk33_2 X1 X2) X1 -> False) -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (r2_hidden X1 (esk34_2 X1 X2) -> False) -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (esk30_2 X1 X2) -> False) -> X1 = k1_xboole_0 -> r1_ordinal2 X1 X2 -> epred1_2 X2 X1 -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X2 X1, (v3_ordinal1 (esk28_2 X1 X2) -> False) -> v3_ordinal1 X1 -> r2_hidden X1 (k3_ordinal2 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (v3_ordinal1 (esk34_2 X1 X2) -> False) -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (r1_ordinal2 X1 X2 -> False) -> (v3_ordinal1 (esk33_2 X1 X2) -> False) -> epred1_2 X2 X1 -> False)
  -> (forall X3 X2 X1, (r2_hidden X2 X1 -> False) -> v1_ordinal1 X1 -> r2_hidden X3 X1 -> r2_hidden X2 X3 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> v3_ordinal1 X2 -> False)
  -> (forall X1 X2, (v3_card_1 (k9_xtuple_0 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v1_card_1 X1 -> v3_card_1 X2 X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_ordinal2 X1 -> False) -> (r2_hidden (esk3_1 X1) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> False)
  -> (forall X1, (v2_ordinal2 X1 -> False) -> (r2_hidden (esk2_1 X1) (esk3_1 X1) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r2_hidden X1 (k3_ordinal2 X2) -> False) -> v3_ordinal1 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> v1_relat_1 X2 -> v5_ordinal1 X2 -> v1_funct_1 X2 -> v1_ordinal2 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_ordinal2 X1 -> False) -> (v3_ordinal1 (esk3_1 X1) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> False)
  -> (forall X1, (v2_ordinal2 X1 -> False) -> (v3_ordinal1 (esk2_1 X1) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k8_ordinal2 X1) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k3_ordinal2 (k10_xtuple_0 X1)) = (k4_ordinal2 X1) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> ((k8_ordinal2 esk1_0) = (k4_ordinal2 esk1_0) -> r1_ordinal2 (k4_ordinal2 esk1_0) esk1_0 -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (r2_hidden (esk29_1 X1) X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k4_ordinal2 X1) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_ordinal1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk25_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk22_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk26_1 X1) np__1 -> False) -> False)
  -> (forall X1, (v4_ordinal1 X1 -> False) -> (v3_ordinal1 (esk29_1 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden k1_xboole_0 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk20_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v1_funct_1 (esk25_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (esk25_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_finset_1 esk19_0 -> False)
  -> (v3_funct_1 esk23_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> ((k9_xtuple_0 esk1_0) = k1_xboole_0 -> False)
  -> (forall X1, (r2_hidden X1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_card_1 (k1_tarski X1) np__1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> (forall X1, (v3_ordinal1 (k3_ordinal2 X1) -> False) -> False)
  -> ((v4_ordinal1 (k9_xtuple_0 esk1_0) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v4_funct_1 esk27_0 -> False) -> False)
  -> ((v1_finset_1 esk14_0 -> False) -> False)
  -> ((v7_ordinal1 esk24_0 -> False) -> False)
  -> ((v7_ordinal1 esk21_0 -> False) -> False)
  -> ((v2_funct_1 esk15_0 -> False) -> False)
  -> ((v2_ordinal1 esk16_0 -> False) -> False)
  -> ((v2_ordinal1 esk14_0 -> False) -> False)
  -> ((v2_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_ordinal1 esk16_0 -> False) -> False)
  -> ((v1_ordinal1 esk14_0 -> False) -> False)
  -> ((v1_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk16_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_card_1 esk14_0 -> False) -> False)
  -> ((v1_card_1 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal2 esk1_0 -> False) -> False)
  -> ((v4_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_ordinal2 esk17_0 -> False) -> False)
  -> ((v1_ordinal2 esk1_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((v1_funct_1 esk10_0 -> False) -> False)
  -> ((v1_funct_1 esk1_0 -> False) -> False)
  -> ((v5_ordinal1 esk17_0 -> False) -> False)
  -> ((v5_ordinal1 esk1_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> ((v1_relat_1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
