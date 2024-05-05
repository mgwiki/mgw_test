(** $I sig/MizarPreamble.mgs **)

Theorem t4_pralg_3:
 forall k9_xtuple_0:set -> set,
 forall v1_relat_1:set -> prop,
 forall esk8_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k1_xboole_0:set,
 forall k10_funct_6:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall esk13_3:set -> set -> set -> set,
 forall v2_relat_1:set -> prop,
 forall esk15_2:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall k1_relset_1:set -> set -> set,
 forall v1_setfam_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall esk43_1:set -> set,
 forall esk24_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall v1_card_3:set -> prop,
 forall v2_setfam_1:set -> prop,
 forall esk36_1:set -> set,
 forall esk37_1:set -> set,
 forall esk42_0:set,
 forall esk45_0:set,
 forall esk33_0:set,
 forall esk26_0:set,
 forall esk22_0:set,
 forall esk1_0:set,
 forall esk31_1:set -> set,
 forall esk40_1:set -> set,
 forall esk35_1:set -> set,
 forall esk21_1:set -> set,
 forall esk34_0:set,
 forall esk18_0:set,
 forall esk19_0:set,
 forall esk25_0:set,
 forall o_0_0_xboole_0:set,
 forall esk20_0:set,
 forall esk29_0:set,
 forall esk27_0:set,
 forall esk46_1:set -> set,
 forall esk28_1:set -> set,
 forall esk38_1:set -> set,
 forall esk16_1:set -> set,
 forall esk3_0:set,
 forall esk23_0:set,
 forall esk32_0:set,
 forall esk39_0:set,
 forall esk30_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall v2_funcop_1:set -> prop,
 forall esk41_1:set -> set,
 forall esk44_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall k9_card_3:set -> set,
 forall v2_card_3:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v3_relat_1:set -> prop,
 forall esk47_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall v1_xboole_0:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall a_2_0_pralg_3:set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall v1_funcop_1:set -> prop,
 forall esk17_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk6_4:set -> set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall k1_funct_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X2 X1 X3 X4, (r1_tarski (k10_xtuple_0 (esk6_4 X1 X2 X3 X4)) X2 -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, ((k9_xtuple_0 (esk6_4 X1 X2 X3 X4)) = X1 -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (v1_funct_1 (esk6_4 X1 X2 X3 X4) -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (v1_relat_1 (esk6_4 X1 X2 X3 X4) -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3, ((k10_xtuple_0 (k1_funct_1 X2 (esk17_3 X1 X3 X2))) = X1 -> False) -> (v1_xboole_0 X3 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v1_funcop_1 X2 -> v4_relat_1 X2 X3 -> v1_partfun1 X2 X3 -> r2_hidden X1 (a_2_0_pralg_3 X3 X2) -> False)
  -> (forall X2 X1 X3, (X3 = (k1_funct_2 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r1_tarski (k10_xtuple_0 (esk8_3 X1 X2 X3)) X2 -> False) -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k1_funct_2 X1 X2) -> False) -> (k9_xtuple_0 X4) = X1 -> (esk7_3 X1 X2 X3) = X4 -> v1_relat_1 X4 -> v1_funct_1 X4 -> r1_tarski (k10_xtuple_0 X4) X2 -> r2_hidden (esk7_3 X1 X2 X3) X3 -> False)
  -> (forall X5 X7 X8 X2 X1 X4 X3 X6, (X6 = k1_xboole_0 -> False) -> (X5 = k1_xboole_0 -> False) -> ((k1_funct_1 X1 X2) = (k1_funct_1 X3 X4) -> False) -> (k1_funct_1 X7 X2) = X3 -> (k1_funct_1 (k10_funct_6 X7) X4) = X1 -> v1_relat_1 X7 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X7 -> v1_funct_1 X3 -> v1_funct_1 X1 -> r2_hidden X4 X6 -> r2_hidden X2 X5 -> r2_hidden X7 (k1_funct_2 X5 (k1_funct_2 X6 X8)) -> False)
  -> (forall X4 X7 X3 X5 X8 X1 X2 X6, (X6 = k1_xboole_0 -> False) -> (X4 = k1_xboole_0 -> False) -> (r1_tarski (k10_xtuple_0 X1) X2 -> False) -> (k1_funct_1 X7 X3) = X1 -> (k1_funct_1 (k10_funct_6 X7) X5) = X8 -> v1_relat_1 X8 -> v1_relat_1 X7 -> v1_relat_1 X1 -> v1_funct_1 X8 -> v1_funct_1 X7 -> v1_funct_1 X1 -> r2_hidden X5 X6 -> r2_hidden X3 X4 -> r2_hidden X7 (k1_funct_2 X4 (k1_funct_2 X6 X2)) -> False)
  -> (forall X4 X8 X7 X3 X5 X1 X2 X6, (X6 = k1_xboole_0 -> False) -> (X4 = k1_xboole_0 -> False) -> (r1_tarski (k10_xtuple_0 X1) X2 -> False) -> (k1_funct_1 X7 X3) = X8 -> (k1_funct_1 (k10_funct_6 X7) X5) = X1 -> v1_relat_1 X8 -> v1_relat_1 X7 -> v1_relat_1 X1 -> v1_funct_1 X8 -> v1_funct_1 X7 -> v1_funct_1 X1 -> r2_hidden X5 X6 -> r2_hidden X3 X4 -> r2_hidden X7 (k1_funct_2 X4 (k1_funct_2 X6 X2)) -> False)
  -> (forall X2 X6 X3 X8 X5 X7 X1 X4, (X4 = k1_xboole_0 -> False) -> (X2 = k1_xboole_0 -> False) -> ((k9_xtuple_0 X1) = X2 -> False) -> (k1_funct_1 X6 X3) = X1 -> (k1_funct_1 (k10_funct_6 X6) X5) = X7 -> v1_relat_1 X7 -> v1_relat_1 X6 -> v1_relat_1 X1 -> v1_funct_1 X7 -> v1_funct_1 X6 -> v1_funct_1 X1 -> r2_hidden X5 X2 -> r2_hidden X3 X4 -> r2_hidden X6 (k1_funct_2 X4 (k1_funct_2 X2 X8)) -> False)
  -> (forall X2 X7 X6 X3 X8 X4 X1 X5, (X5 = k1_xboole_0 -> False) -> (X2 = k1_xboole_0 -> False) -> ((k9_xtuple_0 X1) = X2 -> False) -> (k1_funct_1 X6 X3) = X7 -> (k1_funct_1 (k10_funct_6 X6) X4) = X1 -> v1_relat_1 X7 -> v1_relat_1 X6 -> v1_relat_1 X1 -> v1_funct_1 X7 -> v1_funct_1 X6 -> v1_funct_1 X1 -> r2_hidden X4 X5 -> r2_hidden X3 X2 -> r2_hidden X6 (k1_funct_2 X2 (k1_funct_2 X5 X8)) -> False)
  -> (forall X3 X2 X4 X1, ((esk6_4 X2 X3 X4 X1) = X1 -> False) -> X4 = (k1_funct_2 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk17_3 X1 X2 X3) X2 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v1_funcop_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> r2_hidden X1 (a_2_0_pralg_3 X2 X3) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> ((k9_xtuple_0 (esk8_3 X1 X2 X3)) = X1 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> (v1_funct_1 (esk8_3 X1 X2 X3) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> (v1_relat_1 (esk8_3 X1 X2 X3) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> ((esk7_3 X1 X2 X3) = (esk8_3 X1 X2 X3) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X4 X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X3 (a_2_0_pralg_3 X2 X4) -> False) -> X3 = (k10_xtuple_0 (k1_funct_1 X4 X1)) -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_funcop_1 X4 -> v4_relat_1 X4 X2 -> v1_partfun1 X4 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk9_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk9_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk10_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk10_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk14_2 X1 X2) X3 -> r2_hidden (esk14_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk13_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk13_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m1_subset_1 X3 X1 -> v1_xboole_0 (k1_funct_1 X2 X3) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk11_2 X1 X2)) = (esk10_2 X1 X2) -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> (r2_hidden (esk14_2 X1 X2) (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk47_2 X3 X2) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> (r2_hidden (esk11_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X4 X3 X2 X5, (r2_hidden X2 X5 -> False) -> X1 = X2 -> (k9_xtuple_0 X1) = X3 -> X5 = (k1_funct_2 X3 X4) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r1_tarski (k10_xtuple_0 X1) X4 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> (r2_hidden (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v3_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk12_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_partfun1 X2 X1 -> False) -> (k1_relset_1 X1 X2) = X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X1 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk47_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 (k9_card_3 X1) -> False) -> v4_funct_1 X1 -> v2_card_3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v4_relat_1 X2 (k9_card_3 X1) -> False) -> v4_funct_1 X1 -> v2_card_3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, ((k9_xtuple_0 X2) = (k9_card_3 X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_funct_1 X1 -> v2_card_3 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_card_3 X2 -> False) -> v2_card_3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_setfam_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v1_setfam_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk44_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk43_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk41_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_setfam_1 X1 -> v1_xboole_0 (k3_tarski X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_card_3 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_setfam_1 X1 -> False) -> (m1_subset_1 (esk36_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk41_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 (k10_funct_6 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k10_funct_6 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k10_funct_6 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk44_1 X1) -> False)
  -> (forall X1, (v2_setfam_1 X1 -> False) -> v1_xboole_0 (esk36_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk43_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_setfam_1 X1 -> v2_setfam_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_card_3 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk43_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v2_setfam_1 X1 -> False)
  -> (forall X1, (v2_setfam_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k1_funct_1 (k1_funct_1 (k10_funct_6 esk2_0) esk5_0) esk4_0) = (k1_funct_1 (k1_funct_1 esk2_0 esk4_0) esk5_0) -> False)
  -> (forall X1, v1_subset_1 (esk37_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk42_0 -> False)
  -> (v2_setfam_1 esk30_0 -> False)
  -> (v1_xboole_0 esk45_0 -> False)
  -> (v1_xboole_0 esk39_0 -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk32_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk3_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk40_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk38_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk35_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk46_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk40_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk38_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk35_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk21_1 X1) X1 -> False) -> False)
  -> ((r2_hidden esk5_0 (k9_card_3 esk3_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk4_0 esk1_0 -> False) -> False)
  -> ((v1_partfun1 esk2_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v3_relat_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk46_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk38_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_funcop_1 (esk40_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk46_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk40_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk38_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk21_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk46_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk40_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk38_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk21_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk31_1 X1) -> False) -> False)
  -> ((v3_funct_1 esk26_0 -> False) -> False)
  -> ((v2_funct_1 esk27_0 -> False) -> False)
  -> ((v1_setfam_1 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk39_0 -> False) -> False)
  -> ((v2_relat_1 esk34_0 -> False) -> False)
  -> ((v2_relat_1 esk29_0 -> False) -> False)
  -> ((v1_card_3 esk18_0 -> False) -> False)
  -> ((v2_card_3 esk33_0 -> False) -> False)
  -> ((v2_card_3 esk3_0 -> False) -> False)
  -> ((v4_funct_1 esk45_0 -> False) -> False)
  -> ((v4_funct_1 esk33_0 -> False) -> False)
  -> ((v4_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funcop_1 esk19_0 -> False) -> False)
  -> ((v1_funcop_1 esk2_0 -> False) -> False)
  -> ((v1_funct_1 esk42_0 -> False) -> False)
  -> ((v1_funct_1 esk39_0 -> False) -> False)
  -> ((v1_funct_1 esk34_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk26_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk19_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk42_0 -> False) -> False)
  -> ((v1_relat_1 esk39_0 -> False) -> False)
  -> ((v1_relat_1 esk34_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk25_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> (((k10_xtuple_0 esk2_0) = esk3_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
