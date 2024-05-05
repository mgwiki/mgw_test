(** $I sig/MizarPreamble.mgs **)

Theorem t60_funct_5:
 forall k3_relat_1:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall esk36_4:set -> set -> set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall v2_funct_1:set -> prop,
 forall esk39_2:set -> set -> set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall r2_wellord2:set -> set -> prop,
 forall k1_card_1:set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk13_1:set -> set,
 forall esk12_1:set -> set,
 forall r2_tarski:set -> set -> prop,
 forall v1_setfam_1:set -> prop,
 forall esk31_1:set -> set,
 forall esk19_1:set -> set,
 forall esk27_1:set -> set,
 forall esk30_0:set,
 forall esk28_0:set,
 forall esk17_0:set,
 forall esk26_2:set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall esk35_1:set -> set,
 forall esk15_1:set -> set,
 forall v1_card_1:set -> prop,
 forall esk22_0:set,
 forall esk16_0:set,
 forall esk20_0:set,
 forall o_0_0_xboole_0:set,
 forall esk21_0:set,
 forall esk25_0:set,
 forall esk23_1:set -> set,
 forall esk32_2:set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall esk24_0:set,
 forall esk34_0:set,
 forall k1_xboole_0:set,
 forall esk29_1:set -> set,
 forall esk33_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall k2_funct_1:set -> set,
 forall esk14_2:set -> set -> set,
 forall esk37_1:set -> set,
 forall esk38_1:set -> set,
 forall k4_relat_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk11_2:set -> set -> set,
 forall v2_relat_1:set -> prop,
 forall esk10_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk9_2:set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk5_4:set -> set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall k1_funct_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X2 X1 X3 X4, (r1_tarski (k10_xtuple_0 (esk5_4 X1 X2 X3 X4)) X2 -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X4 X3 X2 X1 X5, ((k1_funct_1 (esk36_4 X2 X3 X4 X5) X1) = (k3_relat_1 (k3_relat_1 X4 X1) X5) -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X5 -> v1_relat_1 X4 -> v1_relat_1 X1 -> r2_hidden X1 (k1_funct_2 X2 X3) -> False)
  -> (forall X2 X1 X3 X4, ((k9_xtuple_0 (esk5_4 X1 X2 X3 X4)) = X1 -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (v1_relat_1 (esk5_4 X1 X2 X3 X4) -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (v1_funct_1 (esk5_4 X1 X2 X3 X4) -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X1 X2 X3 X4, ((k9_xtuple_0 (esk36_4 X1 X2 X3 X4)) = (k1_funct_2 X1 X2) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> False)
  -> (forall X2 X1 X3 X4, (v1_relat_1 (esk36_4 X1 X2 X3 X4) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> False)
  -> (forall X2 X1 X3 X4, (v1_funct_1 (esk36_4 X1 X2 X3 X4) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k1_funct_2 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r1_tarski (k10_xtuple_0 (esk7_3 X1 X2 X3)) X2 -> False) -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k1_funct_2 X1 X2) -> False) -> (k9_xtuple_0 X4) = X1 -> (esk6_3 X1 X2 X3) = X4 -> v1_funct_1 X4 -> v1_relat_1 X4 -> r1_tarski (k10_xtuple_0 X4) X2 -> r2_hidden (esk6_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X4 X1, ((esk5_4 X2 X3 X4 X1) = X1 -> False) -> X4 = (k1_funct_2 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> ((k9_xtuple_0 (esk7_3 X1 X2 X3)) = X1 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> (v1_relat_1 (esk7_3 X1 X2 X3) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> (v1_funct_1 (esk7_3 X1 X2 X3) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> ((esk6_3 X1 X2 X3) = (esk7_3 X1 X2 X3) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (k9_xtuple_0 X2) = (k9_xtuple_0 X3) -> (k3_relat_1 X2 X1) = (k3_relat_1 X3 X1) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X1 -> r1_tarski (k10_xtuple_0 X3) (k9_xtuple_0 X1) -> r1_tarski (k10_xtuple_0 X2) (k9_xtuple_0 X1) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk8_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> (k1_funct_1 X1 (esk39_2 X1 X2)) = (k1_funct_1 X2 (esk39_2 X1 X2)) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk8_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 X3 -> False)
  -> ((k1_card_1 (k1_funct_2 esk2_0 esk4_0)) = (k1_card_1 (k1_funct_2 esk1_0 esk3_0)) -> r2_wellord2 (k1_funct_2 esk1_0 esk3_0) (k1_funct_2 esk2_0 esk4_0) -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk9_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k3_relat_1 X1 X2) X3) = (k1_funct_1 X2 (k1_funct_1 X1 X3)) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (k1_funct_1 X1 X2) = (k1_funct_1 X1 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden X2 (k9_xtuple_0 X1) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk10_2 X1 X2)) = (esk9_2 X1 X2) -> False) -> (r2_hidden (esk9_2 X1 X2) X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk9_2 X1 X2) X2 -> False) -> (r2_hidden (esk10_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2 X3, ((k3_relat_1 (k3_relat_1 X1 X2) X3) = (k3_relat_1 X1 (k3_relat_1 X2 X3)) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X4 X3 X2 X5, (r2_hidden X2 X5 -> False) -> X1 = X2 -> (k9_xtuple_0 X1) = X3 -> X5 = (k1_funct_2 X3 X4) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r1_tarski (k10_xtuple_0 X1) X4 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (r1_tarski (k10_xtuple_0 (k3_relat_1 X1 X2)) (k10_xtuple_0 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk39_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, ((k10_xtuple_0 (k3_relat_1 X2 X1)) = (k10_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_tarski (k9_xtuple_0 X1) (k10_xtuple_0 X2) -> False)
  -> (forall X1 X2, ((k9_xtuple_0 (k3_relat_1 X1 X2)) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_tarski (k10_xtuple_0 X1) (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk11_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v2_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k3_relat_1 X1 (k4_relat_1 X2)) = X1 -> False) -> v1_relat_1 X1 -> r1_tarski (k10_xtuple_0 X1) X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((k3_relat_1 (esk38_1 X1) X1) = (k3_relat_1 (esk37_1 X1) X1) -> False) -> (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, ((k1_funct_1 X1 (esk13_1 X1)) = (k1_funct_1 X1 (esk12_1 X1)) -> False) -> (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r1_tarski (k10_xtuple_0 (esk38_1 X1)) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r1_tarski (k10_xtuple_0 (esk37_1 X1)) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k10_xtuple_0 (esk14_2 X1 X2)) = X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk14_2 X1 X2)) = X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v2_funct_1 (esk14_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (esk14_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 (esk14_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1 X2 X3, (r2_wellord2 X2 X3 -> False) -> (k9_xtuple_0 X1) = X2 -> (k10_xtuple_0 X1) = X3 -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, ((k3_relat_1 (k2_funct_1 X1) X1) = (k4_relat_1 (k10_xtuple_0 X1)) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, ((k3_relat_1 X1 (k2_funct_1 X1)) = (k4_relat_1 (k9_xtuple_0 X1)) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v2_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r2_hidden (esk13_1 X1) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r2_hidden (esk12_1 X1) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1, ((k3_relat_1 (k4_relat_1 (k9_xtuple_0 X1)) X1) = X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1, ((k9_xtuple_0 (esk38_1 X1)) = (k9_xtuple_0 (esk37_1 X1)) -> False) -> (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r2_tarski X1 X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> r2_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X2 X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1, ((k9_xtuple_0 (k2_funct_1 X1)) = (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, ((k10_xtuple_0 (k2_funct_1 X1)) = (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_setfam_1 (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (esk38_1 X1) = (esk37_1 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (esk13_1 X1) = (esk12_1 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, ((k1_card_1 X1) = (k1_card_1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (v1_relat_1 (esk38_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (v1_relat_1 (esk37_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (v1_funct_1 (esk38_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (v1_funct_1 (esk37_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> (k1_card_1 X1) = (k1_card_1 X2) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk33_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k4_relat_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk31_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk27_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk30_0 -> False)
  -> (v1_xboole_0 esk34_0 -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk18_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k4_relat_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk32_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk26_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk18_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk32_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk26_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk18_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk32_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk26_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk32_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_partfun1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_relat_1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk35_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k1_card_1 (k1_card_1 X1)) = (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (r2_wellord2 X1 X1 -> False) -> False)
  -> ((r2_wellord2 esk3_0 esk4_0 -> False) -> False)
  -> ((r2_wellord2 esk1_0 esk2_0 -> False) -> False)
  -> (forall X1, ((k10_xtuple_0 (k4_relat_1 X1)) = X1 -> False) -> False)
  -> (forall X1, ((k9_xtuple_0 (k4_relat_1 X1)) = X1 -> False) -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v2_funct_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk23_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk34_0 -> False) -> False)
  -> ((v2_relat_1 esk28_0 -> False) -> False)
  -> ((v2_relat_1 esk25_0 -> False) -> False)
  -> ((v2_relat_1 esk22_0 -> False) -> False)
  -> ((v2_funct_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk30_0 -> False) -> False)
  -> ((v1_relat_1 esk28_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk30_0 -> False) -> False)
  -> ((v1_funct_1 esk28_0 -> False) -> False)
  -> ((v1_funct_1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
