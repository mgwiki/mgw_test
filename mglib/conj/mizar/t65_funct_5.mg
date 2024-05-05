(** $I sig/MizarPreamble.mgs **)

Theorem t65_funct_5:
 forall k8_relat_1:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall esk17_3:set -> set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall esk10_3:set -> set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall v2_relat_1:set -> prop,
 forall m1_funct_2:set -> set -> set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk16_2:set -> set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall esk34_1:set -> set,
 forall esk31_1:set -> set,
 forall k1_xboole_0:set,
 forall esk29_1:set -> set,
 forall esk35_0:set,
 forall esk27_0:set,
 forall esk26_1:set -> set,
 forall esk25_0:set,
 forall esk20_0:set,
 forall esk23_0:set,
 forall o_0_0_xboole_0:set,
 forall esk24_0:set,
 forall esk28_0:set,
 forall v1_card_1:set -> prop,
 forall esk19_1:set -> set,
 forall esk18_2:set -> set -> set,
 forall esk21_0:set,
 forall esk30_0:set,
 forall esk32_0:set,
 forall esk22_1:set -> set,
 forall esk33_1:set -> set,
 forall v1_setfam_1:set -> prop,
 forall r2_tarski:set -> set -> prop,
 forall v3_relat_1:set -> prop,
 forall esk14_1:set -> set,
 forall esk15_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk13_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall v2_funct_1:set -> prop,
 forall esk11_2:set -> set -> set,
 forall esk38_2:set -> set -> set,
 forall esk4_0:set,
 forall k1_card_1:set -> set,
 forall r2_wellord2:set -> set -> prop,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall k1_zfmisc_1:set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall k9_funct_2:set -> set -> set,
 forall esk36_3:set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall esk37_4:set -> set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk6_4:set -> set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall k1_funct_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X2 X1 X3 X4, (r1_tarski (k10_xtuple_0 (esk6_4 X1 X2 X3 X4)) X2 -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X3 X1, (X3 = (k8_relat_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden (esk17_3 X1 X2 X3) X3 -> r2_hidden (esk17_3 X1 X2 X3) (k9_xtuple_0 X1) -> r2_hidden (k1_funct_1 X1 (esk17_3 X1 X2 X3)) X2 -> False)
  -> (forall X3 X4 X5 X2 X1, ((k1_funct_1 (esk37_4 X3 X4 X5 X2) X1) = X3 -> False) -> r2_hidden X1 X5 -> r2_hidden X1 X2 -> False)
  -> (forall X4 X3 X2 X5 X1, ((k1_funct_1 (esk37_4 X3 X4 X5 X2) X1) = X4 -> False) -> (r2_hidden X1 X2 -> False) -> r2_hidden X1 X5 -> False)
  -> (forall X2 X1 X3 X4, ((k9_xtuple_0 (esk6_4 X1 X2 X3 X4)) = X1 -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (v1_relat_1 (esk6_4 X1 X2 X3 X4) -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (v1_funct_1 (esk6_4 X1 X2 X3 X4) -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X3 X1, (X3 = (k8_relat_1 X1 X2) -> False) -> (r2_hidden (esk17_3 X1 X2 X3) X3 -> False) -> (r2_hidden (k1_funct_1 X1 (esk17_3 X1 X2 X3)) X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, (X3 = (k1_funct_2 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r1_tarski (k10_xtuple_0 (esk8_3 X1 X2 X3)) X2 -> False) -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k1_funct_2 X1 X2) -> False) -> (k9_xtuple_0 X4) = X1 -> (esk7_3 X1 X2 X3) = X4 -> v1_funct_1 X4 -> v1_relat_1 X4 -> r1_tarski (k10_xtuple_0 X4) X2 -> r2_hidden (esk7_3 X1 X2 X3) X3 -> False)
  -> (forall X2 X4 X3 X1, ((k1_funct_1 (esk36_3 X3 X4 X2) X1) = (k8_relat_1 X1 (k1_tarski X3)) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X1 (k9_funct_2 X2 (k2_tarski X3 X4)) -> False)
  -> (forall X3 X2 X4 X1, ((esk6_4 X2 X3 X4 X1) = X1 -> False) -> X4 = (k1_funct_2 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> (esk9_3 X1 X2 X3) = X1 -> r2_hidden (esk9_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> (esk9_3 X1 X2 X3) = X2 -> r2_hidden (esk9_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k8_relat_1 X1 X2) -> False) -> (r2_hidden (esk17_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk17_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> ((k9_xtuple_0 (esk8_3 X1 X2 X3)) = X1 -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k2_tarski X1 X2) -> False) -> ((esk9_3 X1 X2 X3) = X2 -> False) -> ((esk9_3 X1 X2 X3) = X1 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> (v1_relat_1 (esk8_3 X1 X2 X3) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> (v1_funct_1 (esk8_3 X1 X2 X3) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> ((esk7_3 X1 X2 X3) = (esk8_3 X1 X2 X3) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> ((k1_card_1 (k9_funct_2 esk4_0 (k2_tarski esk1_0 esk2_0))) = (k1_card_1 (k1_zfmisc_1 esk4_0)) -> r2_wellord2 (k9_funct_2 esk3_0 (k2_tarski esk1_0 esk2_0)) (k1_zfmisc_1 esk3_0) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk10_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> (k1_funct_1 X1 (esk38_2 X1 X2)) = (k1_funct_1 X2 (esk38_2 X1 X2)) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk10_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk11_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk11_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k8_relat_1 X2 X3) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> r2_hidden (k1_funct_1 X2 X1) X3 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (k1_funct_1 X1 X2) = (k1_funct_1 X1 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden X2 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk12_2 X1 X2)) = (esk11_2 X1 X2) -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> (r2_hidden (esk12_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X4 X2 X1 X3, (r2_hidden (k1_funct_1 X1 X2) X3 -> False) -> X4 = (k8_relat_1 X1 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X2 X4 -> False)
  -> (forall X1 X4 X3 X2 X5, (r2_hidden X2 X5 -> False) -> X1 = X2 -> (k9_xtuple_0 X1) = X3 -> X5 = (k1_funct_2 X3 X4) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r1_tarski (k10_xtuple_0 X1) X4 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X3 X2 X1, v1_xboole_0 X1 -> m1_funct_2 X1 X2 X3 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk5_2 X1 X2) = X1 -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk38_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_funct_2 (k9_funct_2 X2 X1) X2 X1 -> False) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 (k9_xtuple_0 X2) -> False) -> X3 = (k8_relat_1 X2 X4) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk13_2 X1 X2) X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk5_2 X1 X2) = X1 -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((k1_funct_1 X1 (esk15_1 X1)) = (k1_funct_1 X1 (esk14_1 X1)) -> False) -> (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k10_xtuple_0 (esk16_2 X1 X2)) = X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk16_2 X1 X2)) = X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski (k8_relat_1 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v2_funct_1 (esk16_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (esk16_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 (esk16_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1 X2 X3, (r2_wellord2 X2 X3 -> False) -> (k9_xtuple_0 X1) = X2 -> (k10_xtuple_0 X1) = X3 -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> (X1 = X3 -> False) -> X2 = (k2_tarski X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r2_hidden (esk15_1 X1) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r2_hidden (esk14_1 X1) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k8_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k8_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X2 X4) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X4 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (r2_tarski X1 X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> r2_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X2 X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k1_funct_2 X2 X1) = (k9_funct_2 X2 X1) -> False) -> (v1_xboole_0 X1 -> False) -> False)
  -> (forall X1, (v1_setfam_1 (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (esk15_1 X1) = (esk14_1 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, ((k1_card_1 X1) = (k1_card_1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> (k1_card_1 X1) = (k1_card_1 X2) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk31_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk34_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk33_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk33_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk29_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk32_0 -> False)
  -> (v1_xboole_0 esk35_0 -> False)
  -> (v1_xboole_0 esk30_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (esk1_0 = esk2_0 -> False)
  -> (forall X3 X1 X4 X2, ((k9_xtuple_0 (esk37_4 X1 X2 X3 X4)) = X3 -> False) -> False)
  -> (forall X2 X3 X4 X1, (v1_relat_1 (esk37_4 X1 X2 X3 X4) -> False) -> False)
  -> (forall X2 X3 X4 X1, (v1_funct_1 (esk37_4 X1 X2 X3 X4) -> False) -> False)
  -> (forall X1 X2 X3, ((k9_xtuple_0 (esk36_3 X1 X2 X3)) = (k9_funct_2 X3 (k2_tarski X1 X2)) -> False) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (esk36_3 X1 X2 X3) -> False) -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (esk36_3 X1 X2 X3) -> False) -> False)
  -> (forall X2 X1, (m1_funct_2 (esk18_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k1_card_1 (k1_card_1 X1)) = (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (r2_wellord2 X1 X1 -> False) -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk26_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk35_0 -> False) -> False)
  -> ((v2_relat_1 esk30_0 -> False) -> False)
  -> ((v2_relat_1 esk28_0 -> False) -> False)
  -> ((v2_relat_1 esk25_0 -> False) -> False)
  -> ((v2_funct_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk32_0 -> False) -> False)
  -> ((v1_relat_1 esk30_0 -> False) -> False)
  -> ((v1_relat_1 esk28_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk32_0 -> False) -> False)
  -> ((v1_funct_1 esk30_0 -> False) -> False)
  -> ((v1_funct_1 esk28_0 -> False) -> False)
  -> ((v1_funct_1 esk24_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 esk23_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
