(** $I sig/MizarPreamble.mgs **)

Theorem t26_funct_5:
 forall epred1_2:set -> set -> prop,
 forall k9_xtuple_0:set -> set,
 forall k2_tarski:set -> set -> set,
 forall esk42_3:set -> set -> set -> set,
 forall esk40_3:set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk35_2:set -> set -> set,
 forall esk33_2:set -> set -> set,
 forall esk34_2:set -> set -> set,
 forall esk43_2:set -> set -> set,
 forall k2_xtuple_0:set -> set,
 forall esk48_2:set -> set -> set,
 forall esk47_2:set -> set -> set,
 forall esk41_3:set -> set -> set -> set,
 forall esk45_2:set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v2_relat_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk1_0:set,
 forall esk3_0:set,
 forall k4_funct_5:set -> set,
 forall k2_funct_4:set -> set,
 forall v3_relat_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v1_setfam_1:set -> prop,
 forall esk29_1:set -> set,
 forall esk25_1:set -> set,
 forall k1_xboole_0:set,
 forall esk23_1:set -> set,
 forall esk30_0:set,
 forall esk20_0:set,
 forall esk22_2:set -> set -> set,
 forall esk19_1:set -> set,
 forall esk10_1:set -> set,
 forall esk16_0:set,
 forall esk18_0:set,
 forall esk15_0:set,
 forall esk11_0:set,
 forall o_0_0_xboole_0:set,
 forall esk17_0:set,
 forall esk21_0:set,
 forall esk31_1:set -> set,
 forall esk2_0:set,
 forall esk28_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall esk12_0:set,
 forall esk24_0:set,
 forall esk26_0:set,
 forall v2_funct_1:set -> prop,
 forall esk14_1:set -> set,
 forall esk27_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v1_xtuple_0:set -> prop,
 forall esk9_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_xtuple_0:set -> set,
 forall esk46_2:set -> set -> set,
 forall esk44_2:set -> set -> set,
 forall esk38_2:set -> set -> set,
 forall esk37_2:set -> set -> set,
 forall esk39_2:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall esk32_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall esk36_2:set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k2_funct_5:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk4_4:set -> set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall k1_funct_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X2 X1 X3 X4, (r1_tarski (k10_xtuple_0 (esk4_4 X1 X2 X3 X4)) X2 -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X3 X1, ((k2_tarski (k2_tarski (esk40_3 X2 X3 X1) (esk42_3 X2 X3 X1)) (k1_tarski (esk40_3 X2 X3 X1))) = X1 -> False) -> epred1_2 X3 X2 -> r2_hidden X1 (k9_xtuple_0 X3) -> False)
  -> (forall X6 X7 X8 X5 X4 X3 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> X6 = (k1_funct_1 X2 X7) -> X3 = (k1_funct_1 X2 X4) -> (esk32_2 X1 X2) = (k2_tarski (k2_tarski X7 X8) (k1_tarski X7)) -> (esk36_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X6 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X6 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X8 (k9_xtuple_0 X6) -> r2_hidden X7 (k9_xtuple_0 X2) -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False)
  -> (forall X3 X4 X5 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk33_2 X1 X2) (esk35_2 X1 X2)) (k1_tarski (esk33_2 X1 X2))) = (esk32_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk36_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False)
  -> (forall X3 X4 X5 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk37_2 X1 X2) (esk39_2 X1 X2)) (k1_tarski (esk37_2 X1 X2))) = (esk36_2 X1 X2) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk32_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk33_2 X1 X2) (esk35_2 X1 X2)) (k1_tarski (esk33_2 X1 X2))) = (esk32_2 X1 X2) -> False) -> ((k2_tarski (k2_tarski (esk37_2 X1 X2) (esk39_2 X1 X2)) (k1_tarski (esk37_2 X1 X2))) = (esk36_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X2 X1 X3 X4, ((k9_xtuple_0 (esk4_4 X1 X2 X3 X4)) = X1 -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (v1_funct_1 (esk4_4 X1 X2 X3 X4) -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (v1_relat_1 (esk4_4 X1 X2 X3 X4) -> False) -> X3 = (k1_funct_2 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X3 X4 X5 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk35_2 X1 X2) (k9_xtuple_0 (esk34_2 X1 X2)) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk36_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False)
  -> (forall X3 X4 X5 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk39_2 X1 X2) (k9_xtuple_0 (esk38_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk32_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False)
  -> (forall X3 X4 X5 X1 X2, (epred1_2 X1 X2 -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk43_2 X2 X1) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> (k1_funct_1 (esk48_2 X2 X1) (k2_xtuple_0 (esk47_2 X2 X1))) = (k1_funct_1 X1 (esk47_2 X2 X1)) -> v1_relat_1 X3 -> v1_funct_1 X3 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk43_2 X2 X1) (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk37_2 X1 X2) (esk39_2 X1 X2)) (k1_tarski (esk37_2 X1 X2))) = (esk36_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk35_2 X1 X2) (k9_xtuple_0 (esk34_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk33_2 X1 X2) (esk35_2 X1 X2)) (k1_tarski (esk33_2 X1 X2))) = (esk32_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk39_2 X1 X2) (k9_xtuple_0 (esk38_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X2 X1, ((k2_tarski (k2_tarski (esk44_2 X2 X1) (esk46_2 X2 X1)) (k1_tarski (esk44_2 X2 X1))) = (esk43_2 X2 X1) -> False) -> (epred1_2 X1 X2 -> False) -> (r2_hidden (esk43_2 X2 X1) (k9_xtuple_0 X1) -> False) -> (k1_funct_1 (esk48_2 X2 X1) (k2_xtuple_0 (esk47_2 X2 X1))) = (k1_funct_1 X1 (esk47_2 X2 X1)) -> False)
  -> (forall X3 X4 X5 X2 X1, ((k1_funct_1 X2 (esk33_2 X1 X2)) = (esk34_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk36_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False)
  -> (forall X3 X4 X5 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk33_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk36_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False)
  -> (forall X3 X4 X5 X2 X1, ((k1_funct_1 X2 (esk37_2 X1 X2)) = (esk38_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk32_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False)
  -> (forall X3 X4 X5 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk37_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk32_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False)
  -> (forall X3 X4 X5 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_funct_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk36_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False)
  -> (forall X3 X4 X5 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk36_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk37_2 X1 X2)) = (esk38_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk33_2 X1 X2) (esk35_2 X1 X2)) (k1_tarski (esk33_2 X1 X2))) = (esk32_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk33_2 X1 X2)) = (esk34_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk37_2 X1 X2) (esk39_2 X1 X2)) (k1_tarski (esk37_2 X1 X2))) = (esk36_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk37_2 X1 X2) (esk39_2 X1 X2)) (k1_tarski (esk37_2 X1 X2))) = (esk36_2 X1 X2) -> False) -> (r2_hidden (esk33_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk33_2 X1 X2) (esk35_2 X1 X2)) (k1_tarski (esk33_2 X1 X2))) = (esk32_2 X1 X2) -> False) -> (r2_hidden (esk37_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X3 X4 X5 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_funct_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk32_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False)
  -> (forall X3 X4 X5 X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> X3 = (k1_funct_1 X2 X4) -> (esk32_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X2) -> r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk37_2 X1 X2) (esk39_2 X1 X2)) (k1_tarski (esk37_2 X1 X2))) = (esk36_2 X1 X2) -> False) -> (v1_funct_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk37_2 X1 X2) (esk39_2 X1 X2)) (k1_tarski (esk37_2 X1 X2))) = (esk36_2 X1 X2) -> False) -> (v1_relat_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk33_2 X1 X2) (esk35_2 X1 X2)) (k1_tarski (esk33_2 X1 X2))) = (esk32_2 X1 X2) -> False) -> (v1_funct_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> ((k2_tarski (k2_tarski (esk33_2 X1 X2) (esk35_2 X1 X2)) (k1_tarski (esk33_2 X1 X2))) = (esk32_2 X1 X2) -> False) -> (v1_relat_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk42_3 X1 X2 X3) (k9_xtuple_0 (esk41_3 X1 X2 X3)) -> False) -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk35_2 X1 X2) (k9_xtuple_0 (esk34_2 X1 X2)) -> False) -> (r2_hidden (esk39_2 X1 X2) (k9_xtuple_0 (esk38_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden (esk43_2 X2 X1) (k9_xtuple_0 X1) -> False) -> (r2_hidden (esk46_2 X2 X1) (k9_xtuple_0 (esk45_2 X2 X1)) -> False) -> (k1_funct_1 (esk48_2 X2 X1) (k2_xtuple_0 (esk47_2 X2 X1))) = (k1_funct_1 X1 (esk47_2 X2 X1)) -> False)
  -> (forall X5 X4 X3 X2 X1, ((k1_funct_1 X1 (k1_xtuple_0 (esk47_2 X1 X2))) = (esk48_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> X3 = (k1_funct_1 X1 X4) -> (esk43_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_funct_1 X3 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X1) -> r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1 X3, (X3 = (k1_funct_2 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (r1_tarski (k10_xtuple_0 (esk6_3 X1 X2 X3)) X2 -> False) -> False)
  -> (forall X2 X1, ((k1_funct_1 X1 (k1_xtuple_0 (esk47_2 X1 X2))) = (esk48_2 X1 X2) -> False) -> ((k2_tarski (k2_tarski (esk44_2 X1 X2) (esk46_2 X1 X2)) (k1_tarski (esk44_2 X1 X2))) = (esk43_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k1_funct_2 X1 X2) -> False) -> (k9_xtuple_0 X4) = X1 -> (esk5_3 X1 X2 X3) = X4 -> v1_relat_1 X4 -> v1_funct_1 X4 -> r1_tarski (k10_xtuple_0 X4) X2 -> r2_hidden (esk5_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk37_2 X1 X2)) = (esk38_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk35_2 X1 X2) (k9_xtuple_0 (esk34_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk33_2 X1 X2)) = (esk34_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk39_2 X1 X2) (k9_xtuple_0 (esk38_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X2 X1, ((k1_funct_1 X2 (esk44_2 X2 X1)) = (esk45_2 X2 X1) -> False) -> (epred1_2 X1 X2 -> False) -> (r2_hidden (esk43_2 X2 X1) (k9_xtuple_0 X1) -> False) -> (k1_funct_1 (esk48_2 X2 X1) (k2_xtuple_0 (esk47_2 X2 X1))) = (k1_funct_1 X1 (esk47_2 X2 X1)) -> False)
  -> (forall X5 X4 X3 X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden (esk47_2 X1 X2) (k9_xtuple_0 X2) -> False) -> X3 = (k1_funct_1 X1 X4) -> (esk43_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_funct_1 X3 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X1) -> r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk37_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk35_2 X1 X2) (k9_xtuple_0 (esk34_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk33_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk39_2 X1 X2) (k9_xtuple_0 (esk38_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (r2_hidden (esk43_2 X2 X1) (k9_xtuple_0 X1) -> False) -> (r2_hidden (esk44_2 X2 X1) (k9_xtuple_0 X2) -> False) -> (k1_funct_1 (esk48_2 X2 X1) (k2_xtuple_0 (esk47_2 X2 X1))) = (k1_funct_1 X1 (esk47_2 X2 X1)) -> False)
  -> (forall X2 X1, ((k2_tarski (k2_tarski (esk44_2 X1 X2) (esk46_2 X1 X2)) (k1_tarski (esk44_2 X1 X2))) = (esk43_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk47_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X5 X4 X3 X2 X1, (epred1_2 X2 X1 -> False) -> (v1_funct_1 (esk48_2 X1 X2) -> False) -> X3 = (k1_funct_1 X1 X4) -> (esk43_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_funct_1 X3 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X1) -> r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False)
  -> (forall X5 X4 X3 X2 X1, (epred1_2 X2 X1 -> False) -> (v1_relat_1 (esk48_2 X1 X2) -> False) -> X3 = (k1_funct_1 X1 X4) -> (esk43_2 X1 X2) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> v1_relat_1 X3 -> v1_funct_1 X3 -> r2_hidden X5 (k9_xtuple_0 X3) -> r2_hidden X4 (k9_xtuple_0 X1) -> r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_funct_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk35_2 X1 X2) (k9_xtuple_0 (esk34_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_funct_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk39_2 X1 X2) (k9_xtuple_0 (esk38_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk35_2 X1 X2) (k9_xtuple_0 (esk34_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk39_2 X1 X2) (k9_xtuple_0 (esk38_2 X1 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (v1_funct_1 (esk45_2 X2 X1) -> False) -> (r2_hidden (esk43_2 X2 X1) (k9_xtuple_0 X1) -> False) -> (k1_funct_1 (esk48_2 X2 X1) (k2_xtuple_0 (esk47_2 X2 X1))) = (k1_funct_1 X1 (esk47_2 X2 X1)) -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> (v1_relat_1 (esk45_2 X2 X1) -> False) -> (r2_hidden (esk43_2 X2 X1) (k9_xtuple_0 X1) -> False) -> (k1_funct_1 (esk48_2 X2 X1) (k2_xtuple_0 (esk47_2 X2 X1))) = (k1_funct_1 X1 (esk47_2 X2 X1)) -> False)
  -> (forall X2 X1, ((k2_tarski (k2_tarski (esk44_2 X1 X2) (esk46_2 X1 X2)) (k1_tarski (esk44_2 X1 X2))) = (esk43_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (v1_funct_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski (k2_tarski (esk44_2 X1 X2) (esk46_2 X1 X2)) (k1_tarski (esk44_2 X1 X2))) = (esk43_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (v1_relat_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X3 X2 X4 X1, ((esk4_4 X2 X3 X4 X1) = X1 -> False) -> X4 = (k1_funct_2 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk33_2 X1 X2)) = (esk34_2 X1 X2) -> False) -> ((k1_funct_1 X2 (esk37_2 X1 X2)) = (esk38_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk37_2 X1 X2)) = (esk38_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk33_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk33_2 X1 X2)) = (esk34_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk37_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk33_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk37_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk37_2 X1 X2)) = (esk38_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_funct_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk37_2 X1 X2)) = (esk38_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk33_2 X1 X2)) = (esk34_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_funct_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k1_funct_1 X2 (esk33_2 X1 X2)) = (esk34_2 X1 X2) -> False) -> ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_funct_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk33_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_funct_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk37_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk33_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk37_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> ((k9_xtuple_0 (esk6_3 X1 X2 X3)) = X1 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> (v1_funct_1 (esk6_3 X1 X2 X3) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> (v1_relat_1 (esk6_3 X1 X2 X3) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X2 X1, ((k1_funct_1 X1 (k1_xtuple_0 (esk47_2 X1 X2))) = (esk48_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk46_2 X1 X2) (k9_xtuple_0 (esk45_2 X1 X2)) -> False) -> False)
  -> (forall X3 X2 X1, (X3 = (k1_funct_2 X1 X2) -> False) -> ((esk5_3 X1 X2 X3) = (esk6_3 X1 X2 X3) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_funct_1 (esk34_2 X1 X2) -> False) -> (v1_funct_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk38_2 X1 X2) -> False) -> (v1_funct_1 (esk34_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk34_2 X1 X2) -> False) -> (v1_funct_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2, ((k2_zfmisc_1 (k9_xtuple_0 X2) X1) = (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (v1_relat_1 (esk34_2 X1 X2) -> False) -> (v1_relat_1 (esk38_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) (k9_xtuple_0 (k2_funct_5 X2)) -> False) -> (r2_hidden (esk36_2 X1 X2) (k2_zfmisc_1 (k9_xtuple_0 X2) X1) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2 X3, ((k1_funct_1 X1 (esk40_3 X1 X2 X3)) = (esk41_3 X1 X2 X3) -> False) -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X3 X5 X4 X2 X6, (r2_hidden X2 (k9_xtuple_0 X6) -> False) -> X1 = (k1_funct_1 X5 X3) -> X2 = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> v1_relat_1 X1 -> v1_funct_1 X1 -> epred1_2 X6 X5 -> r2_hidden X4 (k9_xtuple_0 X1) -> r2_hidden X3 (k9_xtuple_0 X5) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk47_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk46_2 X1 X2) (k9_xtuple_0 (esk45_2 X1 X2)) -> False) -> False)
  -> (forall X2 X1, ((k1_funct_1 X1 (esk44_2 X1 X2)) = (esk45_2 X1 X2) -> False) -> ((k1_funct_1 X1 (k1_xtuple_0 (esk47_2 X1 X2))) = (esk48_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X1 X2, ((k1_funct_1 X1 (k1_xtuple_0 (esk47_2 X1 X2))) = (esk48_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk44_2 X1 X2) (k9_xtuple_0 X1) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (v1_funct_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk46_2 X1 X2) (k9_xtuple_0 (esk45_2 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (v1_relat_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk46_2 X1 X2) (k9_xtuple_0 (esk45_2 X1 X2)) -> False) -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk40_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, ((k1_funct_1 X1 (k1_xtuple_0 (esk47_2 X1 X2))) = (esk48_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (v1_funct_1 (esk45_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X2 X1, ((k1_funct_1 X1 (k1_xtuple_0 (esk47_2 X1 X2))) = (esk48_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (v1_relat_1 (esk45_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk7_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk7_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2 X3, (v1_funct_1 (esk41_3 X1 X2 X3) -> False) -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2 X3, (v1_relat_1 (esk41_3 X1 X2 X3) -> False) -> epred1_2 X2 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, ((k1_funct_1 X1 (esk44_2 X1 X2)) = (esk45_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk47_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk8_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk8_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk44_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (r2_hidden (esk47_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X2 X1, ((k1_funct_1 X1 (esk44_2 X1 X2)) = (esk45_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (v1_funct_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X2 X1, ((k1_funct_1 X1 (esk44_2 X1 X2)) = (esk45_2 X1 X2) -> False) -> (epred1_2 X2 X1 -> False) -> (v1_relat_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (v1_funct_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk44_2 X1 X2) (k9_xtuple_0 X1) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (v1_funct_1 (esk45_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk47_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X1 X2, (epred1_2 X2 X1 -> False) -> (v1_relat_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk44_2 X1 X2) (k9_xtuple_0 X1) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (v1_relat_1 (esk45_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (esk47_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X4 X3 X2 X1, ((k1_funct_1 X3 X2) = (k1_funct_1 X1 (k2_xtuple_0 X2)) -> False) -> X1 = (k1_funct_1 X4 (k1_xtuple_0 X2)) -> v1_relat_1 X1 -> v1_funct_1 X1 -> epred1_2 X3 X4 -> r2_hidden X2 (k9_xtuple_0 X3) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (v1_funct_1 (esk45_2 X1 X2) -> False) -> (v1_funct_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (v1_relat_1 (esk48_2 X1 X2) -> False) -> (v1_funct_1 (esk45_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (v1_relat_1 (esk45_2 X1 X2) -> False) -> (v1_funct_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X2 X1, (epred1_2 X2 X1 -> False) -> (v1_relat_1 (esk45_2 X1 X2) -> False) -> (v1_relat_1 (esk48_2 X1 X2) -> False) -> (r2_hidden (esk43_2 X1 X2) (k9_xtuple_0 X2) -> False) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk9_2 X1 X2)) = (esk8_2 X1 X2) -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, ((k2_tarski (k2_tarski (k1_xtuple_0 X2) (k2_xtuple_0 X2)) (k1_tarski (k1_xtuple_0 X2))) = X2 -> False) -> v1_relat_1 X1 -> r2_hidden X2 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> (r2_hidden (esk9_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X4 X3 X2 X5, (r2_hidden X2 X5 -> False) -> X1 = X2 -> (k9_xtuple_0 X1) = X3 -> X5 = (k1_funct_2 X3 X4) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r1_tarski (k10_xtuple_0 X1) X4 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (k1_xtuple_0 X1) (k2_xtuple_0 X1)) (k1_tarski (k1_xtuple_0 X1))) = X1 -> False) -> v1_xtuple_0 X1 -> False)
  -> (forall X3 X1 X2, (r2_hidden (k2_xtuple_0 X1) X2 -> False) -> r2_hidden X1 (k2_zfmisc_1 X3 X2) -> False)
  -> (forall X3 X1 X2, (r2_hidden (k1_xtuple_0 X1) X2 -> False) -> r2_hidden X1 (k2_zfmisc_1 X2 X3) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> ((k2_zfmisc_1 esk1_0 (k9_xtuple_0 esk3_0)) = (k9_xtuple_0 (k4_funct_5 esk3_0)) -> (k2_zfmisc_1 (k9_xtuple_0 esk3_0) esk1_0) = (k9_xtuple_0 (k2_funct_5 esk3_0)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (k2_funct_4 X1)) = (k2_zfmisc_1 X3 X2) -> False) -> (k9_xtuple_0 X1) = (k2_zfmisc_1 X2 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (X1 = (k2_funct_5 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (epred1_2 X1 X2 -> False) -> X1 = (k2_funct_5 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_setfam_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k2_funct_4 (k2_funct_5 X1)) = (k4_funct_5 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk25_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_4 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k4_funct_5 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_5 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_4 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k4_funct_5 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_5 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk29_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk14_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk23_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk26_0 -> False)
  -> (v1_xboole_0 esk30_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, ((k2_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X2 -> False) -> False)
  -> (forall X1 X2, ((k1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X1 -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk28_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk22_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk13_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk28_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk22_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk13_2 X1 X2) X1 -> False) -> False)
  -> ((r1_tarski (k10_xtuple_0 esk3_0) (k1_funct_2 esk1_0 esk2_0) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk28_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk31_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk31_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk31_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk31_1 X1) -> False) -> False)
  -> ((v1_xtuple_0 esk16_0 -> False) -> False)
  -> ((v4_funct_1 esk30_0 -> False) -> False)
  -> ((v2_relat_1 esk24_0 -> False) -> False)
  -> ((v2_relat_1 esk21_0 -> False) -> False)
  -> ((v2_relat_1 esk18_0 -> False) -> False)
  -> ((v2_funct_1 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk26_0 -> False) -> False)
  -> ((v1_funct_1 esk24_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk11_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_relat_1 esk3_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
