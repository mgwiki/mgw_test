(** $I sig/MizarPreamble.mgs **)

Theorem t43_funct_6:
 forall esk38_4:set -> set -> set -> set -> set,
 forall esk36_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk10_3:set -> set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall esk39_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall r2_wellord2:set -> set -> prop,
 forall esk9_2:set -> set -> set,
 forall v1_finset_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v5_finset_1:set -> prop,
 forall r2_tarski:set -> set -> prop,
 forall v3_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v2_funcop_1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk35_0:set,
 forall esk33_0:set,
 forall esk29_0:set,
 forall esk26_0:set,
 forall esk22_0:set,
 forall esk15_0:set,
 forall v1_xtuple_0:set -> prop,
 forall esk21_0:set,
 forall esk30_0:set,
 forall esk25_0:set,
 forall esk23_0:set,
 forall o_0_0_xboole_0:set,
 forall esk17_0:set,
 forall esk20_0:set,
 forall esk18_0:set,
 forall esk16_0:set,
 forall esk28_0:set,
 forall esk13_1:set -> set,
 forall esk19_0:set,
 forall esk24_0:set,
 forall esk27_0:set,
 forall esk32_0:set,
 forall esk34_0:set,
 forall esk31_0:set,
 forall v7_ordinal1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall v1_setfam_1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall esk14_1:set -> set,
 forall v1_funcop_1:set -> prop,
 forall v2_finset_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk40_1:set -> set,
 forall k1_xboole_0:set,
 forall k2_tarski:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk8_2:set -> set -> set,
 forall k3_funct_6:set -> set,
 forall esk37_3:set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall k2_funct_6:set -> set,
 forall k4_card_3:set -> set,
 forall k8_relat_1:set -> set -> set,
 forall k1_funct_6:set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall k2_funct_5:set -> set,
 forall k1_binop_1:set -> set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk11_2:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k7_funct_6:set -> set,
     (forall X1 X3 X2, (X3 = (k7_funct_6 X2) -> False) -> (k9_xtuple_0 X3) = (k4_card_3 (k2_funct_6 X2)) -> (k1_funct_1 X3 (esk11_2 X2 X3)) = X1 -> (k9_xtuple_0 X1) = (k8_relat_1 X2 (k1_funct_6 (k10_xtuple_0 X2))) -> (k1_binop_1 (k2_funct_5 X2) (esk12_3 X2 X3 X1) (k1_funct_1 (esk11_2 X2 X3) (esk12_3 X2 X3 X1))) = (k1_funct_1 X1 (esk12_3 X2 X3 X1)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X6 X5 X2 X1 X4 X3, ((k10_xtuple_0 (esk38_4 X1 X2 X3 X4)) = (k1_funct_1 X3 X4) -> False) -> X5 = X6 -> (k9_xtuple_0 X5) = (k1_funct_1 X2 (esk36_3 X1 X2 X3)) -> (k10_xtuple_0 X5) = (k1_funct_1 X3 (esk36_3 X1 X2 X3)) -> v1_relat_1 X5 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X5 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v2_funct_1 X5 -> r2_hidden X4 X1 -> False)
  -> (forall X6 X5 X3 X1 X4 X2, ((k9_xtuple_0 (esk38_4 X1 X2 X3 X4)) = (k1_funct_1 X2 X4) -> False) -> X5 = X6 -> (k9_xtuple_0 X5) = (k1_funct_1 X2 (esk36_3 X1 X2 X3)) -> (k10_xtuple_0 X5) = (k1_funct_1 X3 (esk36_3 X1 X2 X3)) -> v1_relat_1 X5 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X5 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v2_funct_1 X5 -> r2_hidden X4 X1 -> False)
  -> (forall X6 X5 X1 X4 X3 X2, (v2_funct_1 (esk38_4 X1 X2 X3 X4) -> False) -> X5 = X6 -> (k9_xtuple_0 X5) = (k1_funct_1 X2 (esk36_3 X1 X2 X3)) -> (k10_xtuple_0 X5) = (k1_funct_1 X3 (esk36_3 X1 X2 X3)) -> v1_relat_1 X5 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X5 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v2_funct_1 X5 -> r2_hidden X4 X1 -> False)
  -> (forall X6 X5 X1 X4 X3 X2, (v1_funct_1 (esk38_4 X1 X2 X3 X4) -> False) -> X5 = X6 -> (k9_xtuple_0 X5) = (k1_funct_1 X2 (esk36_3 X1 X2 X3)) -> (k10_xtuple_0 X5) = (k1_funct_1 X3 (esk36_3 X1 X2 X3)) -> v1_relat_1 X5 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X5 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v2_funct_1 X5 -> r2_hidden X4 X1 -> False)
  -> (forall X6 X5 X1 X4 X3 X2, (v1_relat_1 (esk38_4 X1 X2 X3 X4) -> False) -> X5 = X6 -> (k9_xtuple_0 X5) = (k1_funct_1 X2 (esk36_3 X1 X2 X3)) -> (k10_xtuple_0 X5) = (k1_funct_1 X3 (esk36_3 X1 X2 X3)) -> v1_relat_1 X5 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X5 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v2_funct_1 X5 -> r2_hidden X4 X1 -> False)
  -> (forall X6 X5 X1 X4 X3 X2, ((k1_funct_1 (esk37_3 X1 X2 X3) X4) = (esk38_4 X1 X2 X3 X4) -> False) -> X5 = X6 -> (k9_xtuple_0 X5) = (k1_funct_1 X2 (esk36_3 X1 X2 X3)) -> (k10_xtuple_0 X5) = (k1_funct_1 X3 (esk36_3 X1 X2 X3)) -> v1_relat_1 X5 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X5 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v2_funct_1 X5 -> r2_hidden X4 X1 -> False)
  -> (forall X4 X2 X3 X1, ((k10_xtuple_0 (esk38_4 X1 X2 X3 X4)) = (k1_funct_1 X3 X4) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X4 X1 -> False)
  -> (forall X4 X2 X3 X1, ((k9_xtuple_0 (esk38_4 X1 X2 X3 X4)) = (k1_funct_1 X2 X4) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X4 X1 -> False)
  -> (forall X4 X1 X3 X2, ((k1_funct_1 (esk10_3 X2 X3 X4) X1) = (k1_binop_1 (k2_funct_5 X2) X1 (k1_funct_1 X4 X1)) -> False) -> X3 = (k7_funct_6 X2) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X4 (k4_card_3 (k2_funct_6 X2)) -> r2_hidden X1 (k9_xtuple_0 (esk10_3 X2 X3 X4)) -> False)
  -> (forall X4 X2 X3 X1, (v2_funct_1 (esk38_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X4 X1 -> False)
  -> (forall X4 X2 X3 X1, (v1_funct_1 (esk38_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X4 X1 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (esk38_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X4 X1 -> False)
  -> (forall X5 X4 X3 X2 X1, ((k9_xtuple_0 (esk37_3 X1 X2 X3)) = X1 -> False) -> X4 = X5 -> (k9_xtuple_0 X4) = (k1_funct_1 X2 (esk36_3 X1 X2 X3)) -> (k10_xtuple_0 X4) = (k1_funct_1 X3 (esk36_3 X1 X2 X3)) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v2_funct_1 X4 -> False)
  -> (forall X5 X4 X1 X2 X3, (v1_funct_1 (esk37_3 X1 X2 X3) -> False) -> X4 = X5 -> (k9_xtuple_0 X4) = (k1_funct_1 X2 (esk36_3 X1 X2 X3)) -> (k10_xtuple_0 X4) = (k1_funct_1 X3 (esk36_3 X1 X2 X3)) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v2_funct_1 X4 -> False)
  -> (forall X5 X4 X1 X2 X3, (v1_relat_1 (esk37_3 X1 X2 X3) -> False) -> X4 = X5 -> (k9_xtuple_0 X4) = (k1_funct_1 X2 (esk36_3 X1 X2 X3)) -> (k10_xtuple_0 X4) = (k1_funct_1 X3 (esk36_3 X1 X2 X3)) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v2_funct_1 X4 -> False)
  -> (forall X4 X2 X3 X1, ((k1_funct_1 (esk37_3 X1 X2 X3) X4) = (esk38_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X4 X1 -> False)
  -> (forall X3 X2 X1, (X2 = (k7_funct_6 X1) -> False) -> (r2_hidden (esk12_3 X1 X2 X3) (k9_xtuple_0 X3) -> False) -> (k9_xtuple_0 X2) = (k4_card_3 (k2_funct_6 X1)) -> (k1_funct_1 X2 (esk11_2 X1 X2)) = X3 -> (k9_xtuple_0 X3) = (k8_relat_1 X1 (k1_funct_6 (k10_xtuple_0 X1))) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (X1 = (k3_funct_6 X2) -> False) -> (k9_xtuple_0 X1) = (k8_relat_1 X2 (k1_funct_6 (k10_xtuple_0 X2))) -> (k1_funct_1 X1 (esk8_2 X2 X1)) = (k10_xtuple_0 (k1_funct_1 X2 (esk8_2 X2 X1))) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (X1 = (k2_funct_6 X2) -> False) -> (k9_xtuple_0 X1) = (k8_relat_1 X2 (k1_funct_6 (k10_xtuple_0 X2))) -> (k1_funct_1 X1 (esk4_2 X2 X1)) = (k9_xtuple_0 (k1_funct_1 X2 (esk4_2 X2 X1))) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2 X3, ((k9_xtuple_0 (esk37_3 X1 X2 X3)) = X1 -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2 X3, (v1_funct_1 (esk37_3 X1 X2 X3) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> False)
  -> (forall X1 X2 X3, (v1_relat_1 (esk37_3 X1 X2 X3) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk10_3 X1 X2 X3)) = (k8_relat_1 X1 (k1_funct_6 (k10_xtuple_0 X1))) -> False) -> X2 = (k7_funct_6 X1) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k4_card_3 (k2_funct_6 X1)) -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (esk10_3 X1 X2 X3) -> False) -> X2 = (k7_funct_6 X1) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k4_card_3 (k2_funct_6 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (esk10_3 X1 X2 X3) -> False) -> X2 = (k7_funct_6 X1) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k4_card_3 (k2_funct_6 X1)) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X3 X1) = (k10_xtuple_0 (k1_funct_1 X2 X1)) -> False) -> X3 = (k3_funct_6 X2) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k8_relat_1 X2 (k1_funct_6 (k10_xtuple_0 X2))) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X3 X1) = (k9_xtuple_0 (k1_funct_1 X2 X1)) -> False) -> X3 = (k2_funct_6 X2) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k8_relat_1 X2 (k1_funct_6 (k10_xtuple_0 X2))) -> False)
  -> (forall X1 X2, (X2 = (k3_funct_6 X1) -> False) -> (r2_hidden (esk8_2 X1 X2) (k8_relat_1 X1 (k1_funct_6 (k10_xtuple_0 X1))) -> False) -> (k9_xtuple_0 X2) = (k8_relat_1 X1 (k1_funct_6 (k10_xtuple_0 X1))) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k2_funct_6 X1) -> False) -> (r2_hidden (esk4_2 X1 X2) (k8_relat_1 X1 (k1_funct_6 (k10_xtuple_0 X1))) -> False) -> (k9_xtuple_0 X2) = (k8_relat_1 X1 (k1_funct_6 (k10_xtuple_0 X1))) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk5_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X2 X1 X3, ((esk10_3 X3 X1 X2) = (k1_funct_1 X1 X2) -> False) -> X1 = (k7_funct_6 X3) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X2 (k4_card_3 (k2_funct_6 X3)) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> (k1_funct_1 X1 (esk39_2 X1 X2)) = (k1_funct_1 X2 (esk39_2 X1 X2)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk5_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk6_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k9_xtuple_0 (k3_funct_6 X2)) -> False) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k9_xtuple_0 (k2_funct_6 X2)) -> False) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X2 = (k7_funct_6 X1) -> False) -> (r2_hidden (esk11_2 X1 X2) (k4_card_3 (k2_funct_6 X1)) -> False) -> (k9_xtuple_0 X2) = (k4_card_3 (k2_funct_6 X1)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk7_2 X1 X2)) = (esk6_2 X1 X2) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2 X3, ((k1_funct_1 (k3_funct_6 X1) X2) = (k10_xtuple_0 X3) -> False) -> X3 = (k1_funct_1 X1 X2) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> r2_hidden X2 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2 X3, ((k1_funct_1 (k2_funct_6 X1) X2) = (k9_xtuple_0 X3) -> False) -> X3 = (k1_funct_1 X1 X2) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> r2_hidden X2 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (esk7_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v2_funct_1 X2 -> False) -> (r2_hidden k1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 (k7_funct_6 X1) -> r2_hidden X2 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk39_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k7_funct_6 X1) -> False) -> (v1_funct_1 (esk11_2 X1 X2) -> False) -> (k9_xtuple_0 X2) = (k4_card_3 (k2_funct_6 X1)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k7_funct_6 X1) -> False) -> (v1_relat_1 (esk11_2 X1 X2) -> False) -> (k9_xtuple_0 X2) = (k4_card_3 (k2_funct_6 X1)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1, (r2_wellord2 (k1_funct_1 esk2_0 X1) (k1_funct_1 esk3_0 X1) -> False) -> r2_hidden X1 esk1_0 -> False)
  -> (forall X1 X2, ((k9_xtuple_0 X1) = (k8_relat_1 X2 (k1_funct_6 (k10_xtuple_0 X2))) -> False) -> X1 = (k3_funct_6 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, ((k9_xtuple_0 X1) = (k8_relat_1 X2 (k1_funct_6 (k10_xtuple_0 X2))) -> False) -> X1 = (k2_funct_6 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 (k7_funct_6 X1) -> False) -> (r2_hidden k1_xboole_0 (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk40_1 X1) (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 (k7_funct_6 X1) -> False) -> (r2_hidden k1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 (esk40_1 X1) -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (esk40_1 X1) -> False) -> (v2_funct_1 (k7_funct_6 X1) -> False) -> (r2_hidden k1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (esk40_1 X1) -> False) -> (v2_funct_1 (k7_funct_6 X1) -> False) -> (r2_hidden k1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, ((k10_xtuple_0 (esk9_2 X1 X2)) = X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk9_2 X1 X2)) = X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v2_funct_1 (esk9_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 (esk9_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (esk9_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1 X2 X3, (r2_wellord2 X2 X3 -> False) -> (k9_xtuple_0 X1) = X2 -> (k10_xtuple_0 X1) = X3 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k8_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, ((k9_xtuple_0 X1) = (k4_card_3 (k2_funct_6 X2)) -> False) -> X1 = (k7_funct_6 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1, ((k4_card_3 X1) = k1_xboole_0 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden k1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v5_finset_1 (k2_tarski X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k8_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k8_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (r2_hidden k1_xboole_0 (k10_xtuple_0 X1) -> False) -> (k4_card_3 X1) = k1_xboole_0 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, ((k1_funct_6 X1) = X1 -> False) -> v1_relat_1 (esk14_1 X1) -> v1_funct_1 (esk14_1 X1) -> False)
  -> (forall X2 X1, (r2_tarski X1 X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> r2_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X2 X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, ((k4_card_3 (k3_funct_6 X1)) = (k10_xtuple_0 (k7_funct_6 X1)) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_setfam_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1, ((k8_relat_1 X1 (k10_xtuple_0 X1)) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k1_funct_6 X1) = X1 -> False) -> (r2_hidden (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_5 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k7_funct_6 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k3_funct_6 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_6 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_5 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k7_funct_6 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k3_funct_6 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_6 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_tarski X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (r2_wellord2 (k4_card_3 esk2_0) (k4_card_3 esk3_0) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v3_funct_1 esk31_0 -> False)
  -> (v1_xboole_0 esk35_0 -> False)
  -> (v1_xboole_0 esk34_0 -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk32_0 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (k2_tarski X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (r2_wellord2 X1 X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (k1_tarski X1) -> False) -> False)
  -> ((v1_xtuple_0 esk21_0 -> False) -> False)
  -> ((v2_finset_1 esk35_0 -> False) -> False)
  -> ((v4_funct_1 esk33_0 -> False) -> False)
  -> ((v7_ordinal1 esk32_0 -> False) -> False)
  -> ((v7_ordinal1 esk30_0 -> False) -> False)
  -> ((v5_finset_1 esk34_0 -> False) -> False)
  -> ((v2_relat_1 esk29_0 -> False) -> False)
  -> ((v2_relat_1 esk28_0 -> False) -> False)
  -> ((v2_relat_1 esk25_0 -> False) -> False)
  -> ((v3_funct_1 esk22_0 -> False) -> False)
  -> ((v2_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funcop_1 esk16_0 -> False) -> False)
  -> ((v2_ordinal1 esk24_0 -> False) -> False)
  -> ((v1_ordinal1 esk24_0 -> False) -> False)
  -> ((v3_ordinal1 esk24_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v1_finset_1 esk34_0 -> False) -> False)
  -> ((v1_finset_1 esk27_0 -> False) -> False)
  -> ((v1_finset_1 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk35_0 -> False) -> False)
  -> ((v1_funct_1 esk31_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk28_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk35_0 -> False) -> False)
  -> ((v1_relat_1 esk31_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk28_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk3_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> (((k10_xtuple_0 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (((k9_xtuple_0 esk3_0) = esk1_0 -> False) -> False)
  -> (((k9_xtuple_0 esk2_0) = esk1_0 -> False) -> False)
  -> (((k9_xtuple_0 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
