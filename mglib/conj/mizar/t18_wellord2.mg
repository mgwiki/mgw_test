(** $I sig/MizarPreamble.mgs **)

Theorem t18_wellord2:
 forall esk33_2:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall k1_xboole_0:set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall k1_wellord1:set -> set -> set,
 forall r1_wellord1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk6_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall esk14_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk1_0:set,
 forall esk39_2:set -> set -> set,
 forall v3_relat_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v1_setfam_1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk29_0:set,
 forall esk30_0:set,
 forall esk24_0:set,
 forall esk19_1:set -> set,
 forall esk28_0:set,
 forall esk26_0:set,
 forall esk23_0:set,
 forall o_0_0_xboole_0:set,
 forall esk21_0:set,
 forall esk20_0:set,
 forall esk25_0:set,
 forall esk38_1:set -> set,
 forall esk22_0:set,
 forall esk27_0:set,
 forall esk31_0:set,
 forall esk2_1:set -> set,
 forall v7_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall k8_relat_1:set -> set -> set,
 forall v4_funct_1:set -> prop,
 forall k10_relat_1:set -> set -> set,
 forall k6_subset_1:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall v2_relat_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall esk15_2:set -> set -> set,
 forall r8_relat_2:set -> set -> prop,
 forall r2_wellord1:set -> set -> prop,
 forall esk13_3:set -> set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall r4_relat_2:set -> set -> prop,
 forall esk3_2:set -> set -> set,
 forall r1_relat_2:set -> set -> prop,
 forall esk17_2:set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall r6_relat_2:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k2_tarski:set -> set -> set,
 forall esk34_2:set -> set -> set,
 forall k1_tarski:set -> set,
 forall v1_relat_1:set -> prop,
 forall esk35_2:set -> set -> set,
 forall esk36_3:set -> set -> set -> set,
 forall esk32_2:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall esk37_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
     (forall X4 X6 X5 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X3 X4) X6) (k1_tarski (esk34_2 X3 X4))) X4 -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X6 (esk32_2 X3 X4) -> r2_hidden X5 (esk35_2 X3 X4) -> r2_hidden (k2_tarski (k2_tarski X5 (esk36_3 X3 X4 X5)) (k1_tarski X5)) X4 -> False)
  -> (forall X4 X6 X5 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X3 X4) X6) (k1_tarski (esk33_2 X3 X4))) X4 -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X6 (esk32_2 X3 X4) -> r2_hidden X5 (esk35_2 X3 X4) -> r2_hidden (k2_tarski (k2_tarski X5 (esk36_3 X3 X4 X5)) (k1_tarski X5)) X4 -> False)
  -> (forall X4 X5 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk34_2 X3 X4) (esk32_2 X3 X4) -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X5 (esk35_2 X3 X4) -> r2_hidden (k2_tarski (k2_tarski X5 (esk36_3 X3 X4 X5)) (k1_tarski X5)) X4 -> False)
  -> (forall X4 X5 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk33_2 X3 X4) (esk32_2 X3 X4) -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X5 (esk35_2 X3 X4) -> r2_hidden (k2_tarski (k2_tarski X5 (esk36_3 X3 X4 X5)) (k1_tarski X5)) X4 -> False)
  -> (forall X4 X1 X2 X5 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> (esk34_2 X3 X4) = (esk33_2 X3 X4) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X5 (esk35_2 X3 X4) -> r2_hidden (k2_tarski (k2_tarski X5 (esk36_3 X3 X4 X5)) (k1_tarski X5)) X4 -> False)
  -> (forall X4 X5 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk32_2 X3 X4) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X5 (esk35_2 X3 X4) -> r2_hidden (k2_tarski (k2_tarski X5 (esk36_3 X3 X4 X5)) (k1_tarski X5)) X4 -> False)
  -> (forall X3 X2 X4 X5 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X5) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X5 (esk32_2 X1 X2) -> r2_hidden X4 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X4 (esk36_3 X1 X2 X4)) (k1_tarski X4)) X2 -> False)
  -> (forall X3 X2 X4 X5 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X5) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X5 (esk32_2 X1 X2) -> r2_hidden X4 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X4 (esk36_3 X1 X2 X4)) (k1_tarski X4)) X2 -> False)
  -> (forall X4 X5 X1 X2 X6 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk36_3 X3 X4 X5) (esk35_2 X3 X4) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X3 X4) X6) (k1_tarski (esk34_2 X3 X4))) X4 -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X6 (esk32_2 X3 X4) -> r2_hidden X5 (esk35_2 X3 X4) -> False)
  -> (forall X4 X5 X1 X2 X6 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk36_3 X3 X4 X5) (esk35_2 X3 X4) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X3 X4) X6) (k1_tarski (esk33_2 X3 X4))) X4 -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X6 (esk32_2 X3 X4) -> r2_hidden X5 (esk35_2 X3 X4) -> False)
  -> (forall X3 X4 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X4) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X3 X4 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X4) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X4) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X4) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X4) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X4) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X4 X1 X2 X5 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk35_2 X3 X4) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X3 X4) X5) (k1_tarski (esk34_2 X3 X4))) X4 -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X5 (esk32_2 X3 X4) -> False)
  -> (forall X4 X1 X2 X5 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk35_2 X3 X4) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X3 X4) X5) (k1_tarski (esk33_2 X3 X4))) X4 -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X5 (esk32_2 X3 X4) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X4 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X4 (esk36_3 X1 X2 X4)) (k1_tarski X4)) X2 -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X4 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X4 (esk36_3 X1 X2 X4)) (k1_tarski X4)) X2 -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X4 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X4 (esk36_3 X1 X2 X4)) (k1_tarski X4)) X2 -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X4 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X4 (esk36_3 X1 X2 X4)) (k1_tarski X4)) X2 -> False)
  -> (forall X4 X1 X2 X5 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk34_2 X3 X4) (esk32_2 X3 X4) -> False) -> (r2_hidden (esk36_3 X3 X4 X5) (esk35_2 X3 X4) -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X5 (esk35_2 X3 X4) -> False)
  -> (forall X4 X1 X2 X5 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk33_2 X3 X4) (esk32_2 X3 X4) -> False) -> (r2_hidden (esk36_3 X3 X4 X5) (esk35_2 X3 X4) -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X5 (esk35_2 X3 X4) -> False)
  -> (forall X4 X5 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk36_3 X3 X4 X5) (esk35_2 X3 X4) -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> (esk34_2 X3 X4) = (esk33_2 X3 X4) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X5 (esk35_2 X3 X4) -> False)
  -> (forall X4 X1 X2 X5 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk32_2 X3 X4) X3 -> False) -> (r2_hidden (esk36_3 X3 X4 X5) (esk35_2 X3 X4) -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> r2_hidden X5 (esk35_2 X3 X4) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> r2_hidden (k2_tarski (k2_tarski X3 (esk36_3 X1 X2 X3)) (k1_tarski X3)) X2 -> False)
  -> (forall X4 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk35_2 X3 X4) X3 -> False) -> (r2_hidden (esk34_2 X3 X4) (esk32_2 X3 X4) -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X4 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk35_2 X3 X4) X3 -> False) -> (r2_hidden (esk33_2 X3 X4) (esk32_2 X3 X4) -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X4 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk35_2 X3 X4) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> (esk34_2 X3 X4) = (esk33_2 X3 X4) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X4 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden (esk32_2 X3 X4) X3 -> False) -> (r2_hidden (esk35_2 X3 X4) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (k1_funct_1 (esk37_2 X3 X4) X2) X1) (k1_tarski (k1_funct_1 (esk37_2 X3 X4) X2))) X4 -> False) -> v1_relat_1 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X5 X4 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (r2_hidden (esk36_3 X1 X2 X4) (esk35_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X5) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X5 (esk32_2 X1 X2) -> r2_hidden X4 (esk35_2 X1 X2) -> False)
  -> (forall X3 X2 X5 X4 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (r2_hidden (esk36_3 X1 X2 X4) (esk35_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X5) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X5 (esk32_2 X1 X2) -> r2_hidden X4 (esk35_2 X1 X2) -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk18_2 X1 X2) (esk17_2 X1 X2)) (k1_tarski (esk18_2 X1 X2))) X1 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk17_2 X1 X2) (esk18_2 X1 X2)) (k1_tarski (esk17_2 X1 X2))) X1 -> False)
  -> (forall X2 X1, (r1_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_hidden (k2_tarski (k2_tarski (esk3_2 X1 X2) (esk3_2 X1 X2)) (k1_tarski (esk3_2 X1 X2))) X1 -> False)
  -> (forall X4 X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X4) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X4 X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X4) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X4) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X4) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X4) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X4) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X4 (esk32_2 X1 X2) -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk16_3 X1 X2 X3) X3 -> r2_hidden (esk16_3 X1 X2 X3) X2 -> r2_hidden (esk16_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X4) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X4 (esk32_2 X1 X2) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X4) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X4 (esk32_2 X1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X3) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk32_2 X1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X3) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk32_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X3) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk32_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X3) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk32_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk34_2 X1 X2) X3) (k1_tarski (esk34_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk32_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk33_2 X1 X2) X3) (k1_tarski (esk33_2 X1 X2))) X2 -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk32_2 X1 X2) -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk12_2 X1 X2) (esk11_2 X1 X2)) (k1_tarski (esk12_2 X1 X2))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk11_2 X1 X2) (esk12_2 X1 X2)) (k1_tarski (esk11_2 X1 X2))) X1 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_relat_1 X1 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> r4_relat_2 X1 X2 -> r2_hidden (k2_tarski (k2_tarski X4 X3) (k1_tarski X4)) X1 -> r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1 -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (r2_hidden (esk36_3 X1 X2 X4) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X4 (esk35_2 X1 X2) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (r2_hidden (esk36_3 X1 X2 X4) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X4 (esk35_2 X1 X2) -> False)
  -> (forall X3 X2 X4 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (r2_hidden (esk36_3 X1 X2 X4) (esk35_2 X1 X2) -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X4 (esk35_2 X1 X2) -> False)
  -> (forall X2 X4 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (r2_hidden (esk36_3 X1 X2 X4) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> r2_hidden X4 (esk35_2 X1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (r1_xboole_0 (k1_wellord1 X1 (esk9_3 X1 X2 X3)) X3 -> False) -> v1_relat_1 X1 -> r1_tarski X3 X2 -> r1_wellord1 X1 X2 -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> (r2_hidden (esk36_3 X1 X2 X3) (esk35_2 X1 X2) -> False) -> v1_relat_1 X2 -> r2_hidden X3 (esk35_2 X1 X2) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (r2_hidden (k2_tarski (k2_tarski X4 X3) (k1_tarski X4)) X1 -> False) -> (r2_hidden (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) X1 -> False) -> v1_relat_1 X1 -> r2_hidden X4 X2 -> r2_hidden X3 X2 -> r6_relat_2 X1 X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X3 X1 X2, (X1 = X2 -> False) -> (r2_hidden X1 (k1_wellord1 X3 X2) -> False) -> v1_relat_1 X3 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (k1_funct_1 (esk37_2 X1 X2) X3) X3 -> False) -> v1_relat_1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X1 X2 X3, (r1_wellord1 X2 X3 -> False) -> v1_relat_1 X2 -> r2_hidden X1 (esk10_2 X2 X3) -> r1_xboole_0 (k1_wellord1 X2 X1) (esk10_2 X2 X3) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> v1_relat_1 X1 -> r1_tarski X3 X2 -> r1_wellord1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) X3 -> False) -> v1_relat_1 X3 -> r2_hidden X1 (k1_wellord1 X3 X2) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk5_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk5_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk6_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden (k2_tarski (k2_tarski X3 X3) (k1_tarski X3)) X1 -> False) -> v1_relat_1 X1 -> r2_hidden X3 X2 -> r1_relat_2 X1 X2 -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk14_2 X1 X2) X3 -> r2_hidden (esk14_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk13_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk13_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (esk34_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (r2_hidden (esk33_2 X1 X2) (esk32_2 X1 X2) -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (r2_wellord1 X1 X2 -> False) -> v1_relat_1 X1 -> r1_relat_2 X1 X2 -> r1_wellord1 X1 X2 -> r4_relat_2 X1 X2 -> r8_relat_2 X1 X2 -> r6_relat_2 X1 X2 -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> (esk34_2 X1 X2) = (esk33_2 X1 X2) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk37_2 X1 X2)) = X1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk37_2 X1 X2) -> False) -> (r2_hidden (esk32_2 X1 X2) X1 -> False) -> (r2_hidden (esk35_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk7_2 X1 X2)) = (esk6_2 X1 X2) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> (r2_hidden (esk14_2 X1 X2) (esk15_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (esk7_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk4_2 X1 X2) = X1 -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk14_2 X1 X2) X2 -> False) -> (r2_hidden (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk8_2 X1 X2) X2 -> False)
  -> (forall X3 X1 X2, X1 = X2 -> v1_relat_1 X3 -> r2_hidden X1 (k1_wellord1 X3 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X2 X1, ((k6_subset_1 (k10_relat_1 X1 X2) (k1_tarski X2)) = (k1_wellord1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> (esk18_2 X1 X2) = (esk17_2 X1 X2) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> (esk12_2 X1 X2) = (esk11_2 X1 X2) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> (r2_hidden (esk18_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> (r2_hidden (esk17_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> (r2_hidden (esk12_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_wellord1 X1 X2 -> False) -> (r1_tarski (esk10_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_relat_2 X1 X2 -> False) -> (r2_hidden (esk3_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk4_2 X1 X2) = X1 -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> (r1_xboole_0 X1 X2 -> False) -> r2_hidden X2 esk1_0 -> r2_hidden X1 esk1_0 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk8_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk39_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk39_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k8_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k8_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r6_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (r8_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (r4_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (r1_wellord1 X1 X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (r1_relat_2 X1 X2 -> False) -> v1_relat_1 X1 -> r2_wellord1 X1 X2 -> False)
  -> (forall X2 X1, (r1_wellord1 X1 X2 -> False) -> (esk10_2 X1 X2) = k1_xboole_0 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, ((k8_relat_1 X1 (k1_tarski X2)) = (k10_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k6_subset_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_setfam_1 (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, X1 = k1_xboole_0 -> r2_hidden X1 esk1_0 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v3_ordinal1 (k3_tarski X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (k3_xboole_0 X1 (esk2_1 X1)) = (k1_tarski X2) -> False)
  -> (v3_funct_1 esk29_0 -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk30_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (r2_wellord1 (esk38_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (r2_hidden (esk2_1 X1) esk1_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk38_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk31_0 -> False) -> False)
  -> ((v7_ordinal1 esk30_0 -> False) -> False)
  -> ((v7_ordinal1 esk28_0 -> False) -> False)
  -> ((v2_relat_1 esk27_0 -> False) -> False)
  -> ((v2_relat_1 esk26_0 -> False) -> False)
  -> ((v2_relat_1 esk25_0 -> False) -> False)
  -> ((v2_funct_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v2_ordinal1 esk24_0 -> False) -> False)
  -> ((v1_ordinal1 esk24_0 -> False) -> False)
  -> ((v3_ordinal1 esk24_0 -> False) -> False)
  -> ((v3_ordinal1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk26_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
