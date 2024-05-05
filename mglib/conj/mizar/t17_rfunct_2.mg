(** $I sig/MizarPreamble.mgs **)

Theorem t17_rfunct_2:
 forall esk7_4:set -> set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k7_relat_1:set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall esk3_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk5_2:set -> set -> set,
 forall v3_ordinal1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall k4_numbers:set,
 forall v1_rat_1:set -> prop,
 forall v4_membered:set -> prop,
 forall v1_valued_0:set -> prop,
 forall v3_valued_0:set -> prop,
 forall v4_valued_0:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v3_membered:set -> prop,
 forall v1_membered:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk21_0:set,
 forall esk27_0:set,
 forall esk20_0:set,
 forall esk18_0:set,
 forall esk12_0:set,
 forall esk10_1:set -> set,
 forall esk25_0:set,
 forall esk15_0:set,
 forall esk11_0:set,
 forall esk17_0:set,
 forall esk24_0:set,
 forall o_0_0_xboole_0:set,
 forall esk13_0:set,
 forall esk14_0:set,
 forall esk23_1:set -> set,
 forall esk16_0:set,
 forall esk19_0:set,
 forall esk22_0:set,
 forall esk28_0:set,
 forall esk26_0:set,
 forall v1_finset_1:set -> prop,
 forall k1_xboole_0:set,
 forall v7_membered:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v2_membered:set -> prop,
 forall v6_membered:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v5_membered:set -> prop,
 forall v1_int_1:set -> prop,
 forall k3_numbers:set,
 forall v4_funct_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v5_valued_0:set -> prop,
 forall v6_valued_0:set -> prop,
 forall v2_valued_0:set -> prop,
 forall v7_valued_0:set -> prop,
 forall v8_valued_0:set -> prop,
 forall v2_funct_1:set -> prop,
 forall k2_funct_1:set -> set,
 forall k3_relat_1:set -> set -> set,
 forall esk29_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall esk30_2:set -> set -> set,
 forall k5_relat_1:set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
     (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X2 -> r2_hidden (esk6_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X4 X1, (r2_hidden (esk7_4 X1 X2 X3 X4) (k9_xtuple_0 X1) -> False) -> X3 = (k7_relat_1 X1 X2) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X4 X3 -> False)
  -> (forall X3 X4 X1 X2, ((k1_funct_1 X2 (esk7_4 X2 X3 X4 X1)) = X1 -> False) -> X4 = (k7_relat_1 X2 X3) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X4 -> False)
  -> (forall X2 X3 X4 X1, (r2_hidden (esk7_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k7_relat_1 X1 X2) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X4 X3 -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k7_relat_1 X1 X2) -> False) -> (esk8_3 X1 X2 X3) = (k1_funct_1 X1 X4) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X4 X2 -> r2_hidden X4 (k9_xtuple_0 X1) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X2 X1, (X3 = (k7_relat_1 X1 X2) -> False) -> ((k1_funct_1 X1 (esk9_3 X1 X2 X3)) = (esk8_3 X1 X2 X3) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (X3 = (k7_relat_1 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k7_relat_1 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X2 X3 X1, ((k1_funct_1 (k5_relat_1 X1 X3) X2) = (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X2 (k9_xtuple_0 (k5_relat_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk3_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> (k1_funct_1 X1 (esk30_2 X1 X2)) = (k1_funct_1 X2 (esk30_2 X1 X2)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk3_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk4_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4 X5, (r2_hidden X4 X5 -> False) -> X5 = (k7_relat_1 X2 X3) -> X4 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> r2_hidden (esk29_2 X1 X2) X2 -> r2_hidden (esk29_2 X1 X2) X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk5_2 X1 X2)) = (esk4_2 X1 X2) -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, ((k1_funct_1 (k3_relat_1 X2 (k2_funct_1 X2)) X1) = X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> (r2_hidden (esk5_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, ((k1_funct_1 (k2_funct_1 X2) (k1_funct_1 X2 X1)) = X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 (k5_relat_1 X1 X3) X2) = (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X2 X3 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk30_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v8_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v7_valued_0 X1 -> v8_valued_0 X2 -> False)
  -> (forall X1 X2, (v8_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v7_valued_0 X2 -> v8_valued_0 X1 -> False)
  -> (forall X1 X2, (v7_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v8_valued_0 X2 -> v8_valued_0 X1 -> False)
  -> (forall X1 X2, (v7_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v7_valued_0 X2 -> v7_valued_0 X1 -> False)
  -> (forall X1 X2, (v6_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v5_valued_0 X1 -> v6_valued_0 X2 -> False)
  -> (forall X1 X2, (v6_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v5_valued_0 X2 -> v6_valued_0 X1 -> False)
  -> (forall X1 X2, (v5_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v6_valued_0 X2 -> v6_valued_0 X1 -> False)
  -> (forall X1 X2, (v5_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v5_valued_0 X2 -> v5_valued_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v8_valued_0 X2 -> v8_valued_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v7_valued_0 X1 -> v8_valued_0 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v7_valued_0 X2 -> v8_valued_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v7_valued_0 X2 -> v7_valued_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v6_valued_0 X2 -> v6_valued_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v5_valued_0 X1 -> v6_valued_0 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v5_valued_0 X2 -> v6_valued_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_valued_0 X2 -> v2_valued_0 X1 -> v5_valued_0 X2 -> v5_valued_0 X1 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk29_2 X1 X2) X2 -> False) -> (r2_hidden (esk29_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v5_relat_1 (k5_relat_1 X1 X2) (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_ordinal1 X2 -> v5_ordinal1 X1 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v2_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v5_relat_1 (k3_relat_1 X1 X2) k3_numbers -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 k3_numbers -> False)
  -> (forall X1 X2, (v5_relat_1 (k3_relat_1 X1 X2) k4_numbers -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 k4_numbers -> False)
  -> (forall X2 X1, (v5_relat_1 (k3_xboole_0 X1 X2) k3_numbers -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X2 X1, (v5_relat_1 (k3_xboole_0 X1 X2) k4_numbers -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X2 X1, (v5_relat_1 (k5_relat_1 X1 X2) k3_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X2 X1, (v5_relat_1 (k5_relat_1 X1 X2) k4_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X2 X1, (v1_int_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X2 X1, (v1_rat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 k3_numbers -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 k4_numbers -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, (v5_ordinal1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_ordinal1 X2 -> v5_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_ordinal1 X2 -> v5_ordinal1 X1 -> False)
  -> (forall X2 X1, (v5_membered (k7_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X2 X1, (v4_membered (k7_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (k5_relat_1 X1 X2)) = (k3_xboole_0 (k9_xtuple_0 X1) X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X2 -> False)
  -> (forall X2 X1, (v1_valued_0 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X1 -> False)
  -> (forall X1 X2, (v3_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v3_valued_0 X2 -> False)
  -> (forall X2 X1, (v3_valued_0 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X1 X2, (v2_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_valued_0 X2 -> False)
  -> (forall X2 X1, (v2_valued_0 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X1 X2, (v4_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_valued_0 X2 -> False)
  -> (forall X2 X1, (v4_valued_0 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_xxreal_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_valued_0 X1 -> False)
  -> (forall X2 X1, (v2_funct_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v3_valued_0 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_valued_0 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_valued_0 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_valued_0 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_valued_0 X1 -> False)
  -> (forall X2 X1, (v3_valued_0 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, (v2_valued_0 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X2 X1, (v4_valued_0 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X2 X1, (v6_membered (k7_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X2 X1, (v3_membered (k7_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, (v2_membered (k7_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_membered (k7_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v5_relat_1 X1 k3_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X1, (v5_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X1, (v4_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X2 X1, (v6_membered (k3_xboole_0 X1 X2) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (v6_membered (k3_xboole_0 X2 X1) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (v5_membered (k3_xboole_0 X1 X2) -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, (v5_membered (k3_xboole_0 X2 X1) -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k3_xboole_0 X1 X2) -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k3_xboole_0 X2 X1) -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v3_membered (k3_xboole_0 X1 X2) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v3_membered (k3_xboole_0 X2 X1) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k3_xboole_0 X1 X2) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k3_xboole_0 X2 X1) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k3_xboole_0 X1 X2) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k3_xboole_0 X2 X1) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k5_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k10_xtuple_0 (k2_funct_1 X1)) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, ((k9_xtuple_0 (k2_funct_1 X1)) = (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v8_valued_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_valued_0 X1 -> v6_valued_0 X1 -> False)
  -> (forall X1, (v7_valued_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_valued_0 X1 -> v5_valued_0 X1 -> False)
  -> (forall X1, (v6_valued_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X1, (v5_valued_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1, (v2_funct_1 (k2_funct_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v5_relat_1 X1 k3_numbers -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v5_relat_1 X1 k4_numbers -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v3_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X1, (v2_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X1, (v1_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_valued_0 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_valued_0 X1 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v2_valued_0 X1 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X1, (v4_valued_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k5_relat_1 (k2_funct_1 esk2_0) (k7_relat_1 esk2_0 esk1_0)) = (k2_funct_1 (k5_relat_1 esk2_0 esk1_0)) -> False)
  -> (v1_finset_1 k3_numbers -> False)
  -> (v1_finset_1 k4_numbers -> False)
  -> (v3_funct_1 esk26_0 -> False)
  -> (v1_zfmisc_1 esk21_0 -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 k3_numbers -> False)
  -> (v1_xboole_0 k4_numbers -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((v5_relat_1 esk20_0 k3_numbers -> False) -> False)
  -> ((v5_relat_1 esk20_0 k4_numbers -> False) -> False)
  -> (forall X1, (v5_ordinal1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk23_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk28_0 -> False) -> False)
  -> ((v3_funct_1 esk20_0 -> False) -> False)
  -> ((v7_membered esk22_0 -> False) -> False)
  -> ((v7_membered k3_numbers -> False) -> False)
  -> ((v7_membered k4_numbers -> False) -> False)
  -> ((v1_zfmisc_1 esk16_0 -> False) -> False)
  -> ((v4_valued_0 esk20_0 -> False) -> False)
  -> ((v4_valued_0 esk14_0 -> False) -> False)
  -> ((v2_ordinal1 esk19_0 -> False) -> False)
  -> ((v1_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 esk25_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v7_ordinal1 esk27_0 -> False) -> False)
  -> ((v7_ordinal1 esk24_0 -> False) -> False)
  -> ((v6_membered esk22_0 -> False) -> False)
  -> ((v6_membered esk18_0 -> False) -> False)
  -> ((v6_membered esk12_0 -> False) -> False)
  -> ((v5_membered k4_numbers -> False) -> False)
  -> ((v4_membered k3_numbers -> False) -> False)
  -> ((v1_xreal_0 esk25_0 -> False) -> False)
  -> ((v1_xreal_0 esk15_0 -> False) -> False)
  -> ((v1_xxreal_0 esk25_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk25_0 -> False) -> False)
  -> ((v2_funct_1 esk17_0 -> False) -> False)
  -> ((v2_funct_1 esk2_0 -> False) -> False)
  -> ((v1_funct_1 esk26_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk11_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
