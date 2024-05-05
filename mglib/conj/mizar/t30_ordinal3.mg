(** $I sig/MizarPreamble.mgs **)

Theorem t30_ordinal3:
 forall r2_hidden:set -> set -> prop,
 forall esk19_3:set -> set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall r1_ordinal1:set -> set -> prop,
 forall esk21_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk16_0:set,
 forall esk12_0:set,
 forall esk8_1:set -> set,
 forall esk10_0:set,
 forall o_0_0_xboole_0:set,
 forall esk9_0:set,
 forall esk11_0:set,
 forall esk15_0:set,
 forall esk13_0:set,
 forall esk14_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall k3_ordinal2:set -> set,
 forall v7_ordinal1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall esk7_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall esk20_3:set -> set -> set -> set,
 forall k4_ordinal2:set -> set,
 forall esk22_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_ordinal2:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall v4_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall v3_ordinal1:set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk17_2:set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall k10_ordinal2:set -> set -> set,
     (forall X3 X2 X1, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> (k10_ordinal2 (k10_ordinal2 X1 X2) (esk18_2 X1 X2)) = (k10_ordinal2 X1 (k10_ordinal2 X2 (esk18_2 X1 X2))) -> (k10_ordinal2 (k10_ordinal2 X1 X2) (k2_xboole_0 (esk17_2 X1 X2) (k1_tarski (esk17_2 X1 X2)))) = (k10_ordinal2 X1 (k10_ordinal2 X2 (k2_xboole_0 (esk17_2 X1 X2) (k1_tarski (esk17_2 X1 X2))))) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X4 X3, ((k10_ordinal2 (k10_ordinal2 X2 X3) X4) = (k10_ordinal2 X2 (k10_ordinal2 X3 X4)) -> False) -> ((k10_ordinal2 (k10_ordinal2 X2 X3) X1) = (k10_ordinal2 X2 (k10_ordinal2 X3 X1)) -> False) -> (k10_ordinal2 (k10_ordinal2 X2 X3) k1_xboole_0) = (k10_ordinal2 X2 (k10_ordinal2 X3 k1_xboole_0)) -> (k10_ordinal2 (k10_ordinal2 X2 X3) (k2_xboole_0 (esk17_2 X2 X3) (k1_tarski (esk17_2 X2 X3)))) = (k10_ordinal2 X2 (k10_ordinal2 X3 (k2_xboole_0 (esk17_2 X2 X3) (k1_tarski (esk17_2 X2 X3))))) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (esk18_2 X2 X3) -> False)
  -> (forall X3 X2 X1, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> (v4_ordinal1 (esk18_2 X1 X2) -> False) -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> (k10_ordinal2 (k10_ordinal2 X1 X2) (k2_xboole_0 (esk17_2 X1 X2) (k1_tarski (esk17_2 X1 X2)))) = (k10_ordinal2 X1 (k10_ordinal2 X2 (k2_xboole_0 (esk17_2 X1 X2) (k1_tarski (esk17_2 X1 X2))))) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> (v3_ordinal1 (esk18_2 X1 X2) -> False) -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> (k10_ordinal2 (k10_ordinal2 X1 X2) (k2_xboole_0 (esk17_2 X1 X2) (k1_tarski (esk17_2 X1 X2)))) = (k10_ordinal2 X1 (k10_ordinal2 X2 (k2_xboole_0 (esk17_2 X1 X2) (k1_tarski (esk17_2 X1 X2))))) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> (esk18_2 X1 X2) = k1_xboole_0 -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> (k10_ordinal2 (k10_ordinal2 X1 X2) (k2_xboole_0 (esk17_2 X1 X2) (k1_tarski (esk17_2 X1 X2)))) = (k10_ordinal2 X1 (k10_ordinal2 X2 (k2_xboole_0 (esk17_2 X1 X2) (k1_tarski (esk17_2 X1 X2))))) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X1 X2, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> ((k10_ordinal2 (k10_ordinal2 X1 X2) (esk17_2 X1 X2)) = (k10_ordinal2 X1 (k10_ordinal2 X2 (esk17_2 X1 X2))) -> False) -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> (k10_ordinal2 (k10_ordinal2 X1 X2) (esk18_2 X1 X2)) = (k10_ordinal2 X1 (k10_ordinal2 X2 (esk18_2 X1 X2))) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X4 X3, ((k10_ordinal2 (k10_ordinal2 X2 X3) X4) = (k10_ordinal2 X2 (k10_ordinal2 X3 X4)) -> False) -> ((k10_ordinal2 (k10_ordinal2 X2 X3) X1) = (k10_ordinal2 X2 (k10_ordinal2 X3 X1)) -> False) -> ((k10_ordinal2 (k10_ordinal2 X2 X3) (esk17_2 X2 X3)) = (k10_ordinal2 X2 (k10_ordinal2 X3 (esk17_2 X2 X3))) -> False) -> (k10_ordinal2 (k10_ordinal2 X2 X3) k1_xboole_0) = (k10_ordinal2 X2 (k10_ordinal2 X3 k1_xboole_0)) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (esk18_2 X2 X3) -> False)
  -> (forall X3 X2 X1, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> (v3_ordinal1 (esk17_2 X1 X2) -> False) -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> (k10_ordinal2 (k10_ordinal2 X1 X2) (esk18_2 X1 X2)) = (k10_ordinal2 X1 (k10_ordinal2 X2 (esk18_2 X1 X2))) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X3 X2, (X2 = k1_xboole_0 -> False) -> ((k10_ordinal2 X3 X2) = (k4_ordinal2 X1) -> False) -> (k9_xtuple_0 X1) = X2 -> (k1_funct_1 X1 (esk22_3 X2 X3 X1)) = (k10_ordinal2 X3 (esk22_3 X2 X3 X1)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> v4_ordinal1 X2 -> False)
  -> (forall X3 X1 X2, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> ((k10_ordinal2 (k10_ordinal2 X1 X2) (esk17_2 X1 X2)) = (k10_ordinal2 X1 (k10_ordinal2 X2 (esk17_2 X1 X2))) -> False) -> (v4_ordinal1 (esk18_2 X1 X2) -> False) -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X1 X2, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> ((k10_ordinal2 (k10_ordinal2 X1 X2) (esk17_2 X1 X2)) = (k10_ordinal2 X1 (k10_ordinal2 X2 (esk17_2 X1 X2))) -> False) -> (v3_ordinal1 (esk18_2 X1 X2) -> False) -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X4 X3, ((k10_ordinal2 (k10_ordinal2 X2 X3) X4) = (k10_ordinal2 X2 (k10_ordinal2 X3 X4)) -> False) -> ((k10_ordinal2 (k10_ordinal2 X2 X3) X1) = (k10_ordinal2 X2 (k10_ordinal2 X3 X1)) -> False) -> (v3_ordinal1 (esk17_2 X2 X3) -> False) -> (k10_ordinal2 (k10_ordinal2 X2 X3) k1_xboole_0) = (k10_ordinal2 X2 (k10_ordinal2 X3 k1_xboole_0)) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (esk18_2 X2 X3) -> False)
  -> (forall X3 X1 X2, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> ((k10_ordinal2 (k10_ordinal2 X1 X2) (esk17_2 X1 X2)) = (k10_ordinal2 X1 (k10_ordinal2 X2 (esk17_2 X1 X2))) -> False) -> (esk18_2 X1 X2) = k1_xboole_0 -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> (v3_ordinal1 (esk17_2 X1 X2) -> False) -> (v4_ordinal1 (esk18_2 X1 X2) -> False) -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> (v3_ordinal1 (esk17_2 X1 X2) -> False) -> (v3_ordinal1 (esk18_2 X1 X2) -> False) -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, ((k10_ordinal2 (k10_ordinal2 X1 X2) X3) = (k10_ordinal2 X1 (k10_ordinal2 X2 X3)) -> False) -> (v3_ordinal1 (esk17_2 X1 X2) -> False) -> (esk18_2 X1 X2) = k1_xboole_0 -> (k10_ordinal2 (k10_ordinal2 X1 X2) k1_xboole_0) = (k10_ordinal2 X1 (k10_ordinal2 X2 k1_xboole_0)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X1 X2 X4, ((k1_funct_1 (esk20_3 X4 X2 X3) X1) = (k10_ordinal2 X4 X1) -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (k10_ordinal2 X2 X3) -> False)
  -> (forall X3 X1 X2 X4, ((k1_funct_1 (esk19_3 X3 X4 X2) X1) = (k10_ordinal2 (k10_ordinal2 X3 X4) X1) -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, (X1 = k1_xboole_0 -> False) -> ((k10_ordinal2 X2 X1) = (k4_ordinal2 X3) -> False) -> (r2_hidden (esk22_3 X1 X2 X3) X1 -> False) -> (k9_xtuple_0 X3) = X1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v5_ordinal1 X3 -> v1_relat_1 X3 -> v1_funct_1 X3 -> v1_ordinal2 X3 -> v4_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, (X1 = k1_xboole_0 -> False) -> ((k10_ordinal2 X2 X1) = (k4_ordinal2 X3) -> False) -> (v3_ordinal1 (esk22_3 X1 X2 X3) -> False) -> (k9_xtuple_0 X3) = X1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v5_ordinal1 X3 -> v1_relat_1 X3 -> v1_funct_1 X3 -> v1_ordinal2 X3 -> v4_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk4_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk4_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, ((k2_xboole_0 (k10_ordinal2 X1 X2) (k1_tarski (k10_ordinal2 X1 X2))) = (k10_ordinal2 X1 (k2_xboole_0 X2 (k1_tarski X2))) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk5_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, ((k9_xtuple_0 (esk20_3 X1 X2 X3)) = (k10_ordinal2 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, ((k9_xtuple_0 (esk19_3 X1 X2 X3)) = X3 -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (v1_ordinal2 (esk20_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (v1_ordinal2 (esk19_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (v1_funct_1 (esk20_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (v1_funct_1 (esk19_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (v1_relat_1 (esk20_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (v1_relat_1 (esk19_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (v5_ordinal1 (esk20_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (v5_ordinal1 (esk19_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk6_2 X1 X2)) = (esk5_2 X1 X2) -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1 X3, (r1_ordinal1 (k10_ordinal2 X3 X1) (k10_ordinal2 X3 X2) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden (k10_ordinal2 X3 X1) (k10_ordinal2 X3 X2) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk5_2 X1 X2) X2 -> False) -> (r2_hidden (esk6_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, ((k10_ordinal2 X2 (esk21_2 X2 X1)) = X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X2 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v3_ordinal1 (esk21_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k1_funct_1 X1 X2) -> False) -> v3_ordinal1 X2 -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 (k10_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 (k10_ordinal2 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (v4_ordinal1 (k10_ordinal2 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_ordinal1 (k3_ordinal2 X1) (k3_ordinal2 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_hidden X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (k10_ordinal2 X1 X2) = k1_xboole_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (k10_ordinal2 X2 X1) = k1_xboole_0 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k3_ordinal2 (k10_xtuple_0 X1)) = (k4_ordinal2 X1) -> False) -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k4_ordinal2 X1) -> False) -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k10_ordinal2 X1 k1_xboole_0) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k10_ordinal2 (k10_ordinal2 esk1_0 esk2_0) esk3_0) = (k10_ordinal2 esk1_0 (k10_ordinal2 esk2_0 esk3_0)) -> False)
  -> (forall X1, v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski k1_xboole_0 X1 -> False) -> False)
  -> (forall X1, (v3_ordinal1 (k3_ordinal2 X1) -> False) -> False)
  -> ((v4_ordinal1 esk10_0 -> False) -> False)
  -> ((v1_ordinal2 esk13_0 -> False) -> False)
  -> ((v1_funct_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v7_ordinal1 esk16_0 -> False) -> False)
  -> ((v7_ordinal1 esk15_0 -> False) -> False)
  -> ((v5_ordinal1 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk12_0 -> False) -> False)
  -> ((v2_ordinal1 esk10_0 -> False) -> False)
  -> ((v1_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 esk9_0 -> False) -> False)
  -> ((v3_ordinal1 esk3_0 -> False) -> False)
  -> ((v3_ordinal1 esk2_0 -> False) -> False)
  -> ((v3_ordinal1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
