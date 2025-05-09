(** $I sig/MizarPreamble.mgs **)

Theorem t50_ordinal3:
 forall r2_hidden:set -> set -> prop,
 forall k4_ordinal3:set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall v5_ordinal1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_ordinal2:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall np__1:set,
 forall esk18_3:set -> set -> set -> set,
 forall k4_ordinal2:set -> set,
 forall esk6_2:set -> set -> set,
 forall esk17_2:set -> set -> set,
 forall v7_ordinal1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k3_ordinal2:set -> set,
 forall k10_xtuple_0:set -> set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk12_0:set,
 forall v2_xxreal_0:set -> prop,
 forall esk11_0:set,
 forall esk13_0:set,
 forall esk9_0:set,
 forall esk7_0:set,
 forall o_0_0_xboole_0:set,
 forall esk8_0:set,
 forall esk5_1:set -> set,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall esk10_0:set,
 forall esk14_0:set,
 forall v6_ordinal1:set -> prop,
 forall k10_ordinal2:set -> set -> set,
 forall r1_ordinal1:set -> set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v4_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall v3_ordinal1:set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk15_2:set -> set -> set,
 forall esk16_2:set -> set -> set,
 forall k11_ordinal2:set -> set -> set,
     (forall X3 X2 X1, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> (k11_ordinal2 (k11_ordinal2 (esk16_2 X1 X2) X1) X2) = (k11_ordinal2 (esk16_2 X1 X2) (k11_ordinal2 X1 X2)) -> (k11_ordinal2 (k11_ordinal2 (k2_xboole_0 (esk15_2 X1 X2) (k1_tarski (esk15_2 X1 X2))) X1) X2) = (k11_ordinal2 (k2_xboole_0 (esk15_2 X1 X2) (k1_tarski (esk15_2 X1 X2))) (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X4 X3 X2, ((k11_ordinal2 (k11_ordinal2 X4 X2) X3) = (k11_ordinal2 X4 (k11_ordinal2 X2 X3)) -> False) -> ((k11_ordinal2 (k11_ordinal2 X1 X2) X3) = (k11_ordinal2 X1 (k11_ordinal2 X2 X3)) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X2) X3) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X2 X3)) -> (k11_ordinal2 (k11_ordinal2 (k2_xboole_0 (esk15_2 X2 X3) (k1_tarski (esk15_2 X2 X3))) X2) X3) = (k11_ordinal2 (k2_xboole_0 (esk15_2 X2 X3) (k1_tarski (esk15_2 X2 X3))) (k11_ordinal2 X2 X3)) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (esk16_2 X2 X3) -> False)
  -> (forall X3 X2 X1, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> (v4_ordinal1 (esk16_2 X1 X2) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> (k11_ordinal2 (k11_ordinal2 (k2_xboole_0 (esk15_2 X1 X2) (k1_tarski (esk15_2 X1 X2))) X1) X2) = (k11_ordinal2 (k2_xboole_0 (esk15_2 X1 X2) (k1_tarski (esk15_2 X1 X2))) (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> (v3_ordinal1 (esk16_2 X1 X2) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> (k11_ordinal2 (k11_ordinal2 (k2_xboole_0 (esk15_2 X1 X2) (k1_tarski (esk15_2 X1 X2))) X1) X2) = (k11_ordinal2 (k2_xboole_0 (esk15_2 X1 X2) (k1_tarski (esk15_2 X1 X2))) (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> (esk16_2 X1 X2) = k1_xboole_0 -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> (k11_ordinal2 (k11_ordinal2 (k2_xboole_0 (esk15_2 X1 X2) (k1_tarski (esk15_2 X1 X2))) X1) X2) = (k11_ordinal2 (k2_xboole_0 (esk15_2 X1 X2) (k1_tarski (esk15_2 X1 X2))) (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1 X3, (X1 = (k4_ordinal3 X2 X3) -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X3) -> (k1_funct_1 X1 (esk4_3 X2 X3 X1)) = (k11_ordinal2 (k1_funct_1 X3 (esk4_3 X2 X3 X1)) X2) -> v3_ordinal1 X2 -> v5_ordinal1 X3 -> v5_ordinal1 X1 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_ordinal2 X3 -> v1_ordinal2 X1 -> False)
  -> (forall X3 X1 X2, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> ((k11_ordinal2 (k11_ordinal2 (esk15_2 X1 X2) X1) X2) = (k11_ordinal2 (esk15_2 X1 X2) (k11_ordinal2 X1 X2)) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> (k11_ordinal2 (k11_ordinal2 (esk16_2 X1 X2) X1) X2) = (k11_ordinal2 (esk16_2 X1 X2) (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X4 X3 X2, ((k11_ordinal2 (k11_ordinal2 X4 X2) X3) = (k11_ordinal2 X4 (k11_ordinal2 X2 X3)) -> False) -> ((k11_ordinal2 (k11_ordinal2 X1 X2) X3) = (k11_ordinal2 X1 (k11_ordinal2 X2 X3)) -> False) -> ((k11_ordinal2 (k11_ordinal2 (esk15_2 X2 X3) X2) X3) = (k11_ordinal2 (esk15_2 X2 X3) (k11_ordinal2 X2 X3)) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X2) X3) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X2 X3)) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (esk16_2 X2 X3) -> False)
  -> (forall X3 X2 X1, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> (v3_ordinal1 (esk15_2 X1 X2) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> (k11_ordinal2 (k11_ordinal2 (esk16_2 X1 X2) X1) X2) = (k11_ordinal2 (esk16_2 X1 X2) (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> ((k11_ordinal2 X3 X2) = (k4_ordinal2 X1) -> False) -> (k9_xtuple_0 X1) = X3 -> (k1_funct_1 X1 (esk18_3 X2 X3 X1)) = (k11_ordinal2 (esk18_3 X2 X3 X1) X2) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> v4_ordinal1 X3 -> r2_hidden np__1 X2 -> False)
  -> (forall X3 X1 X2, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> ((k11_ordinal2 (k11_ordinal2 (esk15_2 X1 X2) X1) X2) = (k11_ordinal2 (esk15_2 X1 X2) (k11_ordinal2 X1 X2)) -> False) -> (v4_ordinal1 (esk16_2 X1 X2) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X1 X2, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> ((k11_ordinal2 (k11_ordinal2 (esk15_2 X1 X2) X1) X2) = (k11_ordinal2 (esk15_2 X1 X2) (k11_ordinal2 X1 X2)) -> False) -> (v3_ordinal1 (esk16_2 X1 X2) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X4 X3 X2, ((k11_ordinal2 (k11_ordinal2 X4 X2) X3) = (k11_ordinal2 X4 (k11_ordinal2 X2 X3)) -> False) -> ((k11_ordinal2 (k11_ordinal2 X1 X2) X3) = (k11_ordinal2 X1 (k11_ordinal2 X2 X3)) -> False) -> (v3_ordinal1 (esk15_2 X2 X3) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X2) X3) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X2 X3)) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 (esk16_2 X2 X3) -> False)
  -> (forall X3 X1 X2, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> ((k11_ordinal2 (k11_ordinal2 (esk15_2 X1 X2) X1) X2) = (k11_ordinal2 (esk15_2 X1 X2) (k11_ordinal2 X1 X2)) -> False) -> (esk16_2 X1 X2) = k1_xboole_0 -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> (v3_ordinal1 (esk15_2 X1 X2) -> False) -> (v4_ordinal1 (esk16_2 X1 X2) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> (v3_ordinal1 (esk15_2 X1 X2) -> False) -> (v3_ordinal1 (esk16_2 X1 X2) -> False) -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X3 X2 X1, ((k11_ordinal2 (k11_ordinal2 X3 X1) X2) = (k11_ordinal2 X3 (k11_ordinal2 X1 X2)) -> False) -> (v3_ordinal1 (esk15_2 X1 X2) -> False) -> (esk16_2 X1 X2) = k1_xboole_0 -> (k11_ordinal2 (k11_ordinal2 k1_xboole_0 X1) X2) = (k11_ordinal2 k1_xboole_0 (k11_ordinal2 X1 X2)) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (X3 = (k4_ordinal3 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) (k9_xtuple_0 X2) -> False) -> (k9_xtuple_0 X2) = (k9_xtuple_0 X3) -> v3_ordinal1 X1 -> v5_ordinal1 X3 -> v5_ordinal1 X2 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_ordinal2 X3 -> v1_ordinal2 X2 -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> ((k11_ordinal2 X2 X1) = (k4_ordinal2 X3) -> False) -> (r2_hidden (esk18_3 X1 X2 X3) X2 -> False) -> (k9_xtuple_0 X3) = X2 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v5_ordinal1 X3 -> v1_relat_1 X3 -> v1_funct_1 X3 -> v1_ordinal2 X3 -> v4_ordinal1 X2 -> r2_hidden np__1 X1 -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> ((k11_ordinal2 X2 X1) = (k4_ordinal2 X3) -> False) -> (v3_ordinal1 (esk18_3 X1 X2 X3) -> False) -> (k9_xtuple_0 X3) = X2 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v5_ordinal1 X3 -> v1_relat_1 X3 -> v1_funct_1 X3 -> v1_ordinal2 X3 -> v4_ordinal1 X2 -> r2_hidden np__1 X1 -> False)
  -> (forall X1 X2 X3, (X3 = (k4_ordinal3 X1 X2) -> False) -> (v3_ordinal1 (esk4_3 X1 X2 X3) -> False) -> (k9_xtuple_0 X2) = (k9_xtuple_0 X3) -> v3_ordinal1 X1 -> v5_ordinal1 X3 -> v5_ordinal1 X2 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_ordinal2 X3 -> v1_ordinal2 X2 -> False)
  -> (forall X1 X4 X2 X3, ((k1_funct_1 X3 X1) = (k11_ordinal2 (k1_funct_1 X2 X1) X4) -> False) -> X3 = (k4_ordinal3 X4 X2) -> v3_ordinal1 X4 -> v3_ordinal1 X1 -> v5_ordinal1 X3 -> v5_ordinal1 X2 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_ordinal2 X3 -> v1_ordinal2 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X4 X1 X3 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden (k11_ordinal2 X3 X1) (k11_ordinal2 X4 X2) -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X3 X4 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden (k11_ordinal2 X3 X1) (k11_ordinal2 X4 X2) -> False) -> v3_ordinal1 X4 -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2 X3, ((k10_ordinal2 (k11_ordinal2 X1 X3) (k11_ordinal2 X2 X3)) = (k11_ordinal2 (k10_ordinal2 X1 X2) X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk6_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> ((k9_xtuple_0 X1) = k1_xboole_0 -> False) -> ((k4_ordinal2 (k4_ordinal3 X2 X1)) = (k11_ordinal2 (k4_ordinal2 X1) X2) -> False) -> v3_ordinal1 X2 -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> v4_ordinal1 (k4_ordinal2 X1) -> False)
  -> (forall X2 X1, ((k11_ordinal2 (k2_xboole_0 X1 (k1_tarski X1)) X2) = (k10_ordinal2 (k11_ordinal2 X1 X2) X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1 X3, ((k1_funct_1 (esk17_2 X3 X2) X1) = (k11_ordinal2 X1 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X1 X2, ((k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> False) -> X1 = (k4_ordinal3 X3 X2) -> v3_ordinal1 X3 -> v5_ordinal1 X2 -> v5_ordinal1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_ordinal2 X2 -> v1_ordinal2 X1 -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_ordinal2 (k4_ordinal3 X1 X2) -> False) -> v3_ordinal1 X1 -> v5_ordinal1 X2 -> v1_relat_1 X2 -> v1_funct_1 X2 -> v1_ordinal2 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 (k4_ordinal3 X1 X2) -> False) -> v3_ordinal1 X1 -> v5_ordinal1 X2 -> v1_relat_1 X2 -> v1_funct_1 X2 -> v1_ordinal2 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k4_ordinal3 X1 X2) -> False) -> v3_ordinal1 X1 -> v5_ordinal1 X2 -> v1_relat_1 X2 -> v1_funct_1 X2 -> v1_ordinal2 X2 -> False)
  -> (forall X1 X2, (v5_ordinal1 (k4_ordinal3 X1 X2) -> False) -> v3_ordinal1 X1 -> v5_ordinal1 X2 -> v1_relat_1 X2 -> v1_funct_1 X2 -> v1_ordinal2 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k1_funct_1 X1 X2) -> False) -> v3_ordinal1 X2 -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_ordinal2 X1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (v4_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v4_ordinal1 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_ordinal1 X1 X2 -> False)
  -> (forall X1 X2, (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k1_tarski X1)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk17_2 X1 X2)) = X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_ordinal2 (esk17_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (esk17_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (esk17_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v5_ordinal1 (esk17_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k10_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k2_xboole_0 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_ordinal1 X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_hidden X2 X1 -> False) -> (r1_ordinal1 X1 X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, ((k2_xboole_0 X1 (k1_tarski X1)) = (k10_ordinal2 X1 np__1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k4_ordinal2 X1) = (k3_ordinal2 (k10_xtuple_0 X1)) -> False) -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k4_ordinal2 X1) -> False) -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v5_ordinal1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (X1 = np__1 -> False) -> v3_ordinal1 X1 -> r1_ordinal1 X1 np__1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_ordinal1 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 np__1 X1) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 X1 np__1) = X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 k1_xboole_0 X1) = k1_xboole_0 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, ((k11_ordinal2 X1 k1_xboole_0) = k1_xboole_0 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k11_ordinal2 (k11_ordinal2 esk1_0 esk2_0) esk3_0) = (k11_ordinal2 esk1_0 (k11_ordinal2 esk2_0 esk3_0)) -> False)
  -> (forall X1, v1_xboole_0 (k2_xboole_0 X1 (k1_tarski X1)) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> (forall X1, (v3_ordinal1 (k3_ordinal2 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v4_ordinal1 esk8_0 -> False) -> False)
  -> ((v1_ordinal2 esk11_0 -> False) -> False)
  -> ((v1_funct_1 esk11_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v7_ordinal1 esk14_0 -> False) -> False)
  -> ((v7_ordinal1 esk13_0 -> False) -> False)
  -> ((v5_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk10_0 -> False) -> False)
  -> ((v2_ordinal1 esk8_0 -> False) -> False)
  -> ((v1_ordinal1 esk10_0 -> False) -> False)
  -> ((v1_ordinal1 esk8_0 -> False) -> False)
  -> ((v3_ordinal1 esk10_0 -> False) -> False)
  -> ((v3_ordinal1 esk8_0 -> False) -> False)
  -> ((v3_ordinal1 esk7_0 -> False) -> False)
  -> ((v3_ordinal1 esk3_0 -> False) -> False)
  -> ((v3_ordinal1 esk2_0 -> False) -> False)
  -> ((v3_ordinal1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
