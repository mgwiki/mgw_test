(** $I sig/MizarPreamble.mgs **)

Theorem t2_altcat_2:
 forall esk7_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k3_relat_1:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall v2_relat_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk23_0:set,
 forall esk19_0:set,
 forall esk13_0:set,
 forall v1_xtuple_0:set -> prop,
 forall esk15_0:set,
 forall esk18_0:set,
 forall esk17_0:set,
 forall esk14_0:set,
 forall esk12_0:set,
 forall esk11_0:set,
 forall esk20_0:set,
 forall esk10_1:set -> set,
 forall esk16_0:set,
 forall esk21_0:set,
 forall esk22_0:set,
 forall k1_xboole_0:set,
 forall v2_funcop_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall k1_binop_1:set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall esk3_3:set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k9_xtuple_0:set -> set,
 forall k2_funct_4:set -> set,
     (forall X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski (esk3_3 X1 X2 X3) (esk4_3 X1 X2 X3)) (k1_tarski (esk3_3 X1 X2 X3))) (k9_xtuple_0 X1) -> False) -> X2 = (k2_funct_4 X1) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_4 X1) -> False) -> (r2_hidden (esk5_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk6_2 X1 X2) (esk7_2 X1 X2)) (k1_tarski (esk6_2 X1 X2))) (k9_xtuple_0 X1) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk8_2 X1 X2) (esk9_2 X1 X2)) (k1_tarski (esk8_2 X1 X2))) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (X1 = (k2_funct_4 X2) -> False) -> (r2_hidden (esk5_2 X2 X1) (k9_xtuple_0 X1) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk6_2 X2 X1) (esk7_2 X2 X1)) (k1_tarski (esk6_2 X2 X1))) (k9_xtuple_0 X2) -> False) -> (k1_binop_1 X1 (esk9_2 X2 X1) (esk8_2 X2 X1)) = (k1_binop_1 X2 (esk8_2 X2 X1) (esk9_2 X2 X1)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X4 X3 X2 X1, (X2 = (k2_funct_4 X1) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk8_2 X1 X2) (esk9_2 X1 X2)) (k1_tarski (esk8_2 X1 X2))) (k9_xtuple_0 X1) -> False) -> (esk5_2 X1 X2) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden (esk5_2 X1 X2) (k9_xtuple_0 X2) -> r2_hidden (k2_tarski (k2_tarski X4 X3) (k1_tarski X4)) (k9_xtuple_0 X1) -> False)
  -> (forall X1 X3 X2, ((k2_tarski (k2_tarski (esk4_3 X2 X3 X1) (esk3_3 X2 X3 X1)) (k1_tarski (esk4_3 X2 X3 X1))) = X1 -> False) -> X3 = (k2_funct_4 X2) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X3) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_4 X1) -> False) -> ((k2_tarski (k2_tarski (esk7_2 X1 X2) (esk6_2 X1 X2)) (k1_tarski (esk7_2 X1 X2))) = (esk5_2 X1 X2) -> False) -> (r2_hidden (esk5_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk8_2 X1 X2) (esk9_2 X1 X2)) (k1_tarski (esk8_2 X1 X2))) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X4 X3 X1 X2, (X1 = (k2_funct_4 X2) -> False) -> (esk5_2 X2 X1) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> (k1_binop_1 X1 (esk9_2 X2 X1) (esk8_2 X2 X1)) = (k1_binop_1 X2 (esk8_2 X2 X1) (esk9_2 X2 X1)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden (esk5_2 X2 X1) (k9_xtuple_0 X1) -> r2_hidden (k2_tarski (k2_tarski X4 X3) (k1_tarski X4)) (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X1 = (k2_funct_4 X2) -> False) -> ((k2_tarski (k2_tarski (esk7_2 X2 X1) (esk6_2 X2 X1)) (k1_tarski (esk7_2 X2 X1))) = (esk5_2 X2 X1) -> False) -> (r2_hidden (esk5_2 X2 X1) (k9_xtuple_0 X1) -> False) -> (k1_binop_1 X1 (esk9_2 X2 X1) (esk8_2 X2 X1)) = (k1_binop_1 X2 (esk8_2 X2 X1) (esk9_2 X2 X1)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, ((k1_binop_1 (k2_funct_4 X1) X2 X3) = (k1_binop_1 X1 X3 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden (k2_tarski (k2_tarski X2 X3) (k1_tarski X2)) (k9_xtuple_0 (k2_funct_4 X1)) -> False)
  -> (forall X1 X2 X4 X3, ((k1_binop_1 X3 X1 X2) = (k1_binop_1 X4 X2 X1) -> False) -> X4 = (k2_funct_4 X3) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k9_xtuple_0 X3) -> False)
  -> (forall X2 X1 X3, (r2_hidden (k2_tarski (k2_tarski X2 X1) (k1_tarski X2)) (k9_xtuple_0 X3) -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k9_xtuple_0 (k2_funct_4 X3)) -> False)
  -> (forall X2 X1 X3, (r2_hidden (k2_tarski (k2_tarski X2 X1) (k1_tarski X2)) (k9_xtuple_0 (k2_funct_4 X3)) -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k9_xtuple_0 X3) -> False)
  -> (forall X4 X3 X2 X1 X5, (r2_hidden X1 (k9_xtuple_0 X5) -> False) -> X5 = (k2_funct_4 X4) -> X1 = (k2_tarski (k2_tarski X2 X3) (k1_tarski X2)) -> v1_relat_1 X5 -> v1_relat_1 X4 -> v1_funct_1 X5 -> v1_funct_1 X4 -> r2_hidden (k2_tarski (k2_tarski X3 X2) (k1_tarski X3)) (k9_xtuple_0 X4) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k3_relat_1 X2 X1) X3) = (k1_funct_1 X1 (k1_funct_1 X2 X3)) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 (k3_relat_1 X2 X1)) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 (k9_xtuple_0 (k3_relat_1 X2 X3)) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> r2_hidden (k1_funct_1 X2 X1) (k9_xtuple_0 X3) -> False)
  -> (forall X1 X2 X3, (r2_hidden (k1_funct_1 X1 X2) (k9_xtuple_0 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> r2_hidden X2 (k9_xtuple_0 (k3_relat_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k9_xtuple_0 X2) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 (k3_relat_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k3_relat_1 X1 X2) X3) = (k1_funct_1 X2 (k1_funct_1 X1 X3)) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2, (v2_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_funcop_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v2_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_4 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_4 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_funct_4 (k3_relat_1 esk1_0 esk2_0)) = (k3_relat_1 (k2_funct_4 esk1_0) esk2_0) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v3_funct_1 esk22_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> ((v1_xtuple_0 esk15_0 -> False) -> False)
  -> ((v4_funct_1 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk21_0 -> False) -> False)
  -> ((v2_relat_1 esk20_0 -> False) -> False)
  -> ((v2_relat_1 esk18_0 -> False) -> False)
  -> ((v3_funct_1 esk16_0 -> False) -> False)
  -> ((v2_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funcop_1 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk11_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_funct_1 esk1_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
