(** $I sig/MizarPreamble.mgs **)

Theorem t3_altcat_2:
 forall k15_funct_3:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall k1_binop_1:set -> set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall esk8_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk32_1:set -> set,
 forall esk18_1:set -> set,
 forall k1_xboole_0:set,
 forall esk31_0:set,
 forall esk29_0:set,
 forall esk21_0:set,
 forall v1_xtuple_0:set -> prop,
 forall esk27_2:set -> set -> set,
 forall esk24_1:set -> set,
 forall esk13_1:set -> set,
 forall esk20_0:set,
 forall esk26_0:set,
 forall esk19_0:set,
 forall esk14_0:set,
 forall esk15_0:set,
 forall esk22_0:set,
 forall esk23_0:set,
 forall esk36_1:set -> set,
 forall esk33_2:set -> set -> set,
 forall esk17_2:set -> set -> set,
 forall esk16_0:set,
 forall esk25_0:set,
 forall esk35_0:set,
 forall esk28_1:set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall v2_funcop_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall esk30_1:set -> set,
 forall esk34_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall k3_relat_1:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall k2_funct_4:set -> set,
 forall k1_tarski:set -> set,
 forall esk37_4:set -> set -> set -> set -> set,
 forall esk38_4:set -> set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X3 X4 X1 X2, ((k2_tarski (k2_tarski (esk37_4 X2 X3 X4 X1) (esk38_4 X2 X3 X4 X1)) (k1_tarski (esk37_4 X2 X3 X4 X1))) = X1 -> False) -> r2_hidden X1 X2 -> r1_tarski X2 (k2_zfmisc_1 X3 X4) -> False)
  -> (forall X2 X1 X3, (X1 = (k15_funct_3 X2 X3) -> False) -> (k9_xtuple_0 X1) = (k2_zfmisc_1 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> (k2_tarski (k2_tarski (k1_funct_1 X2 (esk11_3 X2 X3 X1)) (k1_funct_1 X3 (esk12_3 X2 X3 X1))) (k1_tarski (k1_funct_1 X2 (esk11_3 X2 X3 X1)))) = (k1_binop_1 X1 (esk11_3 X2 X3 X1) (esk12_3 X2 X3 X1)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski (esk4_3 X1 X2 X3) (esk5_3 X1 X2 X3)) (k1_tarski (esk4_3 X1 X2 X3))) (k9_xtuple_0 X1) -> False) -> X2 = (k2_funct_4 X1) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_4 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk7_2 X1 X2) (esk8_2 X1 X2)) (k1_tarski (esk7_2 X1 X2))) (k9_xtuple_0 X1) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk9_2 X1 X2) (esk10_2 X1 X2)) (k1_tarski (esk9_2 X1 X2))) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (X1 = (k2_funct_4 X2) -> False) -> (r2_hidden (esk6_2 X2 X1) (k9_xtuple_0 X1) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk7_2 X2 X1) (esk8_2 X2 X1)) (k1_tarski (esk7_2 X2 X1))) (k9_xtuple_0 X2) -> False) -> (k1_binop_1 X1 (esk10_2 X2 X1) (esk9_2 X2 X1)) = (k1_binop_1 X2 (esk9_2 X2 X1) (esk10_2 X2 X1)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X4 X3 X2 X1, (X2 = (k2_funct_4 X1) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk9_2 X1 X2) (esk10_2 X1 X2)) (k1_tarski (esk9_2 X1 X2))) (k9_xtuple_0 X1) -> False) -> (esk6_2 X1 X2) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden (esk6_2 X1 X2) (k9_xtuple_0 X2) -> r2_hidden (k2_tarski (k2_tarski X4 X3) (k1_tarski X4)) (k9_xtuple_0 X1) -> False)
  -> (forall X1 X3 X2, ((k2_tarski (k2_tarski (esk5_3 X2 X3 X1) (esk4_3 X2 X3 X1)) (k1_tarski (esk5_3 X2 X3 X1))) = X1 -> False) -> X3 = (k2_funct_4 X2) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X3) -> False)
  -> (forall X1 X2, (X2 = (k2_funct_4 X1) -> False) -> ((k2_tarski (k2_tarski (esk8_2 X1 X2) (esk7_2 X1 X2)) (k1_tarski (esk8_2 X1 X2))) = (esk6_2 X1 X2) -> False) -> (r2_hidden (esk6_2 X1 X2) (k9_xtuple_0 X2) -> False) -> (r2_hidden (k2_tarski (k2_tarski (esk9_2 X1 X2) (esk10_2 X1 X2)) (k1_tarski (esk9_2 X1 X2))) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X4 X3 X1 X2, (X1 = (k2_funct_4 X2) -> False) -> (esk6_2 X2 X1) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> (k1_binop_1 X1 (esk10_2 X2 X1) (esk9_2 X2 X1)) = (k1_binop_1 X2 (esk9_2 X2 X1) (esk10_2 X2 X1)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden (esk6_2 X2 X1) (k9_xtuple_0 X1) -> r2_hidden (k2_tarski (k2_tarski X4 X3) (k1_tarski X4)) (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2, (X1 = (k2_funct_4 X2) -> False) -> ((k2_tarski (k2_tarski (esk8_2 X2 X1) (esk7_2 X2 X1)) (k1_tarski (esk8_2 X2 X1))) = (esk6_2 X2 X1) -> False) -> (r2_hidden (esk6_2 X2 X1) (k9_xtuple_0 X1) -> False) -> (k1_binop_1 X1 (esk10_2 X2 X1) (esk9_2 X2 X1)) = (k1_binop_1 X2 (esk9_2 X2 X1) (esk10_2 X2 X1)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X3 X4 X1, (r2_hidden (esk38_4 X1 X2 X3 X4) X3 -> False) -> r2_hidden X4 X1 -> r1_tarski X1 (k2_zfmisc_1 X2 X3) -> False)
  -> (forall X2 X3 X4 X1, (r2_hidden (esk37_4 X1 X2 X3 X4) X2 -> False) -> r2_hidden X4 X1 -> r1_tarski X1 (k2_zfmisc_1 X2 X3) -> False)
  -> (forall X1 X3 X2 X4 X5, ((k1_binop_1 X5 X1 X3) = (k2_tarski (k2_tarski (k1_funct_1 X2 X1) (k1_funct_1 X4 X3)) (k1_tarski (k1_funct_1 X2 X1))) -> False) -> X5 = (k15_funct_3 X2 X4) -> v1_relat_1 X5 -> v1_relat_1 X4 -> v1_relat_1 X2 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X2 -> r2_hidden X3 (k9_xtuple_0 X4) -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X1 X2 X4 X3, ((k1_binop_1 X3 X1 X2) = (k1_binop_1 X4 X2 X1) -> False) -> X4 = (k2_funct_4 X3) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k9_xtuple_0 X3) -> False)
  -> (forall X2 X1 X3, (r2_hidden (k2_tarski (k2_tarski X2 X1) (k1_tarski X2)) (k9_xtuple_0 X3) -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k9_xtuple_0 (k2_funct_4 X3)) -> False)
  -> (forall X2 X1 X3, (r2_hidden (k2_tarski (k2_tarski X2 X1) (k1_tarski X2)) (k9_xtuple_0 (k2_funct_4 X3)) -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> r2_hidden (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k9_xtuple_0 X3) -> False)
  -> (forall X4 X3 X2 X1 X5, (r2_hidden X1 (k9_xtuple_0 X5) -> False) -> X5 = (k2_funct_4 X4) -> X1 = (k2_tarski (k2_tarski X2 X3) (k1_tarski X2)) -> v1_relat_1 X5 -> v1_relat_1 X4 -> v1_funct_1 X5 -> v1_funct_1 X4 -> r2_hidden (k2_tarski (k2_tarski X3 X2) (k1_tarski X3)) (k9_xtuple_0 X4) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X1 X3, (X3 = (k15_funct_3 X1 X2) -> False) -> (r2_hidden (esk12_3 X1 X2 X3) (k9_xtuple_0 X2) -> False) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 (k9_xtuple_0 X1) (k9_xtuple_0 X2)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1 X3, (X3 = (k15_funct_3 X1 X2) -> False) -> (r2_hidden (esk11_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 (k9_xtuple_0 X1) (k9_xtuple_0 X2)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k3_relat_1 X2 X1) X3) = (k1_funct_1 X1 (k1_funct_1 X2 X3)) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 (k3_relat_1 X2 X1)) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 (k9_xtuple_0 (k3_relat_1 X2 X3)) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> r2_hidden (k1_funct_1 X2 X1) (k9_xtuple_0 X3) -> False)
  -> (forall X1 X2 X3, (r2_hidden (k1_funct_1 X1 X2) (k9_xtuple_0 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> r2_hidden X2 (k9_xtuple_0 (k3_relat_1 X1 X3)) -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k9_xtuple_0 X2) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 (k3_relat_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k3_relat_1 X1 X2) X3) = (k1_funct_1 X2 (k1_funct_1 X1 X3)) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1 X3, ((k9_xtuple_0 X1) = (k2_zfmisc_1 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> False) -> X1 = (k15_funct_3 X2 X3) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v2_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X2, (v1_funcop_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k15_funct_3 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k15_funct_3 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (v2_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k2_funct_4 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k2_funct_4 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk34_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk32_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_funct_4 (k3_relat_1 (k15_funct_3 esk2_0 esk3_0) esk1_0)) = (k3_relat_1 (k15_funct_3 esk3_0 esk2_0) (k2_funct_4 esk1_0)) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk28_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk31_0 -> False)
  -> (v1_xboole_0 esk35_0 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk17_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk33_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk27_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk17_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk33_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk27_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk17_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk33_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk33_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk36_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk36_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk36_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk36_1 X1) -> False) -> False)
  -> ((v1_xtuple_0 esk20_0 -> False) -> False)
  -> ((v2_relat_1 esk29_0 -> False) -> False)
  -> ((v2_relat_1 esk26_0 -> False) -> False)
  -> ((v2_relat_1 esk23_0 -> False) -> False)
  -> ((v3_funct_1 esk21_0 -> False) -> False)
  -> ((v2_funct_1 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 esk19_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_funcop_1 esk14_0 -> False) -> False)
  -> ((v4_funct_1 esk35_0 -> False) -> False)
  -> ((v1_funct_1 esk31_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk26_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_funct_1 esk1_0 -> False) -> False)
  -> ((v1_relat_1 esk31_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk3_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
