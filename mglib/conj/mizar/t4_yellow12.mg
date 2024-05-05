(** $I sig/MizarPreamble.mgs **)

Theorem t4_yellow12:
 forall k13_funct_3:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall esk18_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k8_mcart_1:set -> set -> set -> set -> set,
 forall k10_funct_3:set -> set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall esk17_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall v1_partfun1:set -> set -> prop,
 forall esk10_3:set -> set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall k8_subset_1:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk12_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall k1_relset_1:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk22_1:set -> set,
 forall esk25_0:set,
 forall esk20_2:set -> set -> set,
 forall esk19_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk23_0:set,
 forall esk24_1:set -> set,
 forall esk21_2:set -> set -> set,
 forall esk26_1:set -> set,
 forall k1_xboole_0:set,
 forall esk27_1:set -> set,
 forall k2_relset_1:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk14_3:set -> set -> set -> set,
 forall esk15_3:set -> set -> set -> set,
 forall k1_binop_1:set -> set -> set -> set,
 forall k9_funct_3:set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk5_4:set -> set -> set -> set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X3 X2 X4 X1, ((k2_tarski (k2_tarski (esk5_4 X2 X3 X4 X1) (esk6_4 X2 X3 X4 X1)) (k1_tarski (esk5_4 X2 X3 X4 X1))) = X1 -> False) -> X4 = (k2_zfmisc_1 X2 X3) -> r2_hidden X1 X4 -> False)
  -> (forall X2 X1 X3, (X1 = (k13_funct_3 X2 X3) -> False) -> (k9_xtuple_0 X1) = (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> (k2_tarski (k2_tarski (k1_funct_1 X2 (esk18_3 X2 X3 X1)) (k1_funct_1 X3 (esk18_3 X2 X3 X1))) (k1_tarski (k1_funct_1 X2 (esk18_3 X2 X3 X1)))) = (k1_funct_1 X1 (esk18_3 X2 X3 X1)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> ((k2_tarski (k2_tarski (esk8_3 X1 X2 X3) (esk9_3 X1 X2 X3)) (k1_tarski (esk8_3 X1 X2 X3))) = (esk7_3 X1 X2 X3) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> False)
  -> (forall X4 X3 X2 X1, (m1_subset_1 (k8_mcart_1 X2 X4 X1 X3) (k1_zfmisc_1 (k2_zfmisc_1 X2 X4)) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (X1 = (k9_funct_3 X2 X3) -> False) -> (k9_xtuple_0 X1) = (k2_zfmisc_1 X2 X3) -> (k1_binop_1 X1 (esk14_3 X2 X3 X1) (esk15_3 X2 X3 X1)) = (esk14_3 X2 X3 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (X1 = (k10_funct_3 X2 X3) -> False) -> (k9_xtuple_0 X1) = (k2_zfmisc_1 X2 X3) -> (k1_binop_1 X1 (esk16_3 X2 X3 X1) (esk17_3 X2 X3 X1)) = (esk17_3 X2 X3 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk6_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden (esk5_4 X1 X2 X3 X4) X1 -> False) -> X3 = (k2_zfmisc_1 X1 X2) -> r2_hidden X4 X3 -> False)
  -> (forall X5 X4 X1 X2 X3, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (esk7_3 X1 X2 X3) = (k2_tarski (k2_tarski X4 X5) (k1_tarski X4)) -> r2_hidden X5 X2 -> r2_hidden X4 X1 -> r2_hidden (esk7_3 X1 X2 X3) X3 -> False)
  -> ((k9_xtuple_0 (k13_funct_3 (k10_funct_3 esk1_0 esk2_0) (k9_funct_3 esk1_0 esk2_0))) = (k2_zfmisc_1 esk1_0 esk2_0) -> (k10_xtuple_0 (k13_funct_3 (k10_funct_3 esk3_0 esk4_0) (k9_funct_3 esk3_0 esk4_0))) = (k2_zfmisc_1 esk4_0 esk3_0) -> False)
  -> (forall X4 X3 X2 X1, ((k8_mcart_1 X2 X4 X1 X3) = (k2_zfmisc_1 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X4 X2, ((k1_funct_1 X2 X1) = (k2_tarski (k2_tarski (k1_funct_1 X3 X1) (k1_funct_1 X4 X1)) (k1_tarski (k1_funct_1 X3 X1))) -> False) -> X2 = (k13_funct_3 X3 X4) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X4 X3 X2 X1, ((k1_binop_1 (k13_funct_3 (k10_funct_3 X2 X4) (k9_funct_3 X2 X4)) X1 X3) = (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_zfmisc_1 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X1 X3, (X3 = (k13_funct_3 X1 X2) -> False) -> (r2_hidden (esk18_3 X1 X2 X3) (k9_xtuple_0 X3) -> False) -> (k9_xtuple_0 X3) = (k3_xboole_0 (k9_xtuple_0 X1) (k9_xtuple_0 X2)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X3, (X3 = (k9_funct_3 X1 X2) -> False) -> (r2_hidden (esk15_3 X1 X2 X3) X2 -> False) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 X1 X2) -> v1_relat_1 X3 -> v1_funct_1 X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k9_funct_3 X1 X2) -> False) -> (r2_hidden (esk14_3 X1 X2 X3) X1 -> False) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 X1 X2) -> v1_relat_1 X3 -> v1_funct_1 X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k10_funct_3 X1 X2) -> False) -> (r2_hidden (esk17_3 X1 X2 X3) X2 -> False) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 X1 X2) -> v1_relat_1 X3 -> v1_funct_1 X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k10_funct_3 X1 X2) -> False) -> (r2_hidden (esk16_3 X1 X2 X3) X1 -> False) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 X1 X2) -> v1_relat_1 X3 -> v1_funct_1 X3 -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk10_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk10_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk11_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk11_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k8_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k2_zfmisc_1 X2 X4) -> X5 = (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski (k10_xtuple_0 (k13_funct_3 X1 X2)) (k2_zfmisc_1 (k10_xtuple_0 X1) (k10_xtuple_0 X2)) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k8_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X4 X2 X5 X3 X1, ((k1_binop_1 X5 X1 X3) = X1 -> False) -> X5 = (k9_funct_3 X2 X4) -> v1_relat_1 X5 -> v1_funct_1 X5 -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X4 X2 X5 X1 X3, ((k1_binop_1 X5 X1 X3) = X3 -> False) -> X5 = (k10_funct_3 X2 X4) -> v1_relat_1 X5 -> v1_funct_1 X5 -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk12_2 X1 X2)) = (esk11_2 X1 X2) -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk11_2 X1 X2) X2 -> False) -> (r2_hidden (esk12_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k3_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, ((k9_xtuple_0 X1) = (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> False) -> X1 = (k13_funct_3 X2 X3) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k8_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk13_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 (k13_funct_3 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k13_funct_3 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 X1) = (k2_zfmisc_1 X2 X3) -> False) -> X1 = (k9_funct_3 X2 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 X1) = (k2_zfmisc_1 X2 X3) -> False) -> X1 = (k10_funct_3 X2 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k2_relset_1 X2 X1) = (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk26_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (forall X1 X2, (m1_subset_1 (k9_funct_3 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X1)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (k10_funct_3 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_2 (k9_funct_3 X1 X2) (k2_zfmisc_1 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (k10_funct_3 X1 X2) (k2_zfmisc_1 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk21_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk20_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk21_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk20_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk20_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k9_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k9_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k10_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k10_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k9_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k10_funct_3 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk24_1 X1) -> False) -> False)
  -> ((v1_xboole_0 esk23_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
