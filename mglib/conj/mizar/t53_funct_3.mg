(** $I sig/MizarPreamble.mgs **)

Theorem t53_funct_3:
 forall k13_funct_3:set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall k9_funct_3:set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall esk3_3:set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall k1_relset_1:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v3_relat_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk24_1:set -> set,
 forall esk12_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk20_1:set -> set,
 forall esk27_0:set,
 forall esk17_0:set,
 forall esk25_2:set -> set -> set,
 forall esk18_0:set,
 forall esk14_0:set,
 forall esk13_0:set,
 forall esk9_0:set,
 forall esk15_0:set,
 forall esk8_1:set -> set,
 forall esk28_1:set -> set,
 forall esk16_1:set -> set,
 forall esk19_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall esk10_0:set,
 forall esk21_0:set,
 forall esk23_0:set,
 forall k1_xboole_0:set,
 forall v3_funct_1:set -> prop,
 forall esk22_1:set -> set,
 forall esk26_1:set -> set,
 forall k4_relat_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v4_funct_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall k10_funct_3:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall v1_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall k1_binop_1:set -> set -> set -> set,
 forall esk30_4:set -> set -> set -> set -> set,
 forall esk29_4:set -> set -> set -> set -> set,
     (forall X3 X2 X1 X4, (X1 = X4 -> False) -> (k9_xtuple_0 X4) = (k2_zfmisc_1 X2 X3) -> (k9_xtuple_0 X1) = (k2_zfmisc_1 X2 X3) -> (k1_binop_1 X1 (esk29_4 X2 X3 X1 X4) (esk30_4 X2 X3 X1 X4)) = (k1_binop_1 X4 (esk29_4 X2 X3 X1 X4) (esk30_4 X2 X3 X1 X4)) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X4 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, (X1 = (k13_funct_3 X2 X3) -> False) -> (k9_xtuple_0 X1) = (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> (k2_tarski (k2_tarski (k1_funct_1 X2 (esk7_3 X2 X3 X1)) (k1_funct_1 X3 (esk7_3 X2 X3 X1))) (k1_tarski (k1_funct_1 X2 (esk7_3 X2 X3 X1)))) = (k1_funct_1 X1 (esk7_3 X2 X3 X1)) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3 X4, (X3 = X4 -> False) -> (r2_hidden (esk30_4 X1 X2 X3 X4) X2 -> False) -> (k9_xtuple_0 X4) = (k2_zfmisc_1 X1 X2) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 X1 X2) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> False)
  -> (forall X2 X1 X3 X4, (X3 = X4 -> False) -> (r2_hidden (esk29_4 X1 X2 X3 X4) X1 -> False) -> (k9_xtuple_0 X4) = (k2_zfmisc_1 X1 X2) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 X1 X2) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_relat_1 X4 -> v1_relat_1 X3 -> False)
  -> (forall X3 X2 X1, (X1 = (k10_funct_3 X2 X3) -> False) -> (k9_xtuple_0 X1) = (k2_zfmisc_1 X2 X3) -> (k1_binop_1 X1 (esk5_3 X2 X3 X1) (esk6_3 X2 X3 X1)) = (esk6_3 X2 X3 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X3 X2 X1, (X1 = (k9_funct_3 X2 X3) -> False) -> (k9_xtuple_0 X1) = (k2_zfmisc_1 X2 X3) -> (k1_binop_1 X1 (esk3_3 X2 X3 X1) (esk4_3 X2 X3 X1)) = (esk3_3 X2 X3 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X3 X4 X2, ((k1_funct_1 X2 X1) = (k2_tarski (k2_tarski (k1_funct_1 X3 X1) (k1_funct_1 X4 X1)) (k1_tarski (k1_funct_1 X3 X1))) -> False) -> X2 = (k13_funct_3 X3 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X1 X3, (X3 = (k13_funct_3 X1 X2) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) (k9_xtuple_0 X3) -> False) -> (k9_xtuple_0 X3) = (k3_xboole_0 (k9_xtuple_0 X1) (k9_xtuple_0 X2)) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) (k2_zfmisc_1 X4 X2) -> False)
  -> (forall X2 X1 X3, (X3 = (k10_funct_3 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 X1 X2) -> v1_funct_1 X3 -> v1_relat_1 X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k10_funct_3 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 X1 X2) -> v1_funct_1 X3 -> v1_relat_1 X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k9_funct_3 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X2 -> False) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 X1 X2) -> v1_funct_1 X3 -> v1_relat_1 X3 -> False)
  -> (forall X2 X1 X3, (X3 = (k9_funct_3 X1 X2) -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X1 -> False) -> (k9_xtuple_0 X3) = (k2_zfmisc_1 X1 X2) -> v1_funct_1 X3 -> v1_relat_1 X3 -> False)
  -> (forall X4 X3 X2 X1, (r2_hidden (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) (k2_zfmisc_1 X2 X4) -> False) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X4 X2 X5 X3 X1, ((k1_binop_1 X5 X1 X3) = X1 -> False) -> X5 = (k9_funct_3 X2 X4) -> v1_funct_1 X5 -> v1_relat_1 X5 -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X4 X2 X5 X1 X3, ((k1_binop_1 X5 X1 X3) = X3 -> False) -> X5 = (k10_funct_3 X2 X4) -> v1_funct_1 X5 -> v1_relat_1 X5 -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1 X3, ((k9_xtuple_0 X1) = (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> False) -> X1 = (k13_funct_3 X2 X3) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, ((k9_xtuple_0 (k13_funct_3 X1 X2)) = X3 -> False) -> (k9_xtuple_0 X2) = X3 -> (k9_xtuple_0 X1) = X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_relat_1 (k13_funct_3 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k13_funct_3 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k13_funct_3 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k13_funct_3 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k13_funct_3 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k13_funct_3 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k13_funct_3 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k13_funct_3 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 X1) = (k2_zfmisc_1 X2 X3) -> False) -> X1 = (k10_funct_3 X2 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 X1) = (k2_zfmisc_1 X2 X3) -> False) -> X1 = (k9_funct_3 X2 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_funct_1 (k4_relat_1 X2) X1) = X1 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk26_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk12_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k4_relat_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k13_funct_3 (k9_funct_3 esk1_0 esk2_0) (k10_funct_3 esk1_0 esk2_0)) = (k4_relat_1 (k2_zfmisc_1 esk1_0 esk2_0)) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk20_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk23_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (k10_funct_3 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X2)) -> False) -> False)
  -> (forall X1 X2, (m1_subset_1 (k9_funct_3 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X1)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (k10_funct_3 X1 X2) (k2_zfmisc_1 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_funct_2 (k9_funct_3 X1 X2) (k2_zfmisc_1 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk11_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk11_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k10_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k9_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k10_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k10_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k9_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k9_funct_3 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k4_relat_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k9_xtuple_0 (k4_relat_1 X1)) = X1 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v2_funct_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (k4_relat_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk16_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk27_0 -> False) -> False)
  -> ((v2_relat_1 esk21_0 -> False) -> False)
  -> ((v2_relat_1 esk18_0 -> False) -> False)
  -> ((v2_relat_1 esk15_0 -> False) -> False)
  -> ((v2_funct_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> ((v1_relat_1 esk9_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
