(** $I sig/MizarPreamble.mgs **)

Theorem t78_bvfunc14:
 forall esk20_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk21_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk36_1:set -> set,
 forall esk27_1:set -> set,
 forall v2_funcop_1:set -> prop,
 forall k1_xboole_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk6_0:set,
 forall esk9_0:set,
 forall esk8_0:set,
 forall esk7_0:set,
 forall esk5_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk10_0:set,
 forall esk31_0:set,
 forall esk12_0:set,
 forall esk13_0:set,
 forall esk14_0:set,
 forall esk15_0:set,
 forall esk16_0:set,
 forall esk17_0:set,
 forall esk18_0:set,
 forall esk19_0:set,
 forall esk11_0:set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk34_1:set -> set,
 forall esk25_1:set -> set,
 forall esk28_0:set,
 forall esk26_0:set,
 forall esk30_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall esk29_0:set,
 forall esk33_1:set -> set,
 forall esk35_1:set -> set,
 forall esk37_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v1_funcop_1:set -> prop,
 forall esk23_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk32_2:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk22_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k1_funct_4:set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall esk24_10:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k7_enumset1:set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
     (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (X10 = (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> ((esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X9 -> False) -> ((esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X8 -> False) -> ((esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X7 -> False) -> ((esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X6 -> False) -> ((esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X5 -> False) -> ((esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X4 -> False) -> ((esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X3 -> False) -> ((esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X2 -> False) -> ((esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X1 -> False) -> (r2_hidden (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False) -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (X10 = (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X1 -> r2_hidden (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (X10 = (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X2 -> r2_hidden (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (X10 = (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X3 -> r2_hidden (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (X10 = (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X4 -> r2_hidden (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (X10 = (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X5 -> r2_hidden (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (X10 = (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X6 -> r2_hidden (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (X10 = (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X7 -> r2_hidden (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (X10 = (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X8 -> r2_hidden (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False)
  -> (forall X10 X2 X4 X6 X8 X9 X7 X5 X3 X1, (X10 = (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False) -> (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) = X9 -> r2_hidden (esk24_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False)
  -> (forall X10 X8 X6 X4 X2 X3 X5 X7 X9 X1 X11, (X1 = X11 -> False) -> (X1 = X10 -> False) -> (X1 = X9 -> False) -> (X1 = X8 -> False) -> (X1 = X7 -> False) -> (X1 = X6 -> False) -> (X1 = X5 -> False) -> (X1 = X4 -> False) -> (X1 = X3 -> False) -> X2 = (k7_enumset1 X3 X4 X5 X6 X7 X8 X9 X10 X11) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X5 X7 X9 X10 X11 X8 X6 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k7_enumset1 X2 X4 X5 X6 X7 X8 X9 X10 X11) -> False)
  -> (forall X2 X4 X5 X7 X9 X10 X11 X8 X6 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k7_enumset1 X4 X2 X5 X6 X7 X8 X9 X10 X11) -> False)
  -> (forall X2 X4 X7 X9 X10 X11 X8 X6 X5 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k7_enumset1 X4 X5 X2 X6 X7 X8 X9 X10 X11) -> False)
  -> (forall X2 X4 X6 X7 X9 X10 X11 X8 X5 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k7_enumset1 X4 X5 X6 X2 X7 X8 X9 X10 X11) -> False)
  -> (forall X2 X4 X6 X9 X10 X11 X8 X7 X5 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k7_enumset1 X4 X5 X6 X7 X2 X8 X9 X10 X11) -> False)
  -> (forall X2 X4 X6 X8 X9 X10 X11 X7 X5 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k7_enumset1 X4 X5 X6 X7 X8 X2 X9 X10 X11) -> False)
  -> (forall X2 X4 X6 X8 X10 X11 X9 X7 X5 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k7_enumset1 X4 X5 X6 X7 X8 X9 X2 X10 X11) -> False)
  -> (forall X2 X4 X6 X8 X10 X11 X9 X7 X5 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k7_enumset1 X4 X5 X6 X7 X8 X9 X10 X2 X11) -> False)
  -> (forall X2 X4 X6 X8 X10 X11 X9 X7 X5 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k7_enumset1 X4 X5 X6 X7 X8 X9 X10 X11 X2) -> False)
  -> (forall X17 X13 X9 X5 X3 X7 X11 X15 X19 X2 X6 X10 X16 X14 X12 X8 X4 X18 X1, ((k9_xtuple_0 X1) = (k7_enumset1 X18 X2 X4 X6 X8 X10 X12 X14 X16) -> False) -> X1 = (k1_funct_4 (k1_funct_4 (k1_funct_4 (k1_funct_4 (k1_funct_4 (k1_funct_4 (k1_funct_4 (k1_funct_4 (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X3)) (k2_zfmisc_1 (k1_tarski X4) (k1_tarski X5))) (k2_zfmisc_1 (k1_tarski X6) (k1_tarski X7))) (k2_zfmisc_1 (k1_tarski X8) (k1_tarski X9))) (k2_zfmisc_1 (k1_tarski X10) (k1_tarski X11))) (k2_zfmisc_1 (k1_tarski X12) (k1_tarski X13))) (k2_zfmisc_1 (k1_tarski X14) (k1_tarski X15))) (k2_zfmisc_1 (k1_tarski X16) (k1_tarski X17))) (k2_zfmisc_1 (k1_tarski X18) (k1_tarski X19))) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk20_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk20_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk21_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk21_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, (v1_partfun1 (k1_funct_4 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v1_partfun1 (k1_funct_4 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k1_funct_4 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k1_funct_4 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k1_funct_4 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k1_funct_4 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v5_relat_1 X2 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk22_2 X1 X2)) = (esk21_2 X1 X2) -> False) -> (r2_hidden (esk21_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk21_2 X1 X2) X2 -> False) -> (r2_hidden (esk22_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v5_relat_1 X2 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v5_relat_1 X2 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk32_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v4_relat_1 (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X3)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k2_zfmisc_1 (k1_tarski X3) (k1_tarski X2)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, ((k1_funct_4 (k1_funct_4 X1 X2) X2) = (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_xboole_0 (k1_funct_4 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_xboole_0 (k1_funct_4 X1 X2) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k2_zfmisc_1 X3 (k1_tarski X2)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk23_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (v2_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_relat_1 X2 -> v2_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funcop_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_relat_1 X2 -> v2_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_relat_1 X2 -> v2_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X2 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_funcop_1 (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X1)) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_funcop_1 (k2_zfmisc_1 X2 (k1_tarski X1)) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk23_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, ((k1_funct_4 X1 X2) = X1 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X1 X2, ((k1_funct_4 X2 X1) = X1 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_relat_1 (k2_zfmisc_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_partfun1 (esk32_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v4_relat_1 (esk32_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v5_relat_1 (esk32_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_funct_4 X1 X1) = X1 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk32_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (esk32_2 X1 X2) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk35_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk37_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk36_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk36_1 X1) -> False) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X4 X6 X9 X8 X7 X5 X3 X1, v1_xboole_0 (k7_enumset1 X1 X2 X3 X4 X5 X6 X7 X8 X9) -> False)
  -> ((k7_enumset1 (k1_funct_1 esk10_0 esk1_0) (k1_funct_1 esk10_0 esk2_0) (k1_funct_1 esk10_0 esk3_0) (k1_funct_1 esk10_0 esk4_0) (k1_funct_1 esk10_0 esk5_0) (k1_funct_1 esk10_0 esk6_0) (k1_funct_1 esk10_0 esk7_0) (k1_funct_1 esk10_0 esk8_0) (k1_funct_1 esk10_0 esk9_0)) = (k10_xtuple_0 esk10_0) -> False)
  -> (forall X1, v1_subset_1 (esk33_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (((k1_funct_4 (k1_funct_4 (k1_funct_4 (k1_funct_4 (k1_funct_4 (k1_funct_4 (k1_funct_4 (k1_funct_4 (k2_zfmisc_1 (k1_tarski esk2_0) (k1_tarski esk12_0)) (k2_zfmisc_1 (k1_tarski esk3_0) (k1_tarski esk13_0))) (k2_zfmisc_1 (k1_tarski esk4_0) (k1_tarski esk14_0))) (k2_zfmisc_1 (k1_tarski esk5_0) (k1_tarski esk15_0))) (k2_zfmisc_1 (k1_tarski esk6_0) (k1_tarski esk16_0))) (k2_zfmisc_1 (k1_tarski esk7_0) (k1_tarski esk17_0))) (k2_zfmisc_1 (k1_tarski esk8_0) (k1_tarski esk18_0))) (k2_zfmisc_1 (k1_tarski esk9_0) (k1_tarski esk19_0))) (k2_zfmisc_1 (k1_tarski esk1_0) (k1_tarski esk11_0))) = esk10_0 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_zfmisc_1 X1 (k1_tarski X2)) (k1_zfmisc_1 (k2_zfmisc_1 X1 (k1_tarski X2))) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 (k1_tarski X2) -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) (k1_tarski X1) -> False) -> False)
  -> (forall X1 X2, (v2_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_partfun1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, (v3_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (k2_zfmisc_1 k1_xboole_0 (k1_tarski X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk34_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk34_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk34_1 X1) -> False) -> False)
  -> ((v3_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funcop_1 esk26_0 -> False) -> False)
  -> ((v1_xboole_0 esk28_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk26_0 -> False) -> False)
  -> ((v1_funct_1 esk10_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> False.
Admitted.
