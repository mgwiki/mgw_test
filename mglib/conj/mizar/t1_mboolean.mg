(** $I sig/MizarPreamble.mgs **)

Theorem t1_mboolean:
 forall r1_pboole:set -> set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall esk21_3:set -> set -> set -> set,
 forall k1_xboole_0:set,
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall esk17_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v2_relat_1:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall esk20_1:set -> set,
 forall v2_funcop_1:set -> prop,
 forall esk18_1:set -> set,
 forall esk14_0:set,
 forall k10_xtuple_0:set -> set,
 forall v2_funct_1:set -> prop,
 forall esk10_1:set -> set,
 forall esk13_0:set,
 forall esk11_0:set,
 forall esk19_1:set -> set,
 forall esk15_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall esk16_0:set,
 forall esk12_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall k1_relset_1:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall k1_funct_4:set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk3_0:set,
 forall r6_pboole:set -> set -> set -> prop,
 forall esk1_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk5_3:set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k1_mboolean:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall r2_pboole:set -> set -> set -> prop,
     (forall X1 X2 X3, (r2_pboole X2 X1 X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r1_tarski (k1_funct_1 X1 (esk9_3 X2 X1 X3)) (k1_funct_1 X3 (esk9_3 X2 X1 X3)) -> False)
  -> (forall X1 X2 X3, (r1_pboole X2 X1 X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r2_hidden (k1_funct_1 X1 (esk6_3 X2 X1 X3)) (k1_funct_1 X3 (esk6_3 X2 X1 X3)) -> False)
  -> (forall X1 X2 X3, (X1 = (k1_mboolean X2 X3) -> False) -> (k1_funct_1 X1 (esk5_3 X2 X3 X1)) = (k1_zfmisc_1 (k1_funct_1 X3 (esk5_3 X2 X3 X1))) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> (k1_funct_1 X1 (esk21_3 X2 X1 X3)) = (k1_funct_1 X3 (esk21_3 X2 X1 X3)) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_pboole X1 X2 X3 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (r1_pboole X1 X2 X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2 X4 X3, (r1_tarski (k1_funct_1 X2 X4) (k1_funct_1 X3 X4) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> r2_hidden X4 X1 -> r2_pboole X1 X2 X3 -> False)
  -> (forall X1 X2 X4 X3, (r2_hidden (k1_funct_1 X2 X4) (k1_funct_1 X3 X4) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> r2_hidden X4 X1 -> r1_pboole X1 X2 X3 -> False)
  -> (r1_pboole esk1_0 esk4_0 esk2_0 -> r2_pboole esk1_0 esk4_0 esk3_0 -> r6_pboole esk1_0 esk2_0 (k1_mboolean esk1_0 esk3_0) -> False)
  -> (forall X1 X2 X3, (r6_pboole X2 X3 X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r6_pboole X2 X1 X3 -> False)
  -> (forall X1, (r2_pboole esk1_0 X1 esk3_0 -> False) -> (r6_pboole esk1_0 esk2_0 (k1_mboolean esk1_0 esk3_0) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 esk1_0 -> v1_partfun1 X1 esk1_0 -> r1_pboole esk1_0 X1 esk2_0 -> False)
  -> (forall X1, (r1_pboole esk1_0 X1 esk2_0 -> False) -> (r6_pboole esk1_0 esk2_0 (k1_mboolean esk1_0 esk3_0) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 esk1_0 -> v1_partfun1 X1 esk1_0 -> r2_pboole esk1_0 X1 esk3_0 -> False)
  -> (forall X2 X1 X3, (X3 = (k1_mboolean X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (r2_hidden (esk21_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X4 X3 X2 X1, ((k9_xtuple_0 (k1_funct_4 X1 (k2_zfmisc_1 (k1_tarski X3) (k1_tarski X4)))) = X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> r2_hidden X3 X2 -> False)
  -> ((r1_pboole esk1_0 esk4_0 esk2_0 -> False) -> (r2_pboole esk1_0 esk4_0 esk3_0 -> False) -> r6_pboole esk1_0 esk2_0 (k1_mboolean esk1_0 esk3_0) -> False)
  -> (forall X2 X1 X3 X4, ((k1_funct_1 X1 X4) = (k1_zfmisc_1 (k1_funct_1 X3 X4)) -> False) -> X1 = (k1_mboolean X2 X3) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r2_hidden X4 X2 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> r6_pboole X1 X2 X3 -> False)
  -> (forall X3 X1 X2, (r6_pboole X3 X1 X2 -> False) -> X1 = X2 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (r2_pboole X2 X1 X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X2 X1, (r6_pboole X2 X1 X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, (r2_pboole X2 (k2_zfmisc_1 X2 (k1_tarski k1_xboole_0)) X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (X2 = (k1_zfmisc_1 X1) -> False) -> r2_hidden (esk8_2 X1 X2) X2 -> r1_tarski (esk8_2 X1 X2) X1 -> False)
  -> ((v1_partfun1 esk4_0 esk1_0 -> False) -> r6_pboole esk1_0 esk2_0 (k1_mboolean esk1_0 esk3_0) -> False)
  -> ((v4_relat_1 esk4_0 esk1_0 -> False) -> r6_pboole esk1_0 esk2_0 (k1_mboolean esk1_0 esk3_0) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> r6_pboole esk1_0 esk2_0 (k1_mboolean esk1_0 esk3_0) -> False)
  -> ((v1_relat_1 esk4_0 -> False) -> r6_pboole esk1_0 esk2_0 (k1_mboolean esk1_0 esk3_0) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k1_funct_4 X2 X1) X3) = (k1_funct_1 X1 X3) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X3 X1 X2, ((k1_funct_1 (k1_funct_4 X2 X1) X3) = (k1_funct_1 X2 X3) -> False) -> (r2_hidden X3 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk17_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2, (v1_partfun1 (k1_mboolean X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_partfun1 (k1_mboolean X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v4_relat_1 (k1_mboolean X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v4_relat_1 (k1_mboolean X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk7_2 X1 X2) = X1 -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k2_zfmisc_1 (k1_tarski X3) (k1_tarski X2)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v4_relat_1 (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X3)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v2_relat_1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (X2 = (k1_zfmisc_1 X1) -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> (r1_tarski (esk8_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k2_zfmisc_1 X3 (k1_tarski X2)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_funcop_1 (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X1)) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_partfun1 X2 X1 -> False) -> (k1_relset_1 X1 X2) = X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X1 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk7_2 X1 X2) = X1 -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_funcop_1 (k2_zfmisc_1 X2 (k1_tarski X1)) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (v4_relat_1 X1 X2 -> False) -> v1_relat_1 X1 -> r1_tarski (k9_xtuple_0 X1) X2 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski (k9_xtuple_0 X1) X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_relat_1 (k2_zfmisc_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> X2 = (k1_zfmisc_1 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k1_zfmisc_1 X2) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v5_relat_1 (esk17_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_partfun1 (esk17_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v4_relat_1 (esk17_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_funct_4 X1 X1) = X1 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk12_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk18_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_zfmisc_1 X1 (k1_tarski X2)) (k1_zfmisc_1 (k2_zfmisc_1 X1 (k1_tarski X2))) -> False) -> False)
  -> (forall X2 X1, (r1_tarski (k10_xtuple_0 (k2_zfmisc_1 X1 (k1_tarski X2))) (k1_tarski X2) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 (k1_tarski X2) -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) (k1_tarski X1) -> False) -> False)
  -> (forall X2 X1, ((k1_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) X1) = X2 -> False) -> False)
  -> (forall X1 X2, (v2_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_partfun1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (k2_zfmisc_1 X1 (k1_tarski k1_xboole_0)) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k2_zfmisc_1 X1 (k1_tarski k1_xboole_0)) X1 -> False) -> False)
  -> (forall X1 X2, ((k9_xtuple_0 (k2_zfmisc_1 X1 (k1_tarski X2))) = X1 -> False) -> False)
  -> (forall X1 X2, (v3_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (k2_zfmisc_1 k1_xboole_0 (k1_tarski X1)) -> False) -> False)
  -> (forall X1, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski k1_xboole_0)) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k2_zfmisc_1 X1 (k1_tarski k1_xboole_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v1_partfun1 esk3_0 esk1_0 -> False) -> False)
  -> ((v1_partfun1 esk2_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk3_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk15_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk19_1 X1) -> False) -> False)
  -> ((v3_funct_1 esk14_0 -> False) -> False)
  -> ((v1_funcop_1 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk11_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_relat_1 esk3_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> False.
Admitted.
