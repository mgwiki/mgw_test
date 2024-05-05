(** $I sig/MizarPreamble.mgs **)

Theorem t4_pzfmisc1:
 forall k1_pzfmisc1:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall r6_pboole:set -> set -> set -> prop,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall v1_finset_1:set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall esk7_2:set -> set -> set,
 forall v2_finset_1:set -> prop,
 forall k1_relset_1:set -> set -> set,
 forall esk19_2:set -> set -> set,
 forall v5_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk20_1:set -> set,
 forall v2_funcop_1:set -> prop,
 forall k10_xtuple_0:set -> set,
 forall k1_xboole_0:set,
 forall esk22_0:set,
 forall esk15_0:set,
 forall esk13_0:set,
 forall esk17_1:set -> set,
 forall esk10_0:set,
 forall esk11_0:set,
 forall esk8_1:set -> set,
 forall esk18_2:set -> set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk9_0:set,
 forall esk14_0:set,
 forall esk21_0:set,
 forall esk12_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v1_funcop_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk16_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall k1_funct_4:set -> set -> set,
 forall esk23_3:set -> set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall r1_pboole:set -> set -> set -> prop,
     (forall X1 X2 X3, (r1_pboole X2 X1 X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r2_hidden (k1_funct_1 X1 (esk5_3 X2 X1 X3)) (k1_funct_1 X3 (esk5_3 X2 X1 X3)) -> False)
  -> (forall X1 X2 X3, (X1 = (k1_pzfmisc1 X2 X3) -> False) -> (k1_funct_1 X1 (esk6_3 X2 X3 X1)) = (k1_tarski (k1_funct_1 X3 (esk6_3 X2 X3 X1))) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> (k1_funct_1 X1 (esk23_3 X2 X1 X3)) = (k1_funct_1 X3 (esk23_3 X2 X1 X3)) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r1_pboole X1 X2 X3 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2 X4 X3, (r2_hidden (k1_funct_1 X2 X4) (k1_funct_1 X3 X4) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> r2_hidden X4 X1 -> r1_pboole X1 X2 X3 -> False)
  -> (r6_pboole esk1_0 esk4_0 esk3_0 -> r1_pboole esk1_0 esk4_0 esk2_0 -> r6_pboole esk1_0 esk2_0 (k1_pzfmisc1 esk1_0 esk3_0) -> False)
  -> (forall X1 X2 X3, (r6_pboole X2 X3 X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r6_pboole X2 X1 X3 -> False)
  -> (forall X1, (r1_pboole esk1_0 X1 esk2_0 -> False) -> (r6_pboole esk1_0 esk2_0 (k1_pzfmisc1 esk1_0 esk3_0) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 esk1_0 -> v1_partfun1 X1 esk1_0 -> r6_pboole esk1_0 X1 esk3_0 -> False)
  -> (forall X1, (r6_pboole esk1_0 X1 esk3_0 -> False) -> (r6_pboole esk1_0 esk2_0 (k1_pzfmisc1 esk1_0 esk3_0) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 esk1_0 -> v1_partfun1 X1 esk1_0 -> r1_pboole esk1_0 X1 esk2_0 -> False)
  -> (forall X2 X1 X3, (X3 = (k1_pzfmisc1 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (r2_hidden (esk23_3 X1 X2 X3) X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X3 X2 X1, (v1_finset_1 X1 -> False) -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X3 X2 X1, ((k9_xtuple_0 (k1_funct_4 X1 (k2_zfmisc_1 (k1_tarski X3) (k1_tarski X4)))) = X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> r2_hidden X3 X2 -> False)
  -> ((r6_pboole esk1_0 esk4_0 esk3_0 -> False) -> (r1_pboole esk1_0 esk4_0 esk2_0 -> False) -> r6_pboole esk1_0 esk2_0 (k1_pzfmisc1 esk1_0 esk3_0) -> False)
  -> (forall X2 X1 X3 X4, ((k1_funct_1 X1 X4) = (k1_tarski (k1_funct_1 X3 X4)) -> False) -> X1 = (k1_pzfmisc1 X2 X3) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r2_hidden X4 X2 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> r6_pboole X1 X2 X3 -> False)
  -> (forall X3 X1 X2, (r6_pboole X3 X1 X2 -> False) -> X1 = X2 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (r6_pboole X2 X1 X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> ((v1_partfun1 esk4_0 esk1_0 -> False) -> r6_pboole esk1_0 esk2_0 (k1_pzfmisc1 esk1_0 esk3_0) -> False)
  -> ((v4_relat_1 esk4_0 esk1_0 -> False) -> r6_pboole esk1_0 esk2_0 (k1_pzfmisc1 esk1_0 esk3_0) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> r6_pboole esk1_0 esk2_0 (k1_pzfmisc1 esk1_0 esk3_0) -> False)
  -> ((v1_relat_1 esk4_0 -> False) -> r6_pboole esk1_0 esk2_0 (k1_pzfmisc1 esk1_0 esk3_0) -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k1_funct_4 X2 X1) X3) = (k1_funct_1 X1 X3) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X3 X1 X2, ((k1_funct_1 (k1_funct_4 X2 X1) X3) = (k1_funct_1 X2 X3) -> False) -> (r2_hidden X3 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2, (v1_partfun1 (k1_pzfmisc1 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_partfun1 (k1_pzfmisc1 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v4_relat_1 (k1_pzfmisc1 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v4_relat_1 (k1_pzfmisc1 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk7_2 X1 X2) = X1 -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k2_zfmisc_1 (k1_tarski X3) (k1_tarski X2)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v4_relat_1 (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X3)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v2_relat_1 (k1_pzfmisc1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v2_finset_1 (k1_pzfmisc1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_pzfmisc1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_pzfmisc1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_pzfmisc1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_pzfmisc1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k2_zfmisc_1 X3 (k1_tarski X2)) X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False)
  -> (forall X2 X1, (v1_funcop_1 (k2_zfmisc_1 (k1_tarski X2) (k1_tarski X1)) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_partfun1 X2 X1 -> False) -> (k1_relset_1 X1 X2) = X1 -> v1_relat_1 X2 -> v4_relat_1 X2 X1 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk7_2 X1 X2) = X1 -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_funct_4 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_funcop_1 (k2_zfmisc_1 X2 (k1_tarski X1)) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk19_2 X1 X2) -> False)
  -> (forall X2 X1, (v4_relat_1 X1 X2 -> False) -> v1_relat_1 X1 -> r1_tarski (k9_xtuple_0 X1) X2 -> False)
  -> (forall X2 X1, (v1_finset_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski (k9_xtuple_0 X1) X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_relat_1 (k2_zfmisc_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_partfun1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_zfmisc_1 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_funct_4 X1 X1) = X1 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_finset_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk20_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk12_1 X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_tarski X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk20_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk12_1 X1) -> False) -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_zfmisc_1 X1 (k1_tarski X2)) (k1_zfmisc_1 (k2_zfmisc_1 X1 (k1_tarski X2))) -> False) -> False)
  -> (forall X2 X1, (r1_tarski (k10_xtuple_0 (k2_zfmisc_1 X1 (k1_tarski X2))) (k1_tarski X2) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 (k1_tarski X2) -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) (k1_tarski X1) -> False) -> False)
  -> (forall X2 X1, ((k1_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) X1) = X2 -> False) -> False)
  -> (forall X1 X2, (v2_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 (k1_tarski X1) (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_partfun1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) X1 -> False) -> False)
  -> (forall X1 X2, ((k9_xtuple_0 (k2_zfmisc_1 X1 (k1_tarski X2))) = X1 -> False) -> False)
  -> (forall X1 X2, (v3_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 (k1_tarski X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk18_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk18_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (k2_zfmisc_1 k1_xboole_0 (k1_tarski X1)) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v1_partfun1 esk3_0 esk1_0 -> False) -> False)
  -> ((v1_partfun1 esk2_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk3_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 (k1_tarski X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk17_1 X1) -> False) -> False)
  -> ((v3_funct_1 esk13_0 -> False) -> False)
  -> ((v2_finset_1 esk22_0 -> False) -> False)
  -> ((v5_finset_1 esk21_0 -> False) -> False)
  -> ((v1_funcop_1 esk10_0 -> False) -> False)
  -> ((v1_finset_1 esk21_0 -> False) -> False)
  -> ((v1_finset_1 esk15_0 -> False) -> False)
  -> ((v1_finset_1 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((v1_funct_1 esk13_0 -> False) -> False)
  -> ((v1_funct_1 esk10_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> ((v1_relat_1 esk3_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> False.
Admitted.
