(** $I sig/MizarPreamble.mgs **)

Theorem t53_limfunc4:
 forall k1_numbers:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v3_limfunc1:set -> prop,
 forall k4_limfunc1:set -> set,
 forall esk8_2:set -> set -> set,
 forall k2_seq_2:set -> set,
 forall v2_comseq_2:set -> prop,
 forall r1_xxreal_0:set -> set -> prop,
 forall esk7_1:set -> set,
 forall esk4_2:set -> set -> set,
 forall v4_limfunc1:set -> prop,
 forall esk11_1:set -> set,
 forall v1_limfunc1:set -> prop,
 forall esk10_1:set -> set,
 forall esk6_1:set -> set,
 forall k10_xtuple_0:set -> set,
 forall k1_seq_2:set -> set,
 forall v1_xreal_0:set -> prop,
 forall esk9_2:set -> set -> set,
 forall k4_numbers:set,
 forall v5_membered:set -> prop,
 forall v4_valued_0:set -> prop,
 forall v6_membered:set -> prop,
 forall v2_valued_0:set -> prop,
 forall v2_membered:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v1_int_1:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall k4_ordinal1:set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall esk25_0:set,
 forall esk21_0:set,
 forall esk19_0:set,
 forall esk16_2:set -> set -> set,
 forall esk26_1:set -> set,
 forall esk23_1:set -> set,
 forall esk15_0:set,
 forall esk18_0:set,
 forall esk17_0:set,
 forall esk24_0:set,
 forall esk12_1:set -> set,
 forall esk13_2:set -> set -> set,
 forall esk14_0:set,
 forall esk20_0:set,
 forall esk22_0:set,
 forall v1_finset_1:set -> prop,
 forall v7_membered:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_membered:set -> prop,
 forall v1_valued_0:set -> prop,
 forall v3_membered:set -> prop,
 forall v3_valued_0:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v4_membered:set -> prop,
 forall k3_numbers:set,
 forall esk5_2:set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall k9_xtuple_0:set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall k3_relat_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk3_1:set -> set,
 forall v1_funct_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k2_relset_1:set -> set -> set,
 forall k1_relset_1:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k5_numbers:set,
 forall k8_funct_2:set -> set -> set -> set -> set -> set,
 forall k1_partfun1:set -> set -> set -> set -> set -> set -> set,
 forall r2_funct_2:set -> set -> set -> set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X1 X4 X6 X3 X5 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_funct_2 k5_numbers X6 (k8_funct_2 k5_numbers X6 X2 (k8_funct_2 k5_numbers X2 X1 X3 X4) X5) (k8_funct_2 k5_numbers X6 X1 X3 (k1_partfun1 X1 X2 X2 X6 X4 X5)) -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X3 k5_numbers X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 X6)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers X1)) -> r1_tarski (k2_relset_1 X1 X3) (k1_relset_1 X1 (k1_partfun1 X1 X2 X2 X6 X4 X5)) -> False)
  -> (forall X2 X1 X3, (r1_tarski (k2_relset_1 k1_numbers (k8_funct_2 k5_numbers k1_numbers k1_numbers X1 X2)) (k1_relset_1 k1_numbers X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers k1_numbers -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> r1_tarski (k2_relset_1 k1_numbers X1) (k1_relset_1 k1_numbers (k1_partfun1 k1_numbers k1_numbers k1_numbers k1_numbers X2 X3)) -> False)
  -> (forall X3 X1 X2, (r1_tarski (k2_relset_1 k1_numbers X1) (k1_relset_1 k1_numbers X2) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers k1_numbers -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> r1_tarski (k2_relset_1 k1_numbers X1) (k1_relset_1 k1_numbers (k1_partfun1 k1_numbers k1_numbers k1_numbers k1_numbers X2 X3)) -> False)
  -> ((k4_limfunc1 (k1_partfun1 k1_numbers k1_numbers k1_numbers k1_numbers esk1_0 esk2_0)) = (k4_limfunc1 esk2_0) -> v3_limfunc1 (k1_partfun1 k1_numbers k1_numbers k1_numbers k1_numbers esk1_0 esk2_0) -> False)
  -> (forall X1, (r2_hidden (esk3_1 X1) (k1_relset_1 k1_numbers (k1_partfun1 k1_numbers k1_numbers k1_numbers k1_numbers esk1_0 esk2_0)) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X5 X3 X4 X1 X2 X6, (m1_subset_1 (k1_partfun1 X1 X2 X3 X4 X5 X6) (k1_zfmisc_1 (k2_zfmisc_1 X1 X4)) -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X5 X3 X4 X1 X2 X6, (v1_funct_1 (k1_partfun1 X1 X2 X3 X4 X5 X6) -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X1, (v3_limfunc1 X1 -> False) -> (r1_xxreal_0 X3 (esk7_1 X1) -> False) -> (k2_seq_2 (k8_funct_2 k5_numbers k1_numbers k1_numbers (esk8_2 X1 X2) X1)) = X2 -> v1_funct_1 X1 -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X3 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> v2_comseq_2 (k8_funct_2 k5_numbers k1_numbers k1_numbers (esk8_2 X1 X2) X1) -> False)
  -> (forall X2 X1, (v3_limfunc1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) k1_numbers -> False) -> (k2_seq_2 (k8_funct_2 k5_numbers k1_numbers k1_numbers (esk8_2 X1 X2) X1)) = X2 -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> v2_comseq_2 (k8_funct_2 k5_numbers k1_numbers k1_numbers (esk8_2 X1 X2) X1) -> False)
  -> (forall X2 X1, (X2 = (k4_limfunc1 X1) -> False) -> (k2_seq_2 (k8_funct_2 k5_numbers k1_numbers k1_numbers (esk4_2 X1 X2) X1)) = X2 -> v1_funct_1 X1 -> v3_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> v2_comseq_2 (k8_funct_2 k5_numbers k1_numbers k1_numbers (esk4_2 X1 X2) X1) -> False)
  -> (forall X1 X5 X6 X2 X3 X4, ((k1_partfun1 X2 X3 X5 X6 X1 X4) = (k3_relat_1 X1 X4) -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v4_limfunc1 X1 -> False) -> (r1_xxreal_0 X2 (esk10_1 X1) -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> r2_hidden X2 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> v1_limfunc1 (k8_funct_2 k5_numbers k1_numbers k1_numbers (esk11_1 X1) X1) -> False)
  -> (forall X1, (v4_limfunc1 X1 -> False) -> (m1_subset_1 (esk10_1 X1) k1_numbers -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> v1_limfunc1 (k8_funct_2 k5_numbers k1_numbers k1_numbers (esk11_1 X1) X1) -> False)
  -> (forall X1 X3 X2, ((k2_seq_2 (k8_funct_2 k5_numbers k1_numbers k1_numbers X1 X2)) = X3 -> False) -> X3 = (k4_limfunc1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v3_limfunc1 X2 -> v1_limfunc1 X1 -> m1_subset_1 X3 k1_numbers -> v1_funct_2 X1 k5_numbers k1_numbers -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> r1_tarski (k2_relset_1 k1_numbers X1) (k1_relset_1 k1_numbers X2) -> False)
  -> (forall X3 X1 X2, (v2_comseq_2 (k8_funct_2 k5_numbers k1_numbers k1_numbers X1 X2) -> False) -> X3 = (k4_limfunc1 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v3_limfunc1 X2 -> v1_limfunc1 X1 -> m1_subset_1 X3 k1_numbers -> v1_funct_2 X1 k5_numbers k1_numbers -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> r1_tarski (k2_relset_1 k1_numbers X1) (k1_relset_1 k1_numbers X2) -> False)
  -> (forall X1 X2, ((k2_seq_2 (k8_funct_2 k5_numbers k1_numbers k1_numbers X1 X2)) = (esk6_1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v3_limfunc1 X2 -> v1_limfunc1 X1 -> v1_funct_2 X1 k5_numbers k1_numbers -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> r1_tarski (k2_relset_1 k1_numbers X1) (k1_relset_1 k1_numbers X2) -> False)
  -> (forall X1 X2, (v2_comseq_2 (k8_funct_2 k5_numbers k1_numbers k1_numbers X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v3_limfunc1 X2 -> v1_limfunc1 X1 -> v1_funct_2 X1 k5_numbers k1_numbers -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> r1_tarski (k2_relset_1 k1_numbers X1) (k1_relset_1 k1_numbers X2) -> False)
  -> (forall X1 X2, (v1_limfunc1 (k8_funct_2 k5_numbers k1_numbers k1_numbers X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_limfunc1 X2 -> v1_limfunc1 X1 -> v1_funct_2 X1 k5_numbers k1_numbers -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> r1_tarski (k2_relset_1 k1_numbers X1) (k1_relset_1 k1_numbers X2) -> False)
  -> (forall X5 X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 (k8_funct_2 X1 X2 X3 X4 X5) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_relat_1 X5 -> v5_relat_1 X5 X2 -> v1_funct_2 X4 X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X5 X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_2 (k8_funct_2 X1 X2 X3 X4 X5) X1 X2 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_relat_1 X5 -> v5_relat_1 X5 X2 -> v1_funct_2 X4 X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X5 X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k8_funct_2 X1 X2 X3 X4 X5) -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_relat_1 X5 -> v5_relat_1 X5 X2 -> v1_funct_2 X4 X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X3 X1 X2 X5, (v1_xboole_0 X5 -> False) -> (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X5 X4 -> v1_funct_2 X1 X3 X5 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X5 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> False)
  -> (forall X1 X4 X3 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X4 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X1 X2 X4 X5 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X5 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X3 X2 X1, (v3_limfunc1 X1 -> False) -> (r1_xxreal_0 X3 (esk7_1 X1) -> False) -> (r1_tarski (k2_relset_1 k1_numbers (esk8_2 X1 X2)) (k1_relset_1 k1_numbers X1) -> False) -> v1_funct_1 X1 -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X3 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v3_limfunc1 X1 -> False) -> (r1_xxreal_0 X3 (esk7_1 X1) -> False) -> (m1_subset_1 (esk8_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> False) -> v1_funct_1 X1 -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X3 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v3_limfunc1 X1 -> False) -> (r1_xxreal_0 X3 (esk7_1 X1) -> False) -> (v1_funct_2 (esk8_2 X1 X2) k5_numbers k1_numbers -> False) -> v1_funct_1 X1 -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X3 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X2 X1, (v4_limfunc1 X1 -> False) -> (r1_xxreal_0 X2 (esk10_1 X1) -> False) -> (r1_tarski (k2_relset_1 k1_numbers (esk11_1 X1)) (k1_relset_1 k1_numbers X1) -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> r2_hidden X2 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (v4_limfunc1 X1 -> False) -> (r1_xxreal_0 X2 (esk10_1 X1) -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> r2_hidden X2 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (v4_limfunc1 X1 -> False) -> (r1_xxreal_0 X2 (esk10_1 X1) -> False) -> (v1_funct_2 (esk11_1 X1) k5_numbers k1_numbers -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> r2_hidden X2 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (v3_limfunc1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) k1_numbers -> False) -> (r1_tarski (k2_relset_1 k1_numbers (esk8_2 X1 X2)) (k1_relset_1 k1_numbers X1) -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X3 X1, (v3_limfunc1 X1 -> False) -> (v1_limfunc1 (esk8_2 X1 X2) -> False) -> (r1_xxreal_0 X3 (esk7_1 X1) -> False) -> v1_funct_1 X1 -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X3 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X3 X1, (v3_limfunc1 X1 -> False) -> (v1_funct_1 (esk8_2 X1 X2) -> False) -> (r1_xxreal_0 X3 (esk7_1 X1) -> False) -> v1_funct_1 X1 -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> r2_hidden X3 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (X2 = (k4_limfunc1 X1) -> False) -> (r1_tarski (k2_relset_1 k1_numbers (esk4_2 X1 X2)) (k1_relset_1 k1_numbers X1) -> False) -> v1_funct_1 X1 -> v3_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (v3_limfunc1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) k1_numbers -> False) -> (m1_subset_1 (esk8_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v3_limfunc1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) k1_numbers -> False) -> (v1_funct_2 (esk8_2 X1 X2) k5_numbers k1_numbers -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1, (X2 = (k4_limfunc1 X1) -> False) -> (m1_subset_1 (esk4_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> False) -> v1_funct_1 X1 -> v3_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v4_limfunc1 X1 -> False) -> (v1_limfunc1 (esk11_1 X1) -> False) -> (r1_xxreal_0 X2 (esk10_1 X1) -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> r2_hidden X2 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (v4_limfunc1 X1 -> False) -> (v1_funct_1 (esk11_1 X1) -> False) -> (r1_xxreal_0 X2 (esk10_1 X1) -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> r2_hidden X2 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (X2 = (k4_limfunc1 X1) -> False) -> (v1_funct_2 (esk4_2 X1 X2) k5_numbers k1_numbers -> False) -> v1_funct_1 X1 -> v3_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X1, (m1_subset_1 (k2_seq_2 X1) k1_numbers -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> False)
  -> (forall X1, (v4_limfunc1 X1 -> False) -> (m1_subset_1 (esk10_1 X1) k1_numbers -> False) -> (r1_tarski (k2_relset_1 k1_numbers (esk11_1 X1)) (k1_relset_1 k1_numbers X1) -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X1, (v1_xreal_0 (k1_seq_2 X1) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> False)
  -> (forall X2 X1, v1_funct_1 X1 -> v3_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> r1_xxreal_0 (esk5_2 X1 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, v1_funct_1 X1 -> v4_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> r1_xxreal_0 (esk9_2 X1 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (r2_hidden (esk9_2 X1 X2) (k1_relset_1 k1_numbers X1) -> False) -> v1_funct_1 X1 -> v4_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (r2_hidden (esk5_2 X1 X2) (k1_relset_1 k1_numbers X1) -> False) -> v1_funct_1 X1 -> v3_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X1, (v4_limfunc1 X1 -> False) -> (m1_subset_1 (esk10_1 X1) k1_numbers -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X1, ((k2_seq_2 X1) = (k1_seq_2 X1) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 k5_numbers k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers k1_numbers)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1, (v4_limfunc1 X1 -> False) -> (m1_subset_1 (esk10_1 X1) k1_numbers -> False) -> (v1_funct_2 (esk11_1 X1) k5_numbers k1_numbers -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (v3_limfunc1 X1 -> False) -> (v1_limfunc1 (esk8_2 X1 X2) -> False) -> (m1_subset_1 (esk7_1 X1) k1_numbers -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (v3_limfunc1 X1 -> False) -> (v1_funct_1 (esk8_2 X1 X2) -> False) -> (m1_subset_1 (esk7_1 X1) k1_numbers -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk9_2 X1 X2) k1_numbers -> False) -> v1_funct_1 X1 -> v4_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk5_2 X1 X2) k1_numbers -> False) -> v1_funct_1 X1 -> v3_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (X2 = (k4_limfunc1 X1) -> False) -> (v1_limfunc1 (esk4_2 X1 X2) -> False) -> v1_funct_1 X1 -> v3_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (X2 = (k4_limfunc1 X1) -> False) -> (v1_funct_1 (esk4_2 X1 X2) -> False) -> v1_funct_1 X1 -> v3_limfunc1 X1 -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X1, (v4_limfunc1 X1 -> False) -> (v1_limfunc1 (esk11_1 X1) -> False) -> (m1_subset_1 (esk10_1 X1) k1_numbers -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X1, (v4_limfunc1 X1 -> False) -> (v1_funct_1 (esk11_1 X1) -> False) -> (m1_subset_1 (esk10_1 X1) k1_numbers -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X2 k3_numbers -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X2 k4_numbers -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) k1_numbers -> False) -> v1_funct_1 X1 -> v3_limfunc1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v4_valued_0 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v3_valued_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v2_valued_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v1_valued_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1, (m1_subset_1 (k4_limfunc1 X1) k1_numbers -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v5_relat_1 (k3_relat_1 X1 X2) k3_numbers -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 k3_numbers -> False)
  -> (forall X1 X2, (v5_relat_1 (k3_relat_1 X1 X2) k4_numbers -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 k4_numbers -> False)
  -> (forall X1 X2, (v5_relat_1 X2 k3_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_relat_1 X2 k4_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 k3_numbers -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 k4_numbers -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, m1_subset_1 X1 k1_numbers -> r1_xxreal_0 (esk3_1 X1) X1 -> False)
  -> (forall X1 X2, (v4_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_valued_0 X2 -> False)
  -> (forall X1 X2, (v3_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v3_valued_0 X2 -> False)
  -> (forall X1 X2, (v2_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_valued_0 X2 -> False)
  -> (forall X1 X2, (v1_valued_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_valued_0 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v3_valued_0 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_valued_0 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X2 -> False)
  -> (forall X1 X2, (v4_valued_0 X2 -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_valued_0 X2 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_valued_0 X2 -> False) -> v1_relat_1 X1 -> v2_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_valued_0 X2 -> False) -> v1_relat_1 X1 -> v1_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k2_relset_1 X2 X1) = (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v5_relat_1 (k2_zfmisc_1 X2 X1) k3_numbers -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v5_relat_1 (k2_zfmisc_1 X2 X1) k4_numbers -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v5_relat_1 X1 k3_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X1, (m1_subset_1 (esk3_1 X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v4_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X1, (v5_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X2 X1, (v4_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (v3_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v2_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v1_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1, (v4_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k5_numbers -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k1_numbers -> False)
  -> (forall X1, (v4_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k3_numbers) -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1, (v5_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k4_numbers) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v5_relat_1 X1 k3_numbers -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v5_relat_1 X1 k4_numbers -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v3_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X1, (v2_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X1, (v1_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_valued_0 X1 -> False)
  -> (forall X1, (v6_membered (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v4_valued_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v2_valued_0 X1 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X1, (v1_valued_0 X1 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_finset_1 k3_numbers -> False)
  -> (v1_finset_1 k4_numbers -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 k3_numbers -> False)
  -> (v1_xboole_0 k4_numbers -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk13_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False) -> False)
  -> ((m1_subset_1 esk1_0 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk13_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v5_ordinal1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v4_valued_0 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk23_1 X1) -> False) -> False)
  -> ((v7_membered esk22_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k3_numbers -> False) -> False)
  -> ((v7_membered k4_numbers -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v2_ordinal1 esk20_0 -> False) -> False)
  -> ((v1_ordinal1 esk20_0 -> False) -> False)
  -> ((v3_ordinal1 esk20_0 -> False) -> False)
  -> ((v3_ordinal1 esk15_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v7_ordinal1 esk25_0 -> False) -> False)
  -> ((v7_ordinal1 esk24_0 -> False) -> False)
  -> ((v4_valued_0 esk17_0 -> False) -> False)
  -> ((v4_membered k3_numbers -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v6_membered esk22_0 -> False) -> False)
  -> ((v6_membered esk19_0 -> False) -> False)
  -> ((v6_membered esk14_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v5_membered k4_numbers -> False) -> False)
  -> ((v3_limfunc1 esk2_0 -> False) -> False)
  -> ((v4_limfunc1 esk1_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_funct_1 esk1_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
