(** $I sig/MizarPreamble.mgs **)

Theorem t44_fuzzy_2:
 forall k1_funct_1:set -> set -> set,
 forall esk20_4:set -> set -> set -> set -> set,
 forall k1_relset_1:set -> set -> set,
 forall r2_funct_2:set -> set -> set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k1_fuzzy_1:set -> set -> set -> set,
 forall k1_square_1:set -> set -> set,
 forall r1_xxreal_0:set -> set -> prop,
 forall k9_xtuple_0:set -> set,
 forall v1_relat_1:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k3_numbers:set,
 forall v4_membered:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v4_valued_0:set -> prop,
 forall v6_membered:set -> prop,
 forall v2_valued_0:set -> prop,
 forall v2_membered:set -> prop,
 forall esk7_2:set -> set -> set,
 forall k4_xxreal_0:set -> set -> set,
 forall v1_xreal_0:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k5_numbers:set,
 forall esk19_1:set -> set,
 forall v7_membered:set -> prop,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall np__0:set,
 forall v1_finset_1:set -> prop,
 forall esk16_0:set,
 forall esk9_0:set,
 forall esk6_1:set -> set,
 forall esk12_0:set,
 forall esk13_0:set,
 forall k4_ordinal1:set,
 forall esk15_1:set -> set,
 forall esk10_2:set -> set -> set,
 forall esk8_0:set,
 forall esk14_0:set,
 forall esk17_0:set,
 forall esk18_1:set -> set,
 forall esk11_1:set -> set,
 forall v1_measure5:set -> prop,
 forall v6_xxreal_2:set -> prop,
 forall k1_xxreal_1:set -> set -> set,
 forall v2_xxreal_0:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v1_int_1:set -> prop,
 forall k3_xxreal_0:set -> set -> set,
 forall k3_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall v1_membered:set -> prop,
 forall v1_valued_0:set -> prop,
 forall v3_membered:set -> prop,
 forall v3_valued_0:set -> prop,
 forall v5_membered:set -> prop,
 forall k4_numbers:set,
 forall k1_xboole_0:set,
 forall k2_square_1:set -> set -> set,
 forall k2_fuzzy_1:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall np__1:set,
 forall k6_numbers:set,
 forall k1_rcomp_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k1_numbers:set,
 forall k8_real_1:set -> set -> set,
 forall esk5_4:set -> set -> set -> set -> set,
 forall k1_seq_1:set -> set -> set,
 forall k2_fuzzy_2:set -> set -> set -> set,
     (forall X4 X1 X3 X2, (X1 = (k2_fuzzy_2 X2 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (k8_real_1 (k1_seq_1 X3 (esk5_4 X2 X3 X4 X1)) (k1_seq_1 X4 (esk5_4 X2 X3 X4 X1))) = (k1_seq_1 X1 (esk5_4 X2 X3 X4 X1)) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 k1_numbers -> v1_funct_2 X3 X2 k1_numbers -> v1_funct_2 X1 X2 k1_numbers -> v5_relat_1 X4 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X1 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 k1_numbers)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k1_numbers)) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> (k1_relset_1 X2 X1) = (k1_relset_1 X2 X4) -> (k1_funct_1 X1 (esk20_4 X2 X3 X1 X4)) = (k1_funct_1 X4 (esk20_4 X2 X3 X1 X4)) -> v1_funct_1 X4 -> v1_funct_1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X2 X3 X1, (X4 = (k2_fuzzy_2 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk5_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k1_numbers -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X4 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X4 X1 X5, ((k1_seq_1 X1 X5) = (k8_real_1 (k1_seq_1 X3 X5) (k1_seq_1 X4 X5)) -> False) -> (v1_xboole_0 X2 -> False) -> X1 = (k2_fuzzy_2 X2 X3 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X5 X2 -> v1_funct_2 X4 X2 k1_numbers -> v1_funct_2 X3 X2 k1_numbers -> v1_funct_2 X1 X2 k1_numbers -> v5_relat_1 X4 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X1 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 k1_numbers)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k1_numbers)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (r2_hidden (esk20_4 X1 X2 X3 X4) (k1_relset_1 X1 X3) -> False) -> (k1_relset_1 X1 X3) = (k1_relset_1 X1 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> (m1_subset_1 (esk20_4 X1 X2 X3 X4) X1 -> False) -> (k1_relset_1 X1 X3) = (k1_relset_1 X1 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X1 X4, ((k2_square_1 (k1_seq_1 X1 X2) (k1_seq_1 X3 X2)) = (k1_seq_1 (k2_fuzzy_1 X4 X1 X3) X2) -> False) -> (v1_xboole_0 X4 -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X2 X4 -> v1_funct_2 X3 X4 k1_numbers -> v1_funct_2 X1 X4 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X1 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 k1_numbers)) -> False)
  -> (forall X3 X2 X1 X4, ((k1_square_1 (k1_seq_1 X1 X2) (k1_seq_1 X3 X2)) = (k1_seq_1 (k1_fuzzy_1 X4 X1 X3) X2) -> False) -> (v1_xboole_0 X4 -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X2 X4 -> v1_funct_2 X3 X4 k1_numbers -> v1_funct_2 X1 X4 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X1 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_fuzzy_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_fuzzy_2 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_fuzzy_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k2_fuzzy_1 X1 X2 X3) X1 k1_numbers -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k2_fuzzy_2 X1 X2 X3) X1 k1_numbers -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k1_fuzzy_1 X1 X2 X3) X1 k1_numbers -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k2_fuzzy_1 X1 X2 X3) (k1_rcomp_1 k6_numbers np__1) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k2_fuzzy_2 X1 X2 X3) (k1_rcomp_1 k6_numbers np__1) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (k1_fuzzy_1 X1 X2 X3) (k1_rcomp_1 k6_numbers np__1) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k2_fuzzy_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k2_fuzzy_2 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k1_fuzzy_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, ((k2_fuzzy_1 X1 X2 X3) = (k2_fuzzy_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, ((k2_fuzzy_2 X1 X2 X3) = (k2_fuzzy_2 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X2 X1, ((k1_fuzzy_1 X1 X2 X3) = (k1_fuzzy_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X1 X2, ((k2_fuzzy_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X3 X1 X2, ((k1_fuzzy_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k1_numbers -> v1_funct_2 X2 X1 k1_numbers -> v5_relat_1 X3 (k1_rcomp_1 k6_numbers np__1) -> v5_relat_1 X2 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False)
  -> (forall X1 X2 X3, (v1_xboole_0 X3 -> False) -> (r1_xxreal_0 (k1_seq_1 X1 X2) np__1 -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 X3 -> v1_funct_2 X1 X3 k1_numbers -> v5_relat_1 X1 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 k1_numbers)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r1_xxreal_0 k6_numbers (k1_seq_1 X1 X2) -> False) -> v1_funct_1 X1 -> m1_subset_1 X2 X3 -> v1_funct_2 X1 X3 k1_numbers -> v5_relat_1 X1 (k1_rcomp_1 k6_numbers np__1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 k1_numbers)) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> ((k1_relset_1 X2 X1) = X2 -> False) -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (X1 = k1_xboole_0 -> False) -> X3 = k1_xboole_0 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v1_funct_2 X2 X1 X3 -> False) -> (k1_relset_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1 X3, ((k1_square_1 (k8_real_1 X3 X1) (k8_real_1 X3 X2)) = (k8_real_1 X3 (k1_square_1 X1 X2)) -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> r1_xxreal_0 k6_numbers X3 -> False)
  -> (forall X1 X2 X3, (v1_funct_2 X1 X2 X3 -> False) -> X3 = k1_xboole_0 -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X2 k3_numbers -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X2 k4_numbers -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X1 X3 X2, (v4_valued_0 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v3_valued_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v2_valued_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v1_valued_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk7_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_square_1 X1 X2) k1_numbers -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_square_1 X1 X2) k1_numbers -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v5_relat_1 X2 k3_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_relat_1 X2 k4_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k2_square_1 X1 X2) = (k4_xxreal_0 X1 X2) -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k1_square_1 X1 X2) = (k3_xxreal_0 X1 X2) -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k2_square_1 X1 X2) = (k2_square_1 X2 X1) -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k1_square_1 X1 X2) = (k1_square_1 X2 X1) -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (v1_int_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X2 X1, (v1_rat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_seq_1 X1 X2) k1_numbers -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_rcomp_1 X1 X2) (k1_zfmisc_1 k1_numbers) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, ((k2_square_1 X1 X1) = X1 -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k1_square_1 X1 X1) = X1 -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k8_real_1 X1 X2) = (k8_real_1 X2 X1) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k8_real_1 X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (v7_ordinal1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_xxreal_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_valued_0 X1 -> False)
  -> (forall X1 X2, (v4_valued_0 X2 -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_valued_0 X2 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_valued_0 X2 -> False) -> v1_relat_1 X1 -> v2_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_valued_0 X2 -> False) -> v1_relat_1 X1 -> v1_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_seq_1 X1 X2) = (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
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
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k1_xxreal_1 X1 X2) = (k1_rcomp_1 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, ((k4_xxreal_0 X1 X2) = (k4_xxreal_0 X2 X1) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, ((k3_xxreal_0 X1 X2) = (k3_xxreal_0 X2 X1) -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v5_relat_1 X1 k3_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X1, (v6_xxreal_2 X1 -> False) -> v1_measure5 X1 -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v1_measure5 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X2 X1, (v4_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (v3_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v2_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v1_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v4_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k5_numbers -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k1_numbers -> False)
  -> (forall X1, (v4_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k3_numbers) -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1, (v5_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k4_numbers) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k4_xxreal_0 X1 X1) = X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, ((k3_xxreal_0 X1 X1) = X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v5_relat_1 X1 k3_numbers -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v5_relat_1 X1 k4_numbers -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk11_1 X1) -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v4_valued_0 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v2_valued_0 X1 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X1, (v1_valued_0 X1 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_funct_2 esk1_0 k1_numbers (k2_fuzzy_2 esk1_0 esk2_0 (k1_fuzzy_1 esk1_0 esk3_0 esk4_0)) (k1_fuzzy_1 esk1_0 (k2_fuzzy_2 esk1_0 esk2_0 esk3_0) (k2_fuzzy_2 esk1_0 esk2_0 esk4_0)) -> False)
  -> (forall X1, v1_subset_1 (esk18_1 X1) X1 -> False)
  -> (r1_xxreal_0 np__1 np__0 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_finset_1 k3_numbers -> False)
  -> (v1_finset_1 k4_numbers -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (v1_xboole_0 esk8_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (v1_xboole_0 k3_numbers -> False)
  -> (v1_xboole_0 k4_numbers -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk10_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k1_numbers)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k1_numbers)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k1_numbers)) -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((v1_funct_2 esk4_0 esk1_0 k1_numbers -> False) -> False)
  -> ((v1_funct_2 esk3_0 esk1_0 k1_numbers -> False) -> False)
  -> ((v1_funct_2 esk2_0 esk1_0 k1_numbers -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk10_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk10_2 X1 X2) X2 -> False) -> False)
  -> ((v5_relat_1 esk4_0 (k1_rcomp_1 k6_numbers np__1) -> False) -> False)
  -> ((v5_relat_1 esk3_0 (k1_rcomp_1 k6_numbers np__1) -> False) -> False)
  -> ((v5_relat_1 esk2_0 (k1_rcomp_1 k6_numbers np__1) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk10_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk10_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk8_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__0 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk15_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v7_membered esk17_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k3_numbers -> False) -> False)
  -> ((v7_membered k4_numbers -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v1_measure5 esk8_0 -> False) -> False)
  -> ((v4_valued_0 esk12_0 -> False) -> False)
  -> ((v4_membered k3_numbers -> False) -> False)
  -> ((v3_membered esk8_0 -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v2_membered esk8_0 -> False) -> False)
  -> ((v1_membered esk8_0 -> False) -> False)
  -> ((v6_membered esk17_0 -> False) -> False)
  -> ((v6_membered esk14_0 -> False) -> False)
  -> ((v6_membered esk9_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v5_membered k4_numbers -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> ((k1_xboole_0 = k6_numbers -> False) -> False)
  -> False.
Admitted.