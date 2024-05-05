(** $I sig/MizarPreamble.mgs **)

Theorem t15_fdiff_10:
 forall esk1_0:set,
 forall k16_sin_cos:set,
 forall k19_sin_cos:set,
 forall k9_real_1:set -> set -> set,
 forall k5_square_1:set -> set,
 forall esk2_0:set,
 forall v3_membered:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_valued_0:set -> prop,
 forall k3_xcmplx_0:set -> set -> set,
 forall esk3_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall esk17_2:set -> set -> set,
 forall r1_fdiff_1:set -> set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k4_numbers:set,
 forall v5_membered:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall v3_valued_0:set -> prop,
 forall v1_membered:set -> prop,
 forall k4_xcmplx_0:set -> set,
 forall v7_ordinal1:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall np__1:set,
 forall v2_xxreal_0:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk12_0:set,
 forall esk6_0:set,
 forall np__2:set,
 forall np__0:set,
 forall esk9_0:set,
 forall esk15_0:set,
 forall k4_ordinal1:set,
 forall esk10_0:set,
 forall esk16_0:set,
 forall esk13_0:set,
 forall esk7_0:set,
 forall esk4_1:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk11_0:set,
 forall esk14_0:set,
 forall v7_membered:set -> prop,
 forall v3_xxreal_0:set -> prop,
 forall k3_square_1:set -> set,
 forall k5_numbers:set,
 forall k1_real_1:set -> set,
 forall k6_xcmplx_0:set -> set -> set,
 forall v1_int_1:set -> prop,
 forall esk5_2:set -> set -> set,
 forall v2_membered:set -> prop,
 forall v2_valued_0:set -> prop,
 forall v6_membered:set -> prop,
 forall v4_valued_0:set -> prop,
 forall v4_membered:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall k3_numbers:set,
 forall v1_xreal_0:set -> prop,
 forall k18_valued_1:set -> set -> set,
 forall v3_rcomp_1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k1_relset_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall r2_fdiff_1:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall k2_fdiff_1:set -> set -> set,
 forall k1_numbers:set,
 forall k20_valued_1:set -> set -> set -> set -> set -> set,
 forall k7_real_1:set -> set -> set,
 forall k8_real_1:set -> set -> set,
 forall k1_seq_1:set -> set -> set,
 forall k1_fdiff_1:set -> set -> set,
     (forall X4 X1 X3 X2, ((k1_seq_1 (k2_fdiff_1 (k20_valued_1 k1_numbers k1_numbers k1_numbers X3 X4) X2) X1) = (k7_real_1 (k8_real_1 (k1_seq_1 X4 X1) (k1_fdiff_1 X3 X1)) (k8_real_1 (k1_seq_1 X3 X1) (k1_fdiff_1 X4 X1))) -> False) -> v3_rcomp_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X3 -> r2_fdiff_1 X4 X2 -> r2_fdiff_1 X3 X2 -> r2_hidden X1 X2 -> m1_subset_1 X1 k1_numbers -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> r1_tarski X2 (k1_relset_1 k1_numbers (k20_valued_1 k1_numbers k1_numbers k1_numbers X3 X4)) -> False)
  -> ((k1_seq_1 (k2_fdiff_1 (k20_valued_1 k1_numbers k1_numbers k1_numbers k16_sin_cos k19_sin_cos) esk1_0) esk2_0) = (k9_real_1 (k5_square_1 (k1_seq_1 k19_sin_cos esk2_0)) (k5_square_1 (k1_seq_1 k16_sin_cos esk2_0))) -> r2_fdiff_1 (k20_valued_1 k1_numbers k1_numbers k1_numbers k16_sin_cos k19_sin_cos) esk1_0 -> False)
  -> (forall X2 X1 X3, (r2_fdiff_1 (k20_valued_1 k1_numbers k1_numbers k1_numbers X1 X2) X3 -> False) -> v3_rcomp_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_fdiff_1 X2 X3 -> r2_fdiff_1 X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> r1_tarski X3 (k1_relset_1 k1_numbers (k20_valued_1 k1_numbers k1_numbers k1_numbers X1 X2)) -> False)
  -> ((r2_hidden esk2_0 esk1_0 -> False) -> r2_fdiff_1 (k20_valued_1 k1_numbers k1_numbers k1_numbers k16_sin_cos k19_sin_cos) esk1_0 -> False)
  -> ((m1_subset_1 esk2_0 k1_numbers -> False) -> r2_fdiff_1 (k20_valued_1 k1_numbers k1_numbers k1_numbers k16_sin_cos k19_sin_cos) esk1_0 -> False)
  -> (forall X2 X4 X1 X5 X3, (m1_subset_1 (k20_valued_1 X1 X2 X3 X4 X5) (k1_zfmisc_1 (k2_zfmisc_1 X1 k1_numbers)) -> False) -> v3_membered X3 -> v3_membered X2 -> v1_funct_1 X5 -> v1_funct_1 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X4 X1 X5 X3, (v1_funct_1 (k20_valued_1 X1 X2 X3 X4 X5) -> False) -> v3_membered X3 -> v3_membered X2 -> v1_funct_1 X5 -> v1_funct_1 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X3 X4 X5 X2, ((k20_valued_1 X4 X1 X2 X3 X5) = (k20_valued_1 X4 X1 X2 X5 X3) -> False) -> v3_membered X2 -> v3_membered X1 -> v1_funct_1 X5 -> v1_funct_1 X3 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 X1)) -> False)
  -> (forall X1 X3 X4 X5 X2, ((k20_valued_1 X4 X1 X2 X3 X5) = (k18_valued_1 X3 X5) -> False) -> v3_membered X2 -> v3_membered X1 -> v1_funct_1 X5 -> v1_funct_1 X3 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 X1)) -> False)
  -> (forall X2 X1 X3, (X1 = (k18_valued_1 X2 X3) -> False) -> (k9_xtuple_0 X1) = (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> (k3_xcmplx_0 (k1_funct_1 X2 (esk3_3 X2 X3 X1)) (k1_funct_1 X3 (esk3_3 X2 X3 X1))) = (k1_funct_1 X1 (esk3_3 X2 X3 X1)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X3 -> v1_valued_0 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X1 X2, (r2_fdiff_1 X1 X2 -> False) -> v3_rcomp_1 X2 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> r1_fdiff_1 X1 (esk17_2 X2 X1) -> r1_tarski X2 (k1_relset_1 k1_numbers X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (r2_fdiff_1 X2 X1 -> False) -> (r2_hidden (esk17_2 X1 X2) X1 -> False) -> v3_rcomp_1 X1 -> v1_funct_1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> r1_tarski X1 (k1_relset_1 k1_numbers X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (r2_fdiff_1 X2 X1 -> False) -> (m1_subset_1 (esk17_2 X1 X2) k1_numbers -> False) -> v3_rcomp_1 X1 -> v1_funct_1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> r1_tarski X1 (k1_relset_1 k1_numbers X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1 X3, (X3 = (k18_valued_1 X1 X2) -> False) -> (r2_hidden (esk3_3 X1 X2 X3) (k9_xtuple_0 X3) -> False) -> (k9_xtuple_0 X3) = (k3_xboole_0 (k9_xtuple_0 X1) (k9_xtuple_0 X2)) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X2 -> v1_valued_0 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X3 X1, (r1_fdiff_1 X3 X1 -> False) -> v3_rcomp_1 X2 -> v1_funct_1 X3 -> r2_fdiff_1 X3 X2 -> r2_hidden X1 X2 -> m1_subset_1 X1 k1_numbers -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X2 X1, (r1_tarski X1 (k1_relset_1 k1_numbers X2) -> False) -> v3_rcomp_1 X1 -> v1_funct_1 X2 -> r2_fdiff_1 X2 X1 -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X1 X3 X4 X2, ((k1_funct_1 X2 X1) = (k3_xcmplx_0 (k1_funct_1 X3 X1) (k1_funct_1 X4 X1)) -> False) -> X2 = (k18_valued_1 X3 X4) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_valued_0 X4 -> v1_valued_0 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_fdiff_1 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_fdiff_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X2 k3_numbers -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X2 k4_numbers -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_funct_1 (k2_fdiff_1 X1 X2) -> False) -> v1_funct_1 X1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k3_xcmplx_0 X1 X3) (k3_xcmplx_0 X2 X3)) = (k3_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v4_valued_0 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v3_valued_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v2_valued_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X3 X2, (v1_valued_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk5_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X3, ((k9_xtuple_0 X1) = (k3_xboole_0 (k9_xtuple_0 X2) (k9_xtuple_0 X3)) -> False) -> X1 = (k18_valued_1 X2 X3) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X3 -> v1_valued_0 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 X2 -> False) -> r1_tarski X1 (k3_xboole_0 X2 X3) -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 (k18_valued_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X2 -> v1_valued_0 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k18_valued_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X2 -> v1_valued_0 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v5_relat_1 (k3_xboole_0 X1 X2) k3_numbers -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X2 X1, (v5_relat_1 (k3_xboole_0 X1 X2) k4_numbers -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X1 X2, (v5_relat_1 X2 k3_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_relat_1 X2 k4_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, ((k18_valued_1 X1 X2) = (k18_valued_1 X2 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X2 -> v1_valued_0 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k7_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k9_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (v1_int_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X2 X1, (v1_rat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_seq_1 X1 X2) k1_numbers -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, ((k9_real_1 X1 X2) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k8_real_1 X1 X2) = (k8_real_1 X2 X1) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k8_real_1 X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k7_real_1 X2 X1) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k7_real_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k6_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v4_valued_0 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xxreal_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v2_valued_0 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v3_valued_0 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_valued_0 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v2_valued_0 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_valued_0 X1 -> False)
  -> (forall X2 X1, (v1_valued_0 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_valued_0 X1 -> False)
  -> (forall X1 X2, (v4_valued_0 X2 -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_valued_0 X2 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_valued_0 X2 -> False) -> v1_relat_1 X1 -> v2_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_valued_0 X2 -> False) -> v1_relat_1 X1 -> v1_valued_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_funct_1 X1 X2) = (k1_seq_1 X1 X2) -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1, ((k1_real_1 (k1_seq_1 k16_sin_cos X1)) = (k1_fdiff_1 k19_sin_cos X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v5_relat_1 (k2_zfmisc_1 X2 X1) k3_numbers -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v5_relat_1 (k2_zfmisc_1 X2 X1) k4_numbers -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k3_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v5_relat_1 X1 k3_numbers -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X1, (m1_subset_1 (k1_real_1 X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (m1_subset_1 (k5_square_1 X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (v4_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k3_xboole_0 X1 X2) -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v4_membered (k3_xboole_0 X2 X1) -> False) -> v4_membered X1 -> False)
  -> (forall X2 X1, (v3_membered (k3_xboole_0 X1 X2) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v3_membered (k3_xboole_0 X2 X1) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k3_xboole_0 X1 X2) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v2_membered (k3_xboole_0 X2 X1) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v3_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v3_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k3_xboole_0 X1 X2) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (v1_membered (k3_xboole_0 X2 X1) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (v2_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v2_membered X1 -> False)
  -> (forall X2 X1, (v6_membered (k3_xboole_0 X1 X2) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (v6_membered (k3_xboole_0 X2 X1) -> False) -> v6_membered X1 -> False)
  -> (forall X2 X1, (v1_valued_0 (k2_zfmisc_1 X2 X1) -> False) -> v1_membered X1 -> False)
  -> (forall X2 X1, (v5_membered (k3_xboole_0 X1 X2) -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, (v5_membered (k3_xboole_0 X2 X1) -> False) -> v5_membered X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, ((k1_seq_1 k19_sin_cos X1) = (k1_fdiff_1 k16_sin_cos X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v4_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k5_numbers -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k3_numbers -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k4_numbers -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 k1_numbers -> False)
  -> (forall X1, (v4_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k3_numbers) -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1, (v5_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k4_numbers) -> False)
  -> (forall X1, ((k1_real_1 (k1_real_1 X1)) = X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, ((k1_real_1 X1) = (k4_xcmplx_0 X1) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, ((k5_square_1 X1) = (k3_square_1 X1) -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v5_relat_1 X1 k3_numbers -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v5_relat_1 X1 k4_numbers -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 X1) = (k3_square_1 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v3_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (r1_fdiff_1 k19_sin_cos X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (r1_fdiff_1 k16_sin_cos X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v4_valued_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_valued_0 X1 -> False) -> v1_relat_1 X1 -> v4_valued_0 X1 -> False)
  -> (forall X1, (v2_valued_0 X1 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X1, (v1_valued_0 X1 -> False) -> v1_relat_1 X1 -> v3_valued_0 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (v1_finset_1 k3_numbers -> False)
  -> (v1_finset_1 k4_numbers -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk6_0 -> False)
  -> (v1_xboole_0 k3_numbers -> False)
  -> (v1_xboole_0 k4_numbers -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> ((r1_tarski esk1_0 (k1_relset_1 k1_numbers (k20_valued_1 k1_numbers k1_numbers k1_numbers k16_sin_cos k19_sin_cos)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk8_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m1_subset_1 k19_sin_cos (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False) -> False)
  -> ((m1_subset_1 k16_sin_cos (k1_zfmisc_1 (k2_zfmisc_1 k1_numbers k1_numbers)) -> False) -> False)
  -> ((m2_subset_1 np__2 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((v1_funct_2 k19_sin_cos k1_numbers k1_numbers -> False) -> False)
  -> ((v1_funct_2 k16_sin_cos k1_numbers k1_numbers -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk8_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk8_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk8_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk8_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__2)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__2)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk4_1 X1) X1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 (k4_xcmplx_0 np__2) np__1) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 np__1 (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((m1_subset_1 esk12_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 esk7_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 esk1_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) np__2) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__2) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__2)) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__2) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__2) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((m1_subset_1 np__2 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__2 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__2) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__1) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__0) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 np__1) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__2) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__2) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 np__0) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__1) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__2) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__2)) = np__2 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v1_funct_1 esk9_0 -> False) -> False)
  -> ((v1_funct_1 k19_sin_cos -> False) -> False)
  -> ((v1_funct_1 k16_sin_cos -> False) -> False)
  -> ((v2_xxreal_0 esk13_0 -> False) -> False)
  -> ((v2_xxreal_0 np__2 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v3_xxreal_0 esk15_0 -> False) -> False)
  -> ((v7_membered esk14_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k3_numbers -> False) -> False)
  -> ((v7_membered k4_numbers -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 esk16_0 -> False) -> False)
  -> ((v4_valued_0 esk9_0 -> False) -> False)
  -> ((v4_membered k3_numbers -> False) -> False)
  -> ((v3_membered esk7_0 -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v1_xxreal_0 esk16_0 -> False) -> False)
  -> ((v1_xxreal_0 esk15_0 -> False) -> False)
  -> ((v1_xxreal_0 esk13_0 -> False) -> False)
  -> ((v1_xxreal_0 esk10_0 -> False) -> False)
  -> ((v2_membered esk7_0 -> False) -> False)
  -> ((v1_membered esk7_0 -> False) -> False)
  -> ((v6_membered esk14_0 -> False) -> False)
  -> ((v6_membered esk11_0 -> False) -> False)
  -> ((v6_membered esk6_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> ((v1_relat_1 esk9_0 -> False) -> False)
  -> ((v5_membered k4_numbers -> False) -> False)
  -> ((v3_rcomp_1 esk7_0 -> False) -> False)
  -> ((v3_rcomp_1 esk1_0 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
