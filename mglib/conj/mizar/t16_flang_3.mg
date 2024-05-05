(** $I sig/MizarPreamble.mgs **)

Theorem t16_flang_3:
 forall esk8_4:set -> set -> set -> set -> set,
 forall esk7_4:set -> set -> set -> set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall k7_flang_1:set -> set -> set -> set,
 forall esk34_4:set -> set -> set -> set -> set,
 forall k1_flang_3:set -> set -> set -> set,
 forall v7_ordinal1:set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall r1_xxreal_0:set -> set -> prop,
 forall k3_tarski:set -> set,
 forall v1_xboole_0:set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v1_xreal_0:set -> prop,
 forall esk12_2:set -> set -> set,
 forall np__1:set,
 forall v1_xcmplx_0:set -> prop,
 forall v3_xxreal_0:set -> prop,
 forall k7_xcmplx_0:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall esk30_1:set -> set,
 forall m1_catalan2:set -> set -> prop,
 forall k4_ordinal1:set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk26_1:set -> set,
 forall esk33_0:set,
 forall esk21_0:set,
 forall esk22_1:set -> set,
 forall esk10_1:set -> set,
 forall esk11_1:set -> set,
 forall esk25_0:set,
 forall esk27_0:set,
 forall esk32_0:set,
 forall esk28_0:set,
 forall esk19_0:set,
 forall esk18_0:set,
 forall esk29_0:set,
 forall esk17_0:set,
 forall esk15_0:set,
 forall esk31_0:set,
 forall esk24_0:set,
 forall esk20_0:set,
 forall esk23_0:set,
 forall np__0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall v4_funct_1:set -> prop,
 forall esk36_1:set -> set,
 forall k6_numbers:set,
 forall esk16_1:set -> set,
 forall k1_xboole_0:set,
 forall v6_ordinal1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v1_afinsq_1:set -> prop,
 forall k4_xcmplx_0:set -> set,
 forall k6_xcmplx_0:set -> set -> set,
 forall v2_xxreal_0:set -> prop,
 forall esk9_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v5_ordinal1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_numbers:set,
 forall k1_nat_1:set -> set -> set,
 forall k5_numbers:set,
 forall esk35_2:set -> set -> set,
 forall k1_ordinal4:set -> set -> set,
 forall a_3_0_flang_3:set -> set -> set -> set,
 forall esk14_4:set -> set -> set -> set -> set,
 forall esk13_4:set -> set -> set -> set -> set,
 forall k6_flang_1:set -> set -> set -> set,
 forall k8_afinsq_1:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k1_flang_1:set -> set -> set -> set,
 forall esk5_5:set -> set -> set -> set -> set -> set,
 forall esk4_5:set -> set -> set -> set -> set -> set,
     (forall X1 X4 X3 X2 X5, ((k1_flang_1 X2 (esk4_5 X2 X3 X4 X5 X1) (esk5_5 X2 X3 X4 X5 X1)) = X1 -> False) -> X5 = (k6_flang_1 X2 X3 X4) -> r2_hidden X1 X5 -> m1_subset_1 X5 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False)
  -> (forall X5 X3 X2 X1 X4, (m1_subset_1 (esk5_5 X1 X2 X3 X4 X5) (k8_afinsq_1 X1) -> False) -> X4 = (k6_flang_1 X1 X2 X3) -> r2_hidden X5 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> False)
  -> (forall X5 X3 X2 X1 X4, (m1_subset_1 (esk4_5 X1 X2 X3 X4 X5) (k8_afinsq_1 X1) -> False) -> X4 = (k6_flang_1 X1 X2 X3) -> r2_hidden X5 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> False)
  -> (forall X5 X3 X2 X1 X4, (r2_hidden (esk5_5 X1 X2 X3 X4 X5) X3 -> False) -> X4 = (k6_flang_1 X1 X2 X3) -> r2_hidden X5 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> False)
  -> (forall X5 X3 X2 X1 X4, (r2_hidden (esk4_5 X1 X2 X3 X4 X5) X2 -> False) -> X4 = (k6_flang_1 X1 X2 X3) -> r2_hidden X5 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> False)
  -> (forall X2 X3 X4 X1, (X4 = (k6_flang_1 X1 X2 X3) -> False) -> ((k1_flang_1 X1 (esk7_4 X1 X2 X3 X4) (esk8_4 X1 X2 X3 X4)) = (esk6_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk6_4 X1 X2 X3 X4) X4 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> False)
  -> (forall X6 X5 X3 X2 X1 X4, (X4 = (k6_flang_1 X1 X2 X3) -> False) -> (esk6_4 X1 X2 X3 X4) = (k1_flang_1 X1 X5 X6) -> r2_hidden X6 X3 -> r2_hidden X5 X2 -> m1_subset_1 X6 (k8_afinsq_1 X1) -> m1_subset_1 X5 (k8_afinsq_1 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> r2_hidden (esk6_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 (k7_flang_1 X2 X3 (esk34_4 X2 X1 X3 X4)) -> False) -> v7_ordinal1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> r2_hidden X1 (k1_flang_3 X2 X3 X4) -> False)
  -> (forall X2 X3 X4 X1, (X4 = (k6_flang_1 X1 X2 X3) -> False) -> (r2_hidden (esk6_4 X1 X2 X3 X4) X4 -> False) -> (m1_subset_1 (esk8_4 X1 X2 X3 X4) (k8_afinsq_1 X1) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> False)
  -> (forall X2 X3 X4 X1, (X4 = (k6_flang_1 X1 X2 X3) -> False) -> (r2_hidden (esk6_4 X1 X2 X3 X4) X4 -> False) -> (m1_subset_1 (esk7_4 X1 X2 X3 X4) (k8_afinsq_1 X1) -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> False)
  -> (forall X2 X3 X4 X1, (X4 = (k6_flang_1 X1 X2 X3) -> False) -> (r2_hidden (esk6_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk8_4 X1 X2 X3 X4) X3 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> False)
  -> (forall X2 X3 X4 X1, (X4 = (k6_flang_1 X1 X2 X3) -> False) -> (r2_hidden (esk6_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk7_4 X1 X2 X3 X4) X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> False)
  -> (forall X2 X3 X1 X4, ((k7_flang_1 X2 X3 (esk14_4 X1 X2 X3 X4)) = (esk13_4 X1 X2 X3 X4) -> False) -> v7_ordinal1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> r2_hidden X1 (a_3_0_flang_3 X2 X3 X4) -> False)
  -> (forall X5 X3 X1 X4 X2 X6, (r2_hidden (k1_flang_1 X2 X3 X4) (k7_flang_1 X2 X1 (k2_xcmplx_0 X5 X6)) -> False) -> v7_ordinal1 X6 -> v7_ordinal1 X5 -> m1_subset_1 X4 (k8_afinsq_1 X2) -> m1_subset_1 X3 (k8_afinsq_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> r2_hidden X4 (k7_flang_1 X2 X1 X6) -> r2_hidden X3 (k7_flang_1 X2 X1 X5) -> False)
  -> (forall X2 X3 X1 X4, (m1_subset_1 (esk13_4 X1 X2 X3 X4) (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False) -> v7_ordinal1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> r2_hidden X1 (a_3_0_flang_3 X2 X3 X4) -> False)
  -> (forall X2 X4 X3 X1, (r1_xxreal_0 X1 (esk34_4 X2 X3 X4 X1) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> r2_hidden X3 (k1_flang_3 X2 X4 X1) -> False)
  -> (forall X3 X4 X2 X1, (r1_xxreal_0 X1 (esk14_4 X2 X3 X4 X1) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X3)) -> r2_hidden X2 (a_3_0_flang_3 X3 X4 X1) -> False)
  -> (forall X1 X3 X2 X4, (v7_ordinal1 (esk34_4 X1 X2 X3 X4) -> False) -> v7_ordinal1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X1)) -> r2_hidden X2 (k1_flang_3 X1 X3 X4) -> False)
  -> (forall X2 X3 X1 X4, (v7_ordinal1 (esk14_4 X1 X2 X3 X4) -> False) -> v7_ordinal1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> r2_hidden X1 (a_3_0_flang_3 X2 X3 X4) -> False)
  -> (forall X2 X3 X1 X4, ((esk13_4 X1 X2 X3 X4) = X1 -> False) -> v7_ordinal1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> r2_hidden X1 (a_3_0_flang_3 X2 X3 X4) -> False)
  -> (forall X2 X4 X5 X3 X1 X6 X7, (r2_hidden X6 X7 -> False) -> X7 = (k6_flang_1 X2 X4 X5) -> X6 = (k1_flang_1 X2 X1 X3) -> r2_hidden X3 X5 -> r2_hidden X1 X4 -> m1_subset_1 X3 (k8_afinsq_1 X2) -> m1_subset_1 X1 (k8_afinsq_1 X2) -> m1_subset_1 X7 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False)
  -> (forall X3 X2 X1 X4, ((k6_flang_1 X2 (k7_flang_1 X2 X1 X3) (k7_flang_1 X2 X1 X4)) = (k7_flang_1 X2 X1 (k2_xcmplx_0 X3 X4)) -> False) -> v7_ordinal1 X4 -> v7_ordinal1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False)
  -> (forall X1 X2 X5 X4 X3, (r2_hidden X3 (k1_flang_3 X4 X5 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X2 X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k8_afinsq_1 X4)) -> r2_hidden X3 (k7_flang_1 X4 X5 X1) -> False)
  -> (forall X1 X4 X5 X6 X2 X3, (r2_hidden X3 (a_3_0_flang_3 X2 X6 X5) -> False) -> X1 = X3 -> X1 = (k7_flang_1 X2 X6 X4) -> v7_ordinal1 X5 -> v7_ordinal1 X4 -> r1_xxreal_0 X5 X4 -> m1_subset_1 X6 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k6_flang_1 X2 X1 X3) (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False)
  -> (forall X1 X2 X3, ((k3_tarski (a_3_0_flang_3 X2 X1 X3)) = (k1_flang_3 X2 X1 X3) -> False) -> v7_ordinal1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False)
  -> (forall X1 X2 X3, (m1_subset_1 (k7_flang_1 X2 X1 X3) (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False) -> v7_ordinal1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False)
  -> (forall X1 X2 X3, (m1_subset_1 (k1_flang_3 X2 X1 X3) (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False) -> v7_ordinal1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k1_flang_1 X2 X1 X3) (k8_afinsq_1 X2) -> False) -> m1_subset_1 X3 (k8_afinsq_1 X2) -> m1_subset_1 X1 (k8_afinsq_1 X2) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 X1 X3 -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 (k2_xcmplx_0 X1 X2) (k2_xcmplx_0 X3 X2) -> False)
  -> (forall X3 X2 X1, ((k1_flang_1 X2 X1 X3) = (k1_ordinal4 X1 X3) -> False) -> m1_subset_1 X3 (k8_afinsq_1 X2) -> m1_subset_1 X1 (k8_afinsq_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk12_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 (k2_xcmplx_0 X1 X3) (k2_xcmplx_0 X2 X3) -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk35_2 X3 X2) -> False)
  -> (forall X2 X1, ((k7_flang_1 X2 X1 np__1) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k8_afinsq_1 X2)) -> False)
  -> (forall X1 X2, (m2_subset_1 (k1_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_ordinal4 X1 X2) -> False) -> v5_ordinal1 X2 -> v5_ordinal1 X1 -> v1_finset_1 X2 -> v1_finset_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_ordinal4 X1 X2) -> False) -> v5_ordinal1 X2 -> v5_ordinal1 X1 -> v1_finset_1 X2 -> v1_finset_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_finset_1 (k1_ordinal4 X1 X2) -> False) -> v5_ordinal1 X2 -> v5_ordinal1 X1 -> v1_finset_1 X2 -> v1_finset_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v5_ordinal1 (k1_ordinal4 X1 X2) -> False) -> v5_ordinal1 X2 -> v5_ordinal1 X1 -> v1_finset_1 X2 -> v1_finset_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_ordinal4 X1 X2) -> False) -> v5_ordinal1 X2 -> v5_ordinal1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_ordinal4 X1 X2) -> False) -> v5_ordinal1 X2 -> v5_ordinal1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v5_ordinal1 (k1_ordinal4 X1 X2) -> False) -> v5_ordinal1 X2 -> v5_ordinal1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k6_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k6_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1, (r2_hidden (esk35_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k6_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k6_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, ((k1_nat_1 X1 X2) = (k1_nat_1 X2 X1) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2, ((k1_nat_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k6_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_finset_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_afinsq_1 X1 -> v4_relat_1 X1 k5_numbers -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k7_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k6_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k1_ordinal4 k1_xboole_0 X1) = X1 -> False) -> v5_ordinal1 X1 -> v1_finset_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, ((k1_ordinal4 X1 k1_xboole_0) = X1 -> False) -> v5_ordinal1 X1 -> v1_finset_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v4_relat_1 X1 k5_numbers -> False) -> v5_ordinal1 X1 -> v1_finset_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k8_afinsq_1 X2) -> False)
  -> (forall X2 X1, (v5_ordinal1 X1 -> False) -> m1_subset_1 X1 (k8_afinsq_1 X2) -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_afinsq_1 X1 -> False) -> v5_ordinal1 X1 -> v1_finset_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> m1_catalan2 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v3_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v2_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, (X1 = k6_numbers -> False) -> ((k1_nat_1 (esk36_1 X1) np__1) = X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, (v4_funct_1 X1 -> False) -> m1_catalan2 X1 X2 -> False)
  -> (forall X1, (v1_afinsq_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 X1 np__1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k6_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 k6_numbers X1) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (X1 = k6_numbers -> False) -> (v7_ordinal1 (esk36_1 X1) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k3_tarski X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k6_flang_1 esk1_0 (k1_flang_3 esk1_0 esk2_0 esk3_0) esk2_0) = (k1_flang_3 esk1_0 esk2_0 (k2_xcmplx_0 esk3_0 np__1)) -> False)
  -> (forall X1, v1_subset_1 (esk26_1 X1) X1 -> False)
  -> (r1_xxreal_0 np__0 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__1 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__1 np__0 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k8_afinsq_1 X1) -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k8_afinsq_1 esk1_0)) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (m1_catalan2 (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_catalan2 (k8_afinsq_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k7_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__0 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__1 -> False) -> False)
  -> ((m1_subset_1 esk20_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__0 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> (((k7_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__1) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k8_afinsq_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk22_1 X1) -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v2_xxreal_0 esk25_0 -> False) -> False)
  -> ((v2_xxreal_0 esk24_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v1_xcmplx_0 esk31_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk27_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk24_0 -> False) -> False)
  -> ((v1_xxreal_0 esk32_0 -> False) -> False)
  -> ((v1_xxreal_0 esk31_0 -> False) -> False)
  -> ((v1_xxreal_0 esk28_0 -> False) -> False)
  -> ((v1_xxreal_0 esk27_0 -> False) -> False)
  -> ((v1_xxreal_0 esk25_0 -> False) -> False)
  -> ((v1_xxreal_0 esk24_0 -> False) -> False)
  -> ((v1_xxreal_0 esk19_0 -> False) -> False)
  -> ((v3_xxreal_0 esk28_0 -> False) -> False)
  -> ((v3_xxreal_0 esk27_0 -> False) -> False)
  -> ((v1_xreal_0 esk31_0 -> False) -> False)
  -> ((v1_xreal_0 esk27_0 -> False) -> False)
  -> ((v1_xreal_0 esk24_0 -> False) -> False)
  -> ((v1_xreal_0 esk18_0 -> False) -> False)
  -> ((v2_ordinal1 esk21_0 -> False) -> False)
  -> ((v1_ordinal1 esk21_0 -> False) -> False)
  -> ((v3_ordinal1 esk21_0 -> False) -> False)
  -> ((v3_ordinal1 esk20_0 -> False) -> False)
  -> ((v3_ordinal1 esk15_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk32_0 -> False) -> False)
  -> ((v1_xboole_0 esk31_0 -> False) -> False)
  -> ((v1_xboole_0 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v7_ordinal1 esk33_0 -> False) -> False)
  -> ((v7_ordinal1 esk29_0 -> False) -> False)
  -> ((v7_ordinal1 esk3_0 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
