(** $I sig/MizarPreamble.mgs **)

Theorem l13_projred1:
 forall r2_zfmisc_1:set -> set -> set -> set -> prop,
 forall esk7_0:set,
 forall esk1_0:set,
 forall esk23_3:set -> set -> set -> set,
 forall esk34_1:set -> set,
 forall esk35_1:set -> set,
 forall esk30_1:set -> set,
 forall esk33_1:set -> set,
 forall esk29_1:set -> set,
 forall esk28_1:set -> set,
 forall esk27_1:set -> set,
 forall esk26_1:set -> set,
 forall esk12_1:set -> set,
 forall esk10_1:set -> set,
 forall esk9_1:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk31_1:set -> set,
 forall v1_funct_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk20_0:set,
 forall esk2_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk6_0:set,
 forall esk19_0:set,
 forall esk16_0:set,
 forall esk18_0:set,
 forall esk17_1:set -> set,
 forall esk8_0:set,
 forall esk21_0:set,
 forall k1_xboole_0:set,
 forall v2_funct_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk11_1:set -> set,
 forall esk32_1:set -> set,
 forall esk15_1:set -> set,
 forall esk14_1:set -> set,
 forall esk13_3:set -> set -> set -> set,
 forall esk22_3:set -> set -> set -> set,
 forall v6_incsp_1:set -> prop,
 forall v2_incproj:set -> prop,
 forall l1_incsp_1:set -> prop,
 forall v3_incproj:set -> prop,
 forall v1_incproj:set -> prop,
 forall esk24_4:set -> set -> set -> set -> set,
 forall r1_incsp_1:set -> set -> set -> prop,
 forall esk25_10:set -> set -> set -> set -> set -> set -> set -> set -> set -> set -> set,
 forall epred1_1:set -> prop,
 forall u2_incsp_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_incsp_1:set -> set,
 forall v4_incproj:set -> prop,
     (forall X1 X6 X10 X3 X5 X4 X2 X11 X9 X7 X8, (X7 = X8 -> False) -> (r1_incsp_1 X1 X6 X10 -> False) -> (r1_incsp_1 X1 X6 X9 -> False) -> (r1_incsp_1 X1 (esk25_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X9 -> False) -> v4_incproj X1 -> epred1_1 X1 -> r1_incsp_1 X1 X6 X8 -> r1_incsp_1 X1 X6 X7 -> r1_incsp_1 X1 X5 X10 -> r1_incsp_1 X1 X5 X8 -> r1_incsp_1 X1 X4 X9 -> r1_incsp_1 X1 X4 X8 -> r1_incsp_1 X1 X3 X10 -> r1_incsp_1 X1 X3 X7 -> r1_incsp_1 X1 X2 X9 -> r1_incsp_1 X1 X2 X7 -> m1_subset_1 X11 (u1_incsp_1 X1) -> m1_subset_1 X10 (u2_incsp_1 X1) -> m1_subset_1 X9 (u2_incsp_1 X1) -> m1_subset_1 X8 (u2_incsp_1 X1) -> m1_subset_1 X7 (u2_incsp_1 X1) -> m1_subset_1 X6 (u1_incsp_1 X1) -> m1_subset_1 X5 (u1_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X1 X6 X10 X3 X5 X4 X2 X11 X9 X7 X8, (X7 = X8 -> False) -> (r1_incsp_1 X1 X6 X10 -> False) -> (r1_incsp_1 X1 X6 X9 -> False) -> (r1_incsp_1 X1 (esk25_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) X10 -> False) -> v4_incproj X1 -> epred1_1 X1 -> r1_incsp_1 X1 X6 X8 -> r1_incsp_1 X1 X6 X7 -> r1_incsp_1 X1 X5 X10 -> r1_incsp_1 X1 X5 X8 -> r1_incsp_1 X1 X4 X9 -> r1_incsp_1 X1 X4 X8 -> r1_incsp_1 X1 X3 X10 -> r1_incsp_1 X1 X3 X7 -> r1_incsp_1 X1 X2 X9 -> r1_incsp_1 X1 X2 X7 -> m1_subset_1 X11 (u1_incsp_1 X1) -> m1_subset_1 X10 (u2_incsp_1 X1) -> m1_subset_1 X9 (u2_incsp_1 X1) -> m1_subset_1 X8 (u2_incsp_1 X1) -> m1_subset_1 X7 (u2_incsp_1 X1) -> m1_subset_1 X6 (u1_incsp_1 X1) -> m1_subset_1 X5 (u1_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X1 X6 X10 X2 X4 X5 X3 X11 X9 X7 X8, (X7 = X8 -> False) -> (r1_incsp_1 X1 X6 X10 -> False) -> (r1_incsp_1 X1 X6 X9 -> False) -> (m1_subset_1 (esk25_10 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10) (u1_incsp_1 X1) -> False) -> v4_incproj X1 -> epred1_1 X1 -> r1_incsp_1 X1 X6 X8 -> r1_incsp_1 X1 X6 X7 -> r1_incsp_1 X1 X5 X10 -> r1_incsp_1 X1 X5 X8 -> r1_incsp_1 X1 X4 X9 -> r1_incsp_1 X1 X4 X8 -> r1_incsp_1 X1 X3 X10 -> r1_incsp_1 X1 X3 X7 -> r1_incsp_1 X1 X2 X9 -> r1_incsp_1 X1 X2 X7 -> m1_subset_1 X11 (u1_incsp_1 X1) -> m1_subset_1 X10 (u2_incsp_1 X1) -> m1_subset_1 X9 (u2_incsp_1 X1) -> m1_subset_1 X8 (u2_incsp_1 X1) -> m1_subset_1 X7 (u2_incsp_1 X1) -> m1_subset_1 X6 (u1_incsp_1 X1) -> m1_subset_1 X5 (u1_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X3 X1 X2 X4, r2_zfmisc_1 X1 X2 X3 X4 -> m1_subset_1 X4 (u1_incsp_1 esk1_0) -> m1_subset_1 X3 (u1_incsp_1 esk1_0) -> m1_subset_1 X2 (u1_incsp_1 esk1_0) -> m1_subset_1 X1 (u1_incsp_1 esk1_0) -> r1_incsp_1 esk1_0 X4 esk7_0 -> r1_incsp_1 esk1_0 X3 esk7_0 -> r1_incsp_1 esk1_0 X2 esk7_0 -> r1_incsp_1 esk1_0 X1 esk7_0 -> False)
  -> (forall X2 X3 X4 X1, (r1_incsp_1 X1 (esk24_4 X1 X2 X3 X4) X4 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X4 (u2_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X2 X3 X4 X1, (m1_subset_1 (esk24_4 X1 X2 X3 X4) (u1_incsp_1 X1) -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X4 (u2_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X2 X3 X4 X1, (esk24_4 X1 X2 X3 X4) = X2 -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X4 (u2_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X2 X3 X4 X1, (esk24_4 X1 X2 X3 X4) = X3 -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X4 (u2_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X3 X2 X1 X4 X5, (X4 = X5 -> False) -> (X2 = X3 -> False) -> v1_incproj X1 -> l1_incsp_1 X1 -> r1_incsp_1 X1 X3 X5 -> r1_incsp_1 X1 X3 X4 -> r1_incsp_1 X1 X2 X5 -> r1_incsp_1 X1 X2 X4 -> m1_subset_1 X5 (u2_incsp_1 X1) -> m1_subset_1 X4 (u2_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X3 X4 X1 X2, X1 = X2 -> r2_zfmisc_1 X1 X2 X3 X4 -> False)
  -> (forall X3 X4 X1 X2, X1 = X2 -> r2_zfmisc_1 X1 X3 X2 X4 -> False)
  -> (forall X3 X4 X1 X2, X1 = X2 -> r2_zfmisc_1 X1 X3 X4 X2 -> False)
  -> (forall X4 X3 X1 X2, X1 = X2 -> r2_zfmisc_1 X3 X1 X2 X4 -> False)
  -> (forall X4 X3 X1 X2, X1 = X2 -> r2_zfmisc_1 X3 X1 X4 X2 -> False)
  -> (forall X4 X3 X1 X2, X1 = X2 -> r2_zfmisc_1 X3 X4 X1 X2 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> r1_incsp_1 X1 (esk23_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> r1_incsp_1 X1 (esk22_3 X1 X2 X3) X3 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (r1_incsp_1 X1 (esk23_3 X1 X2 X3) X3 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (r1_incsp_1 X1 (esk22_3 X1 X2 X3) X2 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X2 X1 X3 X4, (X3 = X4 -> False) -> (X2 = X4 -> False) -> (X2 = X3 -> False) -> (X1 = X4 -> False) -> (X1 = X3 -> False) -> (X1 = X2 -> False) -> (r2_zfmisc_1 X1 X2 X3 X4 -> False) -> False)
  -> (forall X3 X2 X1, (r1_incsp_1 X1 X2 (esk13_3 X1 X2 X3) -> False) -> v6_incsp_1 X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X3 X2 X1, (r1_incsp_1 X1 X2 (esk13_3 X1 X3 X2) -> False) -> v6_incsp_1 X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (m1_subset_1 (esk23_3 X1 X2 X3) (u1_incsp_1 X1) -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (m1_subset_1 (esk22_3 X1 X2 X3) (u1_incsp_1 X1) -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X1 X2, (v6_incsp_1 X2 -> False) -> l1_incsp_1 X2 -> m1_subset_1 X1 (u2_incsp_1 X2) -> r1_incsp_1 X2 (esk14_1 X2) X1 -> r1_incsp_1 X2 (esk15_1 X2) X1 -> False)
  -> (forall X1 X2, (v4_incproj X2 -> False) -> epred1_1 X2 -> m1_subset_1 X1 (u1_incsp_1 X2) -> r1_incsp_1 X2 X1 (esk34_1 X2) -> r1_incsp_1 X2 X1 (esk35_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk13_3 X1 X2 X3) (u2_incsp_1 X1) -> False) -> v6_incsp_1 X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> epred1_1 X1 -> r1_incsp_1 X1 (esk30_1 X1) (esk35_1 X1) -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> epred1_1 X1 -> r1_incsp_1 X1 (esk30_1 X1) (esk34_1 X1) -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (r1_incsp_1 X1 (esk30_1 X1) (esk33_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (r1_incsp_1 X1 (esk30_1 X1) (esk32_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (r1_incsp_1 X1 (esk29_1 X1) (esk35_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (r1_incsp_1 X1 (esk29_1 X1) (esk33_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (r1_incsp_1 X1 (esk28_1 X1) (esk34_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (r1_incsp_1 X1 (esk28_1 X1) (esk33_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (r1_incsp_1 X1 (esk27_1 X1) (esk35_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (r1_incsp_1 X1 (esk27_1 X1) (esk32_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (r1_incsp_1 X1 (esk26_1 X1) (esk34_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (r1_incsp_1 X1 (esk26_1 X1) (esk32_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v1_incproj X1 -> False) -> (r1_incsp_1 X1 (esk10_1 X1) (esk12_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v1_incproj X1 -> False) -> (r1_incsp_1 X1 (esk10_1 X1) (esk11_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v1_incproj X1 -> False) -> (r1_incsp_1 X1 (esk9_1 X1) (esk12_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v1_incproj X1 -> False) -> (r1_incsp_1 X1 (esk9_1 X1) (esk11_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (m1_subset_1 (esk35_1 X1) (u2_incsp_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (m1_subset_1 (esk34_1 X1) (u2_incsp_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (m1_subset_1 (esk33_1 X1) (u2_incsp_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (m1_subset_1 (esk32_1 X1) (u2_incsp_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (m1_subset_1 (esk31_1 X1) (u1_incsp_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (m1_subset_1 (esk30_1 X1) (u1_incsp_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (m1_subset_1 (esk29_1 X1) (u1_incsp_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (m1_subset_1 (esk28_1 X1) (u1_incsp_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (m1_subset_1 (esk27_1 X1) (u1_incsp_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (m1_subset_1 (esk26_1 X1) (u1_incsp_1 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v1_incproj X1 -> False) -> (m1_subset_1 (esk12_1 X1) (u2_incsp_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v1_incproj X1 -> False) -> (m1_subset_1 (esk11_1 X1) (u2_incsp_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v1_incproj X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u1_incsp_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v1_incproj X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_incsp_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v6_incsp_1 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (u1_incsp_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v6_incsp_1 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (u1_incsp_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_incproj X1 -> False) -> (esk33_1 X1) = (esk32_1 X1) -> epred1_1 X1 -> False)
  -> (forall X1, (v1_incproj X1 -> False) -> (esk12_1 X1) = (esk11_1 X1) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v1_incproj X1 -> False) -> (esk10_1 X1) = (esk9_1 X1) -> l1_incsp_1 X1 -> False)
  -> (forall X1, l1_incsp_1 X1 -> v1_xboole_0 (u2_incsp_1 X1) -> False)
  -> (forall X1, l1_incsp_1 X1 -> v1_xboole_0 (u1_incsp_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (epred1_1 X1 -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v3_funct_1 esk20_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> ((r2_zfmisc_1 esk2_0 esk3_0 esk4_0 esk5_0 -> False) -> False)
  -> ((r1_incsp_1 esk1_0 esk8_0 esk7_0 -> False) -> False)
  -> ((r1_incsp_1 esk1_0 esk8_0 esk6_0 -> False) -> False)
  -> ((r1_incsp_1 esk1_0 esk5_0 esk6_0 -> False) -> False)
  -> ((r1_incsp_1 esk1_0 esk4_0 esk6_0 -> False) -> False)
  -> ((r1_incsp_1 esk1_0 esk3_0 esk6_0 -> False) -> False)
  -> ((r1_incsp_1 esk1_0 esk2_0 esk6_0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk8_0 (u1_incsp_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk7_0 (u2_incsp_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u2_incsp_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_incsp_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_incsp_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_incsp_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_incsp_1 esk1_0) -> False) -> False)
  -> ((v4_funct_1 esk21_0 -> False) -> False)
  -> ((v2_funct_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk19_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((l1_incsp_1 esk16_0 -> False) -> False)
  -> ((l1_incsp_1 esk1_0 -> False) -> False)
  -> ((v4_incproj esk1_0 -> False) -> False)
  -> ((v3_incproj esk1_0 -> False) -> False)
  -> ((v2_incproj esk1_0 -> False) -> False)
  -> ((v1_incproj esk1_0 -> False) -> False)
  -> ((v6_incsp_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
