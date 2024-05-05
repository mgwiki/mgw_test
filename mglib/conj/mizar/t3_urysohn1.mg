(** $I sig/MizarPreamble.mgs **)

Theorem t3_urysohn1:
 forall esk2_3:set -> set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v1_int_1:set -> prop,
 forall v5_membered:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v3_membered:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall v1_membered:set -> prop,
 forall esk24_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall v2_xxreal_0:set -> prop,
 forall k1_newton:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk21_1:set -> set,
 forall v7_membered:set -> prop,
 forall np__0:set,
 forall v1_finset_1:set -> prop,
 forall esk14_0:set,
 forall esk7_0:set,
 forall esk13_1:set -> set,
 forall k4_ordinal1:set,
 forall esk20_0:set,
 forall esk16_0:set,
 forall esk22_0:set,
 forall esk10_0:set,
 forall esk11_0:set,
 forall o_0_0_xboole_0:set,
 forall esk9_0:set,
 forall esk23_0:set,
 forall esk15_0:set,
 forall esk19_0:set,
 forall esk5_1:set -> set,
 forall esk12_0:set,
 forall esk17_0:set,
 forall esk18_1:set -> set,
 forall k1_xboole_0:set,
 forall k6_numbers:set,
 forall esk8_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k10_real_1:set -> set -> set,
 forall v3_xxreal_0:set -> prop,
 forall k7_xcmplx_0:set -> set -> set,
 forall k2_nat_1:set -> set -> set,
 forall np__1:set,
 forall k1_nat_1:set -> set -> set,
 forall k13_newton:set -> set -> set,
 forall k3_xcmplx_0:set -> set -> set,
 forall k2_xcmplx_0:set -> set -> set,
 forall v6_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v4_membered:set -> prop,
 forall v1_rat_1:set -> prop,
 forall esk3_2:set -> set -> set,
 forall k6_real_1:set -> set -> set,
 forall k2_newton:set -> set -> set,
 forall np__2:set,
 forall k5_numbers:set,
 forall r1_xxreal_0:set -> set -> prop,
 forall k1_numbers:set,
 forall v7_ordinal1:set -> prop,
 forall k1_urysohn1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k8_domain_1:set -> set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk1_4:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k1_enumset1:set -> set -> set -> set,
     (forall X4 X2 X3 X1, (X4 = (k1_enumset1 X1 X2 X3) -> False) -> ((esk1_4 X1 X2 X3 X4) = X3 -> False) -> ((esk1_4 X1 X2 X3 X4) = X2 -> False) -> ((esk1_4 X1 X2 X3 X4) = X1 -> False) -> (r2_hidden (esk1_4 X1 X2 X3 X4) X4 -> False) -> False)
  -> (forall X4 X2 X3 X1, (X4 = (k1_enumset1 X1 X2 X3) -> False) -> (esk1_4 X1 X2 X3 X4) = X1 -> r2_hidden (esk1_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X4 X2 X3 X1, (X4 = (k1_enumset1 X1 X2 X3) -> False) -> (esk1_4 X1 X2 X3 X4) = X2 -> r2_hidden (esk1_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X4 X2 X3 X1, (X4 = (k1_enumset1 X1 X2 X3) -> False) -> (esk1_4 X1 X2 X3 X4) = X3 -> r2_hidden (esk1_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k8_domain_1 X1 X2 X3 X4) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X4 X3 X2 X1, ((k8_domain_1 X1 X2 X3 X4) = (k1_enumset1 X2 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X2 X1, (X2 = (k1_urysohn1 X1) -> False) -> (esk3_2 X1 X2) = (k6_real_1 X3 (k2_newton np__2 X1)) -> v7_ordinal1 X1 -> m1_subset_1 X3 k5_numbers -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> r2_hidden (esk3_2 X1 X2) X2 -> r1_xxreal_0 X3 (k2_newton np__2 X1) -> False)
  -> (forall X1 X3 X2, ((k6_real_1 (esk2_3 X2 X3 X1) (k2_newton np__2 X2)) = X1 -> False) -> X3 = (k1_urysohn1 X2) -> v7_ordinal1 X2 -> r2_hidden X1 X3 -> m1_subset_1 X1 k1_numbers -> m1_subset_1 X3 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X3 X2 X1, (r1_xxreal_0 (esk2_3 X1 X2 X3) (k2_newton np__2 X1) -> False) -> X2 = (k1_urysohn1 X1) -> v7_ordinal1 X1 -> r2_hidden X3 X2 -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k1_urysohn1 X2) -> X3 = (k6_real_1 X1 (k2_newton np__2 X2)) -> v7_ordinal1 X2 -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X1 k5_numbers -> m1_subset_1 X4 (k1_zfmisc_1 k1_numbers) -> r1_xxreal_0 X1 (k2_newton np__2 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk2_3 X1 X2 X3) k5_numbers -> False) -> X2 = (k1_urysohn1 X1) -> v7_ordinal1 X1 -> r2_hidden X3 X2 -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1 X2, (X2 = (k1_urysohn1 X1) -> False) -> ((k6_real_1 (esk4_2 X1 X2) (k2_newton np__2 X1)) = (esk3_2 X1 X2) -> False) -> (r2_hidden (esk3_2 X1 X2) X2 -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1 X2, (X2 = (k1_urysohn1 X1) -> False) -> (r2_hidden (esk3_2 X1 X2) X2 -> False) -> (r1_xxreal_0 (esk4_2 X1 X2) (k2_newton np__2 X1) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, (v5_membered (k1_enumset1 X1 X2 X3) -> False) -> v1_int_1 X3 -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X1 X2 X3, (v4_membered (k1_enumset1 X1 X2 X3) -> False) -> v1_rat_1 X3 -> v1_rat_1 X2 -> v1_rat_1 X1 -> False)
  -> (forall X1 X2 X3, (v3_membered (k1_enumset1 X1 X2 X3) -> False) -> v1_xreal_0 X3 -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2 X3, (v2_membered (k1_enumset1 X1 X2 X3) -> False) -> v1_xxreal_0 X3 -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1 X2 X3, (v1_membered (k1_enumset1 X1 X2 X3) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, (v6_membered (k1_enumset1 X1 X2 X3) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> r2_hidden (esk24_2 X1 X2) X2 -> r2_hidden (esk24_2 X1 X2) X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k3_xcmplx_0 X1 X3) (k3_xcmplx_0 X2 X3)) = (k3_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk6_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (X2 = (k1_urysohn1 X1) -> False) -> (r2_hidden (esk3_2 X1 X2) X2 -> False) -> (m1_subset_1 (esk4_2 X1 X2) k5_numbers -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m2_subset_1 (k13_newton X1 X2) k1_numbers k5_numbers -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X4 X2 X3 X1 X5, (X1 = X5 -> False) -> (X1 = X4 -> False) -> (X1 = X3 -> False) -> X2 = (k1_enumset1 X3 X4 X5) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (X2 = (k1_nat_1 X1 np__1) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X1 X2 -> r1_xxreal_0 X2 (k1_nat_1 X1 np__1) -> False)
  -> (forall X2 X4 X5 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_enumset1 X2 X4 X5) -> False)
  -> (forall X2 X4 X5 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_enumset1 X4 X2 X5) -> False)
  -> (forall X2 X4 X5 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_enumset1 X4 X5 X2) -> False)
  -> (forall X2 X1, (m2_subset_1 (k2_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (m2_subset_1 (k1_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k7_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k7_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (X1 = (k1_nat_1 X2 np__1) -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X1 (k1_nat_1 X2 np__1) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk24_2 X1 X2) X2 -> False) -> (r2_hidden (esk24_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (X2 = (k1_urysohn1 X1) -> False) -> (m1_subset_1 (esk3_2 X1 X2) k1_numbers -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k3_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k7_xcmplx_0 X2 X1) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k7_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k13_newton X1 X2) = (k1_newton X1 X2) -> False) -> m1_subset_1 X2 k5_numbers -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X1 -> m1_subset_1 X2 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_newton X1 X2) k1_numbers -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k10_real_1 X1 X2) k1_numbers -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, ((k6_real_1 X1 X2) = (k7_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X1 -> m1_subset_1 X2 k1_numbers -> False)
  -> (forall X2 X1, ((k10_real_1 X1 X2) = (k7_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k2_newton X1 X2) = (k1_newton X1 X2) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, ((k1_nat_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_nat_1 X2 X1) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, ((k1_nat_1 X1 X2) = (k1_nat_1 X2 X1) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k1_newton X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k7_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 (k1_newton X1 X2) -> False) -> v1_xreal_0 X1 -> v7_ordinal1 X2 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k3_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 (k1_newton X1 X2) -> False) -> v1_xcmplx_0 X1 -> v7_ordinal1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X2 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_urysohn1 X1) (k1_zfmisc_1 k1_numbers) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk8_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 X1 np__1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k1_newton X1 np__1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (r1_xxreal_0 k6_numbers X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 k6_numbers X1) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k8_domain_1 k1_numbers k6_numbers (k10_real_1 np__1 np__2) np__1) = (k1_urysohn1 np__1) -> False)
  -> (forall X3 X2 X1, v1_xboole_0 (k1_enumset1 X1 X2 X3) -> False)
  -> (r1_xxreal_0 (k7_xcmplx_0 np__1 np__2) np__0 -> False)
  -> (r1_xxreal_0 np__2 (k7_xcmplx_0 np__1 np__2) -> False)
  -> (r1_xxreal_0 np__1 (k7_xcmplx_0 np__1 np__2) -> False)
  -> (forall X1, v1_subset_1 (esk18_1 X1) X1 -> False)
  -> (r1_xxreal_0 np__2 np__0 -> False)
  -> (r1_xxreal_0 np__2 np__1 -> False)
  -> (r1_xxreal_0 np__1 np__0 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 esk7_0 -> False)
  -> (v1_xboole_0 np__2 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> ((r1_xxreal_0 (k7_xcmplx_0 np__1 np__2) (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> (((k2_xcmplx_0 (k7_xcmplx_0 np__1 np__2) (k7_xcmplx_0 np__1 np__2)) = np__1 -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__2 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (((k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) np__1) = (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> (((k3_xcmplx_0 np__1 (k7_xcmplx_0 np__1 np__2)) = (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> ((r1_xxreal_0 (k7_xcmplx_0 np__1 np__2) np__2 -> False) -> False)
  -> ((r1_xxreal_0 (k7_xcmplx_0 np__1 np__2) np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 (k7_xcmplx_0 np__1 np__2) -> False) -> False)
  -> (((k3_xcmplx_0 (k7_xcmplx_0 np__1 np__2) np__2) = np__1 -> False) -> False)
  -> (((k7_xcmplx_0 np__1 (k7_xcmplx_0 np__1 np__2)) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 (k7_xcmplx_0 np__1 np__2)) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 (k7_xcmplx_0 np__1 np__2)) = np__1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__0 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__2 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__2 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__2 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> (((k7_xcmplx_0 np__2 np__2) = np__1 -> False) -> False)
  -> (((k7_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__2) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 np__1) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__2) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__2) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 np__0) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__1) = np__2 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk13_1 X1) -> False) -> False)
  -> ((v3_xxreal_0 esk20_0 -> False) -> False)
  -> ((v3_xxreal_0 esk19_0 -> False) -> False)
  -> ((v2_xxreal_0 esk16_0 -> False) -> False)
  -> ((v2_xxreal_0 esk15_0 -> False) -> False)
  -> ((v2_xxreal_0 np__2 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v7_membered esk17_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v1_xboole_0 esk23_0 -> False) -> False)
  -> ((v1_xboole_0 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_xreal_0 esk22_0 -> False) -> False)
  -> ((v1_xreal_0 esk19_0 -> False) -> False)
  -> ((v1_xreal_0 esk15_0 -> False) -> False)
  -> ((v1_xreal_0 esk10_0 -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v1_xxreal_0 esk23_0 -> False) -> False)
  -> ((v1_xxreal_0 esk22_0 -> False) -> False)
  -> ((v1_xxreal_0 esk20_0 -> False) -> False)
  -> ((v1_xxreal_0 esk19_0 -> False) -> False)
  -> ((v1_xxreal_0 esk16_0 -> False) -> False)
  -> ((v1_xxreal_0 esk15_0 -> False) -> False)
  -> ((v1_xxreal_0 esk11_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk22_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk19_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk15_0 -> False) -> False)
  -> ((v6_membered esk17_0 -> False) -> False)
  -> ((v6_membered esk12_0 -> False) -> False)
  -> ((v6_membered esk7_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> ((k1_xboole_0 = o_0_0_xboole_0 -> False) -> False)
  -> ((k1_xboole_0 = k6_numbers -> False) -> False)
  -> False.
Admitted.
