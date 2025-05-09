(** $I sig/MizarPreamble.mgs **)

Theorem l64_incsp_1:
 forall esk10_1:set -> set,
 forall esk11_1:set -> set,
 forall esk12_1:set -> set,
 forall esk9_1:set -> set,
 forall v13_incsp_1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall k2_incsp_1:set -> set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall k2_tarski:set -> set -> set,
 forall v11_incsp_1:set -> prop,
 forall r3_incsp_1:set -> set -> set -> prop,
 forall k1_incsp_1:set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk6_1:set -> set,
 forall esk7_1:set -> set,
 forall esk8_1:set -> set,
 forall esk17_2:set -> set -> set,
 forall esk13_1:set -> set,
 forall esk15_1:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk26_1:set -> set,
 forall v9_incsp_1:set -> prop,
 forall v7_incsp_1:set -> prop,
 forall v5_incsp_1:set -> prop,
 forall esk24_0:set,
 forall esk23_1:set -> set,
 forall esk22_0:set,
 forall esk19_0:set,
 forall esk18_0:set,
 forall esk20_1:set -> set,
 forall esk25_1:set -> set,
 forall k1_xboole_0:set,
 forall v6_incsp_1:set -> prop,
 forall v10_incsp_1:set -> prop,
 forall v12_incsp_1:set -> prop,
 forall esk21_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk14_1:set -> set,
 forall esk3_2:set -> set -> set,
 forall esk4_1:set -> set,
 forall v8_incsp_1:set -> prop,
 forall esk16_2:set -> set -> set,
 forall esk5_1:set -> set,
 forall v14_incsp_1:set -> prop,
 forall l1_incsp_1:set -> prop,
 forall k4_subset_1:set -> set -> set -> set,
 forall k6_domain_1:set -> set -> set,
 forall r1_incsp_1:set -> set -> set -> prop,
 forall r4_incsp_1:set -> set -> set -> prop,
 forall k7_domain_1:set -> set -> set -> set,
 forall u2_incsp_1:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall v3_incsp_1:set -> set -> prop,
 forall u1_incsp_1:set -> set,
 forall k8_domain_1:set -> set -> set -> set -> set,
 forall l2_incsp_1:set -> prop,
 forall r5_incsp_1:set -> set -> set -> prop,
 forall k9_domain_1:set -> set -> set -> set -> set -> set,
 forall v4_incsp_1:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u4_incsp_1:set -> set,
 forall v15_incsp_1:set -> prop,
 forall r2_incsp_1:set -> set -> set -> prop,
     (forall X2 X3 X4 X6 X5 X1, (r2_incsp_1 X1 X5 X6 -> False) -> (v3_incsp_1 (k8_domain_1 (u1_incsp_1 X1) X2 X3 X4) X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> m1_subset_1 X6 (u4_incsp_1 X1) -> m1_subset_1 X5 (u1_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> v4_incsp_1 (k9_domain_1 (u1_incsp_1 X1) X2 X3 X4 X5) X1 -> r5_incsp_1 X1 (k8_domain_1 (u1_incsp_1 X1) X2 X3 X4) X6 -> False)
  -> (forall X1, l2_incsp_1 X1 -> v13_incsp_1 X1 -> v4_incsp_1 (k9_domain_1 (u1_incsp_1 X1) (esk9_1 X1) (esk10_1 X1) (esk11_1 X1) (esk12_1 X1)) X1 -> False)
  -> (forall X4 X2 X3 X5 X1, (v4_incsp_1 (k9_domain_1 (u1_incsp_1 X1) X2 X3 X4 X5) X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> m1_subset_1 X5 (u1_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> v3_incsp_1 (k8_domain_1 (u1_incsp_1 X1) X2 X3 X4) X1 -> False)
  -> (forall X3 X2 X1 X4, (v4_incsp_1 (k9_domain_1 (u1_incsp_1 esk1_0) X1 X2 X3 X4) esk1_0 -> False) -> m1_subset_1 X4 (u1_incsp_1 esk1_0) -> m1_subset_1 X3 (u1_incsp_1 esk1_0) -> m1_subset_1 X2 (u1_incsp_1 esk1_0) -> m1_subset_1 X1 (u1_incsp_1 esk1_0) -> r2_incsp_1 esk1_0 X1 esk2_0 -> False)
  -> (forall X4 X3 X1 X5 X2, (v13_incsp_1 X2 -> False) -> (v4_incsp_1 (k9_domain_1 (u1_incsp_1 X2) X1 X3 X4 X5) X2 -> False) -> l2_incsp_1 X2 -> m1_subset_1 X5 (u1_incsp_1 X2) -> m1_subset_1 X4 (u1_incsp_1 X2) -> m1_subset_1 X3 (u1_incsp_1 X2) -> m1_subset_1 X1 (u1_incsp_1 X2) -> False)
  -> (forall X2 X3 X4 X1, (v4_incsp_1 (k9_domain_1 (u1_incsp_1 X1) X2 X2 X3 X4) X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X5 X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k9_domain_1 X1 X2 X3 X4 X5) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X5 X4 X3 X2 X1, (X5 = (k2_incsp_1 X1 X2 X3 X4) -> False) -> (v3_incsp_1 (k8_domain_1 (u1_incsp_1 X1) X2 X3 X4) X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> m1_subset_1 X5 (u4_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> r5_incsp_1 X1 (k8_domain_1 (u1_incsp_1 X1) X2 X3 X4) X5 -> False)
  -> (forall X1 X5 X4 X3 X2, (v3_incsp_1 (k8_domain_1 (u1_incsp_1 X2) X3 X4 X5) X2 -> False) -> (r5_incsp_1 X2 (k8_domain_1 (u1_incsp_1 X2) X3 X4 X5) X1 -> False) -> X1 = (k2_incsp_1 X2 X3 X4 X5) -> v15_incsp_1 X2 -> l2_incsp_1 X2 -> m1_subset_1 X5 (u1_incsp_1 X2) -> m1_subset_1 X4 (u1_incsp_1 X2) -> m1_subset_1 X3 (u1_incsp_1 X2) -> m1_subset_1 X1 (u4_incsp_1 X2) -> False)
  -> (forall X5 X2 X3 X4 X1, ((k9_domain_1 X1 X2 X3 X4 X5) = (k2_xboole_0 (k2_tarski X2 X3) (k2_tarski X4 X5)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (r1_incsp_1 X1 X4 X5 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> m1_subset_1 X5 (u2_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> v3_incsp_1 (k8_domain_1 (u1_incsp_1 X1) X2 X3 X4) X1 -> r4_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) X2 X3) X5 -> False)
  -> (forall X4 X5 X3 X2 X1, (r2_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X5 (u1_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> r5_incsp_1 X1 (k8_domain_1 (u1_incsp_1 X1) X2 X4 X5) X3 -> False)
  -> (forall X4 X5 X3 X2 X1, (r2_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X5 (u1_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> r5_incsp_1 X1 (k8_domain_1 (u1_incsp_1 X1) X4 X2 X5) X3 -> False)
  -> (forall X4 X5 X3 X2 X1, (r2_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X5 (u1_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> r5_incsp_1 X1 (k8_domain_1 (u1_incsp_1 X1) X4 X5 X2) X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (r5_incsp_1 X1 (k8_domain_1 (u1_incsp_1 X1) X2 X4 X5) X3 -> False) -> l2_incsp_1 X1 -> r2_incsp_1 X1 X5 X3 -> r2_incsp_1 X1 X4 X3 -> r2_incsp_1 X1 X2 X3 -> m1_subset_1 X5 (u1_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X1 X2 X3 X4 X5, (X4 = X5 -> False) -> (r3_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> v11_incsp_1 X1 -> m1_subset_1 X5 (u1_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> r4_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) X4 X5) X2 -> r5_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) X4 X5) X3 -> False)
  -> (forall X2 X3 X4 X1, (m1_subset_1 (k2_incsp_1 X1 X2 X3 X4) (u4_incsp_1 X1) -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k8_domain_1 X1 X2 X3 X4) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X4 X3 X2 X1, (r1_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_incsp_1 X1)) -> r4_incsp_1 X1 (k4_subset_1 (u1_incsp_1 X1) X4 (k6_domain_1 (u1_incsp_1 X1) X2)) X3 -> False)
  -> (forall X4 X3 X2 X1, (r5_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> r5_incsp_1 X1 (k4_subset_1 (u1_incsp_1 X1) X2 (k6_domain_1 (u1_incsp_1 X1) X4)) X3 -> False)
  -> (forall X4 X3 X2 X1, (r4_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> r4_incsp_1 X1 (k4_subset_1 (u1_incsp_1 X1) X2 (k6_domain_1 (u1_incsp_1 X1) X4)) X3 -> False)
  -> (forall X4 X3 X2 X1, (r2_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_incsp_1 X1)) -> r5_incsp_1 X1 (k4_subset_1 (u1_incsp_1 X1) X4 (k6_domain_1 (u1_incsp_1 X1) X2)) X3 -> False)
  -> (forall X4 X3 X2 X1, (r5_incsp_1 X1 (k4_subset_1 (u1_incsp_1 X1) X2 (k6_domain_1 (u1_incsp_1 X1) X4)) X3 -> False) -> l2_incsp_1 X1 -> r2_incsp_1 X1 X4 X3 -> r5_incsp_1 X1 X2 X3 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> False)
  -> (forall X2 X3 X4 X1, (r4_incsp_1 X1 (k4_subset_1 (u1_incsp_1 X1) X2 (k6_domain_1 (u1_incsp_1 X1) X4)) X3 -> False) -> l2_incsp_1 X1 -> r4_incsp_1 X1 X2 X3 -> r1_incsp_1 X1 X4 X3 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> False)
  -> (forall X4 X3 X2 X1, (r5_incsp_1 X1 (k4_subset_1 (u1_incsp_1 X1) X2 X4) X3 -> False) -> l2_incsp_1 X1 -> r5_incsp_1 X1 X4 X3 -> r5_incsp_1 X1 X2 X3 -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_incsp_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> False)
  -> (forall X4 X3 X2 X1, (r5_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_incsp_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> r5_incsp_1 X1 (k4_subset_1 (u1_incsp_1 X1) X2 X4) X3 -> False)
  -> (forall X4 X3 X2 X1, (r5_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_incsp_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> r5_incsp_1 X1 (k4_subset_1 (u1_incsp_1 X1) X4 X2) X3 -> False)
  -> (forall X4 X3 X2 X1, (r5_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) X2 X4) X3 -> False) -> l2_incsp_1 X1 -> r2_incsp_1 X1 X4 X3 -> r2_incsp_1 X1 X2 X3 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X4 X3 X2 X1, (r4_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) X2 X4) X3 -> False) -> l1_incsp_1 X1 -> r1_incsp_1 X1 X4 X3 -> r1_incsp_1 X1 X2 X3 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X1 X4 X2 X3, (X2 = X3 -> False) -> (X4 = (k1_incsp_1 X1 X2 X3) -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> m1_subset_1 X4 (u2_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> r4_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) X2 X3) X4 -> False)
  -> (forall X4 X3 X2 X1, (r1_incsp_1 X1 X2 X3 -> False) -> l1_incsp_1 X1 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> r4_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) X2 X4) X3 -> False)
  -> (forall X4 X3 X2 X1, (r1_incsp_1 X1 X2 X3 -> False) -> l1_incsp_1 X1 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> r4_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) X4 X2) X3 -> False)
  -> (forall X4 X3 X2 X1, (r2_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> r5_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) X2 X4) X3 -> False)
  -> (forall X4 X3 X2 X1, (r2_incsp_1 X1 X2 X3 -> False) -> l2_incsp_1 X1 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u4_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> r5_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) X4 X2) X3 -> False)
  -> (forall X2 X1 X3 X4, (X3 = X4 -> False) -> (r4_incsp_1 X2 (k7_domain_1 (u1_incsp_1 X2) X3 X4) X1 -> False) -> X1 = (k1_incsp_1 X2 X3 X4) -> v15_incsp_1 X2 -> l2_incsp_1 X2 -> m1_subset_1 X4 (u1_incsp_1 X2) -> m1_subset_1 X3 (u1_incsp_1 X2) -> m1_subset_1 X1 (u2_incsp_1 X2) -> False)
  -> (forall X4 X3 X2 X1, ((k8_domain_1 X1 X2 X3 X4) = (k2_xboole_0 (k2_tarski X2 X3) (k1_tarski X4)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X4 X2 X1, (r2_incsp_1 X1 X2 X4 -> False) -> l2_incsp_1 X1 -> v14_incsp_1 X1 -> r3_incsp_1 X1 X3 X4 -> r1_incsp_1 X1 X2 X3 -> m1_subset_1 X4 (u4_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X1, (v11_incsp_1 X1 -> False) -> (r5_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) (esk7_1 X1) (esk8_1 X1)) (esk6_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v11_incsp_1 X1 -> False) -> (r4_incsp_1 X1 (k7_domain_1 (u1_incsp_1 X1) (esk7_1 X1) (esk8_1 X1)) (esk5_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k1_incsp_1 X1 X2 X3) (u2_incsp_1 X1) -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, (v3_incsp_1 X3 X2 -> False) -> l1_incsp_1 X2 -> r4_incsp_1 X2 X3 X1 -> m1_subset_1 X1 (u2_incsp_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_incsp_1 X2)) -> False)
  -> (forall X1 X3 X2, (v4_incsp_1 X3 X2 -> False) -> l2_incsp_1 X2 -> r5_incsp_1 X2 X3 X1 -> m1_subset_1 X1 (u4_incsp_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_incsp_1 X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k7_domain_1 X1 X2 X3) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (r5_incsp_1 X1 X2 (esk17_2 X1 X2) -> False) -> l2_incsp_1 X1 -> v4_incsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> False)
  -> (forall X2 X1, (r4_incsp_1 X1 X2 (esk16_2 X1 X2) -> False) -> l1_incsp_1 X1 -> v3_incsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> False)
  -> (forall X2 X3 X1, ((k7_domain_1 X1 X2 X3) = (k7_domain_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v8_incsp_1 X2 -> False) -> l2_incsp_1 X2 -> m1_subset_1 X1 (u1_incsp_1 X2) -> r2_incsp_1 X2 X1 (esk4_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk17_2 X1 X2) (u4_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> v4_incsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (u2_incsp_1 X1) -> False) -> l1_incsp_1 X1 -> v3_incsp_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_incsp_1 X1)) -> False)
  -> (forall X2 X1, (r2_incsp_1 X1 (esk3_2 X1 X2) X2 -> False) -> l2_incsp_1 X1 -> v8_incsp_1 X1 -> m1_subset_1 X2 (u4_incsp_1 X1) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, ((k7_domain_1 X1 X2 X3) = (k2_tarski X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v14_incsp_1 X1 -> False) -> l2_incsp_1 X1 -> r2_incsp_1 X1 (esk13_1 X1) (esk15_1 X1) -> False)
  -> (forall X1, (v11_incsp_1 X1 -> False) -> l2_incsp_1 X1 -> r3_incsp_1 X1 (esk5_1 X1) (esk6_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk3_2 X1 X2) (u1_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> v8_incsp_1 X1 -> m1_subset_1 X2 (u4_incsp_1 X1) -> False)
  -> (forall X1, (v14_incsp_1 X1 -> False) -> (r1_incsp_1 X1 (esk13_1 X1) (esk14_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v14_incsp_1 X1 -> False) -> (r3_incsp_1 X1 (esk14_1 X1) (esk15_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k6_domain_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k6_domain_1 X1 X2) = (k1_tarski X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) (u1_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> v13_incsp_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) (u1_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> v13_incsp_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) (u1_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> v13_incsp_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) (u1_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> v13_incsp_1 X1 -> False)
  -> (forall X1, (v14_incsp_1 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (u4_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v14_incsp_1 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (u2_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v14_incsp_1 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (u1_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v11_incsp_1 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v11_incsp_1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v11_incsp_1 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u4_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v11_incsp_1 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u2_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v8_incsp_1 X1 -> False) -> (m1_subset_1 (esk4_1 X1) (u4_incsp_1 X1) -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v11_incsp_1 X1 -> False) -> (esk8_1 X1) = (esk7_1 X1) -> l2_incsp_1 X1 -> False)
  -> (forall X1, l1_incsp_1 X1 -> v1_xboole_0 (u2_incsp_1 X1) -> False)
  -> (forall X1, l1_incsp_1 X1 -> v1_xboole_0 (u1_incsp_1 X1) -> False)
  -> (forall X1, l2_incsp_1 X1 -> v1_xboole_0 (u4_incsp_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v14_incsp_1 X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v13_incsp_1 X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v12_incsp_1 X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v11_incsp_1 X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v10_incsp_1 X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v9_incsp_1 X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v8_incsp_1 X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v7_incsp_1 X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v6_incsp_1 X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> False)
  -> (forall X1, (v5_incsp_1 X1 -> False) -> v15_incsp_1 X1 -> l2_incsp_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_incsp_1 X1 -> False) -> l2_incsp_1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1 X4 X3, v1_xboole_0 (k2_xboole_0 (k2_tarski X1 X2) (k2_tarski X3 X4)) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 (k2_xboole_0 (k2_tarski X1 X2) (k1_tarski X3)) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk25_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (forall X2 X1 X4 X3, ((k2_xboole_0 (k2_xboole_0 (k2_tarski X1 X2) (k1_tarski X3)) (k1_tarski X4)) = (k2_xboole_0 (k2_tarski X1 X2) (k2_tarski X3 X4)) -> False) -> False)
  -> (forall X3 X2 X4 X1, ((k2_xboole_0 (k2_tarski X1 X2) (k2_tarski X3 X4)) = (k2_xboole_0 (k2_tarski X2 X3) (k2_tarski X1 X4)) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u4_incsp_1 esk1_0) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk23_1 X1) -> False) -> False)
  -> ((l1_incsp_1 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l2_incsp_1 esk19_0 -> False) -> False)
  -> ((l2_incsp_1 esk1_0 -> False) -> False)
  -> ((v15_incsp_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
