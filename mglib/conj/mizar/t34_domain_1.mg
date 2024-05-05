(** $I sig/MizarPreamble.mgs **)

Theorem t34_domain_1:
 forall esk7_5:set -> set -> set -> set -> set -> set,
 forall a_4_4_domain_1:set -> set -> set -> set -> set,
 forall a_3_6_domain_1:set -> set -> set -> set,
 forall esk5_4:set -> set -> set -> set -> set,
 forall k5_subset_1:set -> set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk10_1:set -> set,
 forall v2_relat_1:set -> prop,
 forall k1_xboole_0:set,
 forall esk15_1:set -> set,
 forall esk14_0:set,
 forall esk4_1:set -> set,
 forall esk11_0:set,
 forall o_0_0_xboole_0:set,
 forall esk12_0:set,
 forall esk13_1:set -> set,
 forall esk9_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall v3_relat_1:set -> prop,
 forall esk16_1:set -> set,
 forall esk18_2:set -> set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall a_3_8_domain_1:set -> set -> set -> set,
 forall esk17_4:set -> set -> set -> set -> set,
 forall a_4_6_domain_1:set -> set -> set -> set -> set,
 forall esk8_5:set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
     (forall X2 X3 X1 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_4_6_domain_1 X2 X3 X4 X5) -> r2_hidden (esk8_5 X1 X2 X3 X4 X5) X4 -> r2_hidden (esk8_5 X1 X2 X3 X4 X5) X3 -> False)
  -> (forall X2 X3 X1 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_4_4_domain_1 X2 X3 X4 X5) -> r2_hidden (esk7_5 X1 X2 X3 X4 X5) X4 -> r2_hidden (esk7_5 X1 X2 X3 X4 X5) X3 -> False)
  -> (forall X2 X3 X1 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk8_5 X1 X2 X3 X4 X5) X4 -> False) -> (r2_hidden (esk8_5 X1 X2 X3 X4 X5) X3 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_4_6_domain_1 X2 X3 X4 X5) -> False)
  -> (forall X2 X3 X1 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk7_5 X1 X2 X3 X4 X5) X4 -> False) -> (r2_hidden (esk7_5 X1 X2 X3 X4 X5) X3 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_4_4_domain_1 X2 X3 X4 X5) -> False)
  -> (forall X2 X3 X1 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk8_5 X1 X2 X3 X4 X5) X5 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_4_6_domain_1 X2 X3 X4 X5) -> False)
  -> (forall X2 X3 X1 X4 X5, (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk7_5 X1 X2 X3 X4 X5) X5 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_4_4_domain_1 X2 X3 X4 X5) -> False)
  -> (forall X1 X2 X3 X4, ((a_4_4_domain_1 X1 X2 X3 X4) = (a_4_6_domain_1 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r2_hidden (esk17_4 X1 X2 X3 X4) X3 -> r2_hidden (esk17_4 X1 X2 X3 X4) X2 -> False)
  -> (forall X2 X3 X1 X4 X5, ((esk8_5 X1 X2 X3 X4 X5) = X1 -> False) -> (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_4_6_domain_1 X2 X3 X4 X5) -> False)
  -> (forall X2 X3 X1 X4 X5, ((esk7_5 X1 X2 X3 X4 X5) = X1 -> False) -> (v1_xboole_0 X5 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_4_4_domain_1 X2 X3 X4 X5) -> False)
  -> (forall X1 X2 X3 X4, ((a_4_4_domain_1 X1 X2 X3 X4) = (a_4_6_domain_1 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk17_4 X1 X2 X3 X4) X2 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r2_hidden (esk17_4 X1 X2 X3 X4) X3 -> False)
  -> (forall X1 X2 X3 X4, ((a_4_4_domain_1 X1 X2 X3 X4) = (a_4_6_domain_1 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk17_4 X1 X2 X3 X4) X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r2_hidden (esk17_4 X1 X2 X3 X4) X2 -> False)
  -> (forall X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_6_domain_1 X2 X3 X4) -> r2_hidden (esk5_4 X1 X2 X3 X4) X4 -> r2_hidden (esk5_4 X1 X2 X3 X4) X3 -> False)
  -> (forall X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_8_domain_1 X2 X3 X4) -> r2_hidden (esk6_4 X1 X2 X3 X4) X4 -> r2_hidden (esk6_4 X1 X2 X3 X4) X3 -> False)
  -> (forall X1 X3 X2 X4, ((a_4_4_domain_1 X1 X2 X3 X4) = (a_4_6_domain_1 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk17_4 X1 X2 X3 X4) X3 -> False) -> (r2_hidden (esk17_4 X1 X2 X3 X4) X2 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden (esk6_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk6_4 X1 X2 X3 X4) X3 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_8_domain_1 X2 X3 X4) -> False)
  -> (forall X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden (esk5_4 X1 X2 X3 X4) X4 -> False) -> (r2_hidden (esk5_4 X1 X2 X3 X4) X3 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_6_domain_1 X2 X3 X4) -> False)
  -> (forall X1 X3 X2 X4, ((a_4_4_domain_1 X1 X2 X3 X4) = (a_4_6_domain_1 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_4 X1 X2 X3 X4) X4 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk6_4 X1 X2 X3 X4) X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_8_domain_1 X2 X3 X4) -> False)
  -> (forall X4 X1 X3 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk5_4 X1 X2 X3 X4) X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_6_domain_1 X2 X3 X4) -> False)
  -> (forall X4 X5 X3 X1 X2 X6, (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (r2_hidden X1 X2 -> False) -> (r2_hidden X5 (a_4_4_domain_1 X6 X2 X3 X4) -> False) -> X1 = X5 -> m1_subset_1 X1 X4 -> r2_hidden X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X6) -> m1_subset_1 X2 (k1_zfmisc_1 X6) -> False)
  -> (forall X4 X5 X2 X1 X3 X6, (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (r2_hidden X1 X3 -> False) -> (r2_hidden X5 (a_4_6_domain_1 X6 X2 X3 X4) -> False) -> X1 = X5 -> m1_subset_1 X1 X4 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X6) -> m1_subset_1 X2 (k1_zfmisc_1 X6) -> False)
  -> (forall X4 X5 X2 X1 X3 X6, (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (r2_hidden X1 X3 -> False) -> (r2_hidden X5 (a_4_6_domain_1 X6 X3 X2 X4) -> False) -> X1 = X5 -> m1_subset_1 X1 X4 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X6) -> m1_subset_1 X2 (k1_zfmisc_1 X6) -> False)
  -> (forall X4 X5 X2 X1 X3 X6, (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X4 -> False) -> (r2_hidden X1 X3 -> False) -> (r2_hidden X5 (a_4_4_domain_1 X6 X2 X3 X4) -> False) -> X1 = X5 -> m1_subset_1 X1 X4 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X6) -> m1_subset_1 X2 (k1_zfmisc_1 X6) -> False)
  -> (forall X4 X1 X3 X2, ((esk6_4 X1 X2 X3 X4) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_8_domain_1 X2 X3 X4) -> False)
  -> (forall X4 X1 X3 X2, ((esk5_4 X1 X2 X3 X4) = X1 -> False) -> (v1_xboole_0 X2 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> r2_hidden X1 (a_3_6_domain_1 X2 X3 X4) -> False)
  -> (forall X2 X1 X3 X5 X4, (v1_xboole_0 X4 -> False) -> (r2_hidden X1 X2 -> False) -> (r2_hidden X5 (a_3_6_domain_1 X4 X2 X3) -> False) -> X1 = X5 -> m1_subset_1 X1 X4 -> r2_hidden X1 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X2 (k1_zfmisc_1 X4) -> False)
  -> (forall X3 X1 X2 X5 X4, (v1_xboole_0 X4 -> False) -> (r2_hidden X1 X3 -> False) -> (r2_hidden X5 (a_3_6_domain_1 X4 X2 X3) -> False) -> X1 = X5 -> m1_subset_1 X1 X4 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X2 (k1_zfmisc_1 X4) -> False)
  -> (forall X3 X1 X2 X5 X4, (v1_xboole_0 X4 -> False) -> (r2_hidden X1 X3 -> False) -> (r2_hidden X5 (a_3_8_domain_1 X4 X2 X3) -> False) -> X1 = X5 -> m1_subset_1 X1 X4 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X2 (k1_zfmisc_1 X4) -> False)
  -> (forall X3 X1 X2 X5 X4, (v1_xboole_0 X4 -> False) -> (r2_hidden X1 X3 -> False) -> (r2_hidden X5 (a_3_8_domain_1 X4 X3 X2) -> False) -> X1 = X5 -> m1_subset_1 X1 X4 -> r2_hidden X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X4) -> m1_subset_1 X2 (k1_zfmisc_1 X4) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k5_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k5_subset_1 X2 X1 X3) = (k2_xboole_0 (k4_xboole_0 X1 X3) (k4_xboole_0 X3 X1)) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, ((a_3_6_domain_1 X1 X2 X3) = (k5_subset_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1, ((k5_subset_1 X2 X1 X3) = (k5_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 (k4_xboole_0 X1 X2) (k4_xboole_0 X2 X1)) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk18_2 X3 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk18_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k4_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk10_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk10_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((a_3_8_domain_1 esk1_0 esk2_0 esk3_0) = (k5_subset_1 esk1_0 esk2_0 esk3_0) -> False)
  -> (forall X1, v1_subset_1 (esk15_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X1, ((k2_xboole_0 (k4_xboole_0 X1 X2) (k4_xboole_0 X2 X1)) = (k2_xboole_0 (k4_xboole_0 X2 X1) (k4_xboole_0 X1 X2)) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 (k4_xboole_0 X1 k1_xboole_0) (k4_xboole_0 k1_xboole_0 X1)) = X1 -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk4_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 esk1_0) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk13_1 X1) -> False) -> False)
  -> ((v2_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
