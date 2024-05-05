(** $I sig/MizarPreamble.mgs **)

Theorem t44_normform:
 forall k9_normform:set -> set -> set,
 forall esk24_3:set -> set -> set -> set,
 forall k5_setwiseo:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk13_3:set -> set -> set -> set,
 forall k2_xtuple_0:set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk16_1:set -> set,
 forall v2_relat_1:set -> prop,
 forall v1_finsub_1:set -> prop,
 forall v3_finsub_1:set -> prop,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk14_0:set,
 forall esk15_2:set -> set -> set,
 forall esk19_2:set -> set -> set,
 forall esk18_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk17_0:set,
 forall esk5_1:set -> set,
 forall esk20_1:set -> set,
 forall k1_xboole_0:set,
 forall v3_relat_1:set -> prop,
 forall esk21_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk22_2:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall k1_xtuple_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall k3_domain_1:set -> set -> set -> set,
 forall k2_domain_1:set -> set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall esk23_3:set -> set -> set -> set,
 forall k8_normform:set -> set,
 forall esk8_2:set -> set -> set,
 forall esk11_3:set -> set -> set -> set,
 forall v4_finsub_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k5_finsub_1:set -> set,
 forall k7_normform:set -> set,
 forall r1_normform:set -> set -> set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk12_4:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_2_0_normform:set -> set -> set,
     (forall X4 X2 X3 X1, (r2_hidden X1 (a_2_0_normform X2 X3) -> False) -> X1 = X4 -> (esk12_4 X1 X2 X3 X4) = X4 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> r2_hidden (esk12_4 X1 X2 X3 X4) X3 -> m2_subset_1 X4 (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> r1_normform (k5_finsub_1 X2) (k5_finsub_1 X2) (esk12_4 X1 X2 X3 X4) X4 -> False)
  -> (forall X4 X1 X3 X2, ((esk12_4 X2 X1 X3 X4) = X4 -> False) -> (r2_hidden X2 (a_2_0_normform X1 X3) -> False) -> (r1_normform (k5_finsub_1 X1) (k5_finsub_1 X1) (esk12_4 X2 X1 X3 X4) X4 -> False) -> X2 = X4 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m2_subset_1 X4 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False)
  -> (forall X1 X4 X3 X5 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_normform X1 X2 X3 X5 -> False) -> v4_finsub_1 X2 -> v4_finsub_1 X1 -> r1_normform X1 X2 X4 X5 -> r1_normform X1 X2 X3 X4 -> m1_subset_1 X5 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X4 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X4 X2 X3 X1, ((esk12_4 X1 X2 X3 X4) = X4 -> False) -> (r2_hidden X1 (a_2_0_normform X2 X3) -> False) -> (r2_hidden (esk12_4 X1 X2 X3 X4) X3 -> False) -> X1 = X4 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> m2_subset_1 X4 (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> False)
  -> (forall X4 X3 X1 X2, (X1 = (esk11_3 X4 X3 X2) -> False) -> r2_hidden X1 X2 -> r2_hidden X4 (a_2_0_normform X3 X2) -> m1_subset_1 X2 (k5_finsub_1 (k7_normform X3)) -> m2_subset_1 X1 (k2_zfmisc_1 (k5_finsub_1 X3) (k5_finsub_1 X3)) (k7_normform X3) -> r1_normform (k5_finsub_1 X3) (k5_finsub_1 X3) X1 (esk11_3 X4 X3 X2) -> False)
  -> (forall X2 X1 X3 X4, (X3 = X4 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X2 -> v4_finsub_1 X1 -> r1_normform X1 X2 X4 X3 -> r1_normform X1 X2 X3 X4 -> m1_subset_1 X4 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X4 X1 X3, (X1 = X3 -> False) -> r2_hidden X4 (k8_normform X2) -> r2_hidden X3 (esk8_2 X4 X2) -> r2_hidden X1 (esk8_2 X4 X2) -> r1_normform (k5_finsub_1 X2) (k5_finsub_1 X2) X1 X3 -> m2_subset_1 X3 (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> m2_subset_1 X1 (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> r2_hidden X1 X2 -> r2_hidden X4 (k9_normform X3 X2) -> m1_subset_1 X2 (k5_finsub_1 (k7_normform X3)) -> r1_normform (k5_finsub_1 X3) (k5_finsub_1 X3) X1 X4 -> m2_subset_1 X4 (k2_zfmisc_1 (k5_finsub_1 X3) (k5_finsub_1 X3)) (k7_normform X3) -> m2_subset_1 X1 (k2_zfmisc_1 (k5_finsub_1 X3) (k5_finsub_1 X3)) (k7_normform X3) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (a_2_0_normform X2 X3) -> False) -> (m2_subset_1 (esk12_4 X1 X2 X3 X4) (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> False) -> X1 = X4 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> m2_subset_1 X4 (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> False)
  -> (forall X3 X4 X1 X2, (r1_normform (k5_finsub_1 X1) (k5_finsub_1 X1) X2 (esk11_3 X3 X1 X4) -> False) -> X2 = (esk11_3 X3 X1 X4) -> r2_hidden X3 (a_2_0_normform X1 X4) -> m1_subset_1 X4 (k5_finsub_1 (k7_normform X1)) -> m2_subset_1 X2 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False)
  -> (forall X1 X2 X3, (r2_hidden X2 (k9_normform X1 X3) -> False) -> (r1_normform (k5_finsub_1 X1) (k5_finsub_1 X1) (esk23_3 X1 X2 X3) X2 -> False) -> r2_hidden X2 X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m2_subset_1 X2 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False)
  -> (forall X1 X2 X3, (r1_normform (k5_finsub_1 X1) (k5_finsub_1 X1) (esk24_3 X1 X2 X3) X2 -> False) -> r2_hidden X2 X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m2_subset_1 X2 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 (k7_normform X2) -> False) -> X1 = X3 -> m1_subset_1 X1 (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) -> r1_xboole_0 (k2_domain_1 (k5_finsub_1 X2) (k5_finsub_1 X2) X1) (k3_domain_1 (k5_finsub_1 X2) (k5_finsub_1 X2) X1) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k9_normform X2 (k5_setwiseo (k7_normform X2) X1 X3)) (k5_setwiseo (k7_normform X2) (k9_normform X2 X1) X3) -> False) -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> m1_subset_1 X1 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X3 X2 X1, (r2_hidden X2 (k8_normform X1) -> False) -> (r1_normform (k5_finsub_1 X1) (k5_finsub_1 X1) (esk9_3 X2 X1 X3) (esk10_3 X2 X1 X3) -> False) -> X2 = X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> False)
  -> (forall X1 X2 X3, (r2_hidden X2 (k9_normform X1 X3) -> False) -> (m2_subset_1 (esk23_3 X1 X2 X3) (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False) -> r2_hidden X2 X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m2_subset_1 X2 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> r2_hidden X1 (k9_normform X3 X2) -> m1_subset_1 X2 (k5_finsub_1 (k7_normform X3)) -> m2_subset_1 X4 (k2_zfmisc_1 (k5_finsub_1 X3) (k5_finsub_1 X3)) (k7_normform X3) -> m2_subset_1 X1 (k2_zfmisc_1 (k5_finsub_1 X3) (k5_finsub_1 X3)) (k7_normform X3) -> False)
  -> (forall X1 X2 X3, (m2_subset_1 (esk24_3 X1 X2 X3) (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False) -> r2_hidden X2 X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m2_subset_1 X2 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False)
  -> (forall X1 X2, (r1_xboole_0 (k2_domain_1 (k5_finsub_1 X1) (k5_finsub_1 X1) (esk7_2 X2 X1)) (k3_domain_1 (k5_finsub_1 X1) (k5_finsub_1 X1) (esk7_2 X2 X1)) -> False) -> r2_hidden X2 (k7_normform X1) -> False)
  -> (forall X1 X2 X3, (r2_hidden X2 (k9_normform X1 X3) -> False) -> (r2_hidden (esk23_3 X1 X2 X3) X3 -> False) -> r2_hidden X2 X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m2_subset_1 X2 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_normform X1 X2 X3 X3 -> False) -> v4_finsub_1 X2 -> v4_finsub_1 X1 -> m1_subset_1 X4 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk24_3 X1 X2 X3) (k9_normform X1 X3) -> False) -> r2_hidden X2 X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m2_subset_1 X2 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> r2_hidden (esk4_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> r2_hidden (esk4_3 X1 X2 X3) X2 -> False)
  -> (forall X4 X3 X1 X2, (r2_hidden X1 X2 -> False) -> X1 = (esk11_3 X3 X4 X2) -> r2_hidden X3 (a_2_0_normform X4 X2) -> m1_subset_1 X2 (k5_finsub_1 (k7_normform X4)) -> m2_subset_1 X1 (k2_zfmisc_1 (k5_finsub_1 X4) (k5_finsub_1 X4)) (k7_normform X4) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X2 X3, (r2_hidden X2 (k9_normform X1 X3) -> False) -> (esk23_3 X1 X2 X3) = X2 -> r2_hidden X2 X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m2_subset_1 X2 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False)
  -> (forall X1 X2 X3, (r1_tarski X2 X3 -> False) -> (m2_subset_1 (esk13_3 X1 X2 X3) (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1)) (k7_normform X1) -> False) -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m1_subset_1 X2 (k5_finsub_1 (k7_normform X1)) -> False)
  -> (forall X1 X2 X3, (m2_subset_1 (esk11_3 X1 X2 X3) (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> False) -> r2_hidden X1 (a_2_0_normform X2 X3) -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X1 X2 X3, (r1_tarski X2 X3 -> False) -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m1_subset_1 X2 (k5_finsub_1 (k7_normform X1)) -> r2_hidden (esk13_3 X1 X2 X3) X3 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k8_normform X2) -> False) -> (m2_subset_1 (esk10_3 X1 X2 X3) (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> False) -> X1 = X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k8_normform X2) -> False) -> (m2_subset_1 (esk9_3 X1 X2 X3) (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> False) -> X1 = X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k8_normform X2) -> False) -> X1 = X3 -> (esk10_3 X1 X2 X3) = (esk9_3 X1 X2 X3) -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X1 X2 X3, (r1_tarski X2 X3 -> False) -> (r2_hidden (esk13_3 X1 X2 X3) X2 -> False) -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X1)) -> m1_subset_1 X2 (k5_finsub_1 (k7_normform X1)) -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k8_normform X2) -> False) -> (r2_hidden (esk10_3 X1 X2 X3) X3 -> False) -> X1 = X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k8_normform X2) -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> X1 = X3 -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_domain_1 X1 X2 X3) X2 -> False) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_domain_1 X1 X2 X3) X1 -> False) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k5_setwiseo X2 X1 X3) (k5_finsub_1 X2) -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X3 X2 X1, ((k5_setwiseo X2 X1 X3) = (k5_setwiseo X2 X3 X1) -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X1 X2 X3, ((esk11_3 X1 X2 X3) = X1 -> False) -> r2_hidden X1 (a_2_0_normform X2 X3) -> m1_subset_1 X3 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X2 X1, (m2_subset_1 (k9_normform X2 X1) (k5_finsub_1 (k7_normform X2)) (k8_normform X2) -> False) -> m1_subset_1 X1 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k5_setwiseo X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X1 X3 X2, ((k3_domain_1 X1 X2 X3) = (k2_xtuple_0 X3) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X3 X2, ((k2_domain_1 X1 X2 X3) = (k1_xtuple_0 X3) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk7_2 X1 X2) (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) -> False) -> r2_hidden X1 (k7_normform X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk6_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1, ((k5_setwiseo X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk22_2 X3 X2) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski (k9_normform X2 X1) X1 -> False) -> m1_subset_1 X1 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk8_2 X1 X2) (k5_finsub_1 (k7_normform X2)) -> False) -> r2_hidden X1 (k8_normform X2) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_xboole_0 X1 X3) (k2_xboole_0 X2 X3) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k9_normform X2 X1) = (a_2_0_normform X2 X1) -> False) -> m1_subset_1 X1 (k5_finsub_1 (k7_normform X2)) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk22_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((esk8_2 X1 X2) = X1 -> False) -> r2_hidden X1 (k8_normform X2) -> False)
  -> (forall X2 X1, ((esk7_2 X1 X2) = X1 -> False) -> r2_hidden X1 (k7_normform X2) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk21_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_finsub_1 X1 -> False) -> v1_finsub_1 X1 -> v3_finsub_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k9_normform esk1_0 (k5_setwiseo (k7_normform esk1_0) (k9_normform esk1_0 esk2_0) esk3_0)) = (k9_normform esk1_0 (k5_setwiseo (k7_normform esk1_0) esk2_0 esk3_0)) -> False)
  -> (forall X1, v1_subset_1 (esk20_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k8_normform X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k5_finsub_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k7_normform X1) -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (forall X1, (m1_subset_1 (k7_normform X1) (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk15_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k8_normform X1) (k1_zfmisc_1 (k5_finsub_1 (k7_normform X1))) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk15_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k5_finsub_1 (k7_normform esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k5_finsub_1 (k7_normform esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> ((v2_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
