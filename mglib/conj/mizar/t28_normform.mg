(** $I sig/MizarPreamble.mgs **)

Theorem t28_normform:
 forall v1_xboole_0:set -> prop,
 forall v4_finsub_1:set -> prop,
 forall k1_domain_1:set -> set -> set -> set -> set,
 forall k1_finsub_1:set -> set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall k1_tarski:set -> set,
 forall k2_tarski:set -> set -> set,
 forall k2_xtuple_0:set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_xtuple_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk4_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk18_1:set -> set,
 forall v3_relat_1:set -> prop,
 forall esk17_1:set -> set,
 forall esk10_0:set,
 forall esk11_2:set -> set -> set,
 forall esk16_2:set -> set -> set,
 forall esk15_1:set -> set,
 forall esk14_0:set,
 forall o_0_0_xboole_0:set,
 forall esk13_0:set,
 forall esk7_1:set -> set,
 forall v3_finsub_1:set -> prop,
 forall v1_finsub_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk12_1:set -> set,
 forall v1_finset_1:set -> prop,
 forall k1_xboole_0:set,
 forall esk19_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall k1_xtuple_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k5_setwiseo:set -> set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk6_3:set -> set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k2_domain_1:set -> set -> set -> set,
 forall k3_domain_1:set -> set -> set -> set,
 forall k1_normform:set -> set -> set -> set -> set,
 forall k3_finsub_1:set -> set -> set -> set,
 forall o_3_0_normform:set -> set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k7_normform:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k5_finsub_1:set -> set,
     (forall X3 X2 X1, (m1_subset_1 (o_3_0_normform X2 X1 X3) (k3_finsub_1 (k5_finsub_1 X2) (k2_domain_1 (k5_finsub_1 X2) (k5_finsub_1 X2) (k1_normform (k5_finsub_1 X2) (k5_finsub_1 X2) X1 X3)) (k3_domain_1 (k5_finsub_1 X2) (k5_finsub_1 X2) (k1_normform (k5_finsub_1 X2) (k5_finsub_1 X2) X1 X3))) -> False) -> m2_subset_1 X3 (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> m2_subset_1 X1 (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> False)
  -> (forall X1 X4 X3 X2, ((k1_domain_1 X1 X2 (k1_finsub_1 X1 (k2_domain_1 X1 X2 X3) (k2_domain_1 X1 X2 X4)) (k1_finsub_1 X2 (k3_domain_1 X1 X2 X3) (k3_domain_1 X1 X2 X4))) = (k1_normform X1 X2 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X2 -> v4_finsub_1 X1 -> m1_subset_1 X4 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_normform X1 X2 X3 X4) (k2_zfmisc_1 X1 X2) -> False) -> v4_finsub_1 X2 -> v4_finsub_1 X1 -> m1_subset_1 X4 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X4 X3 X2, ((k1_normform X1 X2 X3 X4) = (k1_normform X1 X2 X4 X3) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X2 -> v4_finsub_1 X1 -> m1_subset_1 X4 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X3 X2 X1, r2_hidden X3 (k2_domain_1 (k5_finsub_1 X2) (k5_finsub_1 X2) X1) -> r2_hidden X3 (k3_domain_1 (k5_finsub_1 X2) (k5_finsub_1 X2) X1) -> m2_subset_1 X1 (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) (k7_normform X2) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_domain_1 X1 X2 X3 X4) (k2_zfmisc_1 X1 X2) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> r2_hidden (esk6_3 X1 X2 X3) X3 -> r2_hidden (esk6_3 X1 X2 X3) X2 -> r2_hidden (esk6_3 X1 X2 X3) X1 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 (k7_normform X2) -> False) -> X1 = X3 -> m1_subset_1 X1 (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) -> r1_xboole_0 (k2_domain_1 (k5_finsub_1 X2) (k5_finsub_1 X2) X1) (k3_domain_1 (k5_finsub_1 X2) (k5_finsub_1 X2) X1) -> False)
  -> (forall X1, m1_subset_1 X1 esk1_0 -> r2_hidden X1 (k2_domain_1 (k5_finsub_1 esk1_0) (k5_finsub_1 esk1_0) esk3_0) -> r2_hidden X1 (k3_domain_1 (k5_finsub_1 esk1_0) (k5_finsub_1 esk1_0) esk2_0) -> False)
  -> (forall X1, m1_subset_1 X1 esk1_0 -> r2_hidden X1 (k2_domain_1 (k5_finsub_1 esk1_0) (k5_finsub_1 esk1_0) esk2_0) -> r2_hidden X1 (k3_domain_1 (k5_finsub_1 esk1_0) (k5_finsub_1 esk1_0) esk3_0) -> False)
  -> (forall X1 X2, (r1_xboole_0 (k2_domain_1 (k5_finsub_1 X1) (k5_finsub_1 X1) (esk9_2 X2 X1)) (k3_domain_1 (k5_finsub_1 X1) (k5_finsub_1 X1) (esk9_2 X2 X1)) -> False) -> r2_hidden X2 (k7_normform X1) -> False)
  -> (forall X4 X1 X2 X3, ((k1_normform X1 X2 X3 X3) = X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X2 -> v4_finsub_1 X1 -> m1_subset_1 X4 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk5_3 X1 X2 X3) X3 -> r2_hidden (esk5_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X4 X3 X2, ((k1_domain_1 X1 X2 X3 X4) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (X3 = (k3_xboole_0 X1 X2) -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk6_3 X1 X2 X3) X2 -> False) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_domain_1 X1 X2 X3) X2 -> False) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_domain_1 X1 X2 X3) X1 -> False) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k5_setwiseo X2 X1 X3) (k5_finsub_1 X2) -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_finsub_1 X1 X2 X3) X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_finsub_1 X1 X2 X3) X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X2 X1, ((k5_setwiseo X2 X1 X3) = (k5_setwiseo X2 X3 X1) -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X3 X2 X1, ((k3_finsub_1 X1 X2 X3) = (k3_finsub_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X2 X1, ((k1_finsub_1 X1 X2 X3) = (k1_finsub_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k5_setwiseo X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X1 X3 X2, ((k3_domain_1 X1 X2 X3) = (k2_xtuple_0 X3) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X3 X2, ((k2_domain_1 X1 X2 X3) = (k1_xtuple_0 X3) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X3 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, ((k3_finsub_1 X1 X2 X3) = (k3_xboole_0 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X2 X1, ((k1_finsub_1 X1 X2 X3) = (k2_xboole_0 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk9_2 X1 X2) (k2_zfmisc_1 (k5_finsub_1 X2) (k5_finsub_1 X2)) -> False) -> r2_hidden X1 (k7_normform X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk8_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1, ((k5_setwiseo X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, ((k3_finsub_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X1 X2, ((k1_finsub_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v4_finsub_1 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk19_2 X3 X2) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1, ((k2_tarski (k2_tarski (k1_xtuple_0 X1) (k2_xtuple_0 X1)) (k1_tarski (k1_xtuple_0 X1))) = X1 -> False) -> v1_xtuple_0 X1 -> False)
  -> (forall X2 X3 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_xboole_0 X2 X3) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk19_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k3_xboole_0 X4 X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk4_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X2 X1, ((esk9_2 X1 X2) = X1 -> False) -> r2_hidden X1 (k7_normform X2) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk12_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_finsub_1 X1 -> False) -> v1_finsub_1 X1 -> v3_finsub_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_hidden (k1_normform (k5_finsub_1 esk1_0) (k5_finsub_1 esk1_0) esk2_0 esk3_0) (k7_normform esk1_0) -> False)
  -> (forall X1, v1_subset_1 (esk17_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k7_normform X1) -> False)
  -> (forall X1, v1_xboole_0 (k5_finsub_1 X1) -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k7_normform X1) (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) (k5_finsub_1 X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk11_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, ((k2_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X2 -> False) -> False)
  -> (forall X2 X1, ((k2_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X2 -> False) -> False)
  -> (forall X1 X2, ((k1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X1 -> False) -> False)
  -> (forall X1 X2, ((k1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) = X1 -> False) -> False)
  -> ((m2_subset_1 esk3_0 (k2_zfmisc_1 (k5_finsub_1 esk1_0) (k5_finsub_1 esk1_0)) (k7_normform esk1_0) -> False) -> False)
  -> ((m2_subset_1 esk2_0 (k2_zfmisc_1 (k5_finsub_1 esk1_0) (k5_finsub_1 esk1_0)) (k7_normform esk1_0) -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk11_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk15_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> ((v1_xtuple_0 esk13_0 -> False) -> False)
  -> ((v2_relat_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
