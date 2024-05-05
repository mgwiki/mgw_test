(** $I sig/MizarPreamble.mgs **)

Theorem t27_funct_1:
 forall esk5_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk6_2:set -> set -> set,
 forall k1_tarski:set -> set,
 forall esk4_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk19_1:set -> set,
 forall k1_xboole_0:set,
 forall v3_relat_1:set -> prop,
 forall esk17_0:set,
 forall esk14_0:set,
 forall esk15_0:set,
 forall esk13_0:set,
 forall esk11_0:set,
 forall o_0_0_xboole_0:set,
 forall esk10_1:set -> set,
 forall esk12_0:set,
 forall esk16_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk18_1:set -> set,
 forall esk9_1:set -> set,
 forall esk8_1:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall esk7_2:set -> set -> set,
 forall esk1_0:set,
 forall v2_funct_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk20_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k3_relat_1:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
     (forall X1 X3 X2, ((k1_funct_1 (k3_relat_1 X2 X1) X3) = (k1_funct_1 X1 (k1_funct_1 X2 X3)) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 (k3_relat_1 X2 X1)) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk5_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> (k1_funct_1 X1 (esk20_2 X1 X2)) = (k1_funct_1 X2 (esk20_2 X1 X2)) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk5_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> (v2_funct_1 esk1_0 -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> (k3_relat_1 X1 esk1_0) = (k3_relat_1 X2 esk1_0) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r1_tarski (k10_xtuple_0 X2) (k9_xtuple_0 esk1_0) -> r1_tarski (k10_xtuple_0 X1) (k9_xtuple_0 esk1_0) -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk6_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k3_relat_1 X1 X2) X3) = (k1_funct_1 X2 (k1_funct_1 X1 X3)) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (k1_funct_1 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden X2 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk7_2 X1 X2)) = (esk6_2 X1 X2) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (esk7_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk4_2 X1 X2) = X1 -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk20_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, ((k9_xtuple_0 (k3_relat_1 X1 X2)) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> r1_tarski (k10_xtuple_0 X1) (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k1_tarski (k1_funct_1 X1 X2)) = (k10_xtuple_0 X1) -> False) -> (k1_tarski X2) = (k9_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk4_2 X1 X2) = X1 -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> False)
  -> (forall X1, ((k1_funct_1 X1 (esk8_1 X1)) = (k1_funct_1 X1 (esk9_1 X1)) -> False) -> (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v2_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, ((k1_funct_1 (esk19_1 X2) X1) = X2 -> False) -> r2_hidden X1 (k1_tarski k1_xboole_0) -> False)
  -> (forall X2 X1, ((k1_funct_1 (esk18_1 X2) X1) = X2 -> False) -> r2_hidden X1 (k1_tarski k1_xboole_0) -> False)
  -> (forall X2 X1, (r2_hidden X1 X2 -> False) -> r1_tarski (k1_tarski X1) X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r2_hidden (esk9_1 X1) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r2_hidden (esk8_1 X1) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_xboole_0 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski (k1_tarski X1) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (esk8_1 X1) = (esk9_1 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (((k3_relat_1 esk3_0 esk1_0) = (k3_relat_1 esk2_0 esk1_0) -> False) -> v2_funct_1 esk1_0 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> ((r1_tarski (k10_xtuple_0 esk3_0) (k9_xtuple_0 esk1_0) -> False) -> v2_funct_1 esk1_0 -> False)
  -> ((r1_tarski (k10_xtuple_0 esk2_0) (k9_xtuple_0 esk1_0) -> False) -> v2_funct_1 esk1_0 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (((k9_xtuple_0 esk3_0) = (k9_xtuple_0 esk2_0) -> False) -> v2_funct_1 esk1_0 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> v2_funct_1 esk1_0 -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> v2_funct_1 esk1_0 -> False)
  -> ((v1_relat_1 esk3_0 -> False) -> v2_funct_1 esk1_0 -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> v2_funct_1 esk1_0 -> False)
  -> (esk3_0 = esk2_0 -> v2_funct_1 esk1_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_zfmisc_1 esk17_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k9_xtuple_0 (esk19_1 X1)) = (k1_tarski k1_xboole_0) -> False) -> False)
  -> (forall X1, ((k9_xtuple_0 (esk18_1 X1)) = (k1_tarski k1_xboole_0) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k1_tarski X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk18_1 X1) -> False) -> False)
  -> ((v2_relat_1 esk15_0 -> False) -> False)
  -> ((v1_zfmisc_1 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk11_0 -> False) -> False)
  -> ((v1_funct_1 esk1_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_relat_1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
