(** $I sig/MizarPreamble.mgs **)

Theorem t6_coh_sp:
 forall esk13_2:set -> set -> set,
 forall esk35_0:set,
 forall k2_tarski:set -> set -> set,
 forall esk33_0:set,
 forall esk37_2:set -> set -> set,
 forall esk36_1:set -> set,
 forall esk9_1:set -> set,
 forall esk11_2:set -> set -> set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall v1_xboole_0:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk31_1:set -> set,
 forall esk30_1:set -> set,
 forall esk19_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk26_1:set -> set,
 forall esk29_0:set,
 forall esk27_0:set,
 forall esk18_0:set,
 forall esk15_1:set -> set,
 forall esk22_0:set,
 forall esk17_0:set,
 forall esk20_0:set,
 forall o_0_0_xboole_0:set,
 forall esk21_0:set,
 forall esk25_0:set,
 forall esk23_1:set -> set,
 forall esk16_0:set,
 forall esk24_0:set,
 forall esk32_0:set,
 forall k1_xboole_0:set,
 forall v3_relat_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk28_1:set -> set,
 forall esk5_1:set -> set,
 forall esk6_1:set -> set,
 forall v4_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_classes1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk10_2:set -> set -> set,
 forall esk34_0:set,
 forall esk14_2:set -> set -> set,
 forall esk12_3:set -> set -> set -> set,
 forall v1_coh_sp:set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k3_tarski:set -> set,
     (forall X2 X1, (r2_hidden (k3_tarski X2) X1 -> False) -> v1_coh_sp X1 -> r1_tarski X2 X1 -> r2_hidden (k2_xboole_0 (esk7_2 X1 X2) (esk8_2 X1 X2)) X1 -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk13_2 X1 X2) X3 -> r2_hidden (esk13_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk12_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk12_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk13_2 X1 X2) X2 -> False) -> (r2_hidden (esk13_2 X1 X2) (esk14_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski esk33_0 esk33_0) = esk35_0 -> False) -> ((k2_tarski (esk37_2 X1 X2) (esk37_2 X1 X2)) = X2 -> False) -> r2_hidden X2 (esk36_1 X1) -> False)
  -> (forall X2 X1, ((k2_tarski esk33_0 esk33_0) = esk34_0 -> False) -> ((k2_tarski (esk37_2 X1 X2) (esk37_2 X1 X2)) = X2 -> False) -> r2_hidden X2 (esk36_1 X1) -> False)
  -> (forall X1 X3 X2, (v1_coh_sp X2 -> False) -> (r2_hidden (k2_xboole_0 X1 X3) X2 -> False) -> r2_hidden X3 (esk9_1 X2) -> r2_hidden X1 (esk9_1 X2) -> False)
  -> (forall X2 X1, (X2 = (k2_tarski X1 X1) -> False) -> (esk10_2 X1 X2) = X1 -> r2_hidden (esk10_2 X1 X2) X2 -> False)
  -> (forall X2 X1, ((k2_tarski (esk37_2 X1 X2) (esk37_2 X1 X2)) = X2 -> False) -> esk35_0 = esk34_0 -> r2_hidden X2 (esk36_1 X1) -> False)
  -> (forall X1 X2, (r2_hidden esk1_0 esk2_0 -> False) -> (r2_hidden (k2_tarski X1 X2) esk2_0 -> False) -> r2_hidden X2 esk1_0 -> r2_hidden X1 esk1_0 -> False)
  -> (forall X2 X1, (r2_hidden (k3_tarski X2) X1 -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> v1_coh_sp X1 -> r1_tarski X2 X1 -> False)
  -> (forall X2 X1, (r2_hidden (k3_tarski X2) X1 -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> v1_coh_sp X1 -> r1_tarski X2 X1 -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk13_2 X1 X2) X2 -> False) -> (r2_hidden (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k2_tarski X1 X3) X2 -> False) -> r2_hidden X3 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k2_tarski esk33_0 esk33_0) = esk35_0 -> False) -> (r2_hidden (esk37_2 X1 X2) X1 -> False) -> r2_hidden X2 (esk36_1 X1) -> False)
  -> (forall X2 X1, ((k2_tarski esk33_0 esk33_0) = esk34_0 -> False) -> (r2_hidden (esk37_2 X1 X2) X1 -> False) -> r2_hidden X2 (esk36_1 X1) -> False)
  -> (forall X2 X3 X1, ((k2_tarski esk33_0 esk33_0) = esk35_0 -> False) -> (r2_hidden X3 (esk36_1 X2) -> False) -> (k2_tarski X1 X1) = X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X3 X1, ((k2_tarski esk33_0 esk33_0) = esk34_0 -> False) -> (r2_hidden X3 (esk36_1 X2) -> False) -> (k2_tarski X1 X1) = X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk11_2 X1 X2) X2 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 X2 -> False) -> r1_tarski (k2_tarski X1 X3) X2 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 X2 -> False) -> r1_tarski (k2_tarski X3 X1) X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk37_2 X1 X2) X1 -> False) -> esk35_0 = esk34_0 -> r2_hidden X2 (esk36_1 X1) -> False)
  -> (forall X2 X1, (X2 = (k2_tarski X1 X1) -> False) -> ((esk10_2 X1 X2) = X1 -> False) -> (r2_hidden (esk10_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (r2_hidden esk1_0 esk2_0 -> r2_hidden (k2_tarski esk3_0 esk4_0) esk2_0 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 (esk36_1 X2) -> False) -> esk35_0 = esk34_0 -> (k2_tarski X1 X1) = X3 -> r2_hidden X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 X1 -> False) -> v1_classes1 X1 -> r2_hidden X2 X1 -> r1_tarski X3 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_coh_sp X1 -> False) -> r2_hidden (k3_tarski (esk9_1 X1)) X1 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k2_tarski X3 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v4_funct_1 (k2_tarski X1 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k2_tarski X2 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> r2_hidden (esk6_1 X1) X1 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> (r1_tarski (esk6_1 X1) (esk5_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> ((r2_hidden esk4_0 esk1_0 -> False) -> r2_hidden esk1_0 esk2_0 -> False)
  -> ((r2_hidden esk3_0 esk1_0 -> False) -> r2_hidden esk1_0 esk2_0 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_coh_sp X1 -> False) -> (r1_tarski (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_classes1 X1 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk31_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk30_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xboole_0 (k2_tarski X1 X1) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk26_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk29_0 -> False)
  -> (v1_xboole_0 esk32_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> (forall X1 X2, ((k2_xboole_0 (k2_tarski X1 X1) (k2_tarski X2 X2)) = (k2_tarski X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk23_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk32_0 -> False) -> False)
  -> ((v2_relat_1 esk27_0 -> False) -> False)
  -> ((v2_relat_1 esk25_0 -> False) -> False)
  -> ((v2_relat_1 esk22_0 -> False) -> False)
  -> ((v2_funct_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_coh_sp esk16_0 -> False) -> False)
  -> ((v1_coh_sp esk2_0 -> False) -> False)
  -> ((v1_classes1 esk16_0 -> False) -> False)
  -> ((v1_classes1 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
