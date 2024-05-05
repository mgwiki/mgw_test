(** $I sig/MizarPreamble.mgs **)

Theorem t10_cantor_1:
 forall k8_setfam_1:set -> set -> set,
 forall esk35_3:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k3_tarski:set -> set,
 forall esk6_2:set -> set -> set,
 forall esk34_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall v5_finset_1:set -> prop,
 forall v4_card_3:set -> prop,
 forall esk30_1:set -> set,
 forall esk27_1:set -> set,
 forall esk17_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall k1_xboole_0:set,
 forall esk23_1:set -> set,
 forall esk26_0:set,
 forall esk33_0:set,
 forall esk31_0:set,
 forall esk21_0:set,
 forall esk12_0:set,
 forall esk19_0:set,
 forall esk14_0:set,
 forall esk16_0:set,
 forall o_0_0_xboole_0:set,
 forall esk11_0:set,
 forall esk13_0:set,
 forall esk25_0:set,
 forall esk8_1:set -> set,
 forall esk20_1:set -> set,
 forall esk18_0:set,
 forall esk22_0:set,
 forall esk32_0:set,
 forall esk28_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall v5_card_3:set -> prop,
 forall v2_finset_1:set -> prop,
 forall v1_card_3:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall v2_funcop_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall esk15_1:set -> set,
 forall esk24_1:set -> set,
 forall esk29_1:set -> set,
 forall v1_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall k5_setfam_1:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk9_2:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk10_3:set -> set -> set -> set,
 forall k9_setfam_1:set -> set,
 forall a_2_0_cantor_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (m2_subset_1 (esk10_3 X1 X2 X3) (k9_setfam_1 (k9_setfam_1 X2)) X3 -> False) -> r2_hidden X1 (a_2_0_cantor_1 X2 X3) -> m1_subset_1 X3 (k9_setfam_1 (k9_setfam_1 (k9_setfam_1 X2))) -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 (k8_setfam_1 X2 X3) -> False) -> r2_hidden X1 X2 -> m1_subset_1 X3 (k9_setfam_1 (k9_setfam_1 X2)) -> r2_hidden X1 (esk35_3 X2 X1 X3) -> False)
  -> (forall X2 X1 X3, ((k8_setfam_1 X2 (esk10_3 X1 X2 X3)) = X1 -> False) -> (v1_xboole_0 X3 -> False) -> r2_hidden X1 (a_2_0_cantor_1 X2 X3) -> m1_subset_1 X3 (k9_setfam_1 (k9_setfam_1 (k9_setfam_1 X2))) -> False)
  -> (forall X4 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X4 (a_2_0_cantor_1 X2 X3) -> False) -> X4 = (k8_setfam_1 X2 X1) -> m2_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) X3 -> m1_subset_1 X3 (k9_setfam_1 (k9_setfam_1 (k9_setfam_1 X2))) -> False)
  -> (forall X2 X1 X3, (r2_hidden X2 (k8_setfam_1 X1 X3) -> False) -> (r2_hidden (esk35_3 X1 X2 X3) X3 -> False) -> r2_hidden X2 X1 -> m1_subset_1 X3 (k9_setfam_1 (k9_setfam_1 X1)) -> False)
  -> (forall X2 X1 X3, (r1_tarski (k8_setfam_1 X2 X3) (k8_setfam_1 X2 X1) -> False) -> r1_tarski X1 X3 -> m1_subset_1 X3 (k9_setfam_1 (k9_setfam_1 X2)) -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> r2_hidden X4 X3 -> r2_hidden X1 X2 -> r2_hidden X1 (k8_setfam_1 X2 X3) -> m1_subset_1 X3 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk6_2 X1 X2) X3 -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk5_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk5_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k9_setfam_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk9_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (esk6_2 X1 X2) (esk7_2 X1 X2) -> False) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk34_2 X3 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k9_setfam_1 X2) -> False) -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_setfam_1 X2 X1) (k9_setfam_1 X2) -> False) -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k9_setfam_1 (k9_setfam_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk34_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k9_setfam_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk4_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k9_setfam_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v4_card_3 X2 -> False) -> v4_card_3 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k9_setfam_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 (k3_tarski X2) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k9_setfam_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_card_3 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (k3_tarski X1) -> False) -> v1_finset_1 X1 -> v5_finset_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk30_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk29_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v5_finset_1 (k9_setfam_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k9_setfam_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_3 X1 -> False) -> v4_card_3 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, v1_finset_1 X1 -> v5_card_3 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v5_card_3 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k8_setfam_1 esk1_0 (k5_setfam_1 (k9_setfam_1 esk1_0) esk2_0)) = (k8_setfam_1 esk1_0 esk3_0) -> False)
  -> (forall X1, v1_subset_1 (esk23_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k9_setfam_1 X1) -> False)
  -> (v3_funct_1 esk26_0 -> False)
  -> (v1_finset_1 esk28_0 -> False)
  -> (v1_xboole_0 esk33_0 -> False)
  -> (v1_xboole_0 esk32_0 -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> ((m1_subset_1 esk2_0 (k9_setfam_1 (k9_setfam_1 (k9_setfam_1 esk1_0))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k9_setfam_1 X1) (k9_setfam_1 (k9_setfam_1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k9_setfam_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k9_setfam_1 (k9_setfam_1 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (((a_2_0_cantor_1 esk1_0 esk2_0) = esk3_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk20_1 X1) -> False) -> False)
  -> ((v2_finset_1 esk33_0 -> False) -> False)
  -> ((v4_funct_1 esk31_0 -> False) -> False)
  -> ((v5_finset_1 esk32_0 -> False) -> False)
  -> ((v3_funct_1 esk18_0 -> False) -> False)
  -> ((v5_card_3 esk25_0 -> False) -> False)
  -> ((v2_funct_1 esk19_0 -> False) -> False)
  -> ((v1_funcop_1 esk13_0 -> False) -> False)
  -> ((v1_finset_1 esk32_0 -> False) -> False)
  -> ((v1_finset_1 esk22_0 -> False) -> False)
  -> ((v1_finset_1 esk12_0 -> False) -> False)
  -> ((v1_card_3 esk11_0 -> False) -> False)
  -> ((v1_funct_1 esk33_0 -> False) -> False)
  -> ((v1_funct_1 esk28_0 -> False) -> False)
  -> ((v1_funct_1 esk26_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk19_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk13_0 -> False) -> False)
  -> ((v1_funct_1 esk11_0 -> False) -> False)
  -> ((v1_relat_1 esk33_0 -> False) -> False)
  -> ((v1_relat_1 esk28_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
