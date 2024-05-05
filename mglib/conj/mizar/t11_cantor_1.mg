(** $I sig/MizarPreamble.mgs **)

Theorem t11_cantor_1:
 forall k10_xtuple_0:set -> set,
 forall k13_prob_1:set -> set -> set -> set -> set -> set,
 forall esk42_3:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk11_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk34_2:set -> set -> set,
 forall v2_finset_1:set -> prop,
 forall v5_finset_1:set -> prop,
 forall v4_card_3:set -> prop,
 forall esk37_1:set -> set,
 forall esk32_1:set -> set,
 forall esk21_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall esk27_1:set -> set,
 forall esk31_0:set,
 forall esk40_0:set,
 forall esk38_0:set,
 forall esk25_0:set,
 forall esk15_0:set,
 forall esk35_2:set -> set -> set,
 forall esk29_0:set,
 forall esk16_0:set,
 forall esk17_0:set,
 forall esk20_0:set,
 forall o_0_0_xboole_0:set,
 forall esk14_0:set,
 forall esk23_0:set,
 forall esk10_1:set -> set,
 forall esk24_1:set -> set,
 forall esk30_2:set -> set -> set,
 forall esk18_2:set -> set -> set,
 forall esk22_0:set,
 forall esk26_0:set,
 forall esk39_0:set,
 forall esk33_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v5_card_3:set -> prop,
 forall v1_card_3:set -> prop,
 forall v2_funcop_1:set -> prop,
 forall esk19_1:set -> set,
 forall esk28_1:set -> set,
 forall esk36_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall esk45_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall k3_tarski:set -> set,
 forall v4_funct_1:set -> prop,
 forall esk9_2:set -> set -> set,
 forall esk44_2:set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall esk7_2:set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall k1_relset_1:set -> set -> set,
 forall k1_xboole_0:set,
 forall k5_setfam_1:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k9_xtuple_0:set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk12_3:set -> set -> set -> set,
 forall a_2_0_cantor_1:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk4_3:set -> set -> set -> set,
 forall k2_cantor_1:set -> set -> set,
 forall esk3_4:set -> set -> set -> set -> set,
 forall v1_finset_1:set -> prop,
 forall esk41_3:set -> set -> set -> set,
 forall esk43_4:set -> set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k8_setfam_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall a_4_0_cantor_1:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall esk13_5:set -> set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
     (forall X4 X3 X1 X2 X5, (m1_subset_1 (esk13_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_4_0_cantor_1 X2 X3 X4 X5) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 (k1_zfmisc_1 X3))) -> False)
  -> (forall X4 X3 X1 X2 X5, (r2_hidden (esk13_5 X1 X2 X3 X4 X5) (k10_xtuple_0 X5) -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_4_0_cantor_1 X2 X3 X4 X5) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 (k1_zfmisc_1 X3))) -> False)
  -> (forall X4 X3 X1 X2 X5, ((k8_setfam_1 X2 (esk13_5 X1 X2 X3 X4 X5)) = X1 -> False) -> v1_funct_1 X5 -> v1_funct_2 X5 X4 (k1_zfmisc_1 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> r2_hidden X1 (a_4_0_cantor_1 X2 X3 X4 X5) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X4 (k1_zfmisc_1 X3))) -> False)
  -> (forall X5 X4 X1 X2 X3, (m1_subset_1 (k13_prob_1 X2 X4 X1 X3 X5) (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> v1_funct_1 X3 -> v1_funct_2 X3 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 (k1_zfmisc_1 X1))) -> False)
  -> (forall X5 X4 X1 X2 X3, ((k13_prob_1 X2 X4 X1 X3 X5) = (k1_funct_1 X3 X5) -> False) -> v1_funct_1 X3 -> v1_funct_2 X3 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X4 (k1_zfmisc_1 X1))) -> False)
  -> (forall X1 X5 X6 X4 X2 X3, (r2_hidden X3 (a_4_0_cantor_1 X2 X5 X6 X4) -> False) -> X3 = (k8_setfam_1 X2 X1) -> v1_funct_1 X4 -> r2_hidden X1 (k10_xtuple_0 X4) -> v1_funct_2 X4 X6 (k1_zfmisc_1 X5) -> m1_subset_1 X6 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X6 (k1_zfmisc_1 X5))) -> False)
  -> (forall X6 X5 X4 X3 X2 X1, (m1_subset_1 (esk43_4 X1 X2 X3 X4) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> X5 = X6 -> (esk41_3 X1 X2 X3) = (k8_setfam_1 X1 X6) -> v1_finset_1 X5 -> r2_hidden X4 X3 -> r2_hidden X5 (k1_zfmisc_1 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X6 X5 X2 X4 X3 X1, ((k8_setfam_1 X2 (esk43_4 X2 X3 X4 X1)) = X1 -> False) -> X5 = X6 -> (esk41_3 X2 X3 X4) = (k8_setfam_1 X2 X6) -> v1_finset_1 X5 -> r2_hidden X1 X4 -> r2_hidden X5 (k1_zfmisc_1 X3) -> m1_subset_1 X6 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X4 X1 X2 X3, (r2_hidden (esk41_3 X1 X2 X3) X3 -> False) -> (m1_subset_1 (esk43_4 X1 X2 X3 X4) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> r2_hidden X4 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2 X3 X4, ((k8_setfam_1 X2 (esk43_4 X2 X3 X4 X1)) = X1 -> False) -> (r2_hidden (esk41_3 X2 X3 X4) X4 -> False) -> r2_hidden X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (esk3_4 X1 X2 X3 X4) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> X3 = (k2_cantor_1 X1 X2) -> r2_hidden X4 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X6 X5 X1 X4 X3 X2, ((k1_funct_1 (esk42_3 X1 X2 X3) X4) = (esk43_4 X1 X2 X3 X4) -> False) -> X5 = X6 -> (esk41_3 X1 X2 X3) = (k8_setfam_1 X1 X6) -> v1_finset_1 X5 -> r2_hidden X4 X3 -> r2_hidden X5 (k1_zfmisc_1 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X1 X2 X3 X4, ((k8_setfam_1 X2 (esk3_4 X2 X3 X4 X1)) = X1 -> False) -> X4 = (k2_cantor_1 X2 X3) -> r2_hidden X1 X4 -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X4 X1 X2 X3, (r1_tarski (esk3_4 X1 X2 X3 X4) X2 -> False) -> X3 = (k2_cantor_1 X1 X2) -> r2_hidden X4 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X4 X1 X2 X3, (v1_finset_1 (esk3_4 X1 X2 X3 X4) -> False) -> X3 = (k2_cantor_1 X1 X2) -> r2_hidden X4 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X4 X1 X2 X3, ((k1_funct_1 (esk42_3 X1 X2 X3) X4) = (esk43_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) X3 -> False) -> r2_hidden X4 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X6 X5 X4 X3 X2 X1, (v1_finset_1 (k1_funct_1 (esk42_3 X1 X2 X3) X4) -> False) -> X5 = X6 -> (esk41_3 X1 X2 X3) = (k8_setfam_1 X1 X6) -> v1_finset_1 X5 -> r2_hidden X4 X3 -> r2_hidden X5 (k1_zfmisc_1 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X5 X4 X1 X3 X2, (m1_subset_1 (esk42_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X3 (k1_zfmisc_1 X2))) -> False) -> X4 = X5 -> (esk41_3 X1 X2 X3) = (k8_setfam_1 X1 X5) -> v1_finset_1 X4 -> r2_hidden X4 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X4 X1 X2 X3, (X3 = (k2_cantor_1 X1 X2) -> False) -> (esk4_3 X1 X2 X3) = (k8_setfam_1 X1 X4) -> v1_finset_1 X4 -> r1_tarski X4 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> r2_hidden (esk4_3 X1 X2 X3) X3 -> False)
  -> (forall X4 X1 X2 X3, (r2_hidden (esk41_3 X1 X2 X3) X3 -> False) -> (v1_finset_1 (k1_funct_1 (esk42_3 X1 X2 X3) X4) -> False) -> r2_hidden X4 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X5 X4 X1 X3 X2, (v1_funct_2 (esk42_3 X1 X2 X3) X3 (k1_zfmisc_1 X2) -> False) -> X4 = X5 -> (esk41_3 X1 X2 X3) = (k8_setfam_1 X1 X5) -> v1_finset_1 X4 -> r2_hidden X4 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (r2_hidden (esk41_3 X1 X2 X3) X3 -> False) -> (m1_subset_1 (esk42_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X3 (k1_zfmisc_1 X2))) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X5 X4 X1 X2 X3, (v1_funct_1 (esk42_3 X1 X2 X3) -> False) -> X4 = X5 -> (esk41_3 X1 X2 X3) = (k8_setfam_1 X1 X5) -> v1_finset_1 X4 -> r2_hidden X4 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (X3 = (k2_cantor_1 X1 X2) -> False) -> ((k8_setfam_1 X1 (esk5_3 X1 X2 X3)) = (esk4_3 X1 X2 X3) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (r2_hidden (esk41_3 X1 X2 X3) X3 -> False) -> (v1_funct_2 (esk42_3 X1 X2 X3) X3 (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (X3 = (k2_cantor_1 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> (m1_subset_1 (esk5_3 X1 X2 X3) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (X3 = (k2_cantor_1 X1 X2) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> (r1_tarski (esk5_3 X1 X2 X3) X2 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X3 X1 X2, (X3 = (k2_cantor_1 X1 X2) -> False) -> (v1_finset_1 (esk5_3 X1 X2 X3) -> False) -> (r2_hidden (esk4_3 X1 X2 X3) X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (m2_subset_1 (esk12_3 X1 X2 X3) (k1_zfmisc_1 (k1_zfmisc_1 X2)) X3 -> False) -> r2_hidden X1 (a_2_0_cantor_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X2))) -> False)
  -> (forall X3 X1 X2, (v1_funct_1 (esk42_3 X1 X2 X3) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X2 X1 X3, ((k8_setfam_1 X2 (esk12_3 X1 X2 X3)) = X1 -> False) -> (v1_xboole_0 X3 -> False) -> r2_hidden X1 (a_2_0_cantor_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X2))) -> False)
  -> (forall X3 X2 X1 X4 X5, (r2_hidden X4 X5 -> False) -> X5 = (k2_cantor_1 X2 X3) -> X4 = (k8_setfam_1 X2 X1) -> v1_finset_1 X1 -> r1_tarski X1 X3 -> m1_subset_1 X4 (k1_zfmisc_1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X4 X2 X1 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X4 (a_2_0_cantor_1 X2 X3) -> False) -> X4 = (k8_setfam_1 X2 X1) -> m2_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) X3 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X2))) -> False)
  -> (forall X3 X1 X2, (X3 = (k2_cantor_1 X1 X2) -> False) -> (m1_subset_1 (esk4_3 X1 X2 X3) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False)
  -> (forall X2 X3 X1, ((k8_setfam_1 X2 X3) = (k8_setfam_1 X2 (k5_setfam_1 (k1_zfmisc_1 X2) X1)) -> False) -> (v1_xboole_0 X1 -> False) -> X3 = (a_2_0_cantor_1 X2 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X2))) -> False)
  -> (forall X3 X2 X1, (v1_finset_1 X1 -> False) -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X3, (X3 = k1_xboole_0 -> False) -> ((k1_relset_1 X2 X1) = X2 -> False) -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (X1 = k1_xboole_0 -> False) -> X3 = k1_xboole_0 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v1_funct_2 X2 X1 X3 -> False) -> (k1_relset_1 X1 X2) = X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X2 X3, (v1_funct_2 X1 X2 X3 -> False) -> X3 = k1_xboole_0 -> X1 = k1_xboole_0 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk6_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk6_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk7_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_relat_1 X1 -> v1_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk11_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk8_2 X1 X2)) = (esk7_2 X1 X2) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_cantor_1 X2 X1) (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk44_2 X3 X2) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk7_2 X1 X2) X2 -> False) -> (r2_hidden (esk8_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_relat_1 X2 -> v1_funct_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (r1_tarski X1 (k2_cantor_1 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk44_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk34_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 X1 X2 -> False) -> v1_relat_1 X1 -> r1_tarski (k10_xtuple_0 X1) X2 -> False)
  -> (forall X2 X1, (v1_finset_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski (k10_xtuple_0 X1) X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk34_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk34_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (r1_tarski (k3_tarski X1) (k3_tarski X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski (k1_zfmisc_1 X1) (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_funct_1 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_zfmisc_1 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> r2_hidden X1 X2 -> v1_finset_1 (k3_tarski X2) -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_card_3 X2 -> False) -> v4_card_3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk34_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk34_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk34_2 X1 X2) -> False) -> False)
  -> (forall X1, (v1_finset_1 (k3_tarski X1) -> False) -> (r2_hidden (esk45_1 X1) X1 -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v1_finset_1 (k3_tarski X1) -> False) -> v1_finset_1 X1 -> v1_finset_1 (esk45_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_card_3 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_finset_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k3_tarski X1) -> False) -> v1_finset_1 X1 -> v5_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk37_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk36_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k3_tarski X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk32_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (v5_card_3 X1 -> False) -> v4_card_3 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (k9_xtuple_0 X1) = k1_xboole_0 -> v1_relat_1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> (k10_xtuple_0 X1) = k1_xboole_0 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk37_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk32_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk21_1 X1) -> False) -> False)
  -> (forall X1, v1_finset_1 X1 -> v5_card_3 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v5_card_3 X1 -> False)
  -> (forall X1, (v4_card_3 X1 -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_cantor_1 esk1_0 (k2_cantor_1 esk1_0 esk2_0)) = (k2_cantor_1 esk1_0 esk2_0) -> False)
  -> (forall X1, v1_subset_1 (esk27_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk31_0 -> False)
  -> (v1_finset_1 esk33_0 -> False)
  -> (v1_xboole_0 esk40_0 -> False)
  -> (v1_xboole_0 esk39_0 -> False)
  -> (v1_xboole_0 esk38_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk18_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk35_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk30_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk18_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk35_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk30_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk18_2 X1 X2) X2 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk30_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk35_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk30_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk35_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk30_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k3_tarski (k1_zfmisc_1 X1)) = X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk24_1 X1) -> False) -> False)
  -> ((v2_finset_1 esk40_0 -> False) -> False)
  -> ((v5_finset_1 esk39_0 -> False) -> False)
  -> ((v3_funct_1 esk22_0 -> False) -> False)
  -> ((v5_card_3 esk29_0 -> False) -> False)
  -> ((v2_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funcop_1 esk16_0 -> False) -> False)
  -> ((v4_funct_1 esk38_0 -> False) -> False)
  -> ((v1_finset_1 esk39_0 -> False) -> False)
  -> ((v1_finset_1 esk26_0 -> False) -> False)
  -> ((v1_finset_1 esk15_0 -> False) -> False)
  -> ((v1_card_3 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk40_0 -> False) -> False)
  -> ((v1_funct_1 esk33_0 -> False) -> False)
  -> ((v1_funct_1 esk31_0 -> False) -> False)
  -> ((v1_funct_1 esk26_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_relat_1 esk40_0 -> False) -> False)
  -> ((v1_relat_1 esk33_0 -> False) -> False)
  -> ((v1_relat_1 esk31_0 -> False) -> False)
  -> ((v1_relat_1 esk26_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> (((k3_tarski k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (((k9_xtuple_0 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (((k10_xtuple_0 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
