(** $I sig/MizarPreamble.mgs **)

Theorem t8_classes1:
 forall k9_xtuple_0:set -> set,
 forall v1_funct_1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall v4_ordinal1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk31_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k3_tarski:set -> set,
 forall k10_xtuple_0:set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall esk26_3:set -> set -> set -> set,
 forall esk25_3:set -> set -> set -> set,
 forall a_2_5_classes1:set -> set -> set,
 forall k3_classes1:set -> set -> set,
 forall esk30_3:set -> set -> set -> set,
 forall esk27_3:set -> set -> set -> set,
 forall esk24_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v3_relat_1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v1_setfam_1:set -> prop,
 forall esk11_1:set -> set,
 forall esk4_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall esk8_1:set -> set,
 forall esk20_0:set,
 forall esk15_0:set,
 forall esk9_0:set,
 forall esk6_0:set,
 forall esk10_0:set,
 forall esk22_0:set,
 forall esk23_0:set,
 forall o_0_0_xboole_0:set,
 forall esk17_0:set,
 forall esk7_0:set,
 forall esk5_0:set,
 forall esk14_1:set -> set,
 forall esk19_1:set -> set,
 forall esk12_0:set,
 forall esk13_0:set,
 forall esk18_0:set,
 forall esk21_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_1:set -> set,
 forall esk16_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk28_3:set -> set -> set -> set,
 forall esk29_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_2_4_classes1:set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall k1_xboole_0:set,
 forall k2_classes1:set -> set -> set,
 forall a_2_0_classes1:set -> set -> set,
 forall a_2_1_classes1:set -> set -> set,
 forall k8_subset_1:set -> set -> set -> set,
 forall k1_classes1:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v3_ordinal1:set -> prop,
     (forall X2 X1, ((k2_xboole_0 (k2_xboole_0 (a_2_0_classes1 X2 X1) (a_2_1_classes1 X2 X1)) (k8_subset_1 (k1_zfmisc_1 (k2_classes1 X2 X1)) (k1_zfmisc_1 (k2_classes1 X2 X1)) (k1_classes1 X2))) = (k2_classes1 X2 (k2_xboole_0 X1 (k2_classes1 X1 k1_xboole_0))) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (X3 = k1_xboole_0 -> False) -> ((k2_classes1 X2 X3) = (k3_xboole_0 (k3_tarski (k10_xtuple_0 X1)) (k1_classes1 X2)) -> False) -> (k9_xtuple_0 X1) = X3 -> (k2_classes1 X2 (esk31_3 X2 X3 X1)) = (k1_funct_1 X1 (esk31_3 X2 X3 X1)) -> v3_ordinal1 X3 -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_ordinal1 X1 -> v4_ordinal1 X3 -> False)
  -> (forall X2 X1 X3, (r1_tarski (esk28_3 X1 X2 X3) (esk29_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_4_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, (r1_tarski (esk25_3 X1 X2 X3) (esk26_3 X1 X2 X3) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_0_classes1 X2 X3) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> ((k2_classes1 X1 X2) = (k3_xboole_0 (k3_tarski (k10_xtuple_0 X3)) (k1_classes1 X1)) -> False) -> (r2_hidden (esk31_3 X1 X2 X3) X2 -> False) -> (k9_xtuple_0 X3) = X2 -> v3_ordinal1 X2 -> v1_relat_1 X3 -> v1_funct_1 X3 -> v5_ordinal1 X3 -> v4_ordinal1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden (esk30_3 X1 X2 X3) (k3_classes1 X2 X3) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_5_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, (r2_hidden (esk29_3 X1 X2 X3) (k3_classes1 X2 X3) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_4_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, (r2_hidden (esk27_3 X1 X2 X3) (k2_classes1 X2 X3) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_1_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, (r2_hidden (esk26_3 X1 X2 X3) (k2_classes1 X2 X3) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_0_classes1 X2 X3) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> ((k2_classes1 X1 X2) = (k3_xboole_0 (k3_tarski (k10_xtuple_0 X3)) (k1_classes1 X1)) -> False) -> (v3_ordinal1 (esk31_3 X1 X2 X3) -> False) -> (k9_xtuple_0 X3) = X2 -> v3_ordinal1 X2 -> v1_relat_1 X3 -> v1_funct_1 X3 -> v5_ordinal1 X3 -> v4_ordinal1 X2 -> False)
  -> (forall X1 X4 X2 X5 X3, (r2_hidden X3 (a_2_0_classes1 X2 X5) -> False) -> X1 = X3 -> v3_ordinal1 X5 -> r1_tarski X1 X4 -> m1_subset_1 X4 (k1_classes1 X2) -> m1_subset_1 X1 (k1_classes1 X2) -> r2_hidden X4 (k2_classes1 X2 X5) -> False)
  -> (forall X1 X4 X2 X5 X3, (r2_hidden X3 (a_2_4_classes1 X2 X5) -> False) -> X1 = X3 -> v3_ordinal1 X5 -> r1_tarski X1 X4 -> m1_subset_1 X4 (k1_classes1 X2) -> m1_subset_1 X1 (k1_classes1 X2) -> r2_hidden X4 (k3_classes1 X2 X5) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk30_3 X1 X2 X3) (k1_classes1 X2) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_5_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk29_3 X1 X2 X3) (k1_classes1 X2) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_4_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk28_3 X1 X2 X3) (k1_classes1 X2) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_4_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk27_3 X1 X2 X3) (k1_classes1 X2) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_1_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk26_3 X1 X2 X3) (k1_classes1 X2) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_0_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (esk25_3 X1 X2 X3) (k1_classes1 X2) -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_0_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, ((k1_zfmisc_1 (esk30_3 X1 X2 X3)) = X1 -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_5_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, ((k1_zfmisc_1 (esk27_3 X1 X2 X3)) = X1 -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_1_classes1 X2 X3) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k8_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X4 X3, (r2_hidden X3 (a_2_1_classes1 X2 X4) -> False) -> X3 = (k1_zfmisc_1 X1) -> v3_ordinal1 X4 -> m1_subset_1 X1 (k1_classes1 X2) -> r2_hidden X1 (k2_classes1 X2 X4) -> False)
  -> (forall X1 X2 X4 X3, (r2_hidden X3 (a_2_5_classes1 X2 X4) -> False) -> X3 = (k1_zfmisc_1 X1) -> v3_ordinal1 X4 -> m1_subset_1 X1 (k1_classes1 X2) -> r2_hidden X1 (k3_classes1 X2 X4) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k8_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, v3_ordinal1 X1 -> v1_xboole_0 (k2_xboole_0 X1 (k2_classes1 X1 k1_xboole_0)) -> False)
  -> (forall X2 X1 X3, ((esk28_3 X1 X2 X3) = X1 -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_4_classes1 X2 X3) -> False)
  -> (forall X2 X1 X3, ((esk25_3 X1 X2 X3) = X1 -> False) -> v3_ordinal1 X3 -> r2_hidden X1 (a_2_0_classes1 X2 X3) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk24_2 X3 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> v1_xboole_0 (k1_funct_1 X1 X2) -> m1_subset_1 X2 (k9_xtuple_0 X1) -> False)
  -> (forall X3 X2 X1, ((k8_subset_1 X2 X1 X3) = (k3_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v7_ordinal1 (k2_xboole_0 X1 (k2_classes1 X1 k1_xboole_0)) -> False) -> v3_ordinal1 X1 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k8_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v3_ordinal1 (k2_xboole_0 X1 (k2_classes1 X1 k1_xboole_0)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_classes1 X2 X1) (k1_zfmisc_1 (k1_classes1 X2)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_classes1 X2 X1) (k1_zfmisc_1 (k1_classes1 X2)) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk24_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v4_funct_1 (k2_classes1 X1 k1_xboole_0) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_xboole_0 X1 X2) -> False) -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, ((k3_classes1 X2 X1) = (k2_classes1 X2 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, ((k3_classes1 X2 X1) = (k2_classes1 X2 X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_setfam_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk3_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk4_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_zfmisc_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_zfmisc_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_zfmisc_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (k9_xtuple_0 X1) -> False) -> v1_zfmisc_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk3_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk4_1 X1) -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k3_tarski X1) -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk3_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_xboole_0 (k2_xboole_0 (a_2_4_classes1 esk1_0 esk2_0) (a_2_5_classes1 esk1_0 esk2_0)) (k8_subset_1 (k1_zfmisc_1 (k3_classes1 esk1_0 esk2_0)) (k1_zfmisc_1 (k3_classes1 esk1_0 esk2_0)) (k1_classes1 esk1_0))) = (k3_classes1 esk1_0 (k2_xboole_0 esk2_0 (k2_classes1 esk2_0 k1_xboole_0))) -> False)
  -> (forall X1, v1_xboole_0 (k2_xboole_0 X1 (k2_classes1 X1 k1_xboole_0)) -> False)
  -> (forall X1, v1_xboole_0 (k2_classes1 X1 k1_xboole_0) -> False)
  -> (forall X1, v1_subset_1 (esk8_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_classes1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (v3_funct_1 esk12_0 -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk21_0 -> False) -> False)
  -> ((v2_ordinal1 esk18_0 -> False) -> False)
  -> ((v1_ordinal1 esk18_0 -> False) -> False)
  -> ((v2_funct_1 esk5_0 -> False) -> False)
  -> ((v2_relat_1 esk9_0 -> False) -> False)
  -> ((v2_relat_1 esk7_0 -> False) -> False)
  -> ((v2_relat_1 esk6_0 -> False) -> False)
  -> ((v7_ordinal1 esk13_0 -> False) -> False)
  -> ((v7_ordinal1 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk9_0 -> False) -> False)
  -> ((v1_funct_1 esk7_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk9_0 -> False) -> False)
  -> ((v1_relat_1 esk7_0 -> False) -> False)
  -> ((v1_relat_1 esk6_0 -> False) -> False)
  -> ((v1_relat_1 esk5_0 -> False) -> False)
  -> ((v3_ordinal1 esk23_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v3_ordinal1 esk2_0 -> False) -> False)
  -> ((k1_xboole_0 = o_0_0_xboole_0 -> False) -> False)
  -> False.
Admitted.
