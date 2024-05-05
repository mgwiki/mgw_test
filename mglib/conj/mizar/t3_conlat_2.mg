(** $I sig/MizarPreamble.mgs **)

Theorem t3_conlat_2:
 forall a_2_6_conlat_2:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall r1_conlat_1:set -> set -> set -> prop,
 forall esk20_4:set -> set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk17_4:set -> set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall esk21_3:set -> set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall k1_xboole_0:set,
 forall k1_setfam_1:set -> set,
 forall esk3_3:set -> set -> set -> set,
 forall o_2_9_conlat_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk4_2:set -> set -> set,
 forall esk5_2:set -> set -> set,
 forall k3_tarski:set -> set,
 forall esk9_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall esk15_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk37_1:set -> set,
 forall l5_struct_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk32_1:set -> set,
 forall esk26_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall l1_struct_0:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk36_0:set,
 forall esk24_2:set -> set -> set,
 forall esk14_1:set -> set,
 forall esk13_0:set,
 forall esk27_0:set,
 forall esk11_0:set,
 forall o_0_0_xboole_0:set,
 forall esk23_0:set,
 forall esk12_0:set,
 forall esk28_1:set -> set,
 forall esk33_2:set -> set -> set,
 forall esk25_2:set -> set -> set,
 forall esk31_0:set,
 forall esk29_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall esk30_1:set -> set,
 forall esk34_1:set -> set,
 forall esk35_1:set -> set,
 forall v4_funct_1:set -> prop,
 forall esk38_2:set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk8_3:set -> set -> set -> set,
 forall o_2_8_conlat_2:set -> set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall esk19_3:set -> set -> set -> set,
 forall esk18_3:set -> set -> set -> set,
 forall a_2_5_conlat_2:set -> set -> set,
 forall k5_setfam_1:set -> set -> set,
 forall a_2_7_conlat_2:set -> set -> set,
 forall esk22_4:set -> set -> set -> set -> set,
 forall v1_conlat_1:set -> prop,
 forall l1_conlat_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall u4_struct_0:set -> set,
 forall esk7_2:set -> set -> set,
 forall a_2_1_conlat_1:set -> set -> set,
 forall k2_conlat_1:set -> set,
     (forall X2 X1, (X2 = (k2_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> (k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) X2 (esk7_2 X1 X2)) = (a_2_1_conlat_1 X1 (esk7_2 X1 X2)) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)))) -> False)
  -> (forall X4 X2 X3 X1, (v1_conlat_1 X1 -> False) -> (v1_xboole_0 X4 -> False) -> (r2_hidden X3 (a_2_6_conlat_2 X1 X4) -> False) -> X2 = X3 -> l1_conlat_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X1))) -> r1_conlat_1 X1 X2 (esk20_4 X3 X1 X4 X2) -> False)
  -> (forall X3 X4 X2 X1, (v1_conlat_1 X1 -> False) -> (r2_hidden X3 (a_2_7_conlat_2 X1 X4) -> False) -> X2 = X3 -> l1_conlat_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u4_struct_0 X1)) -> r1_conlat_1 X1 X2 (esk22_4 X3 X1 X4 X2) -> False)
  -> (forall X3 X4 X2 X1, (v1_conlat_1 X1 -> False) -> (r2_hidden X3 (a_2_1_conlat_1 X1 X4) -> False) -> X2 = X3 -> l1_conlat_1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u4_struct_0 X1)) -> r1_conlat_1 X1 X2 (esk17_4 X3 X1 X4 X2) -> False)
  -> (forall X1 X3 X2, ((k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X2)) (k1_zfmisc_1 (u1_struct_0 X2)) X1 X3) = (a_2_1_conlat_1 X2 X3) -> False) -> (v1_conlat_1 X2 -> False) -> X1 = (k2_conlat_1 X2) -> l1_conlat_1 X2 -> v1_funct_1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> v1_funct_2 X1 (k1_zfmisc_1 (u4_struct_0 X2)) (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X2)) (k1_zfmisc_1 (u1_struct_0 X2)))) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X4 X1 X2, (v1_conlat_1 X2 -> False) -> (v1_xboole_0 X3 -> False) -> (r2_hidden X1 (a_2_6_conlat_2 X2 X3) -> False) -> (r2_hidden (esk20_4 X1 X2 X3 X4) (k5_setfam_1 (u4_struct_0 X2) X3) -> False) -> X1 = X4 -> l1_conlat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X2))) -> False)
  -> (forall X3 X4 X1 X2, (v1_conlat_1 X2 -> False) -> (v1_xboole_0 X3 -> False) -> (r2_hidden X1 (a_2_6_conlat_2 X2 X3) -> False) -> (m1_subset_1 (esk20_4 X1 X2 X3 X4) (u4_struct_0 X2) -> False) -> X1 = X4 -> l1_conlat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X2))) -> False)
  -> (forall X4 X1 X3 X2, (v1_conlat_1 X2 -> False) -> (v1_xboole_0 X4 -> False) -> (r2_hidden X3 (a_2_5_conlat_2 X2 X4) -> False) -> X3 = (k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X2)) (k1_zfmisc_1 (u1_struct_0 X2)) (k2_conlat_1 X2) X1) -> l1_conlat_1 X2 -> r2_hidden X1 X4 -> m1_subset_1 X1 (k1_zfmisc_1 (u4_struct_0 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X2))) -> False)
  -> (forall X1 X3 X4 X2, (v1_conlat_1 X2 -> False) -> (r2_hidden X1 (a_2_7_conlat_2 X2 X3) -> False) -> (m1_subset_1 (esk22_4 X1 X2 X3 X4) (u4_struct_0 X2) -> False) -> X1 = X4 -> l1_conlat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> False)
  -> (forall X1 X3 X4 X2, (v1_conlat_1 X2 -> False) -> (r2_hidden X1 (a_2_1_conlat_1 X2 X3) -> False) -> (m1_subset_1 (esk17_4 X1 X2 X3 X4) (u4_struct_0 X2) -> False) -> X1 = X4 -> l1_conlat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> False)
  -> (forall X1 X3 X4 X2, (v1_conlat_1 X2 -> False) -> (r2_hidden X1 (a_2_7_conlat_2 X2 X3) -> False) -> (r2_hidden (esk22_4 X1 X2 X3 X4) X3 -> False) -> X1 = X4 -> l1_conlat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> False)
  -> (forall X1 X3 X4 X2, (v1_conlat_1 X2 -> False) -> (r2_hidden X1 (a_2_1_conlat_1 X2 X3) -> False) -> (r2_hidden (esk17_4 X1 X2 X3 X4) X3 -> False) -> X1 = X4 -> l1_conlat_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> False)
  -> (forall X2 X1, (X2 = (k2_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> (m1_subset_1 (esk7_2 X1 X2) (k1_zfmisc_1 (u4_struct_0 X1)) -> False) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)))) -> False)
  -> (forall X3 X1 X2, ((k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X2)) (k1_zfmisc_1 (u1_struct_0 X2)) (k2_conlat_1 X2) (esk18_3 X1 X2 X3)) = X1 -> False) -> (v1_conlat_1 X2 -> False) -> (v1_xboole_0 X3 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_2_5_conlat_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X2))) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X4 X2, (v1_conlat_1 X2 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_conlat_1 X2 (esk19_3 X4 X2 X3) X1 -> False) -> l1_conlat_1 X2 -> m1_subset_1 X1 (u4_struct_0 X2) -> r2_hidden X4 (a_2_6_conlat_2 X2 X3) -> r2_hidden X1 (k5_setfam_1 (u4_struct_0 X2) X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X2))) -> False)
  -> (forall X4 X1 X3 X2, (v1_conlat_1 X2 -> False) -> (r1_conlat_1 X2 (esk21_3 X4 X2 X3) X1 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 X3 -> m1_subset_1 X1 (u4_struct_0 X2) -> r2_hidden X4 (a_2_7_conlat_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> False)
  -> (forall X4 X1 X3 X2, (v1_conlat_1 X2 -> False) -> (r1_conlat_1 X2 (esk16_3 X4 X2 X3) X1 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 X3 -> m1_subset_1 X1 (u4_struct_0 X2) -> r2_hidden X4 (a_2_1_conlat_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> False)
  -> (forall X3 X1 X2, (v1_conlat_1 X2 -> False) -> (v1_xboole_0 X3 -> False) -> (m1_subset_1 (esk18_3 X1 X2 X3) (k1_zfmisc_1 (u4_struct_0 X2)) -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_2_5_conlat_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X2))) -> False)
  -> (forall X3 X1 X2, (v1_conlat_1 X2 -> False) -> (v1_xboole_0 X3 -> False) -> (m1_subset_1 (esk19_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_2_6_conlat_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X2))) -> False)
  -> (forall X3 X1 X2, (v1_conlat_1 X2 -> False) -> (v1_xboole_0 X3 -> False) -> (r2_hidden (esk18_3 X1 X2 X3) X3 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_2_5_conlat_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (v1_conlat_1 X2 -> False) -> (m1_subset_1 (esk21_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_2_7_conlat_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v1_conlat_1 X2 -> False) -> (m1_subset_1 (esk16_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_2_1_conlat_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (m1_subset_1 (k2_conlat_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)))) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X3 X1 X2, ((esk19_3 X1 X2 X3) = X1 -> False) -> (v1_conlat_1 X2 -> False) -> (v1_xboole_0 X3 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_2_6_conlat_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X2))) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X3 = (k1_setfam_1 X2) -> r2_hidden X1 (esk3_3 X2 X3 X1) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (v1_conlat_1 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 (o_2_9_conlat_2 X1 X2) (k1_zfmisc_1 (u4_struct_0 X1)) X2 -> False) -> l1_conlat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X1))) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, ((esk21_3 X1 X2 X3) = X1 -> False) -> (v1_conlat_1 X2 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_2_7_conlat_2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((esk16_3 X1 X2 X3) = X1 -> False) -> (v1_conlat_1 X2 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_2_1_conlat_1 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> r2_hidden (esk4_2 X1 X2) X2 -> r2_hidden (esk4_2 X1 X2) (esk5_2 X1 X2) -> False)
  -> (forall X2 X1, (v1_conlat_1 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (o_2_8_conlat_2 X1 X2) (a_2_5_conlat_2 X1 X2) -> False) -> l1_conlat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X1))) -> False)
  -> (forall X3 X2 X1, (X2 = (k3_tarski X1) -> False) -> r2_hidden X3 X1 -> r2_hidden (esk9_2 X1 X2) X3 -> r2_hidden (esk9_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> X2 = (k3_tarski X1) -> r2_hidden X3 X2 -> False)
  -> (forall X2 X3 X1, (r2_hidden X1 (esk8_3 X2 X3 X1) -> False) -> X3 = (k3_tarski X2) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (r2_hidden X3 X2 -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X1 -> False) -> X2 = (k1_setfam_1 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk15_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk9_2 X1 X2) X2 -> False) -> (r2_hidden (esk9_2 X1 X2) (esk10_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk5_2 X1 X2) X1 -> False) -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (X1 = k1_xboole_0 -> False) -> (X2 = (k1_setfam_1 X1) -> False) -> (r2_hidden (esk4_2 X1 X2) X3 -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> r2_hidden X3 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v1_funct_2 (k2_conlat_1 X1) (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk38_2 X3 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_setfam_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X1 X2, (X2 = (k3_tarski X1) -> False) -> (r2_hidden (esk9_2 X1 X2) X2 -> False) -> (r2_hidden (esk10_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X3 X1 X2 X4, (X4 = k1_xboole_0 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k1_setfam_1 X4) -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k5_setfam_1 X2 X1) = (k3_tarski X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> X4 = (k3_tarski X3) -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk38_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 (u4_struct_0 X1)) -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l5_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk34_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (esk37_1 X1) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (esk35_1 X1) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (u4_struct_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v1_funct_1 (k2_conlat_1 X1) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk34_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk32_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk32_1 X1) -> False) -> False)
  -> (forall X2 X1, (X1 = k1_xboole_0 -> False) -> X2 = k1_xboole_0 -> X1 = (k1_setfam_1 X2) -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (l5_struct_0 X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = (k1_setfam_1 X2) -> False) -> X2 = k1_xboole_0 -> X1 = k1_xboole_0 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k3_funct_2 (k1_zfmisc_1 (u4_struct_0 esk1_0)) (k1_zfmisc_1 (u1_struct_0 esk1_0)) (k2_conlat_1 esk1_0) (k5_setfam_1 (u4_struct_0 esk1_0) esk2_0)) = (k1_setfam_1 (a_2_5_conlat_2 esk1_0 esk2_0)) -> False)
  -> (forall X1, v1_subset_1 (esk29_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk31_0 -> False)
  -> (v1_xboole_0 esk36_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> (v1_conlat_1 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk25_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk24_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk24_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 esk1_0))) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk33_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk24_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk33_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk24_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk33_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk24_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk33_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk24_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk28_1 X1) -> False) -> False)
  -> ((l1_struct_0 esk12_0 -> False) -> False)
  -> ((l5_struct_0 esk13_0 -> False) -> False)
  -> ((v4_funct_1 esk36_0 -> False) -> False)
  -> ((v2_funct_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk31_0 -> False) -> False)
  -> ((v1_relat_1 esk27_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk31_0 -> False) -> False)
  -> ((v1_funct_1 esk27_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((l1_conlat_1 esk11_0 -> False) -> False)
  -> ((l1_conlat_1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
