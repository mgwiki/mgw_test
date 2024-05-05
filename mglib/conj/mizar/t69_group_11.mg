(** $I sig/MizarPreamble.mgs **)

Theorem t69_group_11:
 forall esk10_4:set -> set -> set -> set -> set,
 forall esk11_4:set -> set -> set -> set -> set,
 forall k6_algstr_0:set -> set -> set -> set,
 forall a_3_0_group_2:set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall g3_algstr_0:set -> set -> set,
 forall u2_algstr_0:set -> set,
 forall k4_group_2:set -> set -> set -> set,
 forall k6_domain_1:set -> set -> set,
 forall v1_group_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk24_2:set -> set -> set,
 forall v1_finseqop:set -> set -> prop,
 forall esk22_1:set -> set,
 forall esk15_1:set -> set,
 forall v1_setwiseo:set -> set -> prop,
 forall k1_tarski:set -> set,
 forall esk8_1:set -> set,
 forall v1_finset_1:set -> prop,
 forall esk20_0:set,
 forall esk21_0:set,
 forall esk16_0:set,
 forall esk7_0:set,
 forall esk6_0:set,
 forall o_0_0_xboole_0:set,
 forall esk9_1:set -> set,
 forall esk13_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall k1_xboole_0:set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall v2_binop_1:set -> set -> prop,
 forall esk14_1:set -> set,
 forall esk19_1:set -> set,
 forall esk17_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk5_2:set -> set -> set,
 forall esk23_2:set -> set -> set,
 forall esk25_3:set -> set -> set -> set,
 forall v15_algstr_0:set -> prop,
 forall v1_group_3:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k2_group_2:set -> set -> set -> set,
 forall k4_group_11:set -> set -> set -> set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall k7_group_4:set -> set -> set -> set,
 forall v2_group_1:set -> prop,
 forall l3_algstr_0:set -> prop,
 forall k8_group_2:set -> set -> set,
 forall k13_group_2:set -> set -> set -> set,
 forall esk12_4:set -> set -> set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall a_3_3_group_11:set -> set -> set -> set,
 forall m1_group_2:set -> set -> prop,
 forall v3_group_1:set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X4 X1 -> m1_group_2 X2 X1 -> r2_hidden X3 (a_3_3_group_11 X1 X4 X2) -> r1_xboole_0 (k13_group_2 X1 X2 (esk12_4 X3 X1 X4 X2)) (k8_group_2 X1 X4) -> False)
  -> (forall X3 X1 X4 X2, ((k6_algstr_0 X2 (esk10_4 X1 X2 X3 X4) (esk11_4 X1 X2 X3 X4)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l3_algstr_0 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_group_2 X2 X3 X4) -> False)
  -> (forall X1, (u1_struct_0 X1) = (k7_group_4 esk1_0 esk3_0 esk4_0) -> v15_algstr_0 X1 -> m1_group_2 X1 esk1_0 -> v1_group_3 X1 esk1_0 -> r1_tarski (k2_group_2 esk1_0 (k4_group_11 esk1_0 esk2_0 esk3_0) (k4_group_11 esk1_0 esk2_0 esk4_0)) (k4_group_11 esk1_0 esk2_0 X1) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk11_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> l3_algstr_0 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_group_2 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> l3_algstr_0 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_group_2 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk11_4 X1 X2 X3 X4) X4 -> False) -> l3_algstr_0 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_group_2 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X3 -> False) -> l3_algstr_0 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_group_2 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk12_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X4 X2 -> m1_group_2 X3 X2 -> r2_hidden X1 (a_3_3_group_11 X2 X3 X4) -> False)
  -> (forall X2 X3 X4 X5 X6 X1, ((k2_group_2 X1 (k13_group_2 X1 X3 X5) (k13_group_2 X1 X4 X6)) = (k13_group_2 X1 X2 (k6_algstr_0 X1 X5 X6)) -> False) -> (v2_struct_0 X1 -> False) -> (u1_struct_0 X2) = (k7_group_4 X1 X3 X4) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X4 X1 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> v1_group_3 X4 X1 -> v1_group_3 X3 X1 -> v1_group_3 X2 X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> False)
  -> (forall X2 X4 X3 X1, (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> r2_hidden X4 (k4_group_11 X1 X3 X2) -> r1_xboole_0 (k13_group_2 X1 X2 X4) (k8_group_2 X1 X3) -> False)
  -> (forall X3 X1 X4 X2, ((esk12_4 X1 X2 X3 X4) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X4 X2 -> m1_group_2 X3 X2 -> r2_hidden X1 (a_3_3_group_11 X2 X3 X4) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g3_algstr_0 X1 X3) = (g3_algstr_0 X2 X4) -> v1_funct_1 X3 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g3_algstr_0 X3 X1) = (g3_algstr_0 X4 X2) -> v1_funct_1 X1 -> v1_funct_2 X1 (k2_zfmisc_1 X3 X3) X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X3) X3)) -> False)
  -> (forall X1 X2, (v15_algstr_0 (g3_algstr_0 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X1 X2, (l3_algstr_0 (g3_algstr_0 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X4 X5 X6 X3 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X4 (a_3_0_group_2 X2 X5 X6) -> False) -> X4 = (k6_algstr_0 X2 X1 X3) -> l3_algstr_0 X2 -> r2_hidden X3 X6 -> r2_hidden X1 X5 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X5 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_3_3_group_11 X2 X5 X4) -> False) -> (r1_xboole_0 (k13_group_2 X2 X4 X1) (k8_group_2 X2 X5) -> False) -> X1 = X3 -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X5 X2 -> m1_group_2 X4 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X1, (m1_subset_1 (u2_algstr_0 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1))) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X2 X3 X1, ((u1_struct_0 (esk25_3 X1 X2 X3)) = (k7_group_4 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v15_algstr_0 X3 -> v15_algstr_0 X2 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> v1_group_3 X3 X1 -> v1_group_3 X2 X1 -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k2_group_2 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l3_algstr_0 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v1_group_3 (esk25_3 X1 X2 X3) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v15_algstr_0 X3 -> v15_algstr_0 X2 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> v1_group_3 X3 X1 -> v1_group_3 X2 X1 -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_group_2 (esk25_3 X1 X2 X3) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v15_algstr_0 X3 -> v15_algstr_0 X2 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> v1_group_3 X3 X1 -> v1_group_3 X2 X1 -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v15_algstr_0 (esk25_3 X1 X2 X3) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v15_algstr_0 X3 -> v15_algstr_0 X2 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> v1_group_3 X3 X1 -> v1_group_3 X2 X1 -> False)
  -> (forall X2 X3 X1, ((k2_group_2 X1 (k6_domain_1 (u1_struct_0 X1) X2) X3) = (k4_group_2 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> l3_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k4_group_2 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l3_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k2_group_2 X1 (k8_group_2 X1 X2) (k8_group_2 X1 X3)) = (k7_group_4 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X3 X2 X1, ((k2_group_2 X1 X2 X3) = (a_3_0_group_2 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> l3_algstr_0 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k13_group_2 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k4_group_2 X1 X3 (k8_group_2 X1 X2)) = (k13_group_2 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k4_group_11 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k7_group_4 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k6_algstr_0 X1 X2 X3) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k4_group_11 X1 X2 X3) = (a_3_3_group_11 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X2 X1, ((k2_group_2 X1 (k8_group_2 X1 X2) (k8_group_2 X1 X2)) = (k8_group_2 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> v1_group_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk23_2 X3 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k8_group_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk5_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k6_domain_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, r2_hidden X1 X3 -> r2_hidden X1 X2 -> r1_xboole_0 X2 X3 -> False)
  -> (forall X2 X1, ((k8_group_2 X1 X2) = (u1_struct_0 X2) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk23_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v8_struct_0 X2 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v8_struct_0 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk24_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X1 X2 -> False) -> (r2_hidden (esk24_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk5_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v3_group_1 X2 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_finseqop (u2_algstr_0 X1) (u1_struct_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> v2_struct_0 X1 -> v2_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_group_3 (esk15_1 X1) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_group_2 (esk19_1 X1) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_group_2 (esk15_1 X1) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_group_2 (esk14_1 X1) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (l3_algstr_0 X1 -> False) -> v2_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X1 X2 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_group_1 X1 -> False) -> v2_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_setwiseo (u2_algstr_0 X1) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> v1_group_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_binop_1 (u2_algstr_0 X1) (u1_struct_0 X1) -> False) -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X2 X1, ((k6_domain_1 X1 X2) = (k1_tarski X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v2_struct_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v2_struct_0 (esk15_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v2_struct_0 (esk14_1 X1) -> False)
  -> (forall X1, ((g3_algstr_0 (u1_struct_0 X1) (u2_algstr_0 X1)) = X1 -> False) -> l3_algstr_0 X1 -> v15_algstr_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_group_2 (esk8_1 X1) X1 -> False) -> v2_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_algstr_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v8_struct_0 (esk19_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_group_1 (esk19_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_group_1 (esk15_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_group_1 (esk14_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v15_algstr_0 (esk19_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v15_algstr_0 (esk15_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v15_algstr_0 (esk14_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_group_1 (esk19_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_group_1 (esk15_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_group_1 (esk14_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_group_1 (esk19_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_group_1 (esk15_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_group_1 (esk14_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_algstr_0 X1) -> False) -> l3_algstr_0 X1 -> v1_group_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_algstr_0 X1) -> False) -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk18_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk17_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_group_1 X1 -> False) -> v2_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_funct_1 (u2_algstr_0 X1) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk21_0 -> False)
  -> (v2_struct_0 esk13_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v1_group_3 esk4_0 esk1_0 -> False) -> False)
  -> ((v1_group_3 esk3_0 esk1_0 -> False) -> False)
  -> ((m1_group_2 esk4_0 esk1_0 -> False) -> False)
  -> ((m1_group_2 esk3_0 esk1_0 -> False) -> False)
  -> ((m1_group_2 esk2_0 esk1_0 -> False) -> False)
  -> ((v1_xboole_0 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v8_struct_0 esk21_0 -> False) -> False)
  -> ((v1_group_1 esk21_0 -> False) -> False)
  -> ((l1_struct_0 esk6_0 -> False) -> False)
  -> ((v15_algstr_0 esk21_0 -> False) -> False)
  -> ((v15_algstr_0 esk13_0 -> False) -> False)
  -> ((v15_algstr_0 esk4_0 -> False) -> False)
  -> ((v15_algstr_0 esk3_0 -> False) -> False)
  -> ((l3_algstr_0 esk21_0 -> False) -> False)
  -> ((l3_algstr_0 esk13_0 -> False) -> False)
  -> ((l3_algstr_0 esk7_0 -> False) -> False)
  -> ((l3_algstr_0 esk1_0 -> False) -> False)
  -> ((v3_group_1 esk21_0 -> False) -> False)
  -> ((v3_group_1 esk13_0 -> False) -> False)
  -> ((v3_group_1 esk1_0 -> False) -> False)
  -> ((v2_group_1 esk21_0 -> False) -> False)
  -> ((v2_group_1 esk13_0 -> False) -> False)
  -> ((v2_group_1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
