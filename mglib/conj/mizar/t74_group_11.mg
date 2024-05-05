(** $I sig/MizarPreamble.mgs **)

Theorem t74_group_11:
 forall esk9_4:set -> set -> set -> set -> set,
 forall esk10_4:set -> set -> set -> set -> set,
 forall k6_algstr_0:set -> set -> set -> set,
 forall a_3_0_group_2:set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall esk22_4:set -> set -> set -> set -> set,
 forall esk24_2:set -> set -> set,
 forall v1_group_3:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall g3_algstr_0:set -> set -> set,
 forall k3_group_11:set -> set -> set -> set,
 forall esk26_3:set -> set -> set -> set,
 forall k4_group_2:set -> set -> set -> set,
 forall k6_domain_1:set -> set -> set,
 forall esk25_2:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall v8_struct_0:set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk17_1:set -> set,
 forall esk16_1:set -> set,
 forall esk18_1:set -> set,
 forall esk13_1:set -> set,
 forall v1_setwiseo:set -> set -> prop,
 forall k1_tarski:set -> set,
 forall esk7_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall k1_xboole_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall esk12_0:set,
 forall esk8_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk5_0:set,
 forall esk6_0:set,
 forall esk15_0:set,
 forall esk20_0:set,
 forall esk19_0:set,
 forall v1_finset_1:set -> prop,
 forall v2_binop_1:set -> set -> prop,
 forall esk14_1:set -> set,
 forall esk21_1:set -> set,
 forall v1_finseqop:set -> set -> prop,
 forall l1_struct_0:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v1_group_1:set -> prop,
 forall k5_group_2:set -> set -> set -> set,
 forall k2_group_2:set -> set -> set -> set,
 forall u2_algstr_0:set -> set,
 forall v15_algstr_0:set -> prop,
 forall k2_group_1:set -> set -> set,
 forall r1_struct_0:set -> set -> prop,
 forall k14_group_2:set -> set -> set -> set,
 forall esk23_4:set -> set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk11_4:set -> set -> set -> set -> set,
 forall k13_group_2:set -> set -> set -> set,
 forall k8_group_2:set -> set -> set,
 forall v3_group_1:set -> prop,
 forall m1_group_2:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall a_3_2_group_11:set -> set -> set -> set,
 forall l3_algstr_0:set -> prop,
 forall v2_group_1:set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (k13_group_2 X1 X2 (esk11_4 X3 X1 X4 X2)) (k8_group_2 X1 X4) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X4 X1 -> m1_group_2 X2 X1 -> r2_hidden X3 (a_3_2_group_11 X1 X4 X2) -> False)
  -> (forall X3 X1 X4 X2, ((k6_algstr_0 X2 (esk9_4 X1 X2 X3 X4) (esk10_4 X1 X2 X3 X4)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l3_algstr_0 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_group_2 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, ((k6_algstr_0 X2 (esk23_4 X1 X2 X3 X4) X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X4 X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (k14_group_2 X2 X4 X3) -> False)
  -> (forall X3 X1 X4 X2, ((k6_algstr_0 X2 X3 (esk22_4 X1 X2 X3 X4)) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X4 X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (k13_group_2 X2 X4 X3) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> l3_algstr_0 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_group_2 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk9_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> l3_algstr_0 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_group_2 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) X4 -> False) -> l3_algstr_0 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_group_2 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) X3 -> False) -> l3_algstr_0 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (a_3_0_group_2 X2 X3 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk23_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X4 X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (k14_group_2 X2 X4 X3) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk22_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X4 X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (k13_group_2 X2 X4 X3) -> False)
  -> (forall X4 X2 X1 X3, (v2_struct_0 X3 -> False) -> (r1_struct_0 X1 (esk23_4 X2 X3 X4 X1) -> False) -> v2_group_1 X3 -> v3_group_1 X3 -> l3_algstr_0 X3 -> m1_group_2 X1 X3 -> m1_subset_1 X4 (u1_struct_0 X3) -> r2_hidden X2 (k14_group_2 X3 X1 X4) -> False)
  -> (forall X4 X2 X1 X3, (v2_struct_0 X3 -> False) -> (r1_struct_0 X1 (esk22_4 X2 X3 X4 X1) -> False) -> v2_group_1 X3 -> v3_group_1 X3 -> l3_algstr_0 X3 -> m1_group_2 X1 X3 -> m1_subset_1 X4 (u1_struct_0 X3) -> r2_hidden X2 (k13_group_2 X3 X1 X4) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk11_4 X1 X2 X3 X4) (u1_struct_0 X2) -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X4 X2 -> m1_group_2 X3 X2 -> r2_hidden X1 (a_3_2_group_11 X2 X3 X4) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v1_group_3 X1 X2 -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X1 X2 -> r1_tarski (k13_group_2 X2 X1 (esk24_2 X2 X1)) (k14_group_2 X2 X1 (esk24_2 X2 X1)) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_struct_0 X4 (k6_algstr_0 X1 (k6_algstr_0 X1 X2 X3) (k2_group_1 X1 X2)) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v1_group_3 X4 X1 -> m1_group_2 X4 X1 -> r1_struct_0 X4 X3 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X4 X2, ((esk11_4 X1 X2 X3 X4) = X1 -> False) -> (v2_struct_0 X2 -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X4 X2 -> m1_group_2 X3 X2 -> r2_hidden X1 (a_3_2_group_11 X2 X3 X4) -> False)
  -> (forall X3 X5 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_3_2_group_11 X2 X5 X4) -> False) -> X1 = X3 -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X5 X2 -> m1_group_2 X4 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_tarski (k13_group_2 X2 X4 X1) (k8_group_2 X2 X5) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g3_algstr_0 X1 X3) = (g3_algstr_0 X2 X4) -> v1_funct_1 X3 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g3_algstr_0 X3 X1) = (g3_algstr_0 X4 X2) -> v1_funct_1 X1 -> v1_funct_2 X1 (k2_zfmisc_1 X3 X3) X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X3) X3)) -> False)
  -> (forall X2 X4 X3 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (k13_group_2 X1 X2 X4) (k8_group_2 X1 X3) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> r2_hidden X4 (k3_group_11 X1 X3 X2) -> False)
  -> (forall X1 X2, (v15_algstr_0 (g3_algstr_0 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X1 X2, (l3_algstr_0 (g3_algstr_0 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X4 X5 X6 X3 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X4 (a_3_0_group_2 X2 X5 X6) -> False) -> X4 = (k6_algstr_0 X2 X1 X3) -> l3_algstr_0 X2 -> r2_hidden X3 X6 -> r2_hidden X1 X5 -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (k14_group_2 X1 X2 X3) (k14_group_2 X1 X4 X3) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X4 X1 -> m1_group_2 X2 X4 -> m1_group_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (k13_group_2 X1 X2 X3) (k13_group_2 X1 X4 X3) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X4 X1 -> m1_group_2 X2 X4 -> m1_group_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X5 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (k14_group_2 X2 X5 X4) -> False) -> X3 = (k6_algstr_0 X2 X1 X4) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X5 X2 -> r1_struct_0 X5 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X5 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (k13_group_2 X2 X5 X4) -> False) -> X3 = (k6_algstr_0 X2 X4 X1) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X5 X2 -> r1_struct_0 X5 X1 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (r1_tarski (k13_group_2 X2 X1 X3) (k14_group_2 X2 X1 X3) -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> v1_group_3 X1 X2 -> m1_group_2 X1 X2 -> m1_subset_1 X3 (u1_struct_0 X2) -> False)
  -> (forall X1, (m1_subset_1 (u2_algstr_0 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1))) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 (k6_algstr_0 X1 (k2_group_1 X1 X2) X2) X3) = X3 -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 (k6_algstr_0 X1 X2 (k2_group_1 X1 X2)) X3) = X3 -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 (k6_algstr_0 X1 X2 (k2_group_1 X1 X3)) X3) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 X2 (k6_algstr_0 X1 (k2_group_1 X1 X2) X3)) = X3 -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 X2 (k6_algstr_0 X1 (k2_group_1 X1 X3) X3)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 X2 (k6_algstr_0 X1 X3 (k2_group_1 X1 X3))) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((u1_struct_0 (esk26_3 X1 X2 X3)) = (k3_group_11 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v1_group_3 X3 X1 -> m1_group_2 X3 X2 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 (k6_algstr_0 X1 X2 X3) (k2_group_1 X1 X3)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 (k2_group_1 X1 X2) (k6_algstr_0 X1 X2 X3)) = X3 -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k2_group_2 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l3_algstr_0 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, ((k2_group_2 X1 (k6_domain_1 (u1_struct_0 X1) X2) X3) = (k4_group_2 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> l3_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, ((k2_group_2 X1 X3 (k6_domain_1 (u1_struct_0 X1) X2)) = (k5_group_2 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> l3_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_group_2 (esk26_3 X1 X2 X3) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v1_group_3 X3 X1 -> m1_group_2 X3 X2 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k5_group_2 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l3_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k4_group_2 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l3_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (v15_algstr_0 (esk26_3 X1 X2 X3) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v1_group_3 X3 X1 -> m1_group_2 X3 X2 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X3 X2 X1, ((k2_group_2 X1 X2 X3) = (a_3_0_group_2 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> l3_algstr_0 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k14_group_2 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k13_group_2 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k5_group_2 X1 X3 (k8_group_2 X1 X2)) = (k14_group_2 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k4_group_2 X1 X3 (k8_group_2 X1 X2)) = (k13_group_2 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k3_group_11 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_struct_0 X2 X3 -> False) -> (k13_group_2 X1 X2 X3) = (k8_group_2 X1 X2) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X1 (k14_group_2 X2 X3 X1) -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X3 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X1 (k13_group_2 X2 X3 X1) -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X3 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k6_algstr_0 X1 X2 X3) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k3_group_11 X1 X2 X3) = (a_3_2_group_11 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X3 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X2 X1 X3, ((k13_group_2 X3 X1 X2) = (k8_group_2 X3 X1) -> False) -> (v2_struct_0 X3 -> False) -> v2_group_1 X3 -> v3_group_1 X3 -> l3_algstr_0 X3 -> m1_group_2 X1 X3 -> r1_struct_0 X1 X2 -> m1_subset_1 X2 (u1_struct_0 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> v1_group_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (u1_struct_0 X1) = (k3_group_11 esk1_0 esk2_0 esk3_0) -> v15_algstr_0 X1 -> v1_group_3 X1 esk1_0 -> m1_group_2 X1 esk1_0 -> False)
  -> (forall X1, (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v1_group_3 X1 X2 -> False) -> (m1_subset_1 (esk24_2 X2 X1) (u1_struct_0 X2) -> False) -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X1 X2 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk25_2 X3 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k8_group_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k2_group_1 X1 X2) (u1_struct_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k2_group_1 X1 (k2_group_1 X1 X2)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k6_domain_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k8_group_2 X1 X2) = (u1_struct_0 X2) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X2 X1, (r2_hidden (esk25_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v8_struct_0 X2 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v8_struct_0 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk4_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_struct_0 X2 X1 -> False) -> l1_struct_0 X2 -> r2_hidden X1 (u1_struct_0 X2) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (v3_group_1 X2 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_group_2 X2 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_finseqop (u2_algstr_0 X1) (u1_struct_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r2_hidden X2 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> r1_struct_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> v2_struct_0 X1 -> v2_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_group_2 (esk18_1 X1) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_group_2 (esk14_1 X1) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_group_2 (esk13_1 X1) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_group_3 (esk14_1 X1) X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (l3_algstr_0 X1 -> False) -> v2_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X1 X2 -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v2_group_1 X1 -> False) -> v2_group_1 X2 -> l3_algstr_0 X2 -> m1_group_2 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_setwiseo (u2_algstr_0 X1) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> v1_group_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_binop_1 (u2_algstr_0 X1) (u1_struct_0 X1) -> False) -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X2 X1, ((k6_domain_1 X1 X2) = (k1_tarski X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v2_struct_0 (esk18_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v2_struct_0 (esk14_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> v2_struct_0 (esk13_1 X1) -> False)
  -> (forall X1, ((g3_algstr_0 (u1_struct_0 X1) (u2_algstr_0 X1)) = X1 -> False) -> l3_algstr_0 X1 -> v15_algstr_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_group_2 (esk7_1 X1) X1 -> False) -> v2_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_algstr_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v8_struct_0 (esk18_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_group_1 (esk18_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_group_1 (esk14_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_group_1 (esk13_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v15_algstr_0 (esk18_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v15_algstr_0 (esk14_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v15_algstr_0 (esk13_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_group_1 (esk18_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_group_1 (esk14_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_group_1 (esk13_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_group_1 (esk18_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_group_1 (esk14_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_group_1 (esk13_1 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_algstr_0 X1) -> False) -> l3_algstr_0 X1 -> v1_group_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_algstr_0 X1) -> False) -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk17_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk16_1 X1) -> False) -> l1_struct_0 X1 -> False)
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
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk20_0 -> False)
  -> (v2_struct_0 esk12_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_group_2 esk3_0 esk2_0 -> False) -> False)
  -> ((m1_group_2 esk3_0 esk1_0 -> False) -> False)
  -> ((m1_group_2 esk2_0 esk1_0 -> False) -> False)
  -> ((v1_group_3 esk3_0 esk1_0 -> False) -> False)
  -> ((v1_group_3 esk2_0 esk1_0 -> False) -> False)
  -> ((v1_xboole_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v8_struct_0 esk20_0 -> False) -> False)
  -> ((v1_group_1 esk20_0 -> False) -> False)
  -> ((l1_struct_0 esk5_0 -> False) -> False)
  -> ((v15_algstr_0 esk20_0 -> False) -> False)
  -> ((v15_algstr_0 esk12_0 -> False) -> False)
  -> ((l3_algstr_0 esk20_0 -> False) -> False)
  -> ((l3_algstr_0 esk12_0 -> False) -> False)
  -> ((l3_algstr_0 esk6_0 -> False) -> False)
  -> ((l3_algstr_0 esk1_0 -> False) -> False)
  -> ((v3_group_1 esk20_0 -> False) -> False)
  -> ((v3_group_1 esk12_0 -> False) -> False)
  -> ((v3_group_1 esk1_0 -> False) -> False)
  -> ((v2_group_1 esk20_0 -> False) -> False)
  -> ((v2_group_1 esk12_0 -> False) -> False)
  -> ((v2_group_1 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
