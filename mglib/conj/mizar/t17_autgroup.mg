(** $I sig/MizarPreamble.mgs **)

Theorem t17_autgroup:
 forall v2_struct_0:set -> prop,
 forall k4_autgroup:set -> set,
 forall v15_algstr_0:set -> prop,
 forall v3_group_1:set -> prop,
 forall k9_funct_2:set -> set -> set,
 forall m2_funct_2:set -> set -> set -> set -> prop,
 forall m1_funct_2:set -> set -> set -> prop,
 forall l3_algstr_0:set -> prop,
 forall v2_group_1:set -> prop,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall u1_struct_0:set -> set,
 forall esk8_4:set -> set -> set -> set -> set,
 forall k2_group_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk7_3:set -> set -> set -> set,
 forall k5_binop_1:set -> set -> set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k1_binop_1:set -> set -> set -> set,
 forall esk5_1:set -> set,
 forall esk6_1:set -> set,
 forall esk4_1:set -> set,
 forall k6_algstr_0:set -> set -> set -> set,
 forall esk16_3:set -> set -> set -> set,
 forall u2_algstr_0:set -> set,
 forall k1_xboole_0:set,
 forall v1_relat_1:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall k1_tarski:set -> set,
 forall k2_tarski:set -> set -> set,
 forall v1_group_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v4_funct_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk24_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk23_1:set -> set,
 forall v1_setwiseo:set -> set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall esk31_0:set,
 forall esk20_0:set,
 forall esk21_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk30_2:set -> set -> set,
 forall esk17_0:set,
 forall esk22_0:set,
 forall esk13_0:set,
 forall esk12_0:set,
 forall esk25_0:set,
 forall esk15_1:set -> set,
 forall esk18_2:set -> set -> set,
 forall esk19_0:set,
 forall esk27_0:set,
 forall esk26_0:set,
 forall esk29_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall v2_binop_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk28_1:set -> set,
 forall v1_finseqop:set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall k1_funct_2:set -> set -> set,
 forall k2_group_1:set -> set -> set,
 forall g3_algstr_0:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk9_2:set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall k3_relat_1:set -> set -> set,
 forall k1_partfun1:set -> set -> set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
     (forall X5 X3 X4 X1 X2 X6, (m1_subset_1 (k1_partfun1 X1 X2 X3 X4 X5 X6) (k1_zfmisc_1 (k2_zfmisc_1 X1 X4)) -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X5 X3 X4 X1 X2 X6, (v1_funct_1 (k1_partfun1 X1 X2 X3 X4 X5 X6) -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X5 X6 X2 X3 X4, ((k1_partfun1 X2 X3 X5 X6 X1 X4) = (k3_relat_1 X1 X4) -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X5 X6)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X2 X3 -> False) -> X3 = (k4_autgroup X1) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (esk8_4 X1 X3 X2 X4)) = (k2_group_3 X1 (esk8_4 X1 X3 X2 X4) X4) -> v15_algstr_0 X1 -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) -> m2_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) (k9_funct_2 (u1_struct_0 X1) (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X3 X2 -> False) -> (m1_subset_1 (esk8_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> X2 = (k4_autgroup X1) -> v15_algstr_0 X1 -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m2_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) (k9_funct_2 (u1_struct_0 X1) (u1_struct_0 X1)) -> False)
  -> (forall X4 X1 X3 X2, ((k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X2) X3 X1) = (k2_group_3 X2 X1 (esk7_3 X2 X4 X3)) -> False) -> (v2_struct_0 X2 -> False) -> X4 = (k4_autgroup X2) -> v15_algstr_0 X2 -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> r2_hidden X3 X4 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_funct_2 X4 (u1_struct_0 X2) (u1_struct_0 X2) -> m2_funct_2 X3 (u1_struct_0 X2) (u1_struct_0 X2) (k9_funct_2 (u1_struct_0 X2) (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, (X2 = (k4_autgroup X1) -> False) -> (v2_struct_0 X1 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) (esk9_2 X1 X2) (esk10_3 X1 X2 X3)) = (k2_group_3 X1 (esk10_3 X1 X2 X3) X3) -> v15_algstr_0 X1 -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> r2_hidden (esk9_2 X1 X2) X2 -> m1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X4 X3 X1, (m1_subset_1 (k5_binop_1 X2 X1 X3 X4) X2 -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> X2 = (k4_autgroup X1) -> v15_algstr_0 X1 -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> r2_hidden X3 X2 -> m1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m2_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) (k9_funct_2 (u1_struct_0 X1) (u1_struct_0 X1)) -> False)
  -> (forall X2 X4 X3 X1, ((k5_binop_1 X2 X1 X3 X4) = (k1_binop_1 X1 X3 X4) -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1, (v3_group_1 X1 -> False) -> (k6_algstr_0 X1 (k6_algstr_0 X1 (esk4_1 X1) (esk5_1 X1)) (esk6_1 X1)) = (k6_algstr_0 X1 (esk4_1 X1) (k6_algstr_0 X1 (esk5_1 X1) (esk6_1 X1))) -> l3_algstr_0 X1 -> False)
  -> (forall X1 X3 X2, (X3 = (k4_autgroup X2) -> False) -> ((k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X2) (esk9_2 X2 X3) X1) = (k2_group_3 X2 X1 (esk11_2 X2 X3)) -> False) -> (v2_struct_0 X2 -> False) -> (r2_hidden (esk9_2 X2 X3) X3 -> False) -> v15_algstr_0 X2 -> v2_group_1 X2 -> v3_group_1 X2 -> l3_algstr_0 X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_funct_2 X3 (u1_struct_0 X2) (u1_struct_0 X2) -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_2 X1 X2 X3 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X4 X3 X1 X2 X5, (v1_xboole_0 X5 -> False) -> (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X5 X4 -> v1_funct_2 X1 X3 X5 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X5 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X4 X3 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X4 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X2 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 X1 X4 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 X1 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X2 X1, (X2 = (k4_autgroup X1) -> False) -> (v2_struct_0 X1 -> False) -> (m2_funct_2 (esk9_2 X1 X2) (u1_struct_0 X1) (u1_struct_0 X1) (k9_funct_2 (u1_struct_0 X1) (u1_struct_0 X1)) -> False) -> v15_algstr_0 X1 -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g3_algstr_0 X1 X3) = (g3_algstr_0 X2 X4) -> v1_funct_1 X3 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g3_algstr_0 X3 X1) = (g3_algstr_0 X4 X2) -> v1_funct_1 X1 -> v1_funct_2 X1 (k2_zfmisc_1 X3 X3) X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X3) X3)) -> False)
  -> (forall X1 X2 X4 X5 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X5 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m2_funct_2 (esk16_3 X3 X1 X2) X3 X1 X2 -> False) -> m1_funct_2 X2 X3 X1 -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X2, (l3_algstr_0 (g3_algstr_0 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X1 X2, (v15_algstr_0 (g3_algstr_0 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X2 X3 X4 X1, ((k6_algstr_0 X1 (k6_algstr_0 X1 X2 X3) X4) = (k6_algstr_0 X1 X2 (k6_algstr_0 X1 X3 X4)) -> False) -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k5_binop_1 (u1_struct_0 X1) (u2_algstr_0 X1) X2 X3) = (k6_algstr_0 X1 X2 X3) -> False) -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (X2 = (k4_autgroup X1) -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk10_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v15_algstr_0 X1 -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> r2_hidden (esk9_2 X1 X2) X2 -> m1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3 X4, (v1_xboole_0 X4 -> False) -> (m2_funct_2 X1 X3 X4 X2 -> False) -> m1_subset_1 X1 X2 -> m1_funct_2 X2 X3 X4 -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 (k6_algstr_0 X1 (k2_group_1 X1 X3) X2) X3) = (k2_group_3 X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X5 X4 X2 X3, (X3 = k1_xboole_0 -> False) -> ((k1_funct_1 (k3_relat_1 X1 X4) X5) = (k1_funct_1 X4 (k1_funct_1 X1 X5)) -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X4 -> r2_hidden X5 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, ((k6_algstr_0 X1 (k2_group_1 X1 X3) (k2_group_1 X1 X2)) = (k2_group_1 X1 (k6_algstr_0 X1 X2 X3)) -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (m1_subset_1 (u2_algstr_0 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1))) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X2 X1, (r2_hidden X1 (k1_funct_2 X2 X2) -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (X2 = (k4_autgroup X1) -> False) -> (v2_struct_0 X1 -> False) -> (r2_hidden (esk9_2 X1 X2) X2 -> False) -> (m1_subset_1 (esk11_2 X1 X2) (u1_struct_0 X1) -> False) -> v15_algstr_0 X1 -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k2_group_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k6_algstr_0 X1 X2 X3) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> v1_group_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1, (v1_funct_2 (u2_algstr_0 X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_funct_2 (k4_autgroup X1) (u1_struct_0 X1) (u1_struct_0 X1) -> False) -> v15_algstr_0 X1 -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k2_group_1 X1 X2) (u1_struct_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k2_group_1 X1 (k2_group_1 X1 X2)) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, v1_xboole_0 X1 -> m1_funct_2 X1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v4_funct_1 X1 -> False) -> m1_funct_2 X1 X2 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_funct_2 (k9_funct_2 X2 X1) X2 X1 -> False) -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v2_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_finseqop (u2_algstr_0 X1) (u1_struct_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k1_funct_2 X2 X1) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_setwiseo (u2_algstr_0 X1) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> v1_group_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_binop_1 (u2_algstr_0 X1) (u1_struct_0 X1) -> False) -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_xboole_0 (k1_funct_2 X1 X2) -> False) -> v1_xboole_0 X2 -> False)
  -> (forall X1, ((g3_algstr_0 (u1_struct_0 X1) (u2_algstr_0 X1)) = X1 -> False) -> v15_algstr_0 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v3_group_1 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v3_group_1 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v3_group_1 X1 -> False) -> (m1_subset_1 (esk4_1 X1) (u1_struct_0 X1) -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_algstr_0 X1) -> False) -> v2_group_1 X1 -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, ((k9_funct_2 X2 X1) = (k1_funct_2 X2 X1) -> False) -> (v1_xboole_0 X1 -> False) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_algstr_0 X1) -> False) -> l3_algstr_0 X1 -> v1_group_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_algstr_0 X1) -> False) -> v3_group_1 X1 -> l3_algstr_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk24_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk28_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk23_1 X1) -> False) -> l1_struct_0 X1 -> False)
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
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l3_algstr_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (m2_funct_2 (k1_partfun1 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) esk3_0 esk2_0) (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) (k4_autgroup esk1_0) -> False)
  -> (forall X1, v1_xboole_0 (k1_funct_2 X1 X1) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v3_funct_1 esk29_0 -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk26_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk27_0 -> False)
  -> (v2_struct_0 esk20_0 -> False)
  -> (v2_struct_0 esk19_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> ((m2_funct_2 esk3_0 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) (k4_autgroup esk1_0) -> False) -> False)
  -> ((m2_funct_2 esk2_0 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) (k4_autgroup esk1_0) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk21_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk18_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_funct_2 (esk14_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk18_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk30_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk21_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk18_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk30_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk18_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_funct_1 (k1_funct_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk30_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk30_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk18_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v4_funct_1 esk31_0 -> False) -> False)
  -> ((v8_struct_0 esk27_0 -> False) -> False)
  -> ((v2_funct_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_group_1 esk27_0 -> False) -> False)
  -> ((v1_group_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 esk22_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v7_struct_0 esk20_0 -> False) -> False)
  -> ((l1_struct_0 esk12_0 -> False) -> False)
  -> ((l3_algstr_0 esk27_0 -> False) -> False)
  -> ((l3_algstr_0 esk20_0 -> False) -> False)
  -> ((l3_algstr_0 esk19_0 -> False) -> False)
  -> ((l3_algstr_0 esk13_0 -> False) -> False)
  -> ((l3_algstr_0 esk1_0 -> False) -> False)
  -> ((v3_group_1 esk27_0 -> False) -> False)
  -> ((v3_group_1 esk20_0 -> False) -> False)
  -> ((v3_group_1 esk19_0 -> False) -> False)
  -> ((v3_group_1 esk1_0 -> False) -> False)
  -> ((v2_group_1 esk27_0 -> False) -> False)
  -> ((v2_group_1 esk20_0 -> False) -> False)
  -> ((v2_group_1 esk19_0 -> False) -> False)
  -> ((v2_group_1 esk1_0 -> False) -> False)
  -> ((v15_algstr_0 esk27_0 -> False) -> False)
  -> ((v15_algstr_0 esk20_0 -> False) -> False)
  -> ((v15_algstr_0 esk19_0 -> False) -> False)
  -> ((v15_algstr_0 esk1_0 -> False) -> False)
  -> False.
Admitted.
