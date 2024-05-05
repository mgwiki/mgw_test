(** $I sig/MizarPreamble.mgs **)

Theorem t34_conlat_1:
 forall esk6_4:set -> set -> set -> set -> set,
 forall v5_conlat_1:set -> set -> prop,
 forall l2_conlat_1:set -> set -> prop,
 forall v7_conlat_1:set -> set -> prop,
 forall v4_conlat_1:set -> set -> prop,
 forall esk5_4:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_1_6_conlat_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk16_2:set -> set -> set,
 forall esk15_2:set -> set -> set,
 forall l5_struct_0:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall k1_tarski:set -> set,
 forall k2_tarski:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk33_2:set -> set -> set,
 forall esk31_1:set -> set,
 forall esk20_1:set -> set,
 forall esk23_1:set -> set,
 forall k7_conlat_1:set -> set,
 forall esk32_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall k1_xboole_0:set,
 forall esk21_2:set -> set -> set,
 forall esk14_1:set -> set,
 forall esk25_0:set,
 forall esk24_0:set,
 forall esk12_0:set,
 forall esk9_0:set,
 forall esk10_0:set,
 forall esk26_1:set -> set,
 forall v1_xtuple_0:set -> prop,
 forall esk22_2:set -> set -> set,
 forall esk27_0:set,
 forall esk28_1:set -> set,
 forall esk1_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk11_1:set -> set,
 forall esk29_1:set -> set,
 forall esk18_1:set -> set,
 forall esk13_1:set -> set,
 forall m1_conlat_1:set -> set -> prop,
 forall esk19_1:set -> set,
 forall esk17_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk30_1:set -> set,
 forall v6_conlat_1:set -> set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall k3_xboole_0:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall k2_xboole_0:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k10_xtuple_0:set -> set,
 forall k2_relset_1:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall v1_conlat_1:set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall u2_conlat_1:set -> set -> set,
 forall u1_struct_0:set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall k2_conlat_1:set -> set,
 forall k4_subset_1:set -> set -> set -> set,
 forall u3_conlat_1:set -> set -> set,
 forall k1_conlat_1:set -> set,
 forall v1_funct_1:set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k8_conlat_1:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall u4_struct_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall l1_conlat_1:set -> prop,
 forall k1_binop_1:set -> set -> set -> set,
 forall esk8_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall g2_conlat_1:set -> set -> set -> set,
 forall k9_conlat_1:set -> set,
     (forall X3 X1 X4 X2, (X4 = (k9_conlat_1 X2) -> False) -> (v1_conlat_1 X2 -> False) -> (k1_binop_1 X4 (esk7_2 X2 X4) (esk8_2 X2 X4)) = (g2_conlat_1 X2 X1 X3) -> X1 = (k9_subset_1 (u1_struct_0 X2) (u2_conlat_1 X2 (esk7_2 X2 X4)) (u2_conlat_1 X2 (esk8_2 X2 X4))) -> X3 = (k3_funct_2 (k1_zfmisc_1 (u1_struct_0 X2)) (k1_zfmisc_1 (u4_struct_0 X2)) (k1_conlat_1 X2) (k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X2)) (k1_zfmisc_1 (u1_struct_0 X2)) (k2_conlat_1 X2) (k4_subset_1 (u4_struct_0 X2) (u3_conlat_1 X2 (esk7_2 X2 X4)) (u3_conlat_1 X2 (esk8_2 X2 X4))))) -> l1_conlat_1 X2 -> v1_funct_1 X4 -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> v1_funct_2 X4 (k2_zfmisc_1 (k8_conlat_1 X2) (k8_conlat_1 X2)) (k8_conlat_1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X2) (k8_conlat_1 X2)) (k8_conlat_1 X2))) -> False)
  -> (forall X4 X2 X3 X1, ((esk6_4 X1 X2 X3 X4) = (k3_funct_2 (k1_zfmisc_1 (u1_struct_0 X1)) (k1_zfmisc_1 (u4_struct_0 X1)) (k1_conlat_1 X1) (k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) (k2_conlat_1 X1) (k4_subset_1 (u4_struct_0 X1) (u3_conlat_1 X1 X3) (u3_conlat_1 X1 X4)))) -> False) -> (v1_conlat_1 X1 -> False) -> (v5_conlat_1 X4 X1 -> False) -> (v5_conlat_1 X3 X1 -> False) -> X2 = (k9_conlat_1 X1) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v4_conlat_1 X4 X1 -> v4_conlat_1 X3 X1 -> v7_conlat_1 X4 X1 -> v7_conlat_1 X3 X1 -> l2_conlat_1 X4 X1 -> l2_conlat_1 X3 X1 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X2 X1, ((k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) (k2_conlat_1 X1) (k3_funct_2 (k1_zfmisc_1 (u1_struct_0 X1)) (k1_zfmisc_1 (u4_struct_0 X1)) (k1_conlat_1 X1) (k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) (k2_conlat_1 X1) X2))) = (k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) (k2_conlat_1 X1) X2) -> False) -> (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u4_struct_0 X1)) -> False)
  -> (forall X3 X1 X2 X4, ((g2_conlat_1 X4 (esk5_4 X4 X1 X2 X3) (esk6_4 X4 X1 X2 X3)) = (k1_binop_1 X1 X2 X3) -> False) -> (v1_conlat_1 X4 -> False) -> (v5_conlat_1 X3 X4 -> False) -> (v5_conlat_1 X2 X4 -> False) -> X1 = (k9_conlat_1 X4) -> l1_conlat_1 X4 -> v1_funct_1 X1 -> v4_conlat_1 X3 X4 -> v4_conlat_1 X2 X4 -> v7_conlat_1 X3 X4 -> v7_conlat_1 X2 X4 -> l2_conlat_1 X3 X4 -> l2_conlat_1 X2 X4 -> v1_funct_2 X1 (k2_zfmisc_1 (k8_conlat_1 X4) (k8_conlat_1 X4)) (k8_conlat_1 X4) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X4) (k8_conlat_1 X4)) (k8_conlat_1 X4))) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 (u1_struct_0 X1) (k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) (k2_conlat_1 X1) X2) (k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) (k2_conlat_1 X1) X3)) = (k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) (k2_conlat_1 X1) (k4_subset_1 (u4_struct_0 X1) X2 X3)) -> False) -> (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u4_struct_0 X1)) -> False)
  -> (forall X4 X2 X3 X1, (v1_conlat_1 X1 -> False) -> (v5_conlat_1 X4 X1 -> False) -> (v5_conlat_1 X3 X1 -> False) -> (m1_subset_1 (esk6_4 X1 X2 X3 X4) (k1_zfmisc_1 (u4_struct_0 X1)) -> False) -> X2 = (k9_conlat_1 X1) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v4_conlat_1 X4 X1 -> v4_conlat_1 X3 X1 -> v7_conlat_1 X4 X1 -> v7_conlat_1 X3 X1 -> l2_conlat_1 X4 X1 -> l2_conlat_1 X3 X1 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X4 X2 X3 X1, (v1_conlat_1 X1 -> False) -> (v5_conlat_1 X4 X1 -> False) -> (v5_conlat_1 X3 X1 -> False) -> (m1_subset_1 (esk5_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> X2 = (k9_conlat_1 X1) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v4_conlat_1 X4 X1 -> v4_conlat_1 X3 X1 -> v7_conlat_1 X4 X1 -> v7_conlat_1 X3 X1 -> l2_conlat_1 X4 X1 -> l2_conlat_1 X3 X1 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X4 X1 X3 X2, (v1_conlat_1 X2 -> False) -> (r2_hidden X4 (a_1_6_conlat_1 X2) -> False) -> (v5_conlat_1 (g2_conlat_1 X2 X1 X3) X2 -> False) -> X4 = (g2_conlat_1 X2 X1 X3) -> (k3_funct_2 (k1_zfmisc_1 (u1_struct_0 X2)) (k1_zfmisc_1 (u4_struct_0 X2)) (k1_conlat_1 X2) X1) = X3 -> (k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X2)) (k1_zfmisc_1 (u1_struct_0 X2)) (k2_conlat_1 X2) X3) = X1 -> l1_conlat_1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X4 X2 X3 X1, ((esk5_4 X1 X2 X3 X4) = (k9_subset_1 (u1_struct_0 X1) (u2_conlat_1 X1 X3) (u2_conlat_1 X1 X4)) -> False) -> (v1_conlat_1 X1 -> False) -> (v5_conlat_1 X4 X1 -> False) -> (v5_conlat_1 X3 X1 -> False) -> X2 = (k9_conlat_1 X1) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v4_conlat_1 X4 X1 -> v4_conlat_1 X3 X1 -> v7_conlat_1 X4 X1 -> v7_conlat_1 X3 X1 -> l2_conlat_1 X4 X1 -> l2_conlat_1 X3 X1 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1, (X2 = (k9_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v5_conlat_1 (esk8_2 X1 X2) X1 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X2 X1, (X2 = (k9_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v5_conlat_1 (esk7_2 X1 X2) X1 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X2 X1, (X2 = (k9_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> (l2_conlat_1 (esk8_2 X1 X2) X1 -> False) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X2 X1, (X2 = (k9_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> (l2_conlat_1 (esk7_2 X1 X2) X1 -> False) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X2 X1, (X2 = (k9_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> (v7_conlat_1 (esk8_2 X1 X2) X1 -> False) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X2 X1, (X2 = (k9_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> (v7_conlat_1 (esk7_2 X1 X2) X1 -> False) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X2 X1, (X2 = (k9_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> (v4_conlat_1 (esk8_2 X1 X2) X1 -> False) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X2 X1, (X2 = (k9_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> (v4_conlat_1 (esk7_2 X1 X2) X1 -> False) -> l1_conlat_1 X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1, (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> r2_hidden X2 (a_1_6_conlat_1 X1) -> v5_conlat_1 (g2_conlat_1 X1 (esk15_2 X2 X1) (esk16_2 X2 X1)) X1 -> False)
  -> (forall X2 X1, ((k3_funct_2 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) (k2_conlat_1 X1) (esk16_2 X2 X1)) = (esk15_2 X2 X1) -> False) -> (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> r2_hidden X2 (a_1_6_conlat_1 X1) -> False)
  -> (forall X2 X1, ((k3_funct_2 (k1_zfmisc_1 (u1_struct_0 X1)) (k1_zfmisc_1 (u4_struct_0 X1)) (k1_conlat_1 X1) (esk15_2 X2 X1)) = (esk16_2 X2 X1) -> False) -> (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> r2_hidden X2 (a_1_6_conlat_1 X1) -> False)
  -> (forall X3 X2 X1, (v1_conlat_1 X1 -> False) -> (v5_conlat_1 X3 X1 -> False) -> (v5_conlat_1 X2 X1 -> False) -> (r2_hidden (k1_binop_1 (k9_conlat_1 X1) X2 X3) (k2_relset_1 (k8_conlat_1 X1) (k9_conlat_1 X1)) -> False) -> l1_conlat_1 X1 -> v4_conlat_1 X3 X1 -> v4_conlat_1 X2 X1 -> v7_conlat_1 X3 X1 -> v7_conlat_1 X2 X1 -> l2_conlat_1 X3 X1 -> l2_conlat_1 X2 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (m1_subset_1 (k9_conlat_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1))) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X4 X3 X5 X6 X1 X2, (X1 = X2 -> False) -> (g2_conlat_1 X1 X3 X4) = (g2_conlat_1 X2 X5 X6) -> l5_struct_0 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (u4_struct_0 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X5 X6 X1 X2, (X1 = X2 -> False) -> (g2_conlat_1 X3 X1 X4) = (g2_conlat_1 X5 X2 X6) -> l5_struct_0 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u4_struct_0 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X3 X4 X5 X6 X1 X2, (X1 = X2 -> False) -> (g2_conlat_1 X3 X4 X1) = (g2_conlat_1 X5 X6 X2) -> l5_struct_0 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (u4_struct_0 X3)) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (m1_subset_1 (k2_conlat_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)))) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (m1_subset_1 (k1_conlat_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1)) (k1_zfmisc_1 (u4_struct_0 X1)))) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X2 X3 X1, (l2_conlat_1 (g2_conlat_1 X1 X2 X3) X1 -> False) -> l5_struct_0 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v4_conlat_1 (g2_conlat_1 X1 X2 X3) X1 -> False) -> l5_struct_0 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u4_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, ((g2_conlat_1 X1 (u2_conlat_1 X1 X2) (u3_conlat_1 X1 X2)) = X2 -> False) -> l5_struct_0 X1 -> v4_conlat_1 X2 X1 -> l2_conlat_1 X2 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, ((g2_conlat_1 X2 (esk15_2 X1 X2) (esk16_2 X1 X2)) = X1 -> False) -> (v1_conlat_1 X2 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_1_6_conlat_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v1_funct_2 (k9_conlat_1 X1) (k2_zfmisc_1 (k8_conlat_1 X1) (k8_conlat_1 X1)) (k8_conlat_1 X1) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (v1_conlat_1 X2 -> False) -> (v5_conlat_1 X1 X2 -> False) -> (r2_hidden X1 (k8_conlat_1 X2) -> False) -> l1_conlat_1 X2 -> v4_conlat_1 X1 X2 -> v7_conlat_1 X1 X2 -> l2_conlat_1 X1 X2 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v1_funct_2 (k2_conlat_1 X1) (k1_zfmisc_1 (u4_struct_0 X1)) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v1_funct_2 (k1_conlat_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) (k1_zfmisc_1 (u4_struct_0 X1)) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk33_2 X3 X2) -> False)
  -> (forall X1 X2, (v1_conlat_1 X2 -> False) -> (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (u4_struct_0 X2)) -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_1_6_conlat_1 X2) -> False)
  -> (forall X1 X2, (v1_conlat_1 X2 -> False) -> (m1_subset_1 (esk15_2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (a_1_6_conlat_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (u3_conlat_1 X1 X2) (k1_zfmisc_1 (u4_struct_0 X1)) -> False) -> l5_struct_0 X1 -> l2_conlat_1 X2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (u2_conlat_1 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l5_struct_0 X1 -> l2_conlat_1 X2 X1 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_conlat_1 X2 -> False) -> l1_conlat_1 X2 -> v5_conlat_1 X1 X2 -> r2_hidden X1 (k8_conlat_1 X2) -> False)
  -> (forall X2 X1, (r2_hidden (esk33_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_conlat_1 X2 -> False) -> (l2_conlat_1 X1 X2 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (k8_conlat_1 X2) -> False)
  -> (forall X1 X2, (v1_conlat_1 X2 -> False) -> (v7_conlat_1 X1 X2 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (k8_conlat_1 X2) -> False)
  -> (forall X1 X2, (v1_conlat_1 X2 -> False) -> (v4_conlat_1 X1 X2 -> False) -> l1_conlat_1 X2 -> r2_hidden X1 (k8_conlat_1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (v6_conlat_1 X2 X1 -> False) -> v1_conlat_1 X1 -> l5_struct_0 X1 -> l2_conlat_1 X2 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 (u4_struct_0 X1)) -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l5_struct_0 X1 -> False)
  -> (forall X2 X1, ((k2_relset_1 X2 X1) = (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l5_struct_0 X1 -> v5_conlat_1 (esk17_1 X1) X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> v5_conlat_1 (esk20_1 X1) X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> v5_conlat_1 (esk19_1 X1) X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> v1_xboole_0 X2 -> m1_conlat_1 X2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (m1_conlat_1 (esk13_1 X1) X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (m1_conlat_1 (k8_conlat_1 X1) X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v6_conlat_1 (esk18_1 X1) X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (l2_conlat_1 (esk20_1 X1) X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (l2_conlat_1 (esk19_1 X1) X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (l2_conlat_1 (esk18_1 X1) X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (l2_conlat_1 (esk17_1 X1) X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v7_conlat_1 (esk20_1 X1) X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v7_conlat_1 (esk19_1 X1) X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v4_conlat_1 (esk20_1 X1) X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v4_conlat_1 (esk18_1 X1) X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v4_conlat_1 (esk17_1 X1) X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (esk30_1 X1) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (u4_struct_0 X1) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l5_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> v1_xboole_0 (k7_conlat_1 X1) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> v1_xboole_0 (k7_conlat_1 X1) -> False)
  -> (forall X1, (l2_conlat_1 (esk32_1 X1) X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (l2_conlat_1 (esk11_1 X1) X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (v4_conlat_1 (esk32_1 X1) X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v1_funct_1 (k2_conlat_1 X1) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v1_funct_1 (k1_conlat_1 X1) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_conlat_1 X1 -> False) -> (v1_funct_1 (k9_conlat_1 X1) -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk23_1 X1) -> False)
  -> (forall X1, ((k8_conlat_1 X1) = (k7_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, ((k7_conlat_1 X1) = (a_1_6_conlat_1 X1) -> False) -> (v1_conlat_1 X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l5_struct_0 X1 -> False)
  -> (forall X1, (l5_struct_0 X1 -> False) -> l1_conlat_1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k1_binop_1 (k9_conlat_1 esk1_0) (k1_binop_1 (k9_conlat_1 esk1_0) esk2_0 esk3_0) esk4_0) = (k1_binop_1 (k9_conlat_1 esk1_0) esk2_0 (k1_binop_1 (k9_conlat_1 esk1_0) esk3_0 esk4_0)) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk28_1 X1) X1 -> False)
  -> (v5_conlat_1 esk4_0 esk1_0 -> False)
  -> (v5_conlat_1 esk3_0 esk1_0 -> False)
  -> (v5_conlat_1 esk2_0 esk1_0 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_conlat_1 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk22_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk21_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_xtuple_0 (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk21_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X2 X3 X1, ((k3_xboole_0 (k3_xboole_0 X1 X2) X3) = (k3_xboole_0 X1 (k3_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk22_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk21_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk22_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> ((l2_conlat_1 esk4_0 esk1_0 -> False) -> False)
  -> ((l2_conlat_1 esk3_0 esk1_0 -> False) -> False)
  -> ((l2_conlat_1 esk2_0 esk1_0 -> False) -> False)
  -> ((v7_conlat_1 esk4_0 esk1_0 -> False) -> False)
  -> ((v7_conlat_1 esk3_0 esk1_0 -> False) -> False)
  -> ((v7_conlat_1 esk2_0 esk1_0 -> False) -> False)
  -> ((v4_conlat_1 esk4_0 esk1_0 -> False) -> False)
  -> ((v4_conlat_1 esk3_0 esk1_0 -> False) -> False)
  -> ((v4_conlat_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk26_1 X1) -> False) -> False)
  -> ((v1_xtuple_0 esk25_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 esk24_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l5_struct_0 esk12_0 -> False) -> False)
  -> ((l1_conlat_1 esk9_0 -> False) -> False)
  -> ((l1_conlat_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
