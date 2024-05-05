(** $I sig/MizarPreamble.mgs **)

Theorem t58_robbins1:
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall k1_binop_1:set -> set -> set -> set,
 forall l2_lattices:set -> prop,
 forall esk2_1:set -> set,
 forall esk4_1:set -> set,
 forall esk3_1:set -> set,
 forall v5_lattices:set -> prop,
 forall l1_robbins1:set -> prop,
 forall u1_robbins1:set -> set,
 forall v4_lattices:set -> prop,
 forall k5_robbins1:set -> set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk1_0:set,
 forall v5_relat_1:set -> set -> prop,
 forall k12_robbins1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall o_1_1_robbins1:set -> set,
 forall v1_finset_1:set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk19_1:set -> set,
 forall esk18_1:set -> set,
 forall v2_binop_1:set -> set -> prop,
 forall np__1:set,
 forall esk33_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall esk32_1:set -> set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v5_ordinal1:set -> prop,
 forall esk25_0:set,
 forall esk31_0:set,
 forall esk22_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall esk11_1:set -> set,
 forall esk7_0:set,
 forall esk21_0:set,
 forall esk28_0:set,
 forall esk8_0:set,
 forall esk16_0:set,
 forall esk10_0:set,
 forall esk13_0:set,
 forall esk14_0:set,
 forall esk9_0:set,
 forall v2_xxreal_0:set -> prop,
 forall esk26_1:set -> set,
 forall esk15_2:set -> set -> set,
 forall esk17_0:set,
 forall esk23_0:set,
 forall esk24_0:set,
 forall v7_ordinal1:set -> prop,
 forall esk30_1:set -> set,
 forall esk20_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall esk27_1:set -> set,
 forall k1_xboole_0:set,
 forall v3_ordinal1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v1_binop_1:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk29_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall v1_card_1:set -> prop,
 forall v13_struct_0:set -> set -> prop,
 forall v3_card_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk12_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall u2_lattices:set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k5_binop_1:set -> set -> set -> set -> set,
 forall v5_robbins1:set -> prop,
 forall esk5_1:set -> set,
 forall k1_lattices:set -> set -> set -> set,
 forall esk6_1:set -> set,
 forall k3_robbins1:set -> set -> set,
 forall l2_robbins1:set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X1, (v2_struct_0 X1 -> False) -> (v5_robbins1 X1 -> False) -> (k3_robbins1 X1 (k1_lattices X1 (k3_robbins1 X1 (k1_lattices X1 (esk5_1 X1) (esk6_1 X1))) (k3_robbins1 X1 (k1_lattices X1 (esk5_1 X1) (k3_robbins1 X1 (esk6_1 X1)))))) = (esk5_1 X1) -> l2_robbins1 X1 -> False)
  -> (forall X2 X3 X1, ((k3_robbins1 X1 (k1_lattices X1 (k3_robbins1 X1 (k1_lattices X1 X2 X3)) (k3_robbins1 X1 (k1_lattices X1 X2 (k3_robbins1 X1 X3))))) = X2 -> False) -> (v2_struct_0 X1 -> False) -> v5_robbins1 X1 -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X4 X3 X1, (m1_subset_1 (k5_binop_1 X2 X1 X3 X4) X2 -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X4 X3 X1, ((k5_binop_1 X2 X1 X3 X4) = (k1_binop_1 X1 X3 X4) -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (k1_lattices X1 (k1_lattices X1 (esk2_1 X1) (esk3_1 X1)) (esk4_1 X1)) = (k1_lattices X1 (esk2_1 X1) (k1_lattices X1 (esk3_1 X1) (esk4_1 X1))) -> l2_lattices X1 -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X4 X3 X2 X1, ((k1_lattices X1 (k1_lattices X1 X2 X3) X4) = (k1_lattices X1 X2 (k1_lattices X1 X3 X4)) -> False) -> (v2_struct_0 X1 -> False) -> v5_lattices X1 -> l2_lattices X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k5_binop_1 (u1_struct_0 X1) (u2_lattices X1) X2 X3) = (k1_lattices X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> l2_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) (u1_robbins1 X1) X2) = (k3_robbins1 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l1_robbins1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (m1_subset_1 (u2_lattices X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1))) -> False) -> l2_lattices X1 -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k5_robbins1 X1 X2 X3) (u1_struct_0 X1) -> False) -> v4_lattices X1 -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k1_lattices X1 X2 X3) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k5_robbins1 X1 X2 X3) = (k1_lattices X1 X2 X3) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k5_robbins1 X1 X2 X3) = (k5_robbins1 X1 X3 X2) -> False) -> (v2_struct_0 X1 -> False) -> v4_lattices X1 -> l2_robbins1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (k5_robbins1 esk1_0 X1 X2) = X2 -> m1_subset_1 X2 (u1_struct_0 esk1_0) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_lattices X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> v5_lattices X1 -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_2 (u2_lattices X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> v4_lattices X1 -> l2_lattices X1 -> False)
  -> (forall X1, (m1_subset_1 (u1_robbins1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False) -> l1_robbins1 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1, (v1_funct_2 (u2_lattices X1) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk12_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, ((k1_lattices X1 X2 X2) = (k12_robbins1 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l2_robbins1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k3_robbins1 X1 X2) (u1_struct_0 X1) -> False) -> l1_robbins1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k12_robbins1 X1 X2) (u1_struct_0 X1) -> False) -> l2_robbins1 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v1_funct_2 (u1_robbins1 X1) (u1_struct_0 X1) (u1_struct_0 X1) -> False) -> l1_robbins1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (o_1_1_robbins1 X1) (u1_struct_0 X1) -> False) -> v4_lattices X1 -> v5_lattices X1 -> v5_robbins1 X1 -> l2_robbins1 X1 -> False)
  -> (forall X1 X2, (v3_card_1 (u1_struct_0 X2) X1 -> False) -> l1_struct_0 X2 -> v1_card_1 X1 -> v13_struct_0 X2 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_finset_1 X1 -> False) -> v1_finset_1 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_finset_1 X1 -> False) -> v1_finset_1 (k2_zfmisc_1 X2 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_binop_1 (u2_lattices X1) (u1_struct_0 X1) -> False) -> v5_lattices X1 -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_binop_1 (u2_lattices X1) (u1_struct_0 X1) -> False) -> v4_lattices X1 -> l2_lattices X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_robbins1 X1 -> False) -> (m1_subset_1 (esk6_1 X1) (u1_struct_0 X1) -> False) -> l2_robbins1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_robbins1 X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> l2_robbins1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (m1_subset_1 (esk4_1 X1) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (m1_subset_1 (esk3_1 X1) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v5_lattices X1 -> False) -> (m1_subset_1 (esk2_1 X1) (u1_struct_0 X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k2_zfmisc_1 X2 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_lattices X1) -> False) -> v5_lattices X1 -> l2_lattices X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_funct_1 (u2_lattices X1) -> False) -> v4_lattices X1 -> l2_lattices X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk19_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk29_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 (esk20_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk32_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_card_1 (esk30_1 X1) X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, v1_xboole_0 X1 -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v3_card_1 X1 np__1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v3_card_1 X1 k1_xboole_0 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 X1 np__1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v3_card_1 (esk33_1 X1) np__1 -> False) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk18_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (esk27_1 X1) -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finset_1 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v3_card_1 X1 k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> v1_finset_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_funct_1 (esk32_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (u1_robbins1 X1) -> False) -> l1_robbins1 X1 -> False)
  -> (forall X1, (v1_funct_1 (u2_lattices X1) -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (v1_relat_1 (esk32_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (l1_struct_0 (esk20_1 X1) -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (l1_robbins1 X1 -> False) -> l2_robbins1 X1 -> False)
  -> (forall X1, (l2_lattices X1 -> False) -> l2_robbins1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_robbins1 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l2_lattices X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_finset_1 esk25_0 -> False)
  -> (v1_zfmisc_1 esk24_0 -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk15_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk15_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk15_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk15_2 X1 X2) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v5_ordinal1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk26_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((l1_robbins1 esk7_0 -> False) -> False)
  -> ((l2_lattices esk9_0 -> False) -> False)
  -> ((v1_finset_1 esk21_0 -> False) -> False)
  -> ((v7_ordinal1 esk31_0 -> False) -> False)
  -> ((v7_ordinal1 esk28_0 -> False) -> False)
  -> ((v2_ordinal1 esk22_0 -> False) -> False)
  -> ((v2_ordinal1 esk21_0 -> False) -> False)
  -> ((v1_ordinal1 esk22_0 -> False) -> False)
  -> ((v1_ordinal1 esk21_0 -> False) -> False)
  -> ((v3_ordinal1 esk22_0 -> False) -> False)
  -> ((v3_ordinal1 esk21_0 -> False) -> False)
  -> ((v3_ordinal1 esk14_0 -> False) -> False)
  -> ((v1_card_1 esk21_0 -> False) -> False)
  -> ((v1_card_1 esk13_0 -> False) -> False)
  -> ((l1_struct_0 esk8_0 -> False) -> False)
  -> ((v1_zfmisc_1 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l2_robbins1 esk10_0 -> False) -> False)
  -> ((l2_robbins1 esk1_0 -> False) -> False)
  -> ((v5_robbins1 esk1_0 -> False) -> False)
  -> ((v5_lattices esk1_0 -> False) -> False)
  -> ((v4_lattices esk1_0 -> False) -> False)
  -> False.
Admitted.
