(** $I sig/MizarPreamble.mgs **)

Theorem t10_translac:
 forall v1_funct_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk32_2:set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall esk33_2:set -> set -> set,
 forall v3_funct_2:set -> set -> set -> prop,
 forall v6_transgeo:set -> set -> prop,
 forall v7_transgeo:set -> set -> prop,
 forall k1_transgeo:set -> set -> set -> set,
 forall r2_funct_2:set -> set -> set -> set -> prop,
 forall k6_partfun1:set -> set,
 forall esk29_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall o_1_0_translac:set -> set,
 forall esk13_1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v8_relat_2:set -> prop,
 forall v3_relat_2:set -> prop,
 forall esk25_0:set,
 forall esk23_0:set,
 forall esk11_0:set,
 forall esk9_2:set -> set -> set,
 forall esk17_1:set -> set,
 forall esk22_2:set -> set -> set,
 forall esk7_1:set -> set,
 forall v4_relat_2:set -> prop,
 forall esk20_0:set,
 forall esk15_0:set,
 forall esk12_0:set,
 forall esk6_0:set,
 forall esk5_0:set,
 forall esk8_0:set,
 forall esk18_0:set,
 forall esk28_1:set -> set,
 forall esk26_2:set -> set -> set,
 forall esk16_1:set -> set,
 forall esk10_2:set -> set -> set,
 forall esk19_0:set,
 forall esk27_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall v3_funct_1:set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk14_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk24_1:set -> set,
 forall v2_struct_0:set -> prop,
 forall v3_relat_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk21_2:set -> set -> set,
 forall v2_funct_1:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall v1_relat_2:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall k1_xboole_0:set,
 forall v2_funct_2:set -> set -> prop,
 forall v11_aff_2:set -> prop,
 forall esk34_3:set -> set -> set -> set,
 forall k3_relat_1:set -> set -> set,
 forall esk4_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk30_2:set -> set -> set,
 forall esk31_2:set -> set -> set,
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall v2_diraf:set -> prop,
 forall u1_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
 forall l1_analoaf:set -> prop,
 forall v1_diraf:set -> prop,
 forall v7_struct_0:set -> prop,
     (forall X5 X2 X3 X4 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X3 X2 X5 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X3 X5 X2 X4 -> r2_analoaf X1 X3 X2 X5 X4 -> False)
  -> (forall X2 X5 X4 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X4 X5 X2 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X4 X5 X2 X3 -> r2_analoaf X1 X4 X2 X5 X3 -> False)
  -> (forall X3 X4 X5 X2 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X5 X4 X3 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X5 X4 X3 X2 -> r2_analoaf X1 X5 X3 X4 X2 -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v7_transgeo X2 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v6_transgeo X2 X1 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> r2_analoaf X1 (esk32_2 X1 X2) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (esk32_2 X1 X2)) (esk33_2 X1 X2) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (esk33_2 X1 X2)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v6_transgeo X2 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> r2_analoaf X1 (esk30_2 X1 X2) (esk31_2 X1 X2) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (esk30_2 X1 X2)) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (esk31_2 X1 X2)) -> False)
  -> (forall X1 X3 X4 X2, (v7_struct_0 X2 -> False) -> (r2_analoaf X2 X3 (k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X2) X1 X3) X4 (k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X2) X1 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> v1_funct_1 X1 -> v7_transgeo X1 X2 -> v6_transgeo X1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> v1_funct_2 X1 (u1_struct_0 X2) (u1_struct_0 X2) -> v3_funct_2 X1 (u1_struct_0 X2) (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X2))) -> False)
  -> (forall X1 X4 X3 X2, (v7_struct_0 X2 -> False) -> (r2_analoaf X2 X3 X4 (k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X2) X1 X3) (k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X2) X1 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> v1_funct_1 X1 -> v6_transgeo X1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> v1_funct_2 X1 (u1_struct_0 X2) (u1_struct_0 X2) -> v3_funct_2 X1 (u1_struct_0 X2) (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X2))) -> False)
  -> (forall X4 X3 X2 X1, (v7_struct_0 X1 -> False) -> (r2_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) (k1_transgeo (u1_struct_0 X1) X4 X3) (k1_transgeo (u1_struct_0 X1) X3 X4) -> False) -> (r1_aff_1 X1 X2 (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X3 X2) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X4 X2) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v7_transgeo X4 X1 -> v7_transgeo X3 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> v1_funct_2 X4 (u1_struct_0 X1) (u1_struct_0 X1) -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X4 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X4 X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 X1 X2 X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 X1 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X4 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> r2_funct_2 X1 X1 (k1_transgeo X1 X2 X3) (k1_transgeo X1 X4 X3) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 X1 X3 X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 X1 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X4 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> r2_funct_2 X1 X1 (k1_transgeo X1 X2 X3) (k1_transgeo X1 X2 X4) -> False)
  -> (forall X1 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X4 X5 X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X6 -> r1_aff_1 X1 X2 X3 X5 -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (k6_partfun1 (u1_struct_0 X1)) -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 X3) = X3 -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v7_transgeo X2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v7_struct_0 X1 -> False) -> (v7_transgeo (k1_transgeo (u1_struct_0 X1) X3 X2) X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v7_transgeo X3 X1 -> v7_transgeo X2 X1 -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v7_transgeo X2 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v6_transgeo X2 X1 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> r2_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (k6_partfun1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 X1 (k1_transgeo X1 (k6_partfun1 X1) X2) (k1_transgeo X1 X2 (k6_partfun1 X1)) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 (k1_transgeo X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1, ((k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (esk4_2 X1 X2)) = (esk4_2 X1 X2) -> False) -> (v7_struct_0 X1 -> False) -> (v7_transgeo X2 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v6_transgeo X2 X1 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X3 X2 -> False)
  -> (forall X2 X1 X3, (v3_funct_2 (k1_transgeo X1 X2 X3) X1 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1 X3, (v1_funct_2 (k1_transgeo X1 X2 X3) X1 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1 X3, (v1_funct_1 (k1_transgeo X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X3 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X1 X3 X2, (v3_funct_2 (k3_relat_1 X1 X2) X3 X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X3 X3 -> v3_funct_2 X2 X3 X3 -> v3_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X3 X3 -> v3_funct_2 X2 X3 X3 -> v3_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, ((k1_transgeo X2 X1 X3) = (k3_relat_1 X1 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_funct_2 X3 X2 X2 -> v1_funct_2 X1 X2 X2 -> v3_funct_2 X3 X2 X2 -> v3_funct_2 X1 X2 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 (esk29_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X3 X3 -> v3_funct_2 X2 X3 X3 -> v3_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v7_transgeo X2 X1 -> False) -> (m1_subset_1 (esk33_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v6_transgeo X2 X1 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v7_transgeo X2 X1 -> False) -> (m1_subset_1 (esk32_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v6_transgeo X2 X1 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v7_transgeo X2 X1 -> False) -> (m1_subset_1 (esk4_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v6_transgeo X2 X1 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X4 X3 X1 X2 X5, (v1_xboole_0 X5 -> False) -> (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X5 X4 -> v1_funct_2 X1 X3 X5 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X5 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X4 X3 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v1_funct_2 (k3_relat_1 X1 X2) X3 X4 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X4 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X4 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v6_transgeo X2 X1 -> False) -> (m1_subset_1 (esk31_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v6_transgeo X2 X1 -> False) -> (m1_subset_1 (esk30_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X2 X3 X1, ((k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) (esk34_3 X1 X2 X3) X2) = X3 -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v11_aff_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2, (v7_struct_0 X2 -> False) -> (v6_transgeo X1 X2 -> False) -> v1_diraf X2 -> l1_analoaf X2 -> v1_funct_1 X1 -> v7_transgeo X1 X2 -> v1_funct_2 X1 (u1_struct_0 X2) (u1_struct_0 X2) -> v3_funct_2 X1 (u1_struct_0 X2) (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X2))) -> False)
  -> (forall X1 X2 X4 X5 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X5 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X5)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X3 -> v1_funct_2 X1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X4 X3)) -> False)
  -> (forall X3 X4 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v2_funct_2 (k3_relat_1 X1 X2) X3 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_2 X2 X3 -> v2_funct_2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v11_aff_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X5 X4 X2 X3, (X3 = k1_xboole_0 -> False) -> ((k1_funct_1 (k3_relat_1 X1 X4) X5) = (k1_funct_1 X4 (k1_funct_1 X1 X5)) -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_relat_1 X4 -> r2_hidden X5 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_funct_2 X2 X3 -> v2_funct_2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X3)) -> False)
  -> (forall X2 X1, (v3_funct_2 X1 X2 X2 -> False) -> v1_funct_1 X1 -> v1_relat_2 X1 -> v1_partfun1 X1 X2 -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (v3_funct_2 (esk34_3 X1 X2 X3) (u1_struct_0 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v11_aff_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (v1_funct_2 (esk34_3 X1 X2 X3) (u1_struct_0 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v11_aff_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v2_funct_2 X1 X2 -> False) -> v1_funct_1 X1 -> v3_funct_2 X1 X3 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (v7_transgeo (esk34_3 X1 X2 X3) X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v11_aff_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v3_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (v1_funct_1 (esk34_3 X1 X2 X3) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v11_aff_2 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v3_funct_2 X1 X2 X3 -> False) -> v1_funct_1 X1 -> v2_funct_1 X1 -> v2_funct_2 X1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2 X3, ((k3_relat_1 (k3_relat_1 X1 X2) X3) = (k3_relat_1 X1 (k3_relat_1 X2 X3)) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k3_relat_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1 X2, (v2_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v5_relat_1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk21_2 X1 X2) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (o_1_0_translac X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1 X2, (v2_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk21_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X1 -> v1_relat_1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k3_relat_1 X1 X2) -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk13_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk14_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v1_relat_1 X1 -> v3_relat_2 X1 -> v8_relat_2 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk13_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_funct_2 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) (k1_transgeo (u1_struct_0 esk1_0) esk3_0 esk2_0) (k1_transgeo (u1_struct_0 esk1_0) esk2_0 esk3_0) -> False)
  -> (v3_funct_1 esk25_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk10_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk9_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0))) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0))) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk9_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k6_partfun1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> (forall X1, (v3_funct_2 (esk16_1 X1) X1 X1 -> False) -> False)
  -> (forall X1, (v1_funct_2 (esk16_1 X1) X1 X1 -> False) -> False)
  -> ((v3_funct_2 esk3_0 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v3_funct_2 esk2_0 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v1_funct_2 esk3_0 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v1_funct_2 esk2_0 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk26_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk22_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk10_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk9_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk26_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk22_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk10_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk26_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk10_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk9_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk26_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk10_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk9_2 X1 X2) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_relat_1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk28_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk16_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (k6_partfun1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v7_transgeo esk3_0 esk1_0 -> False) -> False)
  -> ((v7_transgeo esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v4_relat_2 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_2 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_2 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v8_relat_2 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v8_relat_2 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v3_relat_2 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v3_relat_2 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v2_funct_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk16_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk28_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk16_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (k6_partfun1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (k6_partfun1 X1) -> False) -> False)
  -> ((v4_funct_1 esk27_0 -> False) -> False)
  -> ((v2_relat_1 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk20_0 -> False) -> False)
  -> ((v2_relat_1 esk18_0 -> False) -> False)
  -> ((v2_funct_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_relat_1 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 esk12_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk6_0 -> False) -> False)
  -> ((v11_aff_2 esk1_0 -> False) -> False)
  -> ((v1_funct_1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((v1_funct_1 esk8_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((l1_analoaf esk5_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v2_diraf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
