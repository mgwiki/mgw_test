(** $I sig/MizarPreamble.mgs **)

Theorem t89_transgeo:
 forall esk26_4:set -> set -> set -> set -> set,
 forall k7_relset_1:set -> set -> set -> set -> set,
 forall k2_aff_1:set -> set -> set -> set,
 forall v1_partfun1:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall esk15_1:set -> set,
 forall k1_xboole_0:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk22_0:set,
 forall esk19_0:set,
 forall esk12_2:set -> set -> set,
 forall esk18_1:set -> set,
 forall esk9_1:set -> set,
 forall esk17_0:set,
 forall esk14_0:set,
 forall esk8_0:set,
 forall esk7_0:set,
 forall esk10_0:set,
 forall esk23_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall esk13_2:set -> set -> set,
 forall esk24_0:set,
 forall esk1_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall v3_funct_1:set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk16_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk21_1:set -> set,
 forall v2_struct_0:set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk20_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall v2_funct_1:set -> prop,
 forall v2_funct_2:set -> set -> prop,
 forall k7_relat_1:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall esk25_3:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk5_4:set -> set -> set -> set -> set,
 forall k1_aff_1:set -> set -> set -> set,
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall l1_analoaf:set -> prop,
 forall v8_transgeo:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall v3_funct_2:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall v1_funct_1:set -> prop,
 forall v1_diraf:set -> prop,
 forall v7_struct_0:set -> prop,
     (forall X5 X4 X3 X2 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v8_transgeo X2 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> r1_aff_1 X1 (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 X3) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 X4) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 X5) -> False)
  -> (forall X5 X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X5 X2) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X5 X3) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X5 X4) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X5 -> v8_transgeo X5 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> v1_funct_2 X5 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X5 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X3 X4 X2 X1, (X4 = (k1_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> r2_hidden (esk5_4 X1 X2 X3 X4) X4 -> r1_aff_1 X1 X2 X3 (esk5_4 X1 X2 X3 X4) -> False)
  -> (forall X2 X4 X3 X1, ((k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (esk26_4 X1 X3 X2 X4)) = X3 -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> r2_hidden X3 (k7_relset_1 (u1_struct_0 X1) (u1_struct_0 X1) X2 X4) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk26_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X3 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> r2_hidden X2 (k7_relset_1 (u1_struct_0 X1) (u1_struct_0 X1) X3 X4) -> False)
  -> (forall X3 X4 X2 X1, (v7_struct_0 X1 -> False) -> (r2_hidden (esk26_4 X1 X2 X3 X4) X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X3 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> v1_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X3 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> r2_hidden X2 (k7_relset_1 (u1_struct_0 X1) (u1_struct_0 X1) X3 X4) -> False)
  -> (forall X5 X3 X4 X1 X2, (v7_struct_0 X2 -> False) -> (r2_hidden X5 (k7_relset_1 (u1_struct_0 X2) (u1_struct_0 X2) X4 X3) -> False) -> (k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X2) X4 X1) = X5 -> v1_diraf X2 -> l1_analoaf X2 -> v1_funct_1 X4 -> r2_hidden X1 X3 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> v1_funct_2 X4 (u1_struct_0 X2) (u1_struct_0 X2) -> v3_funct_2 X4 (u1_struct_0 X2) (u1_struct_0 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X2))) -> False)
  -> (forall X3 X2 X4 X1, (X4 = (k1_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden (esk5_4 X1 X2 X3 X4) X4 -> False) -> (r1_aff_1 X1 X2 X3 (esk5_4 X1 X2 X3 X4) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X4 X1, (X4 = (k1_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk5_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, ((k3_funct_2 X1 X1 X2 (esk25_3 X1 X3 X2)) = X3 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X3 X1 -> v1_funct_2 X2 X1 X1 -> v3_funct_2 X2 X1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X5 X4 X3 X2 X1, (v7_struct_0 X1 -> False) -> (r2_hidden X4 X5 -> False) -> X5 = (k1_aff_1 X1 X2 X3) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k7_relset_1 X2 X3 X1 X4) (k1_zfmisc_1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X5 X4 X2 X3, (v7_struct_0 X3 -> False) -> (r1_aff_1 X3 X4 X5 X1 -> False) -> X2 = (k1_aff_1 X3 X4 X5) -> v1_diraf X3 -> l1_analoaf X3 -> r2_hidden X1 X2 -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X3)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk25_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> m1_subset_1 X2 X1 -> v1_funct_2 X3 X1 X1 -> v3_funct_2 X3 X1 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X4 X1 X2 X3, ((k7_relset_1 X2 X3 X1 X4) = (k7_relat_1 X1 X4) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k1_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (k2_aff_1 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (v2_funct_2 X1 X2 -> False) -> v1_funct_1 X1 -> v3_funct_2 X1 X3 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v3_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v3_funct_2 X1 X2 X3 -> False) -> v1_funct_1 X1 -> v2_funct_1 X1 -> v2_funct_2 X1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, ((k1_aff_1 X1 X2 X3) = (k2_aff_1 X1 X2 X3) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, ((k2_aff_1 X1 X2 X3) = (k2_aff_1 X1 X3 X2) -> False) -> (v7_struct_0 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_2 X1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk6_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk20_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk20_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk16_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk15_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_aff_1 esk1_0 (k3_funct_2 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) esk4_0 esk2_0) (k3_funct_2 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) esk4_0 esk3_0)) = (k7_relset_1 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) esk4_0 (k2_aff_1 esk1_0 esk2_0 esk3_0)) -> False)
  -> (v3_funct_1 esk22_0 -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk12_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk11_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0))) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk11_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> (forall X1, (v3_funct_2 (esk18_1 X1) X1 X1 -> False) -> False)
  -> (forall X1, (v1_funct_2 (esk18_1 X1) X1 X1 -> False) -> False)
  -> ((v3_funct_2 esk4_0 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v1_funct_2 esk4_0 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk23_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk13_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk12_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk11_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk23_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk23_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v8_transgeo esk4_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk18_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk24_0 -> False) -> False)
  -> ((v2_funct_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk8_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk10_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((l1_analoaf esk7_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
