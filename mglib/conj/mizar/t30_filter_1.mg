(** $I sig/MizarPreamble.mgs **)

Theorem t30_filter_1:
 forall k5_binop_1:set -> set -> set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v4_funct_1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v3_relat_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk26_1:set -> set,
 forall esk15_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk22_1:set -> set,
 forall esk25_0:set,
 forall esk23_0:set,
 forall esk12_2:set -> set -> set,
 forall esk21_2:set -> set -> set,
 forall esk30_1:set -> set,
 forall esk17_0:set,
 forall esk10_0:set,
 forall o_0_0_xboole_0:set,
 forall esk16_0:set,
 forall esk19_0:set,
 forall esk9_1:set -> set,
 forall esk18_1:set -> set,
 forall esk27_2:set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk13_0:set,
 forall esk29_0:set,
 forall k1_xboole_0:set,
 forall o_1_0_filter_1:set -> set,
 forall v2_funct_1:set -> prop,
 forall esk24_1:set -> set,
 forall esk28_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk20_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall k2_tarski:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k3_funct_4:set -> set -> set,
 forall esk6_0:set,
 forall esk5_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall r1_lattice2:set -> set -> set -> prop,
 forall esk8_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall esk34_6:set -> set -> set -> set -> set -> set -> set,
 forall esk32_6:set -> set -> set -> set -> set -> set -> set,
 forall k1_domain_1:set -> set -> set -> set -> set,
 forall esk31_6:set -> set -> set -> set -> set -> set -> set,
 forall esk33_6:set -> set -> set -> set -> set -> set -> set,
 forall k1_binop_1:set -> set -> set -> set,
 forall k6_filter_1:set -> set -> set -> set -> set,
     (forall X1 X8 X7 X5 X4 X6 X3 X2, ((k1_binop_1 (k6_filter_1 X1 X2 X3 X4) X7 (k1_binop_1 (k6_filter_1 X1 X2 X5 X6) X7 X8)) = X7 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (k1_binop_1 (k6_filter_1 X1 X2 X3 X4) (k1_domain_1 X1 X2 (esk31_6 X1 X2 X3 X5 X4 X6) (esk33_6 X1 X2 X3 X5 X4 X6)) (k1_binop_1 (k6_filter_1 X1 X2 X5 X6) (k1_domain_1 X1 X2 (esk31_6 X1 X2 X3 X5 X4 X6) (esk33_6 X1 X2 X3 X5 X4 X6)) (k1_domain_1 X1 X2 (esk32_6 X1 X2 X3 X5 X4 X6) (esk34_6 X1 X2 X3 X5 X4 X6)))) = (k1_domain_1 X1 X2 (esk31_6 X1 X2 X3 X5 X4 X6) (esk33_6 X1 X2 X3 X5 X4 X6)) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X3 -> m1_subset_1 X8 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X7 (k2_zfmisc_1 X1 X2) -> v1_funct_2 X6 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X5 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X4 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X1 X8 X7 X3 X6 X5 X4 X2, ((k1_binop_1 (k6_filter_1 X1 X2 X3 X5) X7 (k1_binop_1 (k6_filter_1 X1 X2 X4 X6) X7 X8)) = X7 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk34_6 X1 X2 X3 X4 X5 X6) X2 -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X3 -> m1_subset_1 X8 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X7 (k2_zfmisc_1 X1 X2) -> v1_funct_2 X6 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X5 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X4 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X1 X8 X7 X3 X6 X5 X4 X2, ((k1_binop_1 (k6_filter_1 X1 X2 X3 X5) X7 (k1_binop_1 (k6_filter_1 X1 X2 X4 X6) X7 X8)) = X7 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk33_6 X1 X2 X3 X4 X5 X6) X2 -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X3 -> m1_subset_1 X8 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X7 (k2_zfmisc_1 X1 X2) -> v1_funct_2 X6 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X5 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X4 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X1 X8 X7 X3 X6 X5 X4 X2, ((k1_binop_1 (k6_filter_1 X1 X2 X3 X5) X7 (k1_binop_1 (k6_filter_1 X1 X2 X4 X6) X7 X8)) = X7 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_6 X1 X2 X3 X4 X5 X6) X1 -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X3 -> m1_subset_1 X8 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X7 (k2_zfmisc_1 X1 X2) -> v1_funct_2 X6 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X5 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X4 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X1 X8 X7 X3 X6 X5 X4 X2, ((k1_binop_1 (k6_filter_1 X1 X2 X3 X5) X7 (k1_binop_1 (k6_filter_1 X1 X2 X4 X6) X7 X8)) = X7 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_6 X1 X2 X3 X4 X5 X6) X1 -> False) -> v1_funct_1 X6 -> v1_funct_1 X5 -> v1_funct_1 X4 -> v1_funct_1 X3 -> m1_subset_1 X8 (k2_zfmisc_1 X1 X2) -> m1_subset_1 X7 (k2_zfmisc_1 X1 X2) -> v1_funct_2 X6 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X5 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X4 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X1 X7 X5 X3 X4 X6 X8 X2, ((k5_binop_1 (k2_zfmisc_1 X1 X2) (k6_filter_1 X1 X2 X7 X8) (k1_domain_1 X1 X2 X3 X5) (k1_domain_1 X1 X2 X4 X6)) = (k1_domain_1 X1 X2 (k5_binop_1 X1 X7 X3 X4) (k5_binop_1 X2 X8 X5 X6)) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X8 -> v1_funct_1 X7 -> m1_subset_1 X6 X2 -> m1_subset_1 X5 X2 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> v1_funct_2 X8 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X7 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X8 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_lattice2 X1 X2 X3 -> False) -> (k5_binop_1 X1 X2 (esk7_3 X1 X2 X3) (k5_binop_1 X1 X3 (esk7_3 X1 X2 X3) (esk8_3 X1 X2 X3))) = (esk7_3 X1 X2 X3) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X1 X2 X4, (m1_subset_1 (k6_filter_1 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) (k2_zfmisc_1 X1 X2)) (k2_zfmisc_1 X1 X2))) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (r1_lattice2 esk1_0 esk3_0 esk4_0 -> r1_lattice2 esk2_0 esk5_0 esk6_0 -> r1_lattice2 (k2_zfmisc_1 esk1_0 esk2_0) (k6_filter_1 esk1_0 esk2_0 esk3_0 esk5_0) (k6_filter_1 esk1_0 esk2_0 esk4_0 esk6_0) -> False)
  -> (forall X3 X5 X4 X2 X1, ((k5_binop_1 X1 X2 X4 (k5_binop_1 X1 X3 X4 X5)) = X4 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> r1_lattice2 X1 X2 X3 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X1 X2 X4, (v1_funct_2 (k6_filter_1 X1 X2 X3 X4) (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) (k2_zfmisc_1 X1 X2)) (k2_zfmisc_1 X1 X2) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X1 X2 X4, (v1_funct_1 (k6_filter_1 X1 X2 X3 X4) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 (k2_zfmisc_1 X2 X2) X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> ((r1_lattice2 esk2_0 esk5_0 esk6_0 -> False) -> (r1_lattice2 (k2_zfmisc_1 esk1_0 esk2_0) (k6_filter_1 esk1_0 esk2_0 esk3_0 esk5_0) (k6_filter_1 esk1_0 esk2_0 esk4_0 esk6_0) -> False) -> False)
  -> ((r1_lattice2 esk1_0 esk3_0 esk4_0 -> False) -> (r1_lattice2 (k2_zfmisc_1 esk1_0 esk2_0) (k6_filter_1 esk1_0 esk2_0 esk3_0 esk5_0) (k6_filter_1 esk1_0 esk2_0 esk4_0 esk6_0) -> False) -> False)
  -> (forall X1 X2 X4 X3, ((k6_filter_1 X2 X4 X1 X3) = (k3_funct_4 X1 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_funct_2 X3 (k2_zfmisc_1 X4 X4) X4 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X4 X4) X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_lattice2 X1 X2 X3 -> False) -> (m1_subset_1 (esk8_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_lattice2 X1 X2 X3 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X2 X4 X3 X1, (m1_subset_1 (k5_binop_1 X2 X1 X3 X4) X2 -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X4 X3 X1, ((k5_binop_1 X2 X1 X3 X4) = (k1_binop_1 X1 X3 X4) -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_domain_1 X1 X2 X3 X4) (k2_zfmisc_1 X1 X2) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X1 X4 X3 X2, ((k1_domain_1 X1 X2 X3 X4) = (k2_tarski (k2_tarski X3 X4) (k1_tarski X3)) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (k2_tarski (k2_tarski X1 X3) (k1_tarski X1)) = (k2_tarski (k2_tarski X2 X4) (k1_tarski X2)) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (k2_tarski (k2_tarski X3 X1) (k1_tarski X3)) = (k2_tarski (k2_tarski X4 X2) (k1_tarski X4)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_funct_4 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_funct_4 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk20_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk20_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk20_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (o_1_0_filter_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk28_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk22_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk25_0 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 esk2_0 esk2_0) esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 esk2_0 esk2_0) esk2_0)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0) esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0) esk1_0)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk14_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk12_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk11_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk11_2 X1 X2) X1 X2 -> False) -> False)
  -> ((v1_funct_2 esk6_0 (k2_zfmisc_1 esk2_0 esk2_0) esk2_0 -> False) -> False)
  -> ((v1_funct_2 esk5_0 (k2_zfmisc_1 esk2_0 esk2_0) esk2_0 -> False) -> False)
  -> ((v1_funct_2 esk4_0 (k2_zfmisc_1 esk1_0 esk1_0) esk1_0 -> False) -> False)
  -> ((v1_funct_2 esk3_0 (k2_zfmisc_1 esk1_0 esk1_0) esk1_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk27_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk21_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk14_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk12_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk11_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk27_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk21_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk30_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk30_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk18_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk29_0 -> False) -> False)
  -> ((v2_relat_1 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk19_0 -> False) -> False)
  -> ((v2_relat_1 esk17_0 -> False) -> False)
  -> ((v2_funct_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk25_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> ((v1_funct_1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk19_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk10_0 -> False) -> False)
  -> ((v1_funct_1 esk6_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
