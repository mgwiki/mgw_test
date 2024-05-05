(** $I sig/MizarPreamble.mgs **)

Theorem t9_filter_1:
 forall esk5_3:set -> set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k3_binop_1:set -> set -> set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall r4_binop_1:set -> set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall k7_eqrel_1:set -> set -> set,
 forall m1_eqrel_1:set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall k1_tarski:set -> set,
 forall k2_tarski:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk24_2:set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v3_relat_1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk33_1:set -> set,
 forall esk29_1:set -> set,
 forall v3_funct_1:set -> prop,
 forall esk27_1:set -> set,
 forall v2_relat_1:set -> prop,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk34_0:set,
 forall esk15_0:set,
 forall esk14_2:set -> set -> set,
 forall esk32_2:set -> set -> set,
 forall esk22_1:set -> set,
 forall esk35_1:set -> set,
 forall esk8_1:set -> set,
 forall esk21_0:set,
 forall esk12_0:set,
 forall o_0_0_xboole_0:set,
 forall esk19_0:set,
 forall esk23_0:set,
 forall esk9_1:set -> set,
 forall esk25_2:set -> set -> set,
 forall esk20_1:set -> set,
 forall esk13_2:set -> set -> set,
 forall esk16_2:set -> set -> set,
 forall esk28_0:set,
 forall esk30_0:set,
 forall esk26_1:set -> set,
 forall k1_xboole_0:set,
 forall esk18_1:set -> set,
 forall esk17_1:set -> set,
 forall esk31_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk11_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v1_setfam_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall v2_funct_2:set -> set -> prop,
 forall v1_relat_2:set -> prop,
 forall v3_funct_2:set -> set -> set -> prop,
 forall k9_relat_1:set -> set -> set,
 forall k1_binop_1:set -> set -> set -> set,
 forall k6_eqrel_1:set -> set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v3_relat_2:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall m2_filter_1:set -> set -> set -> prop,
 forall v8_relat_2:set -> prop,
 forall esk38_4:set -> set -> set -> set -> set,
 forall esk37_4:set -> set -> set -> set -> set,
 forall k9_eqrel_1:set -> set -> set -> set,
 forall esk36_4:set -> set -> set -> set -> set,
 forall k5_binop_1:set -> set -> set -> set -> set,
 forall k3_filter_1:set -> set -> set -> set,
 forall k8_eqrel_1:set -> set -> set,
     (forall X3 X4 X2 X5 X6 X7 X1, ((k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X4) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 X6) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 X7)) = (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X4) X6 X7)) -> False) -> (v1_xboole_0 X1 -> False) -> (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X4) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) (k9_eqrel_1 X1 X2 (esk36_4 X1 X2 X3 X4)) (k9_eqrel_1 X1 X2 (esk37_4 X1 X2 X3 X4))) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) (k9_eqrel_1 X1 X2 (esk36_4 X1 X2 X3 X4)) (k9_eqrel_1 X1 X2 (esk38_4 X1 X2 X3 X4)))) = (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) (k9_eqrel_1 X1 X2 (esk36_4 X1 X2 X3 X4)) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X4) (k9_eqrel_1 X1 X2 (esk37_4 X1 X2 X3 X4)) (k9_eqrel_1 X1 X2 (esk38_4 X1 X2 X3 X4)))) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_partfun1 X2 X1 -> m2_filter_1 X4 X1 X2 -> m2_filter_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m2_subset_1 X7 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> m2_subset_1 X6 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> m2_subset_1 X5 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r4_binop_1 X1 X2 X3 -> False) -> (k3_binop_1 X1 X3 (k3_binop_1 X1 X2 (esk5_3 X1 X2 X3) (esk6_3 X1 X2 X3)) (k3_binop_1 X1 X2 (esk5_3 X1 X2 X3) (esk7_3 X1 X2 X3))) = (k3_binop_1 X1 X2 (esk5_3 X1 X2 X3) (k3_binop_1 X1 X3 (esk6_3 X1 X2 X3) (esk7_3 X1 X2 X3))) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X2 X3 X4 X5 X6 X7 X1, ((k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X4) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 X6) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 X7)) = (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X4) X6 X7)) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk38_4 X1 X2 X3 X4) X1 -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_partfun1 X2 X1 -> m2_filter_1 X4 X1 X2 -> m2_filter_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m2_subset_1 X7 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> m2_subset_1 X6 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> m2_subset_1 X5 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> False)
  -> (forall X2 X3 X4 X5 X6 X7 X1, ((k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X4) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 X6) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 X7)) = (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X4) X6 X7)) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk37_4 X1 X2 X3 X4) X1 -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_partfun1 X2 X1 -> m2_filter_1 X4 X1 X2 -> m2_filter_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m2_subset_1 X7 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> m2_subset_1 X6 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> m2_subset_1 X5 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> False)
  -> (forall X2 X3 X4 X5 X6 X7 X1, ((k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X4) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 X6) (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 X7)) = (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X3) X5 (k5_binop_1 (k8_eqrel_1 X1 X2) (k3_filter_1 X1 X2 X4) X6 X7)) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk36_4 X1 X2 X3 X4) X1 -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_partfun1 X2 X1 -> m2_filter_1 X4 X1 X2 -> m2_filter_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m2_subset_1 X7 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> m2_subset_1 X6 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> m2_subset_1 X5 (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> False)
  -> (forall X3 X6 X4 X5 X2 X1, ((k3_binop_1 X1 X3 (k3_binop_1 X1 X2 X4 X5) (k3_binop_1 X1 X2 X4 X6)) = (k3_binop_1 X1 X2 X4 (k3_binop_1 X1 X3 X5 X6)) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_subset_1 X6 X1 -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> r4_binop_1 X1 X2 X3 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X2 X3 X5 X4 X1, ((k1_binop_1 (k3_filter_1 X1 X2 X5) (k6_eqrel_1 X1 X1 X2 X3) (k6_eqrel_1 X1 X1 X2 X4)) = (k6_eqrel_1 X1 X1 X2 (k5_binop_1 X1 X5 X3 X4)) -> False) -> (v1_xboole_0 X1 -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_subset_1 X4 X1 -> m1_subset_1 X3 X1 -> m2_filter_1 X5 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_filter_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k8_eqrel_1 X1 X2) (k8_eqrel_1 X1 X2)) (k8_eqrel_1 X1 X2))) -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_funct_1 X3 -> v1_partfun1 X2 X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r4_binop_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r4_binop_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r4_binop_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk5_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X2 X4 X3 X1, (m1_subset_1 (k5_binop_1 X2 X1 X3 X4) X2 -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X4 X3 X1, (m1_subset_1 (k3_binop_1 X2 X1 X3 X4) X2 -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k3_filter_1 X1 X2 X3) (k2_zfmisc_1 (k8_eqrel_1 X1 X2) (k8_eqrel_1 X1 X2)) (k8_eqrel_1 X1 X2) -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_funct_1 X3 -> v1_partfun1 X2 X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X2 X4 X3 X1, ((k5_binop_1 X2 X1 X3 X4) = (k1_binop_1 X1 X3 X4) -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X4 X3 X1, ((k3_binop_1 X2 X1 X3 X4) = (k1_binop_1 X1 X3 X4) -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k3_filter_1 X1 X2 X3) -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_funct_1 X3 -> v1_partfun1 X2 X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X4 X1 X2 X3, (m1_subset_1 (k6_eqrel_1 X2 X3 X1 X4) (k1_zfmisc_1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X1 X2 X3, ((k6_eqrel_1 X2 X3 X1 X4) = (k9_relat_1 X1 X4) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m2_subset_1 (k9_eqrel_1 X1 X2 X3) (k1_zfmisc_1 X1) (k8_eqrel_1 X1 X2) -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1, (v3_funct_2 X1 X2 X2 -> False) -> v1_funct_1 X1 -> v1_relat_2 X1 -> v1_partfun1 X1 X2 -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False) -> v1_relat_1 X3 -> m2_filter_1 X1 X2 X3 -> False)
  -> (forall X2 X3 X1, ((k9_eqrel_1 X1 X2 X3) = (k9_relat_1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v2_funct_2 X1 X2 -> False) -> v1_funct_1 X1 -> v3_funct_2 X1 X3 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v3_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (m1_subset_1 (k7_eqrel_1 X2 X1) (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> v3_relat_2 X1 -> v8_relat_2 X1 -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X3 X1, (v3_funct_2 X1 X2 X3 -> False) -> v1_funct_1 X1 -> v2_funct_1 X1 -> v2_funct_2 X1 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_partfun1 X2 X1 -> v1_xboole_0 (k7_eqrel_1 X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (m1_eqrel_1 (k8_eqrel_1 X2 X1) X2 -> False) -> v3_relat_2 X1 -> v8_relat_2 X1 -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (k7_eqrel_1 X1 X2) -> False) -> v3_relat_2 X2 -> v8_relat_2 X2 -> v1_partfun1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False)
  -> (forall X2 X1, ((k8_eqrel_1 X2 X1) = (k7_eqrel_1 X2 X1) -> False) -> v3_relat_2 X1 -> v8_relat_2 X1 -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> False) -> v1_relat_1 X3 -> m2_filter_1 X1 X2 X3 -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_partfun1 X3 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk11_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 X1 -> False) -> v1_relat_1 X3 -> m2_filter_1 X1 X2 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m2_filter_1 (esk10_2 X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v4_funct_1 (k2_tarski X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk24_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk24_2 X1 X2) X1 -> False) -> False)
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
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk24_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk24_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk33_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk31_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_2 X1 -> False) -> v3_relat_2 X1 -> v8_relat_2 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk29_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk33_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk31_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk31_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk27_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r4_binop_1 (k8_eqrel_1 esk1_0 esk2_0) (k3_filter_1 esk1_0 esk2_0 esk3_0) (k3_filter_1 esk1_0 esk2_0 esk4_0) -> False)
  -> (forall X1, v1_subset_1 (esk26_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v3_funct_1 esk30_0 -> False)
  -> (v1_xboole_0 esk34_0 -> False)
  -> (v1_xboole_0 esk28_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk14_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk13_2 X1 X2) X1 X2 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 X1)) -> False) -> False)
  -> (forall X1, (v3_funct_2 (esk20_1 X1) X1 X1 -> False) -> False)
  -> (forall X1, (v1_funct_2 (esk20_1 X1) X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0)) -> False) -> False)
  -> ((r4_binop_1 esk1_0 esk3_0 esk4_0 -> False) -> False)
  -> ((m2_filter_1 esk4_0 esk1_0 esk2_0 -> False) -> False)
  -> ((m2_filter_1 esk3_0 esk1_0 esk2_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk32_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk14_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk13_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk32_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk13_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk32_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk32_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk35_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v1_partfun1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk20_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk20_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk22_1 X1) -> False) -> False)
  -> ((v4_funct_1 esk34_0 -> False) -> False)
  -> ((v2_relat_1 esk28_0 -> False) -> False)
  -> ((v2_relat_1 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk21_0 -> False) -> False)
  -> ((v2_funct_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk30_0 -> False) -> False)
  -> ((v1_relat_1 esk28_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk19_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk30_0 -> False) -> False)
  -> ((v1_funct_1 esk28_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk19_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v8_relat_2 esk2_0 -> False) -> False)
  -> ((v3_relat_2 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
