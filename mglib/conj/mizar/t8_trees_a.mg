(** $I sig/MizarPreamble.mgs **)

Theorem t8_trees_a:
 forall esk33_4:set -> set -> set -> set -> set,
 forall r3_xboole_0:set -> set -> prop,
 forall v1_finseq_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k7_finseq_1:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk27_2:set -> set -> set,
 forall esk5_1:set -> set,
 forall esk7_1:set -> set,
 forall esk6_1:set -> set,
 forall v4_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v6_membered:set -> prop,
 forall v2_finseq_1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_rat_1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall esk13_1:set -> set,
 forall k6_finseq_1:set -> set,
 forall v1_finset_1:set -> prop,
 forall v7_membered:set -> prop,
 forall esk23_0:set,
 forall esk20_0:set,
 forall esk15_0:set,
 forall esk14_1:set -> set,
 forall esk10_1:set -> set,
 forall esk11_1:set -> set,
 forall k4_ordinal1:set,
 forall o_0_0_xboole_0:set,
 forall esk17_0:set,
 forall esk21_0:set,
 forall esk12_1:set -> set,
 forall esk26_1:set -> set,
 forall esk18_1:set -> set,
 forall esk16_2:set -> set -> set,
 forall esk19_0:set,
 forall esk22_0:set,
 forall esk25_0:set,
 forall esk1_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall v4_funct_1:set -> prop,
 forall esk24_1:set -> set,
 forall k1_numbers:set,
 forall v1_xcmplx_0:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v1_int_1:set -> prop,
 forall v3_finseq_1:set -> prop,
 forall v1_membered:set -> prop,
 forall v3_membered:set -> prop,
 forall v5_membered:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk28_2:set -> set -> set,
 forall v2_trees_1:set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall m1_finseq_1:set -> set -> prop,
 forall m4_trees_1:set -> set -> prop,
 forall k1_xboole_0:set,
 forall v1_xboole_0:set -> prop,
 forall v1_trees_1:set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall k4_trees_1:set -> set -> set,
 forall esk31_5:set -> set -> set -> set -> set -> set,
 forall esk32_4:set -> set -> set -> set -> set,
 forall esk34_4:set -> set -> set -> set -> set,
 forall esk35_4:set -> set -> set -> set -> set,
 forall k1_trees_a:set -> set -> set -> set,
 forall m2_finseq_1:set -> set -> prop,
 forall epred1_4:set -> set -> set -> set -> prop,
 forall r2_xboole_0:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k8_finseq_1:set -> set -> set -> set,
 forall esk30_5:set -> set -> set -> set -> set -> set,
 forall esk29_5:set -> set -> set -> set -> set -> set,
 forall k5_numbers:set,
     (forall X6 X2 X4 X5 X3 X1, ((k8_finseq_1 k5_numbers (esk29_5 X2 X3 X4 X5 X1) (esk30_5 X2 X3 X4 X5 X1)) = X1 -> False) -> X3 = (k1_trees_a X2 X5 X4) -> r2_hidden X6 X4 -> r2_hidden X1 X3 -> r2_xboole_0 X6 X1 -> m2_finseq_1 X6 k5_numbers -> m2_finseq_1 X1 k5_numbers -> epred1_4 X5 X4 X3 X2 -> False)
  -> (forall X3 X5 X4 X1 X2, ((k8_finseq_1 k5_numbers (esk29_5 X2 X3 X4 X5 X1) (esk30_5 X2 X3 X4 X5 X1)) = X1 -> False) -> (r2_hidden X1 X2 -> False) -> X3 = (k1_trees_a X2 X5 X4) -> r2_hidden X1 X3 -> m2_finseq_1 X1 k5_numbers -> epred1_4 X5 X4 X3 X2 -> False)
  -> (forall X5 X3 X4 X1 X2, (X2 = (k1_trees_a X1 X4 X3) -> False) -> ((k8_finseq_1 k5_numbers (esk34_4 X1 X2 X3 X4) (esk35_4 X1 X2 X3 X4)) = (esk32_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> False) -> r2_hidden X5 X3 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> r2_xboole_0 X5 (esk32_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X2 X3 X4, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (r2_xboole_0 (esk33_4 X1 X2 X3 X4) (esk32_4 X1 X2 X3 X4) -> False) -> epred1_4 X4 X3 X2 X1 -> r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> r2_hidden (esk32_4 X1 X2 X3 X4) X1 -> False)
  -> (forall X6 X1 X3 X5 X2 X4, (r2_hidden (esk30_5 X1 X2 X3 X4 X5) X4 -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X6 X3 -> r2_hidden X5 X2 -> r2_xboole_0 X6 X5 -> m2_finseq_1 X6 k5_numbers -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X6 X1 X4 X5 X2 X3, (r2_hidden (esk29_5 X1 X2 X3 X4 X5) X3 -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X6 X3 -> r2_hidden X5 X2 -> r2_xboole_0 X6 X5 -> m2_finseq_1 X6 k5_numbers -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X6 X1 X3 X4 X5 X2, (m2_finseq_1 (esk30_5 X1 X2 X3 X4 X5) k5_numbers -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X6 X3 -> r2_hidden X5 X2 -> r2_xboole_0 X6 X5 -> m2_finseq_1 X6 k5_numbers -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X6 X1 X3 X4 X5 X2, (m2_finseq_1 (esk29_5 X1 X2 X3 X4 X5) k5_numbers -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X6 X3 -> r2_hidden X5 X2 -> r2_xboole_0 X6 X5 -> m2_finseq_1 X6 k5_numbers -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X2 X4 X3 X5 X1, (r2_hidden X5 X1 -> False) -> (r2_hidden (esk30_5 X1 X2 X3 X4 X5) X4 -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X5 X2 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X2 X4 X3 X5 X1, (r2_hidden X5 X1 -> False) -> (r2_hidden (esk29_5 X1 X2 X3 X4 X5) X3 -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X5 X2 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X1 X4 X3 X5 X2, (r2_hidden X5 X2 -> False) -> (r2_xboole_0 (esk31_5 X1 X2 X3 X4 X5) X5 -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X5 X1 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X1 X4 X3 X5 X2, (r2_hidden X5 X2 -> False) -> (r2_hidden (esk31_5 X1 X2 X3 X4 X5) X3 -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X5 X1 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X2 X4 X3 X5 X1, (r2_hidden X5 X1 -> False) -> (m2_finseq_1 (esk30_5 X1 X2 X3 X4 X5) k5_numbers -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X5 X2 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X2 X4 X3 X5 X1, (r2_hidden X5 X1 -> False) -> (m2_finseq_1 (esk29_5 X1 X2 X3 X4 X5) k5_numbers -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X5 X2 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X1 X4 X3 X5 X2, (r2_hidden X5 X2 -> False) -> (m2_finseq_1 (esk31_5 X1 X2 X3 X4 X5) k5_numbers -> False) -> X2 = (k1_trees_a X1 X4 X3) -> r2_hidden X5 X1 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X4 X1 X2 X3, (X2 = (k1_trees_a X1 X4 X3) -> False) -> ((k8_finseq_1 k5_numbers (esk34_4 X1 X2 X3 X4) (esk35_4 X1 X2 X3 X4)) = (esk32_4 X1 X2 X3 X4) -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X1 -> False) -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X1 X2 X3 X4, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (r2_hidden (esk33_4 X1 X2 X3 X4) X3 -> False) -> epred1_4 X4 X3 X2 X1 -> r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> r2_hidden (esk32_4 X1 X2 X3 X4) X1 -> False)
  -> (forall X1 X2 X3 X4, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (m2_finseq_1 (esk33_4 X1 X2 X3 X4) k5_numbers -> False) -> epred1_4 X4 X3 X2 X1 -> r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> r2_hidden (esk32_4 X1 X2 X3 X4) X1 -> False)
  -> (forall X5 X3 X4 X1 X2, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> False) -> (r2_hidden (esk35_4 X1 X2 X3 X4) X4 -> False) -> r2_hidden X5 X3 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> r2_xboole_0 X5 (esk32_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X3 X4 X1 X2, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> False) -> (r2_hidden (esk34_4 X1 X2 X3 X4) X3 -> False) -> r2_hidden X5 X3 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> r2_xboole_0 X5 (esk32_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X3 X4 X1 X2, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> False) -> (m2_finseq_1 (esk35_4 X1 X2 X3 X4) k5_numbers -> False) -> r2_hidden X5 X3 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> r2_xboole_0 X5 (esk32_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X3 X4 X1 X2, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> False) -> (m2_finseq_1 (esk34_4 X1 X2 X3 X4) k5_numbers -> False) -> r2_hidden X5 X3 -> m2_finseq_1 X5 k5_numbers -> epred1_4 X4 X3 X2 X1 -> r2_xboole_0 X5 (esk32_4 X1 X2 X3 X4) -> False)
  -> (forall X4 X1 X2 X3, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X1 -> False) -> (r2_hidden (esk35_4 X1 X2 X3 X4) X4 -> False) -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X4 X1 X2 X3, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X1 -> False) -> (r2_hidden (esk34_4 X1 X2 X3 X4) X3 -> False) -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X4 X1 X2 X3, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X1 -> False) -> (m2_finseq_1 (esk35_4 X1 X2 X3 X4) k5_numbers -> False) -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X4 X1 X2 X3, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X2 -> False) -> (r2_hidden (esk32_4 X1 X2 X3 X4) X1 -> False) -> (m2_finseq_1 (esk34_4 X1 X2 X3 X4) k5_numbers -> False) -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X2 X1 X3 X4 X5 X6, (X6 = (k1_trees_a X5 X4 X3) -> False) -> (esk32_4 X5 X6 X3 X4) = (k8_finseq_1 k5_numbers X1 X2) -> r2_hidden X2 X4 -> r2_hidden X1 X3 -> m2_finseq_1 X2 k5_numbers -> m2_finseq_1 X1 k5_numbers -> epred1_4 X4 X3 X6 X5 -> r2_hidden (esk32_4 X5 X6 X3 X4) X6 -> False)
  -> (forall X4 X1 X2 X3, (X2 = (k1_trees_a X1 X4 X3) -> False) -> (m2_finseq_1 (esk32_4 X1 X2 X3 X4) k5_numbers -> False) -> epred1_4 X4 X3 X2 X1 -> False)
  -> (forall X1 X2 X3, (X3 = (k4_trees_1 X1 X2) -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X1 -> False) -> v1_trees_1 X3 -> v1_trees_1 X1 -> r2_hidden X2 X1 -> m2_finseq_1 X2 k5_numbers -> r2_hidden (esk9_3 X1 X2 X3) X3 -> r2_hidden (k8_finseq_1 k5_numbers X2 (esk9_3 X1 X2 X3)) X1 -> False)
  -> (forall X7 X4 X3 X2 X1 X5 X6, (r2_hidden X5 X6 -> False) -> X6 = (k1_trees_a X7 X4 X3) -> X5 = (k8_finseq_1 k5_numbers X1 X2) -> r2_hidden X2 X4 -> r2_hidden X1 X3 -> m2_finseq_1 X5 k5_numbers -> m2_finseq_1 X2 k5_numbers -> m2_finseq_1 X1 k5_numbers -> epred1_4 X4 X3 X6 X7 -> False)
  -> (forall X1 X2 X3, (X3 = (k4_trees_1 X1 X2) -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk9_3 X1 X2 X3) X3 -> False) -> (r2_hidden (k8_finseq_1 k5_numbers X2 (esk9_3 X1 X2 X3)) X1 -> False) -> v1_trees_1 X3 -> v1_trees_1 X1 -> r2_hidden X2 X1 -> m2_finseq_1 X2 k5_numbers -> False)
  -> (forall X3 X1 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (r2_hidden X2 X4 -> False) -> X4 = (k4_trees_1 X3 X1) -> v1_trees_1 X4 -> v1_trees_1 X3 -> r2_hidden X1 X3 -> m2_finseq_1 X2 k5_numbers -> m2_finseq_1 X1 k5_numbers -> r2_hidden (k8_finseq_1 k5_numbers X1 X2) X3 -> False)
  -> (forall X4 X1 X2 X3, (X3 = k1_xboole_0 -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (epred1_4 X2 X3 X4 X1 -> False) -> v1_trees_1 X4 -> v1_trees_1 X2 -> v1_trees_1 X1 -> m4_trees_1 X3 X1 -> False)
  -> (forall X2 X3 X1 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (k8_finseq_1 k5_numbers X3 X1) X4 -> False) -> X2 = (k4_trees_1 X4 X3) -> v1_trees_1 X4 -> v1_trees_1 X2 -> r2_hidden X3 X4 -> r2_hidden X1 X2 -> m2_finseq_1 X3 k5_numbers -> m2_finseq_1 X1 k5_numbers -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_trees_1 X2 -> v1_trees_1 X1 -> m4_trees_1 X3 X1 -> v1_xboole_0 (k1_trees_a X1 X2 X3) -> False)
  -> (forall X1 X2 X3, (X3 = (k4_trees_1 X1 X2) -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_finseq_1 (esk9_3 X1 X2 X3) k5_numbers -> False) -> v1_trees_1 X3 -> v1_trees_1 X1 -> r2_hidden X2 X1 -> m2_finseq_1 X2 k5_numbers -> False)
  -> (forall X3 X2 X1, (m2_finseq_1 (k8_finseq_1 X2 X1 X3) X2 -> False) -> m1_finseq_1 X3 X2 -> m1_finseq_1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_trees_1 (k1_trees_a X1 X2 X3) -> False) -> v1_trees_1 X2 -> v1_trees_1 X1 -> m4_trees_1 X3 X1 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_trees_1 X2 -> v1_trees_1 X1 -> r2_hidden (esk8_2 X1 X2) X2 -> r2_hidden (esk8_2 X1 X2) X1 -> False)
  -> (forall X2 X3 X1 X4, (r3_xboole_0 X1 X4 -> False) -> (k7_finseq_1 X1 X2) = (k7_finseq_1 X4 X3) -> v1_finseq_1 X4 -> v1_finseq_1 X3 -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X1 X2, (X1 = X2 -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v2_trees_1 X3 -> r2_hidden X2 X3 -> r2_hidden X1 X3 -> r3_xboole_0 X1 X2 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, ((k8_finseq_1 X2 X1 X3) = (k7_finseq_1 X1 X3) -> False) -> m1_finseq_1 X3 X2 -> m1_finseq_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> (k7_finseq_1 X1 X2) = (k7_finseq_1 X3 X2) -> v1_finseq_1 X3 -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (k7_finseq_1 X1 X2) = (k7_finseq_1 X1 X3) -> v1_finseq_1 X3 -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1 X2, ((k7_finseq_1 X2 (esk28_2 X2 X1)) = X1 -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r1_tarski X2 X1 -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_2 X1 X2) X2 -> False) -> (r2_hidden (esk8_2 X1 X2) X1 -> False) -> v1_trees_1 X2 -> v1_trees_1 X1 -> False)
  -> (forall X1 X3 X2, (r1_tarski X3 X2 -> False) -> X2 = (k7_finseq_1 X3 X1) -> v1_finseq_1 X3 -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (esk28_2 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (esk28_2 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_finseq_1 (esk28_2 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_xboole_0 (k7_finseq_1 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_xboole_0 (k7_finseq_1 X1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers X2)) -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (r3_xboole_0 (esk6_1 X1) (esk7_1 X1) -> False) -> v1_finseq_1 (esk5_1 X1) -> v1_relat_1 (esk5_1 X1) -> v1_funct_1 (esk5_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_trees_1 X1 -> m1_finseq_1 X2 k5_numbers -> v1_xboole_0 (k4_trees_1 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k7_finseq_1 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (k7_finseq_1 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_finseq_1 (k7_finseq_1 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_funct_1 (k7_finseq_1 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_relat_1 (k7_finseq_1 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_finseq_1 (k7_finseq_1 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (r2_hidden (esk7_1 X1) X1 -> False) -> v1_finseq_1 (esk5_1 X1) -> v1_relat_1 (esk5_1 X1) -> v1_funct_1 (esk5_1 X1) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (r2_hidden (esk6_1 X1) X1 -> False) -> v1_finseq_1 (esk5_1 X1) -> v1_relat_1 (esk5_1 X1) -> v1_funct_1 (esk5_1 X1) -> False)
  -> (forall X1 X2, (v1_funct_1 (k7_finseq_1 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k7_finseq_1 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_finseq_1 (k7_finseq_1 X1 X2) -> False) -> v1_finseq_1 X2 -> v1_finseq_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (esk7_1 X1) = (esk6_1 X1) -> v1_finseq_1 (esk5_1 X1) -> v1_relat_1 (esk5_1 X1) -> v1_funct_1 (esk5_1 X1) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_funct_1 (esk7_1 X1) -> False) -> v1_finseq_1 (esk5_1 X1) -> v1_relat_1 (esk5_1 X1) -> v1_funct_1 (esk5_1 X1) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_funct_1 (esk6_1 X1) -> False) -> v1_finseq_1 (esk5_1 X1) -> v1_relat_1 (esk5_1 X1) -> v1_funct_1 (esk5_1 X1) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_relat_1 (esk7_1 X1) -> False) -> v1_finseq_1 (esk5_1 X1) -> v1_relat_1 (esk5_1 X1) -> v1_funct_1 (esk5_1 X1) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_relat_1 (esk6_1 X1) -> False) -> v1_finseq_1 (esk5_1 X1) -> v1_relat_1 (esk5_1 X1) -> v1_funct_1 (esk5_1 X1) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_finseq_1 (esk7_1 X1) -> False) -> v1_finseq_1 (esk5_1 X1) -> v1_relat_1 (esk5_1 X1) -> v1_funct_1 (esk5_1 X1) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_finseq_1 (esk6_1 X1) -> False) -> v1_finseq_1 (esk5_1 X1) -> v1_relat_1 (esk5_1 X1) -> v1_funct_1 (esk5_1 X1) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_finseq_1 (esk8_2 X1 X2) k5_numbers -> False) -> v1_trees_1 X2 -> v1_trees_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_trees_1 (k4_trees_1 X1 X2) -> False) -> v1_trees_1 X1 -> m1_finseq_1 X2 k5_numbers -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_2 X1 X2) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> (r3_xboole_0 (esk6_1 X1) (esk7_1 X1) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk27_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk27_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> (r2_hidden (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> (r2_hidden (esk6_1 X1) X1 -> False) -> False)
  -> (forall X2 X1, r2_xboole_0 X2 X1 -> r2_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_finseq_1 X2 -> False) -> v3_finseq_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> (r2_xboole_0 X1 X2 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v2_trees_1 X2 -> False) -> v1_trees_1 X1 -> m4_trees_1 X2 X1 -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> (esk7_1 X1) = (esk6_1 X1) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (r3_xboole_0 X2 X1 -> False) -> r3_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_finseq_1 X1 X2 -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v5_relat_1 X1 X2 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m2_finseq_1 X1 X2 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_funct_1 (esk7_1 X1) -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_funct_1 (esk6_1 X1) -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_relat_1 (esk7_1 X1) -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_relat_1 (esk6_1 X1) -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_finseq_1 (esk7_1 X1) -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, (v2_trees_1 X1 -> False) -> (v1_finseq_1 (esk6_1 X1) -> False) -> (r2_hidden (esk5_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k7_finseq_1 k1_xboole_0 X1) = X1 -> False) -> v1_finseq_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, ((k7_finseq_1 X1 k1_xboole_0) = X1 -> False) -> v1_finseq_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v4_relat_1 X1 k5_numbers -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v2_finseq_1 X1 -> False)
  -> (forall X1, (v4_relat_1 X1 k5_numbers -> False) -> v1_finseq_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v2_trees_1 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v2_trees_1 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, (v1_finseq_1 X1 -> False) -> v2_trees_1 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_finseq_1 X2 -> False) -> v3_finseq_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m4_trees_1 (esk13_1 X1) X1 -> False) -> v1_trees_1 X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden (k6_finseq_1 k5_numbers) X1 -> False) -> v1_trees_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_finseq_1 X1 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_finseq_1 X1 -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, X1 = X2 -> r2_xboole_0 X1 X2 -> False)
  -> (forall X1, (v2_finseq_1 X1 -> False) -> v1_finseq_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_finseq_1 X1 -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_finseq_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (r2_hidden k1_xboole_0 X1 -> False) -> v1_trees_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk24_1 X1) k5_numbers -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v1_finseq_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_finseq_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v2_finseq_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finseq_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v3_finseq_1 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_finseq_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k4_trees_1 (k1_trees_a esk2_0 esk1_0 esk3_0) esk4_0) = esk1_0 -> False)
  -> (forall X1, r2_xboole_0 X1 X1 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk22_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers X1)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_finseq_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_finseq_1 (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk14_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, (m2_finseq_1 (esk12_1 X1) X1 -> False) -> False)
  -> (forall X1, (m2_finseq_1 (k6_finseq_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk26_1 X1) k5_numbers -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk18_1 X1) k5_numbers -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk14_1 X1) k5_numbers -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (r3_xboole_0 X1 X1 -> False) -> False)
  -> ((v4_relat_1 esk23_0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((r2_hidden esk4_0 esk3_0 -> False) -> False)
  -> ((m2_finseq_1 esk4_0 k5_numbers -> False) -> False)
  -> ((m4_trees_1 esk3_0 esk2_0 -> False) -> False)
  -> (forall X1, (v2_finseq_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk14_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk14_1 X1) -> False) -> False)
  -> (forall X1, (v1_finseq_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_finseq_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_finseq_1 (esk14_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (k6_finseq_1 X1) -> False) -> False)
  -> ((v2_finseq_1 esk23_0 -> False) -> False)
  -> ((v2_finseq_1 esk21_0 -> False) -> False)
  -> ((v1_finset_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v7_membered esk22_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v6_membered esk22_0 -> False) -> False)
  -> ((v6_membered esk19_0 -> False) -> False)
  -> ((v6_membered esk15_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> ((v1_finseq_1 esk23_0 -> False) -> False)
  -> ((v3_finseq_1 esk25_0 -> False) -> False)
  -> ((v1_trees_1 esk2_0 -> False) -> False)
  -> ((v1_trees_1 esk1_0 -> False) -> False)
  -> ((v1_xboole_0 esk17_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
