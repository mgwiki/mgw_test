(** $I sig/MizarPreamble.mgs **)

Theorem t11_radix_6:
 forall k6_radix_6:set -> set -> set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall k5_radix_6:set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall m1_finseq_1:set -> set -> prop,
 forall v1_int_1:set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall k4_numbers:set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall v2_xxreal_0:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v1_finseq_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_numbers:set,
 forall k4_ordinal1:set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall k2_radix_1:set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall np__0:set,
 forall esk20_0:set,
 forall esk18_0:set,
 forall esk13_2:set -> set -> set,
 forall esk7_1:set -> set,
 forall esk8_1:set -> set,
 forall esk11_0:set,
 forall esk22_0:set,
 forall esk27_0:set,
 forall esk28_0:set,
 forall esk14_0:set,
 forall esk15_0:set,
 forall esk12_0:set,
 forall esk17_0:set,
 forall esk26_0:set,
 forall esk16_0:set,
 forall esk25_0:set,
 forall esk24_0:set,
 forall esk21_0:set,
 forall esk9_1:set -> set,
 forall esk23_1:set -> set,
 forall esk19_0:set,
 forall esk29_0:set,
 forall k1_xboole_0:set,
 forall v5_ordinal1:set -> prop,
 forall k1_finseq_1:set -> set,
 forall v1_xxreal_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v3_xxreal_0:set -> prop,
 forall k5_numbers:set,
 forall esk10_2:set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall k4_xcmplx_0:set -> set,
 forall k1_radix_1:set -> set,
 forall k1_radix_5:set -> set -> set -> set,
 forall esk4_4:set -> set -> set -> set -> set,
 forall k2_radix_5:set -> set -> set -> set,
 forall k1_radix_6:set -> set -> set -> set -> set,
 forall esk5_4:set -> set -> set -> set -> set,
 forall k2_radix_6:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k2_finseq_1:set -> set,
 forall k4_radix_1:set -> set -> set -> set -> set,
 forall esk30_5:set -> set -> set -> set -> set -> set,
 forall v7_ordinal1:set -> prop,
 forall v3_card_1:set -> set -> prop,
 forall m2_finseq_1:set -> set -> prop,
 forall k3_radix_1:set -> set,
 forall np__1:set,
 forall r1_xxreal_0:set -> set -> prop,
 forall np__2:set,
 forall k10_radix_1:set -> set -> set -> set,
 forall k6_numbers:set,
 forall k8_radix_1:set -> set -> set -> set,
 forall k2_xcmplx_0:set -> set -> set,
     (forall X1 X4 X3 X5 X2, ((k2_xcmplx_0 (k8_radix_1 X1 X2 X5) (k8_radix_1 X1 X2 (k10_radix_1 X2 X1 k6_numbers))) = (k2_xcmplx_0 (k8_radix_1 X1 X2 X3) (k8_radix_1 X1 X2 X4)) -> False) -> (k4_radix_1 (esk30_5 X1 X2 X3 X4 X5) X2 X1 X3) = k6_numbers -> (k4_radix_1 (esk30_5 X1 X2 X3 X4 X5) X2 X1 X4) = (k4_radix_1 (esk30_5 X1 X2 X3 X4 X5) X2 X1 X5) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v3_card_1 X5 X1 -> v3_card_1 X4 X1 -> v3_card_1 X3 X1 -> r1_xxreal_0 np__2 X2 -> r1_xxreal_0 np__1 X1 -> m2_finseq_1 X5 (k3_radix_1 X2) -> m2_finseq_1 X4 (k3_radix_1 X2) -> m2_finseq_1 X3 (k3_radix_1 X2) -> False)
  -> (forall X1 X4 X3 X5 X2, ((k2_xcmplx_0 (k8_radix_1 X1 X2 X5) (k8_radix_1 X1 X2 (k10_radix_1 X2 X1 k6_numbers))) = (k2_xcmplx_0 (k8_radix_1 X1 X2 X3) (k8_radix_1 X1 X2 X4)) -> False) -> (k4_radix_1 (esk30_5 X1 X2 X3 X4 X5) X2 X1 X4) = k6_numbers -> (k4_radix_1 (esk30_5 X1 X2 X3 X4 X5) X2 X1 X3) = (k4_radix_1 (esk30_5 X1 X2 X3 X4 X5) X2 X1 X5) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v3_card_1 X5 X1 -> v3_card_1 X4 X1 -> v3_card_1 X3 X1 -> r1_xxreal_0 np__2 X2 -> r1_xxreal_0 np__1 X1 -> m2_finseq_1 X5 (k3_radix_1 X2) -> m2_finseq_1 X4 (k3_radix_1 X2) -> m2_finseq_1 X3 (k3_radix_1 X2) -> False)
  -> (forall X1 X4 X3 X5 X2, ((k2_xcmplx_0 (k8_radix_1 X1 X2 X5) (k8_radix_1 X1 X2 (k10_radix_1 X2 X1 k6_numbers))) = (k2_xcmplx_0 (k8_radix_1 X1 X2 X3) (k8_radix_1 X1 X2 X4)) -> False) -> (r2_hidden (esk30_5 X1 X2 X3 X4 X5) (k2_finseq_1 X1) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v3_card_1 X5 X1 -> v3_card_1 X4 X1 -> v3_card_1 X3 X1 -> r1_xxreal_0 np__2 X2 -> r1_xxreal_0 np__1 X1 -> m2_finseq_1 X5 (k3_radix_1 X2) -> m2_finseq_1 X4 (k3_radix_1 X2) -> m2_finseq_1 X3 (k3_radix_1 X2) -> False)
  -> (forall X1 X4 X3 X5 X2, ((k2_xcmplx_0 (k8_radix_1 X1 X2 X5) (k8_radix_1 X1 X2 (k10_radix_1 X2 X1 k6_numbers))) = (k2_xcmplx_0 (k8_radix_1 X1 X2 X3) (k8_radix_1 X1 X2 X4)) -> False) -> (v7_ordinal1 (esk30_5 X1 X2 X3 X4 X5) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v3_card_1 X5 X1 -> v3_card_1 X4 X1 -> v3_card_1 X3 X1 -> r1_xxreal_0 np__2 X2 -> r1_xxreal_0 np__1 X1 -> m2_finseq_1 X5 (k3_radix_1 X2) -> m2_finseq_1 X4 (k3_radix_1 X2) -> m2_finseq_1 X3 (k3_radix_1 X2) -> False)
  -> (forall X1 X3 X4 X2, (X4 = (k2_radix_6 X1 X2 X3) -> False) -> (k4_radix_1 (esk5_4 X1 X2 X3 X4) X2 (k2_xcmplx_0 X1 np__2) X4) = (k1_radix_6 (esk5_4 X1 X2 X3 X4) X1 X2 X3) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m2_finseq_1 X4 (k3_radix_1 X2) -> m2_finseq_1 X3 (k3_radix_1 X2) -> v3_card_1 X4 (k2_xcmplx_0 X1 np__2) -> v3_card_1 X3 (k2_xcmplx_0 X1 np__2) -> False)
  -> (forall X1 X3 X4 X2, (X4 = (k6_radix_6 X1 X2 X3) -> False) -> (k4_radix_1 (esk6_4 X1 X2 X3 X4) X2 (k2_xcmplx_0 X1 np__2) X4) = (k5_radix_6 (esk6_4 X1 X2 X3 X4) X1 X2 X3) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m2_finseq_1 X4 (k3_radix_1 X2) -> m2_finseq_1 X3 (k3_radix_1 X2) -> v3_card_1 X4 (k2_xcmplx_0 X1 np__2) -> v3_card_1 X3 (k2_xcmplx_0 X1 np__2) -> False)
  -> (forall X2 X4 X1 X3, (X4 = (k2_radix_5 X1 X2 X3) -> False) -> (k4_radix_1 (esk4_4 X1 X2 X3 X4) X3 X1 X4) = (k1_radix_5 (esk4_4 X1 X2 X3 X4) X2 X3) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v3_card_1 X4 X1 -> m2_finseq_1 X4 (k3_radix_1 X3) -> False)
  -> (forall X5 X4 X3 X2 X1, ((k4_radix_1 X5 X3 (k2_xcmplx_0 X2 np__2) X1) = (k5_radix_6 X5 X2 X3 X4) -> False) -> X1 = (k6_radix_6 X2 X3 X4) -> v7_ordinal1 X5 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> m2_finseq_1 X4 (k3_radix_1 X3) -> m2_finseq_1 X1 (k3_radix_1 X3) -> v3_card_1 X4 (k2_xcmplx_0 X2 np__2) -> v3_card_1 X1 (k2_xcmplx_0 X2 np__2) -> r2_hidden X5 (k2_finseq_1 (k2_xcmplx_0 X2 np__2)) -> False)
  -> (forall X5 X4 X3 X2 X1, ((k4_radix_1 X5 X3 (k2_xcmplx_0 X2 np__2) X1) = (k1_radix_6 X5 X2 X3 X4) -> False) -> X1 = (k2_radix_6 X2 X3 X4) -> v7_ordinal1 X5 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> m2_finseq_1 X4 (k3_radix_1 X3) -> m2_finseq_1 X1 (k3_radix_1 X3) -> v3_card_1 X4 (k2_xcmplx_0 X2 np__2) -> v3_card_1 X1 (k2_xcmplx_0 X2 np__2) -> r2_hidden X5 (k2_finseq_1 (k2_xcmplx_0 X2 np__2)) -> False)
  -> (forall X1 X3 X4 X2, (X4 = (k2_radix_6 X1 X2 X3) -> False) -> (r2_hidden (esk5_4 X1 X2 X3 X4) (k2_finseq_1 (k2_xcmplx_0 X1 np__2)) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m2_finseq_1 X4 (k3_radix_1 X2) -> m2_finseq_1 X3 (k3_radix_1 X2) -> v3_card_1 X4 (k2_xcmplx_0 X1 np__2) -> v3_card_1 X3 (k2_xcmplx_0 X1 np__2) -> False)
  -> (forall X1 X3 X4 X2, (X4 = (k6_radix_6 X1 X2 X3) -> False) -> (r2_hidden (esk6_4 X1 X2 X3 X4) (k2_finseq_1 (k2_xcmplx_0 X1 np__2)) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m2_finseq_1 X4 (k3_radix_1 X2) -> m2_finseq_1 X3 (k3_radix_1 X2) -> v3_card_1 X4 (k2_xcmplx_0 X1 np__2) -> v3_card_1 X3 (k2_xcmplx_0 X1 np__2) -> False)
  -> (forall X1 X3 X4 X2, (X4 = (k2_radix_6 X1 X2 X3) -> False) -> (v7_ordinal1 (esk5_4 X1 X2 X3 X4) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m2_finseq_1 X4 (k3_radix_1 X2) -> m2_finseq_1 X3 (k3_radix_1 X2) -> v3_card_1 X4 (k2_xcmplx_0 X1 np__2) -> v3_card_1 X3 (k2_xcmplx_0 X1 np__2) -> False)
  -> (forall X1 X3 X4 X2, (X4 = (k6_radix_6 X1 X2 X3) -> False) -> (v7_ordinal1 (esk6_4 X1 X2 X3 X4) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m2_finseq_1 X4 (k3_radix_1 X2) -> m2_finseq_1 X3 (k3_radix_1 X2) -> v3_card_1 X4 (k2_xcmplx_0 X1 np__2) -> v3_card_1 X3 (k2_xcmplx_0 X1 np__2) -> False)
  -> (forall X2 X4 X1 X3, (X4 = (k2_radix_5 X1 X2 X3) -> False) -> (r2_hidden (esk4_4 X1 X2 X3 X4) (k2_finseq_1 X1) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v3_card_1 X4 X1 -> m2_finseq_1 X4 (k3_radix_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (X4 = (k2_radix_5 X1 X2 X3) -> False) -> (v7_ordinal1 (esk4_4 X1 X2 X3 X4) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v3_card_1 X4 X1 -> m2_finseq_1 X4 (k3_radix_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (m1_subset_1 (k5_radix_6 X1 X2 X3 X4) (k3_radix_1 X3) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m1_finseq_1 X4 (k3_radix_1 X3) -> v3_card_1 X4 (k2_xcmplx_0 X2 np__2) -> False)
  -> (forall X2 X4 X1 X3, (m1_subset_1 (k1_radix_6 X1 X2 X3 X4) (k3_radix_1 X3) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m1_finseq_1 X4 (k3_radix_1 X3) -> v3_card_1 X4 (k2_xcmplx_0 X2 np__2) -> False)
  -> (forall X2 X4 X1 X3, (v1_int_1 (k4_radix_1 X1 X2 X3 X4) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v3_card_1 X4 X3 -> m1_finseq_1 X4 (k3_radix_1 X2) -> False)
  -> (forall X3 X4 X1 X2, ((k5_radix_6 X2 X1 X3 X4) = (k2_xcmplx_0 (k4_xcmplx_0 (k1_radix_1 X3)) np__1) -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 np__2 X3 -> m2_finseq_1 X4 (k3_radix_1 X3) -> v3_card_1 X4 (k2_xcmplx_0 X1 np__2) -> r2_hidden X2 (k2_finseq_1 (k2_xcmplx_0 X1 np__2)) -> False)
  -> (forall X2 X4 X1 X3, ((k5_radix_6 X2 X1 X3 X4) = (k1_funct_1 X4 X2) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X1 X2 -> r1_xxreal_0 np__2 X3 -> m2_finseq_1 X4 (k3_radix_1 X3) -> v3_card_1 X4 (k2_xcmplx_0 X1 np__2) -> r2_hidden X2 (k2_finseq_1 (k2_xcmplx_0 X1 np__2)) -> False)
  -> (forall X5 X4 X3 X2 X1, ((k4_radix_1 X5 X4 X2 X1) = (k1_radix_5 X5 X3 X4) -> False) -> X1 = (k2_radix_5 X2 X3 X4) -> v7_ordinal1 X5 -> v7_ordinal1 X4 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v3_card_1 X1 X2 -> m2_finseq_1 X1 (k3_radix_1 X4) -> r2_hidden X5 (k2_finseq_1 X2) -> False)
  -> (forall X2 X4 X1 X3, ((k1_radix_6 X2 X1 X3 X4) = (k1_funct_1 X4 X2) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X1 X2 -> m2_finseq_1 X4 (k3_radix_1 X3) -> v3_card_1 X4 (k2_xcmplx_0 X1 np__2) -> r2_hidden X2 (k2_finseq_1 (k2_xcmplx_0 X1 np__2)) -> False)
  -> (forall X3 X4 X1 X2, ((k1_radix_6 X2 X1 X3 X4) = k6_numbers -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m2_finseq_1 X4 (k3_radix_1 X3) -> v3_card_1 X4 (k2_xcmplx_0 X1 np__2) -> r2_hidden X2 (k2_finseq_1 (k2_xcmplx_0 X1 np__2)) -> False)
  -> (forall X1 X3 X2, (v3_card_1 (k2_radix_6 X1 X2 X3) (k2_xcmplx_0 X1 np__2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m1_finseq_1 X3 (k3_radix_1 X2) -> v3_card_1 X3 (k2_xcmplx_0 X1 np__2) -> False)
  -> (forall X1 X3 X2, (v3_card_1 (k6_radix_6 X1 X2 X3) (k2_xcmplx_0 X1 np__2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m1_finseq_1 X3 (k3_radix_1 X2) -> v3_card_1 X3 (k2_xcmplx_0 X1 np__2) -> False)
  -> (forall X1 X3 X2, (m2_finseq_1 (k2_radix_6 X1 X2 X3) (k3_radix_1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m1_finseq_1 X3 (k3_radix_1 X2) -> v3_card_1 X3 (k2_xcmplx_0 X1 np__2) -> False)
  -> (forall X1 X3 X2, (m2_finseq_1 (k6_radix_6 X1 X2 X3) (k3_radix_1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> m1_finseq_1 X3 (k3_radix_1 X2) -> v3_card_1 X3 (k2_xcmplx_0 X1 np__2) -> False)
  -> (forall X1 X2 X3, (m2_subset_1 (k1_radix_5 X1 X2 X3) k4_numbers (k3_radix_1 X3) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X3 X2, (v1_int_1 (k8_radix_1 X1 X2 X3) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v3_card_1 X3 X1 -> m1_finseq_1 X3 (k3_radix_1 X2) -> False)
  -> (forall X3 X2 X1, ((k1_radix_5 X1 X2 X3) = (k2_xcmplx_0 (k4_xcmplx_0 (k1_radix_1 X3)) np__1) -> False) -> (r1_xxreal_0 X2 X1 -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 np__2 X3 -> r1_xxreal_0 np__1 X1 -> False)
  -> (forall X1 X2 X3, (m2_finseq_1 (k2_radix_5 X1 X2 X3) (k3_radix_1 X3) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (m2_finseq_1 (k10_radix_1 X1 X2 X3) (k3_radix_1 X1) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (v3_card_1 (k2_radix_5 X1 X2 X3) X1 -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, (v3_card_1 (k10_radix_1 X1 X2 X3) X2 -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk10_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, ((k1_radix_5 X2 X1 X3) = k6_numbers -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X1 X2 -> r1_xxreal_0 np__2 X3 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, ((k1_radix_5 X1 X2 X3) = k6_numbers -> False) -> (r1_xxreal_0 np__1 X1 -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 np__2 X3 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers X2)) -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (r1_xxreal_0 X1 (k2_xcmplx_0 X2 X3) -> False) -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (r2_hidden X1 (k2_finseq_1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X1 X2 -> r1_xxreal_0 np__1 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> v1_xboole_0 (k2_xcmplx_0 X2 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (r1_xxreal_0 X1 X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_hidden X1 (k2_finseq_1 X2) -> False)
  -> (forall X2 X1, (r1_xxreal_0 np__1 X1 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_hidden X1 (k2_finseq_1 X2) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> (v3_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 (k2_xcmplx_0 X2 X1) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X2 -> False) -> (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v3_xxreal_0 X2 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xreal_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (v1_int_1 (k2_xcmplx_0 X1 X2) -> False) -> v1_int_1 X2 -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (v7_ordinal1 (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X1 X2, (v3_xxreal_0 X2 -> False) -> (v2_xxreal_0 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> False)
  -> (forall X2 X1, (m1_finseq_1 X1 X2 -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m2_finseq_1 X1 X2 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (m1_subset_1 (k2_finseq_1 X1) (k1_zfmisc_1 k5_numbers) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (m1_subset_1 (k3_radix_1 X1) (k1_zfmisc_1 k4_numbers) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v3_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> v2_xxreal_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, v3_xxreal_0 X1 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X2 X1, (v1_finseq_1 X1 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_finseq_1 X1 -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (k1_radix_1 X1) k5_numbers -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_int_1 X1 -> False) -> m1_subset_1 X1 k4_numbers -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, v7_ordinal1 X1 -> v1_xboole_0 (k3_radix_1 X1) -> False)
  -> (forall X1, (v2_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v1_xxreal_0 X1 -> v1_xboole_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v2_xxreal_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, v3_xxreal_0 X1 -> v1_xxreal_0 X1 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v3_xxreal_0 X1 -> False) -> (v1_xboole_0 X1 -> False) -> (v2_xxreal_0 X1 -> False) -> v1_xxreal_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xreal_0 (k4_xcmplx_0 X1) -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_int_1 (k4_xcmplx_0 X1) -> False) -> v1_int_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, ((k2_radix_1 X1) = (k3_radix_1 X1) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, ((k2_finseq_1 X1) = (k1_finseq_1 X1) -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, v7_ordinal1 X1 -> v3_xxreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v1_int_1 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_int_1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k2_xcmplx_0 (k8_radix_1 (k2_xcmplx_0 esk1_0 np__2) esk2_0 (k2_radix_6 esk1_0 esk2_0 esk3_0)) (k8_radix_1 (k2_xcmplx_0 esk1_0 np__2) esk2_0 (k2_radix_5 (k2_xcmplx_0 esk1_0 np__2) esk1_0 esk2_0))) = (k2_xcmplx_0 (k8_radix_1 (k2_xcmplx_0 esk1_0 np__2) esk2_0 (k6_radix_6 esk1_0 esk2_0 esk3_0)) (k8_radix_1 (k2_xcmplx_0 esk1_0 np__2) esk2_0 (k10_radix_1 esk2_0 (k2_xcmplx_0 esk1_0 np__2) k6_numbers))) -> False)
  -> (r1_xxreal_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__2) -> False)
  -> (r1_xxreal_0 np__0 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__0 (k4_xcmplx_0 np__2) -> False)
  -> (r1_xxreal_0 np__1 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__1 (k4_xcmplx_0 np__2) -> False)
  -> (r1_xxreal_0 np__2 (k4_xcmplx_0 np__1) -> False)
  -> (r1_xxreal_0 np__2 (k4_xcmplx_0 np__2) -> False)
  -> (r1_xxreal_0 np__1 np__0 -> False)
  -> (r1_xxreal_0 np__2 np__0 -> False)
  -> (r1_xxreal_0 np__2 np__1 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (v1_xboole_0 np__2 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk13_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__2 k1_numbers k5_numbers -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk13_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk13_2 X1 X2) X1 -> False) -> False)
  -> ((v3_card_1 esk3_0 (k2_xcmplx_0 esk1_0 np__2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk13_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk13_2 X1 X2) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__2) -> False) -> False)
  -> (forall X1, (m1_finseq_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (m2_finseq_1 (esk9_1 X1) X1 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__0 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__1 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__1) np__2 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__2) np__0 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__2) np__1 -> False) -> False)
  -> ((r1_xxreal_0 (k4_xcmplx_0 np__2) np__2 -> False) -> False)
  -> ((m1_subset_1 esk18_0 (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m2_finseq_1 esk3_0 (k3_radix_1 esk2_0) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__2) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) np__2) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 (k4_xcmplx_0 np__2)) = np__0 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk11_0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__2 k5_numbers -> False) -> False)
  -> ((m1_subset_1 np__2 k1_numbers -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__0 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__2 -> False) -> False)
  -> ((r1_xxreal_0 np__2 esk2_0 -> False) -> False)
  -> ((r1_xxreal_0 np__2 np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__2) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__1) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 np__0) = np__2 -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v5_ordinal1 (esk23_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk23_1 X1) -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__2)) = np__2 -> False) -> False)
  -> ((v2_xxreal_0 esk22_0 -> False) -> False)
  -> ((v2_xxreal_0 esk21_0 -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v2_xxreal_0 np__2 -> False) -> False)
  -> ((v1_xcmplx_0 esk27_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk24_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk21_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 esk28_0 -> False) -> False)
  -> ((v1_xboole_0 esk27_0 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_xxreal_0 esk28_0 -> False) -> False)
  -> ((v1_xxreal_0 esk27_0 -> False) -> False)
  -> ((v1_xxreal_0 esk25_0 -> False) -> False)
  -> ((v1_xxreal_0 esk24_0 -> False) -> False)
  -> ((v1_xxreal_0 esk22_0 -> False) -> False)
  -> ((v1_xxreal_0 esk21_0 -> False) -> False)
  -> ((v1_xxreal_0 esk16_0 -> False) -> False)
  -> ((v1_xxreal_0 esk11_0 -> False) -> False)
  -> ((v3_xxreal_0 esk25_0 -> False) -> False)
  -> ((v3_xxreal_0 esk24_0 -> False) -> False)
  -> ((v1_xreal_0 esk27_0 -> False) -> False)
  -> ((v1_xreal_0 esk24_0 -> False) -> False)
  -> ((v1_xreal_0 esk21_0 -> False) -> False)
  -> ((v1_xreal_0 esk15_0 -> False) -> False)
  -> ((v1_xreal_0 esk11_0 -> False) -> False)
  -> ((v2_ordinal1 esk19_0 -> False) -> False)
  -> ((v1_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk19_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v3_ordinal1 esk12_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> ((v1_int_1 esk17_0 -> False) -> False)
  -> ((v1_int_1 esk11_0 -> False) -> False)
  -> ((v7_ordinal1 esk29_0 -> False) -> False)
  -> ((v7_ordinal1 esk26_0 -> False) -> False)
  -> ((v7_ordinal1 esk2_0 -> False) -> False)
  -> ((v7_ordinal1 esk1_0 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
