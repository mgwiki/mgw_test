(** $I sig/MizarPreamble.mgs **)

Theorem t38_cqc_the3:
 forall esk22_4:set -> set -> set -> set -> set,
 forall esk21_4:set -> set -> set -> set -> set,
 forall k6_numbers:set,
 forall r5_cqc_the3:set -> set -> set -> prop,
 forall k1_numbers:set,
 forall esk23_5:set -> set -> set -> set -> set -> set,
 forall esk7_4:set -> set -> set -> set -> set,
 forall esk6_4:set -> set -> set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall esk11_2:set -> set -> set,
 forall v7_ordinal1:set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall v4_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v6_membered:set -> prop,
 forall v1_int_1:set -> prop,
 forall esk14_1:set -> set,
 forall k1_card_1:set -> set,
 forall v3_relat_1:set -> prop,
 forall v7_membered:set -> prop,
 forall k1_xboole_0:set,
 forall esk19_1:set -> set,
 forall esk15_0:set,
 forall esk12_0:set,
 forall esk10_1:set -> set,
 forall esk16_0:set,
 forall esk9_0:set,
 forall v1_card_1:set -> prop,
 forall k4_ordinal1:set,
 forall esk17_1:set -> set,
 forall esk13_0:set,
 forall esk18_0:set,
 forall np__0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall v2_relat_1:set -> prop,
 forall esk20_1:set -> set,
 forall v1_rat_1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v1_membered:set -> prop,
 forall v3_membered:set -> prop,
 forall v5_membered:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v2_xxreal_0:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k1_nat_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall k15_qc_lang1:set -> set -> set -> set,
 forall k3_finseq_1:set -> set,
 forall np__1:set,
 forall k11_cqc_lang:set -> set -> set -> set,
 forall k2_nat_1:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_finseq_1:set -> prop,
 forall k5_numbers:set,
 forall m1_subset_1:set -> set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k3_cqc_lang:set -> set,
 forall k9_qc_lang1:set -> set,
 forall k2_qc_lang1:set -> set,
 forall k3_qc_lang1:set -> set,
 forall r1_xxreal_0:set -> set -> prop,
 forall v6_qc_lang1:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall m1_qc_lang1:set -> prop,
 forall esk8_5:set -> set -> set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall r6_cqc_the3:set -> set -> set -> prop,
     (forall X7 X4 X1 X3 X6 X5 X2, (r6_cqc_the3 X2 X5 X6 -> False) -> (k3_finseq_1 X4) = X7 -> (k1_funct_1 X4 X7) = X5 -> (k1_funct_1 X4 np__1) = X6 -> X3 = (k1_funct_1 X4 (esk8_5 X2 X5 X6 X7 X4)) -> (k1_funct_1 X4 (k2_nat_1 (esk8_5 X2 X5 X6 X7 X4) np__1)) = (k11_cqc_lang X2 X1 X3) -> m1_qc_lang1 X2 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> v6_qc_lang1 X5 X2 -> m1_subset_1 X7 k5_numbers -> r1_xxreal_0 np__1 X7 -> m2_subset_1 X6 (k9_qc_lang1 X2) (k3_cqc_lang X2) -> m2_subset_1 X5 (k9_qc_lang1 X2) (k3_cqc_lang X2) -> m2_subset_1 X3 (k9_qc_lang1 X2) (k3_cqc_lang X2) -> m2_subset_1 X1 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> False)
  -> (forall X5 X6 X1 X4 X3 X2, ((k1_funct_1 X4 (esk21_4 X1 X2 X3 X4)) = (esk22_4 X1 X2 X3 X4) -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X6 X1 X4 X3 X2, ((k1_funct_1 X4 (esk21_4 X1 X2 X3 X4)) = (esk22_4 X1 X2 X3 X4) -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X6 X4 X3 X2 X1, (m2_subset_1 (esk22_4 X1 X2 X3 X4) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X1 X4 X3 X2, ((k1_funct_1 X4 (esk21_4 X1 X2 X3 X4)) = (esk22_4 X1 X2 X3 X4) -> False) -> (r1_xxreal_0 k6_numbers X3 -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X1 X4 X3 X2, ((k1_funct_1 X4 (esk21_4 X1 X2 X3 X4)) = (esk22_4 X1 X2 X3 X4) -> False) -> (r1_xxreal_0 np__1 k6_numbers -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X6 X2 X3 X4 X5 X1, (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (m2_subset_1 (esk22_4 X1 X2 X3 X4) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X6 X2 X4 X3 X1, (r5_cqc_the3 X1 X2 (esk22_4 X1 X2 X3 X4) -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X1 X4 X3 X2, ((k1_funct_1 X4 (esk21_4 X1 X2 X3 X4)) = (esk22_4 X1 X2 X3 X4) -> False) -> (r1_xxreal_0 k6_numbers X3 -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X1 X4 X3 X2, ((k1_funct_1 X4 (esk21_4 X1 X2 X3 X4)) = (esk22_4 X1 X2 X3 X4) -> False) -> (r1_xxreal_0 np__1 k6_numbers -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X6 X2 X4 X3 X1, (r5_cqc_the3 X1 X2 (esk22_4 X1 X2 X3 X4) -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X2 X4 X5 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (m2_subset_1 (esk22_4 X1 X2 X3 X4) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X2 X3 X4 X5, (r1_xxreal_0 np__1 k6_numbers -> False) -> (m2_subset_1 (esk22_4 X1 X2 X3 X4) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X2 X4 X5 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (m2_subset_1 (esk22_4 X1 X2 X3 X4) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X4 X2 X5 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (r5_cqc_the3 X1 X2 (esk22_4 X1 X2 X3 X4) -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X2 X3 X4 X5, (r1_xxreal_0 np__1 k6_numbers -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (m2_subset_1 (esk22_4 X1 X2 X3 X4) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X3 X4 X2 X5, (r1_xxreal_0 np__1 k6_numbers -> False) -> (r5_cqc_the3 X1 X2 (esk22_4 X1 X2 X3 X4) -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X4 X2 X5 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (r5_cqc_the3 X1 X2 (esk22_4 X1 X2 X3 X4) -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X3 X4 X2 X5, (r1_xxreal_0 np__1 k6_numbers -> False) -> (r5_cqc_the3 X1 X2 (esk22_4 X1 X2 X3 X4) -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X7 X6 X3 X4 X5 X2 X1, (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X7 = (k1_funct_1 X4 k6_numbers) -> X6 = (k1_funct_1 X4 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1)) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X7 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X7 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X7 X6 X2 X3 X4 X5 X1, (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> X7 = (k1_funct_1 X4 k6_numbers) -> X6 = (k1_funct_1 X4 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1)) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X7 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X7 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X1 X2 X5 X4 X6 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X6 = (k1_funct_1 X4 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1)) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X1 X2 X5 X4 X3 X6, (r1_xxreal_0 np__1 k6_numbers -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X6 = (k1_funct_1 X4 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1)) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X1 X5 X4 X2 X6 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> X6 = (k1_funct_1 X4 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1)) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X1 X5 X4 X3 X2 X6, (r1_xxreal_0 np__1 k6_numbers -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> X6 = (k1_funct_1 X4 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1)) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X1 X5 X4 X3 X2, (r6_cqc_the3 X2 X3 X4 -> False) -> (k3_finseq_1 X5) = X1 -> (k1_funct_1 X5 X1) = X3 -> (k1_funct_1 X5 np__1) = X4 -> m1_qc_lang1 X2 -> v1_relat_1 X5 -> v1_funct_1 X5 -> v1_finseq_1 X5 -> v6_qc_lang1 X3 X2 -> m1_subset_1 X1 k5_numbers -> r1_xxreal_0 np__1 X1 -> m2_subset_1 X4 (k9_qc_lang1 X2) (k3_cqc_lang X2) -> m2_subset_1 X3 (k9_qc_lang1 X2) (k3_cqc_lang X2) -> r1_xxreal_0 X1 (esk8_5 X2 X3 X4 X1 X5) -> False)
  -> (forall X6 X1 X3 X2 X5 X4, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> ((k1_funct_1 X4 (esk21_4 X1 X2 X3 X4)) = (esk22_4 X1 X2 X3 X4) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X6 X2 X4 X1 X3, (r1_xxreal_0 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) X3 -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X5 X6 X1 X4 X3 X2, (r1_xxreal_0 np__1 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X6 X2 X3 X4 X5 X1, (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (r1_xxreal_0 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) X3 -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X6 X2 X3 X4 X5 X1, (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (r1_xxreal_0 np__1 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X6 X1 X3 X2 X5 X4, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (m2_subset_1 (esk22_4 X1 X2 X3 X4) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X1 X4 X3 X2, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> ((k1_funct_1 X4 (esk21_4 X1 X2 X3 X4)) = (esk22_4 X1 X2 X3 X4) -> False) -> (r1_xxreal_0 k6_numbers X3 -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X5 X1 X4 X3 X2, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> ((k1_funct_1 X4 (esk21_4 X1 X2 X3 X4)) = (esk22_4 X1 X2 X3 X4) -> False) -> (r1_xxreal_0 np__1 k6_numbers -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X6 X1 X3 X2 X5 X4, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r5_cqc_the3 X1 X2 (esk22_4 X1 X2 X3 X4) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X4 X2 X5 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (r1_xxreal_0 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) X3 -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X3 X1 X4 X2 X5, (r1_xxreal_0 np__1 k6_numbers -> False) -> (r1_xxreal_0 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) X3 -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X4 X1 X5 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (r1_xxreal_0 np__1 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X4 X1 X5, (r1_xxreal_0 np__1 k6_numbers -> False) -> (r1_xxreal_0 np__1 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X1 X4 X2 X5 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (r1_xxreal_0 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) X3 -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X3 X1 X4 X2 X5, (r1_xxreal_0 np__1 k6_numbers -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (r1_xxreal_0 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) X3 -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X4 X1 X5 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (r1_xxreal_0 np__1 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X4 X1 X5, (r1_xxreal_0 np__1 k6_numbers -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (r1_xxreal_0 np__1 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X1 X2 X4 X5 X3, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 k6_numbers X3 -> False) -> (m2_subset_1 (esk22_4 X1 X2 X3 X4) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X2 X3 X4 X5, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 np__1 k6_numbers -> False) -> (m2_subset_1 (esk22_4 X1 X2 X3 X4) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X4 X2 X5 X3, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 k6_numbers X3 -> False) -> (r5_cqc_the3 X1 X2 (esk22_4 X1 X2 X3 X4) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X1 X3 X4 X2 X5, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 np__1 k6_numbers -> False) -> (r5_cqc_the3 X1 X2 (esk22_4 X1 X2 X3 X4) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> r1_xxreal_0 (esk21_4 X1 X2 X3 X4) X3 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r1_xxreal_0 np__1 (esk21_4 X1 X2 X3 X4) -> False)
  -> (forall X7 X6 X1 X3 X2 X5 X4, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> X7 = (k1_funct_1 X4 k6_numbers) -> X6 = (k1_funct_1 X4 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1)) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X7 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X7 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X5 X6 X1 X4 X3 X2, (m2_subset_1 (esk21_4 X1 X2 X3 X4) k1_numbers k5_numbers -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X6 X2 X3 X4 X5 X1, (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (m2_subset_1 (esk21_4 X1 X2 X3 X4) k1_numbers k5_numbers -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X6 X1 X3 X2 X5 X4, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 k6_numbers X3 -> False) -> X6 = (k1_funct_1 X4 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1)) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X6 X1 X3 X2 X5 X4, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 np__1 k6_numbers -> False) -> X6 = (k1_funct_1 X4 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1)) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X4 X1 X5 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (m2_subset_1 (esk21_4 X1 X2 X3 X4) k1_numbers k5_numbers -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X4 X1 X5, (r1_xxreal_0 np__1 k6_numbers -> False) -> (m2_subset_1 (esk21_4 X1 X2 X3 X4) k1_numbers k5_numbers -> False) -> (m2_subset_1 (esk23_5 X1 X2 X3 X4 X5) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X4 X1 X5 X3, (r1_xxreal_0 k6_numbers X3 -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (m2_subset_1 (esk21_4 X1 X2 X3 X4) k1_numbers k5_numbers -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X4 X1 X5, (r1_xxreal_0 np__1 k6_numbers -> False) -> (r5_cqc_the3 X1 X2 (esk23_5 X1 X2 X3 X4 X5) -> False) -> (m2_subset_1 (esk21_4 X1 X2 X3 X4) k1_numbers k5_numbers -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X4 X5 X3 X2 X1, (r6_cqc_the3 X1 X2 X3 -> False) -> (m1_subset_1 (esk8_5 X1 X2 X3 X4 X5) k5_numbers -> False) -> (k3_finseq_1 X5) = X4 -> (k1_funct_1 X5 X4) = X2 -> (k1_funct_1 X5 np__1) = X3 -> m1_qc_lang1 X1 -> v1_relat_1 X5 -> v1_funct_1 X5 -> v1_finseq_1 X5 -> v6_qc_lang1 X2 X1 -> m1_subset_1 X4 k5_numbers -> r1_xxreal_0 np__1 X4 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X4 X5 X3 X2 X1, (r6_cqc_the3 X1 X2 X3 -> False) -> (r1_xxreal_0 np__1 (esk8_5 X1 X2 X3 X4 X5) -> False) -> (k3_finseq_1 X5) = X4 -> (k1_funct_1 X5 X4) = X2 -> (k1_funct_1 X5 np__1) = X3 -> m1_qc_lang1 X1 -> v1_relat_1 X5 -> v1_funct_1 X5 -> v1_finseq_1 X5 -> v6_qc_lang1 X2 X1 -> m1_subset_1 X4 k5_numbers -> r1_xxreal_0 np__1 X4 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X6 X1 X3 X2 X5 X4, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) X3 -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X6 X1 X3 X2 X5 X4, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 np__1 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X1 X4 X2 X5 X3, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 k6_numbers X3 -> False) -> (r1_xxreal_0 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) X3 -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X3 X1 X4 X2 X5, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 np__1 k6_numbers -> False) -> (r1_xxreal_0 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) X3 -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X4 X1 X5 X3, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 k6_numbers X3 -> False) -> (r1_xxreal_0 np__1 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X4 X1 X5, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 np__1 k6_numbers -> False) -> (r1_xxreal_0 np__1 (k2_nat_1 (esk21_4 X1 X2 X3 X4) np__1) -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X6 X1 X3 X2 X5 X4, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (m2_subset_1 (esk21_4 X1 X2 X3 X4) k1_numbers k5_numbers -> False) -> X6 = (k1_funct_1 X4 k6_numbers) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> r5_cqc_the3 X1 X2 X6 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X6 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X4 X1 X5 X3, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 k6_numbers X3 -> False) -> (m2_subset_1 (esk21_4 X1 X2 X3 X4) k1_numbers k5_numbers -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X4 X1 X5, ((esk23_5 X1 X2 X3 X4 X5) = (k1_funct_1 X4 X5) -> False) -> (r1_xxreal_0 np__1 k6_numbers -> False) -> (m2_subset_1 (esk21_4 X1 X2 X3 X4) k1_numbers k5_numbers -> False) -> m1_qc_lang1 X1 -> v1_relat_1 X4 -> v1_funct_1 X4 -> v1_finseq_1 X4 -> r1_xxreal_0 X5 X3 -> m1_subset_1 X3 k5_numbers -> r1_xxreal_0 np__1 X5 -> m2_subset_1 X5 k1_numbers k5_numbers -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X4 X2 X3 X1, ((k11_cqc_lang X1 (esk6_4 X1 X2 X3 X4) (esk7_4 X1 X2 X3 X4)) = (k1_funct_1 (esk5_3 X1 X2 X3) (k2_nat_1 X4 np__1)) -> False) -> (r1_xxreal_0 (esk4_3 X1 X2 X3) X4 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X4 k5_numbers -> r1_xxreal_0 np__1 X4 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X4 X2 X3 X1, (r1_xxreal_0 (esk4_3 X1 X2 X3) X4 -> False) -> (m2_subset_1 (esk7_4 X1 X2 X3 X4) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X4 k5_numbers -> r1_xxreal_0 np__1 X4 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X4 X2 X3 X1, (r1_xxreal_0 (esk4_3 X1 X2 X3) X4 -> False) -> (m2_subset_1 (esk6_4 X1 X2 X3 X4) (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X4 k5_numbers -> r1_xxreal_0 np__1 X4 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X4 X2 X3 X1, ((k1_funct_1 (esk5_3 X1 X2 X3) X4) = (esk7_4 X1 X2 X3 X4) -> False) -> (r1_xxreal_0 (esk4_3 X1 X2 X3) X4 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X4 k5_numbers -> r1_xxreal_0 np__1 X4 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X3 X4 X2 X1, (r5_cqc_the3 X1 X2 X4 -> False) -> m1_qc_lang1 X1 -> r5_cqc_the3 X1 X3 X4 -> r5_cqc_the3 X1 X2 X3 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, ((k1_funct_1 (esk5_3 X1 X2 X3) (esk4_3 X1 X2 X3)) = X2 -> False) -> m1_qc_lang1 X1 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, ((k3_finseq_1 (esk5_3 X1 X2 X3)) = (esk4_3 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, ((k1_funct_1 (esk5_3 X1 X2 X3) np__1) = X3 -> False) -> m1_qc_lang1 X1 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (esk4_3 X1 X2 X3) k5_numbers -> False) -> m1_qc_lang1 X1 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (r1_xxreal_0 np__1 (esk4_3 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v1_finseq_1 (esk5_3 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (esk5_3 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (esk5_3 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> r6_cqc_the3 X1 X2 X3 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (r5_cqc_the3 X1 (k11_cqc_lang X1 X3 X2) X2 -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X3 X1 X2, (v6_qc_lang1 X1 X2 -> False) -> m1_qc_lang1 X2 -> r6_cqc_the3 X2 X1 X3 -> m2_subset_1 X3 (k9_qc_lang1 X2) (k3_cqc_lang X2) -> m2_subset_1 X1 (k9_qc_lang1 X2) (k3_cqc_lang X2) -> False)
  -> (forall X2 X3 X1, (m2_subset_1 (k11_cqc_lang X1 X2 X3) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (r5_cqc_the3 X1 X3 X2 -> False) -> m1_qc_lang1 X1 -> r5_cqc_the3 X1 X2 X3 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k15_qc_lang1 X1 X2 X3) (k9_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m1_subset_1 X2 (k3_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, ((k11_cqc_lang X1 X2 X3) = (k15_qc_lang1 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_qc_lang1 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (r5_cqc_the3 X1 X2 X2 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk11_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m2_subset_1 (k2_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, (m2_subset_1 (k1_nat_1 X1 X2) k1_numbers k5_numbers -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, v7_ordinal1 X2 -> v7_ordinal1 X1 -> r1_xxreal_0 X1 X2 -> r1_xxreal_0 (k1_nat_1 X2 np__1) X1 -> False)
  -> (forall X1, (m2_subset_1 (k3_finseq_1 X1) k1_numbers k5_numbers -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_finseq_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 (k1_nat_1 X1 np__1) X2 -> False) -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, ((k1_nat_1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X2 X1, ((k2_nat_1 X1 X2) = (k2_nat_1 X2 X1) -> False) -> v7_ordinal1 X2 -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1 X2, ((k1_nat_1 X1 X2) = (k1_nat_1 X2 X1) -> False) -> v7_ordinal1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (k3_qc_lang1 X1) (k1_zfmisc_1 (k2_qc_lang1 X1)) -> False) -> m1_qc_lang1 X1 -> False)
  -> (forall X1, (m1_subset_1 (k3_cqc_lang X1) (k1_zfmisc_1 (k9_qc_lang1 X1)) -> False) -> m1_qc_lang1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_membered X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v4_membered X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v3_membered X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v2_membered X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_membered X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_membered X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (r1_xxreal_0 X2 X1 -> False) -> (r1_xxreal_0 X1 X2 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k3_finseq_1 (k3_finseq_1 X1)) = (k3_finseq_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_finseq_1 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 X2 -> False) -> v6_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_int_1 X2 -> False) -> v5_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_rat_1 X2 -> False) -> v4_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xreal_0 X2 -> False) -> v3_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xxreal_0 X2 -> False) -> v2_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v1_xcmplx_0 X2 -> False) -> v1_membered X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k1_numbers) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 k5_numbers) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k3_finseq_1 X1) = (k1_card_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_finseq_1 X1 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, m1_qc_lang1 X1 -> v1_xboole_0 (k3_cqc_lang X1) -> False)
  -> (forall X1, m1_qc_lang1 X1 -> v1_xboole_0 (k9_qc_lang1 X1) -> False)
  -> (forall X1, (X1 = k6_numbers -> False) -> (r1_xxreal_0 np__1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk14_1 X1) -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_membered X1 -> False) -> v6_membered X1 -> False)
  -> (forall X1, (v4_membered X1 -> False) -> v5_membered X1 -> False)
  -> (forall X1, (v3_membered X1 -> False) -> v4_membered X1 -> False)
  -> (forall X1, (v2_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v1_membered X1 -> False) -> v3_membered X1 -> False)
  -> (forall X1, (v6_membered X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r5_cqc_the3 esk1_0 esk2_0 esk3_0 -> False)
  -> (forall X1, v1_subset_1 (esk19_1 X1) X1 -> False)
  -> (r1_xxreal_0 np__1 np__0 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk13_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> ((m2_subset_1 esk3_0 (k9_qc_lang1 esk1_0) (k3_cqc_lang esk1_0) -> False) -> False)
  -> ((m2_subset_1 esk2_0 (k9_qc_lang1 esk1_0) (k3_cqc_lang esk1_0) -> False) -> False)
  -> ((r6_cqc_the3 esk1_0 esk2_0 esk3_0 -> False) -> False)
  -> ((m2_subset_1 np__0 k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, ((k1_card_1 (k1_card_1 X1)) = (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__0 -> False) -> False)
  -> ((r1_xxreal_0 np__0 np__1 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((m1_subset_1 np__0 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk17_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v2_relat_1 esk16_0 -> False) -> False)
  -> ((v7_membered esk18_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v6_membered esk18_0 -> False) -> False)
  -> ((v6_membered esk15_0 -> False) -> False)
  -> ((v6_membered esk12_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> ((m1_qc_lang1 esk9_0 -> False) -> False)
  -> ((m1_qc_lang1 esk1_0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
