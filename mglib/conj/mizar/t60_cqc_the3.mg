(** $I sig/MizarPreamble.mgs **)

Theorem t60_cqc_the3:
 forall r1_xxreal_0:set -> set -> prop,
 forall k3_finseq_1:set -> set,
 forall esk14_4:set -> set -> set -> set -> set,
 forall a_3_0_cqc_the3:set -> set -> set -> set,
 forall m1_finseq_1:set -> set -> prop,
 forall esk13_3:set -> set -> set -> set,
 forall a_2_1_qc_lang1:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall k16_funcop_1:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk28_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk7_2:set -> set -> set,
 forall v4_membered:set -> prop,
 forall v2_membered:set -> prop,
 forall v6_membered:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall v1_rat_1:set -> prop,
 forall esk27_1:set -> set,
 forall v2_relat_1:set -> prop,
 forall v7_membered:set -> prop,
 forall k1_xboole_0:set,
 forall esk26_1:set -> set,
 forall esk24_0:set,
 forall esk18_0:set,
 forall esk23_1:set -> set,
 forall esk11_1:set -> set,
 forall v1_card_1:set -> prop,
 forall esk9_0:set,
 forall esk22_0:set,
 forall k4_ordinal1:set,
 forall esk2_0:set,
 forall esk10_1:set -> set,
 forall esk8_1:set -> set,
 forall esk25_2:set -> set -> set,
 forall esk19_2:set -> set -> set,
 forall esk17_0:set,
 forall esk21_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall v3_relat_1:set -> prop,
 forall k1_card_1:set -> set,
 forall esk20_1:set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall v1_int_1:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v1_membered:set -> prop,
 forall v3_membered:set -> prop,
 forall v5_membered:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v2_xxreal_0:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall esk16_2:set -> set -> set,
 forall k1_numbers:set,
 forall v1_finseq_1:set -> prop,
 forall k23_qc_lang1:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall k9_xtuple_0:set -> set,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall esk6_4:set -> set -> set -> set -> set,
 forall np__1:set,
 forall m1_qc_lang1:set -> prop,
 forall k5_numbers:set,
 forall m1_subset_1:set -> set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k5_qc_lang1:set -> set,
 forall a_5_0_cqc_the3:set -> set -> set -> set -> set -> set,
 forall m2_finseq_1:set -> set -> prop,
 forall k2_qc_lang1:set -> set,
 forall v3_card_1:set -> set -> prop,
 forall k3_qc_lang1:set -> set,
 forall esk15_6:set -> set -> set -> set -> set -> set -> set,
 forall k1_cqc_lang:set -> set -> set -> set,
 forall k2_cqc_lang:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
     (forall X6 X2 X3 X5 X4 X1, (r2_hidden (k1_funct_1 (k1_cqc_lang X1 X2 (k2_cqc_lang X1 X3 X4)) (esk15_6 X5 X1 X6 X2 X3 X4)) (k3_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> v3_card_1 X2 X6 -> m1_subset_1 X6 k5_numbers -> m2_finseq_1 X2 (k2_qc_lang1 X1) -> m2_subset_1 X4 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> m2_subset_1 X3 (k2_qc_lang1 X1) (k5_qc_lang1 X1) -> r2_hidden X5 (a_5_0_cqc_the3 X1 X6 X2 X3 X4) -> False)
  -> (forall X3 X4 X5 X1 X6 X2, (r1_xxreal_0 (esk15_6 X1 X2 X3 X4 X5 X6) (k3_finseq_1 (k1_cqc_lang X2 X4 (k2_cqc_lang X2 X5 X6))) -> False) -> m1_qc_lang1 X2 -> v3_card_1 X4 X3 -> m1_subset_1 X3 k5_numbers -> m2_finseq_1 X4 (k2_qc_lang1 X2) -> m2_subset_1 X6 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> m2_subset_1 X5 (k2_qc_lang1 X2) (k5_qc_lang1 X2) -> r2_hidden X1 (a_5_0_cqc_the3 X2 X3 X4 X5 X6) -> False)
  -> (forall X6 X3 X4 X1 X5 X2, ((k1_funct_1 (k1_cqc_lang X2 X3 (k2_cqc_lang X2 X4 X5)) (esk15_6 X1 X2 X6 X3 X4 X5)) = X1 -> False) -> m1_qc_lang1 X2 -> v3_card_1 X3 X6 -> m1_subset_1 X6 k5_numbers -> m2_finseq_1 X3 (k2_qc_lang1 X2) -> m2_subset_1 X5 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> m2_subset_1 X4 (k2_qc_lang1 X2) (k5_qc_lang1 X2) -> r2_hidden X1 (a_5_0_cqc_the3 X2 X6 X3 X4 X5) -> False)
  -> (forall X3 X4 X5 X1 X6 X2, (m1_subset_1 (esk15_6 X1 X2 X3 X4 X5 X6) k5_numbers -> False) -> m1_qc_lang1 X2 -> v3_card_1 X4 X3 -> m1_subset_1 X3 k5_numbers -> m2_finseq_1 X4 (k2_qc_lang1 X2) -> m2_subset_1 X6 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> m2_subset_1 X5 (k2_qc_lang1 X2) (k5_qc_lang1 X2) -> r2_hidden X1 (a_5_0_cqc_the3 X2 X3 X4 X5 X6) -> False)
  -> (forall X3 X4 X5 X1 X6 X2, (r1_xxreal_0 np__1 (esk15_6 X1 X2 X3 X4 X5 X6) -> False) -> m1_qc_lang1 X2 -> v3_card_1 X4 X3 -> m1_subset_1 X3 k5_numbers -> m2_finseq_1 X4 (k2_qc_lang1 X2) -> m2_subset_1 X6 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> m2_subset_1 X5 (k2_qc_lang1 X2) (k5_qc_lang1 X2) -> r2_hidden X1 (a_5_0_cqc_the3 X2 X3 X4 X5 X6) -> False)
  -> (forall X1 X7 X6 X5 X4 X3 X2, (r2_hidden X2 (a_5_0_cqc_the3 X3 X7 X4 X5 X6) -> False) -> X2 = (k1_funct_1 (k1_cqc_lang X3 X4 (k2_cqc_lang X3 X5 X6)) X1) -> m1_qc_lang1 X3 -> v3_card_1 X4 X7 -> m1_subset_1 X7 k5_numbers -> m1_subset_1 X1 k5_numbers -> r1_xxreal_0 np__1 X1 -> m2_finseq_1 X4 (k2_qc_lang1 X3) -> m2_subset_1 X6 (k2_qc_lang1 X3) (k3_qc_lang1 X3) -> m2_subset_1 X5 (k2_qc_lang1 X3) (k5_qc_lang1 X3) -> r1_xxreal_0 X1 (k3_finseq_1 (k1_cqc_lang X3 X4 (k2_cqc_lang X3 X5 X6))) -> r2_hidden (k1_funct_1 (k1_cqc_lang X3 X4 (k2_cqc_lang X3 X5 X6)) X1) (k3_qc_lang1 X3) -> False)
  -> (forall X2 X3 X1 X4, (X4 = (k1_cqc_lang X2 X1 X3) -> False) -> (k3_finseq_1 X1) = (k3_finseq_1 X4) -> (k1_funct_1 X4 (esk6_4 X2 X1 X3 X4)) = (k1_funct_1 X3 (k1_funct_1 X1 (esk6_4 X2 X1 X3 X4))) -> m1_qc_lang1 X2 -> v1_funct_1 X3 -> m2_finseq_1 X4 (k2_qc_lang1 X2) -> m2_finseq_1 X1 (k2_qc_lang1 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X2) (k2_qc_lang1 X2))) -> r2_hidden (k1_funct_1 X1 (esk6_4 X2 X1 X3 X4)) (k9_xtuple_0 X3) -> False)
  -> (forall X2 X4 X1 X3, (X1 = (k1_cqc_lang X2 X3 X4) -> False) -> (k3_finseq_1 X1) = (k3_finseq_1 X3) -> (k1_funct_1 X1 (esk6_4 X2 X3 X4 X1)) = (k1_funct_1 X3 (esk6_4 X2 X3 X4 X1)) -> (k1_funct_1 X1 (esk6_4 X2 X3 X4 X1)) = (k1_funct_1 X4 (k1_funct_1 X3 (esk6_4 X2 X3 X4 X1))) -> m1_qc_lang1 X2 -> v1_funct_1 X4 -> m2_finseq_1 X3 (k2_qc_lang1 X2) -> m2_finseq_1 X1 (k2_qc_lang1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X2) (k2_qc_lang1 X2))) -> False)
  -> (forall X2 X4 X1 X3, (X1 = (k1_cqc_lang X2 X3 X4) -> False) -> (r2_hidden (k1_funct_1 X3 (esk6_4 X2 X3 X4 X1)) (k9_xtuple_0 X4) -> False) -> (k3_finseq_1 X1) = (k3_finseq_1 X3) -> (k1_funct_1 X1 (esk6_4 X2 X3 X4 X1)) = (k1_funct_1 X3 (esk6_4 X2 X3 X4 X1)) -> m1_qc_lang1 X2 -> v1_funct_1 X4 -> m2_finseq_1 X3 (k2_qc_lang1 X2) -> m2_finseq_1 X1 (k2_qc_lang1 X2) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X2) (k2_qc_lang1 X2))) -> False)
  -> (forall X4 X1 X2 X3, (r2_hidden (k1_funct_1 X1 (esk14_4 X2 X3 X4 X1)) (k3_qc_lang1 X3) -> False) -> m1_qc_lang1 X3 -> v3_card_1 X1 X4 -> m1_subset_1 X4 k5_numbers -> m2_finseq_1 X1 (k2_qc_lang1 X3) -> r2_hidden X2 (a_3_0_cqc_the3 X3 X4 X1) -> False)
  -> (forall X1 X3 X2 X4, (X4 = (k1_cqc_lang X1 X2 X3) -> False) -> (r1_xxreal_0 (esk6_4 X1 X2 X3 X4) (k3_finseq_1 X2) -> False) -> (k3_finseq_1 X2) = (k3_finseq_1 X4) -> m1_qc_lang1 X1 -> v1_funct_1 X3 -> m2_finseq_1 X4 (k2_qc_lang1 X1) -> m2_finseq_1 X2 (k2_qc_lang1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X1) (k2_qc_lang1 X1))) -> False)
  -> (forall X1 X3 X2 X4, (X4 = (k1_cqc_lang X1 X2 X3) -> False) -> (m1_subset_1 (esk6_4 X1 X2 X3 X4) k5_numbers -> False) -> (k3_finseq_1 X2) = (k3_finseq_1 X4) -> m1_qc_lang1 X1 -> v1_funct_1 X3 -> m2_finseq_1 X4 (k2_qc_lang1 X1) -> m2_finseq_1 X2 (k2_qc_lang1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X1) (k2_qc_lang1 X1))) -> False)
  -> (forall X1 X3 X2 X4, (X4 = (k1_cqc_lang X1 X2 X3) -> False) -> (r1_xxreal_0 np__1 (esk6_4 X1 X2 X3 X4) -> False) -> (k3_finseq_1 X2) = (k3_finseq_1 X4) -> m1_qc_lang1 X1 -> v1_funct_1 X3 -> m2_finseq_1 X4 (k2_qc_lang1 X1) -> m2_finseq_1 X2 (k2_qc_lang1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X1) (k2_qc_lang1 X1))) -> False)
  -> (forall X3 X4 X1 X2, (r1_xxreal_0 (esk14_4 X1 X2 X3 X4) (k3_finseq_1 X4) -> False) -> m1_qc_lang1 X2 -> v3_card_1 X4 X3 -> m1_subset_1 X3 k5_numbers -> m2_finseq_1 X4 (k2_qc_lang1 X2) -> r2_hidden X1 (a_3_0_cqc_the3 X2 X3 X4) -> False)
  -> (forall X4 X2 X1 X3, ((k1_funct_1 X2 (esk14_4 X1 X3 X4 X2)) = X1 -> False) -> m1_qc_lang1 X3 -> v3_card_1 X2 X4 -> m1_subset_1 X4 k5_numbers -> m2_finseq_1 X2 (k2_qc_lang1 X3) -> r2_hidden X1 (a_3_0_cqc_the3 X3 X4 X2) -> False)
  -> (forall X3 X4 X1 X2, (m1_subset_1 (esk14_4 X1 X2 X3 X4) k5_numbers -> False) -> m1_qc_lang1 X2 -> v3_card_1 X4 X3 -> m1_subset_1 X3 k5_numbers -> m2_finseq_1 X4 (k2_qc_lang1 X2) -> r2_hidden X1 (a_3_0_cqc_the3 X2 X3 X4) -> False)
  -> (forall X3 X4 X1 X2, (r1_xxreal_0 np__1 (esk14_4 X1 X2 X3 X4) -> False) -> m1_qc_lang1 X2 -> v3_card_1 X4 X3 -> m1_subset_1 X3 k5_numbers -> m2_finseq_1 X4 (k2_qc_lang1 X2) -> r2_hidden X1 (a_3_0_cqc_the3 X2 X3 X4) -> False)
  -> (forall X4 X7 X6 X5 X2 X1 X3, ((k1_funct_1 X1 X2) = X3 -> False) -> ((k1_funct_1 X1 X2) = (k1_funct_1 X4 X2) -> False) -> X5 = (k2_cqc_lang X6 X3 X7) -> X4 = (k1_cqc_lang X6 X1 X5) -> m1_qc_lang1 X6 -> v1_funct_1 X5 -> m1_subset_1 X2 k5_numbers -> r1_xxreal_0 np__1 X2 -> m2_finseq_1 X4 (k2_qc_lang1 X6) -> m2_finseq_1 X1 (k2_qc_lang1 X6) -> r1_xxreal_0 X2 (k3_finseq_1 X1) -> m2_subset_1 X7 (k2_qc_lang1 X6) (k3_qc_lang1 X6) -> m2_subset_1 X3 (k2_qc_lang1 X6) (k5_qc_lang1 X6) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X6) (k2_qc_lang1 X6))) -> False)
  -> (forall X3 X1 X7 X6 X2 X4 X5, ((k1_funct_1 X4 X2) = X5 -> False) -> (k1_funct_1 X1 X2) = X3 -> X6 = (k2_cqc_lang X7 X3 X5) -> X4 = (k1_cqc_lang X7 X1 X6) -> m1_qc_lang1 X7 -> v1_funct_1 X6 -> m1_subset_1 X2 k5_numbers -> r1_xxreal_0 np__1 X2 -> m2_finseq_1 X4 (k2_qc_lang1 X7) -> m2_finseq_1 X1 (k2_qc_lang1 X7) -> r1_xxreal_0 X2 (k3_finseq_1 X1) -> m2_subset_1 X5 (k2_qc_lang1 X7) (k3_qc_lang1 X7) -> m2_subset_1 X3 (k2_qc_lang1 X7) (k5_qc_lang1 X7) -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X7) (k2_qc_lang1 X7))) -> False)
  -> (forall X5 X1 X3 X4 X2, ((k1_funct_1 X4 X2) = (k1_funct_1 X3 (k1_funct_1 X1 X2)) -> False) -> X4 = (k1_cqc_lang X5 X1 X3) -> m1_qc_lang1 X5 -> v1_funct_1 X3 -> m1_subset_1 X2 k5_numbers -> r1_xxreal_0 np__1 X2 -> m2_finseq_1 X4 (k2_qc_lang1 X5) -> m2_finseq_1 X1 (k2_qc_lang1 X5) -> r1_xxreal_0 X2 (k3_finseq_1 X1) -> r2_hidden (k1_funct_1 X1 X2) (k9_xtuple_0 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X5) (k2_qc_lang1 X5))) -> False)
  -> (forall X3 X5 X1 X2 X4, ((k1_funct_1 X1 X2) = (k1_funct_1 X4 X2) -> False) -> (r2_hidden (k1_funct_1 X1 X2) (k9_xtuple_0 X3) -> False) -> X4 = (k1_cqc_lang X5 X1 X3) -> m1_qc_lang1 X5 -> v1_funct_1 X3 -> m1_subset_1 X2 k5_numbers -> r1_xxreal_0 np__1 X2 -> m2_finseq_1 X4 (k2_qc_lang1 X5) -> m2_finseq_1 X1 (k2_qc_lang1 X5) -> r1_xxreal_0 X2 (k3_finseq_1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X5) (k2_qc_lang1 X5))) -> False)
  -> (forall X4 X3 X2 X1, (v3_card_1 (k1_cqc_lang X1 X3 X4) X2 -> False) -> m1_qc_lang1 X1 -> v1_funct_1 X4 -> v3_card_1 X3 X2 -> m1_subset_1 X2 k5_numbers -> m1_finseq_1 X3 (k2_qc_lang1 X1) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X1) (k2_qc_lang1 X1))) -> False)
  -> (forall X1 X3 X5 X4 X2, (r2_hidden X2 (a_3_0_cqc_the3 X4 X5 X3) -> False) -> X2 = (k1_funct_1 X3 X1) -> m1_qc_lang1 X4 -> v3_card_1 X3 X5 -> m1_subset_1 X5 k5_numbers -> m1_subset_1 X1 k5_numbers -> r1_xxreal_0 np__1 X1 -> m2_finseq_1 X3 (k2_qc_lang1 X4) -> r1_xxreal_0 X1 (k3_finseq_1 X3) -> r2_hidden (k1_funct_1 X3 X1) (k3_qc_lang1 X4) -> False)
  -> (forall X3 X4 X1 X2, ((k3_finseq_1 X1) = (k3_finseq_1 X2) -> False) -> X1 = (k1_cqc_lang X3 X2 X4) -> m1_qc_lang1 X3 -> v1_funct_1 X4 -> m2_finseq_1 X2 (k2_qc_lang1 X3) -> m2_finseq_1 X1 (k2_qc_lang1 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X3) (k2_qc_lang1 X3))) -> False)
  -> (forall X3 X2 X1, (m2_finseq_1 (k1_cqc_lang X1 X2 X3) (k2_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> v1_funct_1 X3 -> m1_finseq_1 X2 (k2_qc_lang1 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X1) (k2_qc_lang1 X1))) -> False)
  -> (forall X1 X2 X3, (r2_hidden (k1_funct_1 X1 (esk13_3 X2 X3 X1)) (k3_qc_lang1 X3) -> False) -> m1_qc_lang1 X3 -> m2_finseq_1 X1 (k2_qc_lang1 X3) -> r2_hidden X2 (a_2_1_qc_lang1 X3 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k2_cqc_lang X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 (k5_qc_lang1 X1) (k2_qc_lang1 X1))) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_qc_lang1 X1) -> m1_subset_1 X2 (k5_qc_lang1 X1) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X1 X4 X3 X2, (r2_hidden X2 (a_2_1_qc_lang1 X4 X3) -> False) -> X2 = (k1_funct_1 X3 X1) -> m1_qc_lang1 X4 -> m1_subset_1 X1 k5_numbers -> r1_xxreal_0 np__1 X1 -> m2_finseq_1 X3 (k2_qc_lang1 X4) -> r1_xxreal_0 X1 (k3_finseq_1 X3) -> r2_hidden (k1_funct_1 X3 X1) (k3_qc_lang1 X4) -> False)
  -> (forall X3 X1 X2, (r1_xxreal_0 (esk13_3 X1 X2 X3) (k3_finseq_1 X3) -> False) -> m1_qc_lang1 X2 -> m2_finseq_1 X3 (k2_qc_lang1 X2) -> r2_hidden X1 (a_2_1_qc_lang1 X2 X3) -> False)
  -> (forall X2 X1 X3, ((k1_funct_1 X2 (esk13_3 X1 X3 X2)) = X1 -> False) -> m1_qc_lang1 X3 -> m2_finseq_1 X2 (k2_qc_lang1 X3) -> r2_hidden X1 (a_2_1_qc_lang1 X3 X2) -> False)
  -> (forall X3 X1 X2, (m1_subset_1 (esk13_3 X1 X2 X3) k5_numbers -> False) -> m1_qc_lang1 X2 -> m2_finseq_1 X3 (k2_qc_lang1 X2) -> r2_hidden X1 (a_2_1_qc_lang1 X2 X3) -> False)
  -> (forall X3 X1 X2, (r1_xxreal_0 np__1 (esk13_3 X1 X2 X3) -> False) -> m1_qc_lang1 X2 -> m2_finseq_1 X3 (k2_qc_lang1 X2) -> r2_hidden X1 (a_2_1_qc_lang1 X2 X3) -> False)
  -> (forall X1 X2 X3, X2 = X3 -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> m2_subset_1 X2 (k2_qc_lang1 X1) (k5_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k2_cqc_lang X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_qc_lang1 X1) -> m1_subset_1 X2 (k5_qc_lang1 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X3 X1, ((k2_cqc_lang X1 X2 X3) = (k16_funcop_1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_qc_lang1 X1) -> m1_subset_1 X2 (k5_qc_lang1 X1) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk12_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk28_2 X3 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k23_qc_lang1 X1 X2) (k1_zfmisc_1 (k3_qc_lang1 X1)) -> False) -> m1_qc_lang1 X1 -> m1_finseq_1 X2 (k2_qc_lang1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 k5_numbers X2)) -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X1, (m2_subset_1 (k3_finseq_1 X1) k1_numbers k5_numbers -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_finseq_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk7_2 X1 X2) X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (m1_finseq_1 (esk16_2 X1 X2) (k2_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2, (v5_relat_1 (esk16_2 X1 X2) (k3_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2, (v5_relat_1 (esk16_2 X1 X2) (k2_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v3_card_1 (esk16_2 X1 X2) X2 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X2 X1, ((k23_qc_lang1 X1 X2) = (a_2_1_qc_lang1 X1 X2) -> False) -> m1_qc_lang1 X1 -> m2_finseq_1 X2 (k2_qc_lang1 X1) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) k5_numbers -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X2 X1, (r2_hidden (esk28_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r1_tarski X1 X2 -> r2_hidden X3 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finseq_1 (esk16_2 X1 X2) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2, (v1_funct_1 (esk16_2 X1 X2) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 k5_numbers -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X1 X2, (v2_xxreal_0 X2 -> False) -> v1_xreal_0 X2 -> v1_xreal_0 X1 -> v2_xxreal_0 X1 -> r1_xxreal_0 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (k3_qc_lang1 X1) (k1_zfmisc_1 (k2_qc_lang1 X1)) -> False) -> m1_qc_lang1 X1 -> False)
  -> (forall X1, (m1_subset_1 (k5_qc_lang1 X1) (k1_zfmisc_1 (k2_qc_lang1 X1)) -> False) -> m1_qc_lang1 X1 -> False)
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
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_finseq_1 X1 X2 -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (m2_finseq_1 X1 X2 -> False) -> m1_finseq_1 X1 X2 -> False)
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
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k1_card_1 X1) = (k3_finseq_1 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_finseq_1 X1 -> False)
  -> (forall X2 X1, (r1_xxreal_0 X1 X1 -> False) -> v1_xxreal_0 X2 -> v1_xxreal_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_relat_1 X1 -> v1_xboole_0 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_finseq_1 X1 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_finseq_1 X1 -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> m2_finseq_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> m1_finseq_1 X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v6_membered X1 -> False) -> m1_subset_1 X1 k5_numbers -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
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
  -> (r1_tarski (k23_qc_lang1 esk1_0 esk3_0) (k23_qc_lang1 esk1_0 (k1_cqc_lang esk1_0 esk3_0 (k2_cqc_lang esk1_0 esk4_0 esk5_0))) -> False)
  -> (forall X1, v1_subset_1 (esk26_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk24_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk19_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((m2_subset_1 esk5_0 (k2_qc_lang1 esk1_0) (k3_qc_lang1 esk1_0) -> False) -> False)
  -> ((m2_subset_1 esk4_0 (k2_qc_lang1 esk1_0) (k5_qc_lang1 esk1_0) -> False) -> False)
  -> ((m2_subset_1 np__1 k1_numbers k5_numbers -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_finseq_1 (esk8_1 X1) X1 -> False) -> False)
  -> (forall X1, (m2_finseq_1 (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) X1 -> False) -> False)
  -> ((m2_finseq_1 esk3_0 (k2_qc_lang1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, ((k1_card_1 (k1_card_1 X1)) = (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((r1_xxreal_0 np__1 np__1 -> False) -> False)
  -> ((v3_card_1 esk3_0 esk2_0 -> False) -> False)
  -> ((m1_subset_1 esk2_0 k5_numbers -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((m1_subset_1 np__1 k1_numbers -> False) -> False)
  -> ((m1_subset_1 np__1 k5_numbers -> False) -> False)
  -> (forall X1, (v1_card_1 (k1_card_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk23_1 X1) -> False) -> False)
  -> ((v2_xxreal_0 np__1 -> False) -> False)
  -> ((v2_relat_1 esk22_0 -> False) -> False)
  -> ((v7_membered esk24_0 -> False) -> False)
  -> ((v7_membered k4_ordinal1 -> False) -> False)
  -> ((v7_membered k1_numbers -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v3_membered k1_numbers -> False) -> False)
  -> ((v6_membered esk24_0 -> False) -> False)
  -> ((v6_membered esk21_0 -> False) -> False)
  -> ((v6_membered esk17_0 -> False) -> False)
  -> ((v6_membered k4_ordinal1 -> False) -> False)
  -> ((m1_qc_lang1 esk9_0 -> False) -> False)
  -> ((m1_qc_lang1 esk1_0 -> False) -> False)
  -> ((k4_ordinal1 = k5_numbers -> False) -> False)
  -> False.
Admitted.
