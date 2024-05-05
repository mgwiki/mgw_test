(** $I sig/MizarPreamble.mgs **)

Theorem t61_cqc_the2:
 forall k7_cqc_lang:set -> set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k3_cqc_lang:set -> set,
 forall k9_qc_lang1:set -> set,
 forall k3_qc_lang1:set -> set,
 forall k2_qc_lang1:set -> set,
 forall m1_qc_lang1:set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k2_qc_lang2:set -> set -> set -> set,
 forall k5_qc_lang2:set -> set -> set -> set,
 forall k13_qc_lang1:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall v5_ordinal1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall esk15_0:set,
 forall esk11_0:set,
 forall esk6_1:set -> set,
 forall esk14_0:set,
 forall esk10_0:set,
 forall esk13_0:set,
 forall esk8_0:set,
 forall esk5_0:set,
 forall esk9_0:set,
 forall esk12_0:set,
 forall k1_xboole_0:set,
 forall v1_xcmplx_0:set -> prop,
 forall v1_xxreal_0:set -> prop,
 forall v1_xreal_0:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall k14_qc_lang1:set -> set -> set -> set,
 forall k15_qc_lang1:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k24_qc_lang1:set -> set -> set,
 forall k6_cqc_lang:set -> set -> set,
 forall v2_cqc_the1:set -> set -> prop,
 forall k8_cqc_lang:set -> set -> set -> set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall k12_cqc_lang:set -> set -> set -> set,
 forall k11_cqc_lang:set -> set -> set -> set,
 forall esk1_0:set,
     (v2_cqc_the1 (k8_cqc_lang esk1_0 (k12_cqc_lang esk1_0 esk4_0 (k8_cqc_lang esk1_0 esk2_0 esk3_0)) (k8_cqc_lang esk1_0 (k11_cqc_lang esk1_0 esk4_0 esk2_0) (k12_cqc_lang esk1_0 esk4_0 esk3_0))) esk1_0 -> v2_cqc_the1 (k8_cqc_lang esk1_0 (k8_cqc_lang esk1_0 (k11_cqc_lang esk1_0 esk4_0 esk2_0) (k12_cqc_lang esk1_0 esk4_0 esk3_0)) (k12_cqc_lang esk1_0 esk4_0 (k8_cqc_lang esk1_0 esk2_0 esk3_0))) esk1_0 -> False)
  -> (forall X4 X3 X2 X1, (v2_cqc_the1 (k8_cqc_lang X1 (k7_cqc_lang X1 (k11_cqc_lang X1 X2 X3) (k11_cqc_lang X1 X2 X4)) (k11_cqc_lang X1 X2 (k7_cqc_lang X1 X3 X4))) X1 -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> False)
  -> (forall X4 X3 X2 X1, (v2_cqc_the1 (k8_cqc_lang X1 (k11_cqc_lang X1 X2 (k7_cqc_lang X1 X3 X4)) (k7_cqc_lang X1 (k11_cqc_lang X1 X2 X3) (k11_cqc_lang X1 X2 X4))) X1 -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> False)
  -> (forall X4 X3 X2 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 X2 (k8_cqc_lang X1 X3 X4)) (k8_cqc_lang X1 (k8_cqc_lang X1 X2 X3) (k8_cqc_lang X1 X2 X4))) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X4 (k3_cqc_lang X1) -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X4 X3 X2 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 X4 (k8_cqc_lang X1 X3 X2)) (k8_cqc_lang X1 X3 (k8_cqc_lang X1 X4 X2))) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X4 (k3_cqc_lang X1) -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X4 X3 X2 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 X2 X3) (k8_cqc_lang X1 (k8_cqc_lang X1 X3 X4) (k8_cqc_lang X1 X2 X4))) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X4 (k3_cqc_lang X1) -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X4 X3 X2 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 X2 X3) (k8_cqc_lang X1 (k8_cqc_lang X1 X4 X2) (k8_cqc_lang X1 X4 X3))) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X4 (k3_cqc_lang X1) -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X4 X5 X3 X2 X1, (v2_cqc_the1 (k8_cqc_lang X1 X2 (k8_cqc_lang X1 X3 X5)) X1 -> False) -> m1_qc_lang1 X1 -> v2_cqc_the1 (k8_cqc_lang X1 X4 X5) X1 -> m2_subset_1 X5 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> v2_cqc_the1 (k8_cqc_lang X1 X2 (k8_cqc_lang X1 X3 X4)) X1 -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k8_cqc_lang X1 (k12_cqc_lang X1 X2 (k6_cqc_lang X1 X3)) (k6_cqc_lang X1 (k11_cqc_lang X1 X2 X3))) X1 -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k8_cqc_lang X1 (k6_cqc_lang X1 (k11_cqc_lang X1 X2 X3)) (k12_cqc_lang X1 X2 (k6_cqc_lang X1 X3))) X1 -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> False)
  -> (forall X4 X3 X2 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 (k8_cqc_lang X1 X2 X3) X4) (k8_cqc_lang X1 X3 X4)) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X4 (k3_cqc_lang X1) -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X3 X2 X4 X1, (v2_cqc_the1 (k8_cqc_lang X1 (k7_cqc_lang X1 X4 X2) (k7_cqc_lang X1 X4 X3)) X1 -> False) -> m1_qc_lang1 X1 -> v2_cqc_the1 (k8_cqc_lang X1 X2 X3) X1 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X3 X2 X4 X1, (v2_cqc_the1 (k8_cqc_lang X1 (k8_cqc_lang X1 X3 X4) (k8_cqc_lang X1 X2 X4)) X1 -> False) -> m1_qc_lang1 X1 -> v2_cqc_the1 (k8_cqc_lang X1 X2 X3) X1 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 X2 (k8_cqc_lang X1 X2 X3)) (k8_cqc_lang X1 X2 X3)) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 (k6_cqc_lang X1 (k6_cqc_lang X1 X2)) X3) (k8_cqc_lang X1 X2 X3)) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 X2 (k6_cqc_lang X1 (k6_cqc_lang X1 X3))) (k8_cqc_lang X1 X2 X3)) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X4 (k24_qc_lang1 X1 X3) -> False) -> (v2_cqc_the1 (k8_cqc_lang X1 (k12_cqc_lang X1 X4 X2) X3) X1 -> False) -> m1_qc_lang1 X1 -> v2_cqc_the1 (k8_cqc_lang X1 X2 X3) X1 -> m2_subset_1 X4 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k2_qc_lang2 X1 X2 (k8_cqc_lang X1 (k8_cqc_lang X1 X2 X3) X3)) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 (k6_cqc_lang X1 X2) (k6_cqc_lang X1 X3)) (k8_cqc_lang X1 X3 X2)) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 (k6_cqc_lang X1 X2) X3) (k8_cqc_lang X1 (k6_cqc_lang X1 X3) X2)) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 X2 (k6_cqc_lang X1 X3)) (k8_cqc_lang X1 X3 (k6_cqc_lang X1 X2))) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k8_cqc_lang X1 X2 X3) (k8_cqc_lang X1 (k6_cqc_lang X1 X3) (k6_cqc_lang X1 X2))) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X3 X2 X4 X1, (v2_cqc_the1 (k8_cqc_lang X1 X2 X4) X1 -> False) -> m1_qc_lang1 X1 -> v2_cqc_the1 (k8_cqc_lang X1 X3 X4) X1 -> v2_cqc_the1 (k8_cqc_lang X1 X2 X3) X1 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X3 X2 X1, (v2_cqc_the1 (k8_cqc_lang X1 X3 X2) X1 -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> v2_cqc_the1 (k8_cqc_lang X1 (k6_cqc_lang X1 X2) (k6_cqc_lang X1 X3)) X1 -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k24_qc_lang1 X2 X3) -> False) -> m1_qc_lang1 X2 -> m1_subset_1 X3 (k9_qc_lang1 X2) -> m2_subset_1 X4 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> m2_subset_1 X1 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> r2_hidden X1 (k24_qc_lang1 X2 (k15_qc_lang1 X2 X4 X3)) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden X1 (k24_qc_lang1 X2 X3) -> False) -> m1_qc_lang1 X2 -> m1_subset_1 X3 (k9_qc_lang1 X2) -> m2_subset_1 X4 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> m2_subset_1 X1 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> r2_hidden X1 (k24_qc_lang1 X2 (k5_qc_lang2 X2 X4 X3)) -> False)
  -> (forall X3 X2 X4 X1, (r2_hidden X1 (k24_qc_lang1 X2 X4) -> False) -> (r2_hidden X1 (k24_qc_lang1 X2 X3) -> False) -> m1_qc_lang1 X2 -> m1_subset_1 X4 (k9_qc_lang1 X2) -> m1_subset_1 X3 (k9_qc_lang1 X2) -> m2_subset_1 X1 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> r2_hidden X1 (k24_qc_lang1 X2 (k2_qc_lang2 X2 X3 X4)) -> False)
  -> (forall X3 X4 X1 X2, X1 = X2 -> m1_qc_lang1 X3 -> m1_subset_1 X4 (k9_qc_lang1 X3) -> m2_subset_1 X2 (k2_qc_lang1 X3) (k3_qc_lang1 X3) -> m2_subset_1 X1 (k2_qc_lang1 X3) (k3_qc_lang1 X3) -> r2_hidden X1 (k24_qc_lang1 X3 (k15_qc_lang1 X3 X2 X4)) -> False)
  -> (forall X3 X4 X1 X2, X1 = X2 -> m1_qc_lang1 X3 -> m1_subset_1 X4 (k9_qc_lang1 X3) -> m2_subset_1 X2 (k2_qc_lang1 X3) (k3_qc_lang1 X3) -> m2_subset_1 X1 (k2_qc_lang1 X3) (k3_qc_lang1 X3) -> r2_hidden X1 (k24_qc_lang1 X3 (k5_qc_lang2 X3 X2 X4)) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k8_cqc_lang X1 (k6_cqc_lang X1 X3) (k6_cqc_lang X1 X2)) X1 -> False) -> m1_qc_lang1 X1 -> v2_cqc_the1 (k8_cqc_lang X1 X2 X3) X1 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> (r2_hidden X1 (k24_qc_lang1 X2 (k15_qc_lang1 X2 X4 X3)) -> False) -> m1_qc_lang1 X2 -> m1_subset_1 X3 (k9_qc_lang1 X2) -> r2_hidden X1 (k24_qc_lang1 X2 X3) -> m2_subset_1 X4 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> m2_subset_1 X1 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> (r2_hidden X1 (k24_qc_lang1 X2 (k5_qc_lang2 X2 X4 X3)) -> False) -> m1_qc_lang1 X2 -> m1_subset_1 X3 (k9_qc_lang1 X2) -> r2_hidden X1 (k24_qc_lang1 X2 X3) -> m2_subset_1 X4 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> m2_subset_1 X1 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k8_cqc_lang X1 (k11_cqc_lang X1 X3 X2) X2) X1 -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k8_cqc_lang X1 X2 (k12_cqc_lang X1 X3 X2)) X1 -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X4 X1 X3 X2, (r2_hidden X1 (k24_qc_lang1 X2 (k2_qc_lang2 X2 X3 X4)) -> False) -> m1_qc_lang1 X2 -> m1_subset_1 X4 (k9_qc_lang1 X2) -> m1_subset_1 X3 (k9_qc_lang1 X2) -> r2_hidden X1 (k24_qc_lang1 X2 X3) -> m2_subset_1 X1 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> False)
  -> (forall X4 X1 X3 X2, (r2_hidden X1 (k24_qc_lang1 X2 (k2_qc_lang2 X2 X4 X3)) -> False) -> m1_qc_lang1 X2 -> m1_subset_1 X4 (k9_qc_lang1 X2) -> m1_subset_1 X3 (k9_qc_lang1 X2) -> r2_hidden X1 (k24_qc_lang1 X2 X3) -> m2_subset_1 X1 (k2_qc_lang1 X2) (k3_qc_lang1 X2) -> False)
  -> (forall X2 X3 X1, (v2_cqc_the1 (k2_qc_lang2 X1 X2 (k8_cqc_lang X1 X3 X2)) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, ((k13_qc_lang1 X1 (k15_qc_lang1 X1 X2 (k13_qc_lang1 X1 X3))) = (k5_qc_lang2 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m2_subset_1 X2 (k2_qc_lang1 X1) (k3_qc_lang1 X1) -> False)
  -> (forall X2 X1, (v2_cqc_the1 (k2_qc_lang2 X1 (k6_cqc_lang X1 (k6_cqc_lang X1 X2)) X2) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X1, (v2_cqc_the1 (k2_qc_lang2 X1 X2 (k6_cqc_lang X1 (k6_cqc_lang X1 X2))) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, ((k13_qc_lang1 X1 (k14_qc_lang1 X1 X2 (k13_qc_lang1 X1 X3))) = (k2_qc_lang2 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m1_subset_1 X2 (k9_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (m2_subset_1 (k7_cqc_lang X1 X2 X3) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (m2_subset_1 (k11_cqc_lang X1 X2 X3) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (m2_subset_1 (k12_cqc_lang X1 X2 X3) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (m2_subset_1 (k8_cqc_lang X1 X2 X3) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k15_qc_lang1 X1 X2 X3) (k9_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m1_subset_1 X2 (k3_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k5_qc_lang2 X1 X2 X3) (k9_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m1_subset_1 X2 (k3_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k14_qc_lang1 X1 X2 X3) (k9_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m1_subset_1 X2 (k9_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k2_qc_lang2 X1 X2 X3) (k9_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m1_subset_1 X2 (k9_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, ((k14_qc_lang1 X1 X2 X3) = (k7_cqc_lang X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, ((k11_cqc_lang X1 X2 X3) = (k15_qc_lang1 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, ((k12_cqc_lang X1 X2 X3) = (k5_qc_lang2 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, ((k8_cqc_lang X1 X2 X3) = (k2_qc_lang2 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X1, (v2_cqc_the1 (k2_qc_lang2 X1 X2 X2) X1 -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m2_subset_1 (k6_cqc_lang X1 X2) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk7_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m1_subset_1 (k24_qc_lang1 X1 X2) (k1_zfmisc_1 (k3_qc_lang1 X1)) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 (k9_qc_lang1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k13_qc_lang1 X1 X2) (k9_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 (k9_qc_lang1 X1) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k13_qc_lang1 X1 X2) = (k6_cqc_lang X1 X2) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (m1_subset_1 (k3_qc_lang1 X1) (k1_zfmisc_1 (k2_qc_lang1 X1)) -> False) -> m1_qc_lang1 X1 -> False)
  -> (forall X1, (m1_subset_1 (k3_cqc_lang X1) (k1_zfmisc_1 (k9_qc_lang1 X1)) -> False) -> m1_qc_lang1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, m1_qc_lang1 X1 -> v1_xboole_0 (k3_cqc_lang X1) -> False)
  -> (forall X1, m1_qc_lang1 X1 -> v1_xboole_0 (k9_qc_lang1 X1) -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xxreal_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> v1_xreal_0 X1 -> False)
  -> (forall X1, (v1_xreal_0 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> ((m2_subset_1 esk4_0 (k2_qc_lang1 esk1_0) (k3_qc_lang1 esk1_0) -> False) -> False)
  -> ((m2_subset_1 esk3_0 (k9_qc_lang1 esk1_0) (k3_cqc_lang esk1_0) -> False) -> False)
  -> ((m2_subset_1 esk2_0 (k9_qc_lang1 esk1_0) (k3_cqc_lang esk1_0) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v1_xxreal_0 esk14_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_xreal_0 esk14_0 -> False) -> False)
  -> ((v1_xreal_0 esk10_0 -> False) -> False)
  -> ((v7_ordinal1 esk15_0 -> False) -> False)
  -> ((v7_ordinal1 esk13_0 -> False) -> False)
  -> ((v2_ordinal1 esk11_0 -> False) -> False)
  -> ((v1_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk11_0 -> False) -> False)
  -> ((v3_ordinal1 esk8_0 -> False) -> False)
  -> ((m1_qc_lang1 esk5_0 -> False) -> False)
  -> ((m1_qc_lang1 esk1_0 -> False) -> False)
  -> False.
Admitted.
