(** $I sig/MizarPreamble.mgs **)

Theorem t41_procal_1:
 forall k6_cqc_lang:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall esk6_1:set -> set,
 forall esk5_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall k2_qc_lang2:set -> set -> set -> set,
 forall k3_qc_lang2:set -> set -> set -> set,
 forall k14_qc_lang1:set -> set -> set -> set,
 forall k13_qc_lang1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k8_cqc_lang:set -> set -> set -> set,
 forall k9_cqc_lang:set -> set -> set -> set,
 forall k7_cqc_lang:set -> set -> set -> set,
 forall k4_cqc_the1:set -> set,
 forall k9_qc_lang1:set -> set,
 forall k3_cqc_lang:set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall m1_qc_lang1:set -> prop,
     (forall X4 X3 X2 X1, (r2_hidden (k8_cqc_lang X1 (k7_cqc_lang X1 (k9_cqc_lang X1 X2 X3) (k9_cqc_lang X1 X4 X3)) (k9_cqc_lang X1 (k7_cqc_lang X1 X2 X4) X3)) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (r2_hidden (k8_cqc_lang X1 (k7_cqc_lang X1 (k6_cqc_lang X1 X2) (k6_cqc_lang X1 X3)) (k6_cqc_lang X1 (k9_cqc_lang X1 X2 X3))) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (r2_hidden (k8_cqc_lang X1 (k6_cqc_lang X1 (k7_cqc_lang X1 X2 X3)) (k9_cqc_lang X1 (k6_cqc_lang X1 X2) (k6_cqc_lang X1 X3))) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden (k8_cqc_lang X1 (k7_cqc_lang X1 X4 X2) (k7_cqc_lang X1 X4 X3)) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r2_hidden (k8_cqc_lang X1 X2 X3) (k4_cqc_the1 X1) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden (k8_cqc_lang X1 (k9_cqc_lang X1 X2 X4) (k9_cqc_lang X1 X3 X4)) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r2_hidden (k8_cqc_lang X1 X2 X3) (k4_cqc_the1 X1) -> False)
  -> (forall X4 X2 X3 X1, (r2_hidden (k8_cqc_lang X1 (k9_cqc_lang X1 X4 X2) (k9_cqc_lang X1 X4 X3)) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r2_hidden (k8_cqc_lang X1 X2 X3) (k4_cqc_the1 X1) -> False)
  -> (forall X2 X3 X1, (r2_hidden (k8_cqc_lang X1 (k8_cqc_lang X1 (k6_cqc_lang X1 X2) X3) (k8_cqc_lang X1 (k6_cqc_lang X1 X3) X2)) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X3 X2 X4 X1, (r2_hidden (k8_cqc_lang X1 X2 X4) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X4 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r2_hidden (k8_cqc_lang X1 X3 X4) (k4_cqc_the1 X1) -> r2_hidden (k8_cqc_lang X1 X2 X3) (k4_cqc_the1 X1) -> False)
  -> (forall X3 X2 X1, (r2_hidden (k8_cqc_lang X1 X3 X2) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r2_hidden (k8_cqc_lang X1 (k6_cqc_lang X1 X2) (k6_cqc_lang X1 X3)) (k4_cqc_the1 X1) -> False)
  -> (forall X3 X2 X1, (r2_hidden (k8_cqc_lang X1 (k6_cqc_lang X1 X3) (k6_cqc_lang X1 X2)) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r2_hidden (k8_cqc_lang X1 X2 X3) (k4_cqc_the1 X1) -> False)
  -> (forall X2 X3 X1, (r2_hidden X3 (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> r2_hidden X2 (k4_cqc_the1 X1) -> m2_subset_1 X3 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> r2_hidden (k8_cqc_lang X1 X2 X3) (k4_cqc_the1 X1) -> False)
  -> (forall X2 X1, (r2_hidden (k8_cqc_lang X1 X2 (k6_cqc_lang X1 (k6_cqc_lang X1 X2))) (k4_cqc_the1 X1) -> False) -> m1_qc_lang1 X1 -> m2_subset_1 X2 (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, ((k13_qc_lang1 X1 (k14_qc_lang1 X1 (k13_qc_lang1 X1 X2) (k13_qc_lang1 X1 X3))) = (k3_qc_lang2 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m1_subset_1 X2 (k9_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (m2_subset_1 (k8_cqc_lang X1 X2 X3) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (m2_subset_1 (k7_cqc_lang X1 X2 X3) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (m2_subset_1 (k9_cqc_lang X1 X2 X3) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k2_qc_lang2 X1 X2 X3) (k9_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m1_subset_1 X2 (k9_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k14_qc_lang1 X1 X2 X3) (k9_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m1_subset_1 X2 (k9_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k3_qc_lang2 X1 X2 X3) (k9_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k9_qc_lang1 X1) -> m1_subset_1 X2 (k9_qc_lang1 X1) -> False)
  -> (forall X2 X3 X1, ((k2_qc_lang2 X1 X2 X3) = (k8_cqc_lang X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, ((k7_cqc_lang X1 X2 X3) = (k14_qc_lang1 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X2 X3 X1, ((k9_cqc_lang X1 X2 X3) = (k3_qc_lang2 X1 X2 X3) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X3 (k3_cqc_lang X1) -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m2_subset_1 (k6_cqc_lang X1 X2) (k9_qc_lang1 X1) (k3_cqc_lang X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk7_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (m1_subset_1 (k13_qc_lang1 X1 X2) (k9_qc_lang1 X1) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 (k9_qc_lang1 X1) -> False)
  -> (forall X2 X1, ((k13_qc_lang1 X1 X2) = (k6_cqc_lang X1 X2) -> False) -> m1_qc_lang1 X1 -> m1_subset_1 X2 (k3_cqc_lang X1) -> False)
  -> (forall X1, (m1_subset_1 (k4_cqc_the1 X1) (k1_zfmisc_1 (k3_cqc_lang X1)) -> False) -> m1_qc_lang1 X1 -> False)
  -> (forall X1, (m1_subset_1 (k3_cqc_lang X1) (k1_zfmisc_1 (k9_qc_lang1 X1)) -> False) -> m1_qc_lang1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1, m1_qc_lang1 X1 -> v1_xboole_0 (k3_cqc_lang X1) -> False)
  -> (forall X1, m1_qc_lang1 X1 -> v1_xboole_0 (k9_qc_lang1 X1) -> False)
  -> (r2_hidden (k8_cqc_lang esk1_0 (k7_cqc_lang esk1_0 (k9_cqc_lang esk1_0 esk2_0 esk3_0) esk4_0) (k9_cqc_lang esk1_0 (k7_cqc_lang esk1_0 esk2_0 esk4_0) (k7_cqc_lang esk1_0 esk3_0 esk4_0))) (k4_cqc_the1 esk1_0) -> False)
  -> ((m2_subset_1 esk4_0 (k9_qc_lang1 esk1_0) (k3_cqc_lang esk1_0) -> False) -> False)
  -> ((m2_subset_1 esk3_0 (k9_qc_lang1 esk1_0) (k3_cqc_lang esk1_0) -> False) -> False)
  -> ((m2_subset_1 esk2_0 (k9_qc_lang1 esk1_0) (k3_cqc_lang esk1_0) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> ((m1_qc_lang1 esk5_0 -> False) -> False)
  -> ((m1_qc_lang1 esk1_0 -> False) -> False)
  -> False.
Admitted.
