(** $I sig/MizarPreamble.mgs **)

Theorem t13_arytm_3:
 forall k11_ordinal2:set -> set -> set,
 forall k1_xboole_0:set,
 forall r2_hidden:set -> set -> prop,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v6_ordinal1:set -> prop,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk9_0:set,
 forall esk5_1:set -> set,
 forall esk7_0:set,
 forall esk6_0:set,
 forall esk10_0:set,
 forall esk8_0:set,
 forall esk11_0:set,
 forall v5_ordinal1:set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk3_2:set -> set -> set,
 forall k6_ordinal3:set -> set -> set,
 forall k9_ordinal3:set -> set -> set,
 forall v3_ordinal1:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall r2_arytm_3:set -> set -> prop,
 forall esk4_3:set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k4_ordinal1:set,
 forall k2_arytm_3:set -> set -> set,
     (forall X2 X1 X3, (X1 = (k2_arytm_3 X2 X3) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> r2_arytm_3 X3 X1 -> r2_arytm_3 X2 X1 -> m1_subset_1 X1 k4_ordinal1 -> r2_arytm_3 X1 (esk4_3 X2 X3 X1) -> False)
  -> (forall X1 X3 X2, (X3 = (k2_arytm_3 X1 X2) -> False) -> (r2_arytm_3 X1 (esk4_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X2 X3 -> r2_arytm_3 X1 X3 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_arytm_3 X2 X1) -> False) -> (r2_arytm_3 X1 (esk4_3 X2 X1 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X2 X3 -> r2_arytm_3 X1 X3 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_arytm_3 X1 X2) -> False) -> (v7_ordinal1 (esk4_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X2 X3 -> r2_arytm_3 X1 X3 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_arytm_3 X1 X2) -> False) -> (v3_ordinal1 (esk4_3 X1 X2 X3) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X2 X3 -> r2_arytm_3 X1 X3 -> m1_subset_1 X3 k4_ordinal1 -> False)
  -> (forall X3 X2 X4 X1, (r2_arytm_3 X4 X1 -> False) -> X4 = (k2_arytm_3 X2 X3) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X3 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X3 X1 -> r2_arytm_3 X2 X1 -> m1_subset_1 X4 k4_ordinal1 -> False)
  -> (forall X1 X2, (r2_arytm_3 X2 X1 -> False) -> (k9_ordinal3 X2 (k6_ordinal3 X1 X2)) = X1 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2 X3, ((k11_ordinal2 (k11_ordinal2 X1 X2) X3) = (k11_ordinal2 X1 (k11_ordinal2 X2 X3)) -> False) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (r2_arytm_3 (k2_arytm_3 X1 X2) (k9_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 (k6_ordinal3 X2 X1)) = X2 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> r2_arytm_3 X1 X2 -> False)
  -> (forall X3 X1 X2, (r2_arytm_3 X1 X2 -> False) -> X2 = (k2_arytm_3 X1 X3) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v7_ordinal1 X3 -> v7_ordinal1 X1 -> m1_subset_1 X2 k4_ordinal1 -> False)
  -> (forall X3 X1 X2, (r2_arytm_3 X1 X2 -> False) -> X2 = (k2_arytm_3 X3 X1) -> v3_ordinal1 X3 -> v3_ordinal1 X1 -> v7_ordinal1 X3 -> v7_ordinal1 X1 -> m1_subset_1 X2 k4_ordinal1 -> False)
  -> (forall X1 X2, ((k11_ordinal2 X2 (esk3_2 X2 X1)) = X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_arytm_3 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> (X2 = k1_xboole_0 -> False) -> (k11_ordinal2 X1 X2) = (k11_ordinal2 X3 X2) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (m1_subset_1 (k2_arytm_3 X1 X2) k4_ordinal1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (esk3_2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> r2_arytm_3 X1 X2 -> False)
  -> (forall X1 X3 X2, (r2_arytm_3 X3 X2 -> False) -> X2 = (k11_ordinal2 X3 X1) -> v3_ordinal1 X3 -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v7_ordinal1 (k6_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k6_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 (k9_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k2_arytm_3 X1 X2) = (k2_arytm_3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X1 X2, ((k9_ordinal3 X1 X2) = (k9_ordinal3 X2 X1) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> v7_ordinal1 X2 -> v7_ordinal1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k11_ordinal2 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X2 X1, (v3_ordinal1 (k6_ordinal3 X1 X2) -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_arytm_3 X1 X1 -> False) -> v3_ordinal1 X2 -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> m1_subset_1 X1 k4_ordinal1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_arytm_3 (k6_ordinal3 (k9_ordinal3 esk2_0 esk1_0) (k2_arytm_3 esk2_0 esk1_0)) esk2_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk9_0 -> False)
  -> (v1_xboole_0 esk8_0 -> False)
  -> (v1_xboole_0 k4_ordinal1 -> False)
  -> (k1_xboole_0 = esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk5_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k1_xboole_0 k4_ordinal1 -> False) -> False)
  -> ((v1_xboole_0 esk7_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v2_ordinal1 esk8_0 -> False) -> False)
  -> ((v1_ordinal1 esk8_0 -> False) -> False)
  -> ((v7_ordinal1 esk11_0 -> False) -> False)
  -> ((v7_ordinal1 esk10_0 -> False) -> False)
  -> ((v7_ordinal1 esk2_0 -> False) -> False)
  -> ((v7_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 esk8_0 -> False) -> False)
  -> ((v3_ordinal1 esk6_0 -> False) -> False)
  -> ((v3_ordinal1 esk2_0 -> False) -> False)
  -> ((v3_ordinal1 esk1_0 -> False) -> False)
  -> ((v3_ordinal1 k4_ordinal1 -> False) -> False)
  -> False.
Admitted.
