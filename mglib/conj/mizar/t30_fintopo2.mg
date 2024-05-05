(** $I sig/MizarPreamble.mgs **)

Theorem t30_fintopo2:
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall esk5_0:set,
 forall esk6_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk12_3:set -> set -> set -> set,
 forall esk28_3:set -> set -> set -> set,
 forall u1_fintopo2:set -> set,
 forall esk26_3:set -> set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall k4_xboole_0:set -> set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall esk22_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall esk25_1:set -> set,
 forall esk23_1:set -> set,
 forall esk21_1:set -> set,
 forall esk20_0:set,
 forall esk11_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk10_0:set,
 forall esk9_0:set,
 forall esk16_0:set,
 forall esk19_1:set -> set,
 forall esk14_2:set -> set -> set,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall esk15_1:set -> set,
 forall esk24_1:set -> set,
 forall esk17_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall v7_struct_0:set -> prop,
 forall esk29_2:set -> set -> set,
 forall k1_xboole_0:set,
 forall k3_xboole_0:set -> set -> set,
 forall esk27_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall k7_subset_1:set -> set -> set -> set,
 forall k3_subset_1:set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall a_2_2_fintopo2:set -> set -> set,
 forall l1_fintopo2:set -> prop,
 forall esk13_4:set -> set -> set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall k9_subset_1:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k6_fintopo2:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k9_fintopo2:set -> set -> set,
 forall u1_struct_0:set -> set,
 forall k4_subset_1:set -> set -> set -> set,
 forall esk1_0:set,
     (forall X3 X2 X1 X4 X5, ((k4_subset_1 (u1_struct_0 esk1_0) (k9_fintopo2 esk1_0 X4) (k9_fintopo2 esk1_0 X5)) = (k9_fintopo2 esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) X4 X5)) -> False) -> (r1_tarski (esk7_3 X1 X2 X3) (k9_subset_1 (u1_struct_0 esk1_0) X2 X3) -> False) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> r2_hidden X3 (k6_fintopo2 esk1_0 X1) -> r2_hidden X2 (k6_fintopo2 esk1_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2 X4 X5, ((k4_subset_1 (u1_struct_0 esk1_0) (k9_fintopo2 esk1_0 X4) (k9_fintopo2 esk1_0 X5)) = (k9_fintopo2 esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) X4 X5)) -> False) -> (r2_hidden (esk7_3 X1 X2 X3) (k6_fintopo2 esk1_0 X1) -> False) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> r2_hidden X3 (k6_fintopo2 esk1_0 X1) -> r2_hidden X2 (k6_fintopo2 esk1_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X3 X2 X1 X4 X5, ((k4_subset_1 (u1_struct_0 esk1_0) (k9_fintopo2 esk1_0 X4) (k9_fintopo2 esk1_0 X5)) = (k9_fintopo2 esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) X4 X5)) -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> r2_hidden X3 (k6_fintopo2 esk1_0 X1) -> r2_hidden X2 (k6_fintopo2 esk1_0 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False)
  -> (forall X1 X3 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X1 (a_2_2_fintopo2 X2 X3) -> False) -> (r2_hidden (esk13_4 X1 X2 X3 X4) (k6_fintopo2 X2 X4) -> False) -> X1 = X4 -> l1_fintopo2 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X1 (a_2_2_fintopo2 X2 X3) -> False) -> (m1_subset_1 (esk13_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> X1 = X4 -> l1_fintopo2 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X1 (a_2_2_fintopo2 X2 X3) -> False) -> (r1_xboole_0 (esk13_4 X1 X2 X3 X4) X3 -> False) -> X1 = X4 -> l1_fintopo2 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1, (k4_subset_1 (u1_struct_0 esk1_0) (k9_fintopo2 esk1_0 esk5_0) (k9_fintopo2 esk1_0 esk6_0)) = (k9_fintopo2 esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) esk5_0 esk6_0)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> r2_hidden X1 (k6_fintopo2 esk1_0 esk2_0) -> r1_tarski X1 (k9_subset_1 (u1_struct_0 esk1_0) esk3_0 esk4_0) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (k4_subset_1 (u1_struct_0 X1) (k9_fintopo2 X1 X2) (k9_fintopo2 X1 X3)) (k9_fintopo2 X1 (k4_subset_1 (u1_struct_0 X1) X2 X3)) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> l1_fintopo2 X2 -> r1_xboole_0 X1 X4 -> r2_hidden X3 (a_2_2_fintopo2 X2 X4) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (k6_fintopo2 X2 (esk12_3 X3 X2 X4)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> r2_hidden (esk28_3 X1 X2 X3) X3 -> r2_hidden (esk28_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X1, (X3 = (k2_xboole_0 X1 X2) -> False) -> r2_hidden (esk8_3 X1 X2 X3) X3 -> r2_hidden (esk8_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k2_xboole_0 X1 X2) -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X2 -> False) -> (r2_hidden (esk8_3 X1 X2 X3) X1 -> False) -> False)
  -> ((r2_hidden esk4_0 (k6_fintopo2 esk1_0 esk2_0) -> False) -> (k4_subset_1 (u1_struct_0 esk1_0) (k9_fintopo2 esk1_0 esk5_0) (k9_fintopo2 esk1_0 esk6_0)) = (k9_fintopo2 esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) esk5_0 esk6_0)) -> False)
  -> ((r2_hidden esk3_0 (k6_fintopo2 esk1_0 esk2_0) -> False) -> (k4_subset_1 (u1_struct_0 esk1_0) (k9_fintopo2 esk1_0 esk5_0) (k9_fintopo2 esk1_0 esk6_0)) = (k9_fintopo2 esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) esk5_0 esk6_0)) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> (k4_subset_1 (u1_struct_0 esk1_0) (k9_fintopo2 esk1_0 esk5_0) (k9_fintopo2 esk1_0 esk6_0)) = (k9_fintopo2 esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) esk5_0 esk6_0)) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> (k4_subset_1 (u1_struct_0 esk1_0) (k9_fintopo2 esk1_0 esk5_0) (k9_fintopo2 esk1_0 esk6_0)) = (k9_fintopo2 esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) esk5_0 esk6_0)) -> False)
  -> (forall X2 X1, ((k3_funct_2 (u1_struct_0 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) (u1_fintopo2 X1) X2) = (k6_fintopo2 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> (k4_subset_1 (u1_struct_0 esk1_0) (k9_fintopo2 esk1_0 esk5_0) (k9_fintopo2 esk1_0 esk6_0)) = (k9_fintopo2 esk1_0 (k4_subset_1 (u1_struct_0 esk1_0) esk5_0 esk6_0)) -> False)
  -> (forall X1, (m1_subset_1 esk6_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> r2_hidden X1 (k6_fintopo2 esk1_0 esk2_0) -> r1_tarski X1 (k9_subset_1 (u1_struct_0 esk1_0) esk3_0 esk4_0) -> False)
  -> (forall X1, (m1_subset_1 esk5_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> r2_hidden X1 (k6_fintopo2 esk1_0 esk2_0) -> r1_tarski X1 (k9_subset_1 (u1_struct_0 esk1_0) esk3_0 esk4_0) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (r2_hidden (esk28_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk28_3 X1 X2 X3) X2 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> l1_fintopo2 X2 -> r1_xboole_0 X4 X3 -> m1_subset_1 X1 (u1_struct_0 X2) -> r2_hidden X4 (k6_fintopo2 X2 X1) -> r2_hidden X1 (k9_fintopo2 X2 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X2 (k9_fintopo2 X1 X3) -> False) -> (r2_hidden (esk26_3 X1 X2 X3) (k6_fintopo2 X1 X2) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (m1_subset_1 (u1_fintopo2 X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))))) -> False) -> l1_fintopo2 X1 -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X2 (k9_fintopo2 X1 X3) -> False) -> (m1_subset_1 (esk26_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X2 (k9_fintopo2 X1 X3) -> False) -> (r1_xboole_0 (esk26_3 X1 X2 X3) X3 -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk12_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_fintopo2 X2 -> r2_hidden X1 (a_2_2_fintopo2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 (k3_subset_1 X2 X3)) = (k7_subset_1 X2 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k4_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, ((esk12_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_fintopo2 X2 -> r2_hidden X1 (a_2_2_fintopo2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k4_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k6_fintopo2 X1 X2) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k9_fintopo2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k4_subset_1 X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1, (v1_funct_2 (u1_fintopo2 X1) (u1_struct_0 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_fintopo2 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk27_2 X3 X2) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, ((a_2_2_fintopo2 X1 X2) = (k9_fintopo2 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (r1_tarski (k3_xboole_0 X1 X3) (k3_xboole_0 X2 X3) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_subset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k4_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k4_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X2 = (k2_xboole_0 X3 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (r2_hidden (esk29_2 X1 X2) X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (X2 = k1_xboole_0 -> False) -> (m1_subset_1 (esk29_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 (k3_subset_1 X2 X1)) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk27_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X2 X4) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X4 X1 X3, (r2_hidden X1 X3 -> False) -> X3 = (k2_xboole_0 X4 X2) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 X1) = (k4_xboole_0 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> ((m1_subset_1 esk6_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> (r2_hidden esk4_0 (k6_fintopo2 esk1_0 esk2_0) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> (r2_hidden esk3_0 (k6_fintopo2 esk1_0 esk2_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> (r2_hidden esk4_0 (k6_fintopo2 esk1_0 esk2_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> (r2_hidden esk3_0 (k6_fintopo2 esk1_0 esk2_0) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> (m1_subset_1 esk6_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> (m1_subset_1 esk5_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> (m1_subset_1 esk6_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> (m1_subset_1 esk5_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> (m1_subset_1 esk6_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> (m1_subset_1 esk5_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (k4_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k4_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk18_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk23_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk17_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk25_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk15_1 X1) -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_funct_1 (u1_fintopo2 X1) -> False) -> l1_fintopo2 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk24_1 X1) -> False) -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_fintopo2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, v1_subset_1 (esk21_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k4_xboole_0 X1 X2) (k4_xboole_0 X1 X3)) = (k4_xboole_0 X1 (k3_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X3 X1, ((k2_xboole_0 (k3_xboole_0 X1 X2) (k3_xboole_0 X1 X3)) = (k3_xboole_0 X1 (k2_xboole_0 X2 X3)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk14_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (r1_xboole_0 (k4_xboole_0 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk14_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk14_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski (k3_xboole_0 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk14_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> ((v1_xboole_0 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((l1_fintopo2 esk9_0 -> False) -> False)
  -> ((l1_fintopo2 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
