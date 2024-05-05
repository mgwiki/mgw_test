(** $I sig/MizarPreamble.mgs **)

Theorem t37_fintopo2:
 forall v2_struct_0:set -> prop,
 forall esk8_4:set -> set -> set -> set -> set,
 forall k6_fintopo2:set -> set -> set,
 forall l1_fintopo2:set -> prop,
 forall u1_struct_0:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall a_2_2_fintopo2:set -> set -> set,
 forall r1_xboole_0:set -> set -> prop,
 forall k4_xboole_0:set -> set -> set,
 forall esk3_3:set -> set -> set -> set,
 forall a_2_3_fintopo2:set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall esk24_3:set -> set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k3_subset_1:set -> set -> set,
 forall k9_subset_1:set -> set -> set -> set,
 forall k7_subset_1:set -> set -> set -> set,
 forall esk23_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk26_2:set -> set -> set,
 forall k3_xboole_0:set -> set -> set,
 forall v7_struct_0:set -> prop,
 forall esk15_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk14_1:set -> set,
 forall esk21_1:set -> set,
 forall esk12_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk18_1:set -> set,
 forall esk17_0:set,
 forall esk16_1:set -> set,
 forall esk6_1:set -> set,
 forall o_0_0_xboole_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk13_0:set,
 forall esk11_2:set -> set -> set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk20_1:set -> set,
 forall esk22_1:set -> set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall k1_xboole_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall esk19_1:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall k9_fintopo2:set -> set -> set,
 forall esk25_3:set -> set -> set -> set,
 forall k10_fintopo2:set -> set -> set,
 forall u1_fintopo2:set -> set,
 forall k1_funct_1:set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X1 (a_2_2_fintopo2 X2 X3) -> False) -> (r2_hidden (esk8_4 X1 X2 X3 X4) (k6_fintopo2 X2 X4) -> False) -> X1 = X4 -> l1_fintopo2 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X1 (a_2_2_fintopo2 X2 X3) -> False) -> (m1_subset_1 (esk8_4 X1 X2 X3 X4) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> X1 = X4 -> l1_fintopo2 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X4 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X1 (a_2_2_fintopo2 X2 X3) -> False) -> (r1_xboole_0 (esk8_4 X1 X2 X3 X4) X3 -> False) -> X1 = X4 -> l1_fintopo2 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X1 X4 X2, (v2_struct_0 X2 -> False) -> l1_fintopo2 X2 -> r1_xboole_0 X1 X4 -> r2_hidden X3 (a_2_2_fintopo2 X2 X4) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> r2_hidden X1 (k6_fintopo2 X2 (esk7_3 X3 X2 X4)) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk3_3 X1 X2 X3) X3 -> r2_hidden (esk3_3 X1 X2 X3) X1 -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (r2_hidden (esk10_3 X1 X2 X3) (k6_fintopo2 X2 (esk9_3 X1 X2 X3)) -> False) -> l1_fintopo2 X2 -> r2_hidden X1 (a_2_3_fintopo2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X1, ((k3_funct_2 (u1_struct_0 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) (u1_fintopo2 X1) X2) = (k6_fintopo2 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk3_3 X1 X2 X3) X2 -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r2_hidden (esk25_3 X1 X2 X3) (k6_fintopo2 X1 X2) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_hidden X2 (k10_fintopo2 X1 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk25_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_hidden X2 (k10_fintopo2 X1 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X3 X2, (v2_struct_0 X2 -> False) -> l1_fintopo2 X2 -> r1_xboole_0 X4 X3 -> m1_subset_1 X1 (u1_struct_0 X2) -> r2_hidden X4 (k6_fintopo2 X2 X1) -> r2_hidden X1 (k9_fintopo2 X2 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X2 (k9_fintopo2 X1 X3) -> False) -> (r2_hidden (esk24_3 X1 X2 X3) (k6_fintopo2 X1 X2) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (m1_subset_1 (u1_fintopo2 X1) (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))))) -> False) -> l1_fintopo2 X1 -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_tarski (esk25_3 X1 X2 X3) X3 -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_hidden X2 (k10_fintopo2 X1 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X5 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (a_2_3_fintopo2 X2 X5) -> False) -> X1 = X3 -> l1_fintopo2 X2 -> r1_tarski X4 X5 -> m1_subset_1 X1 (u1_struct_0 X2) -> r2_hidden X4 (k6_fintopo2 X2 X1) -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X2 (k9_fintopo2 X1 X3) -> False) -> (m1_subset_1 (esk24_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X4 X1 X2, (v2_struct_0 X2 -> False) -> (r2_hidden X3 (k10_fintopo2 X2 X4) -> False) -> l1_fintopo2 X2 -> r1_tarski X1 X4 -> m1_subset_1 X3 (u1_struct_0 X2) -> r2_hidden X1 (k6_fintopo2 X2 X3) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk10_3 X1 X2 X3) (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_fintopo2 X2 -> r2_hidden X1 (a_2_3_fintopo2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (X3 = (k4_xboole_0 X1 X2) -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk3_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r2_hidden X2 (k9_fintopo2 X1 X3) -> False) -> (r1_xboole_0 (esk24_3 X1 X2 X3) X3 -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk9_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_fintopo2 X2 -> r2_hidden X1 (a_2_3_fintopo2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) (u1_struct_0 X2) -> False) -> l1_fintopo2 X2 -> r2_hidden X1 (a_2_2_fintopo2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (r1_tarski (esk10_3 X1 X2 X3) X3 -> False) -> l1_fintopo2 X2 -> r2_hidden X1 (a_2_3_fintopo2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 (k3_subset_1 X2 X3)) = (k7_subset_1 X2 X1 X3) -> False) -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X3 X2, ((esk9_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_fintopo2 X2 -> r2_hidden X1 (a_2_3_fintopo2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X2, ((esk7_3 X1 X2 X3) = X1 -> False) -> (v2_struct_0 X2 -> False) -> l1_fintopo2 X2 -> r2_hidden X1 (a_2_2_fintopo2 X2 X3) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k9_subset_1 X2 X3 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X1 X3) = (k9_subset_1 X2 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> r2_hidden (esk23_2 X1 X2) X2 -> r2_hidden (esk23_2 X1 X2) X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k6_fintopo2 X1 X2) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k10_fintopo2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k9_fintopo2 X1 X2) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1, (v1_funct_2 (u1_fintopo2 X1) (u1_struct_0 X1) (k1_zfmisc_1 (k1_zfmisc_1 (u1_struct_0 X1))) -> False) -> l1_fintopo2 X1 -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk26_2 X3 X2) -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X1) = (k3_xboole_0 X3 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k10_fintopo2 X1 X2) = (a_2_3_fintopo2 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X1, ((k9_fintopo2 X1 X2) = (a_2_2_fintopo2 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l1_fintopo2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X2 X1, ((k9_subset_1 X2 X3 X3) = X3 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk23_2 X1 X2) X2 -> False) -> (r2_hidden (esk23_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (k3_subset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k4_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k4_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k3_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k4_xboole_0 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 (k3_subset_1 X2 X1)) = X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k4_xboole_0 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_hidden (esk26_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k4_xboole_0 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, ((k3_subset_1 X2 X1) = (k4_xboole_0 X2 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_xboole_0 X2 X1 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (k4_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X1 X2, (r1_xboole_0 X1 X2 -> False) -> (k3_xboole_0 X1 X2) = k1_xboole_0 -> False)
  -> (forall X2 X1, ((k4_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = k1_xboole_0 -> False) -> r1_xboole_0 X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk15_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk14_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk14_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk22_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk21_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk12_1 X1) -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_funct_1 (u1_fintopo2 X1) -> False) -> l1_fintopo2 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk21_1 X1) -> False) -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_fintopo2 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k3_subset_1 (u1_struct_0 esk1_0) (k9_fintopo2 esk1_0 (k3_subset_1 (u1_struct_0 esk1_0) esk2_0))) = (k10_fintopo2 esk1_0 esk2_0) -> False)
  -> (forall X1, v1_subset_1 (esk18_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk11_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk11_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk11_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk11_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k3_xboole_0 X1 X2) = (k3_xboole_0 X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (u1_struct_0 esk1_0)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk6_1 X1) X1 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> (forall X1, ((k3_xboole_0 X1 k1_xboole_0) = k1_xboole_0 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk16_1 X1) -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk5_0 -> False) -> False)
  -> ((l1_fintopo2 esk4_0 -> False) -> False)
  -> ((l1_fintopo2 esk1_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
