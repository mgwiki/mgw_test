(** $I sig/MizarPreamble.mgs **)

Theorem l16_afvect01:
 forall k1_zfmisc_1:set -> set,
 forall v1_analoaf:set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk15_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk14_1:set -> set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall esk9_0:set,
 forall esk10_0:set,
 forall esk13_0:set,
 forall v1_afvect0:set -> prop,
 forall esk11_1:set -> set,
 forall esk12_0:set,
 forall esk16_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall k1_xboole_0:set,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk17_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall k4_tarski:set -> set -> set,
 forall esk5_0:set,
 forall esk8_0:set,
 forall esk7_0:set,
 forall esk6_0:set,
 forall c4__afvect01:set,
 forall g1_analoaf:set -> set -> set,
 forall o_0_0_afvect01:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall r2_diraf:set -> set -> set -> set -> set -> prop,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall u1_analoaf:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_domain_1:set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall l1_analoaf:set -> prop,
 forall v2_struct_0:set -> prop,
     (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_hidden (k1_domain_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (k1_domain_1 (u1_struct_0 X1) (u1_struct_0 X1) X2 X3) (k1_domain_1 (u1_struct_0 X1) (u1_struct_0 X1) X4 X5)) (u1_analoaf X1) -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_hidden (k1_domain_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (k1_domain_1 (u1_struct_0 X1) (u1_struct_0 X1) X2 X3) (k1_domain_1 (u1_struct_0 X1) (u1_struct_0 X1) X4 X5)) (u1_analoaf X1) -> False) -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (r2_diraf o_0_0_afvect01 esk1_0 esk2_0 esk3_0 esk4_0 -> r2_analoaf (g1_analoaf (u1_struct_0 o_0_0_afvect01) c4__afvect01) esk5_0 esk6_0 esk7_0 esk8_0 -> False)
  -> ((r2_diraf o_0_0_afvect01 esk1_0 esk2_0 esk3_0 esk4_0 -> False) -> (r2_analoaf (g1_analoaf (u1_struct_0 o_0_0_afvect01) c4__afvect01) esk5_0 esk6_0 esk7_0 esk8_0 -> False) -> False)
  -> (forall X3 X1 X2 X4, (r2_hidden (k4_tarski (k4_tarski X1 X2) (k4_tarski X3 X4)) c4__afvect01 -> False) -> m1_subset_1 X4 (u1_struct_0 o_0_0_afvect01) -> m1_subset_1 X3 (u1_struct_0 o_0_0_afvect01) -> m1_subset_1 X2 (u1_struct_0 o_0_0_afvect01) -> m1_subset_1 X1 (u1_struct_0 o_0_0_afvect01) -> r2_diraf o_0_0_afvect01 X1 X2 X3 X4 -> False)
  -> (forall X3 X1 X2 X4, (r2_diraf o_0_0_afvect01 X1 X2 X3 X4 -> False) -> m1_subset_1 X4 (u1_struct_0 o_0_0_afvect01) -> m1_subset_1 X3 (u1_struct_0 o_0_0_afvect01) -> m1_subset_1 X2 (u1_struct_0 o_0_0_afvect01) -> m1_subset_1 X1 (u1_struct_0 o_0_0_afvect01) -> r2_hidden (k4_tarski (k4_tarski X1 X2) (k4_tarski X3 X4)) c4__afvect01 -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_domain_1 X1 X2 X3 X4) (k2_zfmisc_1 X1 X2) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v2_struct_0 (g1_analoaf X1 X2) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X1, (m1_subset_1 (u1_analoaf X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)))) -> False) -> l1_analoaf X1 -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_analoaf X1 X3) = (g1_analoaf X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_analoaf X3 X1) = (g1_analoaf X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X3) (k2_zfmisc_1 X3 X3))) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_analoaf (g1_analoaf X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X1 X2, (v1_analoaf (g1_analoaf X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X1 X2, (l1_analoaf (g1_analoaf X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X1 X4 X3 X2, ((k1_domain_1 X1 X2 X3 X4) = (k4_tarski X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_analoaf (u1_struct_0 X1) (u1_analoaf X1)) = X1 -> False) -> l1_analoaf X1 -> v1_analoaf X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk15_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk14_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk14_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v7_struct_0 esk12_0 -> False)
  -> (v7_struct_0 o_0_0_afvect01 -> False)
  -> (v2_struct_0 esk12_0 -> False)
  -> ((m1_subset_1 c4__afvect01 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 o_0_0_afvect01) (u1_struct_0 o_0_0_afvect01)) (k2_zfmisc_1 (u1_struct_0 o_0_0_afvect01) (u1_struct_0 o_0_0_afvect01)))) -> False) -> False)
  -> ((m1_subset_1 esk8_0 (u1_struct_0 (g1_analoaf (u1_struct_0 o_0_0_afvect01) c4__afvect01)) -> False) -> False)
  -> ((m1_subset_1 esk7_0 (u1_struct_0 (g1_analoaf (u1_struct_0 o_0_0_afvect01) c4__afvect01)) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 (g1_analoaf (u1_struct_0 o_0_0_afvect01) c4__afvect01)) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 (g1_analoaf (u1_struct_0 o_0_0_afvect01) c4__afvect01)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk11_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 o_0_0_afvect01) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 o_0_0_afvect01) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 o_0_0_afvect01) -> False) -> False)
  -> ((m1_subset_1 esk1_0 (u1_struct_0 o_0_0_afvect01) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v1_afvect0 esk12_0 -> False) -> False)
  -> ((v1_afvect0 o_0_0_afvect01 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk10_0 -> False) -> False)
  -> ((v1_analoaf esk12_0 -> False) -> False)
  -> ((l1_analoaf esk12_0 -> False) -> False)
  -> ((l1_analoaf esk9_0 -> False) -> False)
  -> ((l1_analoaf o_0_0_afvect01 -> False) -> False)
  -> ((esk4_0 = esk8_0 -> False) -> False)
  -> ((esk3_0 = esk7_0 -> False) -> False)
  -> ((esk2_0 = esk6_0 -> False) -> False)
  -> ((esk5_0 = esk1_0 -> False) -> False)
  -> False.
Admitted.
