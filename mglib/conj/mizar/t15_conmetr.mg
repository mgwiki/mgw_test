(** $I sig/MizarPreamble.mgs **)

Theorem t15_conmetr:
 forall epred1_5:set -> set -> set -> set -> set -> prop,
 forall esk16_5:set -> set -> set -> set -> set -> set,
 forall esk17_5:set -> set -> set -> set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall r10_analmetr:set -> set -> set -> prop,
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall r5_analmetr:set -> set -> set -> set -> prop,
 forall esk3_1:set -> set,
 forall esk4_1:set -> set,
 forall esk5_1:set -> set,
 forall esk2_1:set -> set,
 forall v1_conmetr:set -> prop,
 forall r6_analmetr:set -> set -> set -> set -> prop,
 forall v4_analmetr:set -> set -> prop,
 forall g1_analoaf:set -> set -> set,
 forall v1_analoaf:set -> prop,
 forall r7_analmetr:set -> set -> set -> prop,
 forall v2_diraf:set -> prop,
 forall l1_struct_0:set -> prop,
 forall esk1_0:set,
 forall esk11_0:set,
 forall esk10_0:set,
 forall esk12_0:set,
 forall esk13_1:set -> set,
 forall esk14_0:set,
 forall r1_tarski:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall u1_analoaf:set -> set,
 forall v1_aff_1:set -> set -> prop,
 forall r3_aff_1:set -> set -> set -> prop,
 forall esk6_4:set -> set -> set -> set -> set,
 forall v1_diraf:set -> prop,
 forall l1_analoaf:set -> prop,
 forall v7_struct_0:set -> prop,
 forall k3_analmetr:set -> set,
 forall v3_conaffm:set -> prop,
 forall esk9_1:set -> set,
 forall esk7_1:set -> set,
 forall esk8_1:set -> set,
 forall v3_analmetr:set -> prop,
 forall esk19_5:set -> set -> set -> set -> set -> set,
 forall esk15_5:set -> set -> set -> set -> set -> set,
 forall esk18_5:set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall v2_analmetr:set -> prop,
 forall u1_struct_0:set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall l1_analmetr:set -> prop,
 forall v2_struct_0:set -> prop,
 forall r4_analmetr:set -> set -> set -> set -> set -> prop,
 forall epred2_7:set -> set -> set -> set -> set -> set -> set -> prop,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
     (forall X1 X5 X6 X7 X4 X2 X3, (X2 = X3 -> False) -> (r4_analmetr X1 X4 X5 X6 X7 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> r4_analmetr X1 X2 X3 X6 X7 -> epred2_7 X1 X2 X4 X5 X6 X7 X3 -> False)
  -> (forall X1 X5 X6 X7 X4 X2 X3, (X2 = X3 -> False) -> (r4_analmetr X1 X4 X5 X6 X7 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> r4_analmetr X1 X6 X7 X2 X3 -> epred2_7 X1 X2 X4 X5 X6 X7 X3 -> False)
  -> (forall X1 X7 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (r4_analmetr X1 X6 X7 X4 X5 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> r4_analmetr X1 X2 X3 X6 X7 -> epred2_7 X1 X2 X6 X7 X4 X5 X3 -> False)
  -> (forall X1 X7 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (r4_analmetr X1 X6 X7 X4 X5 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> r4_analmetr X1 X6 X7 X2 X3 -> epred2_7 X1 X2 X6 X7 X4 X5 X3 -> False)
  -> (forall X1 X3 X6 X7 X2 X4 X5, (X4 = X5 -> False) -> (r4_analmetr X1 X2 X3 X6 X7 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> r4_analmetr X1 X4 X5 X6 X7 -> epred2_7 X1 X4 X2 X3 X6 X7 X5 -> False)
  -> (forall X1 X3 X6 X7 X2 X4 X5, (X4 = X5 -> False) -> (r4_analmetr X1 X2 X3 X6 X7 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> r4_analmetr X1 X6 X7 X4 X5 -> epred2_7 X1 X4 X2 X3 X6 X7 X5 -> False)
  -> (forall X1 X7 X2 X3 X6 X4 X5, (X4 = X5 -> False) -> (r4_analmetr X1 X6 X7 X2 X3 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> r4_analmetr X1 X4 X5 X6 X7 -> epred2_7 X1 X4 X6 X7 X2 X3 X5 -> False)
  -> (forall X1 X7 X2 X3 X6 X4 X5, (X4 = X5 -> False) -> (r4_analmetr X1 X6 X7 X2 X3 -> False) -> r2_analoaf X1 X2 X3 X4 X5 -> r4_analmetr X1 X6 X7 X4 X5 -> epred2_7 X1 X4 X6 X7 X2 X3 X5 -> False)
  -> (forall X7 X5 X2 X3 X4 X6 X1, (v2_struct_0 X1 -> False) -> (epred2_7 X1 X2 X4 X5 X6 X7 X3 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X4 X3 X5 X2, (epred1_5 X1 X5 X2 X4 X3 -> False) -> r2_analoaf X1 X2 (esk16_5 X3 X4 X2 X5 X1) X4 (esk17_5 X3 X4 X2 X5 X1) -> False)
  -> (forall X2 X5 X4 X3 X1, (epred1_5 X5 X4 X3 X2 X1 -> False) -> r2_hidden (esk16_5 X1 X2 X3 X4 X5) (esk18_5 X1 X2 X3 X4 X5) -> False)
  -> (forall X7 X5 X3 X10 X1 X9 X4 X6 X2 X8, (X2 = X8 -> False) -> (X2 = X7 -> False) -> (X2 = X6 -> False) -> (X2 = X5 -> False) -> (X2 = X4 -> False) -> (X2 = X3 -> False) -> (r2_hidden X7 X9 -> False) -> (r2_hidden X5 X10 -> False) -> (r2_analoaf X1 X3 X7 X4 X8 -> False) -> r2_hidden X8 X10 -> r2_hidden X7 X10 -> r2_hidden X6 X10 -> r2_hidden X5 X9 -> r2_hidden X4 X9 -> r2_hidden X3 X9 -> r2_hidden X2 X10 -> r2_hidden X2 X9 -> r10_analmetr X1 X9 X10 -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> r2_analoaf X1 X5 X8 X3 X6 -> r2_analoaf X1 X5 X7 X4 X6 -> epred1_5 X1 X2 X3 X4 X5 -> m1_subset_1 X10 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X9 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X4 X5 X3 X2, (epred1_5 X1 X5 X4 X3 X2 -> False) -> (r2_analoaf X1 X2 (esk17_5 X2 X3 X4 X5 X1) X4 (esk15_5 X2 X3 X4 X5 X1) -> False) -> False)
  -> (forall X1 X3 X4 X5 X2, (epred1_5 X1 X5 X4 X3 X2 -> False) -> (r2_analoaf X1 X2 (esk16_5 X2 X3 X4 X5 X1) X3 (esk15_5 X2 X3 X4 X5 X1) -> False) -> False)
  -> (forall X1 X2 X4 X5 X3, (epred1_5 X1 X5 X4 X3 X2 -> False) -> (r10_analmetr X1 (esk18_5 X2 X3 X4 X5 X1) (esk19_5 X2 X3 X4 X5 X1) -> False) -> False)
  -> (forall X2 X5 X4 X3 X1, (epred1_5 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk17_5 X1 X2 X3 X4 X5) (esk19_5 X1 X2 X3 X4 X5) -> False) -> False)
  -> (forall X2 X5 X4 X3 X1, (epred1_5 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk16_5 X1 X2 X3 X4 X5) (esk19_5 X1 X2 X3 X4 X5) -> False) -> False)
  -> (forall X2 X5 X4 X3 X1, (epred1_5 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk15_5 X1 X2 X3 X4 X5) (esk19_5 X1 X2 X3 X4 X5) -> False) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (v3_conaffm X2 -> False) -> v3_analmetr X2 -> l1_analmetr X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> r4_analmetr X2 X1 (esk7_1 X2) (esk8_1 X2) (esk9_1 X2) -> r4_analmetr X2 X1 (esk8_1 X2) (esk7_1 X2) (esk9_1 X2) -> r4_analmetr X2 X1 (esk9_1 X2) (esk7_1 X2) (esk8_1 X2) -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X2 X3 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r4_analmetr X1 X2 X3 X6 X7 -> r4_analmetr X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r4_analmetr X1 X6 X7 X2 X3 -> r4_analmetr X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X4 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r4_analmetr X1 X4 X5 X6 X7 -> r4_analmetr X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r4_analmetr X1 X6 X7 X4 X5 -> r4_analmetr X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X3 X4 X5 X2, (epred1_5 X5 X4 X3 X2 X1 -> False) -> r2_hidden X1 (esk19_5 X1 X2 X3 X4 X5) -> False)
  -> (forall X5 X2 X4 X3 X1, (epred1_5 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk19_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 (u1_struct_0 X5)) -> False) -> False)
  -> (forall X5 X2 X4 X3 X1, (epred1_5 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk18_5 X1 X2 X3 X4 X5) (k1_zfmisc_1 (u1_struct_0 X5)) -> False) -> False)
  -> (forall X5 X2 X4 X3 X1, (epred1_5 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk17_5 X1 X2 X3 X4 X5) (u1_struct_0 X5) -> False) -> False)
  -> (forall X5 X2 X4 X3 X1, (epred1_5 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk16_5 X1 X2 X3 X4 X5) (u1_struct_0 X5) -> False) -> False)
  -> (forall X5 X2 X4 X3 X1, (epred1_5 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk15_5 X1 X2 X3 X4 X5) (u1_struct_0 X5) -> False) -> False)
  -> (forall X1 X2 X4 X5 X3, (epred1_5 X5 X1 X4 X3 X2 -> False) -> (r2_hidden X1 (esk19_5 X2 X3 X4 X1 X5) -> False) -> False)
  -> (forall X1 X2 X4 X5 X3, (epred1_5 X5 X1 X4 X3 X2 -> False) -> (r2_hidden X1 (esk18_5 X2 X3 X4 X1 X5) -> False) -> False)
  -> (forall X1 X2 X4 X5 X3, (epred1_5 X5 X4 X1 X3 X2 -> False) -> (r2_hidden X1 (esk18_5 X2 X3 X1 X4 X5) -> False) -> False)
  -> (forall X1 X2 X3 X4 X5, (epred1_5 X5 X4 X3 X1 X2 -> False) -> (r2_hidden X1 (esk18_5 X2 X1 X3 X4 X5) -> False) -> False)
  -> (forall X1 X3 X4 X5 X2, (epred1_5 X5 X4 X3 X2 X1 -> False) -> (r2_hidden X1 (esk18_5 X1 X2 X3 X4 X5) -> False) -> False)
  -> (forall X7 X8 X9 X6 X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X6 X7 X8 X9 -> False) -> X5 = X9 -> X4 = X8 -> X3 = X7 -> X2 = X6 -> l1_analmetr X1 -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X4 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X3 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X2 (u1_struct_0 (k3_analmetr X1)) -> r2_analoaf (k3_analmetr X1) X2 X3 X4 X5 -> False)
  -> (forall X7 X8 X9 X6 X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf (k3_analmetr X1) X6 X7 X8 X9 -> False) -> X5 = X9 -> X4 = X8 -> X3 = X7 -> X2 = X6 -> l1_analmetr X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X4 X5 -> m1_subset_1 X9 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X8 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X7 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X6 (u1_struct_0 (k3_analmetr X1)) -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X3 X2 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X3 X2 -> False)
  -> (forall X5 X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X3 X2 -> False)
  -> (forall X5 X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X3 X2 -> False)
  -> (forall X1 X3 X5 X4 X2, (epred1_5 X5 X1 X4 X3 X2 -> False) -> (esk17_5 X2 X3 X4 X1 X5) = X1 -> False)
  -> (forall X1 X3 X5 X4 X2, (epred1_5 X5 X1 X4 X3 X2 -> False) -> (esk16_5 X2 X3 X4 X1 X5) = X1 -> False)
  -> (forall X1 X3 X5 X4 X2, (epred1_5 X5 X1 X4 X3 X2 -> False) -> (esk15_5 X2 X3 X4 X1 X5) = X1 -> False)
  -> (forall X1 X2 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X5 -> r2_analoaf X1 X3 X4 X3 X5 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X2 X4 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r5_analmetr X1 X2 X3 X4 -> False) -> l1_analmetr X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X2 X4 -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r5_analmetr X1 X2 X3 X4 -> False) -> (r4_analmetr X1 (esk6_4 X1 X2 X3 X4) X2 X3 X4 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> v3_conaffm X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r5_analmetr X1 X2 X3 X4 -> False) -> (r4_analmetr X1 (esk6_4 X1 X2 X3 X4) X3 X2 X4 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> v3_conaffm X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r5_analmetr X1 X2 X3 X4 -> False) -> (r4_analmetr X1 (esk6_4 X1 X2 X3 X4) X4 X2 X3 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> v3_conaffm X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_conmetr X1 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> epred1_5 X1 (esk2_1 X1) (esk3_1 X1) (esk4_1 X1) (esk5_1 X1) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X4 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X4 -> False) -> l1_analmetr X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r5_analmetr X1 X2 X3 X4 -> False)
  -> (forall X3 X4 X5 X2 X6 X7 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> r2_hidden X5 X7 -> r2_hidden X4 X7 -> r2_hidden X3 X6 -> r2_hidden X2 X6 -> r3_aff_1 X1 X6 X7 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> m1_subset_1 X7 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X6 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X5 X6 X7 X4 X2 X3 X1, (v2_struct_0 X1 -> False) -> (r4_analmetr X1 X4 X5 X6 X7 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r2_hidden X7 X3 -> r2_hidden X6 X3 -> r2_hidden X5 X2 -> r2_hidden X4 X2 -> r10_analmetr X1 X2 X3 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X2 X5 X1, (v2_struct_0 X1 -> False) -> (epred1_5 X1 X2 X3 X4 X5 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> v1_conmetr X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X3 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X3 X2 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X4 X5 X2 X1, (epred1_5 X3 X1 X2 X4 X5 -> False) -> X1 = X2 -> False)
  -> (forall X3 X4 X5 X2 X1, (epred1_5 X3 X1 X4 X2 X5 -> False) -> X1 = X2 -> False)
  -> (forall X3 X4 X5 X2 X1, (epred1_5 X3 X1 X4 X5 X2 -> False) -> X1 = X2 -> False)
  -> (forall X7 X6 X5 X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r5_analmetr X1 X5 X6 X7 -> False) -> X4 = X7 -> X3 = X6 -> X2 = X5 -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X3 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X2 (u1_struct_0 (k3_analmetr X1)) -> r1_aff_1 (k3_analmetr X1) X2 X3 X4 -> False)
  -> (forall X7 X6 X5 X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r1_aff_1 (k3_analmetr X1) X5 X6 X7 -> False) -> X4 = X7 -> X3 = X6 -> X2 = X5 -> l1_analmetr X1 -> v2_analmetr X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r5_analmetr X1 X2 X3 X4 -> m1_subset_1 X7 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X6 (u1_struct_0 (k3_analmetr X1)) -> m1_subset_1 X5 (u1_struct_0 (k3_analmetr X1)) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r5_analmetr X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk6_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> v3_conaffm X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X3 X2 -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_hidden X4 X5 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> r2_hidden X3 X5 -> r2_hidden X2 X5 -> v1_aff_1 X5 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X4 X3 X5 X2 X1, (v2_struct_0 X1 -> False) -> (v4_analmetr X4 X1 -> False) -> l1_analmetr X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r6_analmetr X1 X2 X3 X4 -> m1_subset_1 X5 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1, (m1_subset_1 (u1_analoaf X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)))) -> False) -> l1_analoaf X1 -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_analoaf X1 X3) = (g1_analoaf X2 X4) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X3 X4 X1 X2, (X1 = X2 -> False) -> (g1_analoaf X3 X1) = (g1_analoaf X4 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X3) (k2_zfmisc_1 X3 X3))) -> False)
  -> (forall X1 X2, (v1_analoaf (g1_analoaf X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X1 X2, (l1_analoaf (g1_analoaf X1 X2) -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (k2_zfmisc_1 X1 X1))) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_conaffm X1 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> r5_analmetr X1 (esk7_1 X1) (esk8_1 X1) (esk9_1 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X2 X3 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X2 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X3 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X3 X4 X5 X2, (v2_struct_0 X2 -> False) -> (v4_analmetr X1 X2 -> False) -> l1_analmetr X2 -> r7_analmetr X2 X1 X3 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X3 X4 X5 X2, (v2_struct_0 X2 -> False) -> (v4_analmetr X1 X2 -> False) -> l1_analmetr X2 -> r7_analmetr X2 X3 X1 -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r7_analmetr X1 X2 X3 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r10_analmetr X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r10_analmetr X1 X2 X3 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r7_analmetr X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> (r10_analmetr X1 X3 X2 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r10_analmetr X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (v4_analmetr X3 X2 -> False) -> X1 = X3 -> l1_analmetr X2 -> v2_analmetr X2 -> v1_aff_1 X1 (k3_analmetr X2) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X2))) -> False)
  -> (forall X2 X3 X1, (v2_struct_0 X1 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> r10_analmetr X1 X2 X2 -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X3 X1 X2, (v2_struct_0 X2 -> False) -> (v1_aff_1 X3 (k3_analmetr X2) -> False) -> X1 = X3 -> l1_analmetr X2 -> v2_analmetr X2 -> v4_analmetr X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X2))) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (r3_aff_1 X1 X2 X2 -> False) -> l1_analoaf X1 -> v1_diraf X1 -> v1_aff_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (u1_struct_0 X1)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False) -> l1_analmetr X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X2))) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 (k3_analmetr X2))) -> False) -> l1_analmetr X2 -> m1_subset_1 X1 (k1_zfmisc_1 (u1_struct_0 X2)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 X1 (u1_struct_0 X2) -> False) -> l1_analmetr X2 -> m1_subset_1 X1 (u1_struct_0 (k3_analmetr X2)) -> False)
  -> (forall X1 X2, (v2_struct_0 X2 -> False) -> (m1_subset_1 X1 (u1_struct_0 (k3_analmetr X2)) -> False) -> l1_analmetr X2 -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_conmetr X1 -> False) -> (m1_subset_1 (esk5_1 X1) (u1_struct_0 X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_conmetr X1 -> False) -> (m1_subset_1 (esk4_1 X1) (u1_struct_0 X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_conmetr X1 -> False) -> (m1_subset_1 (esk3_1 X1) (u1_struct_0 X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_conmetr X1 -> False) -> (m1_subset_1 (esk2_1 X1) (u1_struct_0 X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_conaffm X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_conaffm X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_struct_0 X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v3_conaffm X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_struct_0 X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((g1_analoaf (u1_struct_0 X1) (u1_analoaf X1)) = X1 -> False) -> l1_analoaf X1 -> v1_analoaf X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> v7_struct_0 (k3_analmetr X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> v7_struct_0 (k3_analmetr X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_diraf (k3_analmetr X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_diraf (k3_analmetr X1) -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_diraf (k3_analmetr X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_analoaf (k3_analmetr X1) -> False) -> l1_analmetr X1 -> v2_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_analoaf (k3_analmetr X1) -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_analmetr X1 -> v2_struct_0 (k3_analmetr X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v2_analmetr X1 -> False) -> v3_analmetr X1 -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_analoaf (k3_analmetr X1) -> False) -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_analoaf (k3_analmetr X1) -> False) -> l1_analmetr X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (l1_analoaf (k3_analmetr X1) -> False) -> l1_analmetr X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (forall X1, (l1_analoaf X1 -> False) -> l1_analmetr X1 -> False)
  -> (v1_conmetr esk1_0 -> False)
  -> (v2_struct_0 esk14_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((l1_struct_0 esk12_0 -> False) -> False)
  -> ((l1_analoaf esk11_0 -> False) -> False)
  -> ((v3_conaffm esk1_0 -> False) -> False)
  -> ((l1_analmetr esk14_0 -> False) -> False)
  -> ((l1_analmetr esk10_0 -> False) -> False)
  -> ((l1_analmetr esk1_0 -> False) -> False)
  -> ((v3_analmetr esk1_0 -> False) -> False)
  -> False.
Admitted.
