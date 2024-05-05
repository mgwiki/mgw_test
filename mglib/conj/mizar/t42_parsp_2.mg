(** $I sig/MizarPreamble.mgs **)

Theorem t42_parsp_2:
 forall esk16_4:set -> set -> set -> set -> set,
 forall v7_struct_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk1_0:set,
 forall esk8_0:set,
 forall esk7_0:set,
 forall esk9_0:set,
 forall esk6_0:set,
 forall esk14_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk13_0:set,
 forall esk11_0:set,
 forall esk10_0:set,
 forall esk12_1:set -> set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk15_0:set,
 forall v1_xboole_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall k1_xboole_0:set,
 forall l1_struct_0:set -> prop,
 forall np__1:set,
 forall v13_struct_0:set -> set -> prop,
 forall esk17_3:set -> set -> set -> set,
 forall r1_parsp_1:set -> set -> set -> set -> set -> prop,
 forall v2_struct_0:set -> prop,
 forall v2_parsp_1:set -> prop,
 forall l1_parsp_1:set -> prop,
 forall r1_parsp_2:set -> set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall v1_parsp_2:set -> prop,
 forall r2_parsp_2:set -> set -> set -> set -> set -> prop,
     (forall X1 X2 X5 X7 X6 X3 X4, (X3 = X4 -> False) -> (v2_struct_0 X1 -> False) -> (r2_parsp_2 X1 X3 X6 X4 X7 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X2 X5 X4 X7 -> r2_parsp_2 X1 X2 X5 X3 X6 -> False)
  -> (forall X4 X3 X2 X6 X5 X7 X1, (v2_struct_0 X1 -> False) -> (r1_parsp_2 X1 X2 X3 X4 -> False) -> (r2_parsp_2 X1 X2 X3 X4 X7 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_parsp_2 X1 X5 X6 X4 X7 -> r2_parsp_2 X1 X5 X6 X2 X3 -> False)
  -> (forall X6 X5 X7 X4 X3 X2 X1, (v2_struct_0 X1 -> False) -> (r1_parsp_1 X1 X4 X6 X5 X7 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_parsp_2 X1 X2 X3 X6 X7 -> r2_parsp_2 X1 X2 X3 X4 X5 -> False)
  -> (forall X6 X4 X3 X2 X1 X5 X7, (X5 = X7 -> False) -> (X5 = X6 -> False) -> (v2_struct_0 X1 -> False) -> (r1_parsp_2 X1 X2 X3 X4 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X5 X6 X7 -> r1_parsp_1 X1 X2 X4 X5 X7 -> r1_parsp_1 X1 X2 X3 X5 X6 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_parsp_2 X1 X2 X3 X4 X5 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_parsp_2 X1 X2 X4 X3 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_parsp_2 X1 X2 X3 X4 X5 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_parsp_2 X1 X3 X2 X5 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_parsp_2 X1 X2 X3 X4 X5 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_parsp_2 X1 X3 X5 X2 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_parsp_2 X1 X2 X3 X4 X5 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_parsp_2 X1 X4 X2 X5 X3 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_parsp_2 X1 X2 X3 X4 X5 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_parsp_2 X1 X4 X5 X2 X3 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_parsp_2 X1 X2 X3 X4 X5 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_parsp_2 X1 X5 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> (r2_parsp_2 X1 X2 X3 X4 X5 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_parsp_2 X1 X5 X4 X3 X2 -> False)
  -> (forall X5 X3 X2 X4 X6 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X4 X5 X6 -> r1_parsp_2 X1 X2 X3 X6 -> r2_parsp_2 X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X2 X3 X5 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X2 X4 X3 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X2 X4 X5 X3 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X2 X5 X3 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X2 X5 X4 X3 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X3 X2 X4 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X3 X2 X5 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X3 X4 X2 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X3 X4 X5 X2 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X3 X5 X2 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X3 X5 X4 X2 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X4 X2 X3 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X4 X2 X5 X3 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X4 X3 X2 X5 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X4 X3 X5 X2 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X4 X5 X2 X3 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X4 X5 X3 X2 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X5 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X5 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X5 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X5 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X5 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X5 X1, (v2_struct_0 X1 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> r2_parsp_2 X1 X5 X4 X3 X2 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r1_parsp_2 X1 X2 X3 X4 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_1 X1 X2 X3 X2 X4 -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_parsp_2 X1 X2 X3 X4 -> False) -> (r2_parsp_2 X1 X2 X3 X4 (esk16_4 X1 X2 X3 X4) -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X5 X4 X3, (v2_struct_0 X3 -> False) -> X1 = X2 -> v2_parsp_1 X3 -> v1_parsp_2 X3 -> l1_parsp_1 X3 -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> r2_parsp_2 X3 X1 X2 X4 X5 -> False)
  -> (forall X2 X1 X5 X4 X3, (v2_struct_0 X3 -> False) -> X1 = X2 -> v2_parsp_1 X3 -> v1_parsp_2 X3 -> l1_parsp_1 X3 -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> r2_parsp_2 X3 X1 X4 X5 X2 -> False)
  -> (forall X2 X1 X5 X4 X3, (v2_struct_0 X3 -> False) -> X1 = X2 -> v2_parsp_1 X3 -> v1_parsp_2 X3 -> l1_parsp_1 X3 -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> r2_parsp_2 X3 X2 X4 X1 X5 -> False)
  -> (forall X2 X1 X5 X4 X3, (v2_struct_0 X3 -> False) -> X1 = X2 -> v2_parsp_1 X3 -> v1_parsp_2 X3 -> l1_parsp_1 X3 -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> r2_parsp_2 X3 X4 X1 X2 X5 -> False)
  -> (forall X2 X1 X5 X4 X3, (v2_struct_0 X3 -> False) -> X1 = X2 -> v2_parsp_1 X3 -> v1_parsp_2 X3 -> l1_parsp_1 X3 -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> r2_parsp_2 X3 X4 X1 X5 X2 -> False)
  -> (forall X2 X1 X5 X4 X3, (v2_struct_0 X3 -> False) -> X1 = X2 -> v2_parsp_1 X3 -> v1_parsp_2 X3 -> l1_parsp_1 X3 -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> r2_parsp_2 X3 X4 X5 X1 X2 -> False)
  -> (forall X3 X2 X4 X1, (v2_struct_0 X1 -> False) -> (r1_parsp_1 X1 X2 X3 X2 X4 -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_parsp_2 X1 X2 X3 X4 -> False)
  -> (forall X4 X3 X1 X2 X5, (v2_struct_0 X5 -> False) -> (r1_parsp_1 X5 X1 X3 X2 X4 -> False) -> X3 = X4 -> X1 = X2 -> v2_parsp_1 X5 -> l1_parsp_1 X5 -> m1_subset_1 X4 (u1_struct_0 X5) -> m1_subset_1 X3 (u1_struct_0 X5) -> m1_subset_1 X2 (u1_struct_0 X5) -> m1_subset_1 X1 (u1_struct_0 X5) -> False)
  -> (forall X4 X3 X1 X2 X5, (v2_struct_0 X5 -> False) -> (r1_parsp_1 X5 X1 X3 X4 X2 -> False) -> X3 = X4 -> X1 = X2 -> v2_parsp_1 X5 -> l1_parsp_1 X5 -> m1_subset_1 X4 (u1_struct_0 X5) -> m1_subset_1 X3 (u1_struct_0 X5) -> m1_subset_1 X2 (u1_struct_0 X5) -> m1_subset_1 X1 (u1_struct_0 X5) -> False)
  -> (forall X2 X1 X4 X5 X3, (v2_struct_0 X3 -> False) -> (r1_parsp_1 X3 X1 X2 X4 X5 -> False) -> X1 = X2 -> v2_parsp_1 X3 -> l1_parsp_1 X3 -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> False)
  -> (forall X2 X1 X4 X5 X3, (v2_struct_0 X3 -> False) -> (r1_parsp_1 X3 X4 X5 X1 X2 -> False) -> X1 = X2 -> v2_parsp_1 X3 -> l1_parsp_1 X3 -> m1_subset_1 X5 (u1_struct_0 X3) -> m1_subset_1 X4 (u1_struct_0 X3) -> m1_subset_1 X2 (u1_struct_0 X3) -> m1_subset_1 X1 (u1_struct_0 X3) -> False)
  -> (forall X2 X3 X4 X1, (v2_struct_0 X1 -> False) -> (r1_parsp_2 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk16_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (r1_parsp_2 X1 X2 X3 (esk17_3 X1 X2 X3) -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk17_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (esk17_3 X1 X2 X3) = X2 -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (esk17_3 X1 X2 X3) = X3 -> v2_parsp_1 X1 -> v1_parsp_2 X1 -> l1_parsp_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_parsp_1 X1 -> False)
  -> (r1_parsp_1 esk1_0 esk6_0 esk8_0 esk7_0 esk9_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v2_struct_0 esk14_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> ((r2_parsp_2 esk1_0 esk4_0 esk5_0 esk8_0 esk9_0 -> False) -> False)
  -> ((r2_parsp_2 esk1_0 esk2_0 esk3_0 esk6_0 esk7_0 -> False) -> False)
  -> ((r2_parsp_2 esk1_0 esk2_0 esk3_0 esk4_0 esk5_0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk12_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk9_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk8_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk7_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk11_0 -> False) -> False)
  -> ((l1_parsp_1 esk14_0 -> False) -> False)
  -> ((l1_parsp_1 esk10_0 -> False) -> False)
  -> ((l1_parsp_1 esk1_0 -> False) -> False)
  -> ((v1_parsp_2 esk1_0 -> False) -> False)
  -> ((v2_parsp_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
