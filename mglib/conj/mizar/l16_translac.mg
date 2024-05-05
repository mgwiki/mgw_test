(** $I sig/MizarPreamble.mgs **)

Theorem l16_translac:
 forall esk27_5:set -> set -> set -> set -> set -> set,
 forall esk26_5:set -> set -> set -> set -> set -> set,
 forall esk25_5:set -> set -> set -> set -> set -> set,
 forall epred1_1:set -> prop,
 forall esk35_5:set -> set -> set -> set -> set -> set,
 forall esk34_4:set -> set -> set -> set -> set,
 forall esk33_4:set -> set -> set -> set -> set,
 forall esk24_3:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall l1_struct_0:set -> prop,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall v2_struct_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall esk29_1:set -> set,
 forall k1_xboole_0:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v3_relat_1:set -> prop,
 forall esk1_0:set,
 forall esk7_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk22_0:set,
 forall esk21_0:set,
 forall esk15_0:set,
 forall esk13_1:set -> set,
 forall esk20_0:set,
 forall esk17_0:set,
 forall esk11_0:set,
 forall esk12_0:set,
 forall esk16_0:set,
 forall esk14_0:set,
 forall esk18_0:set,
 forall esk6_0:set,
 forall esk4_0:set,
 forall esk8_0:set,
 forall esk9_0:set,
 forall esk10_0:set,
 forall esk19_0:set,
 forall esk23_0:set,
 forall esk5_0:set,
 forall v2_relat_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall esk28_1:set -> set,
 forall v4_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk31_1:set -> set,
 forall esk32_1:set -> set,
 forall esk30_1:set -> set,
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall v2_diraf:set -> prop,
 forall v11_aff_2:set -> prop,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall l1_analoaf:set -> prop,
 forall v1_diraf:set -> prop,
 forall v7_struct_0:set -> prop,
     (forall X3 X2 X7 X6 X5 X4 X8 X1 X9 X10, (X9 = X10 -> False) -> (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X5 X6 X7 -> False) -> (r1_aff_1 X1 X2 X3 X7 -> False) -> (r1_aff_1 X1 X2 X3 X5 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v11_aff_2 X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X7 X8 X4 X10 -> r2_analoaf X1 X7 X4 X8 X10 -> r2_analoaf X1 X5 X6 X4 X9 -> r2_analoaf X1 X5 X4 X6 X9 -> r2_analoaf X1 X2 X7 X3 X8 -> r2_analoaf X1 X2 X5 X3 X6 -> r2_analoaf X1 X2 X3 X7 X8 -> r2_analoaf X1 X2 X3 X5 X6 -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (r2_analoaf X1 X2 X5 X3 X4 -> False) -> (r1_aff_1 X1 (esk25_5 X1 X2 X3 X4 X5) (esk26_5 X1 X2 X3 X4 X5) (esk27_5 X1 X2 X3 X4 X5) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X4 X3 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (r2_analoaf X1 X2 X5 X3 X4 -> False) -> (esk27_5 X1 X2 X3 X4 X5) = (esk26_5 X1 X2 X3 X4 X5) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X4 X3 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (r2_analoaf X1 X2 X5 X3 X4 -> False) -> (esk27_5 X1 X2 X3 X4 X5) = (esk25_5 X1 X2 X3 X4 X5) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X4 X3 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (r2_analoaf X1 X2 X5 X3 X4 -> False) -> (esk26_5 X1 X2 X3 X4 X5) = (esk25_5 X1 X2 X3 X4 X5) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X4 X3 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X3 X4 X5 X6, (X5 = X6 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X4 X3 X6 -> r2_analoaf X1 X2 X4 X3 X5 -> r2_analoaf X1 X2 X3 X4 X6 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (r2_analoaf X1 X2 X5 X3 X4 -> False) -> (m1_subset_1 (esk27_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X4 X3 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (r2_analoaf X1 X2 X5 X3 X4 -> False) -> (m1_subset_1 (esk26_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X4 X3 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X3 X2 X5 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (r2_analoaf X1 X2 X5 X3 X4 -> False) -> (m1_subset_1 (esk25_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X4 X3 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X5 X3 X4, (X3 = X4 -> False) -> (r2_analoaf X1 X2 X3 X3 (esk35_5 X1 X3 X2 X4 X5) -> False) -> epred1_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X3 X3 X5 -> False)
  -> (forall X1 X4 X2 X3 X5, (X3 = X5 -> False) -> (r2_analoaf X1 X2 X3 X4 (esk35_5 X1 X5 X2 X3 X4) -> False) -> epred1_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X5 X5 X4 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X4 X7 X6 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X2 X3 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X2 X7 X6 X3 X4 X5, (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X6 X7 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X6 X7 X4 X5 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X1 X5 X6 X7 X4 X2 X3, (X2 = X3 -> False) -> (r2_analoaf X1 X4 X5 X6 X7 -> False) -> epred1_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X6 X7 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X5 X2 X3 X4 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X3 X2 X5 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X3 X5 X2 X4 -> r2_analoaf X1 X3 X2 X5 X4 -> False)
  -> (forall X2 X5 X4 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X4 X5 X2 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X4 X5 X2 X3 -> r2_analoaf X1 X4 X2 X5 X3 -> False)
  -> (forall X3 X4 X5 X2 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X5 X4 X3 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X5 X4 X3 X2 -> r2_analoaf X1 X5 X3 X4 X2 -> False)
  -> (forall X1 X3 X5 X2 X4, (X2 = X4 -> False) -> (m1_subset_1 (esk35_5 X1 X2 X3 X4 X5) (u1_struct_0 X1) -> False) -> epred1_1 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X2 X2 X5 -> False)
  -> (forall X6 X5 X7 X3 X4 X2 X1, (r2_analoaf X1 X3 X2 X3 X4 -> False) -> epred1_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X2 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X3 X2 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X3 X2 -> False)
  -> (forall X1 X4 X5 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X2 X3 X4 X5 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X2 X4 -> False)
  -> (forall X1, epred1_1 X1 -> r2_analoaf X1 (esk30_1 X1) (esk31_1 X1) (esk30_1 X1) (esk32_1 X1) -> False)
  -> (forall X4 X3 X2 X1, (r2_analoaf X1 X2 X3 X4 (esk34_4 X1 X2 X3 X4) -> False) -> epred1_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r2_analoaf X1 X2 X3 X4 (esk34_4 X1 X2 X4 X3) -> False) -> epred1_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (r2_analoaf X1 X2 X3 X4 (esk33_4 X1 X2 X4 X3) -> False) -> epred1_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X2 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X1 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X4 X5 X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X3 X6 -> r1_aff_1 X1 X2 X3 X5 -> r1_aff_1 X1 X2 X3 X4 -> False)
  -> (forall X1 X4 X5 X6 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X4 X5 X6 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X5 X3 -> r1_aff_1 X1 X4 X5 X2 -> r1_aff_1 X1 X2 X3 X6 -> False)
  -> (forall X6 X4 X5 X7 X2 X3 X1, (r2_analoaf X1 X2 X3 X3 X2 -> False) -> epred1_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X6 X5 X7 X2 X3 X4 X1, (r2_analoaf X1 X2 X3 X4 X4 -> False) -> epred1_1 X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X1 X2 X3 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 (esk24_3 X1 X2 X3) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X5 X6 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X3 X2 -> False)
  -> (forall X4 X1 X2 X3 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk24_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X5 X6 -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X2 -> False) -> (esk24_3 X2 X1 X3) = X1 -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X6 (u1_struct_0 X2) -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X4 X5 X6 -> False)
  -> (forall X4 X2 X3 X1 X5 X6, (X5 = X6 -> False) -> (X4 = X6 -> False) -> (X4 = X5 -> False) -> (v7_struct_0 X2 -> False) -> (esk24_3 X2 X3 X1) = X1 -> v1_diraf X2 -> l1_analoaf X2 -> m1_subset_1 X6 (u1_struct_0 X2) -> m1_subset_1 X5 (u1_struct_0 X2) -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> r1_aff_1 X2 X4 X5 X6 -> False)
  -> (forall X4 X3 X2 X1, (m1_subset_1 (esk34_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> epred1_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X2 X1, (m1_subset_1 (esk33_4 X1 X2 X3 X4) (u1_struct_0 X1) -> False) -> epred1_1 X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X4 X3 X1 X2, (esk33_4 X2 X3 X1 X4) = X1 -> epred1_1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> m1_subset_1 X1 (u1_struct_0 X2) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (esk32_1 X1) (u1_struct_0 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk31_1 X1) (u1_struct_0 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) (u1_struct_0 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk29_1 X1) (u1_struct_0 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (m1_subset_1 (esk28_1 X1) (u1_struct_0 X1) -> False) -> epred1_1 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (epred1_1 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (esk29_1 X1) = (esk28_1 X1) -> epred1_1 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r1_aff_1 esk1_0 esk2_0 esk3_0 esk7_0 -> False)
  -> (r1_aff_1 esk1_0 esk2_0 esk3_0 esk5_0 -> False)
  -> (v3_funct_1 esk22_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk19_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (esk10_0 = esk9_0 -> False)
  -> (esk3_0 = esk2_0 -> False)
  -> ((r2_analoaf esk1_0 esk7_0 esk8_0 esk4_0 esk10_0 -> False) -> False)
  -> ((r2_analoaf esk1_0 esk7_0 esk4_0 esk8_0 esk10_0 -> False) -> False)
  -> ((r2_analoaf esk1_0 esk5_0 esk6_0 esk4_0 esk9_0 -> False) -> False)
  -> ((r2_analoaf esk1_0 esk5_0 esk4_0 esk6_0 esk9_0 -> False) -> False)
  -> ((r2_analoaf esk1_0 esk2_0 esk7_0 esk3_0 esk8_0 -> False) -> False)
  -> ((r2_analoaf esk1_0 esk2_0 esk5_0 esk3_0 esk6_0 -> False) -> False)
  -> ((r2_analoaf esk1_0 esk2_0 esk3_0 esk7_0 esk8_0 -> False) -> False)
  -> ((r2_analoaf esk1_0 esk2_0 esk3_0 esk5_0 esk6_0 -> False) -> False)
  -> ((r1_aff_1 esk1_0 esk2_0 esk3_0 esk4_0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk10_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk9_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk8_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk7_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v4_funct_1 esk23_0 -> False) -> False)
  -> ((v2_relat_1 esk21_0 -> False) -> False)
  -> ((v2_relat_1 esk20_0 -> False) -> False)
  -> ((v2_relat_1 esk18_0 -> False) -> False)
  -> ((v2_funct_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk20_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk14_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk20_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk16_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((l1_struct_0 esk12_0 -> False) -> False)
  -> ((v11_aff_2 esk1_0 -> False) -> False)
  -> ((l1_analoaf esk11_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v2_diraf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
