(** $I sig/MizarPreamble.mgs **)

Theorem l19_homothet:
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk5_0:set,
 forall esk2_0:set,
 forall epred2_1:set -> prop,
 forall v2_diraf:set -> prop,
 forall v4_aff_2:set -> prop,
 forall l1_analoaf:set -> prop,
 forall v1_diraf:set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk12_1:set -> set,
 forall esk15_1:set -> set,
 forall esk13_1:set -> set,
 forall esk14_1:set -> set,
 forall k1_funct_1:set -> set -> set,
 forall v2_struct_0:set -> prop,
 forall esk18_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk17_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall v8_struct_0:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk8_1:set -> set,
 forall esk6_0:set,
 forall esk7_0:set,
 forall k1_xboole_0:set,
 forall r1_tarski:set -> set -> prop,
 forall esk16_1:set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk9_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall esk10_1:set -> set,
 forall esk11_1:set -> set,
 forall v6_transgeo:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall esk19_2:set -> set -> set,
 forall esk20_2:set -> set -> set,
 forall v3_funct_2:set -> set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall epred3_6:set -> set -> set -> set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall r1_aff_1:set -> set -> set -> set -> prop,
 forall epred1_7:set -> set -> set -> set -> set -> set -> set -> prop,
 forall u1_struct_0:set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall esk21_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall esk22_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall r2_analoaf:set -> set -> set -> set -> set -> prop,
     (forall X4 X7 X6 X2 X5 X3 X1, (r2_analoaf X1 X6 X3 X5 X2 -> False) -> (r2_analoaf X1 (esk21_7 X2 X3 X4 X5 X6 X7 X1) X3 (esk22_7 X2 X3 X4 X5 X6 X7 X1) X2 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X4 X3) = X2 -> epred1_7 X1 X7 X6 X5 X2 X3 X4 -> False)
  -> (forall X5 X7 X2 X3 X6 X4 X1, (r2_analoaf X1 X2 X4 X6 X3 -> False) -> (r2_analoaf X1 X2 (esk21_7 X3 X4 X5 X6 X2 X7 X1) X6 (esk22_7 X3 X4 X5 X6 X2 X7 X1) -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X5 X4) = X3 -> epred1_7 X1 X7 X2 X6 X3 X4 X5 -> False)
  -> (forall X6 X7 X5 X1 X3 X4 X2, (r2_analoaf X1 (esk21_7 X2 X3 X4 X5 X6 X7 X1) X3 (esk22_7 X2 X3 X4 X5 X6 X7 X1) X2 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X4 X3) = X2 -> r1_aff_1 X1 X7 X6 X3 -> epred1_7 X1 X7 X6 X5 X2 X3 X4 -> False)
  -> (forall X2 X7 X6 X1 X4 X5 X3, (r2_analoaf X1 X2 (esk21_7 X3 X4 X5 X6 X2 X7 X1) X6 (esk22_7 X3 X4 X5 X6 X2 X7 X1) -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X5 X4) = X3 -> r1_aff_1 X1 X7 X2 X4 -> epred1_7 X1 X7 X2 X6 X3 X4 X5 -> False)
  -> (forall X5 X2 X7 X3 X6 X4 X1, (r2_analoaf X1 X7 X4 X6 X3 -> False) -> (r1_aff_1 X1 X2 (esk21_7 X3 X4 X5 X6 X7 X2 X1) (esk22_7 X3 X4 X5 X6 X7 X2 X1) -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X5 X4) = X3 -> epred1_7 X1 X2 X7 X6 X3 X4 X5 -> False)
  -> (forall X4 X6 X5 X7 X3 X2 X1, (r1_aff_1 X1 X7 X3 X2 -> False) -> (r2_analoaf X1 (esk21_7 X2 X3 X4 X5 X6 X7 X1) X3 (esk22_7 X2 X3 X4 X5 X6 X7 X1) X2 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X4 X3) = X2 -> epred1_7 X1 X7 X6 X5 X2 X3 X4 -> False)
  -> (forall X5 X2 X6 X7 X4 X3 X1, (r1_aff_1 X1 X7 X4 X3 -> False) -> (r2_analoaf X1 X2 (esk21_7 X3 X4 X5 X6 X2 X7 X1) X6 (esk22_7 X3 X4 X5 X6 X2 X7 X1) -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X5 X4) = X3 -> epred1_7 X1 X7 X2 X6 X3 X4 X5 -> False)
  -> (forall X7 X2 X6 X1 X4 X5 X3, (r1_aff_1 X1 X2 (esk21_7 X3 X4 X5 X6 X7 X2 X1) (esk22_7 X3 X4 X5 X6 X7 X2 X1) -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X5 X4) = X3 -> r1_aff_1 X1 X2 X7 X4 -> epred1_7 X1 X2 X7 X6 X3 X4 X5 -> False)
  -> (forall X5 X7 X6 X2 X4 X3 X1, (r1_aff_1 X1 X2 X4 X3 -> False) -> (r1_aff_1 X1 X2 (esk21_7 X3 X4 X5 X6 X7 X2 X1) (esk22_7 X3 X4 X5 X6 X7 X2 X1) -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X5 X4) = X3 -> epred1_7 X1 X2 X7 X6 X3 X4 X5 -> False)
  -> (forall X6 X2 X3 X4 X7 X5 X1, (r2_analoaf X1 X3 X5 X7 X4 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X6 X5) = X4 -> epred1_7 X1 X2 X3 X7 X4 X5 X6 -> r1_aff_1 X1 X2 X3 (esk21_7 X4 X5 X6 X7 X3 X2 X1) -> False)
  -> (forall X3 X2 X7 X1 X5 X6 X4, (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X6 X5) = X4 -> r1_aff_1 X1 X2 X3 X5 -> epred1_7 X1 X2 X3 X7 X4 X5 X6 -> r1_aff_1 X1 X2 X3 (esk21_7 X4 X5 X6 X7 X3 X2 X1) -> False)
  -> (forall X6 X3 X7 X2 X5 X4 X1, (r1_aff_1 X1 X2 X5 X4 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X6 X5) = X4 -> epred1_7 X1 X2 X3 X7 X4 X5 X6 -> r1_aff_1 X1 X2 X3 (esk21_7 X4 X5 X6 X7 X3 X2 X1) -> False)
  -> (forall X3 X6 X5 X1 X4 X2 X7, (r2_analoaf X7 X5 X2 X4 X1 -> False) -> (m1_subset_1 (esk22_7 X1 X2 X3 X4 X5 X6 X7) (u1_struct_0 X7) -> False) -> (k3_funct_2 (u1_struct_0 X7) (u1_struct_0 X7) X3 X2) = X1 -> epred1_7 X7 X6 X5 X4 X1 X2 X3 -> False)
  -> (forall X3 X6 X5 X1 X4 X2 X7, (r2_analoaf X7 X5 X2 X4 X1 -> False) -> (m1_subset_1 (esk21_7 X1 X2 X3 X4 X5 X6 X7) (u1_struct_0 X7) -> False) -> (k3_funct_2 (u1_struct_0 X7) (u1_struct_0 X7) X3 X2) = X1 -> epred1_7 X7 X6 X5 X4 X1 X2 X3 -> False)
  -> (forall X5 X6 X4 X7 X2 X3 X1, (m1_subset_1 (esk22_7 X1 X2 X3 X4 X5 X6 X7) (u1_struct_0 X7) -> False) -> (k3_funct_2 (u1_struct_0 X7) (u1_struct_0 X7) X3 X2) = X1 -> r1_aff_1 X7 X6 X5 X2 -> epred1_7 X7 X6 X5 X4 X1 X2 X3 -> False)
  -> (forall X5 X6 X4 X7 X2 X3 X1, (m1_subset_1 (esk21_7 X1 X2 X3 X4 X5 X6 X7) (u1_struct_0 X7) -> False) -> (k3_funct_2 (u1_struct_0 X7) (u1_struct_0 X7) X3 X2) = X1 -> r1_aff_1 X7 X6 X5 X2 -> epred1_7 X7 X6 X5 X4 X1 X2 X3 -> False)
  -> (forall X3 X5 X4 X6 X2 X1 X7, (r1_aff_1 X7 X6 X2 X1 -> False) -> (m1_subset_1 (esk22_7 X1 X2 X3 X4 X5 X6 X7) (u1_struct_0 X7) -> False) -> (k3_funct_2 (u1_struct_0 X7) (u1_struct_0 X7) X3 X2) = X1 -> epred1_7 X7 X6 X5 X4 X1 X2 X3 -> False)
  -> (forall X3 X5 X4 X6 X2 X1 X7, (r1_aff_1 X7 X6 X2 X1 -> False) -> (m1_subset_1 (esk21_7 X1 X2 X3 X4 X5 X6 X7) (u1_struct_0 X7) -> False) -> (k3_funct_2 (u1_struct_0 X7) (u1_struct_0 X7) X3 X2) = X1 -> epred1_7 X7 X6 X5 X4 X1 X2 X3 -> False)
  -> (forall X5 X3 X2 X7 X6 X1 X4 X9 X8, ((k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X9 X4) = X8 -> False) -> (r1_aff_1 X1 X2 X3 X5 -> False) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X5 X6 -> r1_aff_1 X1 X2 X3 X8 -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X5 X4 X6 X8 -> r2_analoaf X1 X3 X5 X7 X6 -> epred1_7 X1 X2 X3 X7 X8 X4 X9 -> False)
  -> (forall X3 X2 X6 X1 X4 X7 X5, ((k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X7 X4) = X5 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> r1_aff_1 X1 X2 X4 X5 -> r2_analoaf X1 X3 X4 X6 X5 -> epred1_7 X1 X2 X3 X6 X5 X4 X7 -> False)
  -> (forall X5 X6 X7 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (r2_analoaf X1 X3 X4 X5 X6 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X7 X4) = X6 -> epred1_7 X1 X2 X3 X5 X6 X4 X7 -> False)
  -> (forall X5 X6 X7 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (r2_analoaf X1 X3 X5 X6 X4 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X7 X5) = X4 -> epred1_7 X1 X2 X3 X6 X4 X5 X7 -> False)
  -> (forall X6 X5 X7 X2 X3 X4 X1, (r1_aff_1 X1 X2 X3 X4 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X6 X5) = X4 -> r1_aff_1 X1 X2 X3 X5 -> epred1_7 X1 X2 X3 X7 X4 X5 X6 -> False)
  -> (forall X3 X7 X6 X2 X4 X5 X1, (r1_aff_1 X1 X2 X4 X5 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X6 X4) = X5 -> epred1_7 X1 X2 X3 X7 X5 X4 X6 -> False)
  -> (forall X3 X7 X6 X2 X5 X4 X1, (r1_aff_1 X1 X2 X5 X4 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X6 X5) = X4 -> epred1_7 X1 X2 X3 X7 X4 X5 X6 -> False)
  -> (forall X2 X1, (epred1_7 esk1_0 esk2_0 esk3_0 esk4_0 X2 X1 esk5_0 -> False) -> m1_subset_1 X2 (u1_struct_0 esk1_0) -> m1_subset_1 X1 (u1_struct_0 esk1_0) -> False)
  -> (forall X3 X6 X4 X7 X5 X1 X2 X8, (X2 = X8 -> False) -> (X2 = X3 -> False) -> (r1_aff_1 X1 X2 X3 X5 -> False) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X5 X6 -> r1_aff_1 X1 X2 X3 X8 -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X5 X4 X6 X8 -> r2_analoaf X1 X3 X5 X7 X6 -> epred3_6 X8 X7 X3 X4 X2 X1 -> False)
  -> (forall X1 X11 X7 X6 X8 X4 X12 X10 X5 X9 X2 X3, (X2 = X3 -> False) -> (r1_aff_1 X1 X2 X3 X11 -> False) -> (r1_aff_1 X1 X2 X3 X9 -> False) -> (r2_analoaf X1 X4 X7 X6 X8 -> False) -> epred2_1 X1 -> m1_subset_1 X12 (u1_struct_0 X1) -> m1_subset_1 X11 (u1_struct_0 X1) -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X11 X12 -> r1_aff_1 X1 X2 X9 X10 -> r1_aff_1 X1 X2 X3 X8 -> r1_aff_1 X1 X2 X3 X7 -> r1_aff_1 X1 X2 X3 X6 -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X11 X7 X12 X8 -> r2_analoaf X1 X9 X4 X10 X6 -> r2_analoaf X1 X3 X11 X5 X12 -> r2_analoaf X1 X3 X9 X5 X10 -> False)
  -> (forall X3 X6 X4 X1 X2 X5, (X2 = X5 -> False) -> (X2 = X3 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> r1_aff_1 X1 X2 X4 X5 -> r2_analoaf X1 X3 X4 X6 X5 -> epred3_6 X5 X6 X3 X4 X2 X1 -> False)
  -> (forall X1 X5 X10 X4 X8 X6 X7 X9 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X9 -> False) -> (r1_aff_1 X1 X2 X3 X5 -> False) -> (r2_analoaf X1 X5 X7 X6 X8 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v4_aff_2 X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X9 X10 -> r1_aff_1 X1 X2 X5 X6 -> r1_aff_1 X1 X2 X3 X8 -> r1_aff_1 X1 X2 X3 X7 -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X9 X7 X10 X8 -> r2_analoaf X1 X3 X9 X4 X10 -> r2_analoaf X1 X3 X5 X4 X6 -> False)
  -> (forall X1 X7 X10 X4 X5 X8 X6 X9 X2 X3, (X2 = X3 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X9 -> False) -> (r1_aff_1 X1 X2 X3 X7 -> False) -> (r2_analoaf X1 X5 X7 X6 X8 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v4_aff_2 X1 -> m1_subset_1 X10 (u1_struct_0 X1) -> m1_subset_1 X9 (u1_struct_0 X1) -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X9 X10 -> r1_aff_1 X1 X2 X7 X8 -> r1_aff_1 X1 X2 X3 X6 -> r1_aff_1 X1 X2 X3 X5 -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X9 X5 X10 X6 -> r2_analoaf X1 X3 X9 X4 X10 -> r2_analoaf X1 X3 X7 X4 X8 -> False)
  -> (forall X7 X3 X2 X6 X8 X4 X5 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X7 -> False) -> (r1_aff_1 X1 X2 X3 X5 -> False) -> (r2_analoaf X1 X5 X7 X6 X8 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> v4_aff_2 X1 -> m1_subset_1 X8 (u1_struct_0 X1) -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X7 X8 -> r1_aff_1 X1 X2 X5 X6 -> r1_aff_1 X1 X2 X3 X4 -> r2_analoaf X1 X3 X7 X4 X8 -> r2_analoaf X1 X3 X5 X4 X6 -> False)
  -> (forall X4 X2 X6 X3 X5 X1, (v7_struct_0 X1 -> False) -> (epred3_6 X5 X6 X3 X4 X2 X1 -> False) -> X2 = X4 -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X5 X2 X3 X4 X6 X7, (X6 = X7 -> False) -> (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X7 (u1_struct_0 X1) -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X7 -> r1_aff_1 X1 X2 X4 X6 -> r1_aff_1 X1 X2 X3 X5 -> r2_analoaf X1 X3 X4 X5 X7 -> r2_analoaf X1 X3 X4 X5 X6 -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v6_transgeo X2 X1 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> r2_analoaf X1 (esk19_2 X1 X2) (esk20_2 X1 X2) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (esk19_2 X1 X2)) (k3_funct_2 (u1_struct_0 X1) (u1_struct_0 X1) X2 (esk20_2 X1 X2)) -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X2 X3 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X4 X5 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X3 X2 X5 X4 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X4 X5 X3 X2 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X2 X3 -> False)
  -> (forall X5 X3 X2 X4 X1, (v7_struct_0 X1 -> False) -> (r2_analoaf X1 X2 X3 X4 X5 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r2_analoaf X1 X5 X4 X3 X2 -> False)
  -> (forall X1 X4 X3 X2, (v7_struct_0 X2 -> False) -> (r2_analoaf X2 X3 X4 (k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X2) X1 X3) (k3_funct_2 (u1_struct_0 X2) (u1_struct_0 X2) X1 X4) -> False) -> v1_diraf X2 -> l1_analoaf X2 -> v1_funct_1 X1 -> v6_transgeo X1 X2 -> m1_subset_1 X4 (u1_struct_0 X2) -> m1_subset_1 X3 (u1_struct_0 X2) -> v1_funct_2 X1 (u1_struct_0 X2) (u1_struct_0 X2) -> v3_funct_2 X1 (u1_struct_0 X2) (u1_struct_0 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X2) (u1_struct_0 X2))) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> r2_analoaf X1 (esk12_1 X1) (esk14_1 X1) (esk13_1 X1) (esk15_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (r2_analoaf X1 (esk10_1 X1) (esk14_1 X1) (esk11_1 X1) (esk15_1 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (r2_analoaf X1 (esk10_1 X1) (esk12_1 X1) (esk11_1 X1) (esk13_1 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> ((k3_funct_2 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) esk5_0 esk2_0) = esk2_0 -> (k3_funct_2 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) esk5_0 esk3_0) = esk4_0 -> v6_transgeo esk5_0 esk1_0 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X2 X4 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X2 X4 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X3 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X2 X3 -> False)
  -> (forall X4 X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X4 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_aff_1 X1 X4 X3 X2 -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v6_transgeo X2 X1 -> False) -> (m1_subset_1 (esk20_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X2 X1, (v7_struct_0 X1 -> False) -> (v6_transgeo X2 X1 -> False) -> (m1_subset_1 (esk19_2 X1 X2) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> l1_analoaf X1 -> v1_funct_1 X2 -> v1_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> v3_funct_2 X2 (u1_struct_0 X1) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1))) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> r1_aff_1 X1 (esk9_1 X1) (esk10_1 X1) (esk14_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> r1_aff_1 X1 (esk9_1 X1) (esk10_1 X1) (esk12_1 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X2 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X2 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (v7_struct_0 X1 -> False) -> (r1_aff_1 X1 X2 X3 X3 -> False) -> v1_diraf X1 -> l1_analoaf X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (r1_aff_1 X1 (esk9_1 X1) (esk14_1 X1) (esk15_1 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (r1_aff_1 X1 (esk9_1 X1) (esk12_1 X1) (esk13_1 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (r1_aff_1 X1 (esk9_1 X1) (esk10_1 X1) (esk11_1 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk15_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk13_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk12_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk11_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (v4_aff_2 X1 -> False) -> (m1_subset_1 (esk9_1 X1) (u1_struct_0 X1) -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, l1_struct_0 X1 -> v2_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (epred2_1 X1 -> False) -> v1_diraf X1 -> v2_diraf X1 -> l1_analoaf X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk17_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk16_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v7_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v2_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_analoaf X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v7_struct_0 esk1_0 -> False)
  -> (esk3_0 = esk2_0 -> False)
  -> ((r1_aff_1 esk1_0 esk2_0 esk3_0 esk4_0 -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0))) -> False) -> False)
  -> ((v3_funct_2 esk5_0 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) -> False) -> False)
  -> ((v1_funct_2 esk5_0 (u1_struct_0 esk1_0) (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_struct_0 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((l1_struct_0 esk7_0 -> False) -> False)
  -> ((v4_aff_2 esk1_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((l1_analoaf esk6_0 -> False) -> False)
  -> ((l1_analoaf esk1_0 -> False) -> False)
  -> ((v2_diraf esk1_0 -> False) -> False)
  -> ((v1_diraf esk1_0 -> False) -> False)
  -> False.
Admitted.
