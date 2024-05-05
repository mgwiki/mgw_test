(** $I sig/MizarPreamble.mgs **)

Theorem t19_midsp_2:
 forall k1_midsp_2:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v2_rlvect_1:set -> prop,
 forall v4_rlvect_1:set -> prop,
 forall v1_funct_1:set -> prop,
 forall r1_midsp_2:set -> set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall l2_algstr_0:set -> prop,
 forall v3_rlvect_1:set -> prop,
 forall v13_algstr_0:set -> prop,
 forall v2_struct_0:set -> prop,
 forall k4_algstr_0:set -> set -> set,
 forall esk26_5:set -> set -> set -> set -> set -> set,
 forall v12_vectsp_1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v7_struct_0:set -> prop,
 forall esk21_1:set -> set,
 forall l1_struct_0:set -> prop,
 forall esk20_1:set -> set,
 forall v13_struct_0:set -> set -> prop,
 forall np__1:set,
 forall k1_xboole_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall esk23_0:set,
 forall esk25_0:set,
 forall esk19_0:set,
 forall esk1_0:set,
 forall esk17_2:set -> set -> set,
 forall esk16_1:set -> set,
 forall esk11_0:set,
 forall esk12_0:set,
 forall esk14_0:set,
 forall esk13_0:set,
 forall esk18_0:set,
 forall esk15_0:set,
 forall esk3_0:set,
 forall esk22_0:set,
 forall esk2_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk7_0:set,
 forall esk6_0:set,
 forall l2_struct_0:set -> prop,
 forall v2_midsp_2:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v8_struct_0:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall esk24_1:set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall l1_algstr_0:set -> prop,
 forall k3_rlvect_1:set -> set -> set -> set,
 forall k1_binop_1:set -> set -> set -> set,
 forall esk10_3:set -> set -> set -> set,
 forall esk8_3:set -> set -> set -> set,
 forall esk9_3:set -> set -> set -> set,
 forall k1_midsp_1:set -> set -> set -> set,
 forall l1_midsp_1:set -> prop,
 forall v1_midsp_2:set -> set -> set -> prop,
 forall epred1_3:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k1_algstr_0:set -> set -> set -> set,
 forall esk33_3:set -> set -> set -> set,
 forall esk32_3:set -> set -> set -> set,
 forall esk34_3:set -> set -> set -> set,
 forall esk27_3:set -> set -> set -> set,
 forall esk28_3:set -> set -> set -> set,
 forall esk31_3:set -> set -> set -> set,
 forall k2_binop_1:set -> set -> set -> set -> set -> set -> set,
 forall esk29_3:set -> set -> set -> set,
 forall esk30_3:set -> set -> set -> set,
 forall u1_struct_0:set -> set,
     (forall X4 X2 X1 X3, ((k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk29_3 X2 X3 X1) (esk31_3 X2 X3 X1)) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk29_3 X2 X3 X1) (esk30_3 X2 X3 X1)) -> False) -> (epred1_3 X1 X3 X2 -> False) -> (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk27_3 X2 X3 X1) X4) = (esk28_3 X2 X3 X1) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> m1_subset_1 X4 X2 -> False)
  -> (forall X3 X1 X2, ((k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk29_3 X2 X3 X1) (esk31_3 X2 X3 X1)) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk29_3 X2 X3 X1) (esk30_3 X2 X3 X1)) -> False) -> (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk28_3 X2 X3 X1) (u1_struct_0 X1) -> False) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> False)
  -> (forall X3 X1 X2, ((k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk29_3 X2 X3 X1) (esk31_3 X2 X3 X1)) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk29_3 X2 X3 X1) (esk30_3 X2 X3 X1)) -> False) -> (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk27_3 X2 X3 X1) X2 -> False) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> False)
  -> (forall X4 X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (esk31_3 X2 X3 X1) = (esk30_3 X2 X3 X1) -> (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk27_3 X2 X3 X1) X4) = (esk28_3 X2 X3 X1) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> m1_subset_1 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk31_3 X2 X3 X1) X2 -> False) -> (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk27_3 X2 X3 X1) X4) = (esk28_3 X2 X3 X1) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> m1_subset_1 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk30_3 X2 X3 X1) X2 -> False) -> (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk27_3 X2 X3 X1) X4) = (esk28_3 X2 X3 X1) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> m1_subset_1 X4 X2 -> False)
  -> (forall X4 X2 X3 X1, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk29_3 X2 X3 X1) X2 -> False) -> (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk27_3 X2 X3 X1) X4) = (esk28_3 X2 X3 X1) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> m1_subset_1 X4 X2 -> False)
  -> (forall X4 X8 X7 X2 X1 X6 X5 X3, ((k2_binop_1 X1 X1 (u1_struct_0 X2) X3 X7 X8) = (k1_midsp_2 X2 (k2_binop_1 X1 X1 (u1_struct_0 X2) X3 X5 X6)) -> False) -> (v2_struct_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X2) X3 X4 X6) = (k2_binop_1 X1 X1 (u1_struct_0 X2) X3 X6 X8) -> (k2_binop_1 X1 X1 (u1_struct_0 X2) X3 X4 X5) = (k2_binop_1 X1 X1 (u1_struct_0 X2) X3 X5 X7) -> v13_algstr_0 X2 -> v2_rlvect_1 X2 -> v3_rlvect_1 X2 -> v4_rlvect_1 X2 -> l2_algstr_0 X2 -> v1_funct_1 X3 -> m1_subset_1 X8 X1 -> m1_subset_1 X7 X1 -> m1_subset_1 X6 X1 -> m1_subset_1 X5 X1 -> m1_subset_1 X4 X1 -> r1_midsp_2 X1 X2 X3 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (u1_struct_0 X2))) -> False)
  -> (forall X3 X1 X2, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk28_3 X2 X3 X1) (u1_struct_0 X1) -> False) -> (esk31_3 X2 X3 X1) = (esk30_3 X2 X3 X1) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> False)
  -> (forall X3 X1 X2, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk27_3 X2 X3 X1) X2 -> False) -> (esk31_3 X2 X3 X1) = (esk30_3 X2 X3 X1) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> False)
  -> (forall X3 X1 X2, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk31_3 X2 X3 X1) X2 -> False) -> (m1_subset_1 (esk28_3 X2 X3 X1) (u1_struct_0 X1) -> False) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> False)
  -> (forall X3 X1 X2, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk30_3 X2 X3 X1) X2 -> False) -> (m1_subset_1 (esk28_3 X2 X3 X1) (u1_struct_0 X1) -> False) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> False)
  -> (forall X3 X1 X2, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk29_3 X2 X3 X1) X2 -> False) -> (m1_subset_1 (esk28_3 X2 X3 X1) (u1_struct_0 X1) -> False) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> False)
  -> (forall X3 X1 X2, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk27_3 X2 X3 X1) X2 -> False) -> (m1_subset_1 (esk31_3 X2 X3 X1) X2 -> False) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> False)
  -> (forall X3 X1 X2, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk27_3 X2 X3 X1) X2 -> False) -> (m1_subset_1 (esk30_3 X2 X3 X1) X2 -> False) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> False)
  -> (forall X3 X1 X2, (epred1_3 X1 X3 X2 -> False) -> (m1_subset_1 (esk27_3 X2 X3 X1) X2 -> False) -> (m1_subset_1 (esk29_3 X2 X3 X1) X2 -> False) -> (k1_algstr_0 X1 (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk33_3 X2 X3 X1)) (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk33_3 X2 X3 X1) (esk34_3 X2 X3 X1))) = (k2_binop_1 X2 X2 (u1_struct_0 X1) X3 (esk32_3 X2 X3 X1) (esk34_3 X2 X3 X1)) -> False)
  -> (forall X3 X6 X5 X1 X4 X2, ((k1_algstr_0 X5 (k2_binop_1 X2 X2 (u1_struct_0 X5) X6 X1 X3) (k2_binop_1 X2 X2 (u1_struct_0 X5) X6 X3 X4)) = (k2_binop_1 X2 X2 (u1_struct_0 X5) X6 X1 X4) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> epred1_3 X5 X6 X2 -> False)
  -> (forall X4 X1 X3 X2, ((k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk31_3 X1 X2 X3)) = (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk30_3 X1 X2 X3)) -> False) -> (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X3 X2, ((k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk31_3 X1 X2 X3)) = (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk30_3 X1 X2 X3)) -> False) -> (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X3 X2, ((k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk31_3 X1 X2 X3)) = (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk30_3 X1 X2 X3)) -> False) -> (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_midsp_2 X3 X1 X2 -> False) -> (k1_midsp_1 X1 (esk8_3 X1 X2 X3) (esk9_3 X1 X2 X3)) = (esk10_3 X1 X2 X3) -> (k2_binop_1 (u1_struct_0 X1) (u1_struct_0 X1) (u1_struct_0 X2) X3 (esk10_3 X1 X2 X3) (esk9_3 X1 X2 X3)) = (k2_binop_1 (u1_struct_0 X1) (u1_struct_0 X1) (u1_struct_0 X2) X3 (esk8_3 X1 X2 X3) (esk10_3 X1 X2 X3)) -> l2_algstr_0 X2 -> l1_midsp_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2))) -> False)
  -> (forall X2 X3 X1 X4 X6 X5, ((k1_midsp_1 X1 X4 X6) = X5 -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (k2_binop_1 (u1_struct_0 X1) (u1_struct_0 X1) (u1_struct_0 X2) X3 X4 X5) = (k2_binop_1 (u1_struct_0 X1) (u1_struct_0 X1) (u1_struct_0 X2) X3 X5 X6) -> l2_algstr_0 X2 -> l1_midsp_1 X1 -> v1_funct_1 X3 -> v1_midsp_2 X3 X1 X2 -> m1_subset_1 X6 (u1_struct_0 X1) -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> v1_funct_2 X3 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2))) -> False)
  -> (forall X2 X1 X5 X6 X3 X4, (X3 = X4 -> False) -> (k2_binop_1 X2 X2 (u1_struct_0 X5) X6 X1 X3) = (k2_binop_1 X2 X2 (u1_struct_0 X5) X6 X1 X4) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> epred1_3 X5 X6 X2 -> False)
  -> (forall X1 X3 X2 X5 X4, ((k4_algstr_0 X4 (k2_binop_1 X1 X1 (u1_struct_0 X4) X5 X3 X2)) = (k2_binop_1 X1 X1 (u1_struct_0 X4) X5 X2 X3) -> False) -> (v2_struct_0 X4 -> False) -> (v1_xboole_0 X1 -> False) -> v13_algstr_0 X4 -> v3_rlvect_1 X4 -> v4_rlvect_1 X4 -> l2_algstr_0 X4 -> v1_funct_1 X5 -> m1_subset_1 X3 X1 -> m1_subset_1 X2 X1 -> r1_midsp_2 X1 X4 X5 -> v1_funct_2 X5 (k2_zfmisc_1 X1 X1) (u1_struct_0 X4) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (u1_struct_0 X4))) -> False)
  -> (forall X1 X3 X2, ((k1_midsp_1 X1 (esk8_3 X1 X2 X3) (esk9_3 X1 X2 X3)) = (esk10_3 X1 X2 X3) -> False) -> ((k2_binop_1 (u1_struct_0 X1) (u1_struct_0 X1) (u1_struct_0 X2) X3 (esk10_3 X1 X2 X3) (esk9_3 X1 X2 X3)) = (k2_binop_1 (u1_struct_0 X1) (u1_struct_0 X1) (u1_struct_0 X2) X3 (esk8_3 X1 X2 X3) (esk10_3 X1 X2 X3)) -> False) -> (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_midsp_2 X3 X1 X2 -> False) -> l2_algstr_0 X2 -> l1_midsp_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2))) -> False)
  -> (forall X1 X6 X2 X3 X4 X5, ((k2_binop_1 (u1_struct_0 X1) (u1_struct_0 X1) (u1_struct_0 X5) X6 X2 X4) = (k2_binop_1 (u1_struct_0 X1) (u1_struct_0 X1) (u1_struct_0 X5) X6 X4 X3) -> False) -> (v2_struct_0 X5 -> False) -> (v2_struct_0 X1 -> False) -> (k1_midsp_1 X1 X2 X3) = X4 -> l2_algstr_0 X5 -> l1_midsp_1 X1 -> v1_funct_1 X6 -> v1_midsp_2 X6 X1 X5 -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> v1_funct_2 X6 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X5) -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X5))) -> False)
  -> (forall X3 X2 X1, ((k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk31_3 X1 X2 X3)) = (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk30_3 X1 X2 X3)) -> False) -> (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X3 X2 X1, ((k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk31_3 X1 X2 X3)) = (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk30_3 X1 X2 X3)) -> False) -> (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X3 X2 X1, ((k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk31_3 X1 X2 X3)) = (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk30_3 X1 X2 X3)) -> False) -> (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X1 X3 X2, ((k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk31_3 X1 X2 X3)) = (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk30_3 X1 X2 X3)) -> False) -> (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, ((k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk31_3 X1 X2 X3)) = (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk30_3 X1 X2 X3)) -> False) -> (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, ((k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk31_3 X1 X2 X3)) = (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk29_3 X1 X2 X3) (esk30_3 X1 X2 X3)) -> False) -> (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X6 X4 X5 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_binop_1 X1 X2 X4 X3 X5 X6) X4 -> False) -> v1_funct_1 X3 -> m1_subset_1 X6 X2 -> m1_subset_1 X5 X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X2) X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X4)) -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (esk31_3 X1 X2 X3) = (esk30_3 X1 X2 X3) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (esk31_3 X1 X2 X3) = (esk30_3 X1 X2 X3) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (esk31_3 X1 X2 X3) = (esk30_3 X1 X2 X3) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk31_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk31_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk31_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X4 X1 X2 X3, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (k2_binop_1 X1 X1 (u1_struct_0 X3) X2 (esk27_3 X1 X2 X3) X4) = (esk28_3 X1 X2 X3) -> m1_subset_1 X4 X1 -> False)
  -> (forall X5 X2 X3 X4 X1, ((k2_binop_1 X1 X1 (u1_struct_0 X2) X3 X4 (esk26_5 X1 X3 X2 X4 X5)) = X5 -> False) -> m1_subset_1 X4 X1 -> epred1_3 X2 X3 X1 -> m1_subset_1 X5 (u1_struct_0 X2) -> False)
  -> (forall X1 X6 X4 X5 X3 X2, ((k2_binop_1 X1 X2 X4 X3 X5 X6) = (k1_binop_1 X3 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> m1_subset_1 X6 X2 -> m1_subset_1 X5 X1 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X2) X4 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X2) X4)) -> False)
  -> (forall X5 X3 X2 X4 X1, (m1_subset_1 (esk26_5 X1 X2 X3 X4 X5) X1 -> False) -> m1_subset_1 X4 X1 -> epred1_3 X3 X2 X1 -> m1_subset_1 X5 (u1_struct_0 X3) -> False)
  -> (forall X4 X5 X1 X3 X2, ((k1_midsp_1 X1 X2 X3) = (k1_midsp_1 X1 X3 X2) -> False) -> (v2_struct_0 X4 -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X4 -> v3_rlvect_1 X4 -> v4_rlvect_1 X4 -> l2_algstr_0 X4 -> l1_midsp_1 X1 -> v1_funct_1 X5 -> v1_midsp_2 X5 X1 X4 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> r1_midsp_2 (u1_struct_0 X1) X4 X5 -> v1_funct_2 X5 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X4) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X4))) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_midsp_2 X3 X1 X2 -> False) -> (m1_subset_1 (esk10_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l2_algstr_0 X2 -> l1_midsp_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_midsp_2 X3 X1 X2 -> False) -> (m1_subset_1 (esk9_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l2_algstr_0 X2 -> l1_midsp_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2))) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v2_struct_0 X1 -> False) -> (v1_midsp_2 X3 X1 X2 -> False) -> (m1_subset_1 (esk8_3 X1 X2 X3) (u1_struct_0 X1) -> False) -> l2_algstr_0 X2 -> l1_midsp_1 X1 -> v1_funct_1 X3 -> v1_funct_2 X3 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 X1) (u1_struct_0 X1)) (u1_struct_0 X2))) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (v1_xboole_0 X3 -> False) -> (r1_midsp_2 X3 X1 X2 -> False) -> l2_algstr_0 X1 -> v1_funct_1 X2 -> epred1_3 X1 X2 X3 -> v1_funct_2 X2 (k2_zfmisc_1 X3 X3) (u1_struct_0 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X3) (u1_struct_0 X1))) -> False)
  -> (forall X1 X3 X2, (v2_struct_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (epred1_3 X2 X3 X1 -> False) -> l2_algstr_0 X2 -> v1_funct_1 X3 -> r1_midsp_2 X1 X2 X3 -> v1_funct_2 X3 (k2_zfmisc_1 X1 X1) (u1_struct_0 X2) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) (u1_struct_0 X2))) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (esk31_3 X1 X2 X3) = (esk30_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (esk31_3 X1 X2 X3) = (esk30_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> (esk31_3 X1 X2 X3) = (esk30_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (esk31_3 X1 X2 X3) = (esk30_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (esk31_3 X1 X2 X3) = (esk30_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (esk31_3 X1 X2 X3) = (esk30_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk31_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk31_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk31_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X3 X2 X1, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk28_3 X1 X2 X3) (u1_struct_0 X3) -> False) -> False)
  -> (forall X1 X3 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk31_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk31_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk31_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk30_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk34_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk33_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X3 X2, (epred1_3 X3 X2 X1 -> False) -> (m1_subset_1 (esk27_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk29_3 X1 X2 X3) X1 -> False) -> (m1_subset_1 (esk32_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X1 X5 X3 X2 X4, (X2 = X4 -> False) -> (v2_struct_0 X1 -> False) -> (k1_algstr_0 X1 X2 X3) = (k1_algstr_0 X1 X4 X3) -> v13_algstr_0 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l2_algstr_0 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X5 X2 X3 X4, (X3 = X4 -> False) -> (v2_struct_0 X1 -> False) -> (k1_algstr_0 X1 X2 X3) = (k1_algstr_0 X1 X2 X4) -> v13_algstr_0 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l2_algstr_0 X1 -> m1_subset_1 X5 (u1_struct_0 X1) -> m1_subset_1 X4 (u1_struct_0 X1) -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k3_rlvect_1 X1 X2 X3) (u1_struct_0 X1) -> False) -> v2_rlvect_1 X1 -> l1_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k1_midsp_1 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_midsp_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (k1_algstr_0 X1 X2 X3) (u1_struct_0 X1) -> False) -> l1_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k3_rlvect_1 X1 X2 X3) = (k1_algstr_0 X1 X2 X3) -> False) -> v2_rlvect_1 X1 -> l1_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X2 X1, ((k3_rlvect_1 X1 X2 X3) = (k3_rlvect_1 X1 X3 X2) -> False) -> v2_rlvect_1 X1 -> l1_algstr_0 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (v2_struct_0 X1 -> False) -> (k1_midsp_2 X1 X2) = (k1_midsp_2 X1 X3) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l2_algstr_0 X1 -> v12_vectsp_1 X1 -> m1_subset_1 X3 (u1_struct_0 X1) -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, ((k1_midsp_2 X1 (k4_algstr_0 X1 X2)) = (k4_algstr_0 X1 (k1_midsp_2 X1 X2)) -> False) -> (v2_struct_0 X1 -> False) -> v13_algstr_0 X1 -> v2_rlvect_1 X1 -> v3_rlvect_1 X1 -> v4_rlvect_1 X1 -> l2_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, ((k1_algstr_0 X1 X2 X2) = (k1_midsp_2 X1 X2) -> False) -> (v2_struct_0 X1 -> False) -> l2_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (k1_midsp_2 X1 X2) (u1_struct_0 X1) -> False) -> l2_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k4_algstr_0 X1 X2) (u1_struct_0 X1) -> False) -> l2_algstr_0 X1 -> m1_subset_1 X2 (u1_struct_0 X1) -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> (m1_subset_1 (esk21_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (m1_subset_1 (esk20_1 X1) (k1_zfmisc_1 (u1_struct_0 X1)) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, v2_struct_0 X1 -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 np__1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v13_struct_0 X1 k1_xboole_0 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v13_struct_0 X1 np__1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_finset_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (esk21_1 X1) -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_zfmisc_1 (u1_struct_0 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> l1_struct_0 X1 -> v1_xboole_0 (u1_struct_0 X1) -> False)
  -> (forall X1, (v13_struct_0 X1 k1_xboole_0 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v1_finset_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v8_struct_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 (u1_struct_0 X1) -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (u1_struct_0 X1) -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v12_vectsp_1 X1 -> False) -> v2_midsp_2 X1 -> l2_algstr_0 X1 -> False)
  -> (forall X1, (v2_struct_0 X1 -> False) -> (v1_zfmisc_1 (esk20_1 X1) -> False) -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> l1_struct_0 X1 -> v7_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v8_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X1, (v7_struct_0 X1 -> False) -> v2_struct_0 X1 -> l1_struct_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (l2_struct_0 X1 -> False) -> l2_algstr_0 X1 -> False)
  -> (forall X1, (l1_algstr_0 X1 -> False) -> l2_algstr_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l2_struct_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_algstr_0 X1 -> False)
  -> (forall X1, (l1_struct_0 X1 -> False) -> l1_midsp_1 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k1_midsp_1 esk2_0 (k1_midsp_1 esk2_0 esk4_0 esk6_0) (k1_midsp_1 esk2_0 esk5_0 esk7_0)) = (k1_midsp_1 esk2_0 (k1_midsp_1 esk2_0 esk4_0 esk5_0) (k1_midsp_1 esk2_0 esk6_0 esk7_0)) -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v2_struct_0 esk25_0 -> False)
  -> (v2_struct_0 esk22_0 -> False)
  -> (v2_struct_0 esk19_0 -> False)
  -> (v2_struct_0 esk2_0 -> False)
  -> (v2_struct_0 esk1_0 -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (u1_struct_0 esk2_0) (u1_struct_0 esk2_0)) (u1_struct_0 esk1_0))) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk17_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> ((v1_funct_2 esk3_0 (k2_zfmisc_1 (u1_struct_0 esk2_0) (u1_struct_0 esk2_0)) (u1_struct_0 esk1_0) -> False) -> False)
  -> ((r1_midsp_2 (u1_struct_0 esk2_0) esk1_0 esk3_0 -> False) -> False)
  -> ((v1_midsp_2 esk3_0 esk2_0 esk1_0 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk17_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk17_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk17_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk16_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk7_0 (u1_struct_0 esk2_0) -> False) -> False)
  -> ((m1_subset_1 esk6_0 (u1_struct_0 esk2_0) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u1_struct_0 esk2_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u1_struct_0 esk2_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((l2_struct_0 esk19_0 -> False) -> False)
  -> ((l2_struct_0 esk15_0 -> False) -> False)
  -> ((l1_algstr_0 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v12_vectsp_1 esk25_0 -> False) -> False)
  -> ((v7_struct_0 esk19_0 -> False) -> False)
  -> ((l1_struct_0 esk13_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((l1_midsp_1 esk22_0 -> False) -> False)
  -> ((l1_midsp_1 esk12_0 -> False) -> False)
  -> ((l1_midsp_1 esk2_0 -> False) -> False)
  -> ((l2_algstr_0 esk25_0 -> False) -> False)
  -> ((l2_algstr_0 esk14_0 -> False) -> False)
  -> ((l2_algstr_0 esk1_0 -> False) -> False)
  -> ((v2_midsp_2 esk1_0 -> False) -> False)
  -> ((v4_rlvect_1 esk1_0 -> False) -> False)
  -> ((v3_rlvect_1 esk1_0 -> False) -> False)
  -> ((v2_rlvect_1 esk1_0 -> False) -> False)
  -> ((v13_algstr_0 esk1_0 -> False) -> False)
  -> False.
Admitted.
