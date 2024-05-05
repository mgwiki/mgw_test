(** $I sig/MizarPreamble.mgs **)

Theorem t20_setwiseo:
 forall r1_tarski:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall esk32_5:set -> set -> set -> set -> set -> set,
 forall esk33_5:set -> set -> set -> set -> set -> set,
 forall k1_binop_1:set -> set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k2_tarski:set -> set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall esk27_2:set -> set -> set,
 forall esk28_1:set -> set,
 forall esk24_1:set -> set,
 forall esk16_1:set -> set,
 forall v3_relat_1:set -> prop,
 forall esk1_0:set,
 forall esk5_0:set,
 forall esk6_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk23_1:set -> set,
 forall esk31_0:set,
 forall esk21_0:set,
 forall esk11_0:set,
 forall esk9_2:set -> set -> set,
 forall esk22_2:set -> set -> set,
 forall esk13_1:set -> set,
 forall esk17_0:set,
 forall esk15_0:set,
 forall esk7_1:set -> set,
 forall esk19_1:set -> set,
 forall esk25_2:set -> set -> set,
 forall esk12_2:set -> set -> set,
 forall esk10_1:set -> set,
 forall esk8_0:set,
 forall esk20_0:set,
 forall esk30_0:set,
 forall v3_finsub_1:set -> prop,
 forall v1_finsub_1:set -> prop,
 forall v4_finsub_1:set -> prop,
 forall v2_relat_1:set -> prop,
 forall esk14_1:set -> set,
 forall esk18_1:set -> set,
 forall esk26_1:set -> set,
 forall esk29_1:set -> set,
 forall v1_zfmisc_1:set -> prop,
 forall v5_finset_1:set -> prop,
 forall v2_finset_1:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall k2_setwiseo:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall k5_setwiseo:set -> set -> set -> set,
 forall v1_finset_1:set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall v1_binop_1:set -> set -> prop,
 forall v1_setwiseo:set -> set -> prop,
 forall v2_binop_1:set -> set -> prop,
 forall v3_binop_1:set -> set -> prop,
 forall k7_setwiseo:set -> set -> set -> set -> set -> set,
 forall esk34_6:set -> set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k1_xboole_0:set,
 forall esk35_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall r3_binop_1:set -> set -> set -> prop,
 forall esk36_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k2_xboole_0:set -> set -> set,
 forall esk38_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall esk37_7:set -> set -> set -> set -> set -> set -> set -> set,
 forall k5_binop_1:set -> set -> set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v1_funct_1:set -> prop,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall k5_finsub_1:set -> set,
 forall epred1_6:set -> set -> set -> set -> set -> set -> prop,
     (forall X1 X6 X4 X3 X2 X5 X7, (epred1_6 X7 X6 X5 X4 X3 X2 -> False) -> (r3_binop_1 X7 (esk35_7 X2 X3 X4 X5 X6 X7 X1) X6 -> False) -> X3 = (k3_funct_2 (k5_finsub_1 X2) X7 X1 X5) -> (k1_funct_1 X1 (k1_tarski (esk36_7 X2 X3 X4 X5 X6 X7 X1))) = (k3_funct_2 X2 X7 X4 (esk36_7 X2 X3 X4 X5 X6 X7 X1)) -> (k5_binop_1 X7 X6 (k3_funct_2 (k5_finsub_1 X2) X7 X1 (esk37_7 X2 X3 X4 X5 X6 X7 X1)) (k3_funct_2 X2 X7 X4 (esk38_7 X2 X3 X4 X5 X6 X7 X1))) = (k1_funct_1 X1 (k2_xboole_0 (esk37_7 X2 X3 X4 X5 X6 X7 X1) (k1_tarski (esk38_7 X2 X3 X4 X5 X6 X7 X1)))) -> v1_funct_1 X1 -> v1_funct_2 X1 (k5_finsub_1 X2) X7 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X7)) -> False)
  -> (forall X1 X6 X4 X3 X2 X5 X7, (epred1_6 X7 X6 X5 X4 X3 X2 -> False) -> (m1_subset_1 (esk35_7 X2 X3 X4 X5 X6 X7 X1) X7 -> False) -> X3 = (k3_funct_2 (k5_finsub_1 X2) X7 X1 X5) -> (k1_funct_1 X1 (k1_tarski (esk36_7 X2 X3 X4 X5 X6 X7 X1))) = (k3_funct_2 X2 X7 X4 (esk36_7 X2 X3 X4 X5 X6 X7 X1)) -> (k5_binop_1 X7 X6 (k3_funct_2 (k5_finsub_1 X2) X7 X1 (esk37_7 X2 X3 X4 X5 X6 X7 X1)) (k3_funct_2 X2 X7 X4 (esk38_7 X2 X3 X4 X5 X6 X7 X1))) = (k1_funct_1 X1 (k2_xboole_0 (esk37_7 X2 X3 X4 X5 X6 X7 X1) (k1_tarski (esk38_7 X2 X3 X4 X5 X6 X7 X1)))) -> v1_funct_1 X1 -> v1_funct_2 X1 (k5_finsub_1 X2) X7 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X7)) -> False)
  -> (forall X1 X6 X4 X3 X2 X5 X7, (epred1_6 X7 X6 X5 X4 X3 X2 -> False) -> X3 = (k3_funct_2 (k5_finsub_1 X2) X7 X1 X5) -> (esk35_7 X2 X3 X4 X5 X6 X7 X1) = (k1_funct_1 X1 k1_xboole_0) -> (k1_funct_1 X1 (k1_tarski (esk36_7 X2 X3 X4 X5 X6 X7 X1))) = (k3_funct_2 X2 X7 X4 (esk36_7 X2 X3 X4 X5 X6 X7 X1)) -> (k5_binop_1 X7 X6 (k3_funct_2 (k5_finsub_1 X2) X7 X1 (esk37_7 X2 X3 X4 X5 X6 X7 X1)) (k3_funct_2 X2 X7 X4 (esk38_7 X2 X3 X4 X5 X6 X7 X1))) = (k1_funct_1 X1 (k2_xboole_0 (esk37_7 X2 X3 X4 X5 X6 X7 X1) (k1_tarski (esk38_7 X2 X3 X4 X5 X6 X7 X1)))) -> v1_funct_1 X1 -> v1_funct_2 X1 (k5_finsub_1 X2) X7 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X7)) -> False)
  -> (forall X1 X6 X4 X3 X2 X5 X7, (epred1_6 X7 X6 X5 X4 X3 X2 -> False) -> (m1_subset_1 (esk36_7 X2 X3 X4 X5 X6 X7 X1) X2 -> False) -> (r3_binop_1 X7 (esk35_7 X2 X3 X4 X5 X6 X7 X1) X6 -> False) -> X3 = (k3_funct_2 (k5_finsub_1 X2) X7 X1 X5) -> (k5_binop_1 X7 X6 (k3_funct_2 (k5_finsub_1 X2) X7 X1 (esk37_7 X2 X3 X4 X5 X6 X7 X1)) (k3_funct_2 X2 X7 X4 (esk38_7 X2 X3 X4 X5 X6 X7 X1))) = (k1_funct_1 X1 (k2_xboole_0 (esk37_7 X2 X3 X4 X5 X6 X7 X1) (k1_tarski (esk38_7 X2 X3 X4 X5 X6 X7 X1)))) -> v1_funct_1 X1 -> v1_funct_2 X1 (k5_finsub_1 X2) X7 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X7)) -> False)
  -> (forall X1 X6 X4 X3 X2 X5 X7, (epred1_6 X7 X6 X5 X4 X3 X2 -> False) -> (m1_subset_1 (esk35_7 X2 X3 X4 X5 X6 X7 X1) X7 -> False) -> (m1_subset_1 (esk36_7 X2 X3 X4 X5 X6 X7 X1) X2 -> False) -> X3 = (k3_funct_2 (k5_finsub_1 X2) X7 X1 X5) -> (k5_binop_1 X7 X6 (k3_funct_2 (k5_finsub_1 X2) X7 X1 (esk37_7 X2 X3 X4 X5 X6 X7 X1)) (k3_funct_2 X2 X7 X4 (esk38_7 X2 X3 X4 X5 X6 X7 X1))) = (k1_funct_1 X1 (k2_xboole_0 (esk37_7 X2 X3 X4 X5 X6 X7 X1) (k1_tarski (esk38_7 X2 X3 X4 X5 X6 X7 X1)))) -> v1_funct_1 X1 -> v1_funct_2 X1 (k5_finsub_1 X2) X7 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X7)) -> False)
  -> (forall X1 X6 X4 X3 X2 X5 X7, (epred1_6 X7 X6 X5 X4 X3 X2 -> False) -> (m1_subset_1 (esk36_7 X2 X3 X4 X5 X6 X7 X1) X2 -> False) -> X3 = (k3_funct_2 (k5_finsub_1 X2) X7 X1 X5) -> (esk35_7 X2 X3 X4 X5 X6 X7 X1) = (k1_funct_1 X1 k1_xboole_0) -> (k5_binop_1 X7 X6 (k3_funct_2 (k5_finsub_1 X2) X7 X1 (esk37_7 X2 X3 X4 X5 X6 X7 X1)) (k3_funct_2 X2 X7 X4 (esk38_7 X2 X3 X4 X5 X6 X7 X1))) = (k1_funct_1 X1 (k2_xboole_0 (esk37_7 X2 X3 X4 X5 X6 X7 X1) (k1_tarski (esk38_7 X2 X3 X4 X5 X6 X7 X1)))) -> v1_funct_1 X1 -> v1_funct_2 X1 (k5_finsub_1 X2) X7 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X7)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r3_binop_1 X6 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> (m1_subset_1 (esk37_7 X1 X2 X3 X4 X5 X6 X7) (k5_finsub_1 X1) -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r1_tarski (esk37_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> (r3_binop_1 X6 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk38_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> (r3_binop_1 X6 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk38_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (r3_binop_1 X6 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> (m1_subset_1 (esk37_7 X1 X2 X3 X4 X5 X6 X7) (k5_finsub_1 X1) -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> (r1_tarski (esk37_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> (r2_hidden (esk38_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> (m1_subset_1 (esk38_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r3_binop_1 X6 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk37_7 X1 X2 X3 X4 X5 X6 X7) = k1_xboole_0 -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk37_7 X1 X2 X3 X4 X5 X6 X7) (k5_finsub_1 X1) -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk35_7 X1 X2 X3 X4 X5 X6 X7) = (k1_funct_1 X7 k1_xboole_0) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r1_tarski (esk37_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk35_7 X1 X2 X3 X4 X5 X6 X7) = (k1_funct_1 X7 k1_xboole_0) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (r2_hidden (esk38_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk35_7 X1 X2 X3 X4 X5 X6 X7) = (k1_funct_1 X7 k1_xboole_0) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk38_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk35_7 X1 X2 X3 X4 X5 X6 X7) = (k1_funct_1 X7 k1_xboole_0) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk37_7 X1 X2 X3 X4 X5 X6 X7) = k1_xboole_0 -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk37_7 X1 X2 X3 X4 X5 X6 X7) = k1_xboole_0 -> (esk35_7 X1 X2 X3 X4 X5 X6 X7) = (k1_funct_1 X7 k1_xboole_0) -> (k1_funct_1 X7 (k1_tarski (esk36_7 X1 X2 X3 X4 X5 X6 X7))) = (k3_funct_2 X1 X6 X3 (esk36_7 X1 X2 X3 X4 X5 X6 X7)) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (r3_binop_1 X6 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> (m1_subset_1 (esk37_7 X1 X2 X3 X4 X5 X6 X7) (k5_finsub_1 X1) -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (r1_tarski (esk37_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> (r3_binop_1 X6 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (r2_hidden (esk38_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> (r3_binop_1 X6 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (m1_subset_1 (esk38_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (r3_binop_1 X6 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (m1_subset_1 (esk37_7 X1 X2 X3 X4 X5 X6 X7) (k5_finsub_1 X1) -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (r1_tarski (esk37_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (r2_hidden (esk38_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (m1_subset_1 (esk38_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (r3_binop_1 X6 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X5 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk37_7 X1 X2 X3 X4 X5 X6 X7) = k1_xboole_0 -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (m1_subset_1 (esk37_7 X1 X2 X3 X4 X5 X6 X7) (k5_finsub_1 X1) -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk35_7 X1 X2 X3 X4 X5 X6 X7) = (k1_funct_1 X7 k1_xboole_0) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (r1_tarski (esk37_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk35_7 X1 X2 X3 X4 X5 X6 X7) = (k1_funct_1 X7 k1_xboole_0) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (r2_hidden (esk38_7 X1 X2 X3 X4 X5 X6 X7) X4 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk35_7 X1 X2 X3 X4 X5 X6 X7) = (k1_funct_1 X7 k1_xboole_0) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> (m1_subset_1 (esk38_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk35_7 X1 X2 X3 X4 X5 X6 X7) = (k1_funct_1 X7 k1_xboole_0) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk35_7 X1 X2 X3 X4 X5 X6 X7) X6 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk37_7 X1 X2 X3 X4 X5 X6 X7) = k1_xboole_0 -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X7 X5 X3 X2 X1 X4 X6, (epred1_6 X6 X5 X4 X3 X2 X1 -> False) -> (m1_subset_1 (esk36_7 X1 X2 X3 X4 X5 X6 X7) X1 -> False) -> X2 = (k3_funct_2 (k5_finsub_1 X1) X6 X7 X4) -> (esk37_7 X1 X2 X3 X4 X5 X6 X7) = k1_xboole_0 -> (esk35_7 X1 X2 X3 X4 X5 X6 X7) = (k1_funct_1 X7 k1_xboole_0) -> v1_funct_1 X7 -> v1_funct_2 X7 (k5_finsub_1 X1) X6 -> m1_subset_1 X7 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False)
  -> (forall X2 X4 X7 X6 X5 X8 X3 X1, (X1 = k1_xboole_0 -> False) -> ((k5_binop_1 X8 X7 (k3_funct_2 (k5_finsub_1 X2) X8 (esk34_6 X2 X5 X6 X3 X7 X8) X1) (k3_funct_2 X2 X8 X6 X4)) = (k1_funct_1 (esk34_6 X2 X5 X6 X3 X7 X8) (k2_xboole_0 X1 (k1_tarski X4))) -> False) -> m1_subset_1 X4 X2 -> r2_hidden X4 X3 -> r1_tarski X1 X3 -> m1_subset_1 X1 (k5_finsub_1 X2) -> epred1_6 X8 X7 X3 X6 X5 X2 -> False)
  -> (forall X5 X1 X2 X4 X3 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X1 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (k1_funct_1 X1 k1_xboole_0) = (k1_funct_1 X5 k1_xboole_0) -> (k1_funct_1 X1 (k2_xboole_0 (esk32_5 X2 X3 X4 X5 X1) (k1_tarski (esk33_5 X2 X3 X4 X5 X1)))) = (k1_funct_1 X5 (k2_xboole_0 (esk32_5 X2 X3 X4 X5 X1) (k1_tarski (esk33_5 X2 X3 X4 X5 X1)))) -> v1_funct_1 X5 -> v1_funct_1 X1 -> r1_tarski X6 X4 -> m1_subset_1 X6 (k5_finsub_1 X3) -> m1_subset_1 X4 (k5_finsub_1 X3) -> v1_funct_2 X5 (k5_finsub_1 X3) X2 -> v1_funct_2 X1 (k5_finsub_1 X3) X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X3) X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X3) X2)) -> False)
  -> (forall X5 X1 X2 X4 X3 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X1 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (r1_tarski k1_xboole_0 X4 -> False) -> (k1_funct_1 X1 (k2_xboole_0 (esk32_5 X2 X3 X4 X5 X1) (k1_tarski (esk33_5 X2 X3 X4 X5 X1)))) = (k1_funct_1 X5 (k2_xboole_0 (esk32_5 X2 X3 X4 X5 X1) (k1_tarski (esk33_5 X2 X3 X4 X5 X1)))) -> v1_funct_1 X5 -> v1_funct_1 X1 -> r1_tarski X6 X4 -> m1_subset_1 X6 (k5_finsub_1 X3) -> m1_subset_1 X4 (k5_finsub_1 X3) -> v1_funct_2 X5 (k5_finsub_1 X3) X2 -> v1_funct_2 X1 (k5_finsub_1 X3) X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X3) X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X3) X2)) -> False)
  -> (forall X5 X1 X2 X4 X3 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X1 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (k1_funct_1 X1 (k2_xboole_0 (esk32_5 X2 X3 X4 X5 X1) (k1_tarski (esk33_5 X2 X3 X4 X5 X1)))) = (k1_funct_1 X5 (k2_xboole_0 (esk32_5 X2 X3 X4 X5 X1) (k1_tarski (esk33_5 X2 X3 X4 X5 X1)))) -> v1_funct_1 X5 -> v1_funct_1 X1 -> r1_tarski X6 X4 -> m1_subset_1 X6 (k5_finsub_1 X3) -> m1_subset_1 X4 (k5_finsub_1 X3) -> v1_funct_2 X5 (k5_finsub_1 X3) X2 -> v1_funct_2 X1 (k5_finsub_1 X3) X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X3) X2)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X3) X2)) -> False)
  -> (forall X6 X4 X3 X5 X7 X1 X2, ((k1_funct_1 (esk34_6 X2 X3 X4 X5 X6 X7) (k1_tarski X1)) = (k3_funct_2 X2 X7 X4 X1) -> False) -> m1_subset_1 X1 X2 -> epred1_6 X7 X6 X5 X4 X3 X2 -> False)
  -> (forall X3 X5 X2 X1 X4 X6, ((k3_funct_2 (k5_finsub_1 X2) X3 (esk34_6 X2 X1 X4 X5 X6 X3) X5) = X1 -> False) -> epred1_6 X3 X6 X5 X4 X1 X2 -> False)
  -> (forall X3 X7 X4 X5 X6 X1 X2, ((k1_funct_1 (esk34_6 X4 X5 X6 X7 X3 X2) k1_xboole_0) = X1 -> False) -> m1_subset_1 X1 X2 -> r3_binop_1 X2 X1 X3 -> epred1_6 X2 X3 X7 X6 X5 X4 -> False)
  -> (forall X6 X4 X1 X2 X3 X5, (m1_subset_1 (esk34_6 X1 X2 X3 X4 X5 X6) (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X1) X6)) -> False) -> epred1_6 X6 X5 X4 X3 X2 X1 -> False)
  -> (forall X6 X4 X1 X2 X3 X5, (v1_funct_2 (esk34_6 X1 X2 X3 X4 X5 X6) (k5_finsub_1 X1) X6 -> False) -> epred1_6 X6 X5 X4 X3 X2 X1 -> False)
  -> (forall X6 X4 X1 X2 X3 X5, (v1_funct_1 (esk34_6 X1 X2 X3 X4 X5 X6) -> False) -> epred1_6 X6 X5 X4 X3 X2 X1 -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_tarski (k2_xboole_0 (esk32_5 X1 X2 X3 X4 X5) (k1_tarski (esk33_5 X1 X2 X3 X4 X5))) X3 -> False) -> (k1_funct_1 X4 k1_xboole_0) = (k1_funct_1 X5 k1_xboole_0) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_tarski k1_xboole_0 X3 -> False) -> (r1_tarski (k2_xboole_0 (esk32_5 X1 X2 X3 X4 X5) (k1_tarski (esk33_5 X1 X2 X3 X4 X5))) X3 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_tarski (k2_xboole_0 (esk32_5 X1 X2 X3 X4 X5) (k1_tarski (esk33_5 X1 X2 X3 X4 X5))) X3 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (k1_funct_1 X4 k1_xboole_0) = (k1_funct_1 X5 k1_xboole_0) -> (k2_xboole_0 (esk32_5 X1 X2 X3 X4 X5) (k1_tarski (esk33_5 X1 X2 X3 X4 X5))) = k1_xboole_0 -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_tarski k1_xboole_0 X3 -> False) -> (k2_xboole_0 (esk32_5 X1 X2 X3 X4 X5) (k1_tarski (esk33_5 X1 X2 X3 X4 X5))) = k1_xboole_0 -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (k2_xboole_0 (esk32_5 X1 X2 X3 X4 X5) (k1_tarski (esk33_5 X1 X2 X3 X4 X5))) = k1_xboole_0 -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X1 X2 X3 X5 X4 X6, (X5 = (k7_setwiseo X6 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> v3_binop_1 X2 X1 -> v1_binop_1 X2 X1 -> v2_binop_1 X2 X1 -> v1_setwiseo X2 X1 -> v1_funct_2 X4 X6 X1 -> m1_subset_1 X3 (k5_finsub_1 X6) -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> epred1_6 X1 X2 X3 X4 X5 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X6 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X6 X4 X5 X2 X1 X3, (X3 = k1_xboole_0 -> False) -> (X5 = (k7_setwiseo X6 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X6 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> v3_binop_1 X2 X1 -> v1_binop_1 X2 X1 -> v2_binop_1 X2 X1 -> v1_funct_2 X4 X6 X1 -> m1_subset_1 X3 (k5_finsub_1 X6) -> v1_funct_2 X2 (k2_zfmisc_1 X1 X1) X1 -> epred1_6 X1 X2 X3 X4 X5 X6 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X6 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> ((esk32_5 X1 X2 X3 X4 X5) = k1_xboole_0 -> False) -> ((k1_funct_1 X4 (esk32_5 X1 X2 X3 X4 X5)) = (k1_funct_1 X5 (esk32_5 X1 X2 X3 X4 X5)) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (k1_funct_1 X4 k1_xboole_0) = (k1_funct_1 X5 k1_xboole_0) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> r1_tarski (esk32_5 X1 X2 X3 X4 X5) X3 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> ((esk32_5 X1 X2 X3 X4 X5) = k1_xboole_0 -> False) -> ((k1_funct_1 X4 (esk32_5 X1 X2 X3 X4 X5)) = (k1_funct_1 X5 (esk32_5 X1 X2 X3 X4 X5)) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_tarski k1_xboole_0 X3 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> r1_tarski (esk32_5 X1 X2 X3 X4 X5) X3 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> ((esk32_5 X1 X2 X3 X4 X5) = k1_xboole_0 -> False) -> ((k1_funct_1 X4 (esk32_5 X1 X2 X3 X4 X5)) = (k1_funct_1 X5 (esk32_5 X1 X2 X3 X4 X5)) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> r1_tarski (esk32_5 X1 X2 X3 X4 X5) X3 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X2 X4 X5 X1 X6 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (epred1_6 X3 X4 X5 X6 X1 X2 -> False) -> X1 = (k7_setwiseo X2 X3 X4 X5 X6) -> v1_funct_1 X6 -> v1_funct_1 X4 -> m1_subset_1 X1 X3 -> v3_binop_1 X4 X3 -> v1_binop_1 X4 X3 -> v2_binop_1 X4 X3 -> v1_setwiseo X4 X3 -> v1_funct_2 X6 X2 X3 -> m1_subset_1 X5 (k5_finsub_1 X2) -> v1_funct_2 X4 (k2_zfmisc_1 X3 X3) X3 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X3) X3)) -> False)
  -> (forall X3 X6 X1 X4 X2 X5, (X5 = k1_xboole_0 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (epred1_6 X3 X4 X5 X6 X1 X2 -> False) -> X1 = (k7_setwiseo X2 X3 X4 X5 X6) -> v1_funct_1 X6 -> v1_funct_1 X4 -> m1_subset_1 X1 X3 -> v3_binop_1 X4 X3 -> v1_binop_1 X4 X3 -> v2_binop_1 X4 X3 -> v1_funct_2 X6 X2 X3 -> m1_subset_1 X5 (k5_finsub_1 X2) -> v1_funct_2 X4 (k2_zfmisc_1 X3 X3) X3 -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X3) X3)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_5 X1 X2 X3 X4 X5) (k5_finsub_1 X2) -> False) -> (k1_funct_1 X4 k1_xboole_0) = (k1_funct_1 X5 k1_xboole_0) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk33_5 X1 X2 X3 X4 X5) X2 -> False) -> (k1_funct_1 X4 k1_xboole_0) = (k1_funct_1 X5 k1_xboole_0) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X1 X3 X4 X5 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k7_setwiseo X1 X2 X3 X4 X5) X2 -> False) -> v1_funct_1 X5 -> v1_funct_1 X3 -> v1_funct_2 X5 X1 X2 -> m1_subset_1 X4 (k5_finsub_1 X1) -> v1_funct_2 X3 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_tarski k1_xboole_0 X3 -> False) -> (m1_subset_1 (esk32_5 X1 X2 X3 X4 X5) (k5_finsub_1 X2) -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_tarski k1_xboole_0 X3 -> False) -> (m1_subset_1 (esk33_5 X1 X2 X3 X4 X5) X2 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_5 X1 X2 X3 X4 X5) (k5_finsub_1 X2) -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X5 X4 X1 X3 X2 X6, (X6 = k1_xboole_0 -> False) -> ((k1_funct_1 X4 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk33_5 X1 X2 X3 X4 X5) X2 -> False) -> v1_funct_1 X5 -> v1_funct_1 X4 -> r1_tarski X6 X3 -> m1_subset_1 X6 (k5_finsub_1 X2) -> m1_subset_1 X3 (k5_finsub_1 X2) -> v1_funct_2 X5 (k5_finsub_1 X2) X1 -> v1_funct_2 X4 (k5_finsub_1 X2) X1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (k5_finsub_1 X2) X1)) -> False)
  -> (forall X2 X4 X3 X1, (m1_subset_1 (k5_binop_1 X2 X1 X3 X4) X2 -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X4 X3 X1, ((k5_binop_1 X2 X1 X3 X4) = (k1_binop_1 X1 X3 X4) -> False) -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X3 X1, ((k5_binop_1 X2 X1 X3 X3) = X3 -> False) -> v1_funct_1 X1 -> m1_subset_1 X3 X2 -> v3_binop_1 X1 X2 -> v1_funct_2 X1 (k2_zfmisc_1 X2 X2) X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X2) X2)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_partfun1 X2 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_partfun1 X2 X3 -> False) -> v1_funct_2 X2 X3 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_finset_1 X1 -> False) -> v1_funct_1 X1 -> v1_finset_1 X2 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_partfun1 X1 X2 -> False) -> v1_funct_2 X1 X2 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X2)) -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k5_setwiseo X2 X1 X3) (k5_finsub_1 X2) -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X3 X1 X2, (v1_funct_2 X1 X2 X3 -> False) -> v1_partfun1 X1 X2 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, ((k5_setwiseo X2 X1 X3) = (k5_setwiseo X2 X3 X1) -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k2_tarski (k2_tarski X2 X3) (k1_tarski X2))) = (k1_binop_1 X1 X2 X3) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X3 X2 X1, ((k5_setwiseo X2 X1 X3) = (k2_xboole_0 X1 X3) -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, ((k5_setwiseo X2 X1 X1) = X1 -> False) -> m1_subset_1 X3 (k5_finsub_1 X2) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X3 X2 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k2_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> (r2_hidden X1 X2 -> False) -> r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False)
  -> (forall X1 X2 X3, (r1_tarski (k2_xboole_0 X3 (k1_tarski X1)) X2 -> False) -> r2_hidden X1 X2 -> r1_tarski X3 X2 -> False)
  -> (forall X3 X1 X2, (r1_tarski X1 X2 -> False) -> r1_tarski (k2_xboole_0 X1 (k1_tarski X3)) X2 -> False)
  -> (forall X3 X1 X2, (r2_hidden X1 X2 -> False) -> r1_tarski (k2_xboole_0 X3 (k1_tarski X1)) X2 -> False)
  -> (forall X1 X3 X2, (v5_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X3 X2, (v4_relat_1 X3 X2 -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> m1_subset_1 X3 (k1_zfmisc_1 X1) -> False)
  -> (forall X3 X2 X1, (r2_hidden X1 (k2_xboole_0 X2 (k1_tarski X3)) -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_setwiseo X1 X2) (k5_finsub_1 X1) -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X3, (r1_tarski X1 X3 -> False) -> r1_tarski X2 X3 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk27_2 X1 X2) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X3 X2 X1, (r2_hidden X1 (k2_xboole_0 X3 (k1_tarski X2)) -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_xboole_0 X2 X1) -> False)
  -> (forall X2 X1, (v1_finset_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v5_relat_1 (esk27_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v4_relat_1 (esk27_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k2_setwiseo X1 X2) = (k1_tarski X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v5_finset_1 (k2_xboole_0 X1 X2) -> False) -> v5_finset_1 X2 -> v5_finset_1 X1 -> False)
  -> (forall X2 X1, (v5_finset_1 (k2_tarski X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k2_xboole_0 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_xboole_0 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k2_zfmisc_1 X1 X2) -> False) -> v1_finset_1 X2 -> v1_finset_1 X1 -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_relat_1 X2 -> False) -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_relat_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (v1_funct_1 (esk27_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 X1 -> False) -> m1_subset_1 X1 (k5_finsub_1 X2) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk29_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk28_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_1 X1) (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk14_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk29_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk28_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk18_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk16_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk14_1 X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_relat_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v4_finsub_1 X1 -> False) -> v1_finsub_1 X1 -> v3_finsub_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_tarski X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk29_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk16_1 X1) -> False) -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_relat_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finsub_1 X1 -> False) -> v4_finsub_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k5_binop_1 esk1_0 esk3_0 (k7_setwiseo esk2_0 esk1_0 esk3_0 esk4_0 esk5_0) (k3_funct_2 esk2_0 esk1_0 esk5_0 esk6_0)) = (k7_setwiseo esk2_0 esk1_0 esk3_0 (k5_setwiseo esk2_0 esk4_0 (k2_setwiseo esk2_0 esk6_0)) esk5_0) -> False)
  -> (forall X1 X2, v1_xboole_0 (k2_tarski X1 X2) -> False)
  -> (forall X1, v1_subset_1 (esk23_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k5_finsub_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (v1_xboole_0 esk31_0 -> False)
  -> (v1_xboole_0 esk30_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk8_0 -> False)
  -> (v1_xboole_0 esk2_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (esk4_0 = k1_xboole_0 -> False)
  -> (forall X1 X2 X3 X4, (v1_relat_1 (k2_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1)) (k2_tarski (k2_tarski X3 X4) (k1_tarski X3))) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_tarski (k2_tarski (k2_tarski X1 X2) (k1_tarski X1))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk10_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X1 X1) X1)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 esk1_0 esk1_0) esk1_0)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk12_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk9_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1, (v1_funct_2 (esk10_1 X1) (k2_zfmisc_1 X1 X1) X1 -> False) -> False)
  -> (forall X2 X1, (v1_funct_2 (esk9_2 X1 X2) X1 X2 -> False) -> False)
  -> ((v1_funct_2 esk3_0 (k2_zfmisc_1 esk1_0 esk1_0) esk1_0 -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (k2_zfmisc_1 esk2_0 esk1_0)) -> False) -> False)
  -> ((v1_funct_2 esk5_0 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk10_1 X1) (k2_zfmisc_1 X1 X1) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk25_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk22_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk12_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk9_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk25_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk22_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk9_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (r1_tarski X1 (k2_xboole_0 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk22_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk9_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k2_zfmisc_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_finset_1 (k2_tarski X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk25_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk9_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X2 X1, ((k2_xboole_0 X1 X2) = (k2_xboole_0 X2 X1) -> False) -> False)
  -> (forall X2 X1, ((k2_tarski X1 X2) = (k2_tarski X2 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk23_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v5_relat_1 (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (v3_binop_1 (esk10_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 k1_xboole_0 (k5_finsub_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k5_finsub_1 esk2_0) -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 X1) = X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k2_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> ((v2_binop_1 esk3_0 esk1_0 -> False) -> False)
  -> ((v1_binop_1 esk3_0 esk1_0 -> False) -> False)
  -> ((v3_binop_1 esk3_0 esk1_0 -> False) -> False)
  -> ((m1_subset_1 esk6_0 esk2_0 -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk10_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k5_finsub_1 X1) -> False) -> False)
  -> (forall X1, (v4_finsub_1 (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 (esk13_1 X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 (k1_tarski X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk10_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk13_1 X1) -> False) -> False)
  -> ((v2_finset_1 esk31_0 -> False) -> False)
  -> ((v5_finset_1 esk30_0 -> False) -> False)
  -> ((v2_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk31_0 -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_finset_1 esk30_0 -> False) -> False)
  -> ((v1_finset_1 esk21_0 -> False) -> False)
  -> ((v1_finset_1 esk8_0 -> False) -> False)
  -> ((v1_funct_1 esk31_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_xboole_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
