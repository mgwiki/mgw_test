(** $I sig/MizarPreamble.mgs **)

Theorem t32_card_1:
 forall esk41_3:set -> set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall v1_funct_1:set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk6_2:set -> set -> set,
 forall esk7_2:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk8_2:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_subset_1:set -> set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall v3_ordinal1:set -> prop,
 forall esk36_1:set -> set,
 forall esk32_1:set -> set,
 forall esk19_1:set -> set,
 forall v1_ordinal1:set -> prop,
 forall v2_ordinal1:set -> prop,
 forall v1_card_1:set -> prop,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk1_0:set,
 forall esk33_0:set,
 forall esk40_0:set,
 forall esk38_0:set,
 forall esk29_0:set,
 forall esk25_0:set,
 forall esk21_0:set,
 forall esk26_1:set -> set,
 forall esk31_0:set,
 forall esk16_0:set,
 forall esk17_0:set,
 forall o_0_0_xboole_0:set,
 forall esk14_0:set,
 forall esk18_0:set,
 forall esk20_0:set,
 forall esk24_0:set,
 forall esk13_1:set -> set,
 forall esk15_0:set,
 forall esk23_0:set,
 forall esk27_0:set,
 forall esk34_0:set,
 forall esk39_0:set,
 forall esk28_0:set,
 forall esk30_1:set -> set,
 forall k1_xboole_0:set,
 forall v7_ordinal1:set -> prop,
 forall v2_funcop_1:set -> prop,
 forall esk22_1:set -> set,
 forall esk35_1:set -> set,
 forall esk37_1:set -> set,
 forall v5_ordinal1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall r2_tarski:set -> set -> prop,
 forall v6_ordinal1:set -> prop,
 forall v5_finset_1:set -> prop,
 forall v2_finset_1:set -> prop,
 forall v1_finset_1:set -> prop,
 forall v1_funcop_1:set -> prop,
 forall esk11_2:set -> set -> set,
 forall r2_wellord2:set -> set -> prop,
 forall esk9_1:set -> set,
 forall esk10_1:set -> set,
 forall esk4_2:set -> set -> set,
 forall v2_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk12_3:set -> set -> set -> set,
 forall esk42_3:set -> set -> set -> set,
 forall esk43_3:set -> set -> set -> set,
 forall esk44_3:set -> set -> set -> set,
 forall k1_tarski:set -> set,
 forall k6_subset_1:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall esk45_3:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
     (forall X1 X4 X2 X3, ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> (esk43_3 X2 X3 X4) = (esk42_3 X2 X3 X4) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X3 X4 X2, ((esk43_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X3 X4 X2, ((esk42_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X2 X3 X4, ((esk41_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X2 X3 X4, ((esk41_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X4 X2 X3, ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> (r2_hidden (esk41_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X2 X3 X4, ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> (esk44_3 X2 X3 X4) = X5 -> (esk43_3 X2 X3 X4) = (esk42_3 X2 X3 X4) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X5 X1 X3 X4 X2, ((esk43_3 X2 X3 X4) = X2 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X5 X1 X3 X4 X2, ((esk42_3 X2 X3 X4) = X2 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X5 X1 X2 X3 X4, ((esk41_3 X2 X3 X4) = X4 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X5 X1 X2 X3 X4, ((esk41_3 X2 X3 X4) = X4 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X2 X3 X4, ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> (r2_hidden (esk41_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X3 X4 X2, ((esk43_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> (esk41_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X3 X4 X2, ((esk42_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> (esk41_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X5 X1 X3 X4 X2, ((esk43_3 X2 X3 X4) = X2 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> (esk41_3 X2 X3 X4) = X4 -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X5 X1 X3 X4 X2, ((esk42_3 X2 X3 X4) = X2 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> (esk41_3 X2 X3 X4) = X4 -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X5 X4 X3 X2 X1, ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> (esk43_3 X2 X3 X4) = (esk42_3 X2 X3 X4) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X3 X4 X2, ((esk43_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X3 X4 X2, ((esk42_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X2 X3 X4, ((esk41_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X2 X3 X4, ((esk41_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X5 X4 X3 X2 X1, ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> (r2_hidden (esk41_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X3 X4 X2, ((esk43_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> X2 = X5 -> (esk41_3 X2 X3 X4) = X4 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X3 X4 X2, ((esk42_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X2 -> False) -> X2 = X5 -> (esk41_3 X2 X3 X4) = X4 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X2 X3 X4, ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> (r2_hidden (esk44_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> X1 = X2 -> (esk43_3 X3 X4 X2) = (esk42_3 X3 X4 X2) -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> (esk43_3 X2 X3 X4) = (esk42_3 X2 X3 X4) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X4 X2 X3, ((esk43_3 X3 X4 X2) = X3 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk43_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> (r2_hidden (esk44_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> X1 = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X1 X4 X2 X3, ((esk42_3 X3 X4 X2) = X3 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk42_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> (r2_hidden (esk44_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> X1 = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X1 X3 X4 X2, ((esk41_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk43_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> (r2_hidden (esk44_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> X1 = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X1 X3 X4 X2, ((esk41_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk42_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> (r2_hidden (esk44_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> X1 = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> ((esk43_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> ((esk42_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> ((esk41_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> ((esk41_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X2 X3 X4, ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> (r2_hidden (esk41_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> (r2_hidden (esk44_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> X1 = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X3 X2 X1 X4, (X1 = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> (r2_hidden (esk41_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X3 X4 X2, ((esk44_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> X1 = X2 -> (esk44_3 X3 X4 X2) = X5 -> (esk43_3 X3 X4 X2) = (esk42_3 X3 X4 X2) -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X3 X2 X5 X1 X4, (X1 = X4 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> (esk44_3 X2 X3 X4) = X5 -> (esk43_3 X2 X3 X4) = (esk42_3 X2 X3 X4) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X2 -> False) -> r2_hidden (esk12_3 X1 X2 X3) X3 -> r2_hidden (esk12_3 X1 X2 X3) X1 -> False)
  -> (forall X5 X1 X4 X2 X3, ((esk43_3 X3 X4 X2) = X3 -> False) -> ((esk44_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk43_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> X1 = X2 -> (esk44_3 X3 X4 X2) = X5 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X5 X1 X4 X2 X3, ((esk42_3 X3 X4 X2) = X3 -> False) -> ((esk44_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk42_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> X1 = X2 -> (esk44_3 X3 X4 X2) = X5 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X5 X1 X3 X4 X2, ((esk41_3 X3 X4 X2) = X2 -> False) -> ((esk44_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk43_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> X1 = X2 -> (esk44_3 X3 X4 X2) = X5 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X5 X1 X3 X4 X2, ((esk41_3 X3 X4 X2) = X2 -> False) -> ((esk44_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk42_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> X1 = X2 -> (esk44_3 X3 X4 X2) = X5 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X2 X3 X5 X1 X4, (X1 = X4 -> False) -> ((esk43_3 X2 X3 X4) = X2 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X2 X3 X5 X1 X4, (X1 = X4 -> False) -> ((esk42_3 X2 X3 X4) = X2 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X3 X2 X5 X1 X4, (X1 = X4 -> False) -> ((esk41_3 X2 X3 X4) = X4 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X3 X2 X5 X1 X4, (X1 = X4 -> False) -> ((esk41_3 X2 X3 X4) = X4 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X3 X4 X2, ((esk44_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> (r2_hidden (esk41_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> X1 = X2 -> (esk44_3 X3 X4 X2) = X5 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X1 X4 X2 X3, ((esk43_3 X3 X4 X2) = X3 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> (r2_hidden (esk44_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> X1 = X2 -> (esk41_3 X3 X4 X2) = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X1 X4 X2 X3, ((esk42_3 X3 X4 X2) = X3 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> (r2_hidden (esk44_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> X1 = X2 -> (esk41_3 X3 X4 X2) = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X3 X2 X5 X1 X4, (X1 = X4 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> (r2_hidden (esk41_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> ((esk43_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> (esk41_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X2 X3 X1 X4, (X1 = X4 -> False) -> ((esk42_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> (r2_hidden (esk44_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> (esk41_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X5 X1 X4 X2 X3, ((esk43_3 X3 X4 X2) = X3 -> False) -> ((esk44_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> X1 = X2 -> (esk41_3 X3 X4 X2) = X2 -> (esk44_3 X3 X4 X2) = X5 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X5 X1 X4 X2 X3, ((esk42_3 X3 X4 X2) = X3 -> False) -> ((esk44_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> X1 = X2 -> (esk41_3 X3 X4 X2) = X2 -> (esk44_3 X3 X4 X2) = X5 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X2 X3 X5 X1 X4, (X1 = X4 -> False) -> ((esk43_3 X2 X3 X4) = X2 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> (esk41_3 X2 X3 X4) = X4 -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X2 X3 X5 X1 X4, (X1 = X4 -> False) -> ((esk42_3 X2 X3 X4) = X2 -> False) -> ((esk44_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> (esk41_3 X2 X3 X4) = X4 -> (esk44_3 X2 X3 X4) = X5 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X5 X1 X2 X4 X3, ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> X3 = X5 -> X1 = X2 -> (esk44_3 X3 X4 X2) = X2 -> (esk43_3 X3 X4 X2) = (esk42_3 X3 X4 X2) -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X2 X3 X5 X1 X4, (X1 = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> (esk43_3 X2 X3 X4) = (esk42_3 X2 X3 X4) -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X1 X5 X4 X2 X3, ((esk43_3 X3 X4 X2) = X3 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk43_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> X3 = X5 -> X1 = X2 -> (esk44_3 X3 X4 X2) = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X1 X5 X4 X2 X3, ((esk42_3 X3 X4 X2) = X3 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk42_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> X3 = X5 -> X1 = X2 -> (esk44_3 X3 X4 X2) = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X1 X5 X3 X4 X2, ((esk41_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk43_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> X3 = X5 -> X1 = X2 -> (esk44_3 X3 X4 X2) = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X1 X5 X3 X4 X2, ((esk41_3 X3 X4 X2) = X2 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> ((esk42_3 X3 X4 X2) = (esk41_3 X3 X4 X2) -> False) -> X3 = X5 -> X1 = X2 -> (esk44_3 X3 X4 X2) = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X2 X3 X5 X1 X4, (X1 = X4 -> False) -> ((esk43_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X2 X3 X5 X1 X4, (X1 = X4 -> False) -> ((esk42_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X3 X2 X5 X1 X4, (X1 = X4 -> False) -> ((esk41_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk43_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X3 X2 X5 X1 X4, (X1 = X4 -> False) -> ((esk41_3 X2 X3 X4) = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> ((esk42_3 X2 X3 X4) = (esk41_3 X2 X3 X4) -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X3 X2 X1, ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk43_3 X1 X2 X3) = (esk42_3 X1 X2 X3) -> False)
  -> (forall X5 X1 X2 X4 X3, ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> (r2_hidden (esk41_3 X3 X4 X2) (k6_subset_1 X4 (k1_tarski X3)) -> False) -> X3 = X5 -> X1 = X2 -> (esk44_3 X3 X4 X2) = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X2 X3 X5 X1 X4, (X1 = X4 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> (r2_hidden (esk41_3 X2 X3 X4) (k6_subset_1 X3 (k1_tarski X2)) -> False) -> X2 = X5 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X2 X1 X3, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X4 X1 X2 X3, ((esk44_3 X1 X2 X3) = X3 -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk44_3 X1 X2 X3) = X4 -> (esk43_3 X1 X2 X3) = (esk42_3 X1 X2 X3) -> False)
  -> (forall X1 X5 X4 X2 X3, ((esk43_3 X3 X4 X2) = X3 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> X3 = X5 -> X1 = X2 -> (esk41_3 X3 X4 X2) = X2 -> (esk44_3 X3 X4 X2) = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X1 X5 X4 X2 X3, ((esk42_3 X3 X4 X2) = X3 -> False) -> ((k1_funct_1 (esk45_3 X3 X4 X2) X1) = X3 -> False) -> X3 = X5 -> X1 = X2 -> (esk41_3 X3 X4 X2) = X2 -> (esk44_3 X3 X4 X2) = X2 -> r2_hidden X1 (k6_subset_1 X4 (k1_tarski X3)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk43_3 X1 X2 X3) = (esk42_3 X1 X2 X3) -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk43_3 X1 X2 X3) = (esk42_3 X1 X2 X3) -> False)
  -> (forall X2 X3 X5 X1 X4, (X1 = X4 -> False) -> ((esk43_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> X2 = X5 -> (esk41_3 X2 X3 X4) = X4 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X2 X3 X5 X1 X4, (X1 = X4 -> False) -> ((esk42_3 X2 X3 X4) = X2 -> False) -> ((k1_funct_1 (esk45_3 X2 X3 X4) X1) = X1 -> False) -> X2 = X5 -> (esk41_3 X2 X3 X4) = X4 -> (esk44_3 X2 X3 X4) = X4 -> r2_hidden X1 (k6_subset_1 X3 (k1_tarski X2)) -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X2 X1 X3, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X4 X1 X2 X3, ((esk44_3 X1 X2 X3) = X3 -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X3 X2 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk41_3 X1 X2 X3) = X3 -> False)
  -> (forall X3 X2 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk41_3 X1 X2 X3) = X3 -> False)
  -> (forall X2 X1 X3, (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X2 X1 X3, (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> False)
  -> (forall X4 X1 X2 X3, ((esk44_3 X1 X2 X3) = X3 -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (esk44_3 X1 X2 X3) = X4 -> (esk43_3 X1 X2 X3) = (esk42_3 X1 X2 X3) -> False)
  -> (forall X4 X1 X2 X3, ((esk44_3 X1 X2 X3) = X3 -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (esk44_3 X1 X2 X3) = X4 -> (esk43_3 X1 X2 X3) = (esk42_3 X1 X2 X3) -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X1 X2 X3, ((esk44_3 X1 X2 X3) = X3 -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X1 X2 X3, ((esk44_3 X1 X2 X3) = X3 -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X3 X2 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk41_3 X1 X2 X3) = X3 -> False)
  -> (forall X3 X2 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk41_3 X1 X2 X3) = X3 -> False)
  -> (forall X3 X2 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk41_3 X1 X2 X3) = X3 -> False)
  -> (forall X3 X2 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk44_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (esk41_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk44_3 X1 X2 X3) = X3 -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X4 -> False)
  -> (forall X4 X3 X1 X2, ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> (esk43_3 X1 X2 X3) = (esk42_3 X1 X2 X3) -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X3 X1 X2, ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X1 X2 X3, (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> (esk43_3 X1 X2 X3) = (esk42_3 X1 X2 X3) -> False)
  -> (forall X4 X1 X2 X3, (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> (esk43_3 X1 X2 X3) = (esk42_3 X1 X2 X3) -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk43_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X1 X2 X3, ((esk41_3 X1 X2 X3) = X3 -> False) -> ((esk42_3 X1 X2 X3) = (esk41_3 X1 X2 X3) -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> X1 = X4 -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> ((k9_xtuple_0 (esk45_3 X1 X2 X3)) = (k6_subset_1 X2 (k1_tarski X1)) -> False) -> X1 = X4 -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X1 X2 X3, (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X1 X2 X3, (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> (r2_hidden (esk41_3 X1 X2 X3) (k6_subset_1 X2 (k1_tarski X1)) -> False) -> X1 = X4 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk43_3 X1 X2 X3) = X1 -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> (v1_relat_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X4 X2 X3 X1, ((esk42_3 X1 X2 X3) = X1 -> False) -> (v1_funct_1 (esk45_3 X1 X2 X3) -> False) -> X1 = X4 -> (esk41_3 X1 X2 X3) = X3 -> (esk44_3 X1 X2 X3) = X3 -> False)
  -> (forall X2 X3 X1, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X3 -> False) -> r2_hidden (esk12_3 X1 X2 X3) X2 -> False)
  -> (forall X1 X3 X2, (X3 = (k6_subset_1 X1 X2) -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X3 -> False) -> (r2_hidden (esk12_3 X1 X2 X3) X1 -> False) -> False)
  -> (forall X3 X2 X1, (r2_hidden (esk5_3 X1 X2 X3) (k9_xtuple_0 X1) -> False) -> X2 = (k10_xtuple_0 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 X2 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 X2 (esk5_3 X2 X3 X1)) = X1 -> False) -> X3 = (k10_xtuple_0 X2) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 X3 -> False)
  -> (forall X3 X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (esk6_2 X1 X2) = (k1_funct_1 X1 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden (esk6_2 X1 X2) X2 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> (k1_funct_1 X1 X2) = (k1_funct_1 X1 X3) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> r2_hidden X2 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> ((k1_funct_1 X1 (esk7_2 X1 X2)) = (esk6_2 X1 X2) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X2 = (k10_xtuple_0 X1) -> False) -> (r2_hidden (esk6_2 X1 X2) X2 -> False) -> (r2_hidden (esk7_2 X1 X2) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3 X4, (r2_hidden X3 X4 -> False) -> X4 = (k10_xtuple_0 X2) -> X3 = (k1_funct_1 X2 X1) -> v1_funct_1 X2 -> v1_relat_1 X2 -> r2_hidden X1 (k9_xtuple_0 X2) -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> (esk4_2 X1 X2) = X1 -> r2_hidden (esk4_2 X1 X2) X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> r2_hidden (esk8_2 X1 X2) X2 -> False)
  -> (forall X3 X2 X1 X4, (r2_hidden X1 X4 -> False) -> (r2_hidden X1 X3 -> False) -> X4 = (k6_subset_1 X2 X3) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X4 X3 X2 X1, X3 = (k6_subset_1 X4 X2) -> r2_hidden X1 X3 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X4 X1 X2, (r2_hidden X1 X2 -> False) -> X3 = (k6_subset_1 X2 X4) -> r2_hidden X1 X3 -> False)
  -> (forall X2 X1, (X2 = (k1_tarski X1) -> False) -> ((esk4_2 X1 X2) = X1 -> False) -> (r2_hidden (esk4_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X3 X2, (r2_hidden X3 X2 -> False) -> r2_hidden X3 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X1, ((k1_funct_1 X1 (esk10_1 X1)) = (k1_funct_1 X1 (esk9_1 X1)) -> False) -> (v2_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (r1_tarski X1 X2 -> False) -> (r2_hidden (esk8_2 X1 X2) X1 -> False) -> False)
  -> (forall X2 X1, ((k9_xtuple_0 (esk11_2 X1 X2)) = X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, ((k10_xtuple_0 (esk11_2 X1 X2)) = X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v2_funct_1 (esk11_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 (esk11_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 (esk11_2 X1 X2) -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1 X2 X3, (r2_wellord2 X2 X3 -> False) -> (k10_xtuple_0 X1) = X3 -> (k9_xtuple_0 X1) = X2 -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X2 X1, (v1_finset_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> r1_tarski X2 X1 -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r2_hidden (esk10_1 X1) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (r2_hidden (esk9_1 X1) (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v5_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_zfmisc_1 X2 -> False) -> v1_zfmisc_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v1_finset_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v6_ordinal1 X2 -> False) -> v6_ordinal1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_finset_1 (k6_subset_1 X1 X2) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X2 X1, (r2_tarski X1 X2 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X1 X2 -> False) -> r2_tarski X1 X2 -> False)
  -> (forall X2 X1, (r2_wellord2 X2 X1 -> False) -> r2_wellord2 X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_finset_1 X2 -> False) -> v5_finset_1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X1 X2, (v3_ordinal1 X2 -> False) -> v3_ordinal1 X1 -> m1_subset_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (X1 = X3 -> False) -> X2 = (k1_tarski X3) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 (k9_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v5_ordinal1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> (esk10_1 X1) = (esk9_1 X1) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk37_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (m1_subset_1 (esk36_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk35_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk32_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk19_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, (r2_hidden X1 X3 -> False) -> X1 = X2 -> X3 = (k1_tarski X2) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v1_funcop_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk32_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_funct_1 (k1_tarski X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k10_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v2_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k9_xtuple_0 X1) -> False) -> v1_finset_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k10_xtuple_0 X1) -> False) -> v1_finset_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk37_1 X1) -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_zfmisc_1 (esk36_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk35_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk22_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk19_1 X1) -> False)
  -> (forall X1, (v2_finset_1 X1 -> False) -> v1_xboole_0 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_ordinal1 X1 -> v2_ordinal1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> X1 = X2 -> False)
  -> (forall X1, (v5_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v5_finset_1 (k1_tarski X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_finset_1 (k1_zfmisc_1 X1) -> False) -> v1_finset_1 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k9_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 (k10_xtuple_0 X1) -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> (v1_finset_1 (esk37_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_zfmisc_1 (esk35_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_finset_1 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v5_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v2_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_ordinal1 X1 -> False) -> v3_ordinal1 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v1_finset_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v7_ordinal1 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v3_ordinal1 X1 -> False) -> v1_card_1 X1 -> False)
  -> (forall X1, (v1_card_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v6_ordinal1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_wellord2 (k6_subset_1 esk2_0 (k1_tarski esk1_0)) (k6_subset_1 esk2_0 (k1_tarski esk3_0)) -> False)
  -> (forall X1, v1_subset_1 (esk30_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v3_funct_1 esk33_0 -> False)
  -> (v1_zfmisc_1 esk28_0 -> False)
  -> (v1_xboole_0 esk40_0 -> False)
  -> (v1_xboole_0 esk39_0 -> False)
  -> (v1_xboole_0 esk38_0 -> False)
  -> (v1_xboole_0 esk34_0 -> False)
  -> (v1_xboole_0 esk29_0 -> False)
  -> (v1_xboole_0 esk27_0 -> False)
  -> (v1_xboole_0 esk25_0 -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk21_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (forall X1 X2, (m1_subset_1 (k6_subset_1 X1 X2) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk30_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk26_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, (r2_wellord2 X1 X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k6_subset_1 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((r2_hidden esk3_0 esk2_0 -> False) -> False)
  -> ((r2_hidden esk1_0 esk2_0 -> False) -> False)
  -> (forall X1, (v1_zfmisc_1 (k1_tarski X1) -> False) -> False)
  -> (forall X1, (v1_finset_1 (k1_tarski X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk26_1 X1) -> False) -> False)
  -> ((v2_finset_1 esk40_0 -> False) -> False)
  -> ((v4_funct_1 esk38_0 -> False) -> False)
  -> ((v7_ordinal1 esk34_0 -> False) -> False)
  -> ((v7_ordinal1 esk31_0 -> False) -> False)
  -> ((v5_finset_1 esk39_0 -> False) -> False)
  -> ((v3_funct_1 esk23_0 -> False) -> False)
  -> ((v2_funct_1 esk24_0 -> False) -> False)
  -> ((v1_funcop_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk40_0 -> False) -> False)
  -> ((v1_relat_1 esk33_0 -> False) -> False)
  -> ((v1_relat_1 esk29_0 -> False) -> False)
  -> ((v1_relat_1 esk24_0 -> False) -> False)
  -> ((v1_relat_1 esk23_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_zfmisc_1 esk21_0 -> False) -> False)
  -> ((v2_ordinal1 esk25_0 -> False) -> False)
  -> ((v1_ordinal1 esk25_0 -> False) -> False)
  -> ((v1_funct_1 esk40_0 -> False) -> False)
  -> ((v1_funct_1 esk33_0 -> False) -> False)
  -> ((v1_funct_1 esk29_0 -> False) -> False)
  -> ((v1_funct_1 esk24_0 -> False) -> False)
  -> ((v1_funct_1 esk23_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_finset_1 esk39_0 -> False) -> False)
  -> ((v1_finset_1 esk29_0 -> False) -> False)
  -> ((v1_finset_1 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 esk20_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v3_ordinal1 esk25_0 -> False) -> False)
  -> ((v3_ordinal1 esk18_0 -> False) -> False)
  -> ((v1_card_1 esk14_0 -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> False.
Admitted.
