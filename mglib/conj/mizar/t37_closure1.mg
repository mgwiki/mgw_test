(** $I sig/MizarPreamble.mgs **)

Theorem t37_closure1:
 forall r2_pboole:set -> set -> set -> prop,
 forall v4_mssubfam:set -> set -> set -> prop,
 forall esk23_5:set -> set -> set -> set -> set -> set,
 forall v2_relat_1:set -> prop,
 forall v3_closure1:set -> set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall v1_funcop_1:set -> prop,
 forall v6_mssubfam:set -> set -> set -> prop,
 forall v2_mssubfam:set -> set -> set -> prop,
 forall v3_mssubfam:set -> set -> set -> prop,
 forall k3_mssubfam:set -> set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall esk21_2:set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall esk19_1:set -> set,
 forall esk17_1:set -> set,
 forall esk22_1:set -> set,
 forall esk16_0:set,
 forall esk12_0:set,
 forall esk15_0:set,
 forall esk11_0:set,
 forall esk13_1:set -> set,
 forall esk18_1:set -> set,
 forall v2_funcop_1:set -> prop,
 forall esk8_2:set -> set -> set,
 forall esk20_2:set -> set -> set,
 forall k16_pralg_1:set -> set -> set -> set,
 forall v1_mssubfam:set -> set -> set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k15_pralg_1:set -> set -> set,
 forall esk3_0:set,
 forall esk5_2:set -> set -> set,
 forall esk1_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk24_4:set -> set -> set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall r1_pboole:set -> set -> set -> prop,
 forall k1_mboolean:set -> set -> set,
 forall m3_pboole:set -> set -> set -> prop,
 forall m2_pboole:set -> set -> set -> set -> prop,
 forall k4_mssubfam:set -> set -> set -> set,
 forall esk26_5:set -> set -> set -> set -> set -> set,
 forall esk25_5:set -> set -> set -> set -> set -> set,
 forall m1_pboole:set -> set -> set -> prop,
 forall k5_mssubfam:set -> set -> set,
 forall v5_mssubfam:set -> set -> set -> prop,
 forall v1_partfun1:set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall r6_pboole:set -> set -> set -> prop,
 forall k2_closure1:set -> set -> set -> set -> set,
     (forall X4 X5 X2 X3 X1, (r6_pboole X1 (k2_closure1 X1 X2 X3 X5) X5 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> r1_pboole X1 X5 X4 -> v5_mssubfam X4 X1 X2 -> m3_pboole X4 X1 (k1_mboolean X1 X2) -> m1_pboole X5 X1 (k5_mssubfam X1 X2) -> m2_pboole X3 X1 (k5_mssubfam X1 X2) (k5_mssubfam X1 X2) -> r6_pboole X1 (k2_closure1 X1 X2 X3 (esk25_5 X1 X2 X4 X5 X3)) (k4_mssubfam X1 X2 (esk26_5 X1 X2 X4 X5 X3)) -> False)
  -> (forall X2 X4 X3 X5 X1, (r2_pboole X1 X5 X3 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X5 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> v4_mssubfam X3 X1 X2 -> m3_pboole X5 X1 (k1_mboolean X1 X2) -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> r2_pboole X1 X4 (esk23_5 X1 X2 X3 X4 X5) -> r1_pboole X1 (esk23_5 X1 X2 X3 X4 X5) X5 -> r1_pboole X1 (esk23_5 X1 X2 X3 X4 X5) X3 -> False)
  -> (forall X3 X2 X5 X4 X6 X1, (r6_pboole X1 (k2_closure1 X1 X4 X6 X5) X5 -> False) -> (r1_pboole X1 X2 (esk26_5 X1 X4 X3 X5 X6) -> False) -> v1_relat_1 X4 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X2 -> v4_relat_1 X4 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X4 X1 -> v1_partfun1 X2 X1 -> r1_pboole X1 X5 X3 -> r1_pboole X1 X2 X3 -> v5_mssubfam X3 X1 X4 -> m3_pboole X3 X1 (k1_mboolean X1 X4) -> m1_pboole X5 X1 (k5_mssubfam X1 X4) -> r2_pboole X1 (esk25_5 X1 X4 X3 X5 X6) X2 -> m2_pboole X6 X1 (k5_mssubfam X1 X4) (k5_mssubfam X1 X4) -> False)
  -> (forall X6 X3 X4 X2 X5 X1, (r6_pboole X1 (k2_closure1 X1 X2 X5 X4) X4 -> False) -> (r2_pboole X1 (esk25_5 X1 X2 X3 X4 X5) X6 -> False) -> v1_relat_1 X6 -> v1_relat_1 X2 -> v1_funct_1 X6 -> v1_funct_1 X2 -> v4_relat_1 X6 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X6 X1 -> v1_partfun1 X2 X1 -> r1_pboole X1 X4 X3 -> v5_mssubfam X3 X1 X2 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> r1_pboole X1 X6 (esk26_5 X1 X2 X3 X4 X5) -> m2_pboole X5 X1 (k5_mssubfam X1 X2) (k5_mssubfam X1 X2) -> False)
  -> (forall X2 X4 X3 X5 X1, (r2_pboole X1 X5 X3 -> False) -> (r1_pboole X1 (esk23_5 X1 X2 X3 X4 X5) X5 -> False) -> (r1_pboole X1 (esk23_5 X1 X2 X3 X4 X5) X3 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X5 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> v4_mssubfam X3 X1 X2 -> m3_pboole X5 X1 (k1_mboolean X1 X2) -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> False)
  -> (forall X3 X2 X4 X5 X1, (r2_pboole X1 X5 X4 -> False) -> (r2_pboole X1 X2 (esk23_5 X1 X3 X4 X2 X5) -> False) -> (r1_pboole X1 (esk23_5 X1 X3 X4 X2 X5) X5 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v2_relat_1 X5 -> v4_relat_1 X3 X1 -> v1_partfun1 X3 X1 -> v4_mssubfam X4 X1 X3 -> m3_pboole X5 X1 (k1_mboolean X1 X3) -> m3_pboole X4 X1 (k1_mboolean X1 X3) -> m1_pboole X2 X1 (k5_mssubfam X1 X3) -> False)
  -> (forall X6 X4 X5 X3 X2 X1, (r1_pboole X1 X2 X3 -> False) -> (r6_pboole X1 (k2_closure1 X1 X4 X6 X5) X5 -> False) -> v1_relat_1 X4 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X2 -> v4_relat_1 X4 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X4 X1 -> v1_partfun1 X2 X1 -> r1_pboole X1 X5 X3 -> v5_mssubfam X3 X1 X4 -> m3_pboole X3 X1 (k1_mboolean X1 X4) -> m1_pboole X5 X1 (k5_mssubfam X1 X4) -> r1_pboole X1 X2 (esk26_5 X1 X4 X3 X5 X6) -> m2_pboole X6 X1 (k5_mssubfam X1 X4) (k5_mssubfam X1 X4) -> False)
  -> (forall X3 X1 X2, (v3_closure1 X3 X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m2_pboole X3 X1 (k5_mssubfam X1 X2) (k5_mssubfam X1 X2) -> r6_pboole X1 (k2_closure1 X1 X2 X3 (esk6_3 X1 X2 X3)) (k2_closure1 X1 X2 X3 (k2_closure1 X1 X2 X3 (esk6_3 X1 X2 X3))) -> False)
  -> (forall X3 X4 X2 X5 X1, (r6_pboole X1 (k2_closure1 X1 X2 X5 X4) X4 -> False) -> (m1_pboole (esk25_5 X1 X2 X3 X4 X5) X1 (k5_mssubfam X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> r1_pboole X1 X4 X3 -> v5_mssubfam X3 X1 X2 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> m2_pboole X5 X1 (k5_mssubfam X1 X2) (k5_mssubfam X1 X2) -> False)
  -> (forall X3 X4 X2 X5 X1, (r6_pboole X1 (k2_closure1 X1 X2 X5 X4) X4 -> False) -> (m3_pboole (esk26_5 X1 X2 X3 X4 X5) X1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> r1_pboole X1 X4 X3 -> v5_mssubfam X3 X1 X2 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> m2_pboole X5 X1 (k5_mssubfam X1 X2) (k5_mssubfam X1 X2) -> False)
  -> (forall X3 X4 X2 X5 X1, (v2_relat_1 (esk26_5 X1 X2 X3 X4 X5) -> False) -> (r6_pboole X1 (k2_closure1 X1 X2 X5 X4) X4 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> r1_pboole X1 X4 X3 -> v5_mssubfam X3 X1 X2 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> m2_pboole X5 X1 (k5_mssubfam X1 X2) (k5_mssubfam X1 X2) -> False)
  -> (forall X2 X4 X3 X5 X1, (r2_pboole X1 X5 X3 -> False) -> (v1_partfun1 (esk23_5 X1 X2 X3 X4 X5) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X5 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> v4_mssubfam X3 X1 X2 -> m3_pboole X5 X1 (k1_mboolean X1 X2) -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> False)
  -> (forall X2 X4 X3 X5 X1, (r2_pboole X1 X5 X3 -> False) -> (v4_relat_1 (esk23_5 X1 X2 X3 X4 X5) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X5 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> v4_mssubfam X3 X1 X2 -> m3_pboole X5 X1 (k1_mboolean X1 X2) -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> False)
  -> (forall X2 X4 X3 X5 X1, (r2_pboole X1 X5 X3 -> False) -> (v1_funct_1 (esk23_5 X1 X2 X3 X4 X5) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X5 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> v4_mssubfam X3 X1 X2 -> m3_pboole X5 X1 (k1_mboolean X1 X2) -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> False)
  -> (forall X2 X4 X3 X5 X1, (r2_pboole X1 X5 X3 -> False) -> (v1_relat_1 (esk23_5 X1 X2 X3 X4 X5) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X5 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> v4_mssubfam X3 X1 X2 -> m3_pboole X5 X1 (k1_mboolean X1 X2) -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> False)
  -> (forall X4 X1 X2 X3, (r6_pboole X2 (k2_closure1 X2 X3 X1 X4) (k2_closure1 X2 X3 X1 (k2_closure1 X2 X3 X1 X4)) -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> v3_closure1 X1 X2 X3 -> m1_pboole X4 X2 (k5_mssubfam X2 X3) -> m2_pboole X1 X2 (k5_mssubfam X2 X3) (k5_mssubfam X2 X3) -> False)
  -> (forall X4 X5 X3 X2 X1, (r2_pboole X1 X2 X3 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v4_relat_1 X4 X1 -> v4_relat_1 X3 X1 -> v1_partfun1 X4 X1 -> v1_partfun1 X3 X1 -> v5_mssubfam X5 X1 X4 -> m3_pboole X5 X1 (k1_mboolean X1 X4) -> m1_pboole X2 X1 (k5_mssubfam X1 X4) -> r1_pboole X1 X3 (esk24_4 X1 X4 X5 X2) -> False)
  -> (forall X4 X5 X3 X2 X1, (r1_pboole X1 X2 X3 -> False) -> v1_relat_1 X4 -> v1_relat_1 X2 -> v1_funct_1 X4 -> v1_funct_1 X2 -> v4_relat_1 X4 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X4 X1 -> v1_partfun1 X2 X1 -> v5_mssubfam X3 X1 X4 -> m3_pboole X3 X1 (k1_mboolean X1 X4) -> m1_pboole X5 X1 (k5_mssubfam X1 X4) -> r1_pboole X1 X2 (esk24_4 X1 X4 X3 X5) -> False)
  -> (forall X1 X2, (r6_pboole esk1_0 (k2_closure1 esk1_0 esk2_0 esk4_0 X1) (k4_mssubfam esk1_0 esk2_0 X2) -> False) -> v2_relat_1 X2 -> r2_pboole esk1_0 X1 (esk5_2 X1 X2) -> r1_pboole esk1_0 (esk5_2 X1 X2) X2 -> r1_pboole esk1_0 (esk5_2 X1 X2) esk3_0 -> m3_pboole X2 esk1_0 (k1_mboolean esk1_0 esk2_0) -> m1_pboole X1 esk1_0 (k5_mssubfam esk1_0 esk2_0) -> False)
  -> (forall X4 X3 X2 X1, (m1_pboole (k2_closure1 X2 X1 X3 X4) X2 (k5_mssubfam X2 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> m1_pboole X4 X2 (k5_mssubfam X2 X1) -> m2_pboole X3 X2 (k5_mssubfam X2 X1) (k5_mssubfam X2 X1) -> False)
  -> (forall X2 X4 X3 X1 X5, (r1_pboole X1 X2 (esk24_4 X1 X5 X3 X4) -> False) -> v1_relat_1 X5 -> v1_relat_1 X2 -> v1_funct_1 X5 -> v1_funct_1 X2 -> v4_relat_1 X5 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X5 X1 -> v1_partfun1 X2 X1 -> r1_pboole X1 X2 X3 -> r2_pboole X1 X4 X2 -> v5_mssubfam X3 X1 X5 -> m3_pboole X3 X1 (k1_mboolean X1 X5) -> m1_pboole X4 X1 (k5_mssubfam X1 X5) -> False)
  -> (forall X1 X2, (r2_pboole esk1_0 X1 (esk5_2 X1 X2) -> False) -> (r1_pboole esk1_0 (esk5_2 X1 X2) X2 -> False) -> (r6_pboole esk1_0 (k2_closure1 esk1_0 esk2_0 esk4_0 X1) (k4_mssubfam esk1_0 esk2_0 X2) -> False) -> v2_relat_1 X2 -> m3_pboole X2 esk1_0 (k1_mboolean esk1_0 esk2_0) -> m1_pboole X1 esk1_0 (k5_mssubfam esk1_0 esk2_0) -> False)
  -> (forall X1 X2, (r1_pboole esk1_0 (esk5_2 X1 X2) X2 -> False) -> (r1_pboole esk1_0 (esk5_2 X1 X2) esk3_0 -> False) -> (r6_pboole esk1_0 (k2_closure1 esk1_0 esk2_0 esk4_0 X1) (k4_mssubfam esk1_0 esk2_0 X2) -> False) -> v2_relat_1 X2 -> m3_pboole X2 esk1_0 (k1_mboolean esk1_0 esk2_0) -> m1_pboole X1 esk1_0 (k5_mssubfam esk1_0 esk2_0) -> False)
  -> (forall X4 X3 X1 X2, (m3_pboole (esk24_4 X1 X2 X3 X4) X1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> v5_mssubfam X3 X1 X2 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> False)
  -> (forall X4 X3 X2 X1, ((k2_closure1 X2 X1 X3 X4) = (k15_pralg_1 X3 X4) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> m1_pboole X4 X2 (k5_mssubfam X2 X1) -> m2_pboole X3 X2 (k5_mssubfam X2 X1) (k5_mssubfam X2 X1) -> False)
  -> (forall X1 X2, (v1_partfun1 (esk5_2 X1 X2) esk1_0 -> False) -> (r6_pboole esk1_0 (k2_closure1 esk1_0 esk2_0 esk4_0 X1) (k4_mssubfam esk1_0 esk2_0 X2) -> False) -> v2_relat_1 X2 -> m3_pboole X2 esk1_0 (k1_mboolean esk1_0 esk2_0) -> m1_pboole X1 esk1_0 (k5_mssubfam esk1_0 esk2_0) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk5_2 X1 X2) esk1_0 -> False) -> (r6_pboole esk1_0 (k2_closure1 esk1_0 esk2_0 esk4_0 X1) (k4_mssubfam esk1_0 esk2_0 X2) -> False) -> v2_relat_1 X2 -> m3_pboole X2 esk1_0 (k1_mboolean esk1_0 esk2_0) -> m1_pboole X1 esk1_0 (k5_mssubfam esk1_0 esk2_0) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk5_2 X1 X2) -> False) -> (r6_pboole esk1_0 (k2_closure1 esk1_0 esk2_0 esk4_0 X1) (k4_mssubfam esk1_0 esk2_0 X2) -> False) -> v2_relat_1 X2 -> m3_pboole X2 esk1_0 (k1_mboolean esk1_0 esk2_0) -> m1_pboole X1 esk1_0 (k5_mssubfam esk1_0 esk2_0) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk5_2 X1 X2) -> False) -> (r6_pboole esk1_0 (k2_closure1 esk1_0 esk2_0 esk4_0 X1) (k4_mssubfam esk1_0 esk2_0 X2) -> False) -> v2_relat_1 X2 -> m3_pboole X2 esk1_0 (k1_mboolean esk1_0 esk2_0) -> m1_pboole X1 esk1_0 (k5_mssubfam esk1_0 esk2_0) -> False)
  -> (forall X4 X3 X1 X2, (v2_relat_1 (esk24_4 X1 X2 X3 X4) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> v5_mssubfam X3 X1 X2 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> m1_pboole X4 X1 (k5_mssubfam X1 X2) -> False)
  -> (forall X3 X1 X2, (v4_mssubfam X3 X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> r1_pboole X1 (k4_mssubfam X1 X2 (esk7_3 X1 X2 X3)) X3 -> False)
  -> (forall X3 X1 X2, (v3_closure1 X3 X1 X2 -> False) -> (m1_pboole (esk6_3 X1 X2 X3) X1 (k5_mssubfam X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m2_pboole X3 X1 (k5_mssubfam X1 X2) (k5_mssubfam X1 X2) -> False)
  -> (forall X4 X1 X2 X3, (r1_pboole X2 (k4_mssubfam X2 X3 X4) X1 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> v4_mssubfam X1 X2 X3 -> r2_pboole X2 X4 X1 -> m3_pboole X4 X2 (k1_mboolean X2 X3) -> m3_pboole X1 X2 (k1_mboolean X2 X3) -> False)
  -> (forall X4 X3 X1 X2, (v1_partfun1 X1 X2 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X4 X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X3 X2 X1 X4, (v1_funcop_1 X4 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> m2_pboole X4 X2 X1 X3 -> False)
  -> (forall X4 X2 X3 X1, (v1_funct_1 X1 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 X1 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> m2_pboole X1 X2 X3 X4 -> False)
  -> (forall X1 X2 X3, (m2_pboole (esk9_3 X2 X1 X3) X2 X1 X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X1 X2, (v4_mssubfam X3 X1 X2 -> False) -> (m3_pboole (esk7_3 X1 X2 X3) X1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> False)
  -> (forall X3 X4 X1 X2, (r1_pboole X2 X1 X4 -> False) -> v1_relat_1 X4 -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X4 X2 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X4 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r1_pboole X2 X1 X3 -> r2_pboole X2 X3 X4 -> False)
  -> (forall X3 X1 X2, (v4_mssubfam X3 X1 X2 -> False) -> (r2_pboole X1 (esk7_3 X1 X2 X3) X3 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> False)
  -> (forall X3 X2 X1, (m3_pboole (k4_mssubfam X2 X1 X3) X2 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> m3_pboole X3 X2 (k1_mboolean X2 X1) -> False)
  -> (forall X3 X2 X1, (v6_mssubfam X3 X2 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> v2_mssubfam X3 X2 X1 -> m3_pboole X3 X2 (k1_mboolean X2 X1) -> False)
  -> (forall X3 X2 X1, (v5_mssubfam X3 X2 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> v4_mssubfam X3 X2 X1 -> m3_pboole X3 X2 (k1_mboolean X2 X1) -> False)
  -> (forall X3 X2 X1, (v3_mssubfam X3 X2 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> v4_mssubfam X3 X2 X1 -> m3_pboole X3 X2 (k1_mboolean X2 X1) -> False)
  -> (forall X3 X2 X1, (v1_mssubfam X3 X2 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> v2_mssubfam X3 X2 X1 -> m3_pboole X3 X2 (k1_mboolean X2 X1) -> False)
  -> (forall X3 X1 X2, (v1_partfun1 (k3_mssubfam X1 X2 X3) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 (k3_mssubfam X1 X2 X3) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> False)
  -> (forall X3 X1 X2, (v1_funct_1 (k3_mssubfam X1 X2 X3) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> False)
  -> (forall X3 X1 X2, (v1_relat_1 (k3_mssubfam X1 X2 X3) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> m3_pboole X3 X1 (k1_mboolean X1 X2) -> False)
  -> (forall X3 X2 X1, ((k3_mssubfam X2 X1 X3) = (k4_mssubfam X2 X1 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> m3_pboole X3 X2 (k1_mboolean X2 X1) -> False)
  -> (forall X1 X2 X3, (v2_relat_1 X3 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> v6_mssubfam X3 X2 X1 -> m3_pboole X3 X2 (k1_mboolean X2 X1) -> False)
  -> (forall X1 X2 X3, (v2_relat_1 X3 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> v5_mssubfam X3 X2 X1 -> m3_pboole X3 X2 (k1_mboolean X2 X1) -> False)
  -> (forall X1 X2 X3, (r6_pboole X2 X3 X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r6_pboole X2 X1 X3 -> False)
  -> (forall X1 X2 X3, (r2_pboole X2 X1 X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> m3_pboole X1 X2 X3 -> False)
  -> (forall X1 X2 X3, (m1_pboole X1 X2 X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> r1_pboole X2 X1 X3 -> False)
  -> (forall X2 X1 X3, (m3_pboole X2 X1 X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> r2_pboole X1 X2 X3 -> False)
  -> (forall X2 X1 X3, (v1_funct_1 (k16_pralg_1 X1 X2 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funcop_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_relat_1 (k16_pralg_1 X1 X2 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funcop_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2 X3, (X2 = X3 -> False) -> v1_relat_1 X3 -> v1_relat_1 X2 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v4_relat_1 X3 X1 -> v4_relat_1 X2 X1 -> v1_partfun1 X3 X1 -> v1_partfun1 X2 X1 -> r6_pboole X1 X2 X3 -> False)
  -> (forall X1 X2 X3, ((k16_pralg_1 X2 X1 X3) = (k15_pralg_1 X1 X3) -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X1 X2, (r6_pboole X3 X1 X2 -> False) -> X1 = X2 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (r6_pboole X2 X1 X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X3 X2 X1, (r2_pboole X2 X1 X1 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v1_funct_1 X3 -> v1_funct_1 X1 -> v4_relat_1 X3 X2 -> v4_relat_1 X1 X2 -> v1_partfun1 X3 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X3 X2, (v1_partfun1 (k15_pralg_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v1_partfun1 (k15_pralg_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k15_pralg_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k15_pralg_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1 X3 X2, (v4_relat_1 (k15_pralg_1 X1 X2) X3 -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X1 X2, (m3_pboole (esk20_2 X1 X2) X1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (m3_pboole (esk14_2 X1 X2) X1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (m3_pboole (k5_mssubfam X1 X2) X1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X3 X1 X2, (v1_partfun1 X1 X2 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> m1_pboole X1 X2 X3 -> False)
  -> (forall X3 X1 X2, (v1_partfun1 X1 X2 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> m3_pboole X1 X2 X3 -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> m1_pboole X1 X2 X3 -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> m3_pboole X1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k15_pralg_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k15_pralg_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 (k15_pralg_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k15_pralg_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k15_pralg_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 (k15_pralg_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> v4_relat_1 X2 X3 -> v4_relat_1 X1 X3 -> v1_partfun1 X2 X3 -> v1_partfun1 X1 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 X1 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> m1_pboole X1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_funct_1 X1 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> m3_pboole X1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> m1_pboole X1 X2 X3 -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> v1_relat_1 X3 -> v1_funct_1 X3 -> v4_relat_1 X3 X2 -> v1_partfun1 X3 X2 -> m3_pboole X1 X2 X3 -> False)
  -> (forall X1 X2, (m3_pboole (esk21_2 X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v6_mssubfam (esk20_2 X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v6_mssubfam (k5_mssubfam X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v5_mssubfam (esk20_2 X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v5_mssubfam (k5_mssubfam X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v3_mssubfam (esk20_2 X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v3_mssubfam (k5_mssubfam X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_mssubfam (esk20_2 X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_mssubfam (k5_mssubfam X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v2_mssubfam (esk20_2 X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v2_mssubfam (k5_mssubfam X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1, (m1_pboole (esk8_2 X2 X1) X2 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X2 X1, (m3_pboole (esk10_2 X2 X1) X2 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v4_mssubfam (esk20_2 X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v4_mssubfam (k5_mssubfam X1 X2) X1 X2 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_partfun1 (esk21_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v4_relat_1 (esk21_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_partfun1 (esk20_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_partfun1 (esk14_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_partfun1 (k1_mboolean X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v4_relat_1 (esk20_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v4_relat_1 (esk14_2 X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v4_relat_1 (k1_mboolean X1 X2) X1 -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v2_relat_1 (esk21_2 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (esk21_2 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (esk21_2 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v2_relat_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v2_relat_1 (esk20_2 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v2_relat_1 (esk14_2 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (esk20_2 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (esk14_2 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (esk20_2 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (esk14_2 X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k1_mboolean X1 X2) -> False) -> v1_relat_1 X2 -> v1_funct_1 X2 -> v4_relat_1 X2 X1 -> v1_partfun1 X2 X1 -> False)
  -> (forall X2 X1, ((k5_mssubfam X2 X1) = (k1_mboolean X2 X1) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v4_relat_1 X1 X2 -> v1_partfun1 X1 X2 -> False)
  -> (forall X1 X2, (v1_funct_1 (k15_pralg_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k15_pralg_1 X1 X2) -> False) -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (forall X1, (v2_funcop_1 X1 -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> v1_funcop_1 X1 -> False)
  -> (v3_closure1 esk4_0 esk1_0 esk2_0 -> False)
  -> ((m2_pboole esk4_0 esk1_0 (k5_mssubfam esk1_0 esk2_0) (k5_mssubfam esk1_0 esk2_0) -> False) -> False)
  -> ((m3_pboole esk3_0 esk1_0 (k1_mboolean esk1_0 esk2_0) -> False) -> False)
  -> ((v4_mssubfam esk3_0 esk1_0 esk2_0 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_partfun1 (esk13_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk22_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk19_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk17_1 X1) X1 -> False) -> False)
  -> (forall X1, (v4_relat_1 (esk13_1 X1) X1 -> False) -> False)
  -> ((v1_partfun1 esk2_0 esk1_0 -> False) -> False)
  -> ((v4_relat_1 esk2_0 esk1_0 -> False) -> False)
  -> (forall X1, (v1_funcop_1 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v2_relat_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v1_funct_1 (esk13_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk22_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk19_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk18_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk17_1 X1) -> False) -> False)
  -> (forall X1, (v1_relat_1 (esk13_1 X1) -> False) -> False)
  -> ((v1_funcop_1 esk11_0 -> False) -> False)
  -> ((v2_relat_1 esk16_0 -> False) -> False)
  -> ((v2_relat_1 esk15_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk11_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_relat_1 esk12_0 -> False) -> False)
  -> ((v1_relat_1 esk11_0 -> False) -> False)
  -> ((v1_relat_1 esk2_0 -> False) -> False)
  -> False.
Admitted.
