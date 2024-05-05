(** $I sig/MizarPreamble.mgs **)

Theorem t41_bvfunc_3:
 forall k16_margrel1:set -> set -> set -> set,
 forall esk15_4:set -> set -> set -> set -> set,
 forall k10_margrel1:set -> set -> set,
 forall k17_bvfunc_1:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k15_bvfunc_1:set -> set -> set -> set,
 forall esk12_4:set -> set -> set -> set -> set,
 forall esk13_4:set -> set -> set -> set -> set,
 forall k15_margrel1:set -> set -> set,
 forall esk14_3:set -> set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall k7_bvfunc_2:set -> set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k1_bvfunc_1:set -> set -> set,
 forall k11_eqrel_1:set -> set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall esk20_2:set -> set -> set,
 forall esk17_2:set -> set -> set,
 forall v1_xboolean:set -> prop,
 forall k3_xboolean:set -> set,
 forall k4_xboolean:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall epred1_2:set -> set -> prop,
 forall k3_xcmplx_0:set -> set -> set,
 forall np__1:set,
 forall k6_xcmplx_0:set -> set -> set,
 forall k1_xboolean:set,
 forall k2_xboolean:set,
 forall esk1_0:set,
 forall esk3_0:set,
 forall esk6_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk5_0:set,
 forall esk18_1:set -> set,
 forall esk22_0:set,
 forall esk21_0:set,
 forall k4_ordinal1:set,
 forall esk19_1:set -> set,
 forall v1_eqrel_1:set -> set -> prop,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall k6_numbers:set,
 forall esk23_0:set,
 forall k1_xboole_0:set,
 forall v2_card_3:set -> prop,
 forall v1_margrel1:set -> prop,
 forall m1_bvfunc_1:set -> set -> set -> prop,
 forall k13_margrel1:set -> set,
 forall k7_bvfunc_1:set -> set -> set,
 forall k14_margrel1:set -> set -> set,
 forall k2_bvfunc_1:set -> set -> set -> set,
 forall k5_bvfunc_2:set -> set -> set -> set,
 forall k6_bvfunc_2:set -> set -> set -> set -> set,
 forall k1_bvfunc_2:set -> set,
 forall r1_bvfunc_1:set -> set -> set -> prop,
 forall esk11_5:set -> set -> set -> set -> set -> set,
 forall k7_margrel1:set,
 forall esk9_4:set -> set -> set -> set -> set,
 forall esk10_4:set -> set -> set -> set -> set,
 forall esk8_5:set -> set -> set -> set -> set -> set,
 forall m1_eqrel_1:set -> set -> prop,
 forall k16_bvfunc_1:set -> set -> set -> set,
 forall k8_margrel1:set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k5_xboolean:set -> set -> set,
 forall k9_margrel1:set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall esk16_4:set -> set -> set -> set -> set,
 forall k6_margrel1:set,
 forall k9_bvfunc_1:set -> set -> set -> set,
     (forall X4 X2 X3 X1, (X2 = (k9_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (k5_xboolean (k9_margrel1 (k3_funct_2 X1 k6_margrel1 X3 (esk16_4 X1 X3 X4 X2))) (k3_funct_2 X1 k6_margrel1 X4 (esk16_4 X1 X3 X4 X2))) = (k3_funct_2 X1 k6_margrel1 X2 (esk16_4 X1 X3 X4 X2)) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X2 X3 X1, (X2 = (k16_margrel1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (k10_margrel1 (k3_funct_2 X1 k6_margrel1 X3 (esk15_4 X1 X3 X4 X2)) (k3_funct_2 X1 k6_margrel1 X4 (esk15_4 X1 X3 X4 X2))) = (k3_funct_2 X1 k6_margrel1 X2 (esk15_4 X1 X3 X4 X2)) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> X4 = (k16_bvfunc_1 X1 X2 X3) -> (k3_funct_2 X1 k6_margrel1 X2 (esk8_5 X1 X2 X3 X4 X5)) = k8_margrel1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X4 X3 X2 X5, (X5 = (k17_bvfunc_1 X2 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk13_4 X2 X3 X4 X5) (k15_bvfunc_1 X2 (esk12_4 X2 X3 X4 X5) X4) -> False) -> (k3_funct_2 X2 k6_margrel1 X3 X1) = k8_margrel1 -> v1_funct_1 X5 -> v1_funct_1 X3 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X5 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> r2_hidden X1 (k15_bvfunc_1 X2 (esk12_4 X2 X3 X4 X5) X4) -> False)
  -> (forall X5 X3 X2 X1 X4, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> ((k3_funct_2 X1 k6_margrel1 X2 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) (k15_bvfunc_1 X1 (esk9_4 X1 X2 X3 X4) X3) -> False) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> r2_hidden X5 (k15_bvfunc_1 X1 (esk9_4 X1 X2 X3 X4) X3) -> False)
  -> (forall X1 X4 X3 X2 X5, (X5 = (k17_bvfunc_1 X2 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (k3_funct_2 X2 k6_margrel1 X3 X1) = k8_margrel1 -> (k3_funct_2 X2 k6_margrel1 X5 (esk12_4 X2 X3 X4 X5)) = k8_margrel1 -> v1_funct_1 X5 -> v1_funct_1 X3 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X5 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> r2_hidden X1 (k15_bvfunc_1 X2 (esk12_4 X2 X3 X4 X5) X4) -> False)
  -> (forall X5 X4 X3 X1 X2, (X2 = (k16_bvfunc_1 X1 X3 X4) -> False) -> ((k3_funct_2 X1 k6_margrel1 X3 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk9_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> r2_hidden X5 (k15_bvfunc_1 X1 (esk9_4 X1 X3 X4 X2) X4) -> False)
  -> (forall X5 X3 X2 X1 X4, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> ((k3_funct_2 X1 k6_margrel1 X2 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk10_4 X1 X2 X3 X4)) = k8_margrel1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> r2_hidden X5 (k15_bvfunc_1 X1 (esk9_4 X1 X2 X3 X4) X3) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k7_margrel1 -> False) -> ((k3_funct_2 X1 k6_margrel1 X2 (esk11_5 X1 X2 X3 X4 X5)) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> X4 = (k17_bvfunc_1 X1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X4 X3 X2 X5, (X5 = (k17_bvfunc_1 X2 X3 X4) -> False) -> ((k3_funct_2 X2 k6_margrel1 X3 (esk13_4 X2 X3 X4 X5)) = k8_margrel1 -> False) -> (v1_xboole_0 X2 -> False) -> (k3_funct_2 X2 k6_margrel1 X3 X1) = k8_margrel1 -> v1_funct_1 X5 -> v1_funct_1 X3 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X5 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> r2_hidden X1 (k15_bvfunc_1 X2 (esk12_4 X2 X3 X4 X5) X4) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k7_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk11_5 X1 X2 X3 X4 X5) (k15_bvfunc_1 X1 X5 X3) -> False) -> X4 = (k17_bvfunc_1 X1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk8_5 X1 X2 X3 X4 X5) (k15_bvfunc_1 X1 X5 X3) -> False) -> X4 = (k16_bvfunc_1 X1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k17_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk13_4 X1 X3 X4 X2) (k15_bvfunc_1 X1 (esk12_4 X1 X3 X4 X2) X4) -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk12_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk10_4 X1 X2 X3 X4) (k15_bvfunc_1 X1 (esk9_4 X1 X2 X3 X4) X3) -> False) -> (k3_funct_2 X1 k6_margrel1 X4 (esk9_4 X1 X2 X3 X4)) = k8_margrel1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k7_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk11_5 X1 X2 X3 X4 X5) X1 -> False) -> X4 = (k17_bvfunc_1 X1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk8_5 X1 X2 X3 X4 X5) X1 -> False) -> X4 = (k16_bvfunc_1 X1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X4 X3 X2 X5, (X5 = (k17_bvfunc_1 X2 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk13_4 X2 X3 X4 X5) X2 -> False) -> (k3_funct_2 X2 k6_margrel1 X3 X1) = k8_margrel1 -> v1_funct_1 X5 -> v1_funct_1 X3 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X5 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> r2_hidden X1 (k15_bvfunc_1 X2 (esk12_4 X2 X3 X4 X5) X4) -> False)
  -> (forall X5 X3 X2 X1 X4, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> ((k3_funct_2 X1 k6_margrel1 X2 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> r2_hidden X5 (k15_bvfunc_1 X1 (esk9_4 X1 X2 X3 X4) X3) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k16_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk9_4 X1 X3 X4 X2)) = k8_margrel1 -> (k3_funct_2 X1 k6_margrel1 X2 (esk9_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k17_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk12_4 X1 X3 X4 X2)) = k8_margrel1 -> (k3_funct_2 X1 k6_margrel1 X2 (esk12_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X4 (esk9_4 X1 X2 X3 X4)) = k8_margrel1 -> (k3_funct_2 X1 k6_margrel1 X2 (esk10_4 X1 X2 X3 X4)) = k8_margrel1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X3 X4 X5 X2, ((k3_funct_2 X2 k6_margrel1 X1 X5) = (k5_xboolean (k9_margrel1 (k3_funct_2 X2 k6_margrel1 X3 X5)) (k3_funct_2 X2 k6_margrel1 X4 X5)) -> False) -> (v1_xboole_0 X2 -> False) -> X1 = (k9_bvfunc_1 X2 X3 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X5 X2 -> v1_funct_2 X4 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k17_bvfunc_1 X1 X3 X4) -> False) -> ((k3_funct_2 X1 k6_margrel1 X3 (esk13_4 X1 X3 X4 X2)) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk12_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k17_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_4 X1 X3 X4 X2) X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk12_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X4 (esk9_4 X1 X2 X3 X4)) = k8_margrel1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (X2 = (k15_margrel1 X1 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk14_3 X1 X3 X2)) = (k9_margrel1 (k3_funct_2 X1 k6_margrel1 X3 (esk14_3 X1 X3 X2))) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X3 X4 X5 X2, ((k3_funct_2 X2 k6_margrel1 X1 X5) = (k10_margrel1 (k3_funct_2 X2 k6_margrel1 X3 X5) (k3_funct_2 X2 k6_margrel1 X4 X5)) -> False) -> (v1_xboole_0 X2 -> False) -> X1 = (k16_margrel1 X2 X3 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X5 X2 -> v1_funct_2 X4 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X1 X4 X5 X2 X3 X6, ((k3_funct_2 X2 k6_margrel1 X6 X3) = k8_margrel1 -> False) -> (v1_xboole_0 X2 -> False) -> X6 = (k17_bvfunc_1 X2 X5 X4) -> (k3_funct_2 X2 k6_margrel1 X5 X1) = k8_margrel1 -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X6 X2 k6_margrel1 -> v1_funct_2 X5 X2 k6_margrel1 -> r2_hidden X1 (k15_bvfunc_1 X2 X3 X4) -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X5 X1 X4 X2 X3 X6, ((k3_funct_2 X2 k6_margrel1 X6 X3) = k7_margrel1 -> False) -> ((k3_funct_2 X2 k6_margrel1 X5 X1) = k8_margrel1 -> False) -> (v1_xboole_0 X2 -> False) -> X6 = (k16_bvfunc_1 X2 X5 X4) -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X6 X2 k6_margrel1 -> v1_funct_2 X5 X2 k6_margrel1 -> r2_hidden X1 (k15_bvfunc_1 X2 X3 X4) -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X1 X3 X4 X2, ((k3_funct_2 X2 k6_margrel1 X1 X4) = (k9_margrel1 (k3_funct_2 X2 k6_margrel1 X3 X4)) -> False) -> (v1_xboole_0 X2 -> False) -> X1 = (k15_margrel1 X2 X3) -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> v1_funct_2 X3 X2 k6_margrel1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X4 X2 X3 X1, (X4 = (k16_margrel1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk15_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X2 X3 X1, (X4 = (k9_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk16_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1 X4 X3, ((k3_funct_2 X1 k6_margrel1 X3 X4) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 X4) = k8_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> r1_bvfunc_1 X1 X2 X3 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X3 X2 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk7_3 X1 X3 X2)) = k8_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk9_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k17_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k6_bvfunc_2 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k7_bvfunc_2 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k6_bvfunc_2 X1 X2 X3 X4) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k7_bvfunc_2 X1 X2 X3 X4) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k3_funct_2 X1 k6_margrel1 X2 (esk7_3 X1 X2 X3)) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X3 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k6_bvfunc_2 X1 X2 X3 X4) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k7_bvfunc_2 X1 X2 X3 X4) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X3 X4 X1, ((k16_bvfunc_1 X1 X2 (k5_bvfunc_2 X1 X4 X3)) = (k6_bvfunc_2 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, ((k17_bvfunc_1 X1 X2 (k5_bvfunc_2 X1 X4 X3)) = (k7_bvfunc_2 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk7_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k16_margrel1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k9_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k16_margrel1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k2_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k9_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (X3 = (k15_margrel1 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk14_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k16_margrel1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k2_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k9_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k16_margrel1 X1 X2 X3) = (k16_margrel1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_1 X1 X2 X3) = (k2_bvfunc_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, ((k16_margrel1 X1 X2 X3) = (k14_margrel1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_1 X1 X2 X3) = (k14_margrel1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k9_bvfunc_1 X1 X2 X3) = (k7_bvfunc_1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X1 X2, ((k16_margrel1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X1 X2, ((k2_bvfunc_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X2 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k16_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k17_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k16_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k17_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k16_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k17_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k15_margrel1 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_bvfunc_1 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k15_margrel1 X1 X2) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k1_bvfunc_1 X1 X2) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, ((k15_margrel1 X1 (k15_margrel1 X1 X2)) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, ((k1_bvfunc_1 X1 (k1_bvfunc_1 X1 X2)) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k15_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k1_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, ((k15_margrel1 X1 X2) = (k13_margrel1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, ((k1_bvfunc_1 X1 X2) = (k13_margrel1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_bvfunc_1 (k15_bvfunc_1 X1 X2 X3) X1 X3 -> False) -> m1_subset_1 X2 X1 -> m1_eqrel_1 X3 X1 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (k5_bvfunc_2 X1 X2 X3) X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X1, (v1_margrel1 X1 -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k11_eqrel_1 X1 X2 X3) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X2 X1 -> m1_eqrel_1 X3 X1 -> False)
  -> (forall X3 X2 X1, ((k15_bvfunc_1 X1 X2 X3) = (k11_eqrel_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> m1_eqrel_1 X3 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 (k1_zfmisc_1 X1) -> False) -> m1_eqrel_1 X2 X1 -> m1_bvfunc_1 X3 X1 X2 -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m1_eqrel_1 X3 X2 -> m1_bvfunc_1 X1 X2 X3 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk20_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_bvfunc_1 (esk17_2 X1 X2) X1 X2 -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (m1_bvfunc_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_eqrel_1 X2 X3 -> False)
  -> (forall X2 X1, ((k3_xboolean (k4_xboolean (k3_xboolean X1) (k3_xboolean X2))) = (k5_xboolean X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k10_margrel1 X1 X2) k6_margrel1 -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k7_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_margrel1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k7_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, ((k14_margrel1 X1 X2) = (k14_margrel1 X2 X1) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k10_margrel1 X1 X2) = (k4_xboolean X1 X2) -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, ((k10_margrel1 X1 X2) = (k10_margrel1 X2 X1) -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, ((k14_margrel1 X1 X1) = X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k10_margrel1 X1 X1) = X1 -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboolean (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (X2 = k7_margrel1 -> False) -> (X1 = k7_margrel1 -> False) -> (k4_xboolean X1 X2) = k7_margrel1 -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k8_margrel1 -> False) -> (k4_xboolean X1 X2) = k8_margrel1 -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k8_margrel1 -> False) -> (k4_xboolean X2 X1) = k8_margrel1 -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k4_xboolean X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k5_xboolean X1 X2) = (k5_xboolean X2 X1) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k4_xboolean X1 X2) = (k4_xboolean X2 X1) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X1 X2, ((k4_xboolean X1 X2) = k8_margrel1 -> False) -> X2 = k8_margrel1 -> X1 = k8_margrel1 -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, ((k4_xboolean X1 X2) = k7_margrel1 -> False) -> X1 = k7_margrel1 -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, ((k4_xboolean X2 X1) = k7_margrel1 -> False) -> X1 = k7_margrel1 -> epred1_2 X2 X1 -> False)
  -> (forall X1, (m1_subset_1 (k9_margrel1 X1) k6_margrel1 -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1, ((k13_margrel1 (k13_margrel1 X1)) = X1 -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k13_margrel1 X1) -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_margrel1 (k13_margrel1 X1) -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k13_margrel1 X1) -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, ((k9_margrel1 (k9_margrel1 X1)) = X1 -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k5_xboolean X1 X1) = X1 -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k4_xboolean X1 X1) = X1 -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, (epred1_2 X1 X2 -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X1, ((k9_margrel1 X1) = (k3_xboolean X1) -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1, ((k6_xcmplx_0 np__1 X1) = (k3_xboolean X1) -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, ((k5_xboolean X1 k7_margrel1) = X1 -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, ((k3_xboolean (k3_xboolean X1)) = X1 -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (v1_xboolean (k3_xboolean X1) -> False) -> v1_xboolean X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k7_margrel1 -> False) -> (k3_xboolean X1) = k8_margrel1 -> v1_xboolean X1 -> False)
  -> (forall X1, (X1 = k8_margrel1 -> False) -> (k3_xboolean X1) = k7_margrel1 -> v1_xboolean X1 -> False)
  -> (forall X1, ((k3_xboolean X1) = k7_margrel1 -> False) -> X1 = k8_margrel1 -> v1_xboolean X1 -> False)
  -> (forall X1, ((k3_xboolean X1) = k8_margrel1 -> False) -> X1 = k7_margrel1 -> v1_xboolean X1 -> False)
  -> (forall X1, (v2_card_3 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboolean -> False) -> (X1 = k2_xboolean -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> X1 = k2_xboolean -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> X1 = k1_xboolean -> False)
  -> (r1_bvfunc_1 esk1_0 (k2_bvfunc_1 esk1_0 (k2_bvfunc_1 esk1_0 (k7_bvfunc_2 esk1_0 esk3_0 esk2_0 esk6_0) (k6_bvfunc_2 esk1_0 (k9_bvfunc_1 esk1_0 esk4_0 (k1_bvfunc_1 esk1_0 esk3_0)) esk2_0 esk6_0)) (k6_bvfunc_2 esk1_0 (k9_bvfunc_1 esk1_0 esk3_0 esk5_0) esk2_0 esk6_0)) (k7_bvfunc_2 esk1_0 (k2_bvfunc_1 esk1_0 esk5_0 (k1_bvfunc_1 esk1_0 esk4_0)) esk2_0 esk6_0) -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k6_margrel1 -> False)
  -> (forall X1, (m1_subset_1 (k1_bvfunc_2 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((v1_funct_2 esk5_0 esk1_0 k6_margrel1 -> False) -> False)
  -> ((v1_funct_2 esk4_0 esk1_0 k6_margrel1 -> False) -> False)
  -> ((v1_funct_2 esk3_0 esk1_0 k6_margrel1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_bvfunc_2 esk1_0)) -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (k1_bvfunc_2 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk18_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk19_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> ((m1_eqrel_1 esk6_0 esk1_0 -> False) -> False)
  -> ((m1_subset_1 k7_margrel1 k6_margrel1 -> False) -> False)
  -> ((m1_subset_1 k8_margrel1 k6_margrel1 -> False) -> False)
  -> ((v1_relat_1 esk22_0 -> False) -> False)
  -> ((v1_margrel1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk22_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_xboole_0 esk21_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> ((k1_xboole_0 = k6_numbers -> False) -> False)
  -> ((np__1 = k2_xboolean -> False) -> False)
  -> ((k8_margrel1 = k2_xboolean -> False) -> False)
  -> ((k1_xboolean = k6_numbers -> False) -> False)
  -> ((k1_xboolean = k7_margrel1 -> False) -> False)
  -> False.
Admitted.
