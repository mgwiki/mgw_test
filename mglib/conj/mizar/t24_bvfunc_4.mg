(** $I sig/MizarPreamble.mgs **)

Theorem t24_bvfunc_4:
 forall k8_margrel1:set,
 forall k16_bvfunc_1:set -> set -> set -> set,
 forall m1_eqrel_1:set -> set -> prop,
 forall esk7_5:set -> set -> set -> set -> set -> set,
 forall k7_margrel1:set,
 forall r1_bvfunc_1:set -> set -> set -> prop,
 forall k5_bvfunc_2:set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall m1_bvfunc_1:set -> set -> set -> prop,
 forall v1_margrel1:set -> prop,
 forall k4_xboole_0:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall v1_xboolean:set -> prop,
 forall k1_tarski:set -> set,
 forall k6_numbers:set,
 forall v2_card_3:set -> prop,
 forall k1_xboole_0:set,
 forall k1_numbers:set,
 forall k5_numbers:set,
 forall v1_eqrel_1:set -> set -> prop,
 forall esk13_1:set -> set,
 forall k4_ordinal1:set,
 forall esk15_0:set,
 forall esk16_0:set,
 forall esk17_0:set,
 forall esk12_1:set -> set,
 forall np__0:set,
 forall esk18_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall k2_xboolean:set,
 forall k1_xboolean:set,
 forall v7_ordinal1:set -> prop,
 forall np__1:set,
 forall r1_tarski:set -> set -> prop,
 forall k6_xcmplx_0:set -> set -> set,
 forall k4_xcmplx_0:set -> set,
 forall k4_xboolean:set -> set -> set,
 forall k3_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall esk11_2:set -> set -> set,
 forall esk14_2:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k11_eqrel_1:set -> set -> set -> set,
 forall k7_subset_1:set -> set -> set -> set,
 forall k4_bvfunc_2:set -> set -> set,
 forall k2_bvfunc_2:set -> set -> set,
 forall k14_margrel1:set -> set -> set,
 forall k2_bvfunc_1:set -> set -> set -> set,
 forall k6_bvfunc_2:set -> set -> set -> set -> set,
 forall k1_bvfunc_2:set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k15_bvfunc_1:set -> set -> set -> set,
 forall esk8_4:set -> set -> set -> set -> set,
 forall esk9_4:set -> set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k10_margrel1:set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall esk10_4:set -> set -> set -> set -> set,
 forall k6_margrel1:set,
 forall k16_margrel1:set -> set -> set -> set,
     (forall X4 X2 X3 X1, (X2 = (k16_margrel1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (k10_margrel1 (k3_funct_2 X1 k6_margrel1 X3 (esk10_4 X1 X3 X4 X2)) (k3_funct_2 X1 k6_margrel1 X4 (esk10_4 X1 X3 X4 X2))) = (k3_funct_2 X1 k6_margrel1 X2 (esk10_4 X1 X3 X4 X2)) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> X4 = (k16_bvfunc_1 X1 X2 X3) -> (k3_funct_2 X1 k6_margrel1 X2 (esk7_5 X1 X2 X3 X4 X5)) = k8_margrel1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X5 X3 X2 X1 X4, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> ((k3_funct_2 X1 k6_margrel1 X2 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) (k15_bvfunc_1 X1 (esk8_4 X1 X2 X3 X4) X3) -> False) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> r2_hidden X5 (k15_bvfunc_1 X1 (esk8_4 X1 X2 X3 X4) X3) -> False)
  -> (forall X5 X4 X3 X1 X2, (X2 = (k16_bvfunc_1 X1 X3 X4) -> False) -> ((k3_funct_2 X1 k6_margrel1 X3 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk8_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> r2_hidden X5 (k15_bvfunc_1 X1 (esk8_4 X1 X3 X4 X2) X4) -> False)
  -> (forall X5 X3 X2 X1 X4, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> ((k3_funct_2 X1 k6_margrel1 X2 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk9_4 X1 X2 X3 X4)) = k8_margrel1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> r2_hidden X5 (k15_bvfunc_1 X1 (esk8_4 X1 X2 X3 X4) X3) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk7_5 X1 X2 X3 X4 X5) (k15_bvfunc_1 X1 X5 X3) -> False) -> X4 = (k16_bvfunc_1 X1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk9_4 X1 X2 X3 X4) (k15_bvfunc_1 X1 (esk8_4 X1 X2 X3 X4) X3) -> False) -> (k3_funct_2 X1 k6_margrel1 X4 (esk8_4 X1 X2 X3 X4)) = k8_margrel1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk7_5 X1 X2 X3 X4 X5) X1 -> False) -> X4 = (k16_bvfunc_1 X1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X5 X3 X2 X1 X4, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> ((k3_funct_2 X1 k6_margrel1 X2 X5) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk9_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> r2_hidden X5 (k15_bvfunc_1 X1 (esk8_4 X1 X2 X3 X4) X3) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k16_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk8_4 X1 X3 X4 X2)) = k8_margrel1 -> (k3_funct_2 X1 k6_margrel1 X2 (esk8_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X4 (esk8_4 X1 X2 X3 X4)) = k8_margrel1 -> (k3_funct_2 X1 k6_margrel1 X2 (esk9_4 X1 X2 X3 X4)) = k8_margrel1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk9_4 X1 X2 X3 X4) X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X4 (esk8_4 X1 X2 X3 X4)) = k8_margrel1 -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X3 X4 X5 X2, ((k3_funct_2 X2 k6_margrel1 X1 X5) = (k10_margrel1 (k3_funct_2 X2 k6_margrel1 X3 X5) (k3_funct_2 X2 k6_margrel1 X4 X5)) -> False) -> (v1_xboole_0 X2 -> False) -> X1 = (k16_margrel1 X2 X3 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X5 X2 -> v1_funct_2 X4 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X5 X1 X4 X2 X3 X6, ((k3_funct_2 X2 k6_margrel1 X6 X3) = k7_margrel1 -> False) -> ((k3_funct_2 X2 k6_margrel1 X5 X1) = k8_margrel1 -> False) -> (v1_xboole_0 X2 -> False) -> X6 = (k16_bvfunc_1 X2 X5 X4) -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X6 X2 k6_margrel1 -> v1_funct_2 X5 X2 k6_margrel1 -> r2_hidden X1 (k15_bvfunc_1 X2 X3 X4) -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X4 X2 X3 X1, (X4 = (k16_margrel1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1 X4 X3, ((k3_funct_2 X1 k6_margrel1 X3 X4) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 X4) = k8_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> r1_bvfunc_1 X1 X2 X3 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X3 X2 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk6_3 X1 X3 X2)) = k8_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k16_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk8_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k6_bvfunc_2 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k6_bvfunc_2 X1 X2 X3 X4) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k3_funct_2 X1 k6_margrel1 X2 (esk6_3 X1 X2 X3)) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X3 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k6_bvfunc_2 X1 X2 X3 X4) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X3 X4 X1, ((k16_bvfunc_1 X1 X2 (k5_bvfunc_2 X1 X4 X3)) = (k6_bvfunc_2 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k16_margrel1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k16_margrel1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k2_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k16_margrel1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k2_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k16_margrel1 X1 X2 X3) = (k16_margrel1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_1 X1 X2 X3) = (k2_bvfunc_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, ((k16_margrel1 X1 X2 X3) = (k14_margrel1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_1 X1 X2 X3) = (k14_margrel1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X1 X2, ((k16_margrel1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X1 X2, ((k2_bvfunc_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X2 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k16_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k16_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k16_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_2 X1 (k7_subset_1 (k1_bvfunc_2 X1) X3 (k4_bvfunc_2 X1 X2))) = (k5_bvfunc_2 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_bvfunc_1 (k15_bvfunc_1 X1 X2 X3) X1 X3 -> False) -> m1_subset_1 X2 X1 -> m1_eqrel_1 X3 X1 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (k5_bvfunc_2 X1 X2 X3) X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X1, (v1_margrel1 X1 -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X2 X1 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 X2 -> False) -> X1 = (k11_eqrel_1 X3 X4 X2) -> m1_subset_1 X4 X3 -> m1_eqrel_1 X2 X3 -> m1_subset_1 X1 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1 X4 X3, (v1_xboole_0 X3 -> False) -> (r2_hidden X1 X2 -> False) -> X2 = (k11_eqrel_1 X3 X1 X4) -> m1_subset_1 X1 X3 -> m1_eqrel_1 X4 X3 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2 X3 X4, (X2 = (k11_eqrel_1 X4 X1 X3) -> False) -> (v1_xboole_0 X4 -> False) -> m1_subset_1 X1 X4 -> m1_eqrel_1 X3 X4 -> r2_hidden X2 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X4) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k11_eqrel_1 X1 X2 X3) (k1_zfmisc_1 X1) -> False) -> m1_subset_1 X2 X1 -> m1_eqrel_1 X3 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (k7_subset_1 X2 X1 X3) (k1_zfmisc_1 X2) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, ((k15_bvfunc_1 X1 X2 X3) = (k11_eqrel_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> m1_eqrel_1 X3 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 (k1_zfmisc_1 X1) -> False) -> m1_eqrel_1 X2 X1 -> m1_bvfunc_1 X3 X1 X2 -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m1_eqrel_1 X3 X2 -> m1_bvfunc_1 X1 X2 X3 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk14_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_bvfunc_1 (esk11_2 X1 X2) X1 X2 -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (m1_bvfunc_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_eqrel_1 X2 X3 -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (k2_bvfunc_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k4_bvfunc_2 X1 X2) (k1_zfmisc_1 (k1_bvfunc_2 X1)) -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k10_margrel1 X1 X2) k6_margrel1 -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_margrel1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, ((k14_margrel1 X1 X2) = (k14_margrel1 X2 X1) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k10_margrel1 X1 X2) = (k4_xboolean X1 X2) -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, ((k10_margrel1 X1 X2) = (k10_margrel1 X2 X1) -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k14_margrel1 X1 X1) = X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k10_margrel1 X1 X1) = X1 -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1, ((k6_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xboolean (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k4_bvfunc_2 X1 X2) = (k1_tarski X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboolean (k4_xboolean X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k4_xboolean X1 X2) = (k4_xboolean X2 X1) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k4_xboolean X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k4_xboolean X1 X1) = X1 -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k6_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (v2_card_3 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboolean -> False) -> (X1 = k2_xboolean -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> X1 = k2_xboolean -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> X1 = k1_xboolean -> False)
  -> (r1_bvfunc_1 esk1_0 (k6_bvfunc_2 esk1_0 (k2_bvfunc_1 esk1_0 esk2_0 esk3_0) esk4_0 esk5_0) (k2_bvfunc_1 esk1_0 esk2_0 (k6_bvfunc_2 esk1_0 esk3_0 esk4_0 esk5_0)) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (v1_xboole_0 esk18_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k6_margrel1 -> False)
  -> (forall X1, (m1_subset_1 (k1_bvfunc_2 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((v1_funct_2 esk3_0 esk1_0 k6_margrel1 -> False) -> False)
  -> ((v1_funct_2 esk2_0 esk1_0 k6_margrel1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k1_bvfunc_2 esk1_0)) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (k1_bvfunc_2 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk12_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((m1_eqrel_1 esk5_0 esk1_0 -> False) -> False)
  -> ((m1_subset_1 k7_margrel1 k6_margrel1 -> False) -> False)
  -> ((m1_subset_1 k8_margrel1 k6_margrel1 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_margrel1 esk17_0 -> False) -> False)
  -> ((v1_xboolean esk16_0 -> False) -> False)
  -> ((v1_xboolean k2_xboolean -> False) -> False)
  -> ((v1_xboolean k1_xboolean -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk15_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> ((k1_xboole_0 = k6_numbers -> False) -> False)
  -> ((np__1 = k2_xboolean -> False) -> False)
  -> ((k8_margrel1 = k2_xboolean -> False) -> False)
  -> ((k1_xboolean = k6_numbers -> False) -> False)
  -> ((k1_xboolean = k7_margrel1 -> False) -> False)
  -> False.
Admitted.
