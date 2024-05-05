(** $I sig/MizarPreamble.mgs **)

Theorem l4_bvfunc10:
 forall k5_bvfunc_1:set -> set -> set -> set,
 forall esk8_4:set -> set -> set -> set -> set,
 forall k5_xboolean:set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall k14_margrel1:set -> set -> set,
 forall k3_bvfunc_1:set -> set -> set,
 forall k1_bvfunc_1:set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v1_xcmplx_0:set -> prop,
 forall k2_xcmplx_0:set -> set -> set,
 forall k3_xcmplx_0:set -> set -> set,
 forall v1_xboolean:set -> prop,
 forall k3_xboolean:set -> set,
 forall k4_xboolean:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k4_xcmplx_0:set -> set,
 forall k6_xcmplx_0:set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall np__1:set,
 forall k6_numbers:set,
 forall v2_card_3:set -> prop,
 forall k1_xboole_0:set,
 forall esk14_0:set,
 forall np__3:set,
 forall esk9_1:set -> set,
 forall esk13_0:set,
 forall esk12_0:set,
 forall k4_ordinal1:set,
 forall esk11_0:set,
 forall np__0:set,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall np__2:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall k2_xboolean:set,
 forall v7_ordinal1:set -> prop,
 forall k1_xboolean:set,
 forall epred1_2:set -> set -> prop,
 forall k7_margrel1:set,
 forall k7_xcmplx_0:set -> set -> set,
 forall esk10_2:set -> set -> set,
 forall v1_margrel1:set -> prop,
 forall k13_margrel1:set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k2_bvfunc_1:set -> set -> set -> set,
 forall r1_bvfunc_1:set -> set -> set -> prop,
 forall k8_margrel1:set,
 forall k9_margrel1:set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall k15_margrel1:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k10_margrel1:set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall esk7_4:set -> set -> set -> set -> set,
 forall k6_margrel1:set,
 forall k16_margrel1:set -> set -> set -> set,
     (forall X4 X2 X3 X1, (X2 = (k16_margrel1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (k10_margrel1 (k3_funct_2 X1 k6_margrel1 X3 (esk7_4 X1 X3 X4 X2)) (k3_funct_2 X1 k6_margrel1 X4 (esk7_4 X1 X3 X4 X2))) = (k3_funct_2 X1 k6_margrel1 X2 (esk7_4 X1 X3 X4 X2)) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X2 X3 X1, (X2 = (k5_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (k5_xboolean (k3_funct_2 X1 k6_margrel1 X3 (esk8_4 X1 X3 X4 X2)) (k3_funct_2 X1 k6_margrel1 X4 (esk8_4 X1 X3 X4 X2))) = (k3_funct_2 X1 k6_margrel1 X2 (esk8_4 X1 X3 X4 X2)) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (X2 = (k15_margrel1 X1 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk6_3 X1 X3 X2)) = (k9_margrel1 (k3_funct_2 X1 k6_margrel1 X3 (esk6_3 X1 X3 X2))) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X3 X4 X5 X2, ((k3_funct_2 X2 k6_margrel1 X1 X5) = (k5_xboolean (k3_funct_2 X2 k6_margrel1 X3 X5) (k3_funct_2 X2 k6_margrel1 X4 X5)) -> False) -> (v1_xboole_0 X2 -> False) -> X1 = (k5_bvfunc_1 X2 X3 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X5 X2 -> v1_funct_2 X4 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X1 X3 X4 X5 X2, ((k3_funct_2 X2 k6_margrel1 X1 X5) = (k10_margrel1 (k3_funct_2 X2 k6_margrel1 X3 X5) (k3_funct_2 X2 k6_margrel1 X4 X5)) -> False) -> (v1_xboole_0 X2 -> False) -> X1 = (k16_margrel1 X2 X3 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X5 X2 -> v1_funct_2 X4 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X1 X3 X4 X2, ((k3_funct_2 X2 k6_margrel1 X1 X4) = (k9_margrel1 (k3_funct_2 X2 k6_margrel1 X3 X4)) -> False) -> (v1_xboole_0 X2 -> False) -> X1 = (k15_margrel1 X2 X3) -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X4 X2 -> v1_funct_2 X3 X2 k6_margrel1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X4 X2 X3 X1, (X4 = (k16_margrel1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk7_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X2 X3 X1, (X4 = (k5_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk8_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1 X4 X3, ((k3_funct_2 X1 k6_margrel1 X3 X4) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 X4) = k8_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> r1_bvfunc_1 X1 X2 X3 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X3 X2 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk5_3 X1 X3 X2)) = k8_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k3_funct_2 X1 k6_margrel1 X2 (esk5_3 X1 X2 X3)) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X3 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk5_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k16_margrel1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k5_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k16_margrel1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k2_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k5_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (X3 = (k15_margrel1 X1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k16_margrel1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k2_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k5_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k16_margrel1 X1 X2 X3) = (k16_margrel1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_1 X1 X2 X3) = (k2_bvfunc_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k5_bvfunc_1 X1 X2 X3) = (k5_bvfunc_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, ((k16_margrel1 X1 X2 X3) = (k14_margrel1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_1 X1 X2 X3) = (k14_margrel1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k5_bvfunc_1 X1 X2 X3) = (k3_bvfunc_1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X1 X2, ((k16_margrel1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X1 X2, ((k2_bvfunc_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X1 X2, ((k5_bvfunc_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X2 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
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
  -> (forall X2 X1, (v1_margrel1 X1 -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k3_xcmplx_0 X1 X3) (k3_xcmplx_0 X2 X3)) = (k3_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk10_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k7_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k7_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k3_xboolean (k4_xboolean (k3_xboolean X1) (k3_xboolean X2))) = (k5_xboolean X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k10_margrel1 X1 X2) k6_margrel1 -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_margrel1 (k3_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_margrel1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, ((k3_bvfunc_1 X1 X2) = (k3_bvfunc_1 X2 X1) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, ((k14_margrel1 X1 X2) = (k14_margrel1 X2 X1) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k10_margrel1 X1 X2) = (k4_xboolean X1 X2) -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, ((k10_margrel1 X1 X2) = (k10_margrel1 X2 X1) -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, ((k3_bvfunc_1 X1 X1) = X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k14_margrel1 X1 X1) = X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k10_margrel1 X1 X1) = X1 -> False) -> m1_subset_1 X2 k6_margrel1 -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, ((k6_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xboolean (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 (k4_xcmplx_0 X2)) = (k6_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (X2 = k7_margrel1 -> False) -> (X1 = k7_margrel1 -> False) -> (k4_xboolean X1 X2) = k7_margrel1 -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k8_margrel1 -> False) -> (k4_xboolean X1 X2) = k8_margrel1 -> epred1_2 X1 X2 -> False)
  -> (forall X2 X1, (X1 = k8_margrel1 -> False) -> (k4_xboolean X2 X1) = k8_margrel1 -> epred1_2 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboolean (k5_xboolean X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, (v1_xboolean (k4_xboolean X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k5_xboolean X1 X2) = (k5_xboolean X2 X1) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k4_xboolean X1 X2) = (k4_xboolean X2 X1) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k4_xboolean X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
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
  -> (forall X1, ((k3_xcmplx_0 X1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k4_xboolean X1 (k3_xboolean X1)) = k1_xboolean -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1, ((k6_xcmplx_0 np__1 X1) = (k3_xboolean X1) -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 X1 np__1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k6_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k7_xcmplx_0 k6_numbers X1) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xboolean (k3_xboolean X1)) = X1 -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xboolean (k3_xboolean X1) -> False) -> v1_xboolean X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (v2_card_3 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboolean -> False) -> (X1 = k2_xboolean -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> X1 = k2_xboolean -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> X1 = k1_xboolean -> False)
  -> (r1_bvfunc_1 esk1_0 (k2_bvfunc_1 esk1_0 (k2_bvfunc_1 esk1_0 (k5_bvfunc_1 esk1_0 esk2_0 (k1_bvfunc_1 esk1_0 esk3_0)) (k5_bvfunc_1 esk1_0 esk3_0 (k1_bvfunc_1 esk1_0 esk4_0))) (k5_bvfunc_1 esk1_0 esk4_0 (k1_bvfunc_1 esk1_0 esk2_0))) (k2_bvfunc_1 esk1_0 (k2_bvfunc_1 esk1_0 (k5_bvfunc_1 esk1_0 esk3_0 (k1_bvfunc_1 esk1_0 esk2_0)) (k5_bvfunc_1 esk1_0 esk4_0 (k1_bvfunc_1 esk1_0 esk3_0))) (k5_bvfunc_1 esk1_0 esk2_0 (k1_bvfunc_1 esk1_0 esk4_0))) -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (v1_xboole_0 np__3 -> False)
  -> (v1_xboole_0 np__2 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k6_margrel1 -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((v1_funct_2 esk4_0 esk1_0 k6_margrel1 -> False) -> False)
  -> ((v1_funct_2 esk3_0 esk1_0 k6_margrel1 -> False) -> False)
  -> ((v1_funct_2 esk2_0 esk1_0 k6_margrel1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__3) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__3) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__2) (k4_xcmplx_0 np__2)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__2)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__0) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k3_xcmplx_0 (k4_xcmplx_0 np__3) np__1) = (k4_xcmplx_0 np__3) -> False) -> False)
  -> (((k3_xcmplx_0 (k4_xcmplx_0 np__2) np__1) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__3) np__2) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__3) np__1) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k7_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k3_xcmplx_0 np__1 (k4_xcmplx_0 np__3)) = (k4_xcmplx_0 np__3) -> False) -> False)
  -> (((k3_xcmplx_0 np__1 (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k2_xcmplx_0 np__2 (k4_xcmplx_0 np__3)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__3)) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__2)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__3) np__3) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) np__3) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__2) np__2) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__3) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__2) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__3 (k4_xcmplx_0 np__3)) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__3 (k4_xcmplx_0 np__2)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__3 (k4_xcmplx_0 np__1)) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 (k4_xcmplx_0 np__2)) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__2) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__1) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__3) = (k4_xcmplx_0 np__2) -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__2) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((m1_subset_1 k7_margrel1 k6_margrel1 -> False) -> False)
  -> ((m1_subset_1 k8_margrel1 k6_margrel1 -> False) -> False)
  -> (((k7_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__3 np__2) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__3 np__1) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__2) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__0) = np__2 -> False) -> False)
  -> (((k6_xcmplx_0 np__2 np__1) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k6_xcmplx_0 np__1 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__3 np__1) = np__3 -> False) -> False)
  -> (((k3_xcmplx_0 np__2 np__1) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__3) = np__3 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__2) = np__2 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 np__0) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__2 np__1) = np__3 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__2) = np__2 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__2) = np__3 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__1) = np__2 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__3)) = np__3 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__2)) = np__2 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_margrel1 esk13_0 -> False) -> False)
  -> ((v1_xboolean esk12_0 -> False) -> False)
  -> ((v1_xboolean k2_xboolean -> False) -> False)
  -> ((v1_xboolean k1_xboolean -> False) -> False)
  -> ((v1_funct_1 esk13_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk11_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((k7_margrel1 = k1_xboolean -> False) -> False)
  -> ((np__1 = k2_xboolean -> False) -> False)
  -> ((k8_margrel1 = k2_xboolean -> False) -> False)
  -> ((k6_numbers = k1_xboolean -> False) -> False)
  -> False.
Admitted.
