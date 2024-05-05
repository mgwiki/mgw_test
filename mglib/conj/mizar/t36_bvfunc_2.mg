(** $I sig/MizarPreamble.mgs **)

Theorem t36_bvfunc_2:
 forall k17_bvfunc_1:set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k15_bvfunc_1:set -> set -> set -> set,
 forall esk8_4:set -> set -> set -> set -> set,
 forall esk9_4:set -> set -> set -> set -> set,
 forall m1_eqrel_1:set -> set -> prop,
 forall k8_margrel1:set,
 forall k7_margrel1:set,
 forall esk7_5:set -> set -> set -> set -> set -> set,
 forall r1_bvfunc_1:set -> set -> set -> prop,
 forall k5_bvfunc_2:set -> set -> set -> set,
 forall k7_bvfunc_1:set -> set -> set,
 forall m1_bvfunc_1:set -> set -> set -> prop,
 forall v1_margrel1:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall esk11_2:set -> set -> set,
 forall k4_xboole_0:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk17_1:set -> set,
 forall esk20_1:set -> set,
 forall np__1:set,
 forall k6_xcmplx_0:set -> set -> set,
 forall v2_card_3:set -> prop,
 forall k1_xboole_0:set,
 forall esk25_1:set -> set,
 forall esk22_1:set -> set,
 forall v1_eqrel_1:set -> set -> prop,
 forall esk13_1:set -> set,
 forall esk19_0:set,
 forall o_0_0_xboole_0:set,
 forall k4_ordinal1:set,
 forall esk18_0:set,
 forall esk21_0:set,
 forall esk12_1:set -> set,
 forall k5_numbers:set,
 forall k1_numbers:set,
 forall k6_numbers:set,
 forall esk15_1:set -> set,
 forall esk16_2:set -> set -> set,
 forall esk23_0:set,
 forall esk24_1:set -> set,
 forall esk4_0:set,
 forall esk3_0:set,
 forall esk2_0:set,
 forall esk5_0:set,
 forall esk1_0:set,
 forall k2_xboolean:set,
 forall k1_xboolean:set,
 forall v7_ordinal1:set -> prop,
 forall esk26_1:set -> set,
 forall v1_setfam_1:set -> prop,
 forall esk27_1:set -> set,
 forall k3_xcmplx_0:set -> set -> set,
 forall k1_tarski:set -> set,
 forall v1_subset_1:set -> set -> prop,
 forall k4_xboolean:set -> set -> set,
 forall k3_xboolean:set -> set,
 forall v1_xboolean:set -> prop,
 forall v1_relat_1:set -> prop,
 forall esk14_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall m2_subset_1:set -> set -> set -> prop,
 forall k11_eqrel_1:set -> set -> set -> set,
 forall k7_subset_1:set -> set -> set -> set,
 forall k4_bvfunc_2:set -> set -> set,
 forall k2_bvfunc_2:set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k7_bvfunc_2:set -> set -> set -> set -> set,
 forall k1_partit1:set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall m1_subset_1:set -> set -> prop,
 forall v1_funct_2:set -> set -> set -> prop,
 forall k5_xboolean:set -> set -> set,
 forall k9_margrel1:set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall esk10_4:set -> set -> set -> set -> set,
 forall k6_margrel1:set,
 forall k9_bvfunc_1:set -> set -> set -> set,
     (forall X4 X2 X3 X1, (X2 = (k9_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (k5_xboolean (k9_margrel1 (k3_funct_2 X1 k6_margrel1 X3 (esk10_4 X1 X3 X4 X2))) (k3_funct_2 X1 k6_margrel1 X4 (esk10_4 X1 X3 X4 X2))) = (k3_funct_2 X1 k6_margrel1 X2 (esk10_4 X1 X3 X4 X2)) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X4 X3 X2 X5, (X5 = (k17_bvfunc_1 X2 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (r2_hidden (esk9_4 X2 X3 X4 X5) (k15_bvfunc_1 X2 (esk8_4 X2 X3 X4 X5) X4) -> False) -> (k3_funct_2 X2 k6_margrel1 X3 X1) = k8_margrel1 -> v1_funct_1 X5 -> v1_funct_1 X3 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X5 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> r2_hidden X1 (k15_bvfunc_1 X2 (esk8_4 X2 X3 X4 X5) X4) -> False)
  -> (forall X1 X4 X3 X2 X5, (X5 = (k17_bvfunc_1 X2 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (k3_funct_2 X2 k6_margrel1 X3 X1) = k8_margrel1 -> (k3_funct_2 X2 k6_margrel1 X5 (esk8_4 X2 X3 X4 X5)) = k8_margrel1 -> v1_funct_1 X5 -> v1_funct_1 X3 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X5 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> r2_hidden X1 (k15_bvfunc_1 X2 (esk8_4 X2 X3 X4 X5) X4) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k7_margrel1 -> False) -> ((k3_funct_2 X1 k6_margrel1 X2 (esk7_5 X1 X2 X3 X4 X5)) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> X4 = (k17_bvfunc_1 X1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X4 X3 X2 X5, (X5 = (k17_bvfunc_1 X2 X3 X4) -> False) -> ((k3_funct_2 X2 k6_margrel1 X3 (esk9_4 X2 X3 X4 X5)) = k8_margrel1 -> False) -> (v1_xboole_0 X2 -> False) -> (k3_funct_2 X2 k6_margrel1 X3 X1) = k8_margrel1 -> v1_funct_1 X5 -> v1_funct_1 X3 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X5 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> r2_hidden X1 (k15_bvfunc_1 X2 (esk8_4 X2 X3 X4 X5) X4) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k7_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk7_5 X1 X2 X3 X4 X5) (k15_bvfunc_1 X1 X5 X3) -> False) -> X4 = (k17_bvfunc_1 X1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k17_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (r2_hidden (esk9_4 X1 X3 X4 X2) (k15_bvfunc_1 X1 (esk8_4 X1 X3 X4 X2) X4) -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk8_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1 X5 X4, ((k3_funct_2 X1 k6_margrel1 X4 X5) = k7_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk7_5 X1 X2 X3 X4 X5) X1 -> False) -> X4 = (k17_bvfunc_1 X1 X2 X3) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_subset_1 X5 X1 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X4 X3 X2 X5, (X5 = (k17_bvfunc_1 X2 X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 (esk9_4 X2 X3 X4 X5) X2 -> False) -> (k3_funct_2 X2 k6_margrel1 X3 X1) = k8_margrel1 -> v1_funct_1 X5 -> v1_funct_1 X3 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X5 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> r2_hidden X1 (k15_bvfunc_1 X2 (esk8_4 X2 X3 X4 X5) X4) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k17_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk8_4 X1 X3 X4 X2)) = k8_margrel1 -> (k3_funct_2 X1 k6_margrel1 X2 (esk8_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X3 X4 X5 X2, ((k3_funct_2 X2 k6_margrel1 X1 X5) = (k5_xboolean (k9_margrel1 (k3_funct_2 X2 k6_margrel1 X3 X5)) (k3_funct_2 X2 k6_margrel1 X4 X5)) -> False) -> (v1_xboole_0 X2 -> False) -> X1 = (k9_bvfunc_1 X2 X3 X4) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X1 -> m1_subset_1 X5 X2 -> v1_funct_2 X4 X2 k6_margrel1 -> v1_funct_2 X3 X2 k6_margrel1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k17_bvfunc_1 X1 X3 X4) -> False) -> ((k3_funct_2 X1 k6_margrel1 X3 (esk9_4 X1 X3 X4 X2)) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk8_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X4 X2 X1, (X2 = (k17_bvfunc_1 X1 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk9_4 X1 X3 X4 X2) X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk8_4 X1 X3 X4 X2)) = k7_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X4 X5 X2 X3 X6, ((k3_funct_2 X2 k6_margrel1 X6 X3) = k8_margrel1 -> False) -> (v1_xboole_0 X2 -> False) -> X6 = (k17_bvfunc_1 X2 X5 X4) -> (k3_funct_2 X2 k6_margrel1 X5 X1) = k8_margrel1 -> v1_funct_1 X6 -> v1_funct_1 X5 -> m1_subset_1 X3 X2 -> m1_subset_1 X1 X2 -> m1_eqrel_1 X4 X2 -> v1_funct_2 X6 X2 k6_margrel1 -> v1_funct_2 X5 X2 k6_margrel1 -> r2_hidden X1 (k15_bvfunc_1 X2 X3 X4) -> m1_subset_1 X6 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X4 X2 X3 X1, (X4 = (k9_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk10_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1 X4 X3, ((k3_funct_2 X1 k6_margrel1 X3 X4) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 X4) = k8_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> r1_bvfunc_1 X1 X2 X3 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X3 X2 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk6_3 X1 X3 X2)) = k8_margrel1 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X3 X2 X1, (X4 = (k17_bvfunc_1 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk8_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k7_bvfunc_2 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k7_bvfunc_2 X1 X2 X3 X4) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k3_funct_2 X1 k6_margrel1 X2 (esk6_3 X1 X2 X3)) = k8_margrel1 -> False) -> (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X3 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k7_bvfunc_2 X1 X2 X3 X4) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X2 X3 X4 X1, ((k17_bvfunc_1 X1 X2 (k5_bvfunc_2 X1 X4 X3)) = (k7_bvfunc_2 X1 X2 X3 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X4 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X3 -> False) -> (m1_subset_1 (esk6_3 X1 X2 X3) X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k9_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k9_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k9_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X2 X1, ((k9_bvfunc_1 X1 X2 X3) = (k7_bvfunc_1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r1_bvfunc_1 X1 X2 X2 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k17_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k17_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k17_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X2 -> m1_eqrel_1 X3 X1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_2 X1 (k7_subset_1 (k1_partit1 X1) X3 (k4_bvfunc_2 X1 X2))) = (k5_bvfunc_2 X1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_bvfunc_1 (k15_bvfunc_1 X1 X2 X3) X1 X3 -> False) -> m1_subset_1 X2 X1 -> m1_eqrel_1 X3 X1 -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (k5_bvfunc_2 X1 X2 X3) X1 -> False) -> m1_eqrel_1 X2 X1 -> m1_subset_1 X3 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
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
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X1 X2, (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m1_eqrel_1 X3 X2 -> m1_bvfunc_1 X1 X2 X3 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk14_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_bvfunc_1 (esk11_2 X1 X2) X1 X2 -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (m1_bvfunc_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_eqrel_1 X2 X3 -> False)
  -> (forall X3 X2 X1, ((k7_subset_1 X2 X1 X3) = (k4_xboole_0 X1 X3) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (k2_bvfunc_2 X1 X2) X1 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 (k1_partit1 X1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k4_bvfunc_2 X1 X2) (k1_zfmisc_1 (k1_partit1 X1)) -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1, ((k3_xboolean (k4_xboolean (k3_xboolean X1) (k3_xboolean X2))) = (k5_xboolean X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X1 X2 X3, (v5_relat_1 (k4_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v5_relat_1 X1 X2 -> False)
  -> (forall X1 X2 X3, (v4_relat_1 (k4_xboole_0 X1 X3) X2 -> False) -> v1_relat_1 X3 -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X1 X2, (v1_relat_1 (k7_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k7_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, v1_xboole_0 X1 -> v1_subset_1 X2 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 X2 X1 -> False) -> v1_xboole_0 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xboole_0 (k2_zfmisc_1 X1 X2) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 (k1_zfmisc_1 X2)) -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_xboolean (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_margrel1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, ((k4_bvfunc_2 X1 X2) = (k1_tarski X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboolean (k5_xboolean X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, (v1_xboolean (k4_xboolean X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k4_xboolean X1 X2) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k5_xboolean X1 X2) = (k5_xboolean X2 X1) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k4_xboolean X1 X2) = (k4_xboolean X2 X1) -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (k9_margrel1 X1) k6_margrel1 -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 X2 -> m1_eqrel_1 X2 X1 -> False)
  -> (forall X1, ((k9_margrel1 (k9_margrel1 X1)) = X1 -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk27_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k5_xboolean X1 X1) = X1 -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X2 X1, ((k4_xboolean X1 X1) = X1 -> False) -> v1_xboolean X2 -> v1_xboolean X1 -> False)
  -> (forall X1, ((k9_margrel1 X1) = (k3_xboolean X1) -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, (v1_setfam_1 X1 -> False) -> m1_eqrel_1 X1 X2 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_subset_1 (esk27_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk26_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_eqrel_1 (esk20_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X1, ((k6_xcmplx_0 np__1 X1) = (k3_xboolean X1) -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk26_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk20_1 X1) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xboole_0 (esk17_1 X1) -> False)
  -> (forall X1, ((k5_xboolean X1 k7_margrel1) = X1 -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, ((k5_xboolean X1 k8_margrel1) = k8_margrel1 -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, ((k3_xboolean (k3_xboolean X1)) = X1 -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (v1_xboolean (k3_xboolean X1) -> False) -> v1_xboolean X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk26_1 X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_setfam_1 (esk20_1 X1) -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (v2_card_3 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboolean -> False) -> (X1 = k2_xboolean -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> X1 = k2_xboolean -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> X1 = k1_xboolean -> False)
  -> (r1_bvfunc_1 esk1_0 (k9_bvfunc_1 esk1_0 esk3_0 (k7_bvfunc_2 esk1_0 esk4_0 esk2_0 esk5_0)) (k7_bvfunc_2 esk1_0 (k9_bvfunc_1 esk1_0 esk3_0 esk4_0) esk2_0 esk5_0) -> False)
  -> (forall X1, v1_subset_1 (esk25_1 X1) X1 -> False)
  -> (forall X1, v1_xboole_0 (esk24_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_tarski X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_zfmisc_1 X1) -> False)
  -> (forall X1, v1_xboole_0 (k1_partit1 X1) -> False)
  -> (v1_xboole_0 esk23_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k6_margrel1 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk24_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk15_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_partit1 X1) (k1_zfmisc_1 (k1_zfmisc_1 (k1_zfmisc_1 X1))) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> ((v1_funct_2 esk4_0 esk1_0 k6_margrel1 -> False) -> False)
  -> ((v1_funct_2 esk3_0 esk1_0 k6_margrel1 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (k1_zfmisc_1 X1) (k1_zfmisc_1 (k1_zfmisc_1 X1)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk25_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk22_1 X1) (k1_zfmisc_1 X1) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k1_partit1 esk1_0)) -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (esk24_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (esk15_1 X1) X1 -> False) -> False)
  -> (forall X1, (v1_eqrel_1 (k1_partit1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_eqrel_1 (esk12_1 X1) X1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 X1 k1_xboole_0) = X1 -> False) -> False)
  -> (forall X1, ((k4_xboole_0 k1_xboole_0 X1) = k1_xboole_0 -> False) -> False)
  -> ((m1_eqrel_1 esk5_0 esk1_0 -> False) -> False)
  -> ((m1_subset_1 k7_margrel1 k6_margrel1 -> False) -> False)
  -> ((m1_subset_1 k8_margrel1 k6_margrel1 -> False) -> False)
  -> (forall X1, (v1_xboole_0 (esk22_1 X1) -> False) -> False)
  -> ((v1_margrel1 esk21_0 -> False) -> False)
  -> ((v1_xboolean esk19_0 -> False) -> False)
  -> ((v1_xboolean k2_xboolean -> False) -> False)
  -> ((v1_xboolean k1_xboolean -> False) -> False)
  -> ((v1_relat_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk21_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_xboole_0 esk18_0 -> False) -> False)
  -> ((v1_xboole_0 o_0_0_xboole_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> ((np__1 = k2_xboolean -> False) -> False)
  -> ((k8_margrel1 = k2_xboolean -> False) -> False)
  -> ((o_0_0_xboole_0 = k1_xboole_0 -> False) -> False)
  -> ((k1_xboole_0 = k6_numbers -> False) -> False)
  -> ((k1_xboolean = k6_numbers -> False) -> False)
  -> ((k1_xboolean = k7_margrel1 -> False) -> False)
  -> False.
Admitted.
