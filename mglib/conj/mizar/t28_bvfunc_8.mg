(** $I sig/MizarPreamble.mgs **)

Theorem t28_bvfunc_8:
 forall k9_bvfunc_1:set -> set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall k1_funct_1:set -> set -> set,
 forall k3_bvfunc_1:set -> set -> set,
 forall k7_bvfunc_1:set -> set -> set,
 forall k13_margrel1:set -> set,
 forall v1_xboolean:set -> prop,
 forall v7_ordinal1:set -> prop,
 forall k1_xboole_0:set,
 forall esk11_0:set,
 forall np__1:set,
 forall esk7_1:set -> set,
 forall k2_xboolean:set,
 forall esk8_0:set,
 forall esk9_0:set,
 forall esk10_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk5_0:set,
 forall esk4_0:set,
 forall esk1_0:set,
 forall v2_card_3:set -> prop,
 forall r1_tarski:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall v1_relat_1:set -> prop,
 forall v1_margrel1:set -> prop,
 forall k14_margrel1:set -> set -> set,
 forall esk6_2:set -> set -> set,
 forall k8_margrel1:set,
 forall k12_bvfunc_1:set -> set,
 forall k1_bvfunc_1:set -> set -> set,
 forall r2_funct_2:set -> set -> set -> set -> prop,
 forall k6_margrel1:set,
 forall k5_bvfunc_1:set -> set -> set -> set,
 forall k2_bvfunc_1:set -> set -> set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v1_funct_1:set -> prop,
 forall v1_xboole_0:set -> prop,
     (forall X4 X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k6_margrel1 (k5_bvfunc_1 X1 (k2_bvfunc_1 X1 X2 X3) X4) (k2_bvfunc_1 X1 (k5_bvfunc_1 X1 X2 X4) (k5_bvfunc_1 X1 X3 X4)) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X4 X2 X3 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k6_margrel1 (k5_bvfunc_1 X1 (k5_bvfunc_1 X1 X2 X3) X4) (k5_bvfunc_1 X1 X2 (k5_bvfunc_1 X1 X3 X4)) -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X4 X1 k6_margrel1 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k6_margrel1 (k1_bvfunc_1 X1 (k5_bvfunc_1 X1 X2 X3)) (k2_bvfunc_1 X1 (k1_bvfunc_1 X1 X2) (k1_bvfunc_1 X1 X3)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k6_margrel1 (k1_bvfunc_1 X1 (k2_bvfunc_1 X1 X2 X3)) (k5_bvfunc_1 X1 (k1_bvfunc_1 X1 X2) (k1_bvfunc_1 X1 X3)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k6_margrel1 (k9_bvfunc_1 X1 X2 X3) (k5_bvfunc_1 X1 (k1_bvfunc_1 X1 X2) X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X2 X1, (X2 = (k12_bvfunc_1 X1) -> False) -> (v1_xboole_0 X1 -> False) -> (k3_funct_2 X1 k6_margrel1 X2 (esk6_2 X1 X2)) = k8_margrel1 -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k6_margrel1 (k5_bvfunc_1 X1 X2 (k1_bvfunc_1 X1 X2)) (k12_bvfunc_1 X1) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k6_margrel1 (k5_bvfunc_1 X1 X2 (k12_bvfunc_1 X1)) (k12_bvfunc_1 X1) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k5_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k2_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k9_bvfunc_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k6_margrel1 (k2_bvfunc_1 X1 X2 (k12_bvfunc_1 X1)) X2 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k5_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k2_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k9_bvfunc_1 X1 X2 X3) X1 k6_margrel1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k5_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k2_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k9_bvfunc_1 X1 X2 X3) -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k5_bvfunc_1 X1 X2 X3) = (k5_bvfunc_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_1 X1 X2 X3) = (k2_bvfunc_1 X1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, ((k3_funct_2 X2 k6_margrel1 X1 X3) = k8_margrel1 -> False) -> (v1_xboole_0 X2 -> False) -> X1 = (k12_bvfunc_1 X2) -> v1_funct_1 X1 -> m1_subset_1 X3 X2 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k5_bvfunc_1 X1 X2 X3) = (k3_bvfunc_1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k2_bvfunc_1 X1 X2 X3) = (k14_margrel1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X2 X1, ((k9_bvfunc_1 X1 X2 X3) = (k7_bvfunc_1 X2 X3) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X1 X2, ((k5_bvfunc_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X3 X1 X2, ((k2_bvfunc_1 X1 X2 X2) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X3 -> v1_funct_1 X2 -> v1_funct_2 X3 X1 k6_margrel1 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_bvfunc_1 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k1_bvfunc_1 X1 X2) X1 k6_margrel1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (X2 = (k12_bvfunc_1 X1) -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk6_2 X1 X2) X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, ((k1_bvfunc_1 X1 (k1_bvfunc_1 X1 X2)) = X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k1_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, ((k1_bvfunc_1 X1 X2) = (k13_margrel1 X2) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> v1_funct_2 X2 X1 k6_margrel1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False)
  -> (forall X2 X1, (v1_margrel1 X1 -> False) -> v1_funct_1 X1 -> v1_funct_2 X1 X2 k6_margrel1 -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 k6_margrel1)) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k12_bvfunc_1 X1) (k1_zfmisc_1 (k2_zfmisc_1 X1 k6_margrel1)) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k7_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_margrel1 (k3_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_margrel1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k7_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_bvfunc_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k14_margrel1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, ((k3_bvfunc_1 X1 X2) = (k3_bvfunc_1 X2 X1) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, ((k14_margrel1 X1 X2) = (k14_margrel1 X2 X1) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k12_bvfunc_1 X1) X1 k6_margrel1 -> False) -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k3_bvfunc_1 X1 X1) = X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, ((k14_margrel1 X1 X1) = X1 -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_margrel1 X2 -> v1_margrel1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (v1_xboolean (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k13_margrel1 (k13_margrel1 X1)) = X1 -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_relat_1 (k13_margrel1 X1) -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_margrel1 (k13_margrel1 X1) -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v1_funct_1 (k13_margrel1 X1) -> False) -> v1_funct_1 X1 -> v1_margrel1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xboolean X1 -> False) -> m1_subset_1 X1 k6_margrel1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k12_bvfunc_1 X1) -> False) -> False)
  -> (forall X1, (v7_ordinal1 X1 -> False) -> v1_xboolean X1 -> False)
  -> (forall X1, (v2_card_3 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_funct_2 esk1_0 k6_margrel1 (k9_bvfunc_1 esk1_0 (k2_bvfunc_1 esk1_0 (k2_bvfunc_1 esk1_0 (k9_bvfunc_1 esk1_0 esk2_0 esk4_0) (k9_bvfunc_1 esk1_0 esk3_0 esk5_0)) (k5_bvfunc_1 esk1_0 (k1_bvfunc_1 esk1_0 esk4_0) (k1_bvfunc_1 esk1_0 esk5_0))) (k5_bvfunc_1 esk1_0 (k1_bvfunc_1 esk1_0 esk2_0) (k1_bvfunc_1 esk1_0 esk3_0))) (k12_bvfunc_1 esk1_0) -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k6_margrel1 -> False)
  -> ((m1_subset_1 esk5_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (k1_zfmisc_1 (k2_zfmisc_1 esk1_0 k6_margrel1)) -> False) -> False)
  -> ((v1_funct_2 esk5_0 esk1_0 k6_margrel1 -> False) -> False)
  -> ((v1_funct_2 esk4_0 esk1_0 k6_margrel1 -> False) -> False)
  -> ((v1_funct_2 esk3_0 esk1_0 k6_margrel1 -> False) -> False)
  -> ((v1_funct_2 esk2_0 esk1_0 k6_margrel1 -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk7_1 X1) X1 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 k8_margrel1 k6_margrel1 -> False) -> False)
  -> ((v1_relat_1 esk10_0 -> False) -> False)
  -> ((v1_margrel1 esk10_0 -> False) -> False)
  -> ((v1_xboolean esk9_0 -> False) -> False)
  -> ((v1_xboolean k2_xboolean -> False) -> False)
  -> ((v1_funct_1 esk10_0 -> False) -> False)
  -> ((v1_funct_1 esk5_0 -> False) -> False)
  -> ((v1_funct_1 esk4_0 -> False) -> False)
  -> ((v1_funct_1 esk3_0 -> False) -> False)
  -> ((v1_funct_1 esk2_0 -> False) -> False)
  -> ((v1_xboole_0 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((k2_xboolean = np__1 -> False) -> False)
  -> ((k2_xboolean = k8_margrel1 -> False) -> False)
  -> False.
Admitted.