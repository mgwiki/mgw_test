(** $I sig/MizarPreamble.mgs **)

Theorem t11_cfuncdom:
 forall esk13_4:set -> set -> set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_binop_1:set -> set -> set -> set,
 forall m1_funct_2:set -> set -> set -> prop,
 forall esk5_3:set -> set -> set -> set,
 forall k4_tarski:set -> set -> set,
 forall k8_funcop_1:set -> set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk6_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k2_funcop_1:set -> set -> set,
 forall k4_xcmplx_0:set -> set,
 forall k1_numbers:set,
 forall k6_numbers:set,
 forall np__1:set,
 forall k1_xboole_0:set,
 forall v1_finset_1:set -> prop,
 forall esk11_0:set,
 forall esk3_2:set -> set -> set,
 forall esk4_1:set -> set,
 forall esk9_0:set,
 forall k4_ordinal1:set,
 forall esk8_0:set,
 forall np__0:set,
 forall k5_numbers:set,
 forall esk7_2:set -> set -> set,
 forall esk10_0:set,
 forall esk2_0:set,
 forall k6_complex1:set,
 forall esk1_0:set,
 forall k1_funct_2:set -> set -> set,
 forall k10_complex1:set -> set,
 forall r1_tarski:set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k3_xcmplx_0:set -> set -> set,
 forall k2_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall k4_cfuncdom:set -> set,
 forall esk14_4:set -> set -> set -> set -> set,
 forall r2_relset_1:set -> set -> set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall k1_cfuncdom:set -> set,
 forall k1_funcsdom:set -> set -> set -> set -> set -> set,
 forall esk12_4:set -> set -> set -> set -> set,
 forall k8_complex1:set -> set -> set,
 forall v1_xboole_0:set -> prop,
 forall r2_funct_2:set -> set -> set -> set -> prop,
 forall k3_cfuncdom:set -> set,
 forall k1_domain_1:set -> set -> set -> set -> set,
 forall k2_funcsdom:set -> set -> set -> set -> set -> set -> set,
 forall k9_funct_2:set -> set -> set,
 forall m2_funct_2:set -> set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall k9_complex1:set -> set -> set,
 forall k3_funct_2:set -> set -> set -> set -> set,
 forall k2_numbers:set,
     (forall X5 X4 X2 X3 X1, ((k3_funct_2 X1 k2_numbers X2 X5) = (k9_complex1 X3 (k3_funct_2 X1 k2_numbers X4 X5)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X5 X1 -> m1_subset_1 X3 k2_numbers -> m2_funct_2 X4 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> r2_funct_2 X1 k2_numbers X2 (k2_funcsdom X1 k2_numbers k2_numbers (k9_funct_2 X1 k2_numbers) (k3_cfuncdom X1) (k1_domain_1 k2_numbers (k9_funct_2 X1 k2_numbers) X3 X4)) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k2_numbers X2 (k2_funcsdom X1 k2_numbers k2_numbers (k9_funct_2 X1 k2_numbers) (k3_cfuncdom X1) (k1_domain_1 k2_numbers (k9_funct_2 X1 k2_numbers) X4 X3)) -> False) -> (k3_funct_2 X1 k2_numbers X2 (esk13_4 X1 X2 X3 X4)) = (k9_complex1 X4 (k3_funct_2 X1 k2_numbers X3 (esk13_4 X1 X2 X3 X4))) -> m1_subset_1 X4 k2_numbers -> m2_funct_2 X3 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk13_4 X1 X2 X3 X4) X1 -> False) -> (r2_funct_2 X1 k2_numbers X2 (k2_funcsdom X1 k2_numbers k2_numbers (k9_funct_2 X1 k2_numbers) (k3_cfuncdom X1) (k1_domain_1 k2_numbers (k9_funct_2 X1 k2_numbers) X4 X3)) -> False) -> m1_subset_1 X4 k2_numbers -> m2_funct_2 X3 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> False)
  -> (forall X3 X1 X6 X5 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_funct_2 (k2_funcsdom X1 X2 X3 X4 X5 X6) X1 X2 (k9_funct_2 X1 X2) -> False) -> v1_funct_1 X5 -> m1_subset_1 X6 (k2_zfmisc_1 X3 X4) -> v1_funct_2 X5 (k2_zfmisc_1 X3 X4) (k9_funct_2 X1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X4) (k9_funct_2 X1 X2))) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k2_numbers X2 (k1_funcsdom X1 k2_numbers (k1_cfuncdom X1) X3 X4) -> False) -> (k8_complex1 (k3_funct_2 X1 k2_numbers X3 (esk12_4 X1 X2 X3 X4)) (k3_funct_2 X1 k2_numbers X4 (esk12_4 X1 X2 X3 X4))) = (k3_funct_2 X1 k2_numbers X2 (esk12_4 X1 X2 X3 X4)) -> m2_funct_2 X4 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X3 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> False)
  -> (forall X5 X3 X2 X4 X1, ((k3_funct_2 X1 k2_numbers X2 X5) = (k8_complex1 (k3_funct_2 X1 k2_numbers X3 X5) (k3_funct_2 X1 k2_numbers X4 X5)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X5 X1 -> m2_funct_2 X4 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X3 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> r2_funct_2 X1 k2_numbers X2 (k1_funcsdom X1 k2_numbers (k1_cfuncdom X1) X3 X4) -> False)
  -> (forall X3 X1 X6 X5 X2 X4, ((k2_funcsdom X1 X2 X3 X4 X5 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X5 -> m1_subset_1 X6 (k2_zfmisc_1 X3 X4) -> v1_funct_2 X5 (k2_zfmisc_1 X3 X4) (k9_funct_2 X1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X4) (k9_funct_2 X1 X2))) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk12_4 X1 X2 X3 X4) X1 -> False) -> (r2_funct_2 X1 k2_numbers X2 (k1_funcsdom X1 k2_numbers (k1_cfuncdom X1) X3 X4) -> False) -> m2_funct_2 X4 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X3 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> False)
  -> (forall X2 X4 X3 X5 X1, (v1_xboole_0 X1 -> False) -> (m2_funct_2 (k1_funcsdom X3 X1 X2 X4 X5) X3 X1 (k9_funct_2 X3 X1) -> False) -> v1_funct_1 X2 -> m1_subset_1 X5 (k9_funct_2 X3 X1) -> m1_subset_1 X4 (k9_funct_2 X3 X1) -> v1_funct_2 X2 (k2_zfmisc_1 (k9_funct_2 X3 X1) (k9_funct_2 X3 X1)) (k9_funct_2 X3 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k9_funct_2 X3 X1) (k9_funct_2 X3 X1)) (k9_funct_2 X3 X1))) -> False)
  -> (forall X2 X4 X3 X5 X1, ((k1_funcsdom X3 X1 X2 X4 X5) = (k1_binop_1 X2 X4 X5) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X5 (k9_funct_2 X3 X1) -> m1_subset_1 X4 (k9_funct_2 X3 X1) -> v1_funct_2 X2 (k2_zfmisc_1 (k9_funct_2 X3 X1) (k9_funct_2 X3 X1)) (k9_funct_2 X3 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k9_funct_2 X3 X1) (k9_funct_2 X3 X1)) (k9_funct_2 X3 X1))) -> False)
  -> (forall X1 X3 X2 X4, (r2_relset_1 X2 X3 X1 X4 -> False) -> (k1_funct_1 X1 (esk14_4 X2 X3 X1 X4)) = (k1_funct_1 X4 (esk14_4 X2 X3 X1 X4)) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1 X4, (r2_relset_1 X1 X2 X3 X4 -> False) -> (m1_subset_1 (esk14_4 X1 X2 X3 X4) X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X4 X1 X2 X3, (r2_relset_1 X2 X3 X4 X1 -> False) -> r2_relset_1 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_cfuncdom X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k9_funct_2 X1 k2_numbers) (k9_funct_2 X1 k2_numbers)) (k9_funct_2 X1 k2_numbers))) -> False) -> False)
  -> (forall X2 X1 X3 X4, (X3 = X4 -> False) -> r2_relset_1 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_domain_1 X1 X2 X3 X4) (k2_zfmisc_1 X1 X2) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_2 X1 X2 X3 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X4 X1 X2 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 X1 X4 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 X1 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X4 X3 X1 X2, (r2_relset_1 X3 X4 X1 X2 -> False) -> X1 = X2 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_relset_1 X2 X3 X1 X1 -> False) -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_cfuncdom X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 k2_numbers (k9_funct_2 X1 k2_numbers)) (k9_funct_2 X1 k2_numbers))) -> False) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m2_funct_2 (esk5_3 X3 X1 X2) X3 X1 X2 -> False) -> m1_funct_2 X2 X3 X1 -> False)
  -> (forall X2 X1 X3 X4, (v1_xboole_0 X4 -> False) -> (m2_funct_2 X1 X3 X4 X2 -> False) -> m1_subset_1 X1 X2 -> m1_funct_2 X2 X3 X4 -> False)
  -> (forall X1 X4 X3 X2, ((k1_domain_1 X1 X2 X3 X4) = (k4_tarski X3 X4) -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m2_funct_2 (k4_cfuncdom X1) X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> False) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k8_funcop_1 X1 X2 X3) (k1_zfmisc_1 (k2_zfmisc_1 X2 X1)) -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k1_cfuncdom X1) (k2_zfmisc_1 (k9_funct_2 X1 k2_numbers) (k9_funct_2 X1 k2_numbers)) (k9_funct_2 X1 k2_numbers) -> False) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k8_funcop_1 X1 X2 X3) X2 X1 -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_funct_2 (k3_cfuncdom X1) (k2_zfmisc_1 k2_numbers (k9_funct_2 X1 k2_numbers)) (k9_funct_2 X1 k2_numbers) -> False) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 X3 X1 -> False) -> m2_subset_1 X3 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m1_subset_1 X1 X3 -> False) -> m2_subset_1 X1 X2 X3 -> m1_subset_1 X3 (k1_zfmisc_1 X2) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k8_funcop_1 X1 X2 X3) -> False) -> m1_subset_1 X3 X1 -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k3_xcmplx_0 X1 X3) (k3_xcmplx_0 X2 X3)) = (k3_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk6_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1 X3, (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (m2_subset_1 X1 X3 X2 -> False) -> m1_subset_1 X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 X1 (k4_tarski X2 X3)) = (k1_binop_1 X1 X2 X3) -> False) -> v1_relat_1 X1 -> v1_funct_1 X1 -> False)
  -> (forall X1 X2 X3, ((k3_xcmplx_0 (k3_xcmplx_0 X1 X2) X3) = (k3_xcmplx_0 X1 (k3_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k2_xcmplx_0 (k2_xcmplx_0 X1 X2) X3) = (k2_xcmplx_0 X1 (k2_xcmplx_0 X2 X3)) -> False) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X3 X2 X1, ((k8_funcop_1 X1 X3 X2) = (k2_funcop_1 X3 X2) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X2 X1 -> False)
  -> (forall X3 X2 X1, v1_xboole_0 X1 -> m1_funct_2 X1 X2 X3 -> False)
  -> (forall X2 X1, (v1_xboole_0 X1 -> False) -> (m1_funct_2 (k9_funct_2 X2 X1) X2 X1 -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (k9_complex1 X1 X2) k2_numbers -> False) -> m1_subset_1 X2 k2_numbers -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k8_complex1 X1 X2) k2_numbers -> False) -> m1_subset_1 X2 k2_numbers -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> v1_xboole_0 (k3_xcmplx_0 X1 X2) -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 (k4_xcmplx_0 X1) (k4_xcmplx_0 X2)) = (k4_xcmplx_0 (k2_xcmplx_0 X1 X2)) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, ((k9_complex1 X1 X2) = (k9_complex1 X2 X1) -> False) -> m1_subset_1 X2 k2_numbers -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X2 X1, ((k9_complex1 X1 X2) = (k3_xcmplx_0 X1 X2) -> False) -> m1_subset_1 X2 k2_numbers -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X2 X1, ((k8_complex1 X1 X2) = (k8_complex1 X2 X1) -> False) -> m1_subset_1 X2 k2_numbers -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X2 X1, ((k8_complex1 X1 X2) = (k2_xcmplx_0 X1 X2) -> False) -> m1_subset_1 X2 k2_numbers -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X3 X2 X1, ((k1_funct_1 (k2_funcop_1 X2 X3) X1) = X3 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1, ((k8_funcop_1 k1_numbers X1 k6_numbers) = (k4_cfuncdom X1) -> False) -> (v1_xboole_0 X1 -> False) -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k3_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k2_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k2_xcmplx_0 X1 X2) = (k2_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (k10_complex1 X1) k2_numbers -> False) -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k1_funct_2 X2 X1) = (k9_funct_2 X2 X1) -> False) -> (v1_xboole_0 X1 -> False) -> False)
  -> (forall X1, ((k10_complex1 (k10_complex1 X1)) = X1 -> False) -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, ((k10_complex1 X1) = (k4_xcmplx_0 X1) -> False) -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> v1_xcmplx_0 X1 -> v1_xboole_0 (k4_xcmplx_0 X1) -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k4_xcmplx_0 (k4_xcmplx_0 X1)) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, (v1_xcmplx_0 (k4_xcmplx_0 X1) -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k3_cfuncdom X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k1_cfuncdom X1) -> False) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (r2_funct_2 esk1_0 k2_numbers (k1_funcsdom esk1_0 k2_numbers (k1_cfuncdom esk1_0) esk2_0 (k2_funcsdom esk1_0 k2_numbers k2_numbers (k9_funct_2 esk1_0 k2_numbers) (k3_cfuncdom esk1_0) (k1_domain_1 k2_numbers (k9_funct_2 esk1_0 k2_numbers) (k10_complex1 k6_complex1) esk2_0))) (k4_cfuncdom esk1_0) -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_finset_1 k2_numbers -> False)
  -> (v1_xboole_0 esk11_0 -> False)
  -> (v1_xboole_0 esk10_0 -> False)
  -> (v1_xboole_0 esk1_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (v1_xboole_0 k2_numbers -> False)
  -> ((m2_funct_2 esk2_0 esk1_0 k2_numbers (k9_funct_2 esk1_0 k2_numbers) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk7_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_funct_2 (esk3_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk7_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk7_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk7_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk7_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk4_1 X1) X1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 (k4_xcmplx_0 np__1)) = (k4_xcmplx_0 np__1) -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (((k2_xcmplx_0 (k4_xcmplx_0 np__1) np__1) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 (k4_xcmplx_0 np__1)) = np__0 -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 k6_complex1 k2_numbers -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__0 np__1) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__0) = np__0 -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__0) = np__0 -> False) -> False)
  -> (((k2_xcmplx_0 np__0 np__1) = np__1 -> False) -> False)
  -> (((k2_xcmplx_0 np__1 np__0) = np__1 -> False) -> False)
  -> (((k4_xcmplx_0 (k4_xcmplx_0 np__1)) = np__1 -> False) -> False)
  -> ((v1_xcmplx_0 esk11_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 esk8_0 -> False) -> False)
  -> ((v1_xboole_0 np__0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> (((k4_xcmplx_0 np__0) = np__0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((np__1 = k6_complex1 -> False) -> False)
  -> False.
Admitted.
