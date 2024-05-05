(** $I sig/MizarPreamble.mgs **)

Theorem t18_cfuncdom:
 forall esk18_4:set -> set -> set -> set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall k1_zfmisc_1:set -> set,
 forall v1_funct_2:set -> set -> set -> prop,
 forall v1_funct_1:set -> prop,
 forall k1_binop_1:set -> set -> set -> set,
 forall k6_complex1:set,
 forall m1_funct_2:set -> set -> set -> prop,
 forall esk10_3:set -> set -> set -> set,
 forall k4_tarski:set -> set -> set,
 forall k8_funcop_1:set -> set -> set -> set,
 forall m2_subset_1:set -> set -> set -> prop,
 forall v4_relat_1:set -> set -> prop,
 forall esk11_2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall k2_funcop_1:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall esk7_0:set,
 forall k5_complex1:set,
 forall esk6_0:set,
 forall esk15_0:set,
 forall esk4_0:set,
 forall esk5_0:set,
 forall esk12_2:set -> set -> set,
 forall k5_numbers:set,
 forall esk14_0:set,
 forall k4_ordinal1:set,
 forall esk13_0:set,
 forall esk9_1:set -> set,
 forall esk8_2:set -> set -> set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall esk16_0:set,
 forall v1_finset_1:set -> prop,
 forall k1_xboole_0:set,
 forall np__1:set,
 forall k1_funct_2:set -> set -> set,
 forall k1_numbers:set,
 forall k3_xcmplx_0:set -> set -> set,
 forall k2_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
 forall v5_relat_1:set -> set -> prop,
 forall k4_cfuncdom:set -> set,
 forall k6_numbers:set,
 forall epred1_5:set -> set -> set -> set -> set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall k1_cfuncdom:set -> set,
 forall k1_funcsdom:set -> set -> set -> set -> set -> set,
 forall esk17_4:set -> set -> set -> set -> set,
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
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k2_numbers X2 (k2_funcsdom X1 k2_numbers k2_numbers (k9_funct_2 X1 k2_numbers) (k3_cfuncdom X1) (k1_domain_1 k2_numbers (k9_funct_2 X1 k2_numbers) X4 X3)) -> False) -> (k3_funct_2 X1 k2_numbers X2 (esk18_4 X1 X2 X3 X4)) = (k9_complex1 X4 (k3_funct_2 X1 k2_numbers X3 (esk18_4 X1 X2 X3 X4))) -> m1_subset_1 X4 k2_numbers -> m2_funct_2 X3 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk18_4 X1 X2 X3 X4) X1 -> False) -> (r2_funct_2 X1 k2_numbers X2 (k2_funcsdom X1 k2_numbers k2_numbers (k9_funct_2 X1 k2_numbers) (k3_cfuncdom X1) (k1_domain_1 k2_numbers (k9_funct_2 X1 k2_numbers) X4 X3)) -> False) -> m1_subset_1 X4 k2_numbers -> m2_funct_2 X3 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> False)
  -> (forall X3 X1 X6 X5 X2 X4, (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_funct_2 (k2_funcsdom X1 X2 X3 X4 X5 X6) X1 X2 (k9_funct_2 X1 X2) -> False) -> v1_funct_1 X5 -> m1_subset_1 X6 (k2_zfmisc_1 X3 X4) -> v1_funct_2 X5 (k2_zfmisc_1 X3 X4) (k9_funct_2 X1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X4) (k9_funct_2 X1 X2))) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (r2_funct_2 X1 k2_numbers X2 (k1_funcsdom X1 k2_numbers (k1_cfuncdom X1) X3 X4) -> False) -> (k8_complex1 (k3_funct_2 X1 k2_numbers X3 (esk17_4 X1 X2 X3 X4)) (k3_funct_2 X1 k2_numbers X4 (esk17_4 X1 X2 X3 X4))) = (k3_funct_2 X1 k2_numbers X2 (esk17_4 X1 X2 X3 X4)) -> m2_funct_2 X4 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X3 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> False)
  -> (forall X5 X3 X2 X4 X1, ((k3_funct_2 X1 k2_numbers X2 X5) = (k8_complex1 (k3_funct_2 X1 k2_numbers X3 X5) (k3_funct_2 X1 k2_numbers X4 X5)) -> False) -> (v1_xboole_0 X1 -> False) -> m1_subset_1 X5 X1 -> m2_funct_2 X4 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X3 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> r2_funct_2 X1 k2_numbers X2 (k1_funcsdom X1 k2_numbers (k1_cfuncdom X1) X3 X4) -> False)
  -> (forall X3 X1 X6 X5 X2 X4, ((k2_funcsdom X1 X2 X3 X4 X5 X6) = (k1_funct_1 X5 X6) -> False) -> (v1_xboole_0 X4 -> False) -> (v1_xboole_0 X3 -> False) -> (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X5 -> m1_subset_1 X6 (k2_zfmisc_1 X3 X4) -> v1_funct_2 X5 (k2_zfmisc_1 X3 X4) (k9_funct_2 X1 X2) -> m1_subset_1 X5 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X3 X4) (k9_funct_2 X1 X2))) -> False)
  -> (forall X4 X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (esk17_4 X1 X2 X3 X4) X1 -> False) -> (r2_funct_2 X1 k2_numbers X2 (k1_funcsdom X1 k2_numbers (k1_cfuncdom X1) X3 X4) -> False) -> m2_funct_2 X4 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X3 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> m2_funct_2 X2 X1 k2_numbers (k9_funct_2 X1 k2_numbers) -> False)
  -> (forall X2 X4 X3 X5 X1, (v1_xboole_0 X1 -> False) -> (m2_funct_2 (k1_funcsdom X3 X1 X2 X4 X5) X3 X1 (k9_funct_2 X3 X1) -> False) -> v1_funct_1 X2 -> m1_subset_1 X5 (k9_funct_2 X3 X1) -> m1_subset_1 X4 (k9_funct_2 X3 X1) -> v1_funct_2 X2 (k2_zfmisc_1 (k9_funct_2 X3 X1) (k9_funct_2 X3 X1)) (k9_funct_2 X3 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k9_funct_2 X3 X1) (k9_funct_2 X3 X1)) (k9_funct_2 X3 X1))) -> False)
  -> (forall X2 X4 X3 X5 X1, ((k1_funcsdom X3 X1 X2 X4 X5) = (k1_binop_1 X2 X4 X5) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X5 (k9_funct_2 X3 X1) -> m1_subset_1 X4 (k9_funct_2 X3 X1) -> v1_funct_2 X2 (k2_zfmisc_1 (k9_funct_2 X3 X1) (k9_funct_2 X3 X1)) (k9_funct_2 X3 X1) -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k9_funct_2 X3 X1) (k9_funct_2 X3 X1)) (k9_funct_2 X3 X1))) -> False)
  -> (forall X2 X5 X6 X4 X1 X3, ((k1_funct_1 X3 X1) = k6_numbers -> False) -> X1 = X2 -> r2_hidden X1 X4 -> epred1_5 X3 X5 X2 X4 X6 -> False)
  -> (forall X2 X6 X5 X4 X1 X3, ((k1_funct_1 X3 X1) = k6_complex1 -> False) -> X1 = X2 -> r2_hidden X1 X4 -> epred1_5 X5 X3 X2 X4 X6 -> False)
  -> (forall X3 X6 X5 X4 X1 X2, (X1 = X2 -> False) -> ((k1_funct_1 X3 X1) = k6_numbers -> False) -> r2_hidden X1 X4 -> epred1_5 X5 X3 X2 X4 X6 -> False)
  -> (forall X3 X5 X6 X4 X1 X2, (X1 = X2 -> False) -> ((k1_funct_1 X3 X1) = k6_complex1 -> False) -> r2_hidden X1 X4 -> epred1_5 X3 X5 X2 X4 X6 -> False)
  -> (forall X4 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> epred1_5 X3 X4 X1 X2 X5 -> False)
  -> (forall X4 X5 X3 X1 X2, (r2_hidden X1 X2 -> False) -> epred1_5 X3 X4 X5 X2 X1 -> False)
  -> (forall X1 X3 X2 X4, (r2_funct_2 X2 X3 X4 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> r2_funct_2 X2 X3 X1 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X2 X3 X4, (X3 = X4 -> False) -> v1_funct_1 X4 -> v1_funct_1 X3 -> v1_funct_2 X4 X1 X2 -> v1_funct_2 X3 X1 X2 -> r2_funct_2 X1 X2 X3 X4 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> m1_subset_1 X3 (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False)
  -> (forall X2 X3 X4 X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_funct_2 X1 X3 X2 X4) X3 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X3 X4 X1 X2, (r2_funct_2 X3 X4 X1 X2 -> False) -> X1 = X2 -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_funct_2 X2 X3 X4 -> v1_funct_2 X1 X3 X4 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X4)) -> False)
  -> (forall X4 X1 X3 X2, (r2_funct_2 X2 X3 X1 X1 -> False) -> v1_funct_1 X4 -> v1_funct_1 X1 -> v1_funct_2 X4 X2 X3 -> v1_funct_2 X1 X2 X3 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_cfuncdom X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 (k9_funct_2 X1 k2_numbers) (k9_funct_2 X1 k2_numbers)) (k9_funct_2 X1 k2_numbers))) -> False) -> False)
  -> (forall X1 X4 X3 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k1_domain_1 X1 X2 X3 X4) (k2_zfmisc_1 X1 X2) -> False) -> m1_subset_1 X4 X2 -> m1_subset_1 X3 X1 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_2 X1 X2 X3 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X2 X3 X4 X1, ((k3_funct_2 X1 X3 X2 X4) = (k1_funct_1 X2 X4) -> False) -> (v1_xboole_0 X1 -> False) -> v1_funct_1 X2 -> m1_subset_1 X4 X1 -> v1_funct_2 X2 X1 X3 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X4 X1 X2 X3, (v1_xboole_0 X3 -> False) -> (m1_subset_1 X1 X4 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X1 X2 X4 X3, (v1_xboole_0 X3 -> False) -> (v1_funct_1 X1 -> False) -> m1_funct_2 X4 X2 X3 -> m2_funct_2 X1 X2 X3 X4 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (m1_subset_1 (k3_cfuncdom X1) (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 k2_numbers (k9_funct_2 X1 k2_numbers)) (k9_funct_2 X1 k2_numbers))) -> False) -> False)
  -> (forall X3 X2 X1, (v1_xboole_0 X1 -> False) -> (m2_funct_2 (esk10_3 X3 X1 X2) X3 X1 X2 -> False) -> m1_funct_2 X2 X3 X1 -> False)
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
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (v1_xboole_0 X1 -> False) -> (m2_subset_1 (esk11_2 X1 X2) X1 X2 -> False) -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
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
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, ((k1_funct_2 X2 X1) = (k9_funct_2 X2 X1) -> False) -> (v1_xboole_0 X1 -> False) -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1, (v1_xcmplx_0 X1 -> False) -> m1_subset_1 X1 k2_numbers -> False)
  -> (forall X1, ((k3_xcmplx_0 np__1 X1) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k2_xcmplx_0 X1 k6_numbers) = X1 -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X1, ((k3_xcmplx_0 X1 k6_numbers) = k6_numbers -> False) -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k3_cfuncdom X1) -> False) -> False)
  -> (forall X1, (v1_xboole_0 X1 -> False) -> (v1_funct_1 (k1_cfuncdom X1) -> False) -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> (esk6_0 = k5_complex1 -> esk7_0 = k5_complex1 -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v1_finset_1 k2_numbers -> False)
  -> (v1_xboole_0 esk16_0 -> False)
  -> (v1_xboole_0 esk15_0 -> False)
  -> (v1_xboole_0 esk3_0 -> False)
  -> (v1_xboole_0 np__1 -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (v1_xboole_0 k2_numbers -> False)
  -> (esk2_0 = esk1_0 -> False)
  -> ((r2_funct_2 esk3_0 k2_numbers (k1_funcsdom esk3_0 k2_numbers (k1_cfuncdom esk3_0) (k2_funcsdom esk3_0 k2_numbers k2_numbers (k9_funct_2 esk3_0 k2_numbers) (k3_cfuncdom esk3_0) (k1_domain_1 k2_numbers (k9_funct_2 esk3_0 k2_numbers) esk6_0 esk4_0)) (k2_funcsdom esk3_0 k2_numbers k2_numbers (k9_funct_2 esk3_0 k2_numbers) (k3_cfuncdom esk3_0) (k1_domain_1 k2_numbers (k9_funct_2 esk3_0 k2_numbers) esk7_0 esk5_0))) (k4_cfuncdom esk3_0) -> False) -> False)
  -> ((epred1_5 esk5_0 esk4_0 esk1_0 esk3_0 esk2_0 -> False) -> False)
  -> ((m2_funct_2 esk5_0 esk3_0 k2_numbers (k9_funct_2 esk3_0 k2_numbers) -> False) -> False)
  -> ((m2_funct_2 esk4_0 esk3_0 k2_numbers (k9_funct_2 esk3_0 k2_numbers) -> False) -> False)
  -> (forall X2 X1, (m1_subset_1 (esk12_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (m1_funct_2 (esk8_2 X1 X2) X1 X2 -> False) -> False)
  -> ((m2_subset_1 k6_numbers k1_numbers k5_numbers -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk12_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk12_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk12_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk9_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 k5_numbers (k1_zfmisc_1 k1_numbers) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((m1_subset_1 esk7_0 k2_numbers -> False) -> False)
  -> ((m1_subset_1 esk6_0 k2_numbers -> False) -> False)
  -> ((m1_subset_1 k5_complex1 k2_numbers -> False) -> False)
  -> ((m1_subset_1 k6_complex1 k2_numbers -> False) -> False)
  -> (((k3_xcmplx_0 np__1 np__1) = np__1 -> False) -> False)
  -> ((v1_xcmplx_0 esk16_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk14_0 -> False) -> False)
  -> ((v1_xboole_0 esk13_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((k5_numbers = k4_ordinal1 -> False) -> False)
  -> ((k5_complex1 = k1_xboole_0 -> False) -> False)
  -> ((k6_numbers = k1_xboole_0 -> False) -> False)
  -> ((np__1 = k6_complex1 -> False) -> False)
  -> False.
Admitted.
