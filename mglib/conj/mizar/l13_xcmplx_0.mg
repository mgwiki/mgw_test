(** $I sig/MizarPreamble.mgs **)

Theorem l13_xcmplx_0:
 forall k1_numbers:set,
 forall m1_subset_1:set -> set -> prop,
 forall k2_numbers:set,
 forall v1_xboole_0:set -> prop,
 forall v1_funct_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall k1_xboole_0:set,
 forall v1_finset_1:set -> prop,
 forall esk16_0:set,
 forall esk17_0:set,
 forall esk12_0:set,
 forall esk9_0:set,
 forall esk11_0:set,
 forall esk10_0:set,
 forall esk13_0:set,
 forall esk8_1:set -> set,
 forall esk14_0:set,
 forall esk15_0:set,
 forall esk1_0:set,
 forall esk2_0:set,
 forall esk3_0:set,
 forall v1_zfmisc_1:set -> prop,
 forall v3_funct_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall v1_relat_1:set -> prop,
 forall r2_hidden:set -> set -> prop,
 forall esk6_3:set -> set -> set -> set,
 forall esk5_3:set -> set -> set -> set,
 forall k2_arytm_0:set -> set -> set,
 forall esk7_3:set -> set -> set -> set,
 forall esk4_3:set -> set -> set -> set,
 forall k1_arytm_0:set -> set -> set,
 forall k3_arytm_0:set -> set,
 forall k5_arytm_0:set -> set -> set,
 forall k3_xcmplx_0:set -> set -> set,
 forall v1_xcmplx_0:set -> prop,
     (forall X1 X3 X2, ((k5_arytm_0 (k1_arytm_0 (k2_arytm_0 (esk4_3 X2 X3 X1) (esk6_3 X2 X3 X1)) (k3_arytm_0 (k2_arytm_0 (esk5_3 X2 X3 X1) (esk7_3 X2 X3 X1)))) (k1_arytm_0 (k2_arytm_0 (esk4_3 X2 X3 X1) (esk7_3 X2 X3 X1)) (k2_arytm_0 (esk5_3 X2 X3 X1) (esk6_3 X2 X3 X1)))) = X1 -> False) -> X1 = (k3_xcmplx_0 X2 X3) -> v1_xcmplx_0 X3 -> v1_xcmplx_0 X2 -> False)
  -> (forall X4 X3 X1 X2 X5 X6 X7, (X7 = (k3_xcmplx_0 X5 X6) -> False) -> X6 = (k5_arytm_0 X3 X4) -> X5 = (k5_arytm_0 X1 X2) -> X7 = (k5_arytm_0 (k1_arytm_0 (k2_arytm_0 X1 X3) (k3_arytm_0 (k2_arytm_0 X2 X4))) (k1_arytm_0 (k2_arytm_0 X1 X4) (k2_arytm_0 X2 X3))) -> v1_xcmplx_0 X6 -> v1_xcmplx_0 X5 -> m1_subset_1 X4 k1_numbers -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X3 X2 X1, ((k5_arytm_0 (esk6_3 X2 X1 X3) (esk7_3 X2 X1 X3)) = X1 -> False) -> X3 = (k3_xcmplx_0 X2 X1) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X3 X2 X1, ((k5_arytm_0 (esk4_3 X1 X2 X3) (esk5_3 X1 X2 X3)) = X1 -> False) -> X3 = (k3_xcmplx_0 X1 X2) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k1_arytm_0 (k2_arytm_0 X1 X2) (k2_arytm_0 X1 X3)) = (k2_arytm_0 X1 (k1_arytm_0 X2 X3)) -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk7_3 X1 X2 X3) k1_numbers -> False) -> X3 = (k3_xcmplx_0 X1 X2) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk6_3 X1 X2 X3) k1_numbers -> False) -> X3 = (k3_xcmplx_0 X1 X2) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk5_3 X1 X2 X3) k1_numbers -> False) -> X3 = (k3_xcmplx_0 X1 X2) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk4_3 X1 X2 X3) k1_numbers -> False) -> X3 = (k3_xcmplx_0 X1 X2) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2 X3, ((k2_arytm_0 (k2_arytm_0 X1 X2) X3) = (k2_arytm_0 X1 (k2_arytm_0 X2 X3)) -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2 X3, ((k1_arytm_0 (k1_arytm_0 X1 X2) X3) = (k1_arytm_0 X1 (k1_arytm_0 X2 X3)) -> False) -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X4 X3 X1 X2, (X1 = X2 -> False) -> (k5_arytm_0 X1 X3) = (k5_arytm_0 X2 X4) -> m1_subset_1 X4 k1_numbers -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X4 X3 X1 X2, (X1 = X2 -> False) -> (k5_arytm_0 X3 X1) = (k5_arytm_0 X4 X2) -> m1_subset_1 X4 k1_numbers -> m1_subset_1 X3 k1_numbers -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k1_arytm_0 (k3_arytm_0 X1) (k3_arytm_0 X2)) = (k3_arytm_0 (k1_arytm_0 X1 X2)) -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k3_arytm_0 (k2_arytm_0 X1 X2)) = (k2_arytm_0 (k3_arytm_0 X1) X2) -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k5_arytm_0 X1 X2) k2_numbers -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k2_arytm_0 X1 X2) k1_numbers -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_arytm_0 X1 X2) k1_numbers -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k2_arytm_0 X1 X2) = (k2_arytm_0 X2 X1) -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, ((k1_arytm_0 X1 X2) = (k1_arytm_0 X2 X1) -> False) -> m1_subset_1 X2 k1_numbers -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_xcmplx_0 (k3_xcmplx_0 X1 X2) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X2 X1, ((k3_xcmplx_0 X1 X2) = (k3_xcmplx_0 X2 X1) -> False) -> v1_xcmplx_0 X2 -> v1_xcmplx_0 X1 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (m1_subset_1 (k3_arytm_0 X1) k1_numbers -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, ((k3_arytm_0 (k3_arytm_0 X1)) = X1 -> False) -> m1_subset_1 X1 k1_numbers -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_zfmisc_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k3_xcmplx_0 (k3_xcmplx_0 esk1_0 esk2_0) esk3_0) = (k3_xcmplx_0 esk1_0 (k3_xcmplx_0 esk2_0 esk3_0)) -> False)
  -> (v1_finset_1 k2_numbers -> False)
  -> (v1_finset_1 k1_numbers -> False)
  -> (v3_funct_1 esk16_0 -> False)
  -> (v1_zfmisc_1 esk15_0 -> False)
  -> (v1_xboole_0 esk17_0 -> False)
  -> (v1_xboole_0 esk14_0 -> False)
  -> (v1_xboole_0 esk12_0 -> False)
  -> (v1_xboole_0 k2_numbers -> False)
  -> (v1_xboole_0 k1_numbers -> False)
  -> (forall X1, (m1_subset_1 (esk8_1 X1) X1 -> False) -> False)
  -> ((v4_funct_1 esk17_0 -> False) -> False)
  -> ((v2_funct_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk16_0 -> False) -> False)
  -> ((v1_relat_1 esk13_0 -> False) -> False)
  -> ((v1_relat_1 esk9_0 -> False) -> False)
  -> ((v1_zfmisc_1 esk12_0 -> False) -> False)
  -> ((v1_funct_1 esk16_0 -> False) -> False)
  -> ((v1_funct_1 esk13_0 -> False) -> False)
  -> ((v1_funct_1 esk9_0 -> False) -> False)
  -> ((v1_xboole_0 esk10_0 -> False) -> False)
  -> ((v1_xboole_0 k1_xboole_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk11_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk3_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk2_0 -> False) -> False)
  -> ((v1_xcmplx_0 esk1_0 -> False) -> False)
  -> False.
Admitted.
