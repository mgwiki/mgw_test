(** $I sig/MizarPreamble.mgs **)

Theorem t12_projred2:
 forall u2_incsp_1:set -> set,
 forall k1_projred1:set -> set -> set -> set -> set,
 forall k3_relat_1:set -> set -> set,
 forall k9_xtuple_0:set -> set,
 forall v1_incproj:set -> prop,
 forall v3_incproj:set -> prop,
 forall v5_incproj:set -> prop,
 forall l1_incsp_1:set -> prop,
 forall v9_incproj:set -> prop,
 forall v4_incproj:set -> prop,
 forall v2_incproj:set -> prop,
 forall v6_incsp_1:set -> prop,
 forall k1_zfmisc_1:set -> set,
 forall k2_zfmisc_1:set -> set -> set,
 forall v1_funct_1:set -> prop,
 forall k1_projred2:set -> set -> set,
 forall v1_relat_1:set -> prop,
 forall esk9_3:set -> set -> set -> set,
 forall esk11_1:set -> set,
 forall esk10_1:set -> set,
 forall esk7_1:set -> set,
 forall esk8_1:set -> set,
 forall v5_relat_1:set -> set -> prop,
 forall v1_xboole_0:set -> prop,
 forall v1_zfmisc_1:set -> prop,
 forall esk5_0:set,
 forall esk3_0:set,
 forall esk4_0:set,
 forall esk2_0:set,
 forall esk1_0:set,
 forall esk18_0:set,
 forall esk16_2:set -> set -> set,
 forall esk13_1:set -> set,
 forall esk15_0:set,
 forall esk12_0:set,
 forall esk17_0:set,
 forall esk19_2:set -> set -> set,
 forall esk20_0:set,
 forall k1_xboole_0:set,
 forall v3_funct_1:set -> prop,
 forall v2_funct_1:set -> prop,
 forall v4_funct_1:set -> prop,
 forall esk22_2:set -> set -> set,
 forall v4_relat_1:set -> set -> prop,
 forall esk21_2:set -> set -> set,
 forall esk6_3:set -> set -> set -> set,
 forall a_2_0_projred2:set -> set -> set,
 forall esk14_3:set -> set -> set -> set,
 forall k10_xtuple_0:set -> set,
 forall esk27_5:set -> set -> set -> set -> set -> set,
 forall esk26_5:set -> set -> set -> set -> set -> set,
 forall esk25_5:set -> set -> set -> set -> set -> set,
 forall esk24_5:set -> set -> set -> set -> set -> set,
 forall r2_hidden:set -> set -> prop,
 forall k1_relset_1:set -> set -> set,
 forall r1_tarski:set -> set -> prop,
 forall k1_funct_1:set -> set -> set,
 forall epred1_5:set -> set -> set -> set -> set -> prop,
 forall m1_subset_1:set -> set -> prop,
 forall u1_incsp_1:set -> set,
 forall r1_incsp_1:set -> set -> set -> prop,
 forall esk23_7:set -> set -> set -> set -> set -> set -> set -> set,
     (forall X1 X4 X2 X5 X6 X3 X7, (r1_incsp_1 X1 X2 (esk23_7 X3 X2 X4 X5 X1 X6 X7) -> False) -> (k1_funct_1 X3 X6) = X7 -> r1_incsp_1 X1 X7 X4 -> r1_incsp_1 X1 X6 X5 -> m1_subset_1 X7 (u1_incsp_1 X1) -> m1_subset_1 X6 (u1_incsp_1 X1) -> epred1_5 X1 X4 X2 X3 X5 -> False)
  -> (forall X1 X5 X4 X6 X2 X3 X7, (r1_incsp_1 X1 X2 (esk23_7 X3 X4 X5 X6 X1 X2 X7) -> False) -> (k1_funct_1 X3 X2) = X7 -> r1_incsp_1 X1 X7 X5 -> r1_incsp_1 X1 X2 X6 -> m1_subset_1 X7 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> epred1_5 X1 X5 X4 X3 X6 -> False)
  -> (forall X1 X6 X4 X5 X7 X3 X2, (r1_incsp_1 X1 X2 (esk23_7 X3 X4 X5 X6 X1 X7 X2) -> False) -> (k1_funct_1 X3 X7) = X2 -> r1_incsp_1 X1 X7 X6 -> r1_incsp_1 X1 X2 X5 -> m1_subset_1 X7 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> epred1_5 X1 X5 X4 X3 X6 -> False)
  -> (forall X5 X3 X2 X4 X6 X1 X7, (m1_subset_1 (esk23_7 X1 X2 X3 X4 X5 X6 X7) (u2_incsp_1 X5) -> False) -> (k1_funct_1 X1 X6) = X7 -> r1_incsp_1 X5 X7 X3 -> r1_incsp_1 X5 X6 X4 -> m1_subset_1 X7 (u1_incsp_1 X5) -> m1_subset_1 X6 (u1_incsp_1 X5) -> epred1_5 X5 X3 X2 X1 X4 -> False)
  -> (forall X6 X3 X4 X1 X2 X5, (epred1_5 X5 X3 X2 X1 X4 -> False) -> (k1_funct_1 X1 (esk25_5 X1 X2 X3 X4 X5)) = (esk26_5 X1 X2 X3 X4 X5) -> r1_incsp_1 X5 X2 X6 -> m1_subset_1 X6 (u2_incsp_1 X5) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> r1_incsp_1 X5 (esk24_5 X1 X2 X3 X4 X5) X4 -> r1_incsp_1 X5 (esk25_5 X1 X2 X3 X4 X5) X6 -> r1_incsp_1 X5 (esk26_5 X1 X2 X3 X4 X5) X6 -> r2_hidden (esk24_5 X1 X2 X3 X4 X5) (k1_relset_1 (u1_incsp_1 X5) X1) -> False)
  -> (forall X6 X3 X4 X1 X2 X5, (epred1_5 X5 X3 X2 X1 X4 -> False) -> (r1_incsp_1 X5 (esk24_5 X1 X2 X3 X4 X5) X4 -> False) -> (r2_hidden (esk24_5 X1 X2 X3 X4 X5) (k1_relset_1 (u1_incsp_1 X5) X1) -> False) -> (k1_funct_1 X1 (esk25_5 X1 X2 X3 X4 X5)) = (esk26_5 X1 X2 X3 X4 X5) -> r1_incsp_1 X5 X2 X6 -> m1_subset_1 X6 (u2_incsp_1 X5) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> r1_incsp_1 X5 (esk25_5 X1 X2 X3 X4 X5) X6 -> r1_incsp_1 X5 (esk26_5 X1 X2 X3 X4 X5) X6 -> False)
  -> (forall X4 X5 X3 X2 X1, ((k1_funct_1 X2 (esk25_5 X2 X3 X4 X5 X1)) = (esk26_5 X2 X3 X4 X5 X1) -> False) -> (epred1_5 X1 X4 X3 X2 X5 -> False) -> (r1_incsp_1 X1 (esk26_5 X2 X3 X4 X5 X1) (esk27_5 X2 X3 X4 X5 X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> r1_incsp_1 X1 (esk24_5 X2 X3 X4 X5 X1) X5 -> r2_hidden (esk24_5 X2 X3 X4 X5 X1) (k1_relset_1 (u1_incsp_1 X1) X2) -> False)
  -> (forall X4 X5 X3 X2 X1, ((k1_funct_1 X2 (esk25_5 X2 X3 X4 X5 X1)) = (esk26_5 X2 X3 X4 X5 X1) -> False) -> (epred1_5 X1 X4 X3 X2 X5 -> False) -> (r1_incsp_1 X1 (esk25_5 X2 X3 X4 X5 X1) (esk27_5 X2 X3 X4 X5 X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> r1_incsp_1 X1 (esk24_5 X2 X3 X4 X5 X1) X5 -> r2_hidden (esk24_5 X2 X3 X4 X5 X1) (k1_relset_1 (u1_incsp_1 X1) X2) -> False)
  -> (forall X6 X3 X4 X1 X2 X5, (epred1_5 X5 X3 X2 X1 X4 -> False) -> (m1_subset_1 (esk24_5 X1 X2 X3 X4 X5) (u1_incsp_1 X5) -> False) -> (k1_funct_1 X1 (esk25_5 X1 X2 X3 X4 X5)) = (esk26_5 X1 X2 X3 X4 X5) -> r1_incsp_1 X5 X2 X6 -> m1_subset_1 X6 (u2_incsp_1 X5) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> r1_incsp_1 X5 (esk25_5 X1 X2 X3 X4 X5) X6 -> r1_incsp_1 X5 (esk26_5 X1 X2 X3 X4 X5) X6 -> False)
  -> (forall X4 X5 X2 X3 X1, ((k1_funct_1 X3 (esk25_5 X3 X2 X4 X5 X1)) = (esk26_5 X3 X2 X4 X5 X1) -> False) -> (epred1_5 X1 X4 X2 X3 X5 -> False) -> (r1_incsp_1 X1 X2 (esk27_5 X3 X2 X4 X5 X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X3) (u1_incsp_1 X1) -> r1_incsp_1 X1 (esk24_5 X3 X2 X4 X5 X1) X5 -> r2_hidden (esk24_5 X3 X2 X4 X5 X1) (k1_relset_1 (u1_incsp_1 X1) X3) -> False)
  -> (forall X3 X4 X2 X1 X5, ((k1_funct_1 X1 (esk25_5 X1 X2 X3 X4 X5)) = (esk26_5 X1 X2 X3 X4 X5) -> False) -> (epred1_5 X5 X3 X2 X1 X4 -> False) -> (m1_subset_1 (esk27_5 X1 X2 X3 X4 X5) (u2_incsp_1 X5) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> r1_incsp_1 X5 (esk24_5 X1 X2 X3 X4 X5) X4 -> r2_hidden (esk24_5 X1 X2 X3 X4 X5) (k1_relset_1 (u1_incsp_1 X5) X1) -> False)
  -> (forall X4 X5 X3 X1 X2, ((k1_funct_1 X2 (esk25_5 X2 X3 X4 X5 X1)) = (esk26_5 X2 X3 X4 X5 X1) -> False) -> (epred1_5 X1 X4 X3 X2 X5 -> False) -> (r1_incsp_1 X1 (esk24_5 X2 X3 X4 X5 X1) X5 -> False) -> (r2_hidden (esk24_5 X2 X3 X4 X5 X1) (k1_relset_1 (u1_incsp_1 X1) X2) -> False) -> (r1_incsp_1 X1 (esk26_5 X2 X3 X4 X5 X1) (esk27_5 X2 X3 X4 X5 X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> False)
  -> (forall X4 X5 X3 X1 X2, ((k1_funct_1 X2 (esk25_5 X2 X3 X4 X5 X1)) = (esk26_5 X2 X3 X4 X5 X1) -> False) -> (epred1_5 X1 X4 X3 X2 X5 -> False) -> (r1_incsp_1 X1 (esk24_5 X2 X3 X4 X5 X1) X5 -> False) -> (r2_hidden (esk24_5 X2 X3 X4 X5 X1) (k1_relset_1 (u1_incsp_1 X1) X2) -> False) -> (r1_incsp_1 X1 (esk25_5 X2 X3 X4 X5 X1) (esk27_5 X2 X3 X4 X5 X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> False)
  -> (forall X2 X5 X4 X1 X3, ((k1_funct_1 X3 (esk25_5 X3 X2 X4 X5 X1)) = (esk26_5 X3 X2 X4 X5 X1) -> False) -> (epred1_5 X1 X4 X2 X3 X5 -> False) -> (r1_incsp_1 X1 X2 (esk27_5 X3 X2 X4 X5 X1) -> False) -> (r1_incsp_1 X1 (esk24_5 X3 X2 X4 X5 X1) X5 -> False) -> (r2_hidden (esk24_5 X3 X2 X4 X5 X1) (k1_relset_1 (u1_incsp_1 X1) X3) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X3) (u1_incsp_1 X1) -> False)
  -> (forall X2 X4 X3 X5 X1, ((k1_funct_1 X1 (esk25_5 X1 X2 X3 X4 X5)) = (esk26_5 X1 X2 X3 X4 X5) -> False) -> (epred1_5 X5 X3 X2 X1 X4 -> False) -> (r1_incsp_1 X5 (esk24_5 X1 X2 X3 X4 X5) X4 -> False) -> (m1_subset_1 (esk27_5 X1 X2 X3 X4 X5) (u2_incsp_1 X5) -> False) -> (r2_hidden (esk24_5 X1 X2 X3 X4 X5) (k1_relset_1 (u1_incsp_1 X5) X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> False)
  -> (forall X4 X5 X3 X1 X2, ((k1_funct_1 X2 (esk25_5 X2 X3 X4 X5 X1)) = (esk26_5 X2 X3 X4 X5 X1) -> False) -> (epred1_5 X1 X4 X3 X2 X5 -> False) -> (m1_subset_1 (esk24_5 X2 X3 X4 X5 X1) (u1_incsp_1 X1) -> False) -> (r1_incsp_1 X1 (esk26_5 X2 X3 X4 X5 X1) (esk27_5 X2 X3 X4 X5 X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> False)
  -> (forall X4 X5 X3 X1 X2, ((k1_funct_1 X2 (esk25_5 X2 X3 X4 X5 X1)) = (esk26_5 X2 X3 X4 X5 X1) -> False) -> (epred1_5 X1 X4 X3 X2 X5 -> False) -> (m1_subset_1 (esk24_5 X2 X3 X4 X5 X1) (u1_incsp_1 X1) -> False) -> (r1_incsp_1 X1 (esk25_5 X2 X3 X4 X5 X1) (esk27_5 X2 X3 X4 X5 X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> False)
  -> (forall X4 X5 X3 X2 X1, (epred1_5 X1 X4 X3 X2 X5 -> False) -> (r1_incsp_1 X1 (esk26_5 X2 X3 X4 X5 X1) X4 -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> r1_incsp_1 X1 (esk24_5 X2 X3 X4 X5 X1) X5 -> r2_hidden (esk24_5 X2 X3 X4 X5 X1) (k1_relset_1 (u1_incsp_1 X1) X2) -> False)
  -> (forall X4 X5 X3 X2 X1, (epred1_5 X1 X4 X3 X2 X5 -> False) -> (r1_incsp_1 X1 (esk25_5 X2 X3 X4 X5 X1) X5 -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> r1_incsp_1 X1 (esk24_5 X2 X3 X4 X5 X1) X5 -> r2_hidden (esk24_5 X2 X3 X4 X5 X1) (k1_relset_1 (u1_incsp_1 X1) X2) -> False)
  -> (forall X3 X4 X2 X1 X5, (epred1_5 X5 X3 X2 X1 X4 -> False) -> (m1_subset_1 (esk26_5 X1 X2 X3 X4 X5) (u1_incsp_1 X5) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> r1_incsp_1 X5 (esk24_5 X1 X2 X3 X4 X5) X4 -> r2_hidden (esk24_5 X1 X2 X3 X4 X5) (k1_relset_1 (u1_incsp_1 X5) X1) -> False)
  -> (forall X3 X4 X2 X1 X5, (epred1_5 X5 X3 X2 X1 X4 -> False) -> (m1_subset_1 (esk25_5 X1 X2 X3 X4 X5) (u1_incsp_1 X5) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> r1_incsp_1 X5 (esk24_5 X1 X2 X3 X4 X5) X4 -> r2_hidden (esk24_5 X1 X2 X3 X4 X5) (k1_relset_1 (u1_incsp_1 X5) X1) -> False)
  -> (forall X2 X5 X4 X1 X3, ((k1_funct_1 X3 (esk25_5 X3 X2 X4 X5 X1)) = (esk26_5 X3 X2 X4 X5 X1) -> False) -> (epred1_5 X1 X4 X2 X3 X5 -> False) -> (r1_incsp_1 X1 X2 (esk27_5 X3 X2 X4 X5 X1) -> False) -> (m1_subset_1 (esk24_5 X3 X2 X4 X5 X1) (u1_incsp_1 X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X3) (u1_incsp_1 X1) -> False)
  -> (forall X2 X4 X3 X5 X1, ((k1_funct_1 X1 (esk25_5 X1 X2 X3 X4 X5)) = (esk26_5 X1 X2 X3 X4 X5) -> False) -> (epred1_5 X5 X3 X2 X1 X4 -> False) -> (m1_subset_1 (esk24_5 X1 X2 X3 X4 X5) (u1_incsp_1 X5) -> False) -> (m1_subset_1 (esk27_5 X1 X2 X3 X4 X5) (u2_incsp_1 X5) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> False)
  -> (forall X3 X5 X4 X1 X2, (epred1_5 X1 X4 X3 X2 X5 -> False) -> (r1_incsp_1 X1 (esk24_5 X2 X3 X4 X5 X1) X5 -> False) -> (r1_incsp_1 X1 (esk26_5 X2 X3 X4 X5 X1) X4 -> False) -> (r2_hidden (esk24_5 X2 X3 X4 X5 X1) (k1_relset_1 (u1_incsp_1 X1) X2) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> False)
  -> (forall X3 X5 X4 X1 X2, (epred1_5 X1 X4 X3 X2 X5 -> False) -> (r1_incsp_1 X1 (esk24_5 X2 X3 X4 X5 X1) X5 -> False) -> (r1_incsp_1 X1 (esk25_5 X2 X3 X4 X5 X1) X5 -> False) -> (r2_hidden (esk24_5 X2 X3 X4 X5 X1) (k1_relset_1 (u1_incsp_1 X1) X2) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> False)
  -> (forall X2 X4 X3 X5 X1, (epred1_5 X5 X3 X2 X1 X4 -> False) -> (r1_incsp_1 X5 (esk24_5 X1 X2 X3 X4 X5) X4 -> False) -> (m1_subset_1 (esk26_5 X1 X2 X3 X4 X5) (u1_incsp_1 X5) -> False) -> (r2_hidden (esk24_5 X1 X2 X3 X4 X5) (k1_relset_1 (u1_incsp_1 X5) X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> False)
  -> (forall X2 X4 X3 X5 X1, (epred1_5 X5 X3 X2 X1 X4 -> False) -> (r1_incsp_1 X5 (esk24_5 X1 X2 X3 X4 X5) X4 -> False) -> (m1_subset_1 (esk25_5 X1 X2 X3 X4 X5) (u1_incsp_1 X5) -> False) -> (r2_hidden (esk24_5 X1 X2 X3 X4 X5) (k1_relset_1 (u1_incsp_1 X5) X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> False)
  -> (forall X3 X5 X4 X1 X2, (epred1_5 X1 X4 X3 X2 X5 -> False) -> (r1_incsp_1 X1 (esk26_5 X2 X3 X4 X5 X1) X4 -> False) -> (m1_subset_1 (esk24_5 X2 X3 X4 X5 X1) (u1_incsp_1 X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> False)
  -> (forall X3 X5 X4 X1 X2, (epred1_5 X1 X4 X3 X2 X5 -> False) -> (r1_incsp_1 X1 (esk25_5 X2 X3 X4 X5 X1) X5 -> False) -> (m1_subset_1 (esk24_5 X2 X3 X4 X5 X1) (u1_incsp_1 X1) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> False)
  -> (forall X2 X4 X3 X5 X1, (epred1_5 X5 X3 X2 X1 X4 -> False) -> (m1_subset_1 (esk24_5 X1 X2 X3 X4 X5) (u1_incsp_1 X5) -> False) -> (m1_subset_1 (esk26_5 X1 X2 X3 X4 X5) (u1_incsp_1 X5) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> False)
  -> (forall X2 X4 X3 X5 X1, (epred1_5 X5 X3 X2 X1 X4 -> False) -> (m1_subset_1 (esk24_5 X1 X2 X3 X4 X5) (u1_incsp_1 X5) -> False) -> (m1_subset_1 (esk25_5 X1 X2 X3 X4 X5) (u1_incsp_1 X5) -> False) -> r1_tarski (k1_relset_1 (u1_incsp_1 X5) X1) (u1_incsp_1 X5) -> False)
  -> (forall X3 X2 X4 X5 X6 X1, ((k9_xtuple_0 (k3_relat_1 (k1_projred1 X1 X2 X3 X4) (k1_projred1 X1 X3 X5 X6))) = (k1_relset_1 (u1_incsp_1 X1) (k1_projred1 X1 X2 X3 X4)) -> False) -> (r1_incsp_1 X1 X6 X5 -> False) -> (r1_incsp_1 X1 X6 X3 -> False) -> (r1_incsp_1 X1 X4 X3 -> False) -> (r1_incsp_1 X1 X4 X2 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> v5_incproj X1 -> v9_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X6 (u1_incsp_1 X1) -> m1_subset_1 X5 (u2_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X3 X2 X4 X5 X6 X1, ((k10_xtuple_0 (k3_relat_1 (k1_projred1 X1 X2 X3 X4) (k1_projred1 X1 X3 X5 X6))) = (k10_xtuple_0 (k1_projred1 X1 X3 X5 X6)) -> False) -> (r1_incsp_1 X1 X6 X5 -> False) -> (r1_incsp_1 X1 X6 X3 -> False) -> (r1_incsp_1 X1 X4 X3 -> False) -> (r1_incsp_1 X1 X4 X2 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> v5_incproj X1 -> v9_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X6 (u1_incsp_1 X1) -> m1_subset_1 X5 (u2_incsp_1 X1) -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X2 X4 X5 X3 X1, (X4 = (k1_projred1 X1 X5 X2 X3) -> False) -> (r1_incsp_1 X1 X3 X5 -> False) -> (r1_incsp_1 X1 X3 X2 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> v5_incproj X1 -> v9_incproj X1 -> l1_incsp_1 X1 -> v1_funct_1 X4 -> m1_subset_1 X5 (u2_incsp_1 X1) -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> epred1_5 X1 X2 X3 X4 X5 -> m1_subset_1 X4 (k1_zfmisc_1 (k2_zfmisc_1 (u1_incsp_1 X1) (u1_incsp_1 X1))) -> False)
  -> (forall X2 X8 X7 X3 X1 X4 X6 X5, ((k1_funct_1 X6 X4) = X5 -> False) -> r1_incsp_1 X2 X5 X8 -> r1_incsp_1 X2 X5 X1 -> r1_incsp_1 X2 X4 X7 -> r1_incsp_1 X2 X4 X1 -> r1_incsp_1 X2 X3 X1 -> m1_subset_1 X5 (u1_incsp_1 X2) -> m1_subset_1 X4 (u1_incsp_1 X2) -> m1_subset_1 X1 (u2_incsp_1 X2) -> epred1_5 X2 X8 X3 X6 X7 -> False)
  -> (forall X3 X5 X6 X1 X4 X2, (r2_hidden X2 (k1_relset_1 (u1_incsp_1 X1) X4) -> False) -> r1_incsp_1 X1 X2 X3 -> m1_subset_1 X2 (u1_incsp_1 X1) -> epred1_5 X1 X5 X6 X4 X3 -> False)
  -> (forall X6 X5 X3 X4 X1 X2, (r1_incsp_1 X2 X1 X4 -> False) -> m1_subset_1 X1 (u1_incsp_1 X2) -> epred1_5 X2 X5 X6 X3 X4 -> r2_hidden X1 (k1_relset_1 (u1_incsp_1 X2) X3) -> False)
  -> (forall X3 X1 X4 X5 X2, (r1_incsp_1 X2 X5 X4 -> False) -> (r1_incsp_1 X2 X5 X3 -> False) -> (epred1_5 X2 X4 X5 X1 X3 -> False) -> X1 = (k1_projred1 X2 X3 X4 X5) -> v6_incsp_1 X2 -> v1_incproj X2 -> v2_incproj X2 -> v3_incproj X2 -> v4_incproj X2 -> v5_incproj X2 -> v9_incproj X2 -> l1_incsp_1 X2 -> v1_funct_1 X1 -> m1_subset_1 X5 (u1_incsp_1 X2) -> m1_subset_1 X4 (u2_incsp_1 X2) -> m1_subset_1 X3 (u2_incsp_1 X2) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (u1_incsp_1 X2) (u1_incsp_1 X2))) -> False)
  -> (forall X3 X5 X4 X2 X1, (r1_tarski (k1_relset_1 (u1_incsp_1 X1) X2) (u1_incsp_1 X1) -> False) -> epred1_5 X1 X3 X4 X2 X5 -> False)
  -> (forall X3 X4 X2 X1, ((k1_relset_1 (u1_incsp_1 X1) (k1_projred1 X1 X3 X4 X2)) = (k1_projred2 X1 X3) -> False) -> (r1_incsp_1 X1 X2 X4 -> False) -> (r1_incsp_1 X1 X2 X3 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> v5_incproj X1 -> v9_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X4 (u2_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X2 X3 X4 X1, (m1_subset_1 (k1_projred1 X1 X2 X3 X4) (k1_zfmisc_1 (k2_zfmisc_1 (u1_incsp_1 X1) (u1_incsp_1 X1))) -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> v5_incproj X1 -> v9_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X2 X3 X4 X1, (v1_funct_1 (k1_projred1 X1 X2 X3 X4) -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> v5_incproj X1 -> v9_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X4 (u1_incsp_1 X1) -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X2 X3 X1, (r1_incsp_1 X1 (esk14_3 X2 X1 X3) X3 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> r2_hidden X2 (a_2_0_projred2 X1 X3) -> False)
  -> (forall X4 X2 X3 X1, (v1_relat_1 (k9_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 (k2_zfmisc_1 X2 X3) X4)) -> False)
  -> (forall X2 X4 X3 X1, (v1_relat_1 (k10_xtuple_0 X1) -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 (k2_zfmisc_1 X3 X4))) -> False)
  -> (forall X2 X3 X1, (r1_incsp_1 X1 (esk9_3 X1 X2 X3) X2 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> v5_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X2 X3 X1, (r1_incsp_1 X1 (esk9_3 X1 X2 X3) X3 -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> v5_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X1 X2, (v5_incproj X2 -> False) -> v6_incsp_1 X2 -> v1_incproj X2 -> v2_incproj X2 -> v3_incproj X2 -> v4_incproj X2 -> l1_incsp_1 X2 -> m1_subset_1 X1 (u1_incsp_1 X2) -> r1_incsp_1 X2 X1 (esk10_1 X2) -> r1_incsp_1 X2 X1 (esk11_1 X2) -> False)
  -> (forall X1 X3 X2, (m1_subset_1 (esk14_3 X1 X2 X3) (u1_incsp_1 X2) -> False) -> v6_incsp_1 X2 -> v1_incproj X2 -> v2_incproj X2 -> v3_incproj X2 -> v4_incproj X2 -> l1_incsp_1 X2 -> m1_subset_1 X3 (u2_incsp_1 X2) -> r2_hidden X1 (a_2_0_projred2 X2 X3) -> False)
  -> (forall X2 X3 X1, (m1_subset_1 (esk9_3 X1 X2 X3) (u1_incsp_1 X1) -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> v5_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u2_incsp_1 X1) -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X3 X2 X1, (r1_incsp_1 X1 X2 (esk6_3 X1 X2 X3) -> False) -> v6_incsp_1 X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X3 X2 X1, (r1_incsp_1 X1 X2 (esk6_3 X1 X3 X2) -> False) -> v6_incsp_1 X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X1 X2 X4 X3, (r2_hidden X3 (a_2_0_projred2 X2 X4) -> False) -> X1 = X3 -> v6_incsp_1 X2 -> v1_incproj X2 -> v2_incproj X2 -> v3_incproj X2 -> v4_incproj X2 -> l1_incsp_1 X2 -> r1_incsp_1 X2 X1 X4 -> m1_subset_1 X4 (u2_incsp_1 X2) -> m1_subset_1 X1 (u1_incsp_1 X2) -> False)
  -> (forall X1 X2, (v6_incsp_1 X2 -> False) -> l1_incsp_1 X2 -> m1_subset_1 X1 (u2_incsp_1 X2) -> r1_incsp_1 X2 (esk7_1 X2) X1 -> r1_incsp_1 X2 (esk8_1 X2) X1 -> False)
  -> (forall X3 X2 X1, (m1_subset_1 (esk6_3 X1 X2 X3) (u2_incsp_1 X1) -> False) -> v6_incsp_1 X1 -> l1_incsp_1 X1 -> m1_subset_1 X3 (u1_incsp_1 X1) -> m1_subset_1 X2 (u1_incsp_1 X1) -> False)
  -> (forall X1 X3 X2, ((esk14_3 X1 X2 X3) = X1 -> False) -> v6_incsp_1 X2 -> v1_incproj X2 -> v2_incproj X2 -> v3_incproj X2 -> v4_incproj X2 -> l1_incsp_1 X2 -> m1_subset_1 X3 (u2_incsp_1 X2) -> r2_hidden X1 (a_2_0_projred2 X2 X3) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> (k1_funct_1 X1 (esk21_2 X1 X2)) = (k1_funct_1 X2 (esk21_2 X1 X2)) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X3 X2, ((k1_funct_1 (k3_relat_1 X1 X2) X3) = (k1_funct_1 X2 (k1_funct_1 X1 X3)) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> r2_hidden X3 (k9_xtuple_0 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_projred2 X1 X2) (k1_zfmisc_1 (u1_incsp_1 X1)) -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X3 X1 X2, (v5_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X3 X2)) -> False)
  -> (forall X3 X1 X2, (v4_relat_1 X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X1 X3)) -> False)
  -> (forall X1 X3 X2, (v1_xboole_0 X2 -> False) -> v1_xboole_0 X1 -> m1_subset_1 X2 (k1_zfmisc_1 (k2_zfmisc_1 X3 X1)) -> False)
  -> (forall X3 X2 X1, (v1_relat_1 X1 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 (k2_zfmisc_1 X2 X3)) -> False)
  -> (forall X1 X3 X2, r2_hidden X3 X2 -> r2_hidden X1 X2 -> r2_hidden X1 (esk22_2 X3 X2) -> False)
  -> (forall X2 X1, ((k1_projred2 X1 X2) = (a_2_0_projred2 X1 X2) -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> m1_subset_1 X2 (u2_incsp_1 X1) -> False)
  -> (forall X1 X2, (X1 = X2 -> False) -> (r2_hidden (esk21_2 X1 X2) (k9_xtuple_0 X1) -> False) -> (k9_xtuple_0 X1) = (k9_xtuple_0 X2) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 (k1_relset_1 X2 X1) (k1_zfmisc_1 X2) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X3 X1, (v1_relat_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X2 X3 X1, (v1_funct_1 (k1_funct_1 X1 X2) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v4_funct_1 X3 -> v5_relat_1 X1 X3 -> False)
  -> (forall X1, (v5_incproj X1 -> False) -> (m1_subset_1 (esk11_1 X1) (u2_incsp_1 X1) -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v5_incproj X1 -> False) -> (m1_subset_1 (esk10_1 X1) (u2_incsp_1 X1) -> False) -> v6_incsp_1 X1 -> v1_incproj X1 -> v2_incproj X1 -> v3_incproj X1 -> v4_incproj X1 -> l1_incsp_1 X1 -> False)
  -> (forall X1 X2, (v2_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> v2_funct_1 X2 -> v2_funct_1 X1 -> False)
  -> (forall X2 X1 X3, (m1_subset_1 X1 X3 -> False) -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X2 X1, (r2_hidden (esk22_2 X1 X2) X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X2 X1 X3, v1_xboole_0 X3 -> r2_hidden X1 X2 -> m1_subset_1 X2 (k1_zfmisc_1 X3) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 (k3_relat_1 X1 X2) -> False) -> v1_funct_1 X2 -> v1_funct_1 X1 -> v1_relat_1 X2 -> v1_relat_1 X1 -> False)
  -> (forall X1 X2, (v1_funct_1 X2 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, ((k1_relset_1 X2 X1) = (k9_xtuple_0 X1) -> False) -> v1_relat_1 X1 -> v4_relat_1 X1 X2 -> False)
  -> (forall X2 X1, (r1_tarski X1 X2 -> False) -> m1_subset_1 X1 (k1_zfmisc_1 X2) -> False)
  -> (forall X2 X1, r2_hidden X2 X1 -> r2_hidden X1 X2 -> False)
  -> (forall X1 X2, (v4_funct_1 X2 -> False) -> v4_funct_1 X1 -> m1_subset_1 X2 (k1_zfmisc_1 X1) -> False)
  -> (forall X2 X1, (m1_subset_1 X1 (k1_zfmisc_1 X2) -> False) -> r1_tarski X1 X2 -> False)
  -> (forall X1 X2, (v1_xboole_0 X2 -> False) -> (r2_hidden X1 X2 -> False) -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v6_incsp_1 X1 -> False) -> (m1_subset_1 (esk8_1 X1) (u1_incsp_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X1, (v6_incsp_1 X1 -> False) -> (m1_subset_1 (esk7_1 X1) (u1_incsp_1 X1) -> False) -> l1_incsp_1 X1 -> False)
  -> (forall X2 X1, (m1_subset_1 X1 X2 -> False) -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k9_xtuple_0 X1) -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 (k10_xtuple_0 X1) -> False)
  -> (forall X2 X1, (v1_relat_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X2 X1, (v1_funct_1 X1 -> False) -> v4_funct_1 X2 -> m1_subset_1 X1 X2 -> False)
  -> (forall X1, (v1_zfmisc_1 (k10_xtuple_0 X1) -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v3_funct_1 X1 -> False)
  -> (forall X1 X2, v1_xboole_0 X2 -> r2_hidden X1 X2 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_funct_1 X1 -> v1_relat_1 X1 -> v1_zfmisc_1 X1 -> False)
  -> (forall X1, (v3_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, (v2_funct_1 X1 -> False) -> v1_xboole_0 X1 -> v1_funct_1 X1 -> v1_relat_1 X1 -> False)
  -> (forall X1, l1_incsp_1 X1 -> v1_xboole_0 (u2_incsp_1 X1) -> False)
  -> (forall X1, l1_incsp_1 X1 -> v1_xboole_0 (u1_incsp_1 X1) -> False)
  -> (forall X2 X1, (X1 = X2 -> False) -> v1_xboole_0 X2 -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v4_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (v1_funct_1 X1 -> False) -> v1_xboole_0 X1 -> False)
  -> (forall X1, (X1 = k1_xboole_0 -> False) -> v1_xboole_0 X1 -> False)
  -> ((k3_relat_1 (k1_projred1 esk1_0 esk3_0 esk5_0 esk2_0) (k1_projred1 esk1_0 esk5_0 esk4_0 esk2_0)) = (k1_projred1 esk1_0 esk3_0 esk4_0 esk2_0) -> False)
  -> (r1_incsp_1 esk1_0 esk2_0 esk5_0 -> False)
  -> (r1_incsp_1 esk1_0 esk2_0 esk4_0 -> False)
  -> (r1_incsp_1 esk1_0 esk2_0 esk3_0 -> False)
  -> (v3_funct_1 esk18_0 -> False)
  -> (v1_xboole_0 esk20_0 -> False)
  -> (forall X2 X1, (m1_subset_1 (esk16_2 X1 X2) (k1_zfmisc_1 (k2_zfmisc_1 X1 X2)) -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk19_2 X1 X2) X2 -> False) -> False)
  -> (forall X2 X1, (v5_relat_1 (esk16_2 X1 X2) X2 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk19_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v4_relat_1 (esk16_2 X1 X2) X1 -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_relat_1 (k3_relat_1 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_funct_1 (esk19_2 X1 X2) -> False) -> False)
  -> (forall X1 X2, (v1_xboole_0 (esk16_2 X1 X2) -> False) -> False)
  -> (forall X1, (m1_subset_1 (esk13_1 X1) X1 -> False) -> False)
  -> ((m1_subset_1 esk5_0 (u2_incsp_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk4_0 (u2_incsp_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk3_0 (u2_incsp_1 esk1_0) -> False) -> False)
  -> ((m1_subset_1 esk2_0 (u1_incsp_1 esk1_0) -> False) -> False)
  -> (forall X1, (r1_tarski X1 X1 -> False) -> False)
  -> ((v4_funct_1 esk20_0 -> False) -> False)
  -> ((v2_funct_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk18_0 -> False) -> False)
  -> ((v1_relat_1 esk17_0 -> False) -> False)
  -> ((v1_relat_1 esk15_0 -> False) -> False)
  -> ((v1_funct_1 esk18_0 -> False) -> False)
  -> ((v1_funct_1 esk17_0 -> False) -> False)
  -> ((v1_funct_1 esk15_0 -> False) -> False)
  -> ((l1_incsp_1 esk12_0 -> False) -> False)
  -> ((l1_incsp_1 esk1_0 -> False) -> False)
  -> ((v9_incproj esk1_0 -> False) -> False)
  -> ((v5_incproj esk1_0 -> False) -> False)
  -> ((v4_incproj esk1_0 -> False) -> False)
  -> ((v3_incproj esk1_0 -> False) -> False)
  -> ((v2_incproj esk1_0 -> False) -> False)
  -> ((v1_incproj esk1_0 -> False) -> False)
  -> ((v6_incsp_1 esk1_0 -> False) -> False)
  -> False.
Admitted.
