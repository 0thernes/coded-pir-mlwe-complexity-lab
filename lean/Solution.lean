module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import Challenge
public import TriadFrontier

/-!
# Verified Solutions to All 14 Formalized Theorems (`T1a`–`T3d`)

Zero-Mathlib Lean 4.35.0 proofs depending strictly on a subset of
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero `native_decide`, zero custom axioms.
-/

namespace TriadFrontier.Solution

open TriadFrontier.Challenge
open TriadFrontier.PIRKoszul
open TriadFrontier.MLWETightness
open TriadFrontier.ComplexityTriad

public theorem t1a_koszul_veronese_rank_identity : T1a_KoszulVeroneseRankIdentity :=
  PIRKoszul.t1a_koszul_veronese_rank_identity

public theorem t1b_universal_koszul_domination_over_lfsr : T1b_UniversalKoszulDominationOverLFSR :=
  PIRKoszul.t1b_universal_koszul_domination_over_lfsr

public theorem t1c_byzantine_robust_capacity_and_f11_certificate : T1c_ByzantineRobustCapacityAndF11Certificate :=
  PIRKoszul.t1c_byzantine_robust_capacity_and_f11_certificate

public theorem t1d_flag_privacy_and_feasibility_dimensions : T1d_FlagPrivacyAndFeasibilityDimensions :=
  PIRKoszul.t1d_flag_privacy_and_feasibility_dimensions

public theorem t1e_unconditioned_shannon_ingleton_barrier : T1e_UnconditionedShannonIngletonBarrier :=
  PIRKoszul.t1e_unconditioned_shannon_ingleton_barrier

public theorem t1f_projective_p3_linear_impossibility : T1f_ProjectiveP3LinearImpossibility :=
  PIRKoszul.t1f_projective_p3_linear_impossibility

public theorem t2a_determinant_ideal_secret_independence : T2a_DeterminantIdealSecretIndependence :=
  MLWETightness.t2a_determinant_ideal_secret_independence

public theorem t2b_chen_step9_antiperiodic_dft_cancellation : T2b_ChenStep9AntiPeriodicDFTCancellation :=
  MLWETightness.t2b_chen_step9_antiperiodic_dft_cancellation

public theorem t2c_mlkem_cbd_renyi_cliff : T2c_MLKEMCBDRenyiCliff :=
  MLWETightness.t2c_mlkem_cbd_renyi_cliff

public theorem t2d_qgtl_shifted_lwe_berry_curvature : T2d_QGTLShiftedLWEBerryCurvature :=
  MLWETightness.t2d_qgtl_shifted_lwe_berry_curvature

public theorem t3a_algebrization_multilinear_extension_uniqueness : T3a_AlgebrizationMultilinearExtensionUniqueness :=
  ComplexityTriad.t3a_algebrization_multilinear_extension_uniqueness

public theorem t3b_lwe_to_natural_proofs_obstruction : T3b_LWEToNaturalProofsObstruction :=
  ComplexityTriad.t3b_lwe_to_natural_proofs_obstruction

public theorem t3c_katz_trevisan_byzantine_pir_ldc_distance : T3c_KatzTrevisanByzantinePIRToLDC :=
  ComplexityTriad.t3c_katz_trevisan_byzantine_pir_ldc_distance

public theorem t3d_mlwe_single_server_pir_noise_ceiling : T3d_MLWESingleServerPIRNoiseCeiling :=
  ComplexityTriad.t3d_mlwe_single_server_pir_noise_ceiling

public theorem prove_all_triad_theorems : AllTriadFrontierTheorems :=
  ⟨t1a_koszul_veronese_rank_identity,
   t1b_universal_koszul_domination_over_lfsr,
   t1c_byzantine_robust_capacity_and_f11_certificate,
   t1d_flag_privacy_and_feasibility_dimensions,
   t1e_unconditioned_shannon_ingleton_barrier,
   t1f_projective_p3_linear_impossibility,
   t2a_determinant_ideal_secret_independence,
   t2b_chen_step9_antiperiodic_dft_cancellation,
   t2c_mlkem_cbd_renyi_cliff,
   t2d_qgtl_shifted_lwe_berry_curvature,
   t3a_algebrization_multilinear_extension_uniqueness,
   t3b_lwe_to_natural_proofs_obstruction,
   t3c_katz_trevisan_byzantine_pir_ldc_distance,
   t3d_mlwe_single_server_pir_noise_ceiling⟩

end TriadFrontier.Solution
