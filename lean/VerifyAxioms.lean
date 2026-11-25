module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

import Solution

/-!
# Strict Axiom Allowlist Audit (`TriadFrontier` v2.0.0)

Every exported theorem (`T1a`–`T3f`), the master conjunction `prove_all_triad_theorems`,
and the concrete non-vacuity certificate `nonvac_all_hypotheses` (21 audited declarations)
must depend strictly on a subset of `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms TriadFrontier.Solution.t1a_koszul_veronese_rank_identity
#print axioms TriadFrontier.Solution.t1b_universal_koszul_domination_over_lfsr
#print axioms TriadFrontier.Solution.t1c_byzantine_robust_capacity_and_f11_certificate
#print axioms TriadFrontier.Solution.t1d_flag_privacy_and_feasibility_dimensions
#print axioms TriadFrontier.Solution.t1e_unconditioned_shannon_ingleton_barrier
#print axioms TriadFrontier.Solution.t1f_projective_p3_linear_impossibility
#print axioms TriadFrontier.Solution.t1g_zhang_yeung_reduction_and_mfile_koszul
#print axioms TriadFrontier.Solution.t2a_determinant_ideal_secret_independence
#print axioms TriadFrontier.Solution.t2b_chen_step9_antiperiodic_dft_cancellation
#print axioms TriadFrontier.Solution.t2c_mlkem_cbd_renyi_cliff
#print axioms TriadFrontier.Solution.t2d_qgtl_shifted_lwe_berry_curvature
#print axioms TriadFrontier.Solution.t2e_dyadic256_renyi_floor_and_qgtl_psd
#print axioms TriadFrontier.Solution.t2f_universal_twisted_dft_selection_rule
#print axioms TriadFrontier.Solution.t3a_algebrization_multilinear_extension_uniqueness
#print axioms TriadFrontier.Solution.t3b_lwe_to_natural_proofs_obstruction
#print axioms TriadFrontier.Solution.t3c_katz_trevisan_byzantine_pir_ldc_distance
#print axioms TriadFrontier.Solution.t3d_mlwe_single_server_pir_noise_ceiling
#print axioms TriadFrontier.Solution.t3e_koszul_flattening_tensor_rank_bridge
#print axioms TriadFrontier.Solution.t3f_shannon_counting_and_ldc_smoothness
#print axioms TriadFrontier.Solution.prove_all_triad_theorems
#print axioms TriadFrontier.NonVacuity.nonvac_all_hypotheses
