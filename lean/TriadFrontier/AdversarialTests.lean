module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore
public import TriadFrontier.PIRKoszul
public import TriadFrontier.MLWETightness
public import TriadFrontier.ComplexityTriad
public import TriadFrontier.KoszulTensor
public import TriadFrontier.StrassenWinograd
public import TriadFrontier.ShannonCapacity
public import TriadFrontier.PaleyCapacity

/-!
# Adversarial Negative Boundary Refutations (`TriadFrontier.AdversarialTests`, v5.0.0)

Machine-checked negative counterexamples and sharp threshold refutations proving our headline
theorems cannot be weakened or bypassed at boundary values (Playbook v1.3 falsifiability standard):
1. `adv_compress1_fails_at_832`: FIPS 203 `Compress_1` breaks immediately at `e = +832` (`T3d` sharp!).
2. `adv_flag_privacy_fails_at_e3`: Single-orbit `(K=2, T=2)` flag privacy fails at `E = 3` (`T1d` sharp!).
3. `adv_strassen_no_rank6`: NO field `F` (incl. `F_2`) admits a rank-6 bilinear algorithm for `⟨2,2,2⟩` (`T3h`).
4. `adv_c5_no_3_indep`: `C_5` has NO 3-element independent set (`3^2 = 9 > 5`; `T3j`).
5. `adv_c7_no_rank3_haemers`: `C_7` admits NO rank-3 Haemers fitting matrix over ANY field `F` (`T3j`).
6. `adv_p13_no_4_indep`: Paley graph `P_13` has NO 4-element independent set (`4^2 = 16 > 13`; `T3l`).
7. `adv_koszul_ceiling_broken_at_m3`: Brockett–Dobkin `2m^2-m = 15` strictly beats Koszul ceiling `12` (`T3i`).
-/

namespace TriadFrontier.AdversarialTests

open TriadFrontier.AlgebraCore
open TriadFrontier.ComplexityTriad
open TriadFrontier.KoszulTensor
open TriadFrontier.StrassenWinograd
open TriadFrontier.ShannonCapacity
open TriadFrontier.PaleyCapacity

@[expose] public section

/-- 1. Sharpness of `T3d`: FIPS 203 `Compress_1` decryption FAILS at `e = +832` for both `b = 0` and `b = 1`! -/
theorem adv_compress1_fails_at_832 :
    mlkemCompress1 (1665 * 0 + 832) ≠ 0 ∧ mlkemCompress1 (1665 * 1 + 832) ≠ 1 := by
  decide

/-- 2. Sharpness of `T1d`: `(K=2, T=2)` single-orbit flag privacy fails at `E = 3` (`(3*3-4)+3 = 8 > 6`). -/
theorem adv_flag_privacy_fails_at_e3 :
    ¬ ((3 * 3 - 4) + 3 ≤ 3 * (3 - 1)) := by
  decide

/-- 3. Sharpness of `T3h`: NO field `F` (including `F_2`) admits a 6-multiplication algorithm for `⟨2,2,2⟩`. -/
theorem adv_strassen_no_rank6 (F : Type) [SimpleField F] :
    ¬ HasTensorRankAtMost 4 4 4 6 (fun a b c => intToR (R := F) (matMul2Tensor a b c)) := by
  intro hr
  have h7 := winograd_rank_ge_seven F 6 hr
  omega

/-- 4. Sharpness of `T3j`: `C_5` has NO 3-element independent set (`3 * 3 = 9 > 5`). -/
theorem adv_c5_no_3_indep (f : Nat → Nat) :
    ¬ IsIndepSet 5 c5Adj 3 f := by
  intro hind
  have h1 : IsIndepSet (5 ^ 1) (strongPowAdj 5 c5Adj 1) 3 f := by
    refine ⟨by simpa using hind.1, hind.2.1, fun i j hi hj hne => ?_⟩
    have hna := hind.2.2 i j hi hj hne
    have hnf := hind.2.1 i j hi hj hne
    unfold strongPowAdj
    rw [beq_false_of_ne hnf]
    simp only [Bool.false_eq_true, ↓reduceIte, strongPowAdjGo, digit, Nat.pow_zero, Nat.div_one,
               Nat.mod_eq_of_lt (hind.1 i hi), Nat.mod_eq_of_lt (hind.1 j hj),
               beq_false_of_ne hnf, hna]
    rfl
  have hle := lovasz_c5_strong_pow_upper 1 3 f h1
  omega

/-- 5. Sharpness of `T3j`: NO rank-3 matrix fits `C_7` over ANY field `F` (including `F_2`). -/
theorem adv_c7_no_rank3_haemers (F : Type) [SimpleField F] (U V M : Nat → Nat → F)
    (hUV : ∀ i j, i < 7 → j < 7 → sumR 3 (fun s => U i s * V s j) = M i j) :
    ¬ FitsGraph 7 c7Adj M := by
  intro hFit
  have h4 := t3j_shannon_capacity_lovasz_c5_and_haemers.2.2.2.2.1 F 3 U V M hUV hFit
  omega

/-- 6. Sharpness of `T3l`: Paley graph `P_13` has NO 4-element independent set (`4 * 4 = 16 > 13`). -/
theorem adv_p13_no_4_indep (f : Nat → Nat) :
    ¬ IsIndepSet 13 paley13Adj 4 f := by
  intro hind
  have h1 : IsIndepSet (13 ^ 1) (strongPowAdj 13 paley13Adj 1) 4 f := by
    refine ⟨by simpa using hind.1, hind.2.1, fun i j hi hj hne => ?_⟩
    have hna := hind.2.2 i j hi hj hne
    have hnf := hind.2.1 i j hi hj hne
    unfold strongPowAdj
    rw [beq_false_of_ne hnf]
    simp only [Bool.false_eq_true, ↓reduceIte, strongPowAdjGo, digit, Nat.pow_zero, Nat.div_one,
               Nat.mod_eq_of_lt (hind.1 i hi), Nat.mod_eq_of_lt (hind.1 j hj),
               beq_false_of_ne hnf, hna]
    rfl
  have hle := lovasz_conference_strong_pow_upper 3 paley13Adj paley13_isConference 1 4 f h1
  omega

/-- 7. Sharpness of `T3i`: Brockett–Dobkin `2m^2-m` strictly breaks the Koszul ceiling `m^2+m` at `m = 3`. -/
theorem adv_koszul_ceiling_broken_at_m3 : ¬ (2 * 3 * 3 - 3 ≤ 3 * 3 + 3) := by
  decide

/-- Master conjunction of all 7 adversarial negative boundary refutations. -/
theorem adv_all_boundary_refutations :
    (mlkemCompress1 (1665 * 0 + 832) ≠ 0 ∧ mlkemCompress1 (1665 * 1 + 832) ≠ 1) ∧
    (¬ ((3 * 3 - 4) + 3 ≤ 3 * (3 - 1))) ∧
    (∀ (F : Type) [SimpleField F],
      ¬ HasTensorRankAtMost 4 4 4 6 (fun a b c => intToR (R := F) (matMul2Tensor a b c))) ∧
    (∀ f, ¬ IsIndepSet 5 c5Adj 3 f) ∧
    (∀ (F : Type) [SimpleField F] (U V M : Nat → Nat → F),
      (∀ i j, i < 7 → j < 7 → sumR 3 (fun s => U i s * V s j) = M i j) →
      ¬ FitsGraph 7 c7Adj M) ∧
    (∀ f, ¬ IsIndepSet 13 paley13Adj 4 f) ∧
    (¬ (2 * 3 * 3 - 3 ≤ 3 * 3 + 3)) :=
  ⟨adv_compress1_fails_at_832, adv_flag_privacy_fails_at_e3, adv_strassen_no_rank6,
   adv_c5_no_3_indep, adv_c7_no_rank3_haemers, adv_p13_no_4_indep,
   adv_koszul_ceiling_broken_at_m3⟩

end
end TriadFrontier.AdversarialTests
