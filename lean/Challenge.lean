module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier

/-!
# Formal Challenge Specification (`T1a`–`T3d`)

Clean exported theorem specification contract for independent 6-kernel verification
(`lean`, `leanchecker`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`,
`con-ron` via `lake comparator --config comparator.json --paranoid`).
All proofs live in `Solution.lean` and `TriadFrontier.*`.
-/

namespace TriadFrontier.Challenge

open TriadFrontier.AlgebraCore
open TriadFrontier.PIRCertificates
open TriadFrontier.PIRKoszul
open TriadFrontier.MLWETightness
open TriadFrontier.ComplexityTriad
open TriadFrontier.KoszulTensor

@[expose] public section

def T1a_KoszulVeroneseRankIdentity : Prop :=
  (∀ (R : Type) [CommRing R] (T r : Nat) (α : R),
    r + 1 < T → dotR T (momentVec α) (shiftedDiffVec α r) = 0) ∧
  (∀ (T Tp K : Nat), 1 ≤ T → 1 ≤ Tp → Tp ≤ T → Tp ≤ K →
    K * chooseNat T Tp = koszulLambda T Tp K + (K - Tp) * chooseNat (T - 1) Tp) ∧
  (3 * koszulLambda 3 1 3 + 3 * koszulLambda 3 2 3 + 1 * koszulLambda 3 3 3 = 42 ∧
   60 * 7 > 4 * (60 + 42) ∧ 10 * (60 + 42) = 17 * 60)

def T1b_UniversalKoszulDominationOverLFSR : Prop :=
  (∀ E K T : Nat, koszulDen E K T = koszulDen E T K) ∧
  (∀ E K T : Nat,
    ((E : Int) * E * ((E : Int) - 1)) * lfsrDen E K T - ((E : Int) * E) * koszulDen E K T =
    ((K : Int) - 1) * ((T : Int) - 1) * ((E : Int) * E)) ∧
  (∀ E K T : Nat, 1 ≤ E → 2 ≤ K → 2 ≤ T →
    ((E : Int) * E) * koszulDen E K T < ((E : Int) * E * ((E : Int) - 1)) * lfsrDen E K T) ∧
  (∀ P M E K T : Nat, 1 ≤ P → P < M → 2 ≤ E → 2 ≤ K → 2 ≤ T →
    let numK : Int := (P : Int) * E * (E - 1)
    let denK : Int := (P : Int) * E * (E - 1) + ((M : Int) - P) * (((K : Int) + T - 1) * E - (K : Int) * T)
    let numL : Int := (P : Int) * E
    let denL : Int := (P : Int) * E + ((M : Int) - P) * ((K : Int) + T - 1)
    numK * denL - numL * denK = (P : Int) * ((M : Int) - P) * E * ((K : Int) - 1) * ((T : Int) - 1) ∧
    numL * denK < numK * denL) ∧
  (∀ E : Nat, koszulDen E 2 2 = (E : Int) * E + 2 * E - 4) ∧
  (∀ K : Nat, koszulDen (K + 1) K 2 = 2 * (K : Int) * K + K + 1)

def T1c_ByzantineRobustCapacityAndF11Certificate : Prop :=
  (∀ (C Mtot E D sumSub L num den : Nat),
    0 < C →
    Mtot * sumSub = C * E * D →
    C * L * den ≤ sumSub * num →
    Mtot * L * den ≤ E * D * num) ∧
  (∀ K : Nat, 2 ≤ K → K + 1 < 2 * K ∧
    koszulDen (K + 1) K 2 = 2 * ((K : Int) + 1) * (K + 1) - 3 * (K + 1) + 2) ∧
  (checkF11ByzantineRate25 = true ∧ 2 * 21 > 8 * 5)

def T1d_FlagPrivacyAndFeasibilityDimensions : Prop :=
  (∀ E : Nat, 1 ≤ E → ((3 * E - 4) + E ≤ E * (E - 1) ↔ 4 ≤ E)) ∧
  (∀ E K σ μ : Nat, 1 ≤ K → K + 1 ≤ E →
    K * σ + (K + 1) * μ ≤ E * μ + K * σ ∧
    (K * σ + (K + 1) * μ = E * μ + K * σ ↔ (μ = 0 ∨ E = K + 1))) ∧
  (∀ E : Nat, 3 ≤ E → ((4 * E - 6) + 2 * E ≤ E * (E - 1) ↔ 6 ≤ E))

def T1e_UnconditionedShannonIngletonBarrier : Prop :=
  checkAllOrbitMonotone = true ∧
  checkAll330OrbitsSubmod = true ∧
  checkPIREqualities = true ∧
  checkAll1485SingletonIngletons = true ∧
  (4 * hUncond 256 * 8 = 13 * 128 ∧ 8 * 5 > 3 * 13)

def T1f_ProjectiveP3LinearImpossibility : Prop :=
  ∀ (F : Type) [SimpleField F]
    (u1 v1 u2 v2 u3 v3 u4 v4 : Vec4 F)
    (p12 p13 p14 p23 p24 p34 : Vec4 F),
    Nonzero4 p12 → InSpan2 u1 v1 p12 → InSpan2 u2 v2 p12 →
    Nonzero4 p13 → InSpan2 u1 v1 p13 → InSpan2 u3 v3 p13 →
    Nonzero4 p14 → InSpan2 u1 v1 p14 → InSpan2 u4 v4 p14 →
    Nonzero4 p23 → InSpan2 u2 v2 p23 → InSpan2 u3 v3 p23 →
    Nonzero4 p24 → InSpan2 u2 v2 p24 → InSpan2 u4 v4 p24 →
    Nonzero4 p34 → InSpan2 u3 v3 p34 → InSpan2 u4 v4 p34 →
    (∃ w : Vec4 F, Nonzero4 w ∧
      InSpan2 u1 v1 w ∧ InSpan2 u2 v2 w ∧ InSpan2 u3 v3 w ∧ InSpan2 u4 v4 w) ∨
    (∃ a b c : Vec4 F,
      (∀ x, InSpan2 u1 v1 x → InSpan3 a b c x) ∧
      (∀ x, InSpan2 u2 v2 x → InSpan3 a b c x) ∧
      (∀ x, InSpan2 u3 v3 x → InSpan3 a b c x) ∧
      (∀ x, InSpan2 u4 v4 x → InSpan3 a b c x))

def T2a_DeterminantIdealSecretIndependence : Prop :=
  ∀ (R : Type) [CommRing R] (m k : Nat) (q u uInv : R),
    u * uInv = 1 →
    lowerTriDet (m + k) (mlweBasisDiag m q) = rPow q m ∧
    lowerTriDet (m + k + 1) (kannanBasisDiag m q) = rPow q m ∧
    uInv * (u * lowerTriDet (m + k + 1) (kannanBasisDiag m q)) = rPow q m

def T2b_ChenStep9AntiPeriodicDFTCancellation : Prop :=
  (∀ (R : Type) [CommRing R] (D : Nat) (ω : R) (f : Nat → R) (k : Nat),
    rPow ω D = -(1 : R) →
    (∀ x, x < D → f (D + x) = -(f x)) →
    dftCoeff (D + D) ω f (2 * k) = 0) ∧
  (∀ (a b x : Nat),
    let c := 2 * a + 1
    let D := 2 * b + 1
    c * ((x + D) * (x + D)) = c * (x * x) + D * (c * (2 * x + D)) ∧
    (c * (2 * x + D)) % 2 = 1)

def T2c_MLKEMCBDRenyiCliff : Prop :=
  (cbd2Weight (-2) + cbd2Weight (-1) + cbd2Weight 0 + cbd2Weight 1 + cbd2Weight 2 = 16 ∧
   4 * cbd2Weight (-2) + 1 * cbd2Weight (-1) + 0 * cbd2Weight 0 + 1 * cbd2Weight 1 + 4 * cbd2Weight 2 = 16 ∧
   16 * cbd2Weight (-2) + 1 * cbd2Weight (-1) + 0 * cbd2Weight 0 + 1 * cbd2Weight 1 + 16 * cbd2Weight 2 = 40 ∧
   cbd3Weight (-3) + cbd3Weight (-2) + cbd3Weight (-1) + cbd3Weight 0 + cbd3Weight 1 + cbd3Weight 2 + cbd3Weight 3 = 64 ∧
   9 * cbd3Weight (-3) + 4 * cbd3Weight (-2) + 1 * cbd3Weight (-1) + 1 * cbd3Weight 1 + 4 * cbd3Weight 2 + 9 * cbd3Weight 3 = 96 ∧
   81 * cbd3Weight (-3) + 16 * cbd3Weight (-2) + 1 * cbd3Weight (-1) + 1 * cbd3Weight 1 + 16 * cbd3Weight 2 + 81 * cbd3Weight 3 = 384) ∧
  (∀ (F : Type) [SimpleField F] (n k : Nat) (ζ : F),
    rPow ζ n = -(1 : F) →
    rPow ζ (2 * k) ≠ 1 →
    sumR n (fun j => rPow ζ (2 * k * j)) = 0) ∧
  (1289 * 2048 > 4 * (518 * 1024) ∧
   1289 * 2048 * 10 > 49 * (518 * 1024) ∧
   1289 * 1536 * 10 > 37 * (518 * 1024))

def T2d_QGTLShiftedLWEBerryCurvature : Prop :=
  (∀ (N : Nat) (p x : Nat → Int) (e0 c : Int),
    covNum N p x (fun i => (x i - e0) * (x i - e0) - c) =
    covNum N p x (fun i => (x i - e0) * (x i - e0))) ∧
  (∀ (M : Nat) (p : Int → Int),
    (∀ k : Int, p (-k) = p k) →
    let x : Nat → Int := fun i => (i : Int) - (M : Int)
    let pf : Nat → Int := fun i => p (x i)
    covNum (2 * M + 1) pf x (fun i => x i * x i) = 0) ∧
  (let x : Nat → Int := fun i => (i : Int) - 2
   let pf : Nat → Int := fun i => cbd2Weight (x i)
   covNum 5 pf x (fun i => (x i - 1) * (x i - 1)) = -512 ∧
   covNum 5 pf x (fun i => (x i - 1) * (x i - 1)) ≠ 0)

def T3a_AlgebrizationMultilinearExtensionUniqueness : Prop :=
  ∀ (F : Type) [SimpleField F] (n : Nat) (f : (Fin n → Bool) → F),
    IsMultilinear (mle f) ∧
    (∀ b : Fin n → Bool, mle f (fun i => boolToF (b i)) = f b) ∧
    (∀ g : (Fin n → F) → F, IsMultilinear g →
      (∀ b : Fin n → Bool, g (fun i => boolToF (b i)) = f b) →
      ∀ x : Fin n → F, g x = mle f x)

def T3b_LWEToNaturalProofsObstruction : Prop :=
  ∀ (U K A_rand A_prf num den epsNum epsDen : Nat),
    0 < U → 0 < K → 0 < den → 0 < epsDen →
    A_prf = 0 →
    A_rand * den ≥ U * num →
    epsNum * den ≤ num * epsDen →
    (K * A_rand - U * A_prf) * den ≥ K * U * num ∧
    ¬ ((K * A_rand - U * A_prf) * epsDen < K * U * epsNum)

def T3c_KatzTrevisanByzantinePIRToLDC : Prop :=
  ∀ (α M : Type) [DecidableEq α] (N B : Nat)
    (Enc : M → List α) (Dec : List α → M),
    (∀ m, (Enc m).length = N) →
    (∀ m r, r.length = N → hammingDist (Enc m) r ≤ B → Dec r = m) →
    (∀ m1 m2, m1 ≠ m2 → 2 * B + 1 ≤ hammingDist (Enc m1) (Enc m2))

def T3d_MLWESingleServerPIRNoiseCeiling : Prop :=
  (∀ (b e : Int), (b = 0 ∨ b = 1) → -831 ≤ e → e ≤ 831 →
    mlkemCompress1 (1665 * b + e) = b) ∧
  (mlkemCompress1 832 = 1 ∧ mlkemCompress1 (1665 + 832) = 0) ∧
  (∀ (bStep M : Nat), 0 < bStep → 831 / bStep < M → 832 ≤ M * bStep)

def T1g_ZhangYeungReductionAndMFileKoszul : Prop :=
  (∀ (H : Nat → Int) (a b c d : Nat),
    zhangYeungQ H a b c d =
    ingletonQ H c d a b + condI H a c d + condI H a d c + condI H c d a) ∧
  (∀ (H : Nat → Int) (a b c d : Nat),
    0 ≤ ingletonQ H c d a b →
    0 ≤ condI H a c d →
    0 ≤ condI H a d c →
    0 ≤ condI H c d a →
    0 ≤ zhangYeungQ H a b c d) ∧
  (∀ E K T : Nat, koszulMFileDen 2 E K T = koszulDen E K T) ∧
  (∀ M E K T : Nat, koszulMFileDen M E K T = koszulMFileDen M E T K) ∧
  (∀ M K T : Nat, 3 ≤ M → 2 ≤ K → 2 ≤ T →
    K + 1 < K * T ∧ 0 < koszulMFileDen M (K + 1) K T) ∧
  (koszulMFileDen 3 3 2 2 = 16 ∧ 3 * 2 * 8 = 3 * 16)

def T2e_Dyadic256RenyiFloorAndQGTLPSD : Prop :=
  (∀ (N : Nat) (M : Int) (p q w : Nat → Int),
    0 < M →
    (∀ i, i < N → 0 ≤ w i ∧ w i * q i = M) →
    M * (sumInt N p) * (sumInt N p) ≤
    (sumInt N q) * (sumInt N (fun i => p i * p i * w i))) ∧
  (dyadic256Weight (-3) + dyadic256Weight (-2) + dyadic256Weight (-1) + dyadic256Weight 0 +
     dyadic256Weight 1 + dyadic256Weight 2 + dyadic256Weight 3 = 256 ∧
   9 * dyadic256Weight (-3) + 4 * dyadic256Weight (-2) + 1 * dyadic256Weight (-1) +
     1 * dyadic256Weight 1 + 4 * dyadic256Weight 2 + 9 * dyadic256Weight 3 = 256 ∧
   81 * dyadic256Weight (-3) + 16 * dyadic256Weight (-2) + 1 * dyadic256Weight (-1) +
     1 * dyadic256Weight 1 + 16 * dyadic256Weight 2 + 81 * dyadic256Weight 3 = 736 ∧
   21383 * 176 < 378421 * 10 ∧
   3 * 32 < 15 * 8 ∧ 15 * 2 < 1 * 32) ∧
  (∀ (N : Nat) (p a b : Nat → Int),
    (∀ i, i < N → 0 ≤ p i) →
    covNum N p a b * covNum N p a b ≤ varNum N p a * varNum N p b)

def T2f_UniversalTwistedDFTSelectionRule : Prop :=
  ∀ (R : Type) [CommRing R] (m D r k : Nat) (ω ζ : R) (f : Nat → R),
    rPow ω D = ζ →
    (∀ q x, q < m → x < D → f (q * D + x) = rPow ζ (q * r) * f x) →
    sumR m (fun q => rPow ζ (q * (r + k))) = 0 →
    dftCoeff (m * D) ω f k = 0

def T3e_KoszulFlatteningTensorRankBridge : Prop :=
  (∀ (F : Type) [SimpleField F] (r : Nat),
    HasTensorRankAtMost 4 4 4 r (fun a b c => intToR (R := F) (matMul2Tensor a b c)) →
    6 ≤ r) ∧
  (∀ (F : Type) [SimpleField F] (r : Nat),
    HasTensorRankAtMost 3 3 3 r (fun a b c => intToR (R := F) (tensor3Bin a b c)) →
    5 ≤ r)

def T3f_ShannonCountingAndLDCSmoothness : Prop :=
  (∀ (C M : Nat) (eval : Fin C → Fin M),
    C < M → ∃ f : Fin M, ∀ c : Fin C, eval c ≠ f) ∧
  (∀ (N q S τ : Nat) (cnt : Nat → Nat) (isHeavy : Nat → Bool),
    sumNat N cnt ≤ q * S →
    (∀ i, i < N → isHeavy i = true → τ ≤ cnt i) →
    countBool N isHeavy * τ ≤ q * S)

def AllTriadFrontierTheorems : Prop :=
  T1a_KoszulVeroneseRankIdentity ∧
  T1b_UniversalKoszulDominationOverLFSR ∧
  T1c_ByzantineRobustCapacityAndF11Certificate ∧
  T1d_FlagPrivacyAndFeasibilityDimensions ∧
  T1e_UnconditionedShannonIngletonBarrier ∧
  T1f_ProjectiveP3LinearImpossibility ∧
  T1g_ZhangYeungReductionAndMFileKoszul ∧
  T2a_DeterminantIdealSecretIndependence ∧
  T2b_ChenStep9AntiPeriodicDFTCancellation ∧
  T2c_MLKEMCBDRenyiCliff ∧
  T2d_QGTLShiftedLWEBerryCurvature ∧
  T2e_Dyadic256RenyiFloorAndQGTLPSD ∧
  T2f_UniversalTwistedDFTSelectionRule ∧
  T3a_AlgebrizationMultilinearExtensionUniqueness ∧
  T3b_LWEToNaturalProofsObstruction ∧
  T3c_KatzTrevisanByzantinePIRToLDC ∧
  T3d_MLWESingleServerPIRNoiseCeiling ∧
  T3e_KoszulFlatteningTensorRankBridge ∧
  T3f_ShannonCountingAndLDCSmoothness

end
end TriadFrontier.Challenge
