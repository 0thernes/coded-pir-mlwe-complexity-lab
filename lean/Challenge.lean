module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier

/-!
# Formal Challenge Specification (`T1a`–`T3l`, v5.0.0)

Clean exported theorem specification contract for independent 6-kernel verification
(`lean`, `leanchecker`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`,
`con-ron` via `lake comparator --config comparator.json --paranoid`).
All proofs live in `Solution.lean` and `TriadFrontier.*`.
-/

namespace TriadFrontier.Challenge

open TriadFrontier.AlgebraCore
open TriadFrontier.PIRCertificates
open TriadFrontier.PIRLinearCerts
open TriadFrontier.PIRKoszul
open TriadFrontier.MLWETightness
open TriadFrontier.ComplexityTriad
open TriadFrontier.KoszulTensor
open TriadFrontier.StrassenWinograd
open TriadFrontier.BrockettDobkin
open TriadFrontier.AlgebraicComplexity
open TriadFrontier.ShannonCapacity
open TriadFrontier.PaleyCapacity

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

def T1h_InfiniteNonShannonConeAndContraction : Prop :=
  (∀ (H : Nat → Int) (a b c d : Nat) (α c1 c2 c3 c4 c5 c6 : Nat),
    0 ≤ ingletonQ H c d a b →
    0 ≤ condI H a c d → 0 ≤ condI H a d c → 0 ≤ condI H c d a →
    0 ≤ condI H b c d → 0 ≤ condI H b d c → 0 ≤ condI H c d b →
    0 ≤ nonShannonConeQ H a b c d α c1 c2 c3 c4 c5 c6) ∧
  (∀ (H : Nat → Int) (a b c d : Nat),
    matusFamilyQ H a b c d 1 = zhangYeungQ H a b c d) ∧
  (∀ (H : Nat → Int) (a b c d s : Nat),
    0 ≤ ingletonQ H c d a b →
    0 ≤ condI H a c d → 0 ≤ condI H a d c → 0 ≤ condI H c d a → 0 ≤ condI H b c d →
    0 ≤ matusFamilyQ H a b c d s) ∧
  (∀ (E K T j : Nat), 2 ≤ E → 2 ≤ K → 2 ≤ T → K ≤ E → T ≤ E → 1 ≤ j →
    let numKV : Int := ((K : Int) + T - 1) * E - (K : Int) * T
    let denKV : Int := (E : Int) * ((E : Int) - 1)
    let numLF : Int := (K : Int) + T - 1
    let denLF : Int := (E : Int)
    numLF * denKV - numKV * denLF = ((K : Int) - 1) * ((T : Int) - 1) * E ∧
    (numKV * denLF) ^ j < (numLF * denKV) ^ j) ∧
  (9 * 37 > 16 * 19)

def T2g_QGTLRenyiVariationalBridgeAndDyadic512 : Prop :=
  (∀ (N : Nat) (M : Int) (p q w φ : Nat → Int),
    0 < M →
    (∀ i, i < N → 0 < q i ∧ 0 ≤ w i ∧ w i * q i = M) →
    let P := sumInt N p
    let Q := sumInt N q
    let Sφq := sumInt N (fun i => q i * φ i)
    let Sφp := sumInt N (fun i => p i * φ i)
    let φt : Nat → Int := fun i => Q * φ i - Sφq
    M * Q * (Q * Sφp - P * Sφq) * (Q * Sφp - P * Sφq) ≤
    sumInt N (fun i => q i * φt i * φt i) *
      (Q * sumInt N (fun i => p i * p i * w i) - M * P * P)) ∧
  (dyadic512Weight (-4) + dyadic512Weight (-3) + dyadic512Weight (-2) + dyadic512Weight (-1) +
     dyadic512Weight 0 + dyadic512Weight 1 + dyadic512Weight 2 + dyadic512Weight 3 +
     dyadic512Weight 4 = 512 ∧
   16 * dyadic512Weight (-4) + 9 * dyadic512Weight (-3) + 4 * dyadic512Weight (-2) +
     1 * dyadic512Weight (-1) + 1 * dyadic512Weight 1 + 4 * dyadic512Weight 2 +
     9 * dyadic512Weight 3 + 16 * dyadic512Weight 4 = 768 ∧
   256 * dyadic512Weight (-4) + 81 * dyadic512Weight (-3) + 16 * dyadic512Weight (-2) +
     1 * dyadic512Weight (-1) + 1 * dyadic512Weight 1 + 16 * dyadic512Weight 2 +
     81 * dyadic512Weight 3 + 256 * dyadic512Weight 4 = 3456 ∧
   3456 * 4 = 27 * 512 ∧
   5 * 2 < 1 * 12 ∧
   5921 * 128 < 76298 * 10)

def T3g_AllMKoszulMatMulLowerBound : Prop :=
  (∀ (F : Type) [SimpleField F] (m r : Nat),
    2 ≤ m →
    HasTensorRankAtMost (m * m) (m * m) (m * m) r
      (fun a b c => intToR (R := F) (matMulTensor m a b c)) →
    m * m + 2 ≤ r) ∧
  (∀ (m : Nat), 2 ≤ m →
    (m * m - m + 1) * (m * m + m - 1) < m * m * (m * m))

def T3h_StrassenWinogradExactRankSeven : Prop :=
  (∀ (F : Type) [SimpleField F],
    HasTensorRankAtMost 4 4 4 7 (fun a b c => intToR (R := F) (matMul2Tensor a b c))) ∧
  (∀ (F : Type) [SimpleField F] (r : Nat),
    HasTensorRankAtMost 4 4 4 r (fun a b c => intToR (R := F) (matMul2Tensor a b c)) →
    7 ≤ r)

def T1i_Total4VarEntropicAnd5ObjLinearBarrier : Prop :=
  (∀ (c : Nat → Int),
    (∀ r, r < 23 →
      let sp := linRay4Spec.getD r (2, [])
      0 ≤ evalFunc4 c (subspaceRank4 sp.1 sp.2)) →
    ∀ ci, ci < 24 → 0 ≤ evalFunc4 c (fun m => canonProf4At ci (m - 1))) ∧
  (∀ (c : Nat → Int),
    (∀ subs : List (List (List Nat)), 0 ≤ evalFunc5 c (subspaceRank5 2 subs)) →
    0 ≤ evalFunc5 c (hUncondMarg5 (retObjMask 0) (retObjMask 2) (retObjMask 3) (retObjMask 4) (retObjMask 5)) ∧
    0 ≤ evalFunc5 c (hUncondMarg5 (retObjMask 1) (retObjMask 2) (retObjMask 3) (retObjMask 4) (retObjMask 5)) ∧
    (∀ t ∈ ([(2, 3, 4), (2, 3, 5), (2, 4, 5), (3, 4, 5)] : List (Nat × Nat × Nat)),
      0 ≤ evalFunc5 c (hUncondMarg5 (retObjMask 0) (retObjMask 1) (retObjMask t.1) (retObjMask t.2.1) (retObjMask t.2.2)))) ∧
  (checkLinRay4Exact = true ∧ checkCanonDecomp4 = true ∧
   checkAll510Marg4 = true ∧ checkQuadEnum495and15 = true ∧ checkAll6RetMarg5 = true)

def T2h_AllOrderRenyiHolderTVAndDyadic1024 : Prop :=
  (∀ (N m M : Nat) (p q w : Nat → Nat),
    0 < M → (∀ i, i < N → w i * q i = M) →
    M ^ m * (sumNatML N p) ^ (m + 1) ≤
    (sumNatML N q) ^ m * sumNatML N (fun i => p i ^ (m + 1) * w i ^ m)) ∧
  (∀ (N : Nat) (M : Int) (p q w : Nat → Int),
    0 < M → (∀ i, i < N → 0 < q i ∧ 0 ≤ w i ∧ w i * q i = M) →
    let P := sumInt N p
    let Q := sumInt N q
    let Sabs := sumInt N (fun i => intAbs (Q * p i - P * q i))
    M * Sabs * Sabs ≤ Q * Q * (Q * sumInt N (fun i => p i * p i * w i) - M * P * P)) ∧
  (dyadic1024AWeight (-3) + dyadic1024AWeight (-2) + dyadic1024AWeight (-1) + dyadic1024AWeight 0 +
     dyadic1024AWeight 1 + dyadic1024AWeight 2 + dyadic1024AWeight 3 = 1024 ∧
   9 * dyadic1024AWeight (-3) + 4 * dyadic1024AWeight (-2) + 1 * dyadic1024AWeight (-1) +
     1 * dyadic1024AWeight 1 + 4 * dyadic1024AWeight 2 + 9 * dyadic1024AWeight 3 = 1024 ∧
   81 * dyadic1024AWeight (-3) + 16 * dyadic1024AWeight (-2) + 1 * dyadic1024AWeight (-1) +
     1 * dyadic1024AWeight 1 + 16 * dyadic1024AWeight 2 + 81 * dyadic1024AWeight 3 = 2968 ∧
   2968 * 128 = 371 * 1024 ∧
   15 * 512 < 243 * 32 ∧ 243 * 2 < 512 ∧
   8672 * 77 < 67150 * 10 ∧ 1509 * 25 < 37842 ∧ 9100 * 11 < 100920) ∧
  (dyadic1024BWeight (-4) + dyadic1024BWeight (-3) + dyadic1024BWeight (-2) + dyadic1024BWeight (-1) +
     dyadic1024BWeight 0 + dyadic1024BWeight 1 + dyadic1024BWeight 2 + dyadic1024BWeight 3 +
     dyadic1024BWeight 4 = 1024 ∧
   16 * dyadic1024BWeight (-4) + 9 * dyadic1024BWeight (-3) + 4 * dyadic1024BWeight (-2) +
     1 * dyadic1024BWeight (-1) + 1 * dyadic1024BWeight 1 + 4 * dyadic1024BWeight 2 +
     9 * dyadic1024BWeight 3 + 16 * dyadic1024BWeight 4 = 1536 ∧
   256 * dyadic1024BWeight (-4) + 81 * dyadic1024BWeight (-3) + 16 * dyadic1024BWeight (-2) +
     1 * dyadic1024BWeight (-1) + 1 * dyadic1024BWeight 1 + 16 * dyadic1024BWeight 2 +
     81 * dyadic1024BWeight 3 + 256 * dyadic1024BWeight 4 = 6624 ∧
   6624 * 32 = 207 * 1024 ∧
   5 * 32 < 15 * 12 ∧ 15 * 2 < 32 ∧
   5591 * 44 < 24770 * 10 ∧ 5948 * 49 < 29520 * 10)

def T3i_BrockettDobkinRectangularAndQuadraticMatMulBound : Prop :=
  (∀ (F : Type) [SimpleField F] (m k p r : Nat),
    1 ≤ m → 1 ≤ k → 1 ≤ p →
    HasTensorRankAtMost (m * k) (k * p) (m * p) r
      (fun a b c => intToR (R := F) (rectMatMulTensor m k p a b c)) →
    m * k + m * p - m ≤ r ∧ m * k + k * p - k ≤ r ∧ m * p + k * p - p ≤ r) ∧
  (∀ (F : Type) [SimpleField F] (m r : Nat),
    1 ≤ m →
    HasTensorRankAtMost (m * m) (m * m) (m * m) r
      (fun a b c => intToR (R := F) (matMulTensor m a b c)) →
    2 * m * m - m ≤ r) ∧
  (∀ (m : Nat), 3 ≤ m → m * m + m < 2 * m * m - m) ∧
  (∀ (F : Type) [SimpleField F] (m p r : Nat),
    2 ≤ m → 2 ≤ p →
    HasTensorRankAtMost (m * 2) (2 * p) (m * p) r
      (fun a b c => intToR (R := F) (rectMatMulTensor m 2 p a b c)) →
    m * p + 3 ≤ r)

def T3j_ShannonCapacityLovaszC5AndHaemers : Prop :=
  (∀ (F : Type) [SimpleField F] (n r t k : Nat) (adj : Nat → Nat → Bool)
      (U V M : Nat → Nat → F) (f : Nat → Nat),
    (∀ i j, i < n → j < n → sumR r (fun s => U i s * V s j) = M i j) →
    FitsGraph n adj M →
    IsIndepSet (n ^ t) (strongPowAdj n adj t) k f →
    k ≤ r ^ t) ∧
  (∀ (t k : Nat) (f : Nat → Nat),
    IsIndepSet (5 ^ t) (strongPowAdj 5 c5Adj t) k f → k * k ≤ 5 ^ t) ∧
  (∀ (m : Nat), ∃ f : Nat → Nat,
    IsIndepSet (5 ^ (2 * m)) (strongPowAdj 5 c5Adj (2 * m)) (5 ^ m) f) ∧
  (∀ (m : Nat), ∃ f : Nat → Nat,
    IsIndepSet (7 ^ (2 * m)) (strongPowAdj 7 c7Adj (2 * m)) (10 ^ m) f) ∧
  (∀ (F : Type) [SimpleField F] (r : Nat) (U V M : Nat → Nat → F),
    (∀ i j, i < 7 → j < 7 → sumR r (fun s => U i s * V s j) = M i j) →
    FitsGraph 7 c7Adj M → 4 ≤ r) ∧
  (∀ (F : Type) [SimpleField F],
    ∃ (U V M : Nat → Nat → F),
      (∀ i j, i < 7 → j < 7 → sumR 4 (fun s => U i s * V s j) = M i j) ∧
      FitsGraph 7 c7Adj M)

def T1j_Total6ObjF2EntropicRealizabilityBarrier : Prop :=
  (hUncondRet6 0 = 0 ∧
   ∀ m : Nat, 1 ≤ m → m ≤ 63 →
     hUncondRet6 m = 4 * subspaceRank6F2 64 ret6F2Arrangement m) ∧
  (∀ c : Nat → Int,
    (∀ (d : Nat) (subs : List (List (List Nat))), 0 ≤ evalFunc6 c (subspaceRank6F2 d subs)) →
    0 ≤ evalFunc6 c hUncondRet6) ∧
  (hUncondRet6 1 = 128 ∧ hUncondRet6 4 = 52 ∧ hUncondRet6 60 = 208 ∧
   hUncondRet6 61 = 208 ∧ 4 * 52 * 3 < 128 * 5)

def T2i_BaiEngineDPITensorizationAndDyadic16384 : Prop :=
  (∀ (N L M Mout D : Nat) (K : Nat → Nat → Nat) (p q w W : Nat → Nat),
    0 < M → (∀ i, i < N → w i * q i = M) →
    (∀ j, j < L → W j * sumNatML N (fun i => K j i * q i) = Mout) →
    (∀ i, i < N → sumNatML L (fun j => K j i) = D) →
    M * sumNatML L (fun j => (sumNatML N (fun i => K j i * p i)) ^ 2 * W j) ≤
    Mout * D * sumNatML N (fun i => p i * p i * w i)) ∧
  (∀ (N r m : Nat) (p w : Nat → Nat), 0 < N →
    sumNatML (N ^ m) (fun x => (prodNatPow N p m x) ^ (r + 1) * (prodNatPow N w m x) ^ r) =
    (sumNatML N (fun i => p i ^ (r + 1) * w i ^ r)) ^ m) ∧
  (∀ (N r D M Rmax : Nat) (p q w : Nat → Nat),
    (∀ i, i < N → w i * q i = M) →
    (∀ i, i < N → p i * D ≤ Rmax * q i) →
    D ^ r * sumNatML N (fun i => p i ^ (r + 1) * w i ^ r) ≤
      Rmax ^ r * M ^ r * sumNatML N p ∧
    D * sumNatML N p ≤ Rmax * sumNatML N q) ∧
  (dyadic16384AWeight (-3) + dyadic16384AWeight (-2) + dyadic16384AWeight (-1) +
     dyadic16384AWeight 0 + dyadic16384AWeight 1 + dyadic16384AWeight 2 + dyadic16384AWeight 3 = 16384 ∧
   9 * dyadic16384AWeight (-3) + 4 * dyadic16384AWeight (-2) + dyadic16384AWeight (-1) +
     dyadic16384AWeight 1 + 4 * dyadic16384AWeight 2 + 9 * dyadic16384AWeight 3 = 16384 ∧
   81 * dyadic16384AWeight (-3) + 16 * dyadic16384AWeight (-2) + dyadic16384AWeight (-1) +
     dyadic16384AWeight 1 + 16 * dyadic16384AWeight 2 + 81 * dyadic16384AWeight 3 = 47728 ∧
   47728 * 1024 = 2983 * 16384 ∧
   243 * 4096 < 1959 * 512 ∧ 1959 * 2 < 4096 ∧
   6013 * 111 < 67140 * 10) ∧
  (dyadic16384BWeight (-5) + dyadic16384BWeight (-4) + dyadic16384BWeight (-3) +
     dyadic16384BWeight (-2) + dyadic16384BWeight (-1) + dyadic16384BWeight 0 +
     dyadic16384BWeight 1 + dyadic16384BWeight 2 + dyadic16384BWeight 3 +
     dyadic16384BWeight 4 + dyadic16384BWeight 5 = 16384 ∧
   25 * dyadic16384BWeight (-5) + 16 * dyadic16384BWeight (-4) + 9 * dyadic16384BWeight (-3) +
     4 * dyadic16384BWeight (-2) + dyadic16384BWeight (-1) + dyadic16384BWeight 1 +
     4 * dyadic16384BWeight 2 + 9 * dyadic16384BWeight 3 + 16 * dyadic16384BWeight 4 +
     25 * dyadic16384BWeight 5 = 24576 ∧
   625 * dyadic16384BWeight (-5) + 256 * dyadic16384BWeight (-4) + 81 * dyadic16384BWeight (-3) +
     16 * dyadic16384BWeight (-2) + dyadic16384BWeight (-1) + dyadic16384BWeight 1 +
     16 * dyadic16384BWeight 2 + 81 * dyadic16384BWeight 3 + 256 * dyadic16384BWeight 4 +
     625 * dyadic16384BWeight 5 = 110040 ∧
   110040 * 2048 = 13755 * 16384 ∧
   15 * 6144 < 3049 * 32 ∧ 3049 * 2 < 6144 ∧
   5916 * 418 < 24770 * 100)

def T3k_SchwartzZippelAndStrassenSandwich : Prop :=
  (∀ (F : Type) [SimpleField F] (n d : Nat) (S : List F) (P : MPoly F n),
    ListNodup S → mpNonZero P → mpDegLe d P →
    S.length * countGridRoots S (mpEval P) ≤ d * S.length ^ n) ∧
  (∀ (F : Type) [SimpleField F] (n d : Nat) (S : List F) (P : MPoly F n),
    ListNodup S → mpNonZero P → mpDegLe d P → d < S.length →
    ∃ a : Fin n → F, (∀ i, a i ∈ S) ∧ mpEval P a ≠ 0) ∧
  (∀ (F : Type) [SimpleField F] (m k p r : Nat),
    HasTensorRankAtMost (m * k) (k * p) (m * p) r
      (fun a b c => intToR (R := F) (rectMatMulTensor m k p a b c)) →
    HasTensorRankAtMost (p * k) (k * m) (p * m) r
      (fun a b c => intToR (R := F) (rectMatMulTensor p k m a b c))) ∧
  (∀ (F : Type) [SimpleField F] (k : Nat),
    HasTensorRankAtMost (2 ^ k * 2 ^ k) (2 ^ k * 2 ^ k) (2 ^ k * 2 ^ k) (7 ^ k)
      (fun a b c => intToR (R := F) (matMulTensor (2 ^ k) a b c)) ∧
    ∀ r : Nat,
      HasTensorRankAtMost (2 ^ k * 2 ^ k) (2 ^ k * 2 ^ k) (2 ^ k * 2 ^ k) r
        (fun a b c => intToR (R := F) (matMulTensor (2 ^ k) a b c)) →
      2 * 4 ^ k - 2 ^ k ≤ r)

def T3l_InfinitePaleyConferenceShannonCapacity : Prop :=
  (∀ (k : Nat) (adj : Nat → Nat → Bool),
    IsConferenceGraph k adj →
    ∀ (t m : Nat) (f : Nat → Nat),
      IsIndepSet ((4 * k + 1) ^ t) (strongPowAdj (4 * k + 1) adj t) m f →
      m * m ≤ (4 * k + 1) ^ t) ∧
  (∀ (n : Nat) (adj : Nat → Nat → Bool) (φ : Nat → Nat),
    0 < n → IsSelfCompMap n adj φ →
    ∀ (m : Nat), ∃ f : Nat → Nat,
      IsIndepSet (n ^ (2 * m)) (strongPowAdj n adj (2 * m)) (n ^ m) f) ∧
  ((∀ (t m : Nat) (f : Nat → Nat),
      IsIndepSet (13 ^ t) (strongPowAdj 13 paley13Adj t) m f → m * m ≤ 13 ^ t) ∧
   (∀ (m : Nat), ∃ f : Nat → Nat,
      IsIndepSet (13 ^ (2 * m)) (strongPowAdj 13 paley13Adj (2 * m)) (13 ^ m) f)) ∧
  ((∀ (t m : Nat) (f : Nat → Nat),
      IsIndepSet (17 ^ t) (strongPowAdj 17 paley17Adj t) m f → m * m ≤ 17 ^ t) ∧
   (∀ (m : Nat), ∃ f : Nat → Nat,
      IsIndepSet (17 ^ (2 * m)) (strongPowAdj 17 paley17Adj (2 * m)) (17 ^ m) f))

def AllTriadFrontierTheorems : Prop :=
  T1a_KoszulVeroneseRankIdentity ∧
  T1b_UniversalKoszulDominationOverLFSR ∧
  T1c_ByzantineRobustCapacityAndF11Certificate ∧
  T1d_FlagPrivacyAndFeasibilityDimensions ∧
  T1e_UnconditionedShannonIngletonBarrier ∧
  T1f_ProjectiveP3LinearImpossibility ∧
  T1g_ZhangYeungReductionAndMFileKoszul ∧
  T1h_InfiniteNonShannonConeAndContraction ∧
  T1i_Total4VarEntropicAnd5ObjLinearBarrier ∧
  T1j_Total6ObjF2EntropicRealizabilityBarrier ∧
  T2a_DeterminantIdealSecretIndependence ∧
  T2b_ChenStep9AntiPeriodicDFTCancellation ∧
  T2c_MLKEMCBDRenyiCliff ∧
  T2d_QGTLShiftedLWEBerryCurvature ∧
  T2e_Dyadic256RenyiFloorAndQGTLPSD ∧
  T2f_UniversalTwistedDFTSelectionRule ∧
  T2g_QGTLRenyiVariationalBridgeAndDyadic512 ∧
  T2h_AllOrderRenyiHolderTVAndDyadic1024 ∧
  T2i_BaiEngineDPITensorizationAndDyadic16384 ∧
  T3a_AlgebrizationMultilinearExtensionUniqueness ∧
  T3b_LWEToNaturalProofsObstruction ∧
  T3c_KatzTrevisanByzantinePIRToLDC ∧
  T3d_MLWESingleServerPIRNoiseCeiling ∧
  T3e_KoszulFlatteningTensorRankBridge ∧
  T3f_ShannonCountingAndLDCSmoothness ∧
  T3g_AllMKoszulMatMulLowerBound ∧
  T3h_StrassenWinogradExactRankSeven ∧
  T3i_BrockettDobkinRectangularAndQuadraticMatMulBound ∧
  T3j_ShannonCapacityLovaszC5AndHaemers ∧
  T3k_SchwartzZippelAndStrassenSandwich ∧
  T3l_InfinitePaleyConferenceShannonCapacity

end
end TriadFrontier.Challenge
