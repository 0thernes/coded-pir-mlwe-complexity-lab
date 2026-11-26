module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore
public import TriadFrontier.KoszulTensor

/-!
# Exact Strassen–Winograd Theorem: `rank_F(⟨2, 2, 2⟩) = 7` Over EVERY Field `F` (`T3h`)

Zero-Mathlib, characteristic-free proof of exact optimality of Strassen's (1969) 7-product
algorithm for `2 × 2` matrix multiplication over **EVERY `SimpleField F` (including `char F = 2`!)**:
1. **Upper bound (`strassen_rank_le_seven`):** Explicit 7-product bilinear decomposition verified
   over `Int` and lifted to every `SimpleField F` via `intToR`.
2. **Lower bound (`winograd_rank_ge_seven`):** Elementary Gauss-Jordan RREF on the `4 × 6`
   slice-coefficient matrix, `matRankFactor_le` ruling out rank-3 covers of invertible `X ⊗ I_2`,
   rank-1 `2 × 2` clique bound `≤ 2`, and `2 × 2` Cramer row/column intersection kill — zero
   characteristic restrictions, zero Mathlib, zero `sorry`, zero `native_decide`.
-/

namespace TriadFrontier.StrassenWinograd

open TriadFrontier.AlgebraCore
open TriadFrontier.KoszulTensor

@[expose] public section

-- ============================================================================
-- Section 1: Strassen's (1969) Explicit 7-Product Upper Bound Over Every Field
-- ============================================================================

/-- Strassen's 7 left-factor integer coefficients on `(A00, A01, A10, A11)`. -/
def strassenU (s a : Nat) : Int :=
  match s, a with
  | 0, 0 => 1  | 0, 3 => 1
  | 1, 2 => 1  | 1, 3 => 1
  | 2, 0 => 1
  | 3, 3 => 1
  | 4, 0 => 1  | 4, 1 => 1
  | 5, 0 => -1 | 5, 2 => 1
  | 6, 1 => 1  | 6, 3 => -1
  | _, _ => 0

/-- Strassen's 7 right-factor integer coefficients on `(B00, B01, B10, B11)`. -/
def strassenV (s b : Nat) : Int :=
  match s, b with
  | 0, 0 => 1  | 0, 3 => 1
  | 1, 0 => 1
  | 2, 1 => 1  | 2, 3 => -1
  | 3, 0 => -1 | 3, 2 => 1
  | 4, 3 => 1
  | 5, 0 => 1  | 5, 1 => 1
  | 6, 2 => 1  | 6, 3 => 1
  | _, _ => 0

/-- Strassen's 7 output integer coefficients on `(C00, C01, C10, C11)`. -/
def strassenW (s c : Nat) : Int :=
  match s, c with
  | 0, 0 => 1  | 0, 3 => 1
  | 1, 2 => 1  | 1, 3 => -1
  | 2, 1 => 1  | 2, 3 => 1
  | 3, 0 => 1  | 3, 2 => 1
  | 4, 0 => -1 | 4, 1 => 1
  | 5, 3 => 1
  | 6, 0 => 1
  | _, _ => 0

def checkStrassenExact : Bool :=
  allNatBelow 4 fun a =>
    allNatBelow 4 fun b =>
      allNatBelow 4 fun c =>
        decide (sumInt 7 (fun s => strassenU s a * strassenV s b * strassenW s c) = matMul2Tensor a b c)

theorem checkStrassenExact_ok : checkStrassenExact = true := by decide

/-- Strassen's (1969) upper bound `rank_F(⟨2,2,2⟩) ≤ 7` over EVERY `SimpleField F`. -/
theorem strassen_rank_le_seven (F : Type) [SimpleField F] :
    HasTensorRankAtMost 4 4 4 7 (fun a b c => intToR (R := F) (matMul2Tensor a b c)) := by
  refine ⟨fun s a => intToR (strassenU s a),
          fun s b => intToR (strassenV s b),
          fun s c => intToR (strassenW s c), ?_⟩
  intro a b c ha hb hc
  have h1 := allNatBelow_true checkStrassenExact_ok a ha
  have h2 := allNatBelow_true h1 b hb
  have h3 := allNatBelow_true h2 c hc
  have hint : sumInt 7 (fun s => strassenU s a * strassenV s b * strassenW s c) = matMul2Tensor a b c :=
    of_decide_eq_true h3
  dsimp only
  rw [← hint, ← sumR_intToR]
  apply sumR_congr
  intro s _
  rw [intToR_mul, intToR_mul]

-- ============================================================================
-- Section 2: Elementary Algebra & 4×4 Slice `M(X) = X ⊗ I_2` Lemmas
-- ============================================================================

theorem mul_sub_r {R : Type} [CommRing R] (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [CommRing.sub_eq, CommRing.left_distrib, mul_neg, CommRing.sub_eq]

theorem sub_mul_r {R : Type} [CommRing R] (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [CommRing.sub_eq, right_distrib, neg_mul, CommRing.sub_eq]

theorem sumR_mul_right {R : Type} [CommRing R] (n : Nat) (f : Nat → R) (c : R) :
    sumR n f * c = sumR n (fun i => f i * c) := by
  rw [CommRing.mul_comm, sumR_mul_left]
  exact sumR_congr (fun i _ => CommRing.mul_comm c (f i))

theorem sumR_swap {R : Type} [CommRing R] (m n : Nat) (f : Nat → Nat → R) :
    sumR m (fun i => sumR n (fun j => f i j)) = sumR n (fun j => sumR m (fun i => f i j)) := by
  induction m with
  | zero => simp [sumR, sumR_zero_fn]
  | succ m' ih => simp only [sumR, ih, sumR_add]

def det2 {R : Type} [CommRing R] (X : Nat → R) : R :=
  X 0 * X 3 - X 1 * X 2

def det2Pair {R : Type} [CommRing R] (a0 a1 b0 b1 : R) : R :=
  a0 * b1 - a1 * b0

/-- Explicit `4 × 4` Kronecker slice `M(X) = X ⊗ I_2` matching `matMul2Tensor`. -/
def sliceM {R : Type} [CommRing R] (X : Nat → R) (c b : Nat) : R :=
  sumR 4 (fun a => X a * intToR (R := R) (matMul2Tensor a b c))

theorem field_mul_eq_zero {F : Type} [SimpleField F] {a b : F} (h : a * b = 0) :
    a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have h1 := congrArg (fun x => SimpleField.inv a * x) h
    rw [← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv a) a,
        SimpleField.mul_inv_cancel a ha, CommRing.one_mul, mul_zero] at h1
    exact h1

theorem field_mul_ne_zero {F : Type} [SimpleField F] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro hz
  cases field_mul_eq_zero hz with
  | inl h => exact ha h
  | inr h => exact hb h

theorem neg_eq_zero_iff {R : Type} [CommRing R] {a : R} : -a = 0 ↔ a = 0 := by
  constructor
  · intro h; have h2 := congrArg (fun x => -x) h; rw [neg_neg, neg_zero] at h2; exact h2
  · intro h; rw [h, neg_zero]

theorem sumR_four {R : Type} [CommRing R] (f : Nat → R) :
    sumR 4 f = f 0 + f 1 + f 2 + f 3 := by
  simp only [sumR, CommRing.zero_add]

theorem ite_pos_r {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  split
  · rfl
  · contradiction

theorem ite_neg_r {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by
  split
  · contradiction
  · rfl

theorem sliceM_eval {R : Type} [CommRing R] (X : Nat → R) :
    (sliceM X 0 0 = X 0 ∧ sliceM X 0 1 = 0 ∧ sliceM X 0 2 = X 1 ∧ sliceM X 0 3 = 0) ∧
    (sliceM X 1 0 = 0 ∧ sliceM X 1 1 = X 0 ∧ sliceM X 1 2 = 0 ∧ sliceM X 1 3 = X 1) ∧
    (sliceM X 2 0 = X 2 ∧ sliceM X 2 1 = 0 ∧ sliceM X 2 2 = X 3 ∧ sliceM X 2 3 = 0) ∧
    (sliceM X 3 0 = 0 ∧ sliceM X 3 1 = X 2 ∧ sliceM X 3 2 = 0 ∧ sliceM X 3 3 = X 3) := by
  have z : intToR (R := R) 0 = 0 := intToR_zero
  have o : intToR (R := R) 1 = 1 := intToR_one
  have e0 : ∀ c b, matMul2Tensor 0 b c = 0 → matMul2Tensor 1 b c = 0 →
      matMul2Tensor 2 b c = 0 → matMul2Tensor 3 b c = 0 → sliceM X c b = 0 := by
    intro c b h0 h1 h2 h3
    unfold sliceM; rw [sumR_four, h0, h1, h2, h3, z, mul_zero, mul_zero, mul_zero, mul_zero,
      add_zero, add_zero, add_zero]
  have e1 : ∀ c b a, a < 4 →
      matMul2Tensor 0 b c = (if 0 = a then 1 else 0) →
      matMul2Tensor 1 b c = (if 1 = a then 1 else 0) →
      matMul2Tensor 2 b c = (if 2 = a then 1 else 0) →
      matMul2Tensor 3 b c = (if 3 = a then 1 else 0) → sliceM X c b = X a := by
    intro c b a ha h0 h1 h2 h3
    unfold sliceM; rw [sumR_four, h0, h1, h2, h3]
    have ha4 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
    rcases ha4 with rfl | rfl | rfl | rfl <;>
      simp [z, o, mul_one, mul_zero, add_zero, CommRing.zero_add]
  exact ⟨⟨e1 0 0 0 (by omega) (by decide) (by decide) (by decide) (by decide),
          e0 0 1 (by decide) (by decide) (by decide) (by decide),
          e1 0 2 1 (by omega) (by decide) (by decide) (by decide) (by decide),
          e0 0 3 (by decide) (by decide) (by decide) (by decide)⟩,
         ⟨e0 1 0 (by decide) (by decide) (by decide) (by decide),
          e1 1 1 0 (by omega) (by decide) (by decide) (by decide) (by decide),
          e0 1 2 (by decide) (by decide) (by decide) (by decide),
          e1 1 3 1 (by omega) (by decide) (by decide) (by decide) (by decide)⟩,
         ⟨e1 2 0 2 (by omega) (by decide) (by decide) (by decide) (by decide),
          e0 2 1 (by decide) (by decide) (by decide) (by decide),
          e1 2 2 3 (by omega) (by decide) (by decide) (by decide) (by decide),
          e0 2 3 (by decide) (by decide) (by decide) (by decide)⟩,
         ⟨e0 3 0 (by decide) (by decide) (by decide) (by decide),
          e1 3 1 2 (by omega) (by decide) (by decide) (by decide) (by decide),
          e0 3 2 (by decide) (by decide) (by decide) (by decide),
          e1 3 3 3 (by omega) (by decide) (by decide) (by decide) (by decide)⟩⟩

theorem sliceM_linear {R : Type} [CommRing R] (α β : R) (X Y : Nat → R) (c b : Nat) :
    sliceM (fun a => α * X a + β * Y a) c b = α * sliceM X c b + β * sliceM Y c b := by
  unfold sliceM
  rw [sumR_mul_left, sumR_mul_left, ← sumR_add]
  apply sumR_congr
  intro a _
  rw [right_distrib, CommRing.mul_assoc, CommRing.mul_assoc]

/-- Invertible `2 × 2` matrix `X` (`det2 X ≠ 0`) has explicit `4 × 4` Kronecker inverse `sliceM Xinv`. -/
theorem sliceM_inv_mul {F : Type} [SimpleField F] (X : Nat → F) (hd : det2 X ≠ 0) :
    ∃ Xinv : Nat → F, ∀ c b, c < 4 → b < 4 →
      matMulF 4 (sliceM Xinv) (sliceM X) c b = matIdF c b := by
  let invd := SimpleField.inv (det2 X)
  have hdd : invd * det2 X = 1 := by rw [CommRing.mul_comm, SimpleField.mul_inv_cancel _ hd]
  let Xinv : Nat → F := fun a =>
    match a with
    | 0 => invd * X 3
    | 1 => -(invd * X 1)
    | 2 => -(invd * X 2)
    | _ => invd * X 0
  refine ⟨Xinv, ?_⟩
  have h1 := sliceM_eval X
  have h2 := sliceM_eval Xinv
  have hdiag : invd * X 3 * X 0 + -(invd * X 1) * X 2 = 1 := by
    calc invd * X 3 * X 0 + -(invd * X 1) * X 2
        = invd * (X 0 * X 3) + -(invd * (X 1 * X 2)) := by
          rw [CommRing.mul_assoc, CommRing.mul_comm (X 3) (X 0), neg_mul, CommRing.mul_assoc]
      _ = invd * (X 0 * X 3 - X 1 * X 2) := by rw [← mul_neg, ← CommRing.left_distrib, ← CommRing.sub_eq]
      _ = 1 := hdd
  have hdiag2 : -(invd * X 2) * X 1 + invd * X 0 * X 3 = 1 := by
    rw [CommRing.add_comm]
    calc invd * X 0 * X 3 + -(invd * X 2) * X 1
        = invd * (X 0 * X 3) + -(invd * (X 1 * X 2)) := by
          rw [CommRing.mul_assoc, neg_mul, CommRing.mul_assoc, CommRing.mul_comm (X 2) (X 1)]
      _ = invd * (X 0 * X 3 - X 1 * X 2) := by rw [← mul_neg, ← CommRing.left_distrib, ← CommRing.sub_eq]
      _ = 1 := hdd
  have hoff1 : invd * X 3 * X 1 + -(invd * X 1) * X 3 = 0 := by
    rw [neg_mul, CommRing.mul_assoc, CommRing.mul_assoc, CommRing.mul_comm (X 3) (X 1), CommRing.add_neg]
  have hoff2 : -(invd * X 2) * X 0 + invd * X 0 * X 2 = 0 := by
    rw [neg_mul, CommRing.mul_assoc, CommRing.mul_assoc, CommRing.mul_comm (X 2) (X 0), neg_add]
  intro c b hc hb
  have hc4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  have hb4 : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
  unfold matMulF matIdF
  rw [sumR_four]
  rcases hc4 with rfl | rfl | rfl | rfl <;> rcases hb4 with rfl | rfl | rfl | rfl <;>
    (try rw [ite_pos_r rfl]) <;> (try rw [ite_neg_r (by decide)]) <;>
    simp only [h1, h2, Xinv, mul_zero, zero_mul, add_zero, CommRing.zero_add,
      hdiag, hdiag2, hoff1, hoff2]

/-- **Fact A:** If `sliceM X` is a sum of 3 rank-1 matrices over ANY `SimpleField F`, then `det2 X = 0`! -/
theorem det2_eq_zero_of_sum3 {F : Type} [SimpleField F] (X : Nat → F)
    (p0 w0 p1 w1 p2 w2 : Nat → F)
    (hsum : ∀ c b, c < 4 → b < 4 →
      sliceM X c b = p0 c * w0 b + p1 c * w1 b + p2 c * w2 b) :
    det2 X = 0 := by
  by_cases hd : det2 X = 0
  · exact hd
  · exfalso
    obtain ⟨Xinv, hinv⟩ := sliceM_inv_mul X hd
    let P : Nat → Nat → F := fun c t =>
      match t with
      | 0 => p0 c
      | 1 => p1 c
      | _ => p2 c
    let Q : Nat → Nat → F := fun t b =>
      match t with
      | 0 => w0 b
      | 1 => w1 b
      | _ => w2 b
    let LP : Nat → Nat → F := fun i t => matMulF 4 (sliceM Xinv) P i t
    have h4le3 : 4 ≤ 3 := by
      apply matRankFactor_le 3 4 LP Q
      intro i j hi hj
      unfold matMulF LP
      -- Swap `sumR 3` and `sumR 4`
      have hswap : sumR 3 (fun t => sumR 4 (fun k => sliceM Xinv i k * P k t) * Q t j) =
          sumR 4 (fun k => sliceM Xinv i k * sumR 3 (fun t => P k t * Q t j)) := by
        calc sumR 3 (fun t => sumR 4 (fun k => sliceM Xinv i k * P k t) * Q t j)
            = sumR 3 (fun t => sumR 4 (fun k => (sliceM Xinv i k * P k t) * Q t j)) :=
              sumR_congr (fun t _ => sumR_mul_right 4 _ (Q t j))
          _ = sumR 4 (fun k => sumR 3 (fun t => (sliceM Xinv i k * P k t) * Q t j)) :=
              sumR_swap 3 4 _
          _ = sumR 4 (fun k => sliceM Xinv i k * sumR 3 (fun t => P k t * Q t j)) := by
              apply sumR_congr
              intro k _
              rw [sumR_mul_left]
              exact sumR_congr (fun t _ => CommRing.mul_assoc ..)
      change sumR 3 (fun t => sumR 4 (fun k => sliceM Xinv i k * P k t) * Q t j) = matIdF i j
      rw [hswap]
      have hcongr : sumR 4 (fun k => sliceM Xinv i k * sumR 3 (fun t => P k t * Q t j)) =
          sumR 4 (fun k => sliceM Xinv i k * sliceM X k j) := by
        apply sumR_congr
        intro k hk
        have h3 : sumR 3 (fun t => P k t * Q t j) = sliceM X k j := by
          simp only [sumR, CommRing.zero_add, P, Q]
          exact (hsum k j hk hj).symm
        rw [h3]
      rw [hcongr]
      exact hinv i j hi hj
    omega

/-- **Fact B:** No nonzero `X` can have `sliceM X` equal to a single rank-1 matrix `p c * w b`! -/
theorem sliceM_ne_rank1 {F : Type} [SimpleField F] (X p w : Nat → F)
    (hnz : ∃ a, a < 4 ∧ X a ≠ 0)
    (hr1 : ∀ c b, c < 4 → b < 4 → sliceM X c b = p c * w b) : False := by
  obtain ⟨a, ha, hXa⟩ := hnz
  have h1 := sliceM_eval X
  let i0 := a / 2
  let j0 := a % 2
  let invX := SimpleField.inv (X a)
  let P : Nat → Nat → F := fun r _ => invX * p (2 * i0 + r)
  let Q : Nat → Nat → F := fun _ s => w (2 * j0 + s)
  have h2le1 : 2 ≤ 1 := by
    apply matRankFactor_le 1 2 P Q
    intro r s hr hs
    unfold matMulF P Q matIdF
    simp only [sumR, CommRing.zero_add, CommRing.mul_assoc]
    have ha4 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
    have hr2 : r = 0 ∨ r = 1 := by omega
    have hs2 : s = 0 ∨ s = 1 := by omega
    have hmul : invX * X a = 1 := by rw [CommRing.mul_comm, SimpleField.mul_inv_cancel _ hXa]
    rcases ha4 with rfl | rfl | rfl | rfl <;>
      rcases hr2 with rfl | rfl <;> rcases hs2 with rfl | rfl <;>
      (dsimp only [i0, j0];
       (try rw [ite_pos_r rfl]); (try rw [ite_neg_r (by decide)]);
       rw [← hr1 _ _ (by omega) (by omega)];
       simp only [h1, mul_zero, hmul])
  omega

-- ============================================================================
-- Section 3: Singular `2×2` Factorization, Rank-1 Det Identity & Max-Clique ≤ 2
-- ============================================================================

/-- Every nonzero singular `2 × 2` matrix `X` factors explicitly as `u v^T`. -/
theorem singular2_factor {F : Type} [SimpleField F] (X : Nat → F)
    (hnz : ∃ a, a < 4 ∧ X a ≠ 0) (hdet : det2 X = 0) :
    ∃ u0 u1 v0 v1 : F,
      (u0 ≠ 0 ∨ u1 ≠ 0) ∧ (v0 ≠ 0 ∨ v1 ≠ 0) ∧
      X 0 = u0 * v0 ∧ X 1 = u0 * v1 ∧ X 2 = u1 * v0 ∧ X 3 = u1 * v1 := by
  have heq : X 0 * X 3 = X 1 * X 2 := eq_of_sub_eq_zero hdet
  by_cases h0 : X 0 ≠ 0
  · let inv0 := SimpleField.inv (X 0)
    refine ⟨1, X 2 * inv0, X 0, X 1, Or.inl (Ne.symm SimpleField.zero_ne_one), Or.inl h0,
            by rw [CommRing.one_mul], by rw [CommRing.one_mul], ?_, ?_⟩
    · rw [CommRing.mul_assoc, CommRing.mul_comm inv0 (X 0), SimpleField.mul_inv_cancel _ h0, mul_one]
    · calc X 3 = (inv0 * X 0) * X 3 := by
              rw [CommRing.mul_comm inv0 (X 0), SimpleField.mul_inv_cancel _ h0, CommRing.one_mul]
        _ = inv0 * (X 1 * X 2) := by rw [CommRing.mul_assoc, heq]
        _ = X 2 * inv0 * X 1 := by
              rw [CommRing.mul_comm (X 1) (X 2), ← CommRing.mul_assoc, CommRing.mul_comm inv0 (X 2)]
  · have h0' : X 0 = 0 := Classical.byContradiction h0
    rw [h0', zero_mul] at heq
    cases field_mul_eq_zero heq.symm with
    | inl h1 =>
      -- X 0 = 0, X 1 = 0: first row is zero!
      by_cases h2 : X 2 ≠ 0
      · exact ⟨0, 1, X 2, X 3, Or.inr (Ne.symm SimpleField.zero_ne_one), Or.inl h2,
               by rw [h0', zero_mul], by rw [h1, zero_mul], by rw [CommRing.one_mul], by rw [CommRing.one_mul]⟩
      · have h2' : X 2 = 0 := Classical.byContradiction h2
        have h3 : X 3 ≠ 0 := by
          obtain ⟨a, ha, hXa⟩ := hnz
          have ha4 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
          rcases ha4 with rfl | rfl | rfl | rfl <;> first | exact hXa | exact absurd h0' hXa | exact absurd h1 hXa | exact absurd h2' hXa
        exact ⟨0, 1, 0, X 3, Or.inr (Ne.symm SimpleField.zero_ne_one), Or.inr h3,
               by rw [h0', zero_mul], by rw [h1, zero_mul], by rw [h2', mul_zero], by rw [CommRing.one_mul]⟩
    | inr h2 =>
      -- X 0 = 0, X 2 = 0: first column is zero!
      by_cases h1 : X 1 ≠ 0
      · exact ⟨X 1, X 3, 0, 1, Or.inl h1, Or.inr (Ne.symm SimpleField.zero_ne_one),
               by rw [h0', mul_zero], by rw [mul_one], by rw [h2, mul_zero], by rw [mul_one]⟩
      · have h1' : X 1 = 0 := Classical.byContradiction h1
        have h3 : X 3 ≠ 0 := by
          obtain ⟨a, ha, hXa⟩ := hnz
          have ha4 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
          rcases ha4 with rfl | rfl | rfl | rfl <;> first | exact hXa | exact absurd h0' hXa | exact absurd h1' hXa | exact absurd h2 hXa
        exact ⟨0, X 3, 0, 1, Or.inr h3, Or.inr (Ne.symm SimpleField.zero_ne_one),
               by rw [h0', mul_zero], by rw [h1', zero_mul], by rw [h2, mul_zero], by rw [mul_one]⟩

/-- Exact algebraic determinant identity for a linear combination of two rank-1 `2 × 2` matrices:
`det(α u v^T + β u' v'^T) = α β · det(u, u') · det(v, v')` over ANY `CommRing R`! -/
theorem det2_rank1_comb {R : Type} [CommRing R] (α β u0 u1 v0 v1 u0' u1' v0' v1' : R) :
    (α * (u0 * v0) + β * (u0' * v0')) * (α * (u1 * v1) + β * (u1' * v1')) -
    (α * (u0 * v1) + β * (u0' * v1')) * (α * (u1 * v0) + β * (u1' * v0')) =
    α * β * det2Pair u0 u1 u0' u1' * det2Pair v0 v1 v0' v1' := by
  -- Expand both sides and cancel the `α²` and `β²` symmetric terms!
  have h1 : (α * (u0 * v0)) * (α * (u1 * v1)) = (α * (u0 * v1)) * (α * (u1 * v0)) := by
    simp only [CommRing.mul_assoc]
    have swap : u0 * (v0 * (α * (u1 * v1))) = u0 * (v1 * (α * (u1 * v0))) := by
      congr 1
      rw [← CommRing.mul_assoc v0 α, CommRing.mul_comm v0 α, CommRing.mul_assoc α v0,
          ← CommRing.mul_assoc v1 α, CommRing.mul_comm v1 α, CommRing.mul_assoc α v1]
      congr 1
      rw [← CommRing.mul_assoc v0 u1 v1, CommRing.mul_comm v0 u1, CommRing.mul_assoc u1 v0 v1,
          CommRing.mul_comm v0 v1, ← CommRing.mul_assoc u1 v1 v0, CommRing.mul_comm u1 v1,
          CommRing.mul_assoc v1 u1 v0]
    rw [swap]
  have h2 : (β * (u0' * v0')) * (β * (u1' * v1')) = (β * (u0' * v1')) * (β * (u1' * v0')) := by
    simp only [CommRing.mul_assoc]
    have swap : u0' * (v0' * (β * (u1' * v1'))) = u0' * (v1' * (β * (u1' * v0'))) := by
      congr 1
      rw [← CommRing.mul_assoc v0' β, CommRing.mul_comm v0' β, CommRing.mul_assoc β v0',
          ← CommRing.mul_assoc v1' β, CommRing.mul_comm v1' β, CommRing.mul_assoc β v1']
      congr 1
      rw [← CommRing.mul_assoc v0' u1' v1', CommRing.mul_comm v0' u1', CommRing.mul_assoc u1' v0' v1',
          CommRing.mul_comm v0' v1', ← CommRing.mul_assoc u1' v1' v0', CommRing.mul_comm u1' v1',
          CommRing.mul_assoc v1' u1' v0']
    rw [swap]
  -- Helper: `(a + b) * (c + d) - (e + f) * (g + h)` when `a*c = e*g` and `b*d = f*h` equals `a*d + b*c - e*h - f*g`!
  have hcancel : ∀ a b c d e f g h : R, a * c = e * g → b * d = f * h →
      (a + b) * (c + d) - (e + f) * (g + h) = (a * d - e * h) + (b * c - f * g) := by
    intro a b c d e f g h hac hbd
    rw [right_distrib, CommRing.left_distrib, CommRing.left_distrib,
        right_distrib, CommRing.left_distrib, CommRing.left_distrib, hac, hbd]
    simp only [CommRing.sub_eq, neg_add_distrib]
    -- Cancel `e*g + -(e*g)` and `f*h + -(f*h)`
    have p1 : ∀ x1 x2 x3 x4 y1 y2 y3 y4 : R,
        ((x1 + x2) + (x3 + x4)) + ((-(x1) + y2) + (y3 + -(x4))) = (x2 + y2) + (x3 + y3) := by
      intro x1 x2 x3 x4 y1 y2 y3 y4
      have s : ∀ r1 r2 r3 r4 : R, (r1 + r2) + (r3 + r4) = (r1 + r3) + (r2 + r4) := by
        intro r1 r2 r3 r4
        rw [CommRing.add_assoc, ← CommRing.add_assoc r2 r3 r4, CommRing.add_comm r2 r3,
            CommRing.add_assoc r3 r2 r4, ← CommRing.add_assoc]
      rw [s (x1 + x2) (x3 + x4) (-x1 + y2) (y3 + -x4),
          s x1 x2 (-x1) y2, CommRing.add_neg, CommRing.zero_add,
          s x3 x4 y3 (-x4), CommRing.add_neg, add_zero]
    exact p1 (e * g) (a * d) (b * c) (f * h) (-(e * g)) (-(e * h)) (-(f * g)) (-(f * h))
  rw [hcancel _ _ _ _ _ _ _ _ h1 h2]
  -- Now match each of the 4 cross terms against `α * β * (u0*u1' - u1*u0') * (v0*v1' - v1*v0')`!
  unfold det2Pair
  have m6 : ∀ x1 x2 x3 x4 x5 x6 : R,
      (x1 * (x2 * x3)) * (x4 * (x5 * x6)) = x1 * x4 * (x2 * x5) * (x3 * x6) := by
    intro x1 x2 x3 x4 x5 x6
    calc (x1 * (x2 * x3)) * (x4 * (x5 * x6))
        = x1 * (x4 * ((x2 * x3) * (x5 * x6))) := by
          rw [CommRing.mul_assoc x1, ← CommRing.mul_assoc (x2 * x3) x4, CommRing.mul_comm (x2 * x3) x4,
              CommRing.mul_assoc x4 (x2 * x3)]
      _ = x1 * x4 * ((x2 * x5) * (x3 * x6)) := by
          rw [← CommRing.mul_assoc x1 x4]
          congr 1
          rw [CommRing.mul_assoc x2 x3, ← CommRing.mul_assoc x3 x5 x6, CommRing.mul_comm x3 x5,
              CommRing.mul_assoc x5 x3 x6, ← CommRing.mul_assoc x2 x5]
      _ = x1 * x4 * (x2 * x5) * (x3 * x6) := by rw [← CommRing.mul_assoc]
  rw [m6 α u0 v0 β u1' v1', m6 α u0 v1 β u1' v0', m6 β u0' v0' α u1 v1, m6 β u0' v1' α u1 v0]
  have s1 : β * α * (u0' * u1) * (v0' * v1) = α * β * (u1 * u0') * (v1 * v0') := by
    rw [CommRing.mul_comm β α, CommRing.mul_comm u0' u1, CommRing.mul_comm v0' v1]
  have s2 : β * α * (u0' * u1) * (v1' * v0) = α * β * (u1 * u0') * (v0 * v1') := by
    rw [CommRing.mul_comm β α, CommRing.mul_comm u0' u1, CommRing.mul_comm v1' v0]
  rw [s1, s2]
  have hfo : ∀ x y z w : R, (x - y) * (z - w) = (x * z - x * w) + (y * w - y * z) := by
    intro x y z w
    rw [CommRing.sub_eq x y, CommRing.sub_eq z w, right_distrib, CommRing.left_distrib,
        CommRing.left_distrib, neg_mul, neg_mul, mul_neg, mul_neg, neg_neg,
        CommRing.add_comm (-(y * z)) (y * w), ← CommRing.sub_eq, ← CommRing.sub_eq]
  rw [mul_sub_r (α * β), hfo]

/-- Three `2D` vectors in `F^2` cannot all be pairwise linearly dependent with a non-trivial relation
unless they are all multiples of one vector; here phrased directly on `det2Pair`! -/
theorem det2Pair_trans {F : Type} [SimpleField F] {a0 a1 b0 b1 c0 c1 : F}
    (hb : b0 ≠ 0 ∨ b1 ≠ 0)
    (hab : det2Pair a0 a1 b0 b1 = 0) (hbc : det2Pair b0 b1 c0 c1 = 0) :
    det2Pair a0 a1 c0 c1 = 0 := by
  have e1 : a0 * b1 = a1 * b0 := eq_of_sub_eq_zero hab
  have e2 : b0 * c1 = b1 * c0 := eq_of_sub_eq_zero hbc
  cases hb with
  | inl hb0 =>
    have hmul : b0 * det2Pair a0 a1 c0 c1 = 0 := by
      unfold det2Pair
      rw [mul_sub_r]
      have t1 : b0 * (a0 * c1) = a0 * (b1 * c0) := by
        rw [← CommRing.mul_assoc, CommRing.mul_comm b0 a0, CommRing.mul_assoc, e2]
      have t2 : b0 * (a1 * c0) = a0 * (b1 * c0) := by
        rw [← CommRing.mul_assoc, CommRing.mul_comm b0 a1, ← e1, CommRing.mul_assoc]
      rw [t1, t2, sub_self]
    cases field_mul_eq_zero hmul with
    | inl h => exact absurd h hb0
    | inr h => exact h
  | inr hb1 =>
    have hmul : b1 * det2Pair a0 a1 c0 c1 = 0 := by
      unfold det2Pair
      rw [mul_sub_r]
      have t1 : b1 * (a0 * c1) = a1 * (b0 * c1) := by
        rw [← CommRing.mul_assoc, CommRing.mul_comm b1 a0, e1, CommRing.mul_assoc]
      have t2 : b1 * (a1 * c0) = a1 * (b0 * c1) := by
        rw [← CommRing.mul_assoc, CommRing.mul_comm b1 a1, CommRing.mul_assoc, ← e2]
      rw [t1, t2, sub_self]
    cases field_mul_eq_zero hmul with
    | inl h => exact absurd h hb1
    | inr h => exact h

/-- Three rank-1 matrices sharing collinear left factors (`det2Pair u_i u_j = 0`) are linearly dependent! -/
theorem rank1_three_dep_left {F : Type} [SimpleField F]
    (u0 u1 v0 v1 : Nat → F) (i j k : Nat)
    (hui : u0 i ≠ 0 ∨ u1 i ≠ 0)
    (hij : det2Pair (u0 i) (u1 i) (u0 j) (u1 j) = 0)
    (hik : det2Pair (u0 i) (u1 i) (u0 k) (u1 k) = 0) :
    ∃ α β γ : F, (α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0) ∧
      α * (u0 i * v0 i) + β * (u0 j * v0 j) + γ * (u0 k * v0 k) = 0 ∧
      α * (u0 i * v1 i) + β * (u0 j * v1 j) + γ * (u0 k * v1 k) = 0 ∧
      α * (u1 i * v0 i) + β * (u1 j * v0 j) + γ * (u1 k * v0 k) = 0 ∧
      α * (u1 i * v1 i) + β * (u1 j * v1 j) + γ * (u1 k * v1 k) = 0 := by
  -- Express `u j = sj * u i` and `u k = sk * u i`
  have hscale : ∀ t, det2Pair (u0 i) (u1 i) (u0 t) (u1 t) = 0 →
      ∃ s : F, u0 t = s * u0 i ∧ u1 t = s * u1 i := by
    intro t ht
    have heq : u0 i * u1 t = u1 i * u0 t := eq_of_sub_eq_zero ht
    cases hui with
    | inl h =>
      let s := u0 t * SimpleField.inv (u0 i)
      refine ⟨s, ?_, ?_⟩
      · rw [CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv (u0 i)) (u0 i),
            SimpleField.mul_inv_cancel _ h, mul_one]
      · calc u1 t = SimpleField.inv (u0 i) * (u0 i * u1 t) := by
                rw [← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv (u0 i)) (u0 i),
                    SimpleField.mul_inv_cancel _ h, CommRing.one_mul]
          _ = SimpleField.inv (u0 i) * (u1 i * u0 t) := by rw [heq]
          _ = s * u1 i := by
                rw [← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv (u0 i)) (u1 i),
                    CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv (u0 i)) (u0 t),
                    CommRing.mul_comm (u1 i) s]
    | inr h =>
      let s := u1 t * SimpleField.inv (u1 i)
      refine ⟨s, ?_, ?_⟩
      · calc u0 t = SimpleField.inv (u1 i) * (u1 i * u0 t) := by
                rw [← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv (u1 i)) (u1 i),
                    SimpleField.mul_inv_cancel _ h, CommRing.one_mul]
          _ = SimpleField.inv (u1 i) * (u0 i * u1 t) := by rw [← heq]
          _ = s * u0 i := by
                rw [← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv (u1 i)) (u0 i),
                    CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv (u1 i)) (u1 t),
                    CommRing.mul_comm (u0 i) s]
      · rw [CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv (u1 i)) (u1 i),
            SimpleField.mul_inv_cancel _ h, mul_one]
  obtain ⟨sj, hsj0, hsj1⟩ := hscale j hij
  obtain ⟨sk, hsk0, hsk1⟩ := hscale k hik
  -- Now 3 vectors in `F^2`: `w_i = (v0 i, v1 i)`, `w_j = (sj * v0 j, sj * v1 j)`, `w_k = (sk * v0 k, sk * v1 k)`
  -- are ALWAYS linearly dependent via the `2 × 2` determinant rule!
  let a0 := v0 i; let a1 := v1 i
  let b0 := sj * v0 j; let b1 := sj * v1 j
  let c0 := sk * v0 k; let c1 := sk * v1 k
  have hdep2 : ∃ α β γ : F, (α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0) ∧
      α * a0 + β * b0 + γ * c0 = 0 ∧ α * a1 + β * b1 + γ * c1 = 0 := by
    by_cases hbc : det2Pair b0 b1 c0 c1 ≠ 0
    · refine ⟨det2Pair b0 b1 c0 c1, det2Pair c0 c1 a0 a1, det2Pair a0 a1 b0 b1, Or.inl hbc, ?_, ?_⟩
      · unfold det2Pair
        simp only [right_distrib, CommRing.sub_eq, neg_mul]
        -- `b0*c1*a0 - b1*c0*a0 + c0*a1*b0 - c1*a0*b0 + a0*b1*c0 - a1*b0*c0 = 0`
        have e1 : b0 * c1 * a0 = c1 * a0 * b0 := by rw [CommRing.mul_assoc, CommRing.mul_comm b0]
        have e2 : b1 * c0 * a0 = a0 * b1 * c0 := by rw [CommRing.mul_comm (b1 * c0) a0, ← CommRing.mul_assoc]
        have e3 : c0 * a1 * b0 = a1 * b0 * c0 := by rw [CommRing.mul_assoc, CommRing.mul_comm c0]
        rw [e1, e2, e3]
        have z3 : ∀ x y z : F, ((x + -y) + (z + -x)) + (y + -z) = 0 := by
          intro x y z
          have s : ∀ r1 r2 r3 r4 : F, (r1 + r2) + (r3 + r4) = (r1 + r3) + (r2 + r4) := by
            intro r1 r2 r3 r4
            rw [CommRing.add_assoc, ← CommRing.add_assoc r2 r3 r4, CommRing.add_comm r2 r3,
                CommRing.add_assoc r3 r2 r4, ← CommRing.add_assoc]
          rw [CommRing.add_comm z (-x), s x (-y) (-x) z, CommRing.add_neg, CommRing.zero_add,
              s (-y) z y (-z), neg_add, CommRing.zero_add, CommRing.add_neg]
        exact z3 (c1 * a0 * b0) (a0 * b1 * c0) (a1 * b0 * c0)
      · unfold det2Pair
        simp only [right_distrib, CommRing.sub_eq, neg_mul]
        have e1 : b0 * c1 * a1 = a1 * b0 * c1 := by rw [CommRing.mul_comm (b0 * c1) a1, ← CommRing.mul_assoc]
        have e2 : b1 * c0 * a1 = c0 * a1 * b1 := by rw [CommRing.mul_assoc, CommRing.mul_comm b1]
        have e3 : c1 * a0 * b1 = a0 * b1 * c1 := by rw [CommRing.mul_comm c1 a0, CommRing.mul_assoc, CommRing.mul_comm c1 b1, ← CommRing.mul_assoc]
        rw [e1, e2, e3]
        have z3 : ∀ x y z : F, ((x + -y) + (y + -z)) + (z + -x) = 0 := by
          intro x y z
          have s : ∀ r1 r2 r3 r4 : F, (r1 + r2) + (r3 + r4) = (r1 + r3) + (r2 + r4) := by
            intro r1 r2 r3 r4
            rw [CommRing.add_assoc, ← CommRing.add_assoc r2 r3 r4, CommRing.add_comm r2 r3,
                CommRing.add_assoc r3 r2 r4, ← CommRing.add_assoc]
          rw [CommRing.add_comm y (-z), s x (-y) (-z) y, neg_add, add_zero,
              CommRing.add_comm x (-z), s (-z) x z (-x), neg_add, CommRing.zero_add, CommRing.add_neg]
        exact z3 (a1 * b0 * c1) (c0 * a1 * b1) (a0 * b1 * c1)
    · have hbc0 : det2Pair b0 b1 c0 c1 = 0 := Classical.byContradiction hbc
      by_cases hb0 : b0 ≠ 0
      · refine ⟨0, c0, -b0, Or.inr (Or.inr (fun h => hb0 (neg_eq_zero_iff.mp h))), ?_, ?_⟩
        · rw [zero_mul, CommRing.zero_add, neg_mul, CommRing.mul_comm c0 b0, CommRing.add_neg]
        · rw [zero_mul, CommRing.zero_add, neg_mul]
          have e := eq_of_sub_eq_zero hbc0
          rw [CommRing.mul_comm c0 b1, ← e, CommRing.mul_comm b0 c1, CommRing.add_neg]
      · have hb0' : b0 = 0 := Classical.byContradiction hb0
        by_cases hb1 : b1 ≠ 0
        · refine ⟨0, c1, -b1, Or.inr (Or.inr (fun h => hb1 (neg_eq_zero_iff.mp h))), ?_, ?_⟩
          · have e := eq_of_sub_eq_zero hbc0
            rw [hb0', zero_mul] at e
            cases field_mul_eq_zero e.symm with
            | inl h => exact absurd h hb1
            | inr hc0 => rw [zero_mul, hb0', mul_zero, hc0, mul_zero, add_zero, add_zero]
          · rw [zero_mul, CommRing.zero_add, neg_mul, CommRing.mul_comm c1 b1, CommRing.add_neg]
        · have hb1' : b1 = 0 := Classical.byContradiction hb1
          exact ⟨0, 1, 0, Or.inr (Or.inl (Ne.symm SimpleField.zero_ne_one)),
                 by rw [hb0', zero_mul, mul_zero, zero_mul, add_zero, add_zero],
                 by rw [hb1', zero_mul, mul_zero, zero_mul, add_zero, add_zero]⟩
  obtain ⟨α, β, γ, hne, he0, he1⟩ := hdep2
  refine ⟨α, β, γ, hne, ?_, ?_, ?_, ?_⟩
  · have hfac : α * (u0 i * v0 i) + β * (u0 j * v0 j) + γ * (u0 k * v0 k) = u0 i * (α * a0 + β * b0 + γ * c0) := by
      rw [hsj0, hsk0]; dsimp only [a0, b0, c0]
      simp only [CommRing.left_distrib, CommRing.mul_assoc]
      have f1 : α * (u0 i * v0 i) = u0 i * (α * v0 i) := by rw [← CommRing.mul_assoc, CommRing.mul_comm α (u0 i), CommRing.mul_assoc]
      have f2 : β * (sj * (u0 i * v0 j)) = u0 i * (β * (sj * v0 j)) := by
        rw [← CommRing.mul_assoc sj (u0 i), CommRing.mul_comm sj (u0 i), CommRing.mul_assoc (u0 i) sj,
            ← CommRing.mul_assoc β (u0 i), CommRing.mul_comm β (u0 i), CommRing.mul_assoc (u0 i) β]
      have f3 : γ * (sk * (u0 i * v0 k)) = u0 i * (γ * (sk * v0 k)) := by
        rw [← CommRing.mul_assoc sk (u0 i), CommRing.mul_comm sk (u0 i), CommRing.mul_assoc (u0 i) sk,
            ← CommRing.mul_assoc γ (u0 i), CommRing.mul_comm γ (u0 i), CommRing.mul_assoc (u0 i) γ]
      rw [f1, f2, f3]
    rw [hfac, he0, mul_zero]
  · have hfac : α * (u0 i * v1 i) + β * (u0 j * v1 j) + γ * (u0 k * v1 k) = u0 i * (α * a1 + β * b1 + γ * c1) := by
      rw [hsj0, hsk0]; dsimp only [a1, b1, c1]
      simp only [CommRing.left_distrib, CommRing.mul_assoc]
      have f1 : α * (u0 i * v1 i) = u0 i * (α * v1 i) := by rw [← CommRing.mul_assoc, CommRing.mul_comm α (u0 i), CommRing.mul_assoc]
      have f2 : β * (sj * (u0 i * v1 j)) = u0 i * (β * (sj * v1 j)) := by
        rw [← CommRing.mul_assoc sj (u0 i), CommRing.mul_comm sj (u0 i), CommRing.mul_assoc (u0 i) sj,
            ← CommRing.mul_assoc β (u0 i), CommRing.mul_comm β (u0 i), CommRing.mul_assoc (u0 i) β]
      have f3 : γ * (sk * (u0 i * v1 k)) = u0 i * (γ * (sk * v1 k)) := by
        rw [← CommRing.mul_assoc sk (u0 i), CommRing.mul_comm sk (u0 i), CommRing.mul_assoc (u0 i) sk,
            ← CommRing.mul_assoc γ (u0 i), CommRing.mul_comm γ (u0 i), CommRing.mul_assoc (u0 i) γ]
      rw [f1, f2, f3]
    rw [hfac, he1, mul_zero]
  · have hfac : α * (u1 i * v0 i) + β * (u1 j * v0 j) + γ * (u1 k * v0 k) = u1 i * (α * a0 + β * b0 + γ * c0) := by
      rw [hsj1, hsk1]; dsimp only [a0, b0, c0]
      simp only [CommRing.left_distrib, CommRing.mul_assoc]
      have f1 : α * (u1 i * v0 i) = u1 i * (α * v0 i) := by rw [← CommRing.mul_assoc, CommRing.mul_comm α (u1 i), CommRing.mul_assoc]
      have f2 : β * (sj * (u1 i * v0 j)) = u1 i * (β * (sj * v0 j)) := by
        rw [← CommRing.mul_assoc sj (u1 i), CommRing.mul_comm sj (u1 i), CommRing.mul_assoc (u1 i) sj,
            ← CommRing.mul_assoc β (u1 i), CommRing.mul_comm β (u1 i), CommRing.mul_assoc (u1 i) β]
      have f3 : γ * (sk * (u1 i * v0 k)) = u1 i * (γ * (sk * v0 k)) := by
        rw [← CommRing.mul_assoc sk (u1 i), CommRing.mul_comm sk (u1 i), CommRing.mul_assoc (u1 i) sk,
            ← CommRing.mul_assoc γ (u1 i), CommRing.mul_comm γ (u1 i), CommRing.mul_assoc (u1 i) γ]
      rw [f1, f2, f3]
    rw [hfac, he0, mul_zero]
  · have hfac : α * (u1 i * v1 i) + β * (u1 j * v1 j) + γ * (u1 k * v1 k) = u1 i * (α * a1 + β * b1 + γ * c1) := by
      rw [hsj1, hsk1]; dsimp only [a1, b1, c1]
      simp only [CommRing.left_distrib, CommRing.mul_assoc]
      have f1 : α * (u1 i * v1 i) = u1 i * (α * v1 i) := by rw [← CommRing.mul_assoc, CommRing.mul_comm α (u1 i), CommRing.mul_assoc]
      have f2 : β * (sj * (u1 i * v1 j)) = u1 i * (β * (sj * v1 j)) := by
        rw [← CommRing.mul_assoc sj (u1 i), CommRing.mul_comm sj (u1 i), CommRing.mul_assoc (u1 i) sj,
            ← CommRing.mul_assoc β (u1 i), CommRing.mul_comm β (u1 i), CommRing.mul_assoc (u1 i) β]
      have f3 : γ * (sk * (u1 i * v1 k)) = u1 i * (γ * (sk * v1 k)) := by
        rw [← CommRing.mul_assoc sk (u1 i), CommRing.mul_comm sk (u1 i), CommRing.mul_assoc (u1 i) sk,
            ← CommRing.mul_assoc γ (u1 i), CommRing.mul_comm γ (u1 i), CommRing.mul_assoc (u1 i) γ]
      rw [f1, f2, f3]
    rw [hfac, he1, mul_zero]

/-- **Max-Clique ≤ 2 Lemma:** Three linearly independent rank-1 `2 × 2` matrices CANNOT pairwise satisfy
`det(u_p, u_q) = 0 ∨ det(v_p, v_q) = 0` over ANY `SimpleField F`! -/
theorem no_three_clique_rank1 {F : Type} [SimpleField F]
    (u0 u1 v0 v1 : Nat → F) (i j k : Nat)
    (hui : u0 i ≠ 0 ∨ u1 i ≠ 0) (huj : u0 j ≠ 0 ∨ u1 j ≠ 0)
    (hvi : v0 i ≠ 0 ∨ v1 i ≠ 0) (hvj : v0 j ≠ 0 ∨ v1 j ≠ 0)
    (hij : det2Pair (u0 i) (u1 i) (u0 j) (u1 j) = 0 ∨ det2Pair (v0 i) (v1 i) (v0 j) (v1 j) = 0)
    (hik : det2Pair (u0 i) (u1 i) (u0 k) (u1 k) = 0 ∨ det2Pair (v0 i) (v1 i) (v0 k) (v1 k) = 0)
    (hjk : det2Pair (u0 j) (u1 j) (u0 k) (u1 k) = 0 ∨ det2Pair (v0 j) (v1 j) (v0 k) (v1 k) = 0)
    (hind : ∀ α β γ : F,
      α * (u0 i * v0 i) + β * (u0 j * v0 j) + γ * (u0 k * v0 k) = 0 →
      α * (u0 i * v1 i) + β * (u0 j * v1 j) + γ * (u0 k * v1 k) = 0 →
      α * (u1 i * v0 i) + β * (u1 j * v0 j) + γ * (u1 k * v0 k) = 0 →
      α * (u1 i * v1 i) + β * (u1 j * v1 j) + γ * (u1 k * v1 k) = 0 →
      α = 0 ∧ β = 0 ∧ γ = 0) : False := by
  have killL : det2Pair (u0 i) (u1 i) (u0 j) (u1 j) = 0 →
      det2Pair (u0 i) (u1 i) (u0 k) (u1 k) = 0 → False := by
    intro h1 h2
    obtain ⟨α, β, γ, hne, e0, e1, e2, e3⟩ := rank1_three_dep_left u0 u1 v0 v1 i j k hui h1 h2
    obtain ⟨rfl, rfl, rfl⟩ := hind α β γ e0 e1 e2 e3
    rcases hne with h | h | h <;> exact h rfl
  have killR : det2Pair (v0 i) (v1 i) (v0 j) (v1 j) = 0 →
      det2Pair (v0 i) (v1 i) (v0 k) (v1 k) = 0 → False := by
    intro h1 h2
    obtain ⟨α, β, γ, hne, e0, e1, e2, e3⟩ := rank1_three_dep_left v0 v1 u0 u1 i j k hvi h1 h2
    have c : ∀ x y : F, x * y = y * x := CommRing.mul_comm
    obtain ⟨rfl, rfl, rfl⟩ := hind α β γ
      (by simpa only [c (u0 _)] using e0)
      (by simpa only [c (u0 _)] using e2)
      (by simpa only [c (u1 _)] using e1)
      (by simpa only [c (u1 _)] using e3)
    rcases hne with h | h | h <;> exact h rfl
  cases hij with
  | inl huij =>
    cases hik with
    | inl huik => exact killL huij huik
    | inr hvik =>
      cases hjk with
      | inl hujk => exact killL huij (det2Pair_trans huj huij hujk)
      | inr hvjk =>
        have hvkj : det2Pair (v0 k) (v1 k) (v0 j) (v1 j) = 0 := by
          unfold det2Pair at hvjk ⊢
          have e := eq_of_sub_eq_zero hvjk
          rw [CommRing.mul_comm (v0 k) (v1 j), ← e, CommRing.mul_comm (v0 j) (v1 k), sub_self]
        --Wait: need `v k ≠ 0`? Actually if `v0 k = 0 ∧ v1 k = 0`, then `α=0, β=0, γ=1` kills `hind` immediately!
        by_cases hvk : v0 k ≠ 0 ∨ v1 k ≠ 0
        · exact killR (det2Pair_trans hvk hvik hvkj) hvik
        · have hv0k : v0 k = 0 := Classical.byContradiction (fun h => hvk (Or.inl h))
          have hv1k : v1 k = 0 := Classical.byContradiction (fun h => hvk (Or.inr h))
          have ⟨_, _, h10⟩ := hind 0 0 1
            (by rw [zero_mul, zero_mul, hv0k, mul_zero, mul_zero, add_zero, add_zero])
            (by rw [zero_mul, zero_mul, hv1k, mul_zero, mul_zero, add_zero, add_zero])
            (by rw [zero_mul, zero_mul, hv0k, mul_zero, mul_zero, add_zero, add_zero])
            (by rw [zero_mul, zero_mul, hv1k, mul_zero, mul_zero, add_zero, add_zero])
          exact SimpleField.zero_ne_one h10.symm
  | inr hvij =>
    cases hik with
    | inr hvik => exact killR hvij hvik
    | inl huik =>
      cases hjk with
      | inr hvjk => exact killR hvij (det2Pair_trans hvj hvij hvjk)
      | inl hujk =>
        have hukj : det2Pair (u0 k) (u1 k) (u0 j) (u1 j) = 0 := by
          unfold det2Pair at hujk ⊢
          have e := eq_of_sub_eq_zero hujk
          rw [CommRing.mul_comm (u0 k) (u1 j), ← e, CommRing.mul_comm (u0 j) (u1 k), sub_self]
        by_cases huk : u0 k ≠ 0 ∨ u1 k ≠ 0
        · exact killL (det2Pair_trans huk huik hukj) huik
        · have hu0k : u0 k = 0 := Classical.byContradiction (fun h => huk (Or.inl h))
          have hu1k : u1 k = 0 := Classical.byContradiction (fun h => huk (Or.inr h))
          have ⟨_, _, h10⟩ := hind 0 0 1
            (by rw [zero_mul, zero_mul, hu0k, zero_mul, mul_zero, add_zero, add_zero])
            (by rw [zero_mul, zero_mul, hu0k, zero_mul, mul_zero, add_zero, add_zero])
            (by rw [zero_mul, zero_mul, hu1k, zero_mul, mul_zero, add_zero, add_zero])
            (by rw [zero_mul, zero_mul, hu1k, zero_mul, mul_zero, add_zero, add_zero])
          exact SimpleField.zero_ne_one h10.symm

-- ============================================================================
-- Section 4: `2 × 2` Cramer Row/Column Kill & `4 × 6` Gauss-Jordan RREF
-- ============================================================================

/-- If `sliceM (u v^T) = W1 V1^T + (c * W5) V5^T` with `u ≠ 0, v ≠ 0, c ≠ 0`, then `V5` satisfies
the row-space relations `v1 * V5 0 = v0 * V5 2` and `v1 * V5 1 = v0 * V5 3`, AND `W5` satisfies
the column-space relations `u1 * W5 0 = u0 * W5 2` and `u1 * W5 1 = u0 * W5 3`! -/
theorem row_col_constraints_of_rank2_sum {F : Type} [SimpleField F]
    (u0 u1 v0 v1 c : F) (W1 V1 W5 V5 : Nat → F)
    (hu : u0 ≠ 0 ∨ u1 ≠ 0) (hv : v0 ≠ 0 ∨ v1 ≠ 0) (hc : c ≠ 0)
    (hsum : ∀ r b, r < 4 → b < 4 →
      sliceM (fun a => match a with | 0 => u0 * v0 | 1 => u0 * v1 | 2 => u1 * v0 | _ => u1 * v1) r b =
      W1 r * V1 b + c * (W5 r * V5 b)) :
    (v1 * V5 0 = v0 * V5 2 ∧ v1 * V5 1 = v0 * V5 3) ∧
    (u1 * W5 0 = u0 * W5 2 ∧ u1 * W5 1 = u0 * W5 3) := by
  let X : Nat → F := fun a => match a with | 0 => u0 * v0 | 1 => u0 * v1 | 2 => u1 * v0 | _ => u1 * v1
  have hX := sliceM_eval X
  -- Every row `r < 4` satisfies `v1 * sliceM X r 0 = v0 * sliceM X r 2` and `v1 * sliceM X r 1 = v0 * sliceM X r 3`!
  have hrow_rel : ∀ r, r < 4 →
      v1 * sliceM X r 0 = v0 * sliceM X r 2 ∧ v1 * sliceM X r 1 = v0 * sliceM X r 3 := by
    have hv_comm : ∀ u : F, v1 * (u * v0) = v0 * (u * v1) := by
      intro u
      rw [← CommRing.mul_assoc, CommRing.mul_comm v1 u, CommRing.mul_assoc, CommRing.mul_comm v1 v0,
          ← CommRing.mul_assoc, CommRing.mul_comm u v0, CommRing.mul_assoc]
    intro r hr
    have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr4 with rfl | rfl | rfl | rfl
    · rw [hX.1.1, hX.1.2.2.1, hX.1.2.1, hX.1.2.2.2]; exact ⟨hv_comm u0, by rw [mul_zero, mul_zero]⟩
    · rw [hX.2.1.1, hX.2.1.2.2.1, hX.2.1.2.1, hX.2.1.2.2.2]; exact ⟨by rw [mul_zero, mul_zero], hv_comm u0⟩
    · rw [hX.2.2.1.1, hX.2.2.1.2.2.1, hX.2.2.1.2.1, hX.2.2.1.2.2.2]; exact ⟨hv_comm u1, by rw [mul_zero, mul_zero]⟩
    · rw [hX.2.2.2.1, hX.2.2.2.2.2.1, hX.2.2.2.2.1, hX.2.2.2.2.2.2]; exact ⟨by rw [mul_zero, mul_zero], hv_comm u1⟩
  have hcol_rel : ∀ b, b < 4 →
      u1 * sliceM X 0 b = u0 * sliceM X 2 b ∧ u1 * sliceM X 1 b = u0 * sliceM X 3 b := by
    have hu_comm : ∀ v : F, u1 * (u0 * v) = u0 * (u1 * v) := by
      intro v; rw [← CommRing.mul_assoc, CommRing.mul_comm u1 u0, CommRing.mul_assoc]
    intro b hb
    have hb4 : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
    rcases hb4 with rfl | rfl | rfl | rfl
    · rw [hX.1.1, hX.2.2.1.1, hX.2.1.1, hX.2.2.2.1]; exact ⟨hu_comm v0, by rw [mul_zero, mul_zero]⟩
    · rw [hX.1.2.1, hX.2.2.1.2.1, hX.2.1.2.1, hX.2.2.2.2.1]; exact ⟨by rw [mul_zero, mul_zero], hu_comm v0⟩
    · rw [hX.1.2.2.1, hX.2.2.1.2.2.1, hX.2.1.2.2.1, hX.2.2.2.2.2.1]; exact ⟨hu_comm v1, by rw [mul_zero, mul_zero]⟩
    · rw [hX.1.2.2.2, hX.2.2.1.2.2.2, hX.2.1.2.2.2, hX.2.2.2.2.2.2]; exact ⟨by rw [mul_zero, mul_zero], hu_comm v1⟩
  -- Pick `(r0, s0)` with `u_{r0} ≠ 0` and `v_{s0} ≠ 0` so the `2×2` block `(2r0, 2r0+1) × (2s0, 2s0+1)` is `λ I_2` (`λ ≠ 0`)!
  obtain ⟨r0, hr0_lt, hur0⟩ : ∃ r0, r0 < 2 ∧ (if r0 = 0 then u0 else u1) ≠ 0 := by
    cases hu with | inl h => exact ⟨0, by omega, h⟩ | inr h => exact ⟨1, by omega, h⟩
  obtain ⟨s0, hs0_lt, hvs0⟩ : ∃ s0, s0 < 2 ∧ (if s0 = 0 then v0 else v1) ≠ 0 := by
    cases hv with | inl h => exact ⟨0, by omega, h⟩ | inr h => exact ⟨1, by omega, h⟩
  let rA := 2 * r0; let rB := 2 * r0 + 1
  let bA := 2 * s0; let bB := 2 * s0 + 1
  let lam := (if r0 = 0 then u0 else u1) * (if s0 = 0 then v0 else v1)
  have hlam : lam ≠ 0 := field_mul_ne_zero hur0 hvs0
  have hblk : sliceM X rA bA = lam ∧ sliceM X rA bB = 0 ∧ sliceM X rB bA = 0 ∧ sliceM X rB bB = lam := by
    have hr2 : r0 = 0 ∨ r0 = 1 := by omega
    have hs2 : s0 = 0 ∨ s0 = 1 := by omega
    rcases hr2 with rfl | rfl <;> rcases hs2 with rfl | rfl
    · exact ⟨hX.1.1, hX.1.2.1, hX.2.1.1, hX.2.1.2.1⟩
    · exact ⟨hX.1.2.2.1, hX.1.2.2.2, hX.2.1.2.2.1, hX.2.1.2.2.2⟩
    · exact ⟨hX.2.2.1.1, hX.2.2.1.2.1, hX.2.2.2.1, hX.2.2.2.2.1⟩
    · exact ⟨hX.2.2.1.2.2.1, hX.2.2.1.2.2.2, hX.2.2.2.2.2.1, hX.2.2.2.2.2.2⟩
  -- Express the `2×2` block as `A · B = lam * I_2`:
  -- `det(A) * det(B) = det(lam * I_2) = lam^2 ≠ 0`!
  let detA := W1 rA * (c * W5 rB) - (c * W5 rA) * W1 rB
  let detB := V1 bA * V5 bB - V1 bB * V5 bA
  have hdetAB : detA * detB = lam * lam := by
    have e1 := hsum rA bA (by omega) (by omega)
    have e2 := hsum rA bB (by omega) (by omega)
    have e3 := hsum rB bA (by omega) (by omega)
    have e4 := hsum rB bB (by omega) (by omega)
    rw [hblk.1] at e1; rw [hblk.2.1] at e2; rw [hblk.2.2.1] at e3; rw [hblk.2.2.2] at e4
    -- `lam * lam = lam * lam - 0 * 0 = e1*e4 - e2*e3 = detA * detB` (Binet-Cauchy for `2×2`!)
    have hbc2 : ∀ a11 a12 a21 a22 x11 x12 x21 x22 : F,
        (a11 * x11 + a12 * x21) * (a21 * x12 + a22 * x22) -
        (a11 * x12 + a12 * x22) * (a21 * x11 + a22 * x21) =
        (a11 * a22 - a12 * a21) * (x11 * x22 - x12 * x21) := by
      intro a11 a12 a21 a22 x11 x12 x21 x22
      have h := det2_rank1_comb (1 : F) 1 a11 a21 x11 x12 a12 a22 x21 x22
      simp only [CommRing.one_mul, det2Pair] at h
      -- Wait: `a11*x11 + a12*x21`, etc. Notice `h` has `(a11*x11 + a12*x21)*(a21*x12 + a22*x22) - (a11*x12 + a12*x22)*(a21*x11 + a22*x21) = (a11*a22 - a21*a12)*(x11*x22 - x12*x21)`!
      rw [CommRing.mul_comm a21 a12] at h
      exact h
    have hprod := hbc2 (W1 rA) (c * W5 rA) (W1 rB) (c * W5 rB) (V1 bA) (V1 bB) (V5 bA) (V5 bB)
    have c1 : c * (W5 rA * V5 bA) = c * W5 rA * V5 bA := (CommRing.mul_assoc ..).symm
    have c2 : c * (W5 rA * V5 bB) = c * W5 rA * V5 bB := (CommRing.mul_assoc ..).symm
    have c3 : c * (W5 rB * V5 bA) = c * W5 rB * V5 bA := (CommRing.mul_assoc ..).symm
    have c4 : c * (W5 rB * V5 bB) = c * W5 rB * V5 bB := (CommRing.mul_assoc ..).symm
    rw [c1] at e1; rw [c2] at e2; rw [c3] at e3; rw [c4] at e4
    rw [← e1, ← e2, ← e3, ← e4, mul_zero, CommRing.sub_eq, neg_zero, add_zero] at hprod
    exact hprod.symm
  have hdetA_ne : detA ≠ 0 := by
    intro hz; rw [hz, zero_mul] at hdetAB; exact field_mul_ne_zero hlam hlam hdetAB.symm
  have hdetB_ne : detB ≠ 0 := by
    intro hz; rw [hz, mul_zero] at hdetAB; exact field_mul_ne_zero hlam hlam hdetAB.symm
  -- Helper: eliminate `W1` across rows `rA, rB` to isolate `detA * V5 b`!
  have hisoV : ∀ b, b < 4 →
      detA * V5 b = W1 rA * sliceM X rB b - W1 rB * sliceM X rA b := by
    intro b hb
    rw [hsum rB b (by omega) hb, hsum rA b (by omega) hb]
    dsimp only [detA]
    simp only [CommRing.left_distrib, right_distrib, CommRing.sub_eq, CommRing.mul_assoc, neg_add_distrib, neg_mul]
    have h1 : W1 rA * (c * (W5 rB * V5 b)) = W1 rA * (c * (W5 rB * V5 b)) := rfl
    have h2 : -(W1 rB * (c * (W5 rA * V5 b))) = -(c * (W5 rA * (W1 rB * V5 b))) := by
      congr 1
      calc W1 rB * (c * (W5 rA * V5 b))
          = (W1 rB * (c * W5 rA)) * V5 b := by rw [← CommRing.mul_assoc c, ← CommRing.mul_assoc]
        _ = (c * W5 rA * W1 rB) * V5 b := by rw [CommRing.mul_comm (W1 rB) (c * W5 rA)]
        _ = c * (W5 rA * (W1 rB * V5 b)) := by rw [CommRing.mul_assoc (c * W5 rA), CommRing.mul_assoc c]
    have hneg_eq : -(W1 rB * (W1 rA * V1 b)) = -(W1 rA * (W1 rB * V1 b)) := by
      congr 1
      rw [← CommRing.mul_assoc, CommRing.mul_comm (W1 rB) (W1 rA), CommRing.mul_assoc]
    have rearr : ∀ p q s : F, (p + q) + (-p + s) = q + s := by
      intro p q s
      rw [CommRing.add_assoc, ← CommRing.add_assoc q (-p) s, CommRing.add_comm q (-p),
          CommRing.add_assoc (-p) q s, ← CommRing.add_assoc, CommRing.add_neg, CommRing.zero_add]
    rw [hneg_eq, h2, rearr]
  -- Helper: eliminate `V1` across cols `bA, bB` to isolate `(c * detB) * W5 r`!
  have hisoW : ∀ r, r < 4 →
      (c * detB) * W5 r = V1 bA * sliceM X r bB - V1 bB * sliceM X r bA := by
    intro r hr
    rw [hsum r bB hr (by omega), hsum r bA hr (by omega)]
    dsimp only [detB]
    simp only [CommRing.left_distrib, right_distrib, CommRing.sub_eq, CommRing.mul_assoc, neg_add_distrib, neg_mul, mul_neg]
    have hneg_eq : -(V1 bB * (W1 r * V1 bA)) = -(V1 bA * (W1 r * V1 bB)) := by
      congr 1
      calc V1 bB * (W1 r * V1 bA)
          = (V1 bB * V1 bA) * W1 r := by rw [CommRing.mul_comm (W1 r) (V1 bA), ← CommRing.mul_assoc]
        _ = (V1 bA * V1 bB) * W1 r := by rw [CommRing.mul_comm (V1 bB) (V1 bA)]
        _ = V1 bA * (W1 r * V1 bB) := by rw [CommRing.mul_assoc, CommRing.mul_comm (V1 bB) (W1 r)]
    have h1 : V1 bA * (c * (W5 r * V5 bB)) = c * (V1 bA * (V5 bB * W5 r)) := by
      rw [← CommRing.mul_assoc (V1 bA) c, CommRing.mul_comm (V1 bA) c,
          CommRing.mul_assoc c (V1 bA), CommRing.mul_comm (W5 r) (V5 bB)]
    have h2 : -(V1 bB * (c * (W5 r * V5 bA))) = -(c * (V1 bB * (V5 bA * W5 r))) := by
      congr 1
      rw [← CommRing.mul_assoc (V1 bB) c, CommRing.mul_comm (V1 bB) c,
          CommRing.mul_assoc c (V1 bB), CommRing.mul_comm (W5 r) (V5 bA)]
    rw [hneg_eq, h1, h2]
    have rearr : ∀ p q s : F, (p + q) + (-p + s) = q + s := by
      intro p q s
      rw [CommRing.add_assoc, ← CommRing.add_assoc q (-p) s, CommRing.add_comm q (-p),
          CommRing.add_assoc (-p) q s, ← CommRing.add_assoc, CommRing.add_neg, CommRing.zero_add]
    rw [rearr]
  -- Deduce `v1 * V5 0 = v0 * V5 2` and `v1 * V5 1 = v0 * V5 3` by cancelling `detA ≠ 0`!
  have hcancel_left : ∀ d x y : F, d ≠ 0 → d * x = d * y → x = y := by
    intro d x y hd hxy
    have h := congrArg (fun z => SimpleField.inv d * z) hxy
    rw [← CommRing.mul_assoc, ← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv d) d,
        SimpleField.mul_inv_cancel d hd, CommRing.one_mul, CommRing.one_mul] at h
    exact h
  have hV_rel : ∀ idx : Nat, idx < 2 → v1 * V5 idx = v0 * V5 (idx + 2) := by
    intro idx hidx
    apply hcancel_left detA _ _ hdetA_ne
    have hl : detA * (v1 * V5 idx) = v1 * (detA * V5 idx) := by
      rw [← CommRing.mul_assoc, CommRing.mul_comm detA v1, CommRing.mul_assoc]
    have hr : detA * (v0 * V5 (idx + 2)) = v0 * (detA * V5 (idx + 2)) := by
      rw [← CommRing.mul_assoc, CommRing.mul_comm detA v0, CommRing.mul_assoc]
    rw [hl, hr, hisoV idx (by omega), hisoV (idx + 2) (by omega), mul_sub_r, mul_sub_r]
    have hrB := hrow_rel rB (by omega)
    have hrA := hrow_rel rA (by omega)
    have hsw : ∀ a b c' : F, a * (b * c') = b * (a * c') := by
      intro a b c'; rw [← CommRing.mul_assoc, CommRing.mul_comm a b, CommRing.mul_assoc]
    rw [hsw v1 (W1 rA), hsw v1 (W1 rB), hsw v0 (W1 rA), hsw v0 (W1 rB)]
    have h2 : idx = 0 ∨ idx = 1 := by omega
    rcases h2 with rfl | rfl
    · rw [hrB.1, hrA.1]
    · rw [hrB.2, hrA.2]
  have hcdetB_ne : c * detB ≠ 0 := field_mul_ne_zero hc hdetB_ne
  have hW_rel : ∀ idx : Nat, idx < 2 → u1 * W5 idx = u0 * W5 (idx + 2) := by
    intro idx hidx
    apply hcancel_left (c * detB) _ _ hcdetB_ne
    have hl : (c * detB) * (u1 * W5 idx) = u1 * ((c * detB) * W5 idx) := by
      rw [← CommRing.mul_assoc, CommRing.mul_comm (c * detB) u1, CommRing.mul_assoc]
    have hr : (c * detB) * (u0 * W5 (idx + 2)) = u0 * ((c * detB) * W5 (idx + 2)) := by
      rw [← CommRing.mul_assoc, CommRing.mul_comm (c * detB) u0, CommRing.mul_assoc]
    rw [hl, hr, hisoW idx (by omega), hisoW (idx + 2) (by omega), mul_sub_r, mul_sub_r]
    have hcB := hcol_rel bB (by omega)
    have hcA := hcol_rel bA (by omega)
    have hsw : ∀ a b c' : F, a * (b * c') = b * (a * c') := by
      intro a b c'; rw [← CommRing.mul_assoc, CommRing.mul_comm a b, CommRing.mul_assoc]
    rw [hsw u1 (V1 bA), hsw u1 (V1 bB), hsw u0 (V1 bA), hsw u0 (V1 bB)]
    have h2 : idx = 0 ∨ idx = 1 := by omega
    rcases h2 with rfl | rfl
    · rw [hcB.1, hcA.1]
    · rw [hcB.2, hcA.2]
  exact ⟨⟨hV_rel 0 (by omega), hV_rel 1 (by omega)⟩, ⟨hW_rel 0 (by omega), hW_rel 1 (by omega)⟩⟩

/-- Cramer's 2×2 kill: if `a1 * x = a0 * y` and `b1 * x = b0 * y` with `det2Pair a0 a1 b0 b1 ≠ 0`, then `x = 0 ∧ y = 0`. -/
theorem cramer2_zero {F : Type} [SimpleField F] {a0 a1 b0 b1 x y : F}
    (hdet : det2Pair a0 a1 b0 b1 ≠ 0) (h1 : a1 * x = a0 * y) (h2 : b1 * x = b0 * y) :
    x = 0 ∧ y = 0 := by
  have hx : det2Pair a0 a1 b0 b1 * x = 0 := by
    unfold det2Pair
    rw [sub_mul_r]
    have t1 : a0 * b1 * x = a0 * (b0 * y) := by rw [CommRing.mul_assoc, h2]
    have t2 : a1 * b0 * x = a0 * (b0 * y) := by
      rw [CommRing.mul_comm a1 b0, CommRing.mul_assoc, h1, ← CommRing.mul_assoc,
          CommRing.mul_comm b0 a0, CommRing.mul_assoc]
    rw [t1, t2, sub_self]
  have hy : det2Pair a0 a1 b0 b1 * y = 0 := by
    unfold det2Pair
    rw [sub_mul_r]
    have t1 : a0 * b1 * y = b1 * (a1 * x) := by
      rw [CommRing.mul_comm a0 b1, CommRing.mul_assoc, ← h1]
    have t2 : a1 * b0 * y = b1 * (a1 * x) := by
      rw [CommRing.mul_assoc, ← h2, ← CommRing.mul_assoc, CommRing.mul_comm a1 b1, CommRing.mul_assoc]
    rw [t1, t2, sub_self]
  exact ⟨(field_mul_eq_zero hx).resolve_left hdet, (field_mul_eq_zero hy).resolve_left hdet⟩

-- ============================================================================
-- Section 5: Elementary `4 × 6` Gauss-Jordan Row Reduction & Winograd Lower Bound
-- ============================================================================

def swapNat (a b x : Nat) : Nat :=
  if x = a then b else if x = b then a else x

theorem swapNat_invol (a b x : Nat) : swapNat a b (swapNat a b x) = x := by
  unfold swapNat
  by_cases hxa : x = a
  · rw [hxa]; by_cases hab : a = b <;> simp [hab, Ne.symm]
  · by_cases hxb : x = b
    · rw [hxb] at hxa ⊢; simp [hxa]
    · simp [hxa, hxb]

theorem swapNat_lt {n a b x : Nat} (ha : a < n) (hb : b < n) (hx : x < n) : swapNat a b x < n := by
  unfold swapNat
  split
  · exact hb
  · split
    · exact ha
    · exact hx

theorem sumR_perm_swap {R : Type} [CommRing R] (n a b : Nat) (f : Nat → R) (ha : a < n) (hb : b < n) :
    sumR n (fun s => f (swapNat a b s)) = sumR n f := by
  by_cases hab : a = b
  · subst hab
    apply sumR_congr
    intro s _
    unfold swapNat
    by_cases hsa : s = a <;> simp [hsa]
  · -- Extract `a`, then `b`, compare termwise!
    have haux : ∀ k : Nat, sumR k (fun s => f (swapNat a b s)) - sumR k f =
        (if a < k then f b - f a else 0) + (if b < k then f a - f b else 0) := by
      intro k
      induction k with
      | zero => simp [sumR, sub_self, add_zero]
      | succ m ih =>
        simp only [sumR]
        have hdiff : (sumR m (fun s => f (swapNat a b s)) + f (swapNat a b m)) - (sumR m f + f m) =
            (sumR m (fun s => f (swapNat a b s)) - sumR m f) + (f (swapNat a b m) - f m) := by
          simp only [CommRing.sub_eq, neg_add_distrib]
          have s : ∀ r1 r2 r3 r4 : R, (r1 + r2) + (r3 + r4) = (r1 + r3) + (r2 + r4) := by
            intro r1 r2 r3 r4
            rw [CommRing.add_assoc, ← CommRing.add_assoc r2 r3 r4, CommRing.add_comm r2 r3,
                CommRing.add_assoc r3 r2 r4, ← CommRing.add_assoc]
          exact s ..
        rw [hdiff, ih]
        by_cases hma : m = a
        · rw [hma]
          have h1 : ¬ (a < a) := Nat.lt_irrefl a
          have h2 : a < a + 1 := Nat.lt_succ_self a
          have h3 : (b < a + 1) ↔ (b < a) := by omega
          have hsw : swapNat a b a = b := by simp [swapNat]
          simp only [h1, h2, h3, hsw, ↓reduceIte, CommRing.zero_add, CommRing.add_comm]
        · by_cases hmb : m = b
          · rw [hmb]
            have h1 : ¬ (b < b) := Nat.lt_irrefl b
            have h2 : b < b + 1 := Nat.lt_succ_self b
            have h3 : (a < b + 1) ↔ (a < b) := by omega
            have hsw : swapNat a b b = a := by simp [swapNat, Ne.symm hab]
            simp only [h1, h2, h3, hsw, ↓reduceIte, add_zero]
          · have h1 : (a < m + 1) ↔ (a < m) := by omega
            have h2 : (b < m + 1) ↔ (b < m) := by omega
            have hsw : swapNat a b m = m := by simp [swapNat, hma, hmb]
            simp only [h1, h2, hsw, sub_self, add_zero]
    have h0 := haux n
    simp only [ha, hb, ↓reduceIte, CommRing.sub_eq] at h0
    have hcancel : (f b + -f a) + (f a + -f b) = 0 := by
      rw [CommRing.add_assoc, ← CommRing.add_assoc (-f a) (f a), neg_add, CommRing.zero_add, CommRing.add_neg]
    rw [hcancel, ← CommRing.sub_eq] at h0
    exact eq_of_sub_eq_zero h0

/-- Row-reduced echelon form for 4 linearly independent rows in `F^6` (inductive over pivot `k ≤ 4`). -/
theorem rref_4x6 {F : Type} [SimpleField F] (U : Nat → Nat → F)
    (hinj : ∀ X : Nat → F, (∀ s, s < 6 → sumR 4 (fun a => X a * U s a) = 0) → ∀ a, a < 4 → X a = 0) :
    ∃ (M : Nat → Nat → F) (π : Nat → Nat),
      (∀ s, s < 6 → π s < 6) ∧
      (∀ f : Nat → F, sumR 6 (fun s => f (π s)) = sumR 6 f) ∧
      (∀ α : Nat → F, (∀ a, a < 4 → sumR 4 (fun i => α i * M i a) = 0) → ∀ i, i < 4 → α i = 0) ∧
      (∀ i j, i < 4 → j < 4 → sumR 4 (fun a => M i a * U (π j) a) = if i = j then 1 else 0) := by
  -- Induction on `k ≤ 4`: after `k` pivots, columns `π 0 .. π (k-1)` form `[I_k; 0]`!
  have hstep : ∀ k : Nat, k ≤ 4 →
      ∃ (M : Nat → Nat → F) (π : Nat → Nat),
        (∀ s, s < 6 → π s < 6) ∧
        (∀ f : Nat → F, sumR 6 (fun s => f (π s)) = sumR 6 f) ∧
        (∀ α : Nat → F, (∀ a, a < 4 → sumR 4 (fun i => α i * M i a) = 0) → ∀ i, i < 4 → α i = 0) ∧
        (∀ i j, i < 4 → j < k → sumR 4 (fun a => M i a * U (π j) a) = if i = j then 1 else 0) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun i a => if i = a then 1 else 0, fun s => s, fun _ hs => hs, fun _ => rfl, ?_, fun _ _ _ hj => by omega⟩
      intro α hα i hi
      have hi' := hα i hi
      have hsingle : sumR 4 (fun j => α j * (if j = i then (1 : F) else 0)) = α i := by
        rw [sumR_four]
        have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases hi4 with rfl | rfl | rfl | rfl <;>
          simp [mul_one, mul_zero, add_zero, CommRing.zero_add]
      rw [hsingle] at hi'
      exact hi'
    | succ k ih =>
      intro hk4
      obtain ⟨M, π, hπ_lt, hπ_sum, hM_ind, hM_piv⟩ := ih (by omega)
      -- Row `k` of `M` is nonzero (otherwise setting `α k = 1` violates `hM_ind`), hence by `hinj`
      -- there exists `s < 6` with `sumR 4 (fun a => M k a * U s a) ≠ 0`, hence `j < 6` with `U (π j)` nonzero!
      have hMk_nz : ∃ a, a < 4 ∧ M k a ≠ 0 := by
        apply Classical.byContradiction
        intro h
        have h0 : ∀ a, a < 4 → M k a = 0 := fun a ha => Classical.byContradiction (fun hne => h ⟨a, ha, hne⟩)
        have hα : ∀ a, a < 4 → sumR 4 (fun i => (if i = k then (1 : F) else 0) * M i a) = 0 := by
          intro a ha
          rw [sumR_four]
          have hk4' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hk4' with rfl | rfl | rfl | rfl <;>
            simp [CommRing.one_mul, zero_mul, add_zero, h0 a ha]
        have hk0 := hM_ind (fun i => if i = k then 1 else 0) hα k (by omega)
        simp only [↓reduceIte] at hk0
        exact SimpleField.zero_ne_one hk0.symm
      have hpiv_ex : ∃ j, j < 6 ∧ sumR 4 (fun a => M k a * U (π j) a) ≠ 0 := by
        apply Classical.byContradiction
        intro h
        have hallπ : ∀ j, j < 6 → sumR 4 (fun a => M k a * U (π j) a) = 0 :=
          fun j hj => Classical.byContradiction (fun hne => h ⟨j, hj, hne⟩)
        -- Use `hπ_sum` on indicator? Even simpler: prove `π` is surjective on `{0..5}`?
        -- Wait: `hπ_sum` holds for EVERY `f : Nat → F`, so plug `f s' := if s' = s then 1 else 0`!
        have hall : ∀ s, s < 6 → sumR 4 (fun a => M k a * U s a) = 0 := by
          intro s hs
          -- Prove `∃ j < 6, π j = s` from `hπ_sum`!
          have hex : ∃ j, j < 6 ∧ π j = s := by
            let ind : Nat → F := fun x => if x = s then 1 else 0
            have hs1 : sumR 6 ind = 1 := by
              have h6 : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
              rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
                simp [sumR, ind, add_zero, CommRing.zero_add]
            have hne0 : sumR 6 (fun j => ind (π j)) ≠ 0 := by
              rw [hπ_sum ind, hs1]; exact Ne.symm SimpleField.zero_ne_one
            obtain ⟨j, hj, hjne⟩ := exists_nonzero_of_sumR_ne_zero 6 (fun j => ind (π j)) hne0
            dsimp only [ind] at hjne
            by_cases heq : π j = s
            · exact ⟨j, hj, heq⟩
            · simp [heq] at hjne
          obtain ⟨j, hj, rfl⟩ := hex
          exact hallπ j hj
        obtain ⟨a, ha, hne⟩ := hMk_nz
        exact hne (hinj (M k) hall a ha)
      obtain ⟨j, hj6, hpiv_ne⟩ := hpiv_ex
      -- Notice `j ≥ k`, because for `j < k`, `hM_piv k j` gives `if k = j then 1 else 0 = 0`!
      have hjk : k ≤ j := by
        by_cases hlt : j < k
        · have hz := hM_piv k j (by omega) hlt
          have hne : k ≠ j := by omega
          simp only [hne, ↓reduceIte] at hz
          exact absurd hz hpiv_ne
        · omega
      -- Swap columns `k` and `j` via `π' s := π (swapNat k j s)`, scale row `k` by `inv piv`, eliminate column `k` from all `i ≠ k`!
      let π' : Nat → Nat := fun s => π (swapNat k j s)
      let piv : F := sumR 4 (fun a => M k a * U (π j) a)
      let invP : F := SimpleField.inv piv
      let val : Nat → F := fun i => sumR 4 (fun a => M i a * U (π j) a)
      let M' : Nat → Nat → F := fun i a =>
        if i = k then invP * M k a
        else M i a - (val i * invP) * M k a
      have hπ'_lt : ∀ s, s < 6 → π' s < 6 := fun s hs => hπ_lt _ (swapNat_lt (by omega) hj6 hs)
      have hπ'_sum : ∀ f : Nat → F, sumR 6 (fun s => f (π' s)) = sumR 6 f := by
        intro f
        dsimp only [π']
        rw [sumR_perm_swap 6 k j (fun s => f (π s)) (by omega) hj6, hπ_sum f]
      have hM'_ind : ∀ α : Nat → F, (∀ a, a < 4 → sumR 4 (fun i => α i * M' i a) = 0) → ∀ i, i < 4 → α i = 0 := by
        intro α hα
        -- Express `∑_i α_i M'_i a = ∑_i α'_i M_i a` where `α'_i = α_i` (`i ≠ k`) and
        -- `α'_k = α_k * invP - ∑_{i ≠ k} α_i * val_i * invP`!
        let Snotk : F := sumR 4 (fun i => if i = k then 0 else α i * (val i * invP))
        let α' : Nat → F := fun i => if i = k then α k * invP - Snotk else α i
        have hcomb : ∀ a, a < 4 → sumR 4 (fun i => α' i * M i a) = 0 := by
          intro a ha
          have h0 := hα a ha
          -- Show `sumR 4 (fun i => α i * M' i a) = sumR 4 (fun i => α' i * M i a)`
          have heq : sumR 4 (fun i => α i * M' i a) = sumR 4 (fun i => α' i * M i a) := by
            have hterm : ∀ i, α i * M' i a =
                (if i = k then (α k * invP) * M k a else α i * M i a) +
                (-(if i = k then 0 else α i * (val i * invP)) * M k a) := by
              intro i
              dsimp only [M']
              by_cases hik : i = k
              · subst i; simp [CommRing.mul_assoc, neg_zero, zero_mul, add_zero]
              · simp only [hik, ↓reduceIte]
                rw [mul_sub_r, CommRing.sub_eq, neg_mul, ← CommRing.mul_assoc (α i)]
            rw [sumR_congr (fun i _ => hterm i), sumR_add]
            have hpart2 : sumR 4 (fun i => -(if i = k then 0 else α i * (val i * invP)) * M k a) = -(Snotk * M k a) := by
              rw [← sumR_mul_right, sumR_neg, neg_mul]
            rw [hpart2]
            -- Combine `α k * invP * M k a - Snotk * M k a` at index `k`!
            have hsub : ∀ i, α' i * M i a =
                (if i = k then (α k * invP) * M k a else α i * M i a) +
                (if i = k then -(Snotk * M k a) else 0) := by
              intro i
              dsimp only [α']
              by_cases hik : i = k
              · subst i; simp [CommRing.sub_eq, right_distrib, neg_mul]
              · simp [hik, add_zero]
            rw [sumR_congr (fun i _ => hsub i), sumR_add]
            congr 1
            have hk4' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
            rw [sumR_four]
            rcases hk4' with rfl | rfl | rfl | rfl <;>
              simp [add_zero, CommRing.zero_add]
          rw [← heq]; exact h0
        have hα'0 := hM_ind α' hcomb
        intro i hi
        by_cases hik : i = k
        · subst i
          have hk0 := hα'0 k (by omega)
          dsimp only [α'] at hk0
          simp only [↓reduceIte] at hk0
          have hSn0 : Snotk = 0 := by
            dsimp only [Snotk]
            have hz : ∀ j, j < 4 → (if j = k then (0 : F) else α j * (val j * invP)) = 0 := by
              intro j hj
              by_cases hjk' : j = k
              · simp [hjk']
              · have hαj := hα'0 j hj
                dsimp only [α'] at hαj
                simp only [hjk', ↓reduceIte] at hαj
                simp [hjk', hαj, zero_mul]
            rw [sumR_congr hz, sumR_zero_fn]
          rw [hSn0, CommRing.sub_eq, neg_zero, add_zero] at hk0
          have hmul := congrArg (fun x => x * piv) hk0
          rw [CommRing.mul_assoc, CommRing.mul_comm invP piv, SimpleField.mul_inv_cancel piv hpiv_ne,
              mul_one, zero_mul] at hmul
          exact hmul
        · have h := hα'0 i hi
          dsimp only [α'] at h
          simp only [hik, ↓reduceIte] at h
          exact h
      have hM'_piv : ∀ i col, i < 4 → col < k + 1 →
          sumR 4 (fun a => M' i a * U (π' col) a) = if i = col then 1 else 0 := by
        intro i col hi hcol
        have hdot : ∀ c_idx, sumR 4 (fun a => M' i a * U c_idx a) =
            if i = k then invP * sumR 4 (fun a => M k a * U c_idx a)
            else sumR 4 (fun a => M i a * U c_idx a) - (val i * invP) * sumR 4 (fun a => M k a * U c_idx a) := by
          intro c_idx
          by_cases hik : i = k
          · subst i
            simp only [M', ↓reduceIte, sumR_mul_left]
            exact sumR_congr (fun a _ => CommRing.mul_assoc ..)
          · simp only [M', hik, ↓reduceIte]
            have ht : ∀ a, (M i a - val i * invP * M k a) * U c_idx a =
                M i a * U c_idx a + -(val i * invP * (M k a * U c_idx a)) := by
              intro a
              rw [CommRing.sub_eq, right_distrib, neg_mul, CommRing.mul_assoc]
            rw [sumR_congr (fun a _ => ht a), sumR_add, CommRing.sub_eq, sumR_mul_left, ← sumR_neg]
        rw [hdot (π' col)]
        by_cases hck : col = k
        · subst col
          have hπk : π' k = π j := by dsimp only [π']; simp [swapNat]
          rw [hπk]
          by_cases hik : i = k
          · subst i
            simp only [↓reduceIte]
            change invP * piv = 1
            rw [CommRing.mul_comm, SimpleField.mul_inv_cancel piv hpiv_ne]
          · simp only [hik, ↓reduceIte]
            change val i - val i * invP * piv = 0
            rw [CommRing.mul_assoc, CommRing.mul_comm invP piv, SimpleField.mul_inv_cancel piv hpiv_ne, mul_one, sub_self]
        · have hcol_lt : col < k := by omega
          have hπc : π' col = π col := by
            dsimp only [π', swapNat]
            have h1 : col ≠ k := hck
            have h2 : col ≠ j := by omega
            simp [h1, h2]
          rw [hπc, hM_piv k col (by omega) hcol_lt, hM_piv i col hi hcol_lt]
          have hne_kc : k ≠ col := by omega
          simp only [hne_kc, ↓reduceIte, mul_zero, CommRing.sub_eq, neg_zero, add_zero]
          by_cases hik : i = k
          · subst hik; simp [hne_kc]
          · simp [hik]
      exact ⟨M', π', hπ'_lt, hπ'_sum, hM'_ind, hM'_piv⟩
  exact hstep 4 (Nat.le_refl 4)

/-- **Winograd's (1971) Exact Lower Bound `rank_F(⟨2,2,2⟩) ≥ 7` Over EVERY `SimpleField F` (incl. `char 2`!):**
Rules out `r = 6` directly via `rref_4x6`, `det2_eq_zero_of_sum3`, `no_three_clique_rank1`,
`row_col_constraints_of_rank2_sum`, and `cramer2_zero`, then combines with `T3e` (`6 ≤ r`)! -/
theorem winograd_rank_ge_seven (F : Type) [SimpleField F] (r : Nat)
    (hrank : HasTensorRankAtMost 4 4 4 r (fun a b c => intToR (R := F) (matMul2Tensor a b c))) :
    7 ≤ r := by
  have hge6 : 6 ≤ r := t3e_koszul_flattening_tensor_rank_bridge.1 F r hrank
  by_cases h7 : 7 ≤ r
  · exact h7
  · exfalso
    have hr6 : r = 6 := by omega
    subst hr6
    obtain ⟨U, V, W, hT⟩ := hrank
    -- 1. Show `sliceM X c b = ∑_{s<6} (∑_{a<4} X a * U s a) * (W s c * V s b)`
    have hslice : ∀ (X : Nat → F) (c b : Nat), c < 4 → b < 4 →
        sliceM X c b = sumR 6 (fun s => (sumR 4 (fun a => X a * U s a)) * (W s c * V s b)) := by
      intro X c b hc hb
      unfold sliceM
      have hrew : sumR 4 (fun a => X a * intToR (R := F) (matMul2Tensor a b c)) =
          sumR 4 (fun a => sumR 6 (fun s => (X a * U s a) * (W s c * V s b))) := by
        apply sumR_congr
        intro a ha
        have hTa := hT a b c ha hb hc
        dsimp only at hTa
        rw [hTa, sumR_mul_left]
        apply sumR_congr
        intro s _
        rw [CommRing.mul_assoc (U s a) (V s b) (W s c), CommRing.mul_comm (V s b) (W s c),
            ← CommRing.mul_assoc]
      rw [hrew, sumR_swap 4 6]
      exact sumR_congr (fun s _ => (sumR_mul_right 4 (fun a => X a * U s a) (W s c * V s b)).symm)
    -- 2. Show `U` satisfies the injectivity hypothesis of `rref_4x6`
    have hinj : ∀ X : Nat → F, (∀ s, s < 6 → sumR 4 (fun a => X a * U s a) = 0) → ∀ a, a < 4 → X a = 0 := by
      intro X hzero a ha
      have hsl0 : ∀ c b, c < 4 → b < 4 → sliceM X c b = 0 := by
        intro c b hc hb
        rw [hslice X c b hc hb]
        rw [sumR_congr (fun s hs => by rw [hzero s hs, zero_mul]), sumR_zero_fn]
      have hev := sliceM_eval X
      have ha4 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
      rcases ha4 with rfl | rfl | rfl | rfl
      · rw [← hev.1.1]; exact hsl0 0 0 (by omega) (by omega)
      · rw [← hev.1.2.2.1]; exact hsl0 0 2 (by omega) (by omega)
      · rw [← hev.2.2.1.1]; exact hsl0 2 0 (by omega) (by omega)
      · rw [← hev.2.2.1.2.2.1]; exact hsl0 2 2 (by omega) (by omega)
    -- 3. Obtain RREF basis `M_0..M_3` and column permutation `π` of `{0..5}`!
    obtain ⟨M, π, hπ_lt, hπ_sum, hM_ind, hM_piv⟩ := rref_4x6 U hinj
    let c4 : Nat → F := fun i => sumR 4 (fun a => M i a * U (π 4) a)
    let c5 : Nat → F := fun i => sumR 4 (fun a => M i a * U (π 5) a)
    have hMi_expr : ∀ i c b, i < 4 → c < 4 → b < 4 →
        sliceM (M i) c b =
          W (π i) c * V (π i) b + (c4 i * W (π 4) c) * V (π 4) b + (c5 i * W (π 5) c) * V (π 5) b := by
      intro i c b hi hc hb
      rw [hslice (M i) c b hc hb, ← hπ_sum (fun s => sumR 4 (fun a => M i a * U s a) * (W s c * V s b))]
      have h6 : sumR 6 (fun s => sumR 4 (fun a => M i a * U (π s) a) * (W (π s) c * V (π s) b)) =
          sumR 4 (fun s => sumR 4 (fun a => M i a * U (π s) a) * (W (π s) c * V (π s) b)) +
          c4 i * (W (π 4) c * V (π 4) b) + c5 i * (W (π 5) c * V (π 5) b) := by
        simp only [sumR, c4, c5]
      rw [h6]
      have h4 : sumR 4 (fun s => sumR 4 (fun a => M i a * U (π s) a) * (W (π s) c * V (π s) b)) =
          W (π i) c * V (π i) b := by
        have ht : ∀ s, s < 4 → sumR 4 (fun a => M i a * U (π s) a) * (W (π s) c * V (π s) b) =
            if i = s then W (π i) c * V (π i) b else 0 := by
          intro s hs
          rw [hM_piv i s hi hs]
          by_cases his : i = s
          · subst his; simp [CommRing.one_mul]
          · simp [his, zero_mul]
        rw [sumR_congr ht, sumR_four]
        have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases hi4 with rfl | rfl | rfl | rfl <;> simp [add_zero, CommRing.zero_add]
      rw [h4, CommRing.mul_assoc (c4 i), CommRing.mul_assoc (c5 i)]
    -- 4. Every `M i` is nonzero and singular, hence factors as `u_i v_i^T`!
    have hMi_nz : ∀ i, i < 4 → ∃ a, a < 4 ∧ M i a ≠ 0 := by
      intro i hi
      apply Classical.byContradiction
      intro h
      have h0 : ∀ a, a < 4 → M i a = 0 := fun a ha => Classical.byContradiction (fun hne => h ⟨a, ha, hne⟩)
      have hα : ∀ a, a < 4 → sumR 4 (fun j => (if j = i then (1 : F) else 0) * M j a) = 0 := by
        intro a ha
        rw [sumR_four]
        have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases hi4 with rfl | rfl | rfl | rfl <;> simp [CommRing.one_mul, zero_mul, add_zero, h0 a ha]
      have hi0 := hM_ind (fun j => if j = i then 1 else 0) hα i hi
      simp only [↓reduceIte] at hi0
      exact SimpleField.zero_ne_one hi0.symm
    have hMi_det0 : ∀ i, i < 4 → det2 (M i) = 0 := fun i hi =>
      det2_eq_zero_of_sum3 (M i) (W (π i)) (V (π i)) (fun c => c4 i * W (π 4) c) (V (π 4))
        (fun c => c5 i * W (π 5) c) (V (π 5)) (fun c b hc hb => hMi_expr i c b hi hc hb)
    have hfac_ex : ∀ i, i < 4 → ∃ u0 u1 v0 v1 : F,
        (u0 ≠ 0 ∨ u1 ≠ 0) ∧ (v0 ≠ 0 ∨ v1 ≠ 0) ∧
        M i 0 = u0 * v0 ∧ M i 1 = u0 * v1 ∧ M i 2 = u1 * v0 ∧ M i 3 = u1 * v1 :=
      fun i hi => singular2_factor (M i) (hMi_nz i hi) (hMi_det0 i hi)
    -- Extract the 4 rank-1 factorizations via `Classical.choice` (only for `i < 4`!)
    let u0 : Nat → F := fun i => if h : i < 4 then (hfac_ex i h).choose else 0
    let u1 : Nat → F := fun i => if h : i < 4 then (hfac_ex i h).choose_spec.choose else 0
    let v0 : Nat → F := fun i => if h : i < 4 then (hfac_ex i h).choose_spec.choose_spec.choose else 0
    let v1 : Nat → F := fun i => if h : i < 4 then (hfac_ex i h).choose_spec.choose_spec.choose_spec.choose else 0
    have hfac : ∀ i, i < 4 →
        (u0 i ≠ 0 ∨ u1 i ≠ 0) ∧ (v0 i ≠ 0 ∨ v1 i ≠ 0) ∧
        M i 0 = u0 i * v0 i ∧ M i 1 = u0 i * v1 i ∧ M i 2 = u1 i * v0 i ∧ M i 3 = u1 i * v1 i := by
      intro i hi
      dsimp only [u0, u1, v0, v1]
      simp only [hi, ↓reduceDIte]
      exact (hfac_ex i hi).choose_spec.choose_spec.choose_spec.choose_spec
    -- 5. Clique property on `Z4` (`c4 = 0`) and on `N4` (`c4 ≠ 0`)!
    have hclique_comb : ∀ i j : Nat, i < 4 → j < 4 →
        ∀ α β : F, α ≠ 0 → β ≠ 0 → α * c4 i + β * c4 j = 0 →
        det2Pair (u0 i) (u1 i) (u0 j) (u1 j) = 0 ∨ det2Pair (v0 i) (v1 i) (v0 j) (v1 j) = 0 := by
      intro i j hi hj α β hα hβ hkill4
      have hdet_comb : det2 (fun a => α * M i a + β * M j a) = 0 := by
        apply det2_eq_zero_of_sum3 (fun a => α * M i a + β * M j a)
          (fun c => α * W (π i) c) (V (π i))
          (fun c => β * W (π j) c) (V (π j))
          (fun c => (α * c5 i + β * c5 j) * W (π 5) c) (V (π 5))
        intro c b hc hb
        rw [sliceM_linear, hMi_expr i c b hi hc hb, hMi_expr j c b hj hc hb]
        simp only [CommRing.left_distrib, right_distrib, CommRing.mul_assoc]
        -- Group the `E_4` terms and kill them via `α * c4 i + β * c4 j = 0`!
        have h4zero : α * (c4 i * (W (π 4) c * V (π 4) b)) + β * (c4 j * (W (π 4) c * V (π 4) b)) = 0 := by
          rw [← CommRing.mul_assoc α (c4 i), ← CommRing.mul_assoc β (c4 j), ← right_distrib, hkill4, zero_mul]
        have rearr6 : ∀ a1 a2 a3 b1 b2 b3 : F,
            ((a1 + a2) + a3) + ((b1 + b2) + b3) = ((a1 + b1) + (a3 + b3)) + (a2 + b2) := by
          intro a1 a2 a3 b1 b2 b3
          have s : ∀ r1 r2 r3 r4 : F, (r1 + r2) + (r3 + r4) = (r1 + r3) + (r2 + r4) := by
            intro r1 r2 r3 r4
            rw [CommRing.add_assoc, ← CommRing.add_assoc r2 r3 r4, CommRing.add_comm r2 r3,
                CommRing.add_assoc r3 r2 r4, ← CommRing.add_assoc]
          rw [s (a1 + a2) a3 (b1 + b2) b3, s a1 a2 b1 b2,
              CommRing.add_assoc (a1 + b1) (a2 + b2) (a3 + b3),
              CommRing.add_comm (a2 + b2) (a3 + b3), ← CommRing.add_assoc]
        rw [rearr6, h4zero, add_zero]
      have fi := hfac i hi
      have fj := hfac j hj
      unfold det2 at hdet_comb
      dsimp only at hdet_comb
      rw [fi.2.2.1, fi.2.2.2.1, fi.2.2.2.2.1, fi.2.2.2.2.2,
          fj.2.2.1, fj.2.2.2.1, fj.2.2.2.2.1, fj.2.2.2.2.2,
          det2_rank1_comb] at hdet_comb
      cases field_mul_eq_zero hdet_comb with
      | inl h1 =>
        cases field_mul_eq_zero h1 with
        | inl hαβ => exact absurd hαβ (field_mul_ne_zero hα hβ)
        | inr hdu => exact Or.inl hdu
      | inr hdv => exact Or.inr hdv
    have hZ_edge : ∀ i j, i < 4 → j < 4 → c4 i = 0 → c4 j = 0 →
        det2Pair (u0 i) (u1 i) (u0 j) (u1 j) = 0 ∨ det2Pair (v0 i) (v1 i) (v0 j) (v1 j) = 0 :=
      fun i j hi hj hci hcj => hclique_comb i j hi hj 1 1 (Ne.symm SimpleField.zero_ne_one)
        (Ne.symm SimpleField.zero_ne_one) (by rw [hci, hcj, mul_zero, add_zero])
    have hN_edge : ∀ i j, i < 4 → j < 4 → c4 i ≠ 0 → c4 j ≠ 0 →
        det2Pair (u0 i) (u1 i) (u0 j) (u1 j) = 0 ∨ det2Pair (v0 i) (v1 i) (v0 j) (v1 j) = 0 :=
      fun i j hi hj hci hcj => hclique_comb i j hi hj (c4 j) (-(c4 i)) hcj
        (fun h => hci (neg_eq_zero_iff.mp h)) (by rw [neg_mul, CommRing.mul_comm (c4 j) (c4 i), CommRing.add_neg])
    -- Helper: any 3 distinct indices in `{0..3}` are linearly independent via `hM_ind`!
    have hind3 : ∀ i j k, i < 4 → j < 4 → k < 4 → i ≠ j → i ≠ k → j ≠ k →
        ∀ α β γ : F,
          α * (u0 i * v0 i) + β * (u0 j * v0 j) + γ * (u0 k * v0 k) = 0 →
          α * (u0 i * v1 i) + β * (u0 j * v1 j) + γ * (u0 k * v1 k) = 0 →
          α * (u1 i * v0 i) + β * (u1 j * v0 j) + γ * (u1 k * v0 k) = 0 →
          α * (u1 i * v1 i) + β * (u1 j * v1 j) + γ * (u1 k * v1 k) = 0 →
          α = 0 ∧ β = 0 ∧ γ = 0 := by
      intro i j k hi hj hk hij hik hjk α β γ e0 e1 e2 e3
      let coeff : Nat → F := fun t => if t = i then α else if t = j then β else if t = k then γ else 0
      have hall : ∀ a, a < 4 → sumR 4 (fun t => coeff t * M t a) = 0 := by
        intro a ha
        have hsum_eq : sumR 4 (fun t => coeff t * M t a) = α * M i a + β * M j a + γ * M k a := by
          have hrewrite : ∀ t, coeff t * M t a =
              if t = i then α * M i a else if t = j then β * M j a else if t = k then γ * M k a else 0 := by
            intro t
            dsimp only [coeff]
            by_cases hti : t = i
            · subst hti; simp
            · by_cases htj : t = j
              · subst htj; simp [hti]
              · by_cases htk : t = k
                · subst htk; simp [hti, htj]
                · simp [hti, htj, htk, zero_mul]
          rw [sumR_four, hrewrite 0, hrewrite 1, hrewrite 2, hrewrite 3]
          have p1 : ∀ x y z : F, x + y + z = x + y + z := fun _ _ _ => rfl
          have p2 : ∀ x y z : F, x + z + y = x + y + z := by
            intro x y z; rw [CommRing.add_assoc, CommRing.add_comm z y, ← CommRing.add_assoc]
          have p3 : ∀ x y z : F, y + x + z = x + y + z := by
            intro x y z; rw [CommRing.add_comm y x]
          have p4 : ∀ x y z : F, y + z + x = x + y + z := by
            intro x y z; rw [CommRing.add_comm (y + z) x, ← CommRing.add_assoc]
          have p5 : ∀ x y z : F, z + x + y = x + y + z := by
            intro x y z; rw [CommRing.add_assoc, CommRing.add_comm z (x + y)]
          have p6 : ∀ x y z : F, z + y + x = x + y + z := by
            intro x y z; rw [CommRing.add_comm z y, p4]
          have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
          have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
          have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hi4 with rfl | rfl | rfl | rfl <;>
            rcases hj4 with rfl | rfl | rfl | rfl <;>
            rcases hk4 with rfl | rfl | rfl | rfl <;>
            first
            | omega
            | (simp [add_zero, CommRing.zero_add];
               try (first | exact p1 .. | exact p2 .. | exact p3 .. | exact p4 .. | exact p5 .. | exact p6 ..))
        rw [hsum_eq]
        have fi := hfac i hi; have fj := hfac j hj; have fk := hfac k hk
        have ha4 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
        rcases ha4 with rfl | rfl | rfl | rfl
        · rw [fi.2.2.1, fj.2.2.1, fk.2.2.1]; exact e0
        · rw [fi.2.2.2.1, fj.2.2.2.1, fk.2.2.2.1]; exact e1
        · rw [fi.2.2.2.2.1, fj.2.2.2.2.1, fk.2.2.2.2.1]; exact e2
        · rw [fi.2.2.2.2.2, fj.2.2.2.2.2, fk.2.2.2.2.2]; exact e3
      have h0 := hM_ind coeff hall
      have hα0 := h0 i hi; dsimp only [coeff] at hα0; simp only [↓reduceIte] at hα0
      have hβ0 := h0 j hj; dsimp only [coeff] at hβ0; simp only [Ne.symm hij, ↓reduceIte] at hβ0
      have hγ0 := h0 k hk; dsimp only [coeff] at hγ0; simp only [Ne.symm hik, Ne.symm hjk, ↓reduceIte] at hγ0
      exact ⟨hα0, hβ0, hγ0⟩
    -- 6. No 3 indices can all have `c4 = 0`, and no 3 indices can all have `c4 ≠ 0`!
    have hno3Z : ∀ i j k, i < 4 → j < 4 → k < 4 → i ≠ j → i ≠ k → j ≠ k →
        c4 i = 0 → c4 j = 0 → c4 k = 0 → False := fun i j k hi hj hk hij hik hjk hci hcj hck =>
      no_three_clique_rank1 u0 u1 v0 v1 i j k (hfac i hi).1 (hfac j hj).1 (hfac i hi).2.1 (hfac j hj).2.1
        (hZ_edge i j hi hj hci hcj) (hZ_edge i k hi hk hci hck) (hZ_edge j k hj hk hcj hck)
        (hind3 i j k hi hj hk hij hik hjk)
    have hno3N : ∀ i j k, i < 4 → j < 4 → k < 4 → i ≠ j → i ≠ k → j ≠ k →
        c4 i ≠ 0 → c4 j ≠ 0 → c4 k ≠ 0 → False := fun i j k hi hj hk hij hik hjk hci hcj hck =>
      no_three_clique_rank1 u0 u1 v0 v1 i j k (hfac i hi).1 (hfac j hj).1 (hfac i hi).2.1 (hfac j hj).2.1
        (hN_edge i j hi hj hci hcj) (hN_edge i k hi hk hci hck) (hN_edge j k hj hk hcj hck)
        (hind3 i j k hi hj hk hij hik hjk)
    -- Therefore there exist distinct `i, j < 4` with `c4 i = 0` AND `c4 j = 0`!
    have hex2Z : ∃ i j, i < 4 ∧ j < 4 ∧ i ≠ j ∧ c4 i = 0 ∧ c4 j = 0 := by
      by_cases z0 : c4 0 = 0 <;> by_cases z1 : c4 1 = 0 <;> by_cases z2 : c4 2 = 0 <;> by_cases z3 : c4 3 = 0
      · exact ⟨0, 1, by omega, by omega, by omega, z0, z1⟩
      · exact ⟨0, 1, by omega, by omega, by omega, z0, z1⟩
      · exact ⟨0, 1, by omega, by omega, by omega, z0, z1⟩
      · exact ⟨0, 1, by omega, by omega, by omega, z0, z1⟩
      · exact ⟨0, 2, by omega, by omega, by omega, z0, z2⟩
      · exact ⟨0, 2, by omega, by omega, by omega, z0, z2⟩
      · exact ⟨0, 3, by omega, by omega, by omega, z0, z3⟩
      · exact absurd (hno3N 1 2 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z1 z2 z3) id
      · exact ⟨1, 2, by omega, by omega, by omega, z1, z2⟩
      · exact ⟨1, 2, by omega, by omega, by omega, z1, z2⟩
      · exact ⟨1, 3, by omega, by omega, by omega, z1, z3⟩
      · exact absurd (hno3N 0 2 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z0 z2 z3) id
      · exact ⟨2, 3, by omega, by omega, by omega, z2, z3⟩
      · exact absurd (hno3N 0 1 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z0 z1 z3) id
      · exact absurd (hno3N 0 1 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z0 z1 z2) id
      · exact absurd (hno3N 0 1 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z0 z1 z2) id
    obtain ⟨i, j, hi, hj, hij, hci4, hcj4⟩ := hex2Z
    -- 7. For both `k ∈ {i, j}`, `c4 k = 0`, so `sliceM (M k) = E_k + c5 k * E_5`; hence `c5 k ≠ 0`!
    have hc5_ne : ∀ k, k < 4 → c4 k = 0 → c5 k ≠ 0 := by
      intro k hk hck4 hz
      apply sliceM_ne_rank1 (M k) (W (π k)) (V (π k)) (hMi_nz k hk)
      intro c b hc hb
      rw [hMi_expr k c b hk hc hb, hck4, hz, zero_mul, zero_mul, zero_mul, zero_mul, add_zero, add_zero]
    have hci5 : c5 i ≠ 0 := hc5_ne i hi hci4
    have hcj5 : c5 j ≠ 0 := hc5_ne j hj hcj4
    -- Apply `row_col_constraints_of_rank2_sum` to BOTH `i` and `j`!
    have hrel_of : ∀ k, k < 4 → c4 k = 0 → c5 k ≠ 0 →
        (v1 k * V (π 5) 0 = v0 k * V (π 5) 2 ∧ v1 k * V (π 5) 1 = v0 k * V (π 5) 3) ∧
        (u1 k * W (π 5) 0 = u0 k * W (π 5) 2 ∧ u1 k * W (π 5) 1 = u0 k * W (π 5) 3) := by
      intro k hk hck4 hck5
      have fk := hfac k hk
      apply row_col_constraints_of_rank2_sum (u0 k) (u1 k) (v0 k) (v1 k) (c5 k)
        (W (π k)) (V (π k)) (W (π 5)) (V (π 5)) fk.1 fk.2.1 hck5
      intro r b hr hb
      have hMk_eq : sliceM (fun a => match a with | 0 => u0 k * v0 k | 1 => u0 k * v1 k | 2 => u1 k * v0 k | _ => u1 k * v1 k) r b =
          sliceM (M k) r b := by
        unfold sliceM
        apply sumR_congr
        intro a ha
        have ha4 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
        rcases ha4 with rfl | rfl | rfl | rfl
        · rw [fk.2.2.1]; rfl
        · rw [fk.2.2.2.1]; rfl
        · rw [fk.2.2.2.2.1]; rfl
        · rw [fk.2.2.2.2.2]; rfl
      rw [hMk_eq, hMi_expr k r b hk hr hb, hck4, zero_mul, zero_mul, add_zero, CommRing.mul_assoc]
    have hri := hrel_of i hi hci4 hci5
    have hrj := hrel_of j hj hcj4 hcj5
    -- Since `M i` and `M j` are linearly independent, we CANNOT have BOTH `detU i j = 0` AND `detV i j = 0`!
    have hnot_both : ¬ (det2Pair (u0 i) (u1 i) (u0 j) (u1 j) = 0 ∧ det2Pair (v0 i) (v1 i) (v0 j) (v1 j) = 0) := by
      intro ⟨hdu, hdv⟩
      -- Pick a third index `k ≠ i, j` (`k < 4`) and exhibit `α M i + β M j = 0` contradicting `hind3`!
      have hscale : ∀ x0 x1 y0 y1 : F, (x0 ≠ 0 ∨ x1 ≠ 0) → det2Pair x0 x1 y0 y1 = 0 →
          ∃ s : F, y0 = s * x0 ∧ y1 = s * x1 := by
        intro x0 x1 y0 y1 hx hd
        have heq := eq_of_sub_eq_zero hd
        cases hx with
        | inl h =>
          refine ⟨y0 * SimpleField.inv x0,
            by rw [CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv x0) x0, SimpleField.mul_inv_cancel _ h, mul_one], ?_⟩
          calc y1 = SimpleField.inv x0 * (x0 * y1) := by
                    rw [← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv x0) x0, SimpleField.mul_inv_cancel _ h, CommRing.one_mul]
            _ = SimpleField.inv x0 * (x1 * y0) := by rw [heq]
            _ = y0 * SimpleField.inv x0 * x1 := by
                  rw [CommRing.mul_comm x1 y0, ← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv x0) y0]
        | inr h =>
          refine ⟨y1 * SimpleField.inv x1, ?_,
            by rw [CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv x1) x1, SimpleField.mul_inv_cancel _ h, mul_one]⟩
          calc y0 = SimpleField.inv x1 * (x1 * y0) := by
                    rw [← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv x1) x1, SimpleField.mul_inv_cancel _ h, CommRing.one_mul]
            _ = SimpleField.inv x1 * (x0 * y1) := by rw [← heq]
            _ = y1 * SimpleField.inv x1 * x0 := by
                  rw [CommRing.mul_comm x0 y1, ← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv x1) y1]
      obtain ⟨su, hsu0, hsu1⟩ := hscale (u0 i) (u1 i) (u0 j) (u1 j) (hfac i hi).1 hdu
      obtain ⟨sv, hsv0, hsv1⟩ := hscale (v0 i) (v1 i) (v0 j) (v1 j) (hfac i hi).2.1 hdv
      -- Pick any `k < 4` with `k ≠ i ∧ k ≠ j`
      obtain ⟨k, hk, hki, hkj⟩ : ∃ k, k < 4 ∧ i ≠ k ∧ j ≠ k := by
        by_cases h0 : i ≠ 0 ∧ j ≠ 0
        · exact ⟨0, by omega, h0.1, h0.2⟩
        · by_cases h1 : i ≠ 1 ∧ j ≠ 1
          · exact ⟨1, by omega, h1.1, h1.2⟩
          · exact ⟨2, by omega, by omega, by omega⟩
      have hterm_eq : ∀ a b c : F, -(su * sv) * (a * b) + 1 * ((su * a) * (sv * b)) + 0 * c = 0 := by
        intro a b c
        rw [CommRing.one_mul, zero_mul, add_zero, neg_mul]
        have hm : (su * a) * (sv * b) = su * sv * (a * b) := by
          rw [CommRing.mul_assoc su a, ← CommRing.mul_assoc a sv b, CommRing.mul_comm a sv,
              CommRing.mul_assoc sv a b, ← CommRing.mul_assoc su sv]
        rw [hm, neg_add]
      have ⟨_, h10, _⟩ := hind3 i j k hi hj hk hij hki hkj (-(su * sv)) 1 0
        (by rw [hsu0, hsv0]; exact hterm_eq (u0 i) (v0 i) _)
        (by rw [hsu0, hsv1]; exact hterm_eq (u0 i) (v1 i) _)
        (by rw [hsu1, hsv0]; exact hterm_eq (u1 i) (v0 i) _)
        (by rw [hsu1, hsv1]; exact hterm_eq (u1 i) (v1 i) _)
      exact SimpleField.zero_ne_one h10.symm
    -- 8. FINAL CRAMER KILL: either `detV ≠ 0 ⇒ V(π 5) ≡ 0` OR `detU ≠ 0 ⇒ W(π 5) ≡ 0` — BOTH contradict `sliceM_ne_rank1`!
    by_cases hdv : det2Pair (v0 i) (v1 i) (v0 j) (v1 j) ≠ 0
    · have ⟨hv0, hv2⟩ := cramer2_zero hdv hri.1.1 hrj.1.1
      have ⟨hv1, hv3⟩ := cramer2_zero hdv hri.1.2 hrj.1.2
      apply sliceM_ne_rank1 (M i) (W (π i)) (V (π i)) (hMi_nz i hi)
      intro c b hc hb
      rw [hMi_expr i c b hi hc hb, hci4, zero_mul, zero_mul, add_zero]
      have hb4 : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
      rcases hb4 with rfl | rfl | rfl | rfl <;>
        simp [hv0, hv1, hv2, hv3, mul_zero, add_zero]
    · have hdv0 : det2Pair (v0 i) (v1 i) (v0 j) (v1 j) = 0 := Classical.byContradiction hdv
      have hdu : det2Pair (u0 i) (u1 i) (u0 j) (u1 j) ≠ 0 := fun h => hnot_both ⟨h, hdv0⟩
      have ⟨hw0, hw2⟩ := cramer2_zero hdu hri.2.1 hrj.2.1
      have ⟨hw1, hw3⟩ := cramer2_zero hdu hri.2.2 hrj.2.2
      apply sliceM_ne_rank1 (M i) (W (π i)) (V (π i)) (hMi_nz i hi)
      intro c b hc hb
      rw [hMi_expr i c b hi hc hb, hci4, zero_mul, zero_mul, add_zero]
      have hc4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases hc4 with rfl | rfl | rfl | rfl <;>
        simp [hw0, hw1, hw2, hw3, mul_zero, zero_mul, add_zero]

/-- **Theorem T3h (Exact Strassen–Winograd Optimality `rank_F(⟨2, 2, 2⟩) = 7` Over EVERY Field `F`):**
Over EVERY `SimpleField F` (of ANY characteristic, including `F_2`!):
1. `rank_F(⟨2, 2, 2⟩) ≤ 7` (Strassen's 1969 7-product bilinear algorithm); AND
2. `rank_F(⟨2, 2, 2⟩) ≥ 7` (Winograd's 1971 exact lower bound — zero characteristic restriction!). -/
theorem t3h_strassen_winograd_exact_rank_seven :
    (∀ (F : Type) [SimpleField F],
      HasTensorRankAtMost 4 4 4 7 (fun a b c => intToR (R := F) (matMul2Tensor a b c))) ∧
    (∀ (F : Type) [SimpleField F] (r : Nat),
      HasTensorRankAtMost 4 4 4 r (fun a b c => intToR (R := F) (matMul2Tensor a b c)) →
      7 ≤ r) :=
  ⟨strassen_rank_le_seven, winograd_rank_ge_seven⟩

end
end TriadFrontier.StrassenWinograd
