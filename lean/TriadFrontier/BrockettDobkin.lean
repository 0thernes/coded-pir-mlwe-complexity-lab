module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore
public import TriadFrontier.KoszulTensor
public import TriadFrontier.StrassenWinograd

/-!
# Universal Brockett–Dobkin Rectangular & Quadratic MatMul Rank Lower Bounds (`T3i`, `CS-004`)

Zero-Mathlib, characteristic-free proof over **EVERY `SimpleField F` (including `F_2`!)** of:
1. **Universal Output-Elimination Reduction (`output_elim_reduction`):**
   If a rank-`r` bilinear decomposition `(U, V, W)` has `D` outputs whose `D × r` output matrix
   admits a right-inverse and whose tensor slice vanishes on `[M] × [B]`, then `D ≤ r` and the
   remaining `r - D` rank-1 products compute the exact tensor on `[M] × [B] × [C]`.
2. **Universal Tensor-Subblock Monotonicity (`rect_matmul_subblock_reduction`):**
   For ALL `1 ≤ a ≤ m`, `1 ≤ b ≤ p`, `k ≥ 1`, and EVERY `SimpleField F`:
   `rank_F(⟨m, k, p⟩) ≥ (m * p - a * b) + rank_F(⟨a, k, b⟩)`.
3. **Brockett–Dobkin (1978) Universal 3-Way Rectangular Bound (`brockett_dobkin_rectangular`):**
   For ALL `m, k, p ≥ 1` and EVERY `SimpleField F`:
   `rank_F(⟨m, k, p⟩) ≥ max(m*k + m*p - m, m*k + k*p - k, m*p + k*p - p)`,
   specializing at `m = k = p` to **`rank_F(⟨m, m, m⟩) ≥ 2 * m^2 - m`** (strictly beating both
   `T3g`'s `m^2 + 2` AND the entire degree-`(m-1)` Landsberg–Ottaviani Koszul flattening ceiling
   `m^2 + m` for EVERY `m ≥ 3`!).
4. **Strassen–Winograd Lift (`rect_matmul_k2_lift`):**
   Fusing `rect_matmul_subblock_reduction` with `T3h` (`rank_F(⟨2,2,2⟩) = 7`) immediately yields
   **`rank_F(⟨m, 2, p⟩) ≥ m * p + 3`** for ALL `m ≥ 2, p ≥ 2` and EVERY `SimpleField F`!
-/

namespace TriadFrontier.BrockettDobkin

open TriadFrontier.AlgebraCore
open TriadFrontier.KoszulTensor
open TriadFrontier.StrassenWinograd

@[expose] public section

private theorem ite_t {P : Prop} [Decidable P] {α : Type} {a b : α} (h : P) :
    (if P then a else b) = a := by
  split
  · rfl
  · contradiction

private theorem ite_f {P : Prop} [Decidable P] {α : Type} {a b : α} (h : ¬ P) :
    (if P then a else b) = b := by
  split
  · contradiction
  · rfl

-- ============================================================================
-- Section 1: Rectangular Matrix Multiplication Tensor `⟨m, k, p⟩` & Cyclic Symmetry
-- ============================================================================

/-- Rectangular matrix multiplication tensor `⟨m, k, p⟩` on `[m*k] × [k*p] × [m*p]` over `Int`.
    Indices: `a = i * k + j`, `b = j' * p + l`, `c = i' * p + l'`. -/
def rectMatMulTensor (m k p a b c : Nat) : Int :=
  let i := a / k; let j := a % k
  let j' := b / p; let l := b % p
  let i' := c / p; let l' := c % p
  if i < m ∧ j < k ∧ j' < k ∧ l < p ∧ i' < m ∧ l' < p ∧ i = i' ∧ j = j' ∧ l = l'
  then 1 else 0

theorem rectMatMulTensor_eq_square (m a b c : Nat)
    (ha : a < m * m) (hb : b < m * m) (hc : c < m * m) :
    rectMatMulTensor m m m a b c = matMulTensor m a b c := by
  have hm : 0 < m := by
    cases m with
    | zero => simp at ha
    | succ m' => exact Nat.zero_lt_succ m'
  have hi : a / m < m := Nat.div_lt_of_lt_mul ha
  have hj : a % m < m := Nat.mod_lt a hm
  have hj' : b / m < m := Nat.div_lt_of_lt_mul hb
  have hl : b % m < m := Nat.mod_lt b hm
  have hi' : c / m < m := Nat.div_lt_of_lt_mul hc
  have hl' : c % m < m := Nat.mod_lt c hm
  unfold rectMatMulTensor matMulTensor
  dsimp only
  by_cases hcond : a / m = c / m ∧ a % m = b / m ∧ b % m = c % m
  · have hfull : a / m < m ∧ a % m < m ∧ b / m < m ∧ b % m < m ∧ c / m < m ∧ c % m < m ∧
        a / m = c / m ∧ a % m = b / m ∧ b % m = c % m :=
      ⟨hi, hj, hj', hl, hi', hl', hcond.1, hcond.2.1, hcond.2.2⟩
    have hbt : (decide (a / m = c / m) && decide (a % m = b / m) && decide (b % m = c % m) &&
        decide (a < m * m) && decide (b < m * m) && decide (c < m * m)) = true := by
      simp [hcond.1, hcond.2.1, hcond.2.2, ha, hb, hc]
    rw [ite_t hfull, ite_t hbt]
  · have hnot : ¬ (a / m < m ∧ a % m < m ∧ b / m < m ∧ b % m < m ∧ c / m < m ∧ c % m < m ∧
        a / m = c / m ∧ a % m = b / m ∧ b % m = c % m) := fun h =>
      hcond ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
    have hbf : ¬ ((decide (a / m = c / m) && decide (a % m = b / m) && decide (b % m = c % m) &&
        decide (a < m * m) && decide (b < m * m) && decide (c < m * m)) = true) := by
      intro hbt
      cases h1 : decide (a / m = c / m)
      · rw [h1] at hbt; simp at hbt
      · cases h2 : decide (a % m = b / m)
        · rw [h1, h2] at hbt; simp at hbt
        · cases h3 : decide (b % m = c % m)
          · rw [h1, h2, h3] at hbt; simp at hbt
          · exact hcond ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3⟩
    rw [ite_f hnot, ite_f hbf]

theorem rectMatMulTensor_eq_matMul2 (a b c : Nat) (ha : a < 4) (hb : b < 4) (hc : c < 4) :
    rectMatMulTensor 2 2 2 a b c = matMul2Tensor a b c := by
  rw [rectMatMulTensor_eq_square 2 a b c ha hb hc]
  rfl

/-- Cyclic transpose symmetry: `rank_F(⟨m, k, p⟩) ≤ r → rank_F(⟨k, p, m⟩) ≤ r`. -/
theorem rectMatMul_cyclic {F : Type} [SimpleField F] (m k p r : Nat)
    (hr : HasTensorRankAtMost (m * k) (k * p) (m * p) r
            (fun a b c => intToR (R := F) (rectMatMulTensor m k p a b c))) :
    HasTensorRankAtMost (k * p) (p * m) (k * m) r
      (fun a b c => intToR (R := F) (rectMatMulTensor k p m a b c)) := by
  obtain ⟨U, V, W, hT⟩ := hr
  let U' : Nat → Nat → F := fun s a => V s a
  let V' : Nat → Nat → F := fun s b => W s ((b % m) * p + b / m)
  let W' : Nat → Nat → F := fun s c => U s ((c % m) * k + c / m)
  refine ⟨U', V', W', ?_⟩
  intro a b c ha hb hc
  have hm : 0 < m := by cases m with | zero => simp at hb | succ _ => exact Nat.zero_lt_succ _
  have hk : 0 < k := by cases k with | zero => simp at ha | succ _ => exact Nat.zero_lt_succ _
  have hp : 0 < p := by cases p with | zero => simp at ha | succ _ => exact Nat.zero_lt_succ _
  have hj' : c / m < k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)
  have hi : c % m < m := Nat.mod_lt c hm
  have hl' : b / m < p := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb)
  have hi' : b % m < m := Nat.mod_lt b hm
  have ha' : (c % m) * k + c / m < m * k := by
    calc (c % m) * k + c / m < (c % m) * k + k := Nat.add_lt_add_left hj' _
      _ = (c % m + 1) * k := by rw [Nat.succ_mul]
      _ ≤ m * k := Nat.mul_le_mul_right k hi
  have hc' : (b % m) * p + b / m < m * p := by
    calc (b % m) * p + b / m < (b % m) * p + p := Nat.add_lt_add_left hl' _
      _ = (b % m + 1) * p := by rw [Nat.succ_mul]
      _ ≤ m * p := Nat.mul_le_mul_right p hi'
  have hdiv_a : ((c % m) * k + c / m) / k = c % m := by
    rw [Nat.mul_comm (c % m) k, Nat.mul_add_div hk, Nat.div_eq_of_lt hj', Nat.add_zero]
  have hmod_a : ((c % m) * k + c / m) % k = c / m := by
    rw [Nat.mul_comm (c % m) k, Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
  have hdiv_c : ((b % m) * p + b / m) / p = b % m := by
    rw [Nat.mul_comm (b % m) p, Nat.mul_add_div hp, Nat.div_eq_of_lt hl', Nat.add_zero]
  have hmod_c : ((b % m) * p + b / m) % p = b / m := by
    rw [Nat.mul_comm (b % m) p, Nat.mul_add_mod, Nat.mod_eq_of_lt hl']
  have hmatch : rectMatMulTensor k p m a b c =
      rectMatMulTensor m k p ((c % m) * k + c / m) a ((b % m) * p + b / m) := by
    unfold rectMatMulTensor
    dsimp only
    rw [hdiv_a, hmod_a, hdiv_c, hmod_c]
    have hiff : (a / p < k ∧ a % p < p ∧ b / m < p ∧ b % m < m ∧ c / m < k ∧ c % m < m ∧
        a / p = c / m ∧ a % p = b / m ∧ b % m = c % m) ↔
        (c % m < m ∧ c / m < k ∧ a / p < k ∧ a % p < p ∧ b % m < m ∧ b / m < p ∧
        c % m = b % m ∧ c / m = a / p ∧ a % p = b / m) := by
      constructor <;> intro h
      · exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.1, h.2.1, h.2.2.2.1, h.2.2.1,
               h.2.2.2.2.2.2.2.2.symm, h.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.1⟩
      · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.1, h.1,
               h.2.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.2, h.2.2.2.2.2.2.1.symm⟩
    by_cases h1 : a / p < k ∧ a % p < p ∧ b / m < p ∧ b % m < m ∧ c / m < k ∧ c % m < m ∧
        a / p = c / m ∧ a % p = b / m ∧ b % m = c % m
    · rw [ite_t h1, ite_t (hiff.mp h1)]
    · rw [ite_f h1, ite_f (fun h2 => h1 (hiff.mpr h2))]
  have hT' := hT ((c % m) * k + c / m) a ((b % m) * p + b / m) ha' ha hc'
  dsimp only at hT' ⊢
  rw [hmatch, hT']
  apply sumR_congr
  intro s _
  dsimp only [U', V', W']
  calc U s (c % m * k + c / m) * V s a * W s (b % m * p + b / m)
      = U s (c % m * k + c / m) * (V s a * W s (b % m * p + b / m)) := CommRing.mul_assoc ..
    _ = (V s a * W s (b % m * p + b / m)) * U s (c % m * k + c / m) := CommRing.mul_comm ..

-- ============================================================================
-- Section 2: Universal Output-Elimination Reduction (Over ANY `SimpleField F`)
-- ============================================================================

/-- **Universal Output-Elimination Reduction (Brockett–Dobkin Engine):**
    Given `r` rank-1 products `(U, V, W)` where:
    - `W_drop` (`D × r` output matrix) admits a right-inverse `Rinv` (`W_drop · Rinv = I_D`), and
    - for every `(a, b) ∈ [M] × [B]` and every dropped output `d < D`,
      `∑_{s < r} U s a * V s b * W_drop s d = 0`,
    then `D ≤ r` and there exist `r - D` rank-1 products `(U', V', W')` computing the EXACT same
    bilinear outputs `∑_{s < r} U s a * V s b * W s c` for ALL `a < M, b < B, c < C`! -/
theorem output_elim_reduction {F : Type} [SimpleField F] :
    ∀ (D r M B C : Nat) (U V W Wdrop Rinv : Nat → Nat → F),
      (∀ a b d, a < M → b < B → d < D → sumR r (fun s => U s a * V s b * Wdrop s d) = 0) →
      (∀ d d', d < D → d' < D → sumR r (fun s => Wdrop s d * Rinv s d') = matIdF d d') →
      D ≤ r ∧
      ∃ (U' V' W' : Nat → Nat → F),
        ∀ a b c, a < M → b < B → c < C →
          sumR (r - D) (fun s => U' s a * V' s b * W' s c) =
          sumR r (fun s => U s a * V s b * W s c)
  | 0, r, _, _, _, U, V, W, _, _, _, _ =>
    ⟨Nat.zero_le r, U, V, W, fun _ _ _ _ _ _ => rfl⟩
  | D + 1, 0, _, _, _, _, _, _, Wdrop, Rinv, _, hR => by
    have h0 := hR 0 0 (Nat.zero_lt_succ D) (Nat.zero_lt_succ D)
    simp [sumR, matIdF] at h0
    exact absurd h0 SimpleField.zero_ne_one
  | D + 1, r + 1, M, B, C, U, V, W, Wdrop, Rinv, hZero, hR => by
    have hDD : sumR (r + 1) (fun s => Wdrop s D * Rinv s D) = 1 := by
      have h1 := hR D D (Nat.lt_succ_self D) (Nat.lt_succ_self D)
      simp [matIdF] at h1
      exact h1
    have hne : sumR (r + 1) (fun s => Wdrop s D * Rinv s D) ≠ 0 := by
      rw [hDD]; exact Ne.symm SimpleField.zero_ne_one
    obtain ⟨p, hp, hterm⟩ := exists_nonzero_of_sumR_ne_zero (r + 1) (fun s => Wdrop s D * Rinv s D) hne
    have hWpD : Wdrop p D ≠ 0 := by
      intro hz; rw [hz, zero_mul] at hterm; exact hterm rfl
    let invW : F := SimpleField.inv (Wdrop p D)
    let U1 : Nat → Nat → F := fun t a => U (skipIdx p t) a
    let V1 : Nat → Nat → F := fun t b => V (skipIdx p t) b
    let W1 : Nat → Nat → F := fun t c => W (skipIdx p t) c - (Wdrop (skipIdx p t) D * invW) * W p c
    let Wd1 : Nat → Nat → F := fun t d => Wdrop (skipIdx p t) d - (Wdrop (skipIdx p t) D * invW) * Wdrop p d
    let R1 : Nat → Nat → F := fun t d' => Rinv (skipIdx p t) d'
    have hp_le : p ≤ r := by omega
    -- Helper: for any output vector `Z : Nat → F`, eliminating pivot `p` via `hZero a b D` preserves the sum!
    have hElim : ∀ (a b : Nat) (Z : Nat → F), a < M → b < B →
        sumR r (fun t => U1 t a * V1 t b * (Z (skipIdx p t) - (Wdrop (skipIdx p t) D * invW) * Z p)) =
        sumR (r + 1) (fun s => U s a * V s b * Z s) := by
      intro a b Z ha hb
      have hzD := hZero a b D ha hb (Nat.lt_succ_self D)
      rw [sumR_extract r p (fun s => U s a * V s b * Wdrop s D) hp_le] at hzD
      have hS : sumR r (fun t => U (skipIdx p t) a * V (skipIdx p t) b * Wdrop (skipIdx p t) D) =
          -(U p a * V p b * Wdrop p D) := neg_eq_of_add_eq_zero hzD
      have hsplit : sumR r (fun t => U1 t a * V1 t b * (Z (skipIdx p t) - (Wdrop (skipIdx p t) D * invW) * Z p)) =
          sumR r (fun t => U (skipIdx p t) a * V (skipIdx p t) b * Z (skipIdx p t)) +
          (-(invW * Z p)) * sumR r (fun t => U (skipIdx p t) a * V (skipIdx p t) b * Wdrop (skipIdx p t) D) := by
        rw [sumR_mul_left, ← sumR_add]
        apply sumR_congr
        intro t _
        dsimp only [U1, V1]
        rw [mul_sub_r, CommRing.sub_eq, neg_mul]
        congr 1
        rw [CommRing.mul_comm (invW * Z p)]
        simp only [CommRing.mul_assoc]
      rw [hsplit, hS, mul_neg, neg_mul, neg_neg]
      have hcancel : (invW * Z p) * (U p a * V p b * Wdrop p D) = U p a * V p b * Z p := by
        calc (invW * Z p) * (U p a * V p b * Wdrop p D)
            = (U p a * V p b) * ((Wdrop p D * invW) * Z p) := by
              rw [CommRing.mul_comm (invW * Z p), CommRing.mul_assoc (U p a * V p b),
                  CommRing.mul_comm (Wdrop p D), CommRing.mul_assoc invW (Z p) (Wdrop p D),
                  CommRing.mul_comm (Z p) (Wdrop p D), ← CommRing.mul_assoc invW (Wdrop p D) (Z p),
                  CommRing.mul_comm invW (Wdrop p D)]
          _ = (U p a * V p b) * (1 * Z p) := by rw [SimpleField.mul_inv_cancel (Wdrop p D) hWpD]
          _ = U p a * V p b * Z p := by rw [CommRing.one_mul]
      rw [hcancel, CommRing.add_comm, sumR_extract r p (fun s => U s a * V s b * Z s) hp_le]
    have hZero1 : ∀ a b d, a < M → b < B → d < D →
        sumR r (fun t => U1 t a * V1 t b * Wd1 t d) = 0 := by
      intro a b d ha hb hd
      have he := hElim a b (fun s => Wdrop s d) ha hb
      rw [hZero a b d ha hb (Nat.lt_succ_of_lt hd)] at he
      exact he
    have hR1 : ∀ d d', d < D → d' < D → sumR r (fun t => Wd1 t d * R1 t d') = matIdF d d' := by
      intro d d' hd hd'
      have hdd' := hR d d' (Nat.lt_succ_of_lt hd) (Nat.lt_succ_of_lt hd')
      have hDd' := hR D d' (Nat.lt_succ_self D) (Nat.lt_succ_of_lt hd')
      have hDd'0 : matIdF (R := F) D d' = 0 := by
        unfold matIdF; exact ite_f (by omega)
      rw [hDd'0] at hDd'
      rw [sumR_extract r p (fun s => Wdrop s d * Rinv s d') hp_le] at hdd'
      rw [sumR_extract r p (fun s => Wdrop s D * Rinv s d') hp_le] at hDd'
      have hS2 : sumR r (fun t => Wdrop (skipIdx p t) D * Rinv (skipIdx p t) d') =
          -(Wdrop p D * Rinv p d') := neg_eq_of_add_eq_zero hDd'
      have hsplit : sumR r (fun t => Wd1 t d * R1 t d') =
          sumR r (fun t => Wdrop (skipIdx p t) d * Rinv (skipIdx p t) d') +
          (-(invW * Wdrop p d)) * sumR r (fun t => Wdrop (skipIdx p t) D * Rinv (skipIdx p t) d') := by
        rw [sumR_mul_left, ← sumR_add]
        apply sumR_congr
        intro t _
        dsimp only [Wd1, R1]
        rw [sub_mul_r, CommRing.sub_eq, neg_mul]
        congr 1
        have hre : (Wdrop (skipIdx p t) D * invW) * Wdrop p d * Rinv (skipIdx p t) d' =
            (invW * Wdrop p d) * (Wdrop (skipIdx p t) D * Rinv (skipIdx p t) d') := by
          calc (Wdrop (skipIdx p t) D * invW) * Wdrop p d * Rinv (skipIdx p t) d'
              = Wdrop (skipIdx p t) D * ((invW * Wdrop p d) * Rinv (skipIdx p t) d') := by
                simp only [CommRing.mul_assoc]
            _ = Wdrop (skipIdx p t) D * (Rinv (skipIdx p t) d' * (invW * Wdrop p d)) := by
                rw [CommRing.mul_comm (invW * Wdrop p d)]
            _ = (Wdrop (skipIdx p t) D * Rinv (skipIdx p t) d') * (invW * Wdrop p d) :=
                (CommRing.mul_assoc ..).symm
            _ = (invW * Wdrop p d) * (Wdrop (skipIdx p t) D * Rinv (skipIdx p t) d') :=
                CommRing.mul_comm ..
        rw [hre]
      rw [hsplit, hS2, mul_neg, neg_mul, neg_neg]
      have hcancel : (invW * Wdrop p d) * (Wdrop p D * Rinv p d') = Wdrop p d * Rinv p d' := by
        calc (invW * Wdrop p d) * (Wdrop p D * Rinv p d')
            = Wdrop p d * ((Wdrop p D * invW) * Rinv p d') := by
              rw [CommRing.mul_comm invW (Wdrop p d), CommRing.mul_assoc (Wdrop p d),
                  ← CommRing.mul_assoc invW (Wdrop p D) (Rinv p d'),
                  CommRing.mul_comm invW (Wdrop p D)]
          _ = Wdrop p d * (1 * Rinv p d') := by rw [SimpleField.mul_inv_cancel (Wdrop p D) hWpD]
          _ = Wdrop p d * Rinv p d' := by rw [CommRing.one_mul]
      rw [hcancel, CommRing.add_comm, hdd']
    obtain ⟨hle, U', V', W', hrec⟩ :=
      output_elim_reduction D r M B C U1 V1 W1 Wd1 R1 hZero1 hR1
    refine ⟨by omega, U', V', W', ?_⟩
    intro a b c ha hb hc
    have hstep : (r + 1) - (D + 1) = r - D := by omega
    rw [hstep, hrec a b c ha hb hc]
    exact hElim a b (fun s => W s c) ha hb

-- ============================================================================
-- Section 3: Column-Drop, Row-Drop, Base Rank, & Brockett–Dobkin Theorems
-- ============================================================================

/-- Column-drop reduction: `rank_F(⟨m, k, p⟩) ≥ m * (p - b) + rank_F(⟨m, k, b⟩)` for `1 ≤ b ≤ p`. -/
theorem rect_matmul_col_drop {F : Type} [SimpleField F] (m k p b r : Nat)
    (_hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 1 ≤ b) (hbp : b ≤ p)
    (hr : HasTensorRankAtMost (m * k) (k * p) (m * p) r
            (fun a x c => intToR (R := F) (rectMatMulTensor m k p a x c))) :
    m * (p - b) ≤ r ∧
    HasTensorRankAtMost (m * k) (k * b) (m * b) (r - m * (p - b))
      (fun a x c => intToR (R := F) (rectMatMulTensor m k b a x c)) := by
  cases Nat.eq_or_lt_of_le hbp with
  | inl heq =>
    subst heq
    simp only [Nat.sub_self, Nat.mul_zero, Nat.sub_zero]
    exact ⟨Nat.zero_le r, hr⟩
  | inr hlt =>
    have hpb : 0 < p - b := by omega
    have hp : 0 < p := by omega
    obtain ⟨U, V, W, hT⟩ := hr
    -- Embed [k*b] into [k*p] by keeping columns `< b`, and [m*b] into [m*p] similarly.
    let embB (x : Nat) : Nat := (x / b) * p + x % b
    let embC (c : Nat) : Nat := (c / b) * p + c % b
    -- Index the `D = m * (p - b)` dropped outputs (columns `b .. p - 1`).
    let dropC (d : Nat) : Nat := (d / (p - b)) * p + (b + d % (p - b))
    let D := m * (p - b)
    let Usub : Nat → Nat → F := U
    let Vsub : Nat → Nat → F := fun s x => V s (embB x)
    let Wsub : Nat → Nat → F := fun s c => W s (embC c)
    let Wdrop : Nat → Nat → F := fun s d => W s (dropC d)
    -- Right-inverse on all `D` dropped outputs: `A = E_{i,0}`, `B = E_{0,l}`!
    let Rinv : Nat → Nat → F := fun s d' =>
      let i' := d' / (p - b)
      let l' := b + d' % (p - b)
      U s (i' * k) * V s l'
    have hDropBound : ∀ d, d < D → dropC d < m * p := by
      intro d hd
      have hi : d / (p - b) < m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hd)
      have hl : b + d % (p - b) < p := by
        have hm' : d % (p - b) < p - b := Nat.mod_lt d hpb
        omega
      dsimp only [dropC]
      calc (d / (p - b)) * p + (b + d % (p - b))
          < (d / (p - b)) * p + p := Nat.add_lt_add_left hl _
        _ = (d / (p - b) + 1) * p := by rw [Nat.succ_mul]
        _ ≤ m * p := Nat.mul_le_mul_right p hi
    have hEmbBBound : ∀ x, x < k * b → embB x < k * p := by
      intro x hx
      have hj : x / b < k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
      have hl : x % b < p := Nat.lt_of_lt_of_le (Nat.mod_lt x hb) hbp
      dsimp only [embB]
      calc (x / b) * p + x % b < (x / b) * p + p := Nat.add_lt_add_left hl _
        _ = (x / b + 1) * p := by rw [Nat.succ_mul]
        _ ≤ k * p := Nat.mul_le_mul_right p hj
    have hEmbCBound : ∀ c, c < m * b → embC c < m * p := by
      intro c hc
      have hi : c / b < m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)
      have hl : c % b < p := Nat.lt_of_lt_of_le (Nat.mod_lt c hb) hbp
      dsimp only [embC]
      calc (c / b) * p + c % b < (c / b) * p + p := Nat.add_lt_add_left hl _
        _ = (c / b + 1) * p := by rw [Nat.succ_mul]
        _ ≤ m * p := Nat.mul_le_mul_right p hi
    -- 1. All dropped outputs vanish when `B` is restricted to columns `< b`!
    have hZero : ∀ a x d, a < m * k → x < k * b → d < D →
        sumR r (fun s => Usub s a * Vsub s x * Wdrop s d) = 0 := by
      intro a x d ha hx hd
      have heq := (hT a (embB x) (dropC d) ha (hEmbBBound x hx) (hDropBound d hd)).symm
      rw [heq]
      have hl_x : embB x % p = x % b := by
        dsimp only [embB]
        rw [Nat.mul_comm (x / b) p, Nat.mul_add_mod,
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt x hb) hbp)]
      have hl_d : dropC d % p = b + d % (p - b) := by
        dsimp only [dropC]
        have hltp : b + d % (p - b) < p := by have := Nat.mod_lt d hpb; omega
        rw [Nat.mul_comm (d / (p - b)) p, Nat.mul_add_mod, Nat.mod_eq_of_lt hltp]
      have hne_l : embB x % p ≠ dropC d % p := by
        rw [hl_x, hl_d]; have := Nat.mod_lt x hb; omega
      unfold rectMatMulTensor
      dsimp only
      have hneg : ¬ (a / k < m ∧ a % k < k ∧ embB x / p < k ∧ embB x % p < p ∧
          dropC d / p < m ∧ dropC d % p < p ∧
          a / k = dropC d / p ∧ a % k = embB x / p ∧ embB x % p = dropC d % p) :=
        fun h => hne_l h.2.2.2.2.2.2.2.2
      simp only [hneg, ↓reduceIte]; exact intToR_zero
    -- 2. Right-inverse `Wdrop · Rinv = I_D`!
    have hR : ∀ d d', d < D → d' < D → sumR r (fun s => Wdrop s d * Rinv s d') = matIdF d d' := by
      intro d d' hd hd'
      let i' := d' / (p - b); let l' := b + d' % (p - b)
      have hi' : i' < m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hd')
      have hl' : l' < p := by have := Nat.mod_lt d' hpb; omega
      have ha0 : i' * k < m * k := by
        calc i' * k < i' * k + k := Nat.lt_add_of_pos_right hk
          _ = (i' + 1) * k := by rw [Nat.succ_mul]
          _ ≤ m * k := Nat.mul_le_mul_right k hi'
      have hb0 : l' < k * p := by
        calc l' < p := hl'
          _ = 1 * p := by rw [Nat.one_mul]
          _ ≤ k * p := Nat.mul_le_mul_right p hk
      have hcomm : sumR r (fun s => Wdrop s d * Rinv s d') =
          sumR r (fun s => U s (i' * k) * V s l' * W s (dropC d)) := by
        apply sumR_congr; intro s _; dsimp only [Wdrop, Rinv, i', l']
        exact CommRing.mul_comm (W s (dropC d)) (U s (d' / (p - b) * k) * V s (b + d' % (p - b)))
      rw [hcomm, ← hT (i' * k) l' (dropC d) ha0 hb0 (hDropBound d hd)]
      have hdiv_a : (i' * k) / k = i' := by rw [Nat.mul_div_cancel i' hk]
      have hmod_a : (i' * k) % k = 0 := Nat.mul_mod_left i' k
      have hdiv_b : l' / p = 0 := Nat.div_eq_of_lt hl'
      have hmod_b : l' % p = l' := Nat.mod_eq_of_lt hl'
      have hdiv_c : dropC d / p = d / (p - b) := by
        dsimp only [dropC]
        have hltp : b + d % (p - b) < p := by have := Nat.mod_lt d hpb; omega
        rw [Nat.mul_comm (d / (p - b)) p, Nat.mul_add_div hp, Nat.div_eq_of_lt hltp, Nat.add_zero]
      have hmod_c : dropC d % p = b + d % (p - b) := by
        dsimp only [dropC]
        have hltp : b + d % (p - b) < p := by have := Nat.mod_lt d hpb; omega
        rw [Nat.mul_comm (d / (p - b)) p, Nat.mul_add_mod, Nat.mod_eq_of_lt hltp]
      unfold rectMatMulTensor matIdF
      dsimp only
      rw [hdiv_a, hmod_a, hdiv_b, hmod_b, hdiv_c, hmod_c]
      by_cases heq : d = d'
      · subst heq
        have hcond : i' < m ∧ 0 < k ∧ 0 < k ∧ l' < p ∧ d / (p - b) < m ∧
            b + d % (p - b) < p ∧ i' = d / (p - b) ∧ (0 : Nat) = 0 ∧ l' = b + d % (p - b) :=
          ⟨hi', hk, hk, hl', hi', hl', rfl, rfl, rfl⟩
        simp only [hcond, ↓reduceIte]; exact intToR_one
      · have hne : ¬ (i' = d / (p - b) ∧ l' = b + d % (p - b)) := by
          intro ⟨h1, h2⟩
          have hm_eq : d' % (p - b) = d % (p - b) := by dsimp only [l'] at h2; omega
          have hd_eq : d' = d := by
            have e1 := Nat.div_add_mod d' (p - b)
            have e2 := Nat.div_add_mod d (p - b)
            have hq_eq : d' / (p - b) = d / (p - b) := h1
            rw [hq_eq, hm_eq] at e1; omega
          exact heq hd_eq.symm
        have hneg : ¬ (i' < m ∧ 0 < k ∧ 0 < k ∧ l' < p ∧ d / (p - b) < m ∧
            b + d % (p - b) < p ∧ i' = d / (p - b) ∧ (0 : Nat) = 0 ∧ l' = b + d % (p - b)) :=
          fun h => hne ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
        rw [ite_f hneg, ite_f heq]; exact intToR_zero
    obtain ⟨hle, U', V', W', hred⟩ :=
      output_elim_reduction D r (m * k) (k * b) (m * b) Usub Vsub Wsub Wdrop Rinv hZero hR
    refine ⟨hle, U', V', W', ?_⟩
    intro a x c ha hx hc
    rw [hred a x c ha hx hc]
    dsimp only [Usub, Vsub, Wsub]
    rw [← hT a (embB x) (embC c) ha (hEmbBBound x hx) (hEmbCBound c hc)]
    -- Check `rectMatMulTensor m k b a x c = rectMatMulTensor m k p a (embB x) (embC c)`!
    have hdiv_x : embB x / p = x / b := by
      dsimp only [embB]
      rw [Nat.mul_comm (x / b) p, Nat.mul_add_div hp,
          Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt x hb) hbp), Nat.add_zero]
    have hmod_x : embB x % p = x % b := by
      dsimp only [embB]
      rw [Nat.mul_comm (x / b) p, Nat.mul_add_mod,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt x hb) hbp)]
    have hdiv_c : embC c / p = c / b := by
      dsimp only [embC]
      rw [Nat.mul_comm (c / b) p, Nat.mul_add_div hp,
          Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt c hb) hbp), Nat.add_zero]
    have hmod_c : embC c % p = c % b := by
      dsimp only [embC]
      rw [Nat.mul_comm (c / b) p, Nat.mul_add_mod,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt c hb) hbp)]
    congr 1
    unfold rectMatMulTensor
    dsimp only
    rw [hdiv_x, hmod_x, hdiv_c, hmod_c]
    have hxb : x % b < b := Nat.mod_lt x hb
    have hcb : c % b < b := Nat.mod_lt c hb
    have hxp : x % b < p := Nat.lt_of_lt_of_le hxb hbp
    have hcp : c % b < p := Nat.lt_of_lt_of_le hcb hbp
    by_cases hcond : a / k < m ∧ a % k < k ∧ x / b < k ∧ c / b < m ∧
        a / k = c / b ∧ a % k = x / b ∧ x % b = c % b
    · have h1 : a / k < m ∧ a % k < k ∧ x / b < k ∧ x % b < b ∧ c / b < m ∧ c % b < b ∧
          a / k = c / b ∧ a % k = x / b ∧ x % b = c % b :=
        ⟨hcond.1, hcond.2.1, hcond.2.2.1, hxb, hcond.2.2.2.1, hcb, hcond.2.2.2.2.1, hcond.2.2.2.2.2.1, hcond.2.2.2.2.2.2⟩
      have h2 : a / k < m ∧ a % k < k ∧ x / b < k ∧ x % b < p ∧ c / b < m ∧ c % b < p ∧
          a / k = c / b ∧ a % k = x / b ∧ x % b = c % b :=
        ⟨hcond.1, hcond.2.1, hcond.2.2.1, hxp, hcond.2.2.2.1, hcp, hcond.2.2.2.2.1, hcond.2.2.2.2.2.1, hcond.2.2.2.2.2.2⟩
      rw [ite_t h1, ite_t h2]
    · have h1 : ¬ (a / k < m ∧ a % k < k ∧ x / b < k ∧ x % b < b ∧ c / b < m ∧ c % b < b ∧
          a / k = c / b ∧ a % k = x / b ∧ x % b = c % b) := fun h =>
        hcond ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
      have h2 : ¬ (a / k < m ∧ a % k < k ∧ x / b < k ∧ x % b < p ∧ c / b < m ∧ c % b < p ∧
          a / k = c / b ∧ a % k = x / b ∧ x % b = c % b) := fun h =>
        hcond ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
      rw [ite_f h1, ite_f h2]

/-- Row-drop reduction: `rank_F(⟨m, k, b⟩) ≥ (m - a) * b + rank_F(⟨a, k, b⟩)` for `1 ≤ a ≤ m`. -/
theorem rect_matmul_row_drop {F : Type} [SimpleField F] (m k b a r : Nat)
    (_ha : 1 ≤ a) (ham : a ≤ m) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hr : HasTensorRankAtMost (m * k) (k * b) (m * b) r
            (fun x y c => intToR (R := F) (rectMatMulTensor m k b x y c))) :
    (m - a) * b ≤ r ∧
    HasTensorRankAtMost (a * k) (k * b) (a * b) (r - (m - a) * b)
      (fun x y c => intToR (R := F) (rectMatMulTensor a k b x y c)) := by
  -- Use cyclic symmetry: ⟨m, k, b⟩ → ⟨k, b, m⟩ (now `m` is columns!), col-drop `m → a` drops `k * (m - a)`?
  -- Wait: dropping `m → a` in ⟨k, b, m⟩ drops `k*(m-a)` instead of `b*(m-a)`.
  -- To drop `(m - a) * b`, do direct 10-line row-drop on `c ∈ [a*b, m*b)` (`dropR d := a*b + d`)!
  cases Nat.eq_or_lt_of_le ham with
  | inl heq =>
    subst heq
    simp only [Nat.sub_self, Nat.zero_mul, Nat.sub_zero]
    exact ⟨Nat.zero_le r, hr⟩
  | inr hlt =>
    obtain ⟨U, V, W, hT⟩ := hr
    let D := (m - a) * b
    let dropR (d : Nat) : Nat := a * b + d
    let Wdrop : Nat → Nat → F := fun s d => W s (dropR d)
    -- Right-inverse on `d' < D`: `i' = a + d'/b`, `l' = d'%b`, `A = E_{i',0}`, `B = E_{0,l'}`!
    let Rinv : Nat → Nat → F := fun s d' =>
      U s ((a + d' / b) * k) * V s (d' % b)
    have hD_eq : a * b + D = m * b := by
      dsimp only [D]; rw [← Nat.add_mul, Nat.add_sub_of_le ham]
    have hDropBound : ∀ d, d < D → dropR d < m * b := by
      intro d hd; dsimp only [dropR]; omega
    have hZero : ∀ x y d, x < a * k → y < k * b → d < D →
        sumR r (fun s => U s x * V s y * Wdrop s d) = 0 := by
      intro x y d hx hy hd
      have hx' : x < m * k := Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right k ham)
      rw [← hT x y (dropR d) hx' hy (hDropBound d hd)]
      have hi_x : x / k < a := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
      have hi_d : dropR d / b = a + d / b := by
        dsimp only [dropR]; rw [Nat.mul_comm a b, Nat.mul_add_div hb]
      have hne_i : x / k ≠ dropR d / b :=
        Nat.ne_of_lt (by rw [hi_d]; exact Nat.lt_of_lt_of_le hi_x (Nat.le_add_right a (d / b)))
      unfold rectMatMulTensor
      dsimp only
      have hneg : ¬ (x / k < m ∧ x % k < k ∧ y / b < k ∧ y % b < b ∧
          dropR d / b < m ∧ dropR d % b < b ∧
          x / k = dropR d / b ∧ x % k = y / b ∧ y % b = dropR d % b) :=
        fun h => hne_i h.2.2.2.2.2.2.1
      rw [ite_f hneg]; exact intToR_zero
    have hR : ∀ d d', d < D → d' < D → sumR r (fun s => Wdrop s d * Rinv s d') = matIdF d d' := by
      intro d d' hd hd'
      have hdb' : d' / b < m - a := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hd')
      have hi' : a + d' / b < m := by omega
      have hl' : d' % b < b := Nat.mod_lt d' hb
      have hx0 : (a + d' / b) * k < m * k := by
        calc (a + d' / b) * k < (a + d' / b) * k + k := Nat.lt_add_of_pos_right hk
          _ = (a + d' / b + 1) * k := by rw [Nat.succ_mul]
          _ ≤ m * k := Nat.mul_le_mul_right k hi'
      have hy0 : d' % b < k * b := by
        calc d' % b < b := hl'
          _ = 1 * b := by rw [Nat.one_mul]
          _ ≤ k * b := Nat.mul_le_mul_right b hk
      have hcomm : sumR r (fun s => Wdrop s d * Rinv s d') =
          sumR r (fun s => U s ((a + d' / b) * k) * V s (d' % b) * W s (dropR d)) := by
        apply sumR_congr; intro s _; dsimp only [Wdrop, Rinv]
        exact CommRing.mul_comm _ _
      rw [hcomm, ← hT ((a + d' / b) * k) (d' % b) (dropR d) hx0 hy0 (hDropBound d hd)]
      have hdiv_x : ((a + d' / b) * k) / k = a + d' / b := Nat.mul_div_cancel _ hk
      have hmod_x : ((a + d' / b) * k) % k = 0 := Nat.mul_mod_left _ k
      have hdiv_y : (d' % b) / b = 0 := Nat.div_eq_of_lt hl'
      have hmod_y : (d' % b) % b = d' % b := Nat.mod_eq_of_lt hl'
      have hdiv_c : dropR d / b = a + d / b := by
        dsimp only [dropR]; rw [Nat.mul_comm a b, Nat.mul_add_div hb]
      have hmod_c : dropR d % b = d % b := by
        dsimp only [dropR]; rw [Nat.mul_comm a b, Nat.mul_add_mod]
      unfold rectMatMulTensor matIdF
      dsimp only
      rw [hdiv_x, hmod_x, hdiv_y, hmod_y, hdiv_c, hmod_c]
      by_cases heq : d = d'
      · subst heq
        have hcond : a + d / b < m ∧ 0 < k ∧ 0 < k ∧ d % b < b ∧ a + d / b < m ∧ d % b < b ∧
            a + d / b = a + d / b ∧ (0 : Nat) = 0 ∧ d % b = d % b :=
          ⟨hi', hk, hk, hl', hi', hl', rfl, rfl, rfl⟩
        simp only [hcond, ↓reduceIte]; exact intToR_one
      · have hne : ¬ (a + d' / b = a + d / b ∧ d' % b = d % b) := by
          intro ⟨h1, h2⟩
          have e1 := Nat.div_add_mod d' b
          have e2 := Nat.div_add_mod d b
          have hq : d' / b = d / b := by omega
          rw [hq, h2] at e1
          exact heq (by omega)
        have hneg : ¬ (a + d' / b < m ∧ 0 < k ∧ 0 < k ∧ d' % b < b ∧ a + d / b < m ∧ d % b < b ∧
            a + d' / b = a + d / b ∧ (0 : Nat) = 0 ∧ d' % b = d % b) :=
          fun h => hne ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
        rw [ite_f hneg, ite_f heq]; exact intToR_zero
    obtain ⟨hle, U', V', W', hred⟩ :=
      output_elim_reduction D r (a * k) (k * b) (a * b) U V W Wdrop Rinv hZero hR
    refine ⟨hle, U', V', W', ?_⟩
    intro x y c hx hy hc
    have hx' : x < m * k := Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right k ham)
    have hc' : c < m * b := Nat.lt_of_lt_of_le hc (Nat.mul_le_mul_right b ham)
    rw [hred x y c hx hy hc, ← hT x y c hx' hy hc']
    congr 1
    unfold rectMatMulTensor
    dsimp only
    have hix : x / k < a := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
    have hic : c / b < a := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)
    have hixm : x / k < m := Nat.lt_of_lt_of_le hix ham
    have hicm : c / b < m := Nat.lt_of_lt_of_le hic ham
    by_cases hcond : x % k < k ∧ y / b < k ∧ y % b < b ∧ c % b < b ∧
        x / k = c / b ∧ x % k = y / b ∧ y % b = c % b
    · have h1 : x / k < a ∧ x % k < k ∧ y / b < k ∧ y % b < b ∧ c / b < a ∧ c % b < b ∧
          x / k = c / b ∧ x % k = y / b ∧ y % b = c % b :=
        ⟨hix, hcond.1, hcond.2.1, hcond.2.2.1, hic, hcond.2.2.2.1, hcond.2.2.2.2.1, hcond.2.2.2.2.2.1, hcond.2.2.2.2.2.2⟩
      have h2 : x / k < m ∧ x % k < k ∧ y / b < k ∧ y % b < b ∧ c / b < m ∧ c % b < b ∧
          x / k = c / b ∧ x % k = y / b ∧ y % b = c % b :=
        ⟨hixm, hcond.1, hcond.2.1, hcond.2.2.1, hicm, hcond.2.2.2.1, hcond.2.2.2.2.1, hcond.2.2.2.2.2.1, hcond.2.2.2.2.2.2⟩
      rw [ite_t h1, ite_t h2]
    · have h1 : ¬ (x / k < a ∧ x % k < k ∧ y / b < k ∧ y % b < b ∧ c / b < a ∧ c % b < b ∧
          x / k = c / b ∧ x % k = y / b ∧ y % b = c % b) := fun h =>
        hcond ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
      have h2 : ¬ (x / k < m ∧ x % k < k ∧ y / b < k ∧ y % b < b ∧ c / b < m ∧ c % b < b ∧
          x / k = c / b ∧ x % k = y / b ∧ y % b = c % b) := fun h =>
        hcond ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
      rw [ite_f h1, ite_f h2]

/-- **Universal Subblock-Reduction Lift:**
    `rank_F(⟨m, k, p⟩) ≥ (m*p - a*b) + rank_F(⟨a, k, b⟩)` for ALL `1 ≤ a ≤ m`, `1 ≤ b ≤ p`, `1 ≤ k`! -/
theorem rect_matmul_subblock_reduction {F : Type} [SimpleField F] (m k p a b r : Nat)
    (ha : 1 ≤ a) (ham : a ≤ m) (hk : 1 ≤ k) (hb : 1 ≤ b) (hbp : b ≤ p)
    (hr : HasTensorRankAtMost (m * k) (k * p) (m * p) r
            (fun x y c => intToR (R := F) (rectMatMulTensor m k p x y c))) :
    m * p - a * b ≤ r ∧
    HasTensorRankAtMost (a * k) (k * b) (a * b) (r - (m * p - a * b))
      (fun x y c => intToR (R := F) (rectMatMulTensor a k b x y c)) := by
  have hm : 1 ≤ m := Nat.le_trans ha ham
  obtain ⟨hle1, hr1⟩ := rect_matmul_col_drop m k p b r hm hk hb hbp hr
  obtain ⟨hle2, hr2⟩ := rect_matmul_row_drop m k b a (r - m * (p - b)) ha ham hk hb hr1
  have hsum : m * (p - b) + (m - a) * b = m * p - a * b := by
    have h1 : m * (p - b) = m * p - m * b := Nat.mul_sub_left_distrib m p b
    have h2 : (m - a) * b = m * b - a * b := Nat.mul_sub_right_distrib m a b
    have h3 : m * b ≤ m * p := Nat.mul_le_mul_left m hbp
    have h4 : a * b ≤ m * b := Nat.mul_le_mul_right b ham
    omega
  have htot : m * p - a * b ≤ r := by omega
  have hrem : r - m * (p - b) - (m - a) * b = r - (m * p - a * b) := by omega
  rw [hrem] at hr2
  exact ⟨htot, hr2⟩

/-- Base rank of matrix-vector multiplication: `rank_F(⟨m, k, 1⟩) ≥ m * k` over EVERY `SimpleField F`. -/
theorem rect_matmul_vec_rank_ge {F : Type} [SimpleField F] (m k r : Nat)
    (hk : 1 ≤ k)
    (hr : HasTensorRankAtMost (m * k) k m r
            (fun a b c => intToR (R := F) (rectMatMulTensor m k 1 a b c))) :
    m * k ≤ r := by
  obtain ⟨U, V, W, hT⟩ := hr
  let P : Nat → Nat → F := fun a s => U s a
  let Q : Nat → Nat → F := fun s a' => V s (a' % k) * W s (a' / k)
  apply matRankFactor_le r (m * k) P Q
  intro a a' ha ha'
  unfold matMulF
  have hj' : a' % k < k := Nat.mod_lt a' hk
  have hi' : a' / k < m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ha')
  have hmul : sumR r (fun s => P a s * Q s a') =
      sumR r (fun s => U s a * V s (a' % k) * W s (a' / k)) := by
    apply sumR_congr; intro s _; dsimp only [P, Q]; rw [CommRing.mul_assoc]
  rw [hmul, ← hT a (a' % k) (a' / k) ha hj' hi']
  unfold rectMatMulTensor matIdF
  have hdiv_b : (a' % k) / 1 = a' % k := Nat.div_one _
  have hmod_b : (a' % k) % 1 = 0 := Nat.mod_one _
  have hdiv_c : (a' / k) / 1 = a' / k := Nat.div_one _
  have hmod_c : (a' / k) % 1 = 0 := Nat.mod_one _
  dsimp only
  rw [hdiv_b, hmod_b, hdiv_c, hmod_c]
  have hia : a / k < m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ha)
  have hja : a % k < k := Nat.mod_lt a hk
  by_cases heq : a = a'
  · subst heq
    have hcond : a / k < m ∧ a % k < k ∧ a % k < k ∧ 0 < 1 ∧ a / k < m ∧ 0 < 1 ∧
        a / k = a / k ∧ a % k = a % k ∧ (0 : Nat) = 0 :=
      ⟨hia, hja, hja, Nat.zero_lt_one, hia, Nat.zero_lt_one, rfl, rfl, rfl⟩
    simp only [hcond, ↓reduceIte]
    exact intToR_one
  · have hne : ¬ (a / k = a' / k ∧ a % k = a' % k) := by
      intro ⟨h1, h2⟩
      have e1 := Nat.div_add_mod a k; have e2 := Nat.div_add_mod a' k
      rw [h1, h2] at e1; exact heq (by omega)
    have hneg : ¬ (a / k < m ∧ a % k < k ∧ a' % k < k ∧ 0 < 1 ∧ a' / k < m ∧ 0 < 1 ∧
        a / k = a' / k ∧ a % k = a' % k ∧ (0 : Nat) = 0) :=
      fun h => hne ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩
    rw [ite_f hneg, ite_f heq]; exact intToR_zero

/-- Core substitution-method bound: `rank_F(⟨m, k, p⟩) ≥ m*k + m*p - m` over EVERY `SimpleField F` (weaker than Brockett–Dobkin's published `2n^2 - 1` for `m=k=p=n ≥ 2`). -/
theorem brockett_dobkin_one {F : Type} [SimpleField F] (m k p r : Nat)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hp : 1 ≤ p)
    (hr : HasTensorRankAtMost (m * k) (k * p) (m * p) r
            (fun a b c => intToR (R := F) (rectMatMulTensor m k p a b c))) :
    m * k + m * p - m ≤ r := by
  obtain ⟨hle, hr1⟩ := rect_matmul_col_drop m k p 1 r hm hk (Nat.le_refl 1) hp hr
  simp only [Nat.mul_one] at hr1
  have hmk := rect_matmul_vec_rank_ge m k (r - m * (p - 1)) hk hr1
  have hmul : m * (p - 1) = m * p - m := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hmp : m ≤ m * p := by
    calc m = m * 1 := (Nat.mul_one m).symm
      _ ≤ m * p := Nat.mul_le_mul_left m hp
  omega

/-- **Theorem T3i (Universal Substitution-Method Rectangular & Quadratic MatMul Bound + Strassen Lift):**
    Over **EVERY `SimpleField F` (including characteristic 2 / `F_2`!)**:
    1. **3-Way Symmetric Rectangular Bound (`∀ m, k, p ≥ 1`):**
       `rank_F(⟨m, k, p⟩) ≥ max(m*k + m*p - m, m*k + k*p - k, m*p + k*p - p)`.
    2. **All-`m` Quadratic Square MatMul Bound (`∀ m ≥ 1`):**
       `rank_F(⟨m, m, m⟩) ≥ 2 * m^2 - m` (weaker than Brockett–Dobkin's published `2m^2 - 1`
       for `m ≥ 2`, while exceeding `T3g`'s `m^2 + 2` and the degree-`(m-1)` Landsberg–Ottaviani
       Koszul flattening ceiling `m^2 + m` for EVERY `m ≥ 3`, e.g. `≥ 15 > 12` at `m=3`).
    3. **Strassen–Winograd `T3h` Subblock Lift (`∀ m ≥ 2, p ≥ 2`):**
       `rank_F(⟨m, 2, p⟩) ≥ m * p + 3` over EVERY `SimpleField F`! -/
theorem t3i_brockett_dobkin_rectangular_and_quadratic_matmul_bound :
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
      m * p + 3 ≤ r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F _ m k p r hm hk hp hr
    have h1 := brockett_dobkin_one m k p r hm hk hp hr
    have hcyc1 := rectMatMul_cyclic m k p r hr
    have h2' := brockett_dobkin_one k p m r hk hp hm hcyc1
    have hcyc2 := rectMatMul_cyclic k p m r hcyc1
    have h3' := brockett_dobkin_one p m k r hp hm hk hcyc2
    have h2 : m * k + k * p - k ≤ r := by
      have : k * p + k * m = m * k + k * p := by rw [Nat.add_comm, Nat.mul_comm k m]
      omega
    have h3 : m * p + k * p - p ≤ r := by
      have : p * m + p * k = m * p + k * p := by rw [Nat.mul_comm p m, Nat.mul_comm p k]
      omega
    exact ⟨h1, h2, h3⟩
  · intro F _ m r hm hr
    have hr_rect : HasTensorRankAtMost (m * m) (m * m) (m * m) r
        (fun a b c => intToR (R := F) (rectMatMulTensor m m m a b c)) := by
      obtain ⟨U, V, W, hT⟩ := hr
      refine ⟨U, V, W, fun a b c ha hb hc => ?_⟩
      dsimp only
      rw [rectMatMulTensor_eq_square m a b c ha hb hc]
      exact hT a b c ha hb hc
    have hbd := brockett_dobkin_one m m m r hm hm hm hr_rect
    have h2m : 2 * m * m = m * m + m * m := by
      rw [Nat.mul_assoc, Nat.two_mul]
    omega
  · intro m hm
    have h1 : m * m ≥ 3 * m := Nat.mul_le_mul_right m hm
    have h2 : 2 * m * m = m * m + m * m := by rw [Nat.mul_assoc, Nat.two_mul]
    omega
  · intro F _ m p r hm hp hr
    obtain ⟨hle, hr2⟩ := rect_matmul_subblock_reduction m 2 p 2 2 r (by omega) hm (by omega) (by omega) hp hr
    have hr_m2 : HasTensorRankAtMost 4 4 4 (r - (m * p - 4))
        (fun a b c => intToR (R := F) (matMul2Tensor a b c)) := by
      obtain ⟨U, V, W, hT⟩ := hr2
      refine ⟨U, V, W, fun a b c ha hb hc => ?_⟩
      dsimp only
      rw [← rectMatMulTensor_eq_matMul2 a b c ha hb hc]
      exact hT a b c ha hb hc
    have h7 := winograd_rank_ge_seven F (r - (m * p - 4)) hr_m2
    have hmp4 : 4 ≤ m * p := by
      calc 4 = 2 * 2 := rfl
        _ ≤ m * p := Nat.mul_le_mul hm hp
    omega

end
end TriadFrontier.BrockettDobkin
