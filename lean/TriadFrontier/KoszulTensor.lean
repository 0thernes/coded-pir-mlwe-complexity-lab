module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore

/-!
# Universal Koszul Flattening Tensor Rank Lower Bounds (`CS-053` ↔ `CS-004` ↔ `CS-012`)

Unifies the exterior-power wedge operator `u ∧ · : Λ^1(F^n) → Λ^2(F^n)` from Coded PIR (`T1a`)
with Landsberg–Ottaviani Koszul flattenings for Matrix Multiplication (`CS-004`) and Algebraic
Complexity (`CS-012`) over **ANY `SimpleField F` of ANY characteristic**:
1. Universal Steinitz / Gaussian-elimination Matrix Rank Bound: `P Q = I_N → N ≤ d`.
2. Universal Rank-1 Koszul Flattening Factorization: every tensor of rank `≤ r` in `F^n ⊗ F^b ⊗ F^c`
   factors `Φ_1(T) = A · B` through inner dimension `r * (n - 1)` via `u ∧ u = 0`.
3. Pure-integer `{-1, 0, +1}` 18-nonzero left-inverse certificate proving `rank_F(<2,2,2>) ≥ 6 > 4`
   over EVERY field `F` (beating classical matrix flattening `4`).
4. Explicit 7-nonzero binary `3×3×3` tensor `T_3` with exact `9×9` unimodular `Z`-inverse proving
   `rank_F(T_3) ≥ 5 > 3` over EVERY field `F` (breaking the `3×3` flattening barrier).
-/

namespace TriadFrontier.KoszulTensor

open TriadFrontier.AlgebraCore

@[expose] public section

-- ============================================================================
-- Section 1: Ring Homomorphism `intToR : Int → R` over ANY `CommRing R`
-- ============================================================================

def natToR {R : Type} [CommRing R] : Nat → R
  | 0 => 0
  | k + 1 => natToR k + 1

def intToR {R : Type} [CommRing R] : Int → R
  | Int.ofNat n => natToR n
  | Int.negSucc n => -(natToR (n + 1))

theorem natToR_add {R : Type} [CommRing R] (a b : Nat) :
    natToR (R := R) (a + b) = natToR a + natToR b := by
  induction b with
  | zero => simp [natToR, add_zero]
  | succ k ih => rw [Nat.add_succ, natToR, natToR, ih, CommRing.add_assoc]

theorem natToR_mul {R : Type} [CommRing R] (a b : Nat) :
    natToR (R := R) (a * b) = natToR a * natToR b := by
  induction b with
  | zero => simp [natToR, mul_zero]
  | succ k ih =>
    rw [Nat.mul_succ, natToR_add, natToR, CommRing.left_distrib, ih, mul_one]

theorem intToR_zero {R : Type} [CommRing R] : intToR (R := R) 0 = 0 := rfl

theorem intToR_one {R : Type} [CommRing R] : intToR (R := R) 1 = 1 := by
  simp [intToR, natToR, CommRing.zero_add]

theorem intToR_neg {R : Type} [CommRing R] (a : Int) :
    intToR (R := R) (-a) = -(intToR a) := by
  cases a with
  | ofNat n =>
    cases n with
    | zero => simp [intToR, natToR, neg_zero]
    | succ k => rfl
  | negSucc n =>
    have h : -(Int.negSucc n) = Int.ofNat (n + 1) := rfl
    rw [h, intToR, intToR, neg_neg]

theorem intToR_sub_nat {R : Type} [CommRing R] (a b : Nat) :
    intToR (R := R) ((a : Int) - (b : Int)) = natToR a - natToR b := by
  cases Nat.le_total b a with
  | inl hle =>
    have heq : (a : Int) - (b : Int) = Int.ofNat (a - b) := Int.ofNat_sub hle |>.symm
    rw [heq, intToR]
    have hadd : natToR (R := R) a = natToR (a - b) + natToR b := by
      have ha : (a - b) + b = a := Nat.sub_add_cancel hle
      rw [← natToR_add, ha]
    rw [hadd, CommRing.sub_eq, CommRing.add_assoc, CommRing.add_neg, add_zero]
  | inr hle =>
    cases Nat.eq_or_lt_of_le hle with
    | inl heq =>
      subst heq
      have hz : (a : Int) - (a : Int) = 0 := by omega
      rw [hz, intToR_zero, sub_self]
    | inr hlt =>
      have hk : (a : Int) - (b : Int) = -(Int.ofNat (b - a)) := by
        have hba : Int.ofNat (b - a) = (b : Int) - (a : Int) := Int.ofNat_sub (Nat.le_of_lt hlt)
        rw [hba]; omega
      rw [hk, intToR_neg, intToR]
      have hadd : natToR (R := R) b = natToR a + natToR (b - a) := by
        have hb : a + (b - a) = b := Nat.add_sub_of_le (Nat.le_of_lt hlt)
        rw [← natToR_add, hb]
      rw [hadd, CommRing.sub_eq, neg_add_distrib, ← CommRing.add_assoc,
          CommRing.add_neg, CommRing.zero_add]

theorem intToR_add {R : Type} [CommRing R] (a b : Int) :
    intToR (R := R) (a + b) = intToR a + intToR b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      exact natToR_add m n
    | negSucc n =>
      have h : (Int.ofNat m) + (Int.negSucc n) = (m : Int) - ((n + 1 : Nat) : Int) := by
        change (m : Int) + (-((n + 1 : Nat) : Int)) = (m : Int) - ((n + 1 : Nat) : Int); omega
      rw [h, intToR_sub_nat, CommRing.sub_eq]; rfl
  | negSucc m =>
    cases b with
    | ofNat n =>
      have h : (Int.negSucc m) + (Int.ofNat n) = (n : Int) - ((m + 1 : Nat) : Int) := by
        change (-((m + 1 : Nat) : Int)) + (n : Int) = (n : Int) - ((m + 1 : Nat) : Int); omega
      rw [h, intToR_sub_nat, CommRing.sub_eq, CommRing.add_comm]; rfl
    | negSucc n =>
      have h : (Int.negSucc m) + (Int.negSucc n) = Int.negSucc (m + n + 1) := by
        change (-((m + 1 : Nat) : Int)) + (-((n + 1 : Nat) : Int)) = -(((m + n + 1 + 1 : Nat) : Int)); omega
      rw [h, intToR, intToR, intToR]
      have h2 : (m + n + 1) + 1 = (m + 1) + (n + 1) := by omega
      rw [h2, natToR_add, neg_add_distrib]

theorem intToR_mul {R : Type} [CommRing R] (a b : Int) :
    intToR (R := R) (a * b) = intToR a * intToR b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      exact natToR_mul m n
    | negSucc n =>
      have h : (Int.ofNat m) * (Int.negSucc n) = -(Int.ofNat (m * (n + 1))) := by
        change (m : Int) * (-((n + 1 : Nat) : Int)) = -((m * (n + 1) : Nat) : Int)
        rw [Int.mul_neg]; simp
      rw [h, intToR_neg, intToR, natToR_mul, intToR, intToR, mul_neg]
  | negSucc m =>
    cases b with
    | ofNat n =>
      have h : (Int.negSucc m) * (Int.ofNat n) = -(Int.ofNat ((m + 1) * n)) := by
        change (-((m + 1 : Nat) : Int)) * (n : Int) = -(((m + 1) * n : Nat) : Int)
        rw [Int.neg_mul]; simp
      rw [h, intToR_neg, intToR, natToR_mul, intToR, intToR, neg_mul]
    | negSucc n =>
      have h : (Int.negSucc m) * (Int.negSucc n) = Int.ofNat ((m + 1) * (n + 1)) := by
        change (-((m + 1 : Nat) : Int)) * (-((n + 1 : Nat) : Int)) = (((m + 1) * (n + 1) : Nat) : Int)
        rw [Int.neg_mul_neg]; simp
      rw [h, intToR, natToR_mul, intToR, intToR, neg_mul, mul_neg, neg_neg]

theorem sumR_intToR {R : Type} [CommRing R] (n : Nat) (f : Nat → Int) :
    sumR n (fun i => intToR (R := R) (f i)) = intToR (sumInt n f) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumR, sumInt, ih, intToR_add]

-- ============================================================================
-- Section 2: Universal Steinitz / Gauss Matrix Rank Factorization Bound
-- ============================================================================

def matMulF {R : Type} [CommRing R] (k : Nat) (A B : Nat → Nat → R) (i j : Nat) : R :=
  sumR k (fun t => A i t * B t j)

def matIdF {R : Type} [CommRing R] (i j : Nat) : R :=
  if i = j then 1 else 0

def skipIdx (p t : Nat) : Nat :=
  if t < p then t else t + 1

theorem sumR_extract {R : Type} [CommRing R] :
    ∀ (d p : Nat) (f : Nat → R), p ≤ d →
      sumR (d + 1) f = f p + sumR d (fun t => f (skipIdx p t))
  | 0, 0, f, _ => by simp [sumR, CommRing.zero_add, add_zero]
  | 0, _ + 1, _, h => by omega
  | d + 1, p, f, hp => by
    cases Nat.eq_or_lt_of_le hp with
    | inl heq =>
      subst heq
      have hc : sumR (d + 1) (fun t => f (skipIdx (d + 1) t)) = sumR (d + 1) f := by
        apply sumR_congr
        intro t ht
        simp [skipIdx, ht]
      change sumR (d + 1) f + f (d + 1) = f (d + 1) + sumR (d + 1) (fun t => f (skipIdx (d + 1) t))
      rw [hc, CommRing.add_comm]
    | inr hlt =>
      have hpd : p ≤ d := by omega
      have ih := sumR_extract d p f hpd
      have hskip : skipIdx p d = d + 1 := by
        unfold skipIdx
        have hnot : ¬ (d < p) := by omega
        simp [hnot]
      change sumR (d + 1) f + f (d + 1) = f p + (sumR d (fun t => f (skipIdx p t)) + f (skipIdx p d))
      rw [ih, hskip, CommRing.add_assoc]

theorem exists_nonzero_of_sumR_ne_zero {R : Type} [CommRing R] :
    ∀ (n : Nat) (f : Nat → R), sumR n f ≠ 0 → ∃ i, i < n ∧ f i ≠ 0
  | 0, _, h => absurd rfl h
  | k + 1, f, h => by
    by_cases hk : f k = 0
    · simp only [sumR, hk, add_zero] at h
      obtain ⟨i, hi, hne⟩ := exists_nonzero_of_sumR_ne_zero k f h
      exact ⟨i, Nat.lt_succ_of_lt hi, hne⟩
    · exact ⟨k, Nat.lt_succ_self k, hk⟩

/-- **Universal Matrix Rank Bound (over ANY `SimpleField F`):**
If `P ∈ F^{N × d}` and `Q ∈ F^{d × N}` satisfy `P · Q = I_N`, then `N ≤ d`. -/
theorem matRankFactor_le {F : Type} [SimpleField F] :
    ∀ (d N : Nat) (P Q : Nat → Nat → F),
      (∀ i j, i < N → j < N → matMulF d P Q i j = matIdF i j) →
      N ≤ d
  | 0, N, P, Q, h => by
    cases N with
    | zero => exact Nat.le_refl 0
    | succ n =>
      have h0 := h 0 0 (Nat.zero_lt_succ n) (Nat.zero_lt_succ n)
      simp [matMulF, sumR, matIdF] at h0
      exact absurd h0 SimpleField.zero_ne_one
  | d + 1, 0, _, _, _ => Nat.zero_le (d + 1)
  | d + 1, n + 1, P, Q, h => by
    have hnn : matMulF (d + 1) P Q n n = 1 := by
      have h1 := h n n (Nat.lt_succ_self n) (Nat.lt_succ_self n)
      simp [matIdF] at h1
      exact h1
    have hne : sumR (d + 1) (fun t => P n t * Q t n) ≠ 0 := by
      rw [show sumR (d + 1) (fun t => P n t * Q t n) = 1 from hnn]
      exact Ne.symm SimpleField.zero_ne_one
    obtain ⟨p, hp, hterm⟩ := exists_nonzero_of_sumR_ne_zero (d + 1) (fun t => P n t * Q t n) hne
    have hPnp : P n p ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hterm
      exact hterm rfl
    let invA : F := SimpleField.inv (P n p)
    let P' : Nat → Nat → F := fun i t =>
      P i (skipIdx p t) - (P i p * invA) * P n (skipIdx p t)
    let Q' : Nat → Nat → F := fun t j => Q (skipIdx p t) j
    have hsub : ∀ i j, i < n → j < n → matMulF d P' Q' i j = matIdF i j := by
      intro i j hi hj
      unfold matMulF
      have hij := h i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj)
      have hnj := h n j (Nat.lt_succ_self n) (Nat.lt_succ_of_lt hj)
      unfold matMulF at hij hnj
      have hnj0 : matIdF (R := F) n j = 0 := by
        unfold matIdF
        split
        · omega
        · rfl
      rw [hnj0] at hnj
      have hp_le : p ≤ d := by omega
      rw [sumR_extract d p (fun t => P i t * Q t j) hp_le] at hij
      rw [sumR_extract d p (fun t => P n t * Q t j) hp_le] at hnj
      have hS2 : sumR d (fun t => P n (skipIdx p t) * Q (skipIdx p t) j) = -(P n p * Q p j) :=
        neg_eq_of_add_eq_zero hnj
      have hsplit : sumR d (fun t => P' i t * Q' t j) =
          sumR d (fun t => P i (skipIdx p t) * Q (skipIdx p t) j) +
          (-(P i p * invA)) * sumR d (fun t => P n (skipIdx p t) * Q (skipIdx p t) j) := by
        rw [sumR_mul_left, ← sumR_add]
        apply sumR_congr
        intro t _
        dsimp only [P', Q']
        rw [CommRing.sub_eq, right_distrib, neg_mul, neg_mul, CommRing.mul_assoc]
      rw [hsplit, hS2, mul_neg, neg_mul, neg_neg]
      have hcancel : (P i p * invA) * (P n p * Q p j) = P i p * Q p j := by
        calc (P i p * invA) * (P n p * Q p j)
            = P i p * ((P n p * invA) * Q p j) := by
              rw [CommRing.mul_assoc, ← CommRing.mul_assoc invA (P n p) (Q p j),
                  CommRing.mul_comm invA (P n p)]
          _ = P i p * (1 * Q p j) := by rw [SimpleField.mul_inv_cancel (P n p) hPnp]
          _ = P i p * Q p j := by rw [CommRing.one_mul]
      rw [hcancel, CommRing.add_comm, hij]
    have hle := matRankFactor_le d n P' Q' hsub
    omega

-- ============================================================================
-- Section 3: Universal Koszul Flattening `Φ_1(T)` & Rank-1 Factorization (`u ∧ u = 0`)
-- ============================================================================

/-- Tensor rank `≤ r` decomposition of `T : Nat → Nat → Nat → F` on `[n] × [bDim] × [cDim]`. -/
def HasTensorRankAtMost {F : Type} [SimpleField F] (n bDim cDim r : Nat)
    (T : Nat → Nat → Nat → F) : Prop :=
  ∃ (U V W : Nat → Nat → F),
    ∀ a b c, a < n → b < bDim → c < cDim →
      T a b c = sumR r (fun s => U s a * V s b * W s c)

/-- Coefficient of basis 2-blade `e_{r0} ∧ e_{s0}` (`r0 < s0`) in `u ∧ e_i`. -/
def wedgeCoeff {R : Type} [CommRing R] (pairIdx : Nat → Nat × Nat)
    (u : Nat → R) (i pIdx : Nat) : R :=
  let pair := pairIdx pIdx
  if i = pair.2 then u pair.1
  else if i = pair.1 then -(u pair.2)
  else 0

/-- Exact exterior annihilation `u ∧ u = 0` on every basis 2-blade `(r0, s0)` with `r0 < s0 < n`. -/
theorem wedge_self_zero {R : Type} [CommRing R] (n : Nat) (pairIdx : Nat → Nat × Nat)
    (u : Nat → R) (pIdx : Nat)
    (hvalid : (pairIdx pIdx).1 < (pairIdx pIdx).2 ∧ (pairIdx pIdx).2 < n) :
    sumR n (fun i => u i * wedgeCoeff pairIdx u i pIdx) = 0 := by
  let r0 := (pairIdx pIdx).1
  let s0 := (pairIdx pIdx).2
  have hrs : r0 < s0 := hvalid.1
  have hsn : s0 < n := hvalid.2
  have hsum : ∀ m : Nat, sumR m (fun i => u i * wedgeCoeff pairIdx u i pIdx) =
      (if s0 < m then u s0 * u r0 else 0) + (if r0 < m then -(u r0 * u s0) else 0) := by
    intro m
    induction m with
    | zero => simp [sumR, add_zero]
    | succ k ih =>
      simp only [sumR, ih]
      unfold wedgeCoeff
      change ((if s0 < k then u s0 * u r0 else 0) + (if r0 < k then -(u r0 * u s0) else 0)) +
          u k * (if k = s0 then u r0 else if k = r0 then -(u s0) else 0) =
          (if s0 < k + 1 then u s0 * u r0 else 0) + (if r0 < k + 1 then -(u r0 * u s0) else 0)
      by_cases hks : k = s0
      · subst hks
        have h1 : ¬ (s0 < s0) := Nat.lt_irrefl s0
        have h2 : s0 < s0 + 1 := Nat.lt_succ_self s0
        have h3 : r0 < s0 := hrs
        have h4 : r0 < s0 + 1 := Nat.lt_succ_of_lt hrs
        simp only [h1, h2, h3, h4, ↓reduceIte, CommRing.add_comm]
        rw [add_zero]
      · by_cases hkr : k = r0
        · subst hkr
          have h1 : ¬ (s0 < r0) := by omega
          have h2 : ¬ (s0 < r0 + 1) := by omega
          have h3 : ¬ (r0 < r0) := Nat.lt_irrefl r0
          have h4 : r0 < r0 + 1 := Nat.lt_succ_self r0
          simp only [hks, h1, h2, h3, h4, ↓reduceIte, add_zero, CommRing.zero_add, mul_neg]
        · have h1 : (s0 < k + 1) ↔ (s0 < k) := by omega
          have h2 : (r0 < k + 1) ↔ (r0 < k) := by omega
          simp only [hks, hkr, ↓reduceIte, mul_zero, add_zero, h1, h2]
  rw [hsum n]
  have hrn : r0 < n := Nat.lt_trans hrs hsn
  simp only [hsn, hrn, ↓reduceIte, CommRing.mul_comm (u s0) (u r0), CommRing.add_neg]

/-- `p = 1` Koszul Flattening matrix `Φ_1(T) : (nPairs * cDim) × (n * bDim)`.
Row `pIdx * cDim + c`, Column `i * bDim + b`. -/
def koszulPhi1 {R : Type} [CommRing R] (_n bDim cDim : Nat) (pairIdx : Nat → Nat × Nat)
    (T : Nat → Nat → Nat → R) (row col : Nat) : R :=
  let pIdx := row / cDim
  let c := row % cDim
  let i := col / bDim
  let b := col % bDim
  let pair := pairIdx pIdx
  if i = pair.2 then T pair.1 b c
  else if i = pair.1 then -(T pair.2 b c)
  else 0

/-- Rank-1 Koszul flattening factorization through inner dimension `n - 1` over ANY `SimpleField F`. -/
theorem koszulPhi1_rank1_factor {F : Type} [SimpleField F] (n bDim cDim : Nat)
    (pairIdx : Nat → Nat × Nat) (nPairs : Nat)
    (hn : 1 ≤ n) (_hb : 0 < bDim) (_hc : 0 < cDim)
    (hpairs : ∀ pIdx, pIdx < nPairs → (pairIdx pIdx).1 < (pairIdx pIdx).2 ∧ (pairIdx pIdx).2 < n)
    (u v w : Nat → F) :
    ∃ (A B : Nat → Nat → F),
      ∀ row col, row < nPairs * cDim → col < n * bDim →
        koszulPhi1 n bDim cDim pairIdx (fun a b c => u a * v b * w c) row col =
        matMulF (n - 1) A B row col := by
  by_cases hex : ∃ k, k < n ∧ u k ≠ 0
  · obtain ⟨k, hkn, huk⟩ := hex
    let invUk : F := SimpleField.inv (u k)
    let A : Nat → Nat → F := fun row t =>
      wedgeCoeff pairIdx u (skipIdx k t) (row / cDim) * w (row % cDim)
    let B : Nat → Nat → F := fun t col =>
      let i := col / bDim
      let b := col % bDim
      if i = k then (-(u (skipIdx k t) * invUk)) * v b
      else if skipIdx k t = i then v b
      else 0
    refine ⟨A, B, ?_⟩
    intro row col hrow hcol
    have hpIdx_lt : row / cDim < nPairs := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hrow)
    have hi_lt : col / bDim < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcol)
    have hvalid := hpairs (row / cDim) hpIdx_lt
    -- Relate `koszulPhi1` of `u ⊗ v ⊗ w` to `wedgeCoeff u i pIdx * v b * w c`
    have hphi_eq : koszulPhi1 n bDim cDim pairIdx (fun a b c => u a * v b * w c) row col =
        wedgeCoeff pairIdx u (col / bDim) (row / cDim) * v (col % bDim) * w (row % cDim) := by
      unfold koszulPhi1 wedgeCoeff
      dsimp only
      split
      · rfl
      · split
        · rw [neg_mul, neg_mul]
        · rw [zero_mul, zero_mul]
    rw [hphi_eq]
    unfold matMulF
    by_cases hik : col / bDim = k
    · -- Eliminate `i = k` using `u ∧ u = 0`!
      have hw0 := wedge_self_zero n pairIdx u (row / cDim) hvalid
      have hn1 : (n - 1) + 1 = n := Nat.sub_add_cancel hn
      rw [← hn1] at hw0
      have hk_le : k ≤ n - 1 := by omega
      rw [sumR_extract (n - 1) k (fun i => u i * wedgeCoeff pairIdx u i (row / cDim)) hk_le] at hw0
      have hneg := neg_eq_of_add_eq_zero hw0
      -- Multiply by `invUk` to isolate `wedgeCoeff u k`
      have hwk : wedgeCoeff pairIdx u k (row / cDim) =
          sumR (n - 1) (fun t => (-(u (skipIdx k t) * invUk)) * wedgeCoeff pairIdx u (skipIdx k t) (row / cDim)) := by
        have h1 : invUk * sumR (n - 1) (fun t => u (skipIdx k t) * wedgeCoeff pairIdx u (skipIdx k t) (row / cDim)) =
            invUk * (-(u k * wedgeCoeff pairIdx u k (row / cDim))) := congrArg (fun x => invUk * x) hneg
        rw [mul_neg, ← CommRing.mul_assoc, CommRing.mul_comm invUk (u k),
            SimpleField.mul_inv_cancel (u k) huk, CommRing.one_mul] at h1
        have h2 : wedgeCoeff pairIdx u k (row / cDim) =
            -(invUk * sumR (n - 1) (fun t => u (skipIdx k t) * wedgeCoeff pairIdx u (skipIdx k t) (row / cDim))) := by
          rw [h1, neg_neg]
        rw [h2, sumR_mul_left, ← sumR_neg]
        apply sumR_congr
        intro t _
        rw [← CommRing.mul_assoc, CommRing.mul_comm invUk (u (skipIdx k t)), neg_mul]
      rw [hik, hwk]
      -- Push `* v b * w c` inside the sum!
      have hrhs : sumR (n - 1) (fun t => A row t * B t col) =
          (sumR (n - 1) (fun t => (-(u (skipIdx k t) * invUk)) * wedgeCoeff pairIdx u (skipIdx k t) (row / cDim))) *
          v (col % bDim) * w (row % cDim) := by
        rw [CommRing.mul_assoc, CommRing.mul_comm _ (v (col % bDim) * w (row % cDim)), sumR_mul_left]
        apply sumR_congr
        intro t _
        dsimp only [A, B]
        simp only [hik, ↓reduceIte]
        -- Reassociate 4 factors
        calc wedgeCoeff pairIdx u (skipIdx k t) (row / cDim) * w (row % cDim) *
              (-(u (skipIdx k t) * invUk) * v (col % bDim))
            = (-(u (skipIdx k t) * invUk) * wedgeCoeff pairIdx u (skipIdx k t) (row / cDim)) *
              (v (col % bDim) * w (row % cDim)) := by
              rw [CommRing.mul_assoc (wedgeCoeff pairIdx u (skipIdx k t) (row / cDim)),
                  CommRing.mul_comm (w (row % cDim)),
                  ← CommRing.mul_assoc,
                  CommRing.mul_comm (wedgeCoeff pairIdx u (skipIdx k t) (row / cDim)),
                  CommRing.mul_assoc (-(u (skipIdx k t) * invUk)),
                  CommRing.mul_comm (v (col % bDim)) (wedgeCoeff pairIdx u (skipIdx k t) (row / cDim)),
                  ← CommRing.mul_assoc (-(u (skipIdx k t) * invUk)) (wedgeCoeff pairIdx u (skipIdx k t) (row / cDim)),
                  CommRing.mul_assoc]
          _ = v (col % bDim) * w (row % cDim) *
              (-(u (skipIdx k t) * invUk) * wedgeCoeff pairIdx u (skipIdx k t) (row / cDim)) :=
              CommRing.mul_comm ..
      rw [hrhs]
    · -- Case `i ≠ k`: unique index `t0 < n - 1` has `skipIdx k t0 = i`!
      let i := col / bDim
      let t0 := if i < k then i else i - 1
      have ht0_lt : t0 < n - 1 := by dsimp only [t0, i]; split <;> omega
      have hskip_eq : skipIdx k t0 = i := by
        dsimp only [t0, skipIdx]
        by_cases hlt : i < k
        · simp [hlt]
        · have hnot : ¬ (i - 1 < k) := by omega
          simp [hlt, hnot]; omega
      have hskip_inj : ∀ t, skipIdx k t = i → t = t0 := by
        intro t ht
        unfold skipIdx at ht
        dsimp only [t0]
        by_cases hlt : t < k
        · simp only [hlt, ↓reduceIte] at ht
          have h1 : i < k := by omega
          simp [h1, ht]
        · simp only [hlt, ↓reduceIte] at ht
          have h1 : ¬ (i < k) := by omega
          simp [h1]; omega
      have hsum_single : ∀ m : Nat, sumR m (fun t => A row t * B t col) =
          if t0 < m then A row t0 * v (col % bDim) else 0 := by
        intro m
        induction m with
        | zero => simp [sumR]
        | succ s ih =>
          simp only [sumR, ih]
          by_cases hst : s = t0
          · subst hst
            have h1 : ¬ (t0 < t0) := Nat.lt_irrefl t0
            have h2 : t0 < t0 + 1 := Nat.lt_succ_self t0
            have hik' : i ≠ k := hik
            simp only [h1, h2, ↓reduceIte, CommRing.zero_add]
            dsimp only [B]
            change A row t0 * (if i = k then (-(u (skipIdx k t0) * invUk)) * v (col % bDim)
              else if skipIdx k t0 = i then v (col % bDim) else 0) = A row t0 * v (col % bDim)
            simp only [hik', hskip_eq, ↓reduceIte]
          · have hneq : skipIdx k s ≠ i := fun heq => hst (hskip_inj s heq)
            have h1 : (t0 < s + 1) ↔ (t0 < s) := by omega
            have hik' : i ≠ k := hik
            have hterm0 : A row s * B s col = 0 := by
              dsimp only [B]
              change A row s * (if i = k then (-(u (skipIdx k s) * invUk)) * v (col % bDim)
                else if skipIdx k s = i then v (col % bDim) else 0) = 0
              simp only [hik', hneq, ↓reduceIte, mul_zero]
            rw [hterm0, add_zero]
            simp only [h1]
      rw [hsum_single (n - 1)]
      simp only [ht0_lt, ↓reduceIte]
      dsimp only [A]
      rw [hskip_eq]
      change wedgeCoeff pairIdx u i (row / cDim) * v (col % bDim) * w (row % cDim) =
          wedgeCoeff pairIdx u i (row / cDim) * w (row % cDim) * v (col % bDim)
      rw [CommRing.mul_assoc, CommRing.mul_assoc, CommRing.mul_comm (v (col % bDim)) (w (row % cDim))]
  · -- Case `u ≡ 0`: zero factorization!
    refine ⟨fun _ _ => 0, fun _ _ => 0, ?_⟩
    intro row col hrow hcol
    have hpIdx_lt : row / cDim < nPairs := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hrow)
    have hvalid := hpairs (row / cDim) hpIdx_lt
    have hu0 : ∀ a, a < n → u a = 0 := by
      intro a ha
      by_cases hz : u a = 0
      · exact hz
      · exact absurd ⟨a, ha, hz⟩ hex
    have hm0 : matMulF (n - 1) (fun _ _ => (0 : F)) (fun _ _ => 0) row col = 0 := by
      unfold matMulF
      rw [sumR_congr (fun _ _ => zero_mul (0 : F)), sumR_zero_fn]
    rw [hm0]
    unfold koszulPhi1
    dsimp only
    split
    · rw [hu0 _ (Nat.lt_trans hvalid.1 hvalid.2), zero_mul, zero_mul]
    · split
      · rw [hu0 _ hvalid.2, zero_mul, zero_mul, neg_zero]
      · rfl

/-- Sum of `r` rank-1 Koszul flattenings factors through inner dimension `r * (n - 1)`. -/
theorem koszulPhi1_rank_r_factor {F : Type} [SimpleField F] (n bDim cDim : Nat)
    (pairIdx : Nat → Nat × Nat) (nPairs : Nat)
    (hn : 1 ≤ n) (hb : 0 < bDim) (hc : 0 < cDim)
    (hpairs : ∀ pIdx, pIdx < nPairs → (pairIdx pIdx).1 < (pairIdx pIdx).2 ∧ (pairIdx pIdx).2 < n)
    (U V W : Nat → Nat → F) :
    ∀ r : Nat,
      ∃ (A B : Nat → Nat → F),
        ∀ row col, row < nPairs * cDim → col < n * bDim →
          koszulPhi1 n bDim cDim pairIdx (fun a b c => sumR r (fun s => U s a * V s b * W s c)) row col =
          matMulF (r * (n - 1)) A B row col
  | 0 => by
    refine ⟨fun _ _ => 0, fun _ _ => 0, ?_⟩
    intro row col _ _
    simp only [Nat.zero_mul, matMulF, sumR, koszulPhi1]
    split
    · rfl
    · split
      · exact neg_zero
      · rfl
  | r + 1 => by
    obtain ⟨A1, B1, h1⟩ := koszulPhi1_rank_r_factor n bDim cDim pairIdx nPairs hn hb hc hpairs U V W r
    obtain ⟨A2, B2, h2⟩ := koszulPhi1_rank1_factor n bDim cDim pairIdx nPairs hn hb hc hpairs (U r) (V r) (W r)
    let off := r * (n - 1)
    let A : Nat → Nat → F := fun row t => if t < off then A1 row t else A2 row (t - off)
    let B : Nat → Nat → F := fun t col => if t < off then B1 t col else B2 (t - off) col
    refine ⟨A, B, ?_⟩
    intro row col hrow hcol
    -- Linearity of `koszulPhi1` in `T`
    have hlin : koszulPhi1 n bDim cDim pairIdx (fun a b c => sumR (r + 1) (fun s => U s a * V s b * W s c)) row col =
        koszulPhi1 n bDim cDim pairIdx (fun a b c => sumR r (fun s => U s a * V s b * W s c)) row col +
        koszulPhi1 n bDim cDim pairIdx (fun a b c => U r a * V r b * W r c) row col := by
      unfold koszulPhi1
      dsimp only
      split
      · rfl
      · split
        · exact neg_add_distrib ..
        · rw [add_zero]
    rw [hlin, h1 row col hrow hcol, h2 row col hrow hcol]
    have hdim : (r + 1) * (n - 1) = off + (n - 1) := by dsimp only [off]; rw [Nat.add_mul, Nat.one_mul]
    unfold matMulF
    rw [hdim, sumR_split off (n - 1)]
    have hleft : sumR off (fun t => A row t * B t col) = sumR off (fun t => A1 row t * B1 t col) := by
      apply sumR_congr; intro t ht; dsimp only [A, B]; simp [ht]
    have hright : sumR (n - 1) (fun t => A row (off + t) * B (off + t) col) =
        sumR (n - 1) (fun t => A2 row t * B2 t col) := by
      apply sumR_congr; intro t _
      dsimp only [A, B]
      have hnot : ¬ (off + t < off) := by omega
      have hsub : off + t - off = t := by omega
      simp [hnot, hsub]
    rw [hleft, hright]

/-- **Master Universal Koszul Flattening Lower Bound (over ANY `SimpleField F`):**
If an integer matrix `L` is a left inverse to `Φ_1(T_int)` over `Int` (`L · Φ_1(T_int) = I_{n*b}`),
then for EVERY field `F` and EVERY tensor rank decomposition of `intToR ∘ T_int` of rank `r`,
we MUST have `n * bDim ≤ r * (n - 1)`! -/
theorem koszul_flattening_rank_lb_of_int_left_inv {F : Type} [SimpleField F]
    (n bDim cDim nPairs : Nat) (pairIdx : Nat → Nat × Nat)
    (hn : 1 ≤ n) (hb : 0 < bDim) (hc : 0 < cDim)
    (hpairs : ∀ pIdx, pIdx < nPairs → (pairIdx pIdx).1 < (pairIdx pIdx).2 ∧ (pairIdx pIdx).2 < n)
    (Tint : Nat → Nat → Nat → Int) (Lint : Nat → Nat → Int)
    (hcert : ∀ i j, i < n * bDim → j < n * bDim →
      sumInt (nPairs * cDim) (fun row => Lint i row * koszulPhi1 n bDim cDim pairIdx Tint row j) =
      if i = j then 1 else 0)
    (r : Nat) (hrank : HasTensorRankAtMost n bDim cDim r (fun a b c => intToR (R := F) (Tint a b c))) :
    n * bDim ≤ r * (n - 1) := by
  obtain ⟨U, V, W, hT⟩ := hrank
  obtain ⟨A, B, hAB⟩ := koszulPhi1_rank_r_factor n bDim cDim pairIdx nPairs hn hb hc hpairs U V W r
  -- Let P = L_F · A (shape (n*bDim) × (r*(n-1))) and Q = B (shape (r*(n-1)) × (n*bDim))
  let Lf : Nat → Nat → F := fun i row => intToR (Lint i row)
  let P : Nat → Nat → F := fun i t => sumR (nPairs * cDim) (fun row => Lf i row * A row t)
  apply matRankFactor_le (r * (n - 1)) (n * bDim) P B
  intro i j hi hj
  -- Swap sums: ∑_t (∑_row L_i,row A_row,t) B_t,j = ∑_row L_i,row (∑_t A_row,t B_t,j)
  have hswap : ∀ m : Nat,
      sumR (r * (n - 1)) (fun t => sumR m (fun row => Lf i row * A row t) * B t j) =
      sumR m (fun row => Lf i row * sumR (r * (n - 1)) (fun t => A row t * B t j)) := by
    intro m
    induction m with
    | zero =>
      simp only [sumR]
      rw [sumR_congr (fun _ _ => zero_mul _), sumR_zero_fn]
    | succ k ih =>
      simp only [sumR]
      rw [← ih, sumR_mul_left, ← sumR_add]
      apply sumR_congr
      intro t _
      rw [right_distrib, CommRing.mul_assoc]
  unfold matMulF
  change sumR (r * (n - 1)) (fun t => sumR (nPairs * cDim) (fun row => Lf i row * A row t) * B t j) = matIdF i j
  rw [hswap (nPairs * cDim)]
  -- Replace `∑_t A_row,t B_t,j` with `intToR (koszulPhi1 Tint row j)`!
  have hphi_int : ∀ row, row < nPairs * cDim →
      sumR (r * (n - 1)) (fun t => A row t * B t j) =
      intToR (R := F) (koszulPhi1 n bDim cDim pairIdx Tint row j) := by
    intro row hrow
    change matMulF (r * (n - 1)) A B row j = intToR (R := F) (koszulPhi1 n bDim cDim pairIdx Tint row j)
    rw [← hAB row j hrow hj]
    have hpIdx_lt : row / cDim < nPairs := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hrow)
    have hvalid := hpairs (row / cDim) hpIdx_lt
    have hb_lt : j % bDim < bDim := Nat.mod_lt j hb
    have hc_lt : row % cDim < cDim := Nat.mod_lt row hc
    unfold koszulPhi1
    dsimp only
    split
    · rw [← hT _ _ _ (Nat.lt_trans hvalid.1 hvalid.2) hb_lt hc_lt]
    · split
      · rw [← hT _ _ _ hvalid.2 hb_lt hc_lt, intToR_neg]
      · exact intToR_zero.symm
  have hcongr : sumR (nPairs * cDim) (fun row => Lf i row * sumR (r * (n - 1)) (fun t => A row t * B t j)) =
      sumR (nPairs * cDim) (fun row => intToR (R := F) (Lint i row * koszulPhi1 n bDim cDim pairIdx Tint row j)) := by
    apply sumR_congr
    intro row hrow
    rw [hphi_int row hrow]
    exact (intToR_mul (Lint i row) _).symm
  rw [hcongr, sumR_intToR, hcert i j hi hj]
  unfold matIdF
  split
  · exact intToR_one
  · exact intToR_zero

-- ============================================================================
-- Section 4: Concrete Pure-Integer Certificates for `<2,2,2>` and `3×3×3` `T_3`
-- ============================================================================

/-- Sorted 2-blade table for `n = 4` (`6` pairs). -/
def pairs4 : Nat → Nat × Nat
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (1, 2)
  | 4 => (1, 3)
  | _ => (2, 3)

/-- `2×2` Matrix multiplication tensor `M_2 = ⟨2,2,2⟩ ∈ Z^{4×4×4}`:
`A_{i,j} * B_{j,k} → C_{i,k}` (`a = 2i+j, b = 2j+k, c = 2i+k`). -/
def matMul2Tensor (a b c : Nat) : Int :=
  if a / 2 = c / 2 && a % 2 = b / 2 && b % 2 = c % 2 && a < 4 && b < 4 && c < 4 then 1 else 0

/-- Explicit 18-nonzero `{-1, 0, +1}` left inverse `L_2 ∈ Z^{16×24}` to `Φ_1(M_2)`. -/
def leftInvM2 (r c : Nat) : Int :=
  match r, c with
  | 0, 6   => -1
  | 1, 7   => -1
  | 2, 10  => -1
  | 3, 11  => -1
  | 4, 0   => 1
  | 4, 10  => -1
  | 5, 1   => 1
  | 5, 11  => -1
  | 6, 18  => -1
  | 7, 19  => -1
  | 8, 4   => 1
  | 9, 5   => 1
  | 10, 12 => 1
  | 11, 13 => 1
  | 12, 8  => 1
  | 13, 9  => 1
  | 14, 16 => 1
  | 15, 17 => 1
  | _, _   => 0

/-- Sorted 2-blade table for `n = 3` (`3` pairs). -/
def pairs3 : Nat → Nat × Nat
  | 0 => (0, 1)
  | 1 => (0, 2)
  | _ => (1, 2)

/-- Explicit 7-nonzero binary `3×3×3` tensor `T_3` with unimodular `9×9` Koszul flattening `Φ_1(T_3)`. -/
def tensor3Bin (a b c : Nat) : Int :=
  match a, b, c with
  | 0, 1, 2 => 1
  | 0, 2, 1 => 1
  | 0, 2, 2 => 1
  | 1, 0, 2 => 1
  | 1, 1, 0 => 1
  | 2, 0, 1 => 1
  | 2, 2, 0 => 1
  | _, _, _ => 0

/-- Exact `9×9` integer inverse `L_3 = Φ_1(T_3)^{-1} ∈ Z^{9×9}`. -/
def leftInvT3 (r c : Nat) : Int :=
  match r, c with
  | 0, 1 => -1 | 0, 4 => -1 | 0, 5 => 1 | 0, 6 => -1
  | 1, 0 => -1
  | 2, 3 => -1
  | 3, 7 => -1
  | 4, 1 => -2 | 4, 2 => 1 | 4, 4 => -1 | 4, 5 => 1 | 4, 6 => -1
  | 5, 1 => 1
  | 6, 8 => 1
  | 7, 1 => 1 | 7, 6 => 1
  | 8, 1 => -1 | 8, 5 => 1 | 8, 6 => -1
  | _, _ => 0

def allNatBelow (n : Nat) (p : Nat → Bool) : Bool :=
  match n with
  | 0 => true
  | k + 1 => allNatBelow k p && p k

theorem allNatBelow_true {n : Nat} {p : Nat → Bool} (h : allNatBelow n p = true) :
    ∀ i, i < n → p i = true := by
  induction n with
  | zero => intro _ hi; omega
  | succ k ih =>
    simp only [allNatBelow, Bool.and_eq_true] at h
    intro i hi
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with
    | inl heq => subst heq; exact h.2
    | inr hlt => exact ih h.1 i hlt

def checkM2LeftInv : Bool :=
  allNatBelow 16 fun i =>
    allNatBelow 16 fun j =>
      decide (sumInt 24 (fun row => leftInvM2 i row * koszulPhi1 4 4 4 pairs4 matMul2Tensor row j) =
              if i = j then 1 else 0)

def checkT3LeftInv : Bool :=
  allNatBelow 9 fun i =>
    allNatBelow 9 fun j =>
      decide (sumInt 9 (fun row => leftInvT3 i row * koszulPhi1 3 3 3 pairs3 tensor3Bin row j) =
              if i = j then 1 else 0)

theorem checkM2LeftInv_ok : checkM2LeftInv = true := by decide

theorem checkT3LeftInv_ok : checkT3LeftInv = true := by decide

/-- **Theorem T3e (Universal Koszul Flattening Tensor Rank Lower Bound; `CS-053` ↔ `CS-004` ↔ `CS-012`):**
Using the exact same exterior wedge `u ∧ ·` from Coded PIR (`T1a`) over ANY field `SimpleField F`
of ANY characteristic (including characteristic `2`):
1. The `2×2` matrix multiplication tensor `M_2 = ⟨2,2,2⟩` has tensor rank `≥ 6` (strictly beating
   the classical matrix-flattening bound `4`).
2. The explicit 7-nonzero binary `3×3×3` tensor `T_3` has tensor rank `≥ 5` (strictly breaking the
   classical `3×3` matrix-flattening barrier `3`). -/
theorem t3e_koszul_flattening_tensor_rank_bridge :
    (∀ (F : Type) [SimpleField F] (r : Nat),
      HasTensorRankAtMost 4 4 4 r (fun a b c => intToR (R := F) (matMul2Tensor a b c)) →
      6 ≤ r) ∧
    (∀ (F : Type) [SimpleField F] (r : Nat),
      HasTensorRankAtMost 3 3 3 r (fun a b c => intToR (R := F) (tensor3Bin a b c)) →
      5 ≤ r) := by
  constructor
  · intro F _ r hrank
    have hcert : ∀ i j, i < 4 * 4 → j < 4 * 4 →
        sumInt (6 * 4) (fun row => leftInvM2 i row * koszulPhi1 4 4 4 pairs4 matMul2Tensor row j) =
        if i = j then 1 else 0 := by
      intro i j hi hj
      have h1 := allNatBelow_true checkM2LeftInv_ok i hi
      have h2 := allNatBelow_true h1 j hj
      exact of_decide_eq_true h2
    have hpairs : ∀ pIdx, pIdx < 6 → (pairs4 pIdx).1 < (pairs4 pIdx).2 ∧ (pairs4 pIdx).2 < 4 := by
      intro pIdx hp
      have hc : pIdx = 0 ∨ pIdx = 1 ∨ pIdx = 2 ∨ pIdx = 3 ∨ pIdx = 4 ∨ pIdx = 5 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hlb := koszul_flattening_rank_lb_of_int_left_inv (F := F) 4 4 4 6 pairs4
      (by decide) (by decide) (by decide) hpairs matMul2Tensor leftInvM2 hcert r hrank
    omega
  · intro F _ r hrank
    have hcert : ∀ i j, i < 3 * 3 → j < 3 * 3 →
        sumInt (3 * 3) (fun row => leftInvT3 i row * koszulPhi1 3 3 3 pairs3 tensor3Bin row j) =
        if i = j then 1 else 0 := by
      intro i j hi hj
      have h1 := allNatBelow_true checkT3LeftInv_ok i hi
      have h2 := allNatBelow_true h1 j hj
      exact of_decide_eq_true h2
    have hpairs : ∀ pIdx, pIdx < 3 → (pairs3 pIdx).1 < (pairs3 pIdx).2 ∧ (pairs3 pIdx).2 < 3 := by
      intro pIdx hp
      have hc : pIdx = 0 ∨ pIdx = 1 ∨ pIdx = 2 := by omega
      rcases hc with rfl | rfl | rfl <;> decide
    have hlb := koszul_flattening_rank_lb_of_int_left_inv (F := F) 3 3 3 3 pairs3
      (by decide) (by decide) (by decide) hpairs tensor3Bin leftInvT3 hcert r hrank
    omega

end
end TriadFrontier.KoszulTensor
