module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore
public import TriadFrontier.KoszulTensor
public import TriadFrontier.PIRProtocol

/-!
# Kernel-Certified `F_101` `(M=2, N=6, K=3, T=3)` Rate-`10/17` Zero-Error PIR Existence (`T1l`)

Zero-Mathlib, zero-`native_decide`, 6-kernel-verified Lean 4.35.0 constructive existence proof
upgrading `T1k` from an abstract conditional protocol theorem to a **100% in-kernel certified
concrete instance over `SimpleField (Fin 101)`**:

1. **`instSimpleFieldFin101`:** Prime field `F_101 = Fin 101` with algebraic `CommRing` proofs
   and kernel-checked Fermat multiplicative inverse `a^99 mod 101` via 7-step binary exponentiation.
2. **Kronecker Base-`2^20` Packed Matrix Soundness (`packed_dot_sound`):**
   Pure `Nat` soundness proof (zero `native_decide`) showing that for all `1 ≤ k ≤ 60` and packed
   rows/reversed-columns with digits `< 101`, `((p * q) / B20^(k - 1)) % B20` equals the EXACT
   integer dot product `∑_{t < k} A_t * B_t`, reducing mod `101` to exact `matMulF` over `Fin 101`.
3. **Full Witness Verification inside Lean's Kernel:**
   - `DecInv · desiredMat = I_60` (`60 × 60` over `F_101`),
   - `Cancel · pureIntMat = mixedIntMat` (`18 × 42` × `42 × 60` over `F_101`),
   - All `C(6, 3) = 20` colluding server triples `(n0, n1, n2)`: `M · Minv = I_20`, `Minv · M = I_20`,
     `α · αinv = I_7`, `αinv · α = I_7`, `γ · γinv = I_3`, `γinv · γ = I_3`,
     `P_n · M = α_n · Q_n`, and `C_n · M = γ_n · D_n + β_n · Q_n`.
4. **Headline Theorem `t1l_f101_t3_k3_e6_certified_pir_existence`:**
   Unconditional constructive existence of `(sc, Cancel, DecInv)` over `Fin 101` with `(N,K,D,y,z) =
   (6,3,20,7,3)`, exact rate `60/102 = 10/17 > 4/7`, zero-error decoding for ALL databases and BOTH
   files, and exact `T=3` collusion privacy bijection `Ψ_I` on EVERY 3-subset of the 6 servers!
-/

namespace TriadFrontier.PIRF101Cert

open TriadFrontier.AlgebraCore
open TriadFrontier.KoszulTensor
open TriadFrontier.PIRProtocol

@[expose] public section

-- ============================================================================
-- Section 1: Prime Field `F_101 = Fin 101` (Zero-Mathlib, Algebraic Ring Proofs)
-- ============================================================================

def ofMod101 (n : Nat) : Fin 101 := ⟨n % 101, Nat.mod_lt _ (by decide)⟩

/-- Straight-line 7-squaring Fermat inverse `a^99 mod 101` (`99 = 64 + 32 + 2 + 1`). -/
def f101InvNat (a : Nat) : Nat :=
  let a2  := (a * a) % 101
  let a4  := (a2 * a2) % 101
  let a8  := (a4 * a4) % 101
  let a16 := (a8 * a8) % 101
  let a32 := (a16 * a16) % 101
  let a64 := (a32 * a32) % 101
  let t1  := (a64 * a32) % 101
  let t2  := (t1 * a2) % 101
  (t2 * a) % 101

def f101Inv (a : Fin 101) : Fin 101 := ofMod101 (f101InvNat a.val)

private theorem f101_mul_inv_all :
    ∀ a : Fin 101, a.val ≠ 0 → (a.val * (f101InvNat a.val % 101)) % 101 = 1 := by decide

instance instSimpleFieldFin101 : SimpleField (Fin 101) where
  add a b := ⟨(a.val + b.val) % 101, Nat.mod_lt _ (by decide)⟩
  sub a b := ⟨(a.val + (101 - b.val) % 101) % 101, Nat.mod_lt _ (by decide)⟩
  mul a b := ⟨(a.val * b.val) % 101, Nat.mod_lt _ (by decide)⟩
  neg a := ⟨(101 - a.val) % 101, Nat.mod_lt _ (by decide)⟩
  zero := ⟨0, by decide⟩
  one := ⟨1, by decide⟩
  inv := f101Inv
  add_assoc a b c := by
    apply Fin.ext
    change ((a.val + b.val) % 101 + c.val) % 101 = (a.val + (b.val + c.val) % 101) % 101
    rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
  add_comm a b := by
    apply Fin.ext
    change (a.val + b.val) % 101 = (b.val + a.val) % 101
    rw [Nat.add_comm]
  zero_add a := by
    apply Fin.ext
    change (0 + a.val) % 101 = a.val
    rw [Nat.zero_add, Nat.mod_eq_of_lt a.isLt]
  add_neg a := by
    apply Fin.ext
    change (a.val + (101 - a.val) % 101) % 101 = 0
    rw [Nat.add_mod_mod]
    have hlt := a.isLt
    have hsum : a.val + (101 - a.val) = 101 := by omega
    rw [hsum]
  sub_eq _ _ := rfl
  mul_assoc a b c := by
    apply Fin.ext
    change ((a.val * b.val) % 101 * c.val) % 101 = (a.val * ((b.val * c.val) % 101)) % 101
    rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]
  mul_comm a b := by
    apply Fin.ext
    change (a.val * b.val) % 101 = (b.val * a.val) % 101
    rw [Nat.mul_comm]
  one_mul a := by
    apply Fin.ext
    change (1 * a.val) % 101 = a.val
    rw [Nat.one_mul, Nat.mod_eq_of_lt a.isLt]
  left_distrib a b c := by
    apply Fin.ext
    change (a.val * ((b.val + c.val) % 101)) % 101 = ((a.val * b.val) % 101 + (a.val * c.val) % 101) % 101
    rw [Nat.mul_mod_mod, Nat.mod_add_mod, Nat.add_mod_mod, Nat.mul_add]
  zero_ne_one := by decide
  mul_inv_cancel a ha := by
    apply Fin.ext
    have hne : a.val ≠ 0 := fun h => ha (Fin.ext h)
    exact f101_mul_inv_all a hne

theorem ofMod101_add (a b : Nat) : ofMod101 (a + b) = ofMod101 a + ofMod101 b := by
  apply Fin.ext
  change (a + b) % 101 = (a % 101 + b % 101) % 101
  exact Nat.add_mod a b 101

theorem ofMod101_mul (a b : Nat) : ofMod101 (a * b) = ofMod101 a * ofMod101 b := by
  apply Fin.ext
  change (a * b) % 101 = (a % 101 * (b % 101)) % 101
  exact Nat.mul_mod a b 101

theorem ofMod101_sumNat (n : Nat) (f : Nat → Nat) :
    ofMod101 (sumNat n f) = sumR (R := Fin 101) n (fun i => ofMod101 (f i)) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumNat, sumR, ofMod101_add, ih]

theorem sumR_ofMod101_mul (n : Nat) (f g : Nat → Nat) :
    sumR (R := Fin 101) n (fun t => ofMod101 (f t) * ofMod101 (g t)) =
    ofMod101 (sumNat n (fun t => f t * g t)) := by
  rw [ofMod101_sumNat]
  exact sumR_congr (fun t _ => (ofMod101_mul (f t) (g t)).symm)

-- ============================================================================
-- Section 2: Sound Kronecker Base-`2^20` Packed Matrix Multiplication Engine
-- ============================================================================

def B20 : Nat := 1048576

def vecAtNat : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => vecAtNat xs k

def vecAtList : List (List Nat) → Nat → List Nat
  | [], _ => []
  | x :: _, 0 => x
  | _ :: xs, k + 1 => vecAtList xs k

def unpackEntry (row c : Nat) : Nat := (row / B20 ^ c) % B20

def unpackColRev (k colRev t : Nat) : Nat := unpackEntry colRev (k - 1 - t)

def rowMat (rows : List Nat) (r c : Nat) : Fin 101 :=
  ofMod101 (unpackEntry (vecAtNat rows r) c)

def colRevMat (k : Nat) (colsRev : List Nat) (r c : Nat) : Fin 101 :=
  ofMod101 (unpackColRev k (vecAtNat colsRev c) r)

/-- Checks that `x` encodes `k` base-`B20` digits, each `< 101`, with no higher digits. -/
def rowValid : Nat → Nat → Bool
  | 0, x => x == 0
  | k + 1, x => decide (x % B20 < 101) && rowValid k (x / B20)

def packRow (k : Nat) (f : Nat → Nat) : Nat :=
  sumNat k (fun t => f t * B20 ^ t)

theorem rowValid_digits : ∀ (k x : Nat), rowValid k x = true →
    (∀ c, c < k → unpackEntry x c < 101) ∧ packRow k (unpackEntry x) = x
  | 0, x, h => by
    have hx0 : x = 0 := of_decide_eq_true (by simpa [rowValid] using h)
    exact ⟨fun _ hc => absurd hc (Nat.not_lt_zero _), by simp [packRow, sumNat, hx0]⟩
  | k + 1, x, h => by
    simp only [rowValid, Bool.and_eq_true] at h
    have hd0 : x % B20 < 101 := of_decide_eq_true h.1
    obtain ⟨hdig, hpack⟩ := rowValid_digits k (x / B20) h.2
    have hshift : ∀ c, unpackEntry x (c + 1) = unpackEntry (x / B20) c := by
      intro c
      unfold unpackEntry
      rw [Nat.pow_succ, Nat.mul_comm (B20 ^ c) B20, ← Nat.div_div_eq_div_mul]
    constructor
    · intro c hc
      cases c with
      | zero => simpa [unpackEntry] using hd0
      | succ c' =>
        rw [hshift c']
        exact hdig c' (Nat.lt_of_succ_lt_succ hc)
    · have hsplit : ∀ m : Nat, packRow (m + 1) (unpackEntry x) =
          x % B20 + B20 * packRow m (unpackEntry (x / B20)) := by
        intro m
        induction m with
        | zero => simp [packRow, sumNat, unpackEntry]
        | succ j ih =>
          change packRow (j + 1) (unpackEntry x) + unpackEntry x (j + 1) * B20 ^ (j + 1) =
                 x % B20 + B20 * (packRow j (unpackEntry (x / B20)) + unpackEntry (x / B20) j * B20 ^ j)
          rw [ih, hshift j, Nat.mul_add, Nat.add_assoc]
          congr 1
          rw [Nat.pow_succ, Nat.mul_comm (B20 ^ j) B20,
              ← Nat.mul_assoc, Nat.mul_comm (unpackEntry (x / B20) j) B20, Nat.mul_assoc]
      rw [hsplit k, hpack, Nat.add_comm]
      exact Nat.div_add_mod x B20

theorem sumNat_mul_left (n c : Nat) (f : Nat → Nat) :
    c * sumNat n f = sumNat n (fun i => c * f i) := by
  induction n with
  | zero => simp [sumNat]
  | succ m ih => simp [sumNat, Nat.mul_add, ih]

theorem sumNat_mul_right (n c : Nat) (f : Nat → Nat) :
    sumNat n f * c = sumNat n (fun i => f i * c) := by
  induction n with
  | zero => simp [sumNat]
  | succ m ih => simp [sumNat, Nat.add_mul, ih]

theorem sumNat_add (n : Nat) (f g : Nat → Nat) :
    sumNat n (fun i => f i + g i) = sumNat n f + sumNat n g := by
  induction n with
  | zero => simp [sumNat]
  | succ m ih => simp [sumNat, ih]; omega

theorem sumNat_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumNat]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h m (Nat.lt_succ_self m)]

theorem sumNat_le_sumNat {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i ≤ g i) :
    sumNat n f ≤ sumNat n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    simp only [sumNat]
    exact Nat.add_le_add (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h m (Nat.lt_succ_self m))

theorem sumNat_const (n c : Nat) : sumNat n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumNat]
  | succ m ih => simp [sumNat, ih, Nat.succ_mul]

theorem geom_sum_lt_pow (B : Nat) (hB : 2 ≤ B) :
    ∀ n : Nat, sumNat n (fun d => (B - 1) * B ^ d) < B ^ n
  | 0 => by simp [sumNat]
  | n + 1 => by
    simp only [sumNat]
    have ih := geom_sum_lt_pow B hB n
    have hB1 : 1 + (B - 1) = B := by omega
    have hpow : B ^ (n + 1) = B ^ n + (B - 1) * B ^ n := by
      calc B ^ (n + 1) = B ^ n * B := Nat.pow_succ B n
        _ = B * B ^ n := Nat.mul_comm _ _
        _ = (1 + (B - 1)) * B ^ n := by rw [hB1]
        _ = B ^ n + (B - 1) * B ^ n := by rw [Nat.add_mul, Nat.one_mul]
    rw [hpow]
    exact Nat.add_lt_add_right ih _

/-- **Core Kronecker Dot-Product Soundness Theorem (`packed_dot_sound`):**
    For `1 ≤ k ≤ 60` and valid base-`B20` packed row `p` and reversed column `q` (digits `< 101`),
    `((p * q) / B20^(k - 1)) % B20` equals the EXACT integer dot product `∑_{t < k} A_t * B_t`. -/
theorem packed_dot_sound (k p q : Nat) (hk1 : 1 ≤ k) (hk60 : k ≤ 60)
    (hp : rowValid k p = true) (hq : rowValid k q = true) :
    ((p * q) / B20 ^ (k - 1)) % B20 =
    sumNat k (fun t => unpackEntry p t * unpackColRev k q t) := by
  obtain ⟨hp_d, hp_eq⟩ := rowValid_digits k p hp
  obtain ⟨hq_d, hq_eq⟩ := rowValid_digits k q hq
  let f := unpackEntry p
  let g := unpackEntry q
  have hterm_split : ∀ i j,
      f i * g j * B20 ^ (i + j) =
      (if i + j < k - 1 then f i * g j * B20 ^ (i + j) else 0) +
      (if i + j = k - 1 then f i * g j else 0) * B20 ^ (k - 1) +
      (if k ≤ i + j then f i * g j * B20 ^ (i + j - k) else 0) * B20 * B20 ^ (k - 1) := by
    intro i j
    by_cases h1 : i + j < k - 1
    · have h2 : ¬ (i + j = k - 1) := by omega
      have h3 : ¬ (k ≤ i + j) := by omega
      simp only [h1, h2, h3, ↓reduceIte, Nat.zero_mul, Nat.add_zero]
    · by_cases h2 : i + j = k - 1
      · have h3 : ¬ (k ≤ i + j) := by omega
        simp only [h1, h3, ↓reduceIte, Nat.zero_add, Nat.zero_mul, Nat.add_zero]
        rw [h2]; simp
      · have h3 : k ≤ i + j := by omega
        simp only [h1, h2, h3, ↓reduceIte, Nat.zero_add, Nat.zero_mul]
        have hexp : i + j = (i + j - k) + 1 + (k - 1) := by omega
        calc f i * g j * B20 ^ (i + j)
            = f i * g j * B20 ^ ((i + j - k) + 1 + (k - 1)) := by rw [← hexp]
          _ = f i * g j * (B20 ^ (i + j - k) * B20 * B20 ^ (k - 1)) := by
              rw [Nat.pow_add, Nat.pow_succ]
          _ = f i * g j * B20 ^ (i + j - k) * B20 * B20 ^ (k - 1) := by
              rw [← Nat.mul_assoc, ← Nat.mul_assoc]
  let low := sumNat k (fun i => sumNat k (fun j => if i + j < k - 1 then f i * g j * B20 ^ (i + j) else 0))
  let mid := sumNat k (fun i => sumNat k (fun j => if i + j = k - 1 then f i * g j else 0))
  let high := sumNat k (fun i => sumNat k (fun j => if k ≤ i + j then f i * g j * B20 ^ (i + j - k) else 0))
  have hpq : p * q = low + (mid + high * B20) * B20 ^ (k - 1) := by
    have h1 : p * q = packRow k f * packRow k g := by rw [hp_eq, hq_eq]
    rw [h1]
    unfold packRow
    rw [sumNat_mul_right]
    have hstep1 : sumNat k (fun i => f i * B20 ^ i * sumNat k (fun j => g j * B20 ^ j)) =
        sumNat k (fun i => sumNat k (fun j => f i * g j * B20 ^ (i + j))) := by
      apply sumNat_congr; intro i _
      rw [sumNat_mul_left]
      apply sumNat_congr; intro j _
      rw [Nat.pow_add]
      calc f i * B20 ^ i * (g j * B20 ^ j)
          = f i * (B20 ^ i * g j) * B20 ^ j := by rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
        _ = f i * (g j * B20 ^ i) * B20 ^ j := by rw [Nat.mul_comm (B20 ^ i) (g j)]
        _ = f i * g j * (B20 ^ i * B20 ^ j) := by rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
    rw [hstep1]
    have hstep2 : sumNat k (fun i => sumNat k (fun j => f i * g j * B20 ^ (i + j))) =
        low + mid * B20 ^ (k - 1) + high * B20 * B20 ^ (k - 1) := by
      dsimp only [low, mid, high]
      rw [sumNat_mul_right, sumNat_mul_right, sumNat_mul_right, ← sumNat_add, ← sumNat_add]
      apply sumNat_congr; intro i _
      rw [sumNat_mul_right, sumNat_mul_right, sumNat_mul_right, ← sumNat_add, ← sumNat_add]
      apply sumNat_congr; intro j _
      exact hterm_split i j
    rw [hstep2, Nat.add_mul, Nat.add_assoc]
  have hmid_eq : mid = sumNat k (fun t => unpackEntry p t * unpackColRev k q t) := by
    dsimp only [mid, f, g, unpackColRev]
    apply sumNat_congr; intro i hi
    have hsingle : ∀ n : Nat, sumNat n (fun j => if i + j = k - 1 then unpackEntry p i * unpackEntry q j else 0) =
        if k - 1 - i < n then unpackEntry p i * unpackEntry q (k - 1 - i) else 0 := by
      intro n
      induction n with
      | zero => simp [sumNat]
      | succ m ih =>
        simp only [sumNat, ih]
        by_cases hm : i + m = k - 1
        · have h1 : m = k - 1 - i := by omega
          have h2 : ¬ (k - 1 - i < m) := by omega
          have h3 : k - 1 - i < m + 1 := by omega
          simp only [hm, h2, h3, ↓reduceIte, Nat.zero_add]
          rw [h1]
        · have hiff : (k - 1 - i < m + 1) ↔ (k - 1 - i < m) := by omega
          simp [hm, hiff]
    rw [hsingle k]
    have hlt : k - 1 - i < k := by omega
    simp [hlt]
  have hmid_lt : mid < B20 := by
    rw [hmid_eq]
    have hle : sumNat k (fun t => unpackEntry p t * unpackColRev k q t) ≤ sumNat k (fun _ => 10000) := by
      apply sumNat_le_sumNat; intro t ht
      have h1 : unpackEntry p t ≤ 100 := by have := hp_d t ht; omega
      have h2 : unpackColRev k q t ≤ 100 := by unfold unpackColRev; have := hq_d (k - 1 - t) (by omega); omega
      exact Nat.mul_le_mul h1 h2
    rw [sumNat_const] at hle
    have hB : B20 = 1048576 := rfl
    omega
  have hlow_lt : low < B20 ^ (k - 1) := by
    have hgroup : ∀ i, i < k →
        sumNat k (fun j => if i + j < k - 1 then f i * g j * B20 ^ (i + j) else 0) ≤
        sumNat (k - 1) (fun d => 10000 * B20 ^ d) := by
      intro i hi
      have hrew : sumNat k (fun j => if i + j < k - 1 then f i * g j * B20 ^ (i + j) else 0) ≤
          sumNat (k - 1) (fun d => if i ≤ d then 10000 * B20 ^ d else 0) := by
        have haux : ∀ n : Nat, n ≤ k →
            sumNat n (fun j => if i + j < k - 1 then f i * g j * B20 ^ (i + j) else 0) ≤
            sumNat (k - 1) (fun d => if i ≤ d ∧ d < i + n then 10000 * B20 ^ d else 0) := by
          intro n hn
          induction n with
          | zero => simp only [sumNat]; exact Nat.zero_le _
          | succ m ih =>
            simp only [sumNat]
            have hih := ih (by omega)
            by_cases him : i + m < k - 1
            · simp only [him, ↓reduceIte]
              have hterm : f i * g m * B20 ^ (i + m) ≤ 10000 * B20 ^ (i + m) := by
                have h1 : f i ≤ 100 := by dsimp only [f]; have := hp_d i hi; omega
                have h2 : g m ≤ 100 := by dsimp only [g]; have := hq_d m (by omega); omega
                exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2)
              have hsplit_d : sumNat (k - 1) (fun d => if i ≤ d ∧ d < i + (m + 1) then 10000 * B20 ^ d else 0) =
                  sumNat (k - 1) (fun d => if i ≤ d ∧ d < i + m then 10000 * B20 ^ d else 0) +
                  10000 * B20 ^ (i + m) := by
                have hpoint : ∀ d,
                    (if i ≤ d ∧ d < i + (m + 1) then 10000 * B20 ^ d else 0) =
                    (if i ≤ d ∧ d < i + m then 10000 * B20 ^ d else 0) +
                    (if d = i + m then 10000 * B20 ^ d else 0) := by
                  intro d
                  by_cases hdm : d = i + m
                  · subst hdm
                    have ha : (if i ≤ i + m ∧ i + m < i + (m + 1) then 10000 * B20 ^ (i + m) else 0) = 10000 * B20 ^ (i + m) := by split <;> omega
                    have hb : (if i ≤ i + m ∧ i + m < i + m then 10000 * B20 ^ (i + m) else 0) = 0 := by split <;> omega
                    rw [ha, hb, Nat.zero_add]; simp
                  · have hiff : (i ≤ d ∧ d < i + (m + 1)) ↔ (i ≤ d ∧ d < i + m) := by omega
                    simp [hdm, hiff]
                rw [sumNat_congr (fun d _ => hpoint d), sumNat_add]
                congr 1
                have hs : ∀ N : Nat, sumNat N (fun d => if d = i + m then 10000 * B20 ^ d else 0) =
                    if i + m < N then 10000 * B20 ^ (i + m) else 0 := by
                  intro N
                  induction N with
                  | zero => simp [sumNat]
                  | succ t iht =>
                    simp only [sumNat, iht]
                    by_cases ht : t = i + m
                    · subst ht; simp
                    · have hiff : (i + m < t + 1) ↔ (i + m < t) := by omega
                      simp [ht, hiff]
                rw [hs (k - 1)]; simp [him]
              rw [hsplit_d]
              exact Nat.add_le_add hih hterm
            · simp only [him, ↓reduceIte, Nat.add_zero]
              refine Nat.le_trans hih (sumNat_le_sumNat fun d _ => ?_)
              by_cases hc : i ≤ d ∧ d < i + m
              · have hc2 : i ≤ d ∧ d < i + (m + 1) := by omega
                simp [hc, hc2]
              · simp [hc]
        exact Nat.le_trans (haux k (Nat.le_refl k)) (sumNat_le_sumNat fun d _ => by split <;> split <;> omega)
      exact Nat.le_trans hrew (sumNat_le_sumNat fun d _ => by split <;> omega)
    have hlow_le : low ≤ k * sumNat (k - 1) (fun d => 10000 * B20 ^ d) := by
      have h1 : low ≤ sumNat k (fun _ => sumNat (k - 1) (fun d => 10000 * B20 ^ d)) :=
        sumNat_le_sumNat hgroup
      rw [sumNat_const] at h1
      exact h1
    rw [sumNat_mul_left] at hlow_le
    have hlow_le2 : low ≤ sumNat (k - 1) (fun d => (B20 - 1) * B20 ^ d) := by
      refine Nat.le_trans hlow_le (sumNat_le_sumNat fun d _ => ?_)
      rw [← Nat.mul_assoc]
      apply Nat.mul_le_mul_right
      have hB : B20 = 1048576 := rfl
      omega
    exact Nat.lt_of_le_of_lt hlow_le2 (geom_sum_lt_pow B20 (by decide) (k - 1))
  have hpow_pos : 0 < B20 ^ (k - 1) := Nat.pow_pos (by decide)
  rw [hpq, Nat.add_mul_div_right _ _ hpow_pos, Nat.div_eq_of_lt hlow_lt, Nat.zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmid_lt, hmid_eq]

-- ============================================================================
-- Section 3: Kernel-Decidable Packed Matrix Checkers & Soundness Bridges
-- ============================================================================

def allRowsValid (m k : Nat) (rows : List Nat) : Bool :=
  (rows.length == m) && rows.all (rowValid k)

theorem allRowsValid_len {m k : Nat} {rows : List Nat} (h : allRowsValid m k rows = true) :
    rows.length = m := by
  simp only [allRowsValid, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem allRowsValid_at {m k : Nat} {rows : List Nat} (h : allRowsValid m k rows = true)
    (i : Nat) (hi : i < m) : rowValid k (vecAtNat rows i) = true := by
  simp only [allRowsValid, Bool.and_eq_true, beq_iff_eq] at h
  have hall : ∀ l : List Nat, l.all (rowValid k) = true → ∀ idx, idx < l.length → rowValid k (vecAtNat l idx) = true := by
    intro l
    induction l with
    | nil => intro _ _ hlt; simp at hlt
    | cons x xs ih =>
      intro ha idx hidx
      simp only [List.all_cons, Bool.and_eq_true] at ha
      cases idx with
      | zero => exact ha.1
      | succ j => exact ih ha.2 j (Nat.lt_of_succ_lt_succ hidx)
  exact hall rows h.2 i (by omega)

/-- Streaming `O(k)` check that packed reversed-column `x` agrees entry-for-entry mod 101 with `f`. -/
def checkColRevAgainstFn (f : Nat → Nat) : Nat → Nat → Bool
  | 0, x => x == 0
  | k + 1, x => decide (x % B20 < 101) && ((x % B20) % 101 == f k % 101) && checkColRevAgainstFn f k (x / B20)

theorem checkColRevAgainstFn_sound (f : Nat → Nat) :
    ∀ (k x : Nat), checkColRevAgainstFn f k x = true →
      ∀ t, t < k → unpackColRev k x t % 101 = f t % 101
  | 0, _, _, _, ht => absurd ht (Nat.not_lt_zero _)
  | k + 1, x, h, t, ht => by
    simp only [checkColRevAgainstFn, Bool.and_eq_true, beq_iff_eq] at h
    by_cases htk : t = k
    · rw [htk]
      have h0 : k + 1 - 1 - k = 0 := by omega
      unfold unpackColRev unpackEntry
      rw [h0]; simpa using h.1.2
    · have htlt : t < k := by omega
      have ih := checkColRevAgainstFn_sound f k (x / B20) h.2 t htlt
      have hsh : unpackColRev (k + 1) x t = unpackColRev k (x / B20) t := by
        unfold unpackColRev unpackEntry
        have hexp : k + 1 - 1 - t = (k - 1 - t) + 1 := by omega
        rw [hexp, Nat.pow_succ, Nat.mul_comm (B20 ^ (k - 1 - t)) B20, ← Nat.div_div_eq_div_mul]
      rw [hsh]
      exact ih

def checkColsAgainstMat (k : Nat) (F : Nat → Nat → Nat) : Nat → List Nat → Bool
  | _, [] => true
  | c, col :: cols => checkColRevAgainstFn (fun r => F r c) k col && checkColsAgainstMat k F (c + 1) cols

theorem checkColsAgainstMat_sound (k : Nat) (F : Nat → Nat → Nat) :
    ∀ (c0 : Nat) (cols : List Nat), checkColsAgainstMat k F c0 cols = true →
      ∀ r j, r < k → j < cols.length →
        unpackColRev k (vecAtNat cols j) r % 101 = F r (c0 + j) % 101
  | _, [], _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | c0, col :: cols, h, r, j, hr, hj => by
    simp only [checkColsAgainstMat, Bool.and_eq_true] at h
    cases j with
    | zero =>
      dsimp only [vecAtNat]; rw [Nat.add_zero]
      exact checkColRevAgainstFn_sound (fun r => F r c0) k col h.1 r hr
    | succ j' =>
      have ih := checkColsAgainstMat_sound k F (c0 + 1) cols h.2 r j' hr (Nat.lt_of_succ_lt_succ hj)
      have hadd : c0 + 1 + j' = c0 + (j' + 1) := by omega
      rw [hadd] at ih; exact ih

/-- Streaming `O(n)` check that packed row `x` agrees entry-for-entry mod 101 with `f`. -/
def checkRowAgainstFn (f : Nat → Nat) : Nat → Nat → Nat → Bool
  | _, 0, x => x == 0
  | c, rem + 1, x => decide (x % B20 < 101) && ((x % B20) % 101 == f c % 101) && checkRowAgainstFn f (c + 1) rem (x / B20)

theorem checkRowAgainstFn_sound (f : Nat → Nat) :
    ∀ (c0 rem x : Nat), checkRowAgainstFn f c0 rem x = true →
      ∀ j, j < rem → unpackEntry x j % 101 = f (c0 + j) % 101
  | _, 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | c0, rem + 1, x, h, j, hj => by
    simp only [checkRowAgainstFn, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero =>
      rw [Nat.add_zero]; unfold unpackEntry; simpa using h.1.2
    | succ j' =>
      have ih := checkRowAgainstFn_sound f (c0 + 1) rem (x / B20) h.2 j' (Nat.lt_of_succ_lt_succ hj)
      have hsh : unpackEntry (x / B20) j' = unpackEntry x (j' + 1) := by
        unfold unpackEntry
        rw [Nat.pow_succ, Nat.mul_comm (B20 ^ j') B20, ← Nat.div_div_eq_div_mul]
      have hadd : c0 + 1 + j' = c0 + (j' + 1) := by omega
      rw [← hsh, ← hadd]; exact ih

def checkRowsAgainstMat (n : Nat) (F : Nat → Nat → Nat) : Nat → List Nat → Bool
  | _, [] => true
  | r, row :: rows => checkRowAgainstFn (fun c => F r c) 0 n row && checkRowsAgainstMat n F (r + 1) rows

theorem checkRowsAgainstMat_sound (n : Nat) (F : Nat → Nat → Nat) :
    ∀ (r0 : Nat) (rows : List Nat), checkRowsAgainstMat n F r0 rows = true →
      ∀ i c, i < rows.length → c < n →
        unpackEntry (vecAtNat rows i) c % 101 = F (r0 + i) c % 101
  | _, [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | r0, row :: rows, h, i, c, hi, hc => by
    simp only [checkRowsAgainstMat, Bool.and_eq_true] at h
    cases i with
    | zero =>
      dsimp only [vecAtNat]; rw [Nat.add_zero]
      have hr := checkRowAgainstFn_sound (fun c => F r0 c) 0 n row h.1 c hc
      rw [Nat.zero_add] at hr; exact hr
    | succ i' =>
      have ih := checkRowsAgainstMat_sound n F (r0 + 1) rows h.2 i' c (Nat.lt_of_succ_lt_succ hi) hc
      have hadd : r0 + 1 + i' = r0 + (i' + 1) := by omega
      rw [hadd] at ih; exact ih

/-- Check `rowMat rows = colRevMat m colsRev` on `m × n` (streaming `O(m*n)`). -/
def checkRowEqColRev (m n : Nat) (rows colsRev : List Nat) : Bool :=
  (rows.length == m) && (colsRev.length == n) &&
  checkColsAgainstMat m (fun r c => unpackEntry (vecAtNat rows r) c) 0 colsRev

theorem checkRowEqColRev_sound {m n : Nat} {rows colsRev : List Nat}
    (h : checkRowEqColRev m n rows colsRev = true) :
    MatEq m n (rowMat rows) (colRevMat m colsRev) := by
  simp only [checkRowEqColRev, Bool.and_eq_true, beq_iff_eq] at h
  intro i j hi hj
  have hc := checkColsAgainstMat_sound m (fun r c => unpackEntry (vecAtNat rows r) c) 0 colsRev h.2 i j hi (by omega)
  rw [Nat.zero_add] at hc
  exact Fin.ext hc.symm

/-- Check `A * B = I_m` (`m × k` row-packed times `k × m` colRev-packed). -/
def checkMulIdRows (bKm1 r : Nat) (p : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | c, q :: qs =>
    let exp := if r == c then 1 else 0
    ((((p * q) / bKm1) % B20) % 101 == exp) && checkMulIdRows bKm1 r p (c + 1) qs

def checkMulIdGo (bKm1 : Nat) (cols : List Nat) (r : Nat) : List Nat → Bool
  | [] => true
  | p :: ps => checkMulIdRows bKm1 r p 0 cols && checkMulIdGo bKm1 cols (r + 1) ps

def checkMulId (k m : Nat) (rows colsRev : List Nat) : Bool :=
  (decide (1 ≤ k) && decide (k ≤ 60)) &&
  (allRowsValid m k rows && allRowsValid m k colsRev) &&
  checkMulIdGo (B20 ^ (k - 1)) colsRev 0 rows

theorem checkMulIdRows_sound {bKm1 r p : Nat} :
    ∀ (c0 : Nat) (qs : List Nat),
      checkMulIdRows bKm1 r p c0 qs = true →
      ∀ j, j < qs.length →
        (((p * vecAtNat qs j) / bKm1) % B20) % 101 = (if r = c0 + j then 1 else 0)
  | _, [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | c0, q :: qs, h, j, hj => by
    simp only [checkMulIdRows, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero =>
      dsimp only [vecAtNat]; rw [Nat.add_zero]
      exact h.1
    | succ j' =>
      have ih := checkMulIdRows_sound (c0 + 1) qs h.2 j' (Nat.lt_of_succ_lt_succ hj)
      have hadd : c0 + 1 + j' = c0 + (j' + 1) := by omega
      rw [hadd] at ih; exact ih

theorem checkMulIdGo_sound {bKm1 : Nat} {cols : List Nat} :
    ∀ (r0 : Nat) (ps : List Nat),
      checkMulIdGo bKm1 cols r0 ps = true →
      ∀ i j, i < ps.length → j < cols.length →
        (((vecAtNat ps i * vecAtNat cols j) / bKm1) % B20) % 101 = (if r0 + i = j then 1 else 0)
  | _, [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | r0, p :: ps, h, i, j, hi, hj => by
    simp only [checkMulIdGo, Bool.and_eq_true] at h
    cases i with
    | zero =>
      dsimp only [vecAtNat]; rw [Nat.add_zero]
      have hr := checkMulIdRows_sound 0 cols h.1 j hj
      rw [Nat.zero_add] at hr; exact hr
    | succ i' =>
      have ih := checkMulIdGo_sound (r0 + 1) ps h.2 i' j (Nat.lt_of_succ_lt_succ hi) hj
      have hadd : r0 + 1 + i' = r0 + (i' + 1) := by omega
      rw [hadd] at ih; exact ih

theorem checkMulId_sound {k m : Nat} {rows colsRev : List Nat}
    (h : checkMulId k m rows colsRev = true) :
    MatEq m m (matMulF k (rowMat rows) (colRevMat k colsRev)) matIdF := by
  simp only [checkMulId, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hk1b, hk60b⟩, ⟨hvr, hvc⟩⟩, hgo⟩
  have hk1 : 1 ≤ k := of_decide_eq_true hk1b
  have hk60 : k ≤ 60 := of_decide_eq_true hk60b
  have hlenR := allRowsValid_len hvr
  have hlenC := allRowsValid_len hvc
  intro i j hi hj
  have hcell := checkMulIdGo_sound 0 rows hgo i j (by omega) (by omega)
  rw [Nat.zero_add] at hcell
  have hdot := packed_dot_sound k (vecAtNat rows i) (vecAtNat colsRev j) hk1 hk60
    (allRowsValid_at hvr i hi) (allRowsValid_at hvc j hj)
  unfold matMulF rowMat colRevMat
  rw [sumR_ofMod101_mul, ← hdot]
  apply Fin.ext
  change (((vecAtNat rows i * vecAtNat colsRev j) / B20 ^ (k - 1)) % B20) % 101 = (matIdF (R := Fin 101) i j).val
  rw [hcell]; unfold matIdF
  by_cases hij : i = j <;> simp [hij]

/-- Check `A * B = C` (`m × k` row-packed times `k × n` colRev-packed = `m × n` row-packed). -/
def checkMulEqRowInner (bKm1 p cRow : Nat) : List Nat → Bool
  | [] => true
  | q :: qs =>
    ((((p * q) / bKm1) % B20) % 101 == (cRow % B20) % 101) &&
    checkMulEqRowInner bKm1 p (cRow / B20) qs

def checkMulEqRowGo (bKm1 : Nat) (Bcols : List Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | p :: ps, c :: cs => checkMulEqRowInner bKm1 p c Bcols && checkMulEqRowGo bKm1 Bcols ps cs
  | _, _ => false

def checkMulEqRow (m k n : Nat) (Arows Bcols Crows : List Nat) : Bool :=
  (decide (1 ≤ k) && decide (k ≤ 60)) &&
  (allRowsValid m k Arows && allRowsValid n k Bcols && allRowsValid m n Crows) &&
  checkMulEqRowGo (B20 ^ (k - 1)) Bcols Arows Crows

theorem checkMulEqRowInner_sound {bKm1 p : Nat} :
    ∀ (cRow : Nat) (qs : List Nat),
      checkMulEqRowInner bKm1 p cRow qs = true →
      ∀ j, j < qs.length →
        (((p * vecAtNat qs j) / bKm1) % B20) % 101 = unpackEntry cRow j % 101
  | _, [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | cRow, q :: qs, h, j, hj => by
    simp only [checkMulEqRowInner, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => simpa [vecAtNat, unpackEntry] using h.1
    | succ j' =>
      have ih := checkMulEqRowInner_sound (cRow / B20) qs h.2 j' (Nat.lt_of_succ_lt_succ hj)
      have hsh : unpackEntry (cRow / B20) j' = unpackEntry cRow (j' + 1) := by
        unfold unpackEntry
        rw [Nat.pow_succ, Nat.mul_comm (B20 ^ j') B20, ← Nat.div_div_eq_div_mul]
      rw [hsh] at ih; exact ih

theorem checkMulEqRowGo_sound {bKm1 : Nat} {Bcols : List Nat} :
    ∀ (ps cs : List Nat),
      checkMulEqRowGo bKm1 Bcols ps cs = true →
      ∀ i j, i < ps.length → j < Bcols.length →
        (((vecAtNat ps i * vecAtNat Bcols j) / bKm1) % B20) % 101 = unpackEntry (vecAtNat cs i) j % 101
  | [], [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | [], _ :: _, h, _, _, _, _ => by simp [checkMulEqRowGo] at h
  | _ :: _, [], h, _, _, _, _ => by simp [checkMulEqRowGo] at h
  | p :: ps, c :: cs, h, i, j, hi, hj => by
    simp only [checkMulEqRowGo, Bool.and_eq_true] at h
    cases i with
    | zero => exact checkMulEqRowInner_sound c Bcols h.1 j hj
    | succ i' => exact checkMulEqRowGo_sound ps cs h.2 i' j (Nat.lt_of_succ_lt_succ hi) hj

theorem checkMulEqRow_sound {m k n : Nat} {Arows Bcols Crows : List Nat}
    (h : checkMulEqRow m k n Arows Bcols Crows = true) :
    MatEq m n (matMulF k (rowMat Arows) (colRevMat k Bcols)) (rowMat Crows) := by
  simp only [checkMulEqRow, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hk1b, hk60b⟩, ⟨⟨hvA, hvB⟩, _hvC⟩⟩, hgo⟩
  have hk1 : 1 ≤ k := of_decide_eq_true hk1b
  have hk60 : k ≤ 60 := of_decide_eq_true hk60b
  have hlenA := allRowsValid_len hvA
  have hlenB := allRowsValid_len hvB
  intro i j hi hj
  have hcell := checkMulEqRowGo_sound Arows Crows hgo i j (by omega) (by omega)
  have hdot := packed_dot_sound k (vecAtNat Arows i) (vecAtNat Bcols j) hk1 hk60
    (allRowsValid_at hvA i hi) (allRowsValid_at hvB j hj)
  unfold matMulF rowMat colRevMat
  rw [sumR_ofMod101_mul, ← hdot]
  exact Fin.ext hcell

/-- Check `A * B = C * D` (`m × k1 · k1 × n = m × k2 · k2 × n`). -/
def checkMulEqMulInner (b1 b2 p1 p2 : Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | q1 :: qs1, q2 :: qs2 =>
    ((((p1 * q1) / b1) % B20) % 101 == (((p2 * q2) / b2) % B20) % 101) &&
    checkMulEqMulInner b1 b2 p1 p2 qs1 qs2
  | _, _ => false

def checkMulEqMulGo (b1 b2 : Nat) (Bcols Dcols : List Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | p1 :: ps1, p2 :: ps2 =>
    checkMulEqMulInner b1 b2 p1 p2 Bcols Dcols && checkMulEqMulGo b1 b2 Bcols Dcols ps1 ps2
  | _, _ => false

def checkMulEqMul (m k1 k2 n : Nat) (Arows Bcols Crows Dcols : List Nat) : Bool :=
  ((decide (1 ≤ k1) && decide (k1 ≤ 60)) && (decide (1 ≤ k2) && decide (k2 ≤ 60))) &&
  ((allRowsValid m k1 Arows && allRowsValid n k1 Bcols) &&
   (allRowsValid m k2 Crows && allRowsValid n k2 Dcols)) &&
  checkMulEqMulGo (B20 ^ (k1 - 1)) (B20 ^ (k2 - 1)) Bcols Dcols Arows Crows

theorem checkMulEqMulInner_sound {b1 b2 p1 p2 : Nat} :
    ∀ (qs1 qs2 : List Nat),
      checkMulEqMulInner b1 b2 p1 p2 qs1 qs2 = true →
      ∀ j, j < qs1.length →
        (((p1 * vecAtNat qs1 j) / b1) % B20) % 101 = (((p2 * vecAtNat qs2 j) / b2) % B20) % 101
  | [], [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | [], _ :: _, h, _, _ => by simp [checkMulEqMulInner] at h
  | _ :: _, [], h, _, _ => by simp [checkMulEqMulInner] at h
  | q1 :: qs1, q2 :: qs2, h, j, hj => by
    simp only [checkMulEqMulInner, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => exact h.1
    | succ j' => exact checkMulEqMulInner_sound qs1 qs2 h.2 j' (Nat.lt_of_succ_lt_succ hj)

theorem checkMulEqMulGo_sound {b1 b2 : Nat} {Bcols Dcols : List Nat} :
    ∀ (ps1 ps2 : List Nat),
      checkMulEqMulGo b1 b2 Bcols Dcols ps1 ps2 = true →
      ∀ i j, i < ps1.length → j < Bcols.length →
        (((vecAtNat ps1 i * vecAtNat Bcols j) / b1) % B20) % 101 =
        (((vecAtNat ps2 i * vecAtNat Dcols j) / b2) % B20) % 101
  | [], [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | [], _ :: _, h, _, _, _, _ => by simp [checkMulEqMulGo] at h
  | _ :: _, [], h, _, _, _, _ => by simp [checkMulEqMulGo] at h
  | p1 :: ps1, p2 :: ps2, h, i, j, hi, hj => by
    simp only [checkMulEqMulGo, Bool.and_eq_true] at h
    cases i with
    | zero => exact checkMulEqMulInner_sound Bcols Dcols h.1 j hj
    | succ i' => exact checkMulEqMulGo_sound ps1 ps2 h.2 i' j (Nat.lt_of_succ_lt_succ hi) hj

theorem checkMulEqMul_sound {m k1 k2 n : Nat} {Arows Bcols Crows Dcols : List Nat}
    (h : checkMulEqMul m k1 k2 n Arows Bcols Crows Dcols = true) :
    MatEq m n (matMulF k1 (rowMat Arows) (colRevMat k1 Bcols))
              (matMulF k2 (rowMat Crows) (colRevMat k2 Dcols)) := by
  simp only [checkMulEqMul, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hk1a, hk1b⟩, ⟨hk2a, hk2b⟩⟩, ⟨⟨hvA, hvB⟩, ⟨hvC, hvD⟩⟩⟩, hgo⟩
  have hlenA := allRowsValid_len hvA
  have hlenB := allRowsValid_len hvB
  intro i j hi hj
  have hcell := checkMulEqMulGo_sound Arows Crows hgo i j (by omega) (by omega)
  have hd1 := packed_dot_sound k1 (vecAtNat Arows i) (vecAtNat Bcols j)
    (of_decide_eq_true hk1a) (of_decide_eq_true hk1b)
    (allRowsValid_at hvA i hi) (allRowsValid_at hvB j hj)
  have hd2 := packed_dot_sound k2 (vecAtNat Crows i) (vecAtNat Dcols j)
    (of_decide_eq_true hk2a) (of_decide_eq_true hk2b)
    (allRowsValid_at hvC i hi) (allRowsValid_at hvD j hj)
  unfold matMulF rowMat colRevMat
  rw [sumR_ofMod101_mul, sumR_ofMod101_mul, ← hd1, ← hd2]
  exact Fin.ext hcell

/-- Check `A * B = C * D + E * F` (`m × k1 · k1 × n = m × k2 · k2 × n + m × k3 · k3 × n`). -/
def checkMulEqAddInner (b1 b2 b3 p1 p2 p3 : Nat) : List Nat → List Nat → List Nat → Bool
  | [], [], [] => true
  | q1 :: qs1, q2 :: qs2, q3 :: qs3 =>
    let lhs := (((p1 * q1) / b1) % B20) % 101
    let rhs := ((((p2 * q2) / b2) % B20) + (((p3 * q3) / b3) % B20)) % 101
    (lhs == rhs) && checkMulEqAddInner b1 b2 b3 p1 p2 p3 qs1 qs2 qs3
  | _, _, _ => false

def checkMulEqAddGo (b1 b2 b3 : Nat) (Bcols Dcols Fcols : List Nat) :
    List Nat → List Nat → List Nat → Bool
  | [], [], [] => true
  | p1 :: ps1, p2 :: ps2, p3 :: ps3 =>
    checkMulEqAddInner b1 b2 b3 p1 p2 p3 Bcols Dcols Fcols &&
    checkMulEqAddGo b1 b2 b3 Bcols Dcols Fcols ps1 ps2 ps3
  | _, _, _ => false

def checkMulEqAdd (m k1 k2 k3 n : Nat)
    (Arows Bcols Crows Dcols Erows Fcols : List Nat) : Bool :=
  ((decide (1 ≤ k1) && decide (k1 ≤ 60)) &&
   (decide (1 ≤ k2) && decide (k2 ≤ 60)) &&
   (decide (1 ≤ k3) && decide (k3 ≤ 60))) &&
  ((allRowsValid m k1 Arows && allRowsValid n k1 Bcols) &&
   (allRowsValid m k2 Crows && allRowsValid n k2 Dcols) &&
   (allRowsValid m k3 Erows && allRowsValid n k3 Fcols)) &&
  checkMulEqAddGo (B20 ^ (k1 - 1)) (B20 ^ (k2 - 1)) (B20 ^ (k3 - 1)) Bcols Dcols Fcols Arows Crows Erows

theorem checkMulEqAddInner_sound {b1 b2 b3 p1 p2 p3 : Nat} :
    ∀ (qs1 qs2 qs3 : List Nat),
      checkMulEqAddInner b1 b2 b3 p1 p2 p3 qs1 qs2 qs3 = true →
      ∀ j, j < qs1.length →
        (((p1 * vecAtNat qs1 j) / b1) % B20) % 101 =
        ((((p2 * vecAtNat qs2 j) / b2) % B20) + (((p3 * vecAtNat qs3 j) / b3) % B20)) % 101
  | [], [], [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | q1 :: qs1, q2 :: qs2, q3 :: qs3, h, j, hj => by
    simp only [checkMulEqAddInner, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => exact h.1
    | succ j' => exact checkMulEqAddInner_sound qs1 qs2 qs3 h.2 j' (Nat.lt_of_succ_lt_succ hj)
  | [], _ :: _, _, h, _, _ => by simp [checkMulEqAddInner] at h
  | [], [], _ :: _, h, _, _ => by simp [checkMulEqAddInner] at h
  | _ :: _, [], _, h, _, _ => by simp [checkMulEqAddInner] at h
  | _ :: _, _ :: _, [], h, _, _ => by simp [checkMulEqAddInner] at h

theorem checkMulEqAddGo_sound {b1 b2 b3 : Nat} {Bcols Dcols Fcols : List Nat} :
    ∀ (ps1 ps2 ps3 : List Nat),
      checkMulEqAddGo b1 b2 b3 Bcols Dcols Fcols ps1 ps2 ps3 = true →
      ∀ i j, i < ps1.length → j < Bcols.length →
        (((vecAtNat ps1 i * vecAtNat Bcols j) / b1) % B20) % 101 =
        ((((vecAtNat ps2 i * vecAtNat Dcols j) / b2) % B20) +
         (((vecAtNat ps3 i * vecAtNat Fcols j) / b3) % B20)) % 101
  | [], [], [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | p1 :: ps1, p2 :: ps2, p3 :: ps3, h, i, j, hi, hj => by
    simp only [checkMulEqAddGo, Bool.and_eq_true] at h
    cases i with
    | zero => exact checkMulEqAddInner_sound Bcols Dcols Fcols h.1 j hj
    | succ i' => exact checkMulEqAddGo_sound ps1 ps2 ps3 h.2 i' j (Nat.lt_of_succ_lt_succ hi) hj
  | [], _ :: _, _, h, _, _, _, _ => by simp [checkMulEqAddGo] at h
  | [], [], _ :: _, h, _, _, _, _ => by simp [checkMulEqAddGo] at h
  | _ :: _, [], _, h, _, _, _, _ => by simp [checkMulEqAddGo] at h
  | _ :: _, _ :: _, [], h, _, _, _, _ => by simp [checkMulEqAddGo] at h

theorem checkMulEqAdd_sound {m k1 k2 k3 n : Nat} {Arows Bcols Crows Dcols Erows Fcols : List Nat}
    (h : checkMulEqAdd m k1 k2 k3 n Arows Bcols Crows Dcols Erows Fcols = true) :
    MatEq m n (matMulF k1 (rowMat Arows) (colRevMat k1 Bcols))
              (matAdd (matMulF k2 (rowMat Crows) (colRevMat k2 Dcols))
                      (matMulF k3 (rowMat Erows) (colRevMat k3 Fcols))) := by
  simp only [checkMulEqAdd, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨hk1a, hk1b⟩, ⟨hk2a, hk2b⟩⟩, ⟨hk3a, hk3b⟩⟩,
                  ⟨⟨⟨hvA, hvB⟩, ⟨hvC, hvD⟩⟩, ⟨hvE, hvF⟩⟩⟩, hgo⟩
  have hlenA := allRowsValid_len hvA
  have hlenB := allRowsValid_len hvB
  intro i j hi hj
  have hcell := checkMulEqAddGo_sound Arows Crows Erows hgo i j (by omega) (by omega)
  have hd1 := packed_dot_sound k1 (vecAtNat Arows i) (vecAtNat Bcols j)
    (of_decide_eq_true hk1a) (of_decide_eq_true hk1b)
    (allRowsValid_at hvA i hi) (allRowsValid_at hvB j hj)
  have hd2 := packed_dot_sound k2 (vecAtNat Crows i) (vecAtNat Dcols j)
    (of_decide_eq_true hk2a) (of_decide_eq_true hk2b)
    (allRowsValid_at hvC i hi) (allRowsValid_at hvD j hj)
  have hd3 := packed_dot_sound k3 (vecAtNat Erows i) (vecAtNat Fcols j)
    (of_decide_eq_true hk3a) (of_decide_eq_true hk3b)
    (allRowsValid_at hvE i hi) (allRowsValid_at hvF j hj)
  unfold matAdd matMulF rowMat colRevMat
  rw [sumR_ofMod101_mul, sumR_ofMod101_mul, sumR_ofMod101_mul, ← hd1, ← hd2, ← hd3, ← ofMod101_add]
  exact Fin.ext hcell

-- ============================================================================
-- Section 4: Concrete `F_101` `(M=2, N=6, K=3, T=3, D=20, y=7, z=3)` Scheme
-- ============================================================================

def f101G (n k : Nat) : Nat := ((n + 1) ^ k) % 101

def f101P_rows : List (List Nat) := [
  [0x260000e00062000150005800002000350004b0000100046000010005400014000210002e0002f000030005a000160002d, 0x540002c0000a000320004f0001b000200002f0000c0001e0004e000420004800000000430002d0004e0004f0002700018, 0x20004f000250003d00045000380005a000530005d00040000100004a0003c000260000000001000190004e0000700046, 0x7000430006100025000240002a0000d0003f0005e000110003c0000b0003b0004f0005600040000350001d0005400025, 0x390005a000060004a0004c00010000620001c0002a00012000480002c0001d00051000630002b00030000340001400060, 0x110001300059000570003e0005500028000500002500054000570003d0005c00002000230001e0002f000160004700018, 0x800057000390004f00044000060002f0000000013000330003b0004a000170003e0005a0002d0001c000250003d00043],
  [0x210004c000290005e000400002c0001b000570000f0003f0000600052000320005700053000620004b0004d0000f00036, 0x58000350001a0002400028000430001d000630005c000120005e000480005b000000000c000240001d000490000800049, 0x410002a000340000b0004100053000170003b00018000600003900038000000005c00061000050001d000360003c00042, 0x80001a000410001b0002a00016000010004b00061000270005c0002b000180005d000500002a00030000590000a0000c, 0x3e0002600003000190002600038000230005b00051000620001f0001a000400001b00037000200002a00060000630004f, 0x22000190004f000580004e000630004600006000270000d0000c00004000130004d000160002500059000020000300039, 0x440001d00055000450000b0001e000430000c000260004a000640003d0006000014000470003c00059000430002000056],
  [0x3200010000550005c000160005c00041000480004d0003f0004a0004c0004e000610003c0000000024000310000d0004a, 0x5000025000440001d0002e0004500046000390001300034000320005e000020004f0002d000460004600034000440002b, 0x2200010000390000b0004d000100004d00031000560001c00008000600006300045000620002b000450002c0005d0001f, 0x340000d0004a000550000c00054000330004a0004e00010000620002c000440006100063000180002e00054000470003b, 0x1f000610001e0003100018000510000b0004e00032000150003a0004b0003b00034000100003500002000140003400001, 0x5b000100005900023000640000a00020000140004400054000150000c0005600007000110000e00023000060005400034, 0x42000310004f0003900028000010004f0000e00014000000000b0001f0003f00011000390005f000640002d000470003a],
  [0x13000440003100049000060000100036000630004d0002f00000000100001b000400005d00053000620003d0005a00007, 0x5000017000460000b000620002f0005800047000350003c00055000190001f000260000f0004e000020004d0001b0002f, 0x2b00031000560001b000010002d00025000620003b0002e000500004c00052000290003f0003100023000040005b0005d, 0x1000230003400055000300002c000420002f000150004000058000310006100061000260001000053000520005000014, 0x63000060004d00016000440004d0000000013000370005d0003b00022000140005a000060002700054000090005400032, 0x90003800028000180004500044000240000e0001400029000260005f0000d00058000620000800042000190003f00008, 0x3c00056000610004000030000570005a0001800013000260000c000090000d0000a0001f000400004d0005f0001f0003a],
  [0x39000160003f0003700057000100001f0003a000090000100039000210000d000340005600014000310003f0000e00052, 0x440001b0001c00027000320002800054000590000500017000360004c0004100025000240003f0005600000000530001c, 0x330003b0003d00042000290000d0000d00001000440002100059000400001b0002f0001b00012000020003d0003c00062, 0x3d00010000270001700006000290004f000190005400048000290004a000470002b000200000c000180004b0002b00064, 0x3c000210003f00024000500003c00050000620002e0003a000280002c0004e0000f0005000060000380000b0004800031, 0x3800015000580004d00059000380001f00020000320002000042000300004500041000200003c0002b000050001b00026, 0xb000530002500044000510004f0001f0004a0002200024000350000d0004400050000150001f0005800037000100003a],
  [0xa0003e0005700044000130004f00022000240000f00000000360000000027000370005a0003400009000360006200047, 0x4400009000550002000052000450005f0005900044000150004c0001e0005c000460004f0000f00053000440003c00046, 0xd0000100013000470001900016000280001b0002800062000090001e000110001b0004b0004d0003b00016000270001f, 0x2e0005800030000590001b000130001500057000040005700042000340002d000420004d0005c000300004a0001900060, 0x36000280000e000420002e000170000400055000210003b000290002800059000240001c0000d0000200020000580003b, 0x5600054000520005000026000430002c0001e0003d00056000030000000039000250002f000060003a000390001e00017, 0x260001500005000150000b0002f00012000400002d0003b0005c000270005f0003f000130000c00014000490000800063]
]
def f101C_rows : List (List Nat) := [
  [0x3f000430004c0004800011000200004e0002d0005f000590003e0005c0005d000070000c0005c0001c000540004500042, 0x5c00031000420000800020000260006200046000570006200063000380003100053000210005d0005d0001a0004b00050, 0x5d000100003a000220001e000360001000001000580000500034000190004200023000640004400012000610002f00055],
  [0x3100029000050000b0004a0000500006000090002a0005400056000260003b00005000350002c00054000140000300001, 0x30000560002500003000240001c0000800013000170004900062000050001e0002f000600002f0005b0005b0001100045, 0x410004700022000140003e0001d000160002200014000070002400004000370000e000470001700041000590002700002],
  [0xf0003800013000440002e00060000390000800040000190003d0003a0003c0004c0004f0001700053000230004600003, 0x170003f0004c0005e00010000610004300023000350006000059000040002900034000210003200027000420002d0000d, 0x360004c00018000180004e000610003a0001f0003e0003c000040001b000140002e000520005900055000470005100035],
  [0x520002f0002f000590002d0005d0003d0001800045000590001d00027000430001000044000440004900018000130005f, 0x300003c0003d00058000100001d00026000440005800015000070000e0000b00006000050001700043000460001700016, 0x5c0004c00006000370001d00047000510002500058000200000f0005e0000c0004b0005a000050005a0004e0004100030],
  [0x410002e0001900024000570000e000620000600013000400004c00053000400004700000000180002a000000005400001, 0x550002f000090002900045000450003600059000110001900028000300004e000550003a0000a0001f0005c000380000b, 0x1500013000230002e000260001e0005a0002f0003d0005d0003100036000480004b0000e0002500041000620005300046],
  [0x440005b0003a0000e0005b0004600024000430001f000160001a0003400045000250003c0005400011000330000400030, 0xc000140002d00007000220003a0004d000360000200034000020001b0004700057000100000c0004e0005c0001600054, 0x800020000070004d000490006000051000250002300044000640002100022000570006200040000290000c0002100013]
]
def f101Q_cols : List (List Nat) := [
  [0x43000370002e00020000300004600056, 0x13000640001c00014000570004900055, 0x5d000430003c000020000e0005500008, 0x4a0004400020000530001c0000c00018, 0x2700041000630004f00042000570001e, 0x52000030003200038000640002400026, 0x2b00027000340004e000220003200008, 0x35000340000e0003e000060001200039, 0x12000180000f0000d0004f0000e0003a, 0x42000490000100034000490006100001, 0x56000310005e00021000240003b00032, 0x56000310005e00021000240003b00032, 0x56000310005e00021000240003b00032, 0x570002a0001c0002300015000410002f, 0x570002a0001c0002300015000410002f, 0x570002a0001c0002300015000410002f, 0x17000410004b00055000360001600018, 0x17000410004b00055000360001600018, 0x17000410004b00055000360001600018, 0x0],
  [0xb0002a0002800041000610002000012, 0x570004e000350001b0004b0005e00030, 0x46000230004e0003c000110000700048, 0x5f0003d0002d0000c000250002a00035, 0x61000450002b0005b000280000d0004e, 0x500002f0002e00059000350000d00024, 0x4b0001400015000100002f0004b0003f, 0x3f0004c0002e0001e000140000e00050, 0x3e000430003a000220003b0000d00023, 0x4a000200002100031000260004700035, 0x5800009000170006400053000380003a, 0x4b000120002e00063000410000b0000f, 0x31000240005c000610001d000160001e, 0x20004400008000190005c0004d00064, 0x4000230001000032000530003500063, 0x8000460002000064000410000500061, 0x39000130006100013000140002300057, 0xd000260005d00026000280004600049, 0x1a0004c000550004c00050000270002d, 0x0],
  [0x8000600003000041000570004000021, 0x4a00053000370005c0003f0005100051, 0x1d0001b0000a00001000020001500037, 0x1b0002900028000540002d000290002a, 0x26000520001c000170005a0000000006, 0x610001d0002e0003c000140001d00061, 0x3200038000580004a0003a0005700023, 0x80003c00040000360002d0000d0005f, 0xf00044000480006000016000580005a, 0x4a000440002c00004000410002e00015, 0x160003a0002200061000310000f00046, 0x420004900001000590002e0002d00008, 0x61000110000300041000250002200018, 0x210003e000070000700000000600001d, 0x63000550001500015000000005600057, 0x5f000350003f0003f00000000380003b, 0x590002f0000e00064000360006100037, 0x41000280002a000620003d0005900040, 0x5e00013000190005c00052000410005b, 0x0],
  [0x31000010003e0005d00017000020003d, 0x210003b00039000510001b0004a0003d, 0x410002e000340000b0002f0003a00052, 0x2300030000030003d0003b0003a0003b, 0x420002700003000640004a0000d00035, 0x1c00045000110001100061000160001b, 0x420003800014000540000c0005200044, 0x1b0005700007000510004c0005500043, 0x12000120002900052000180001300052, 0x2c0005e000340002a0005c0001d00040, 0xc0001e000480003400052000190005e, 0x30000130005600006000190006400049, 0x5b0004c000290001800064000610005a, 0x14000330002600041000000001600001, 0x5000002000330003a000000005800004, 0x1100008000020001e000000003100010, 0x4b000550003800006000040003e0001e, 0x62000250001600018000100002e00013, 0x590002f000580006000040000530004c, 0x0],
  [0x1a00000000070001c0000c0003400060, 0x3000200001c00009000340004200035, 0x2e0000e0003d000590000a0004500013, 0x360004e00009000120003f0000800053, 0x3a0002e0001b0001400004000130005f, 0x1f0005e0004d0002d0002e0005a0002e, 0x120001b0000d0001c0001d0004c0004d, 0x100007000330002d000010001900048, 0x2b0002c0000c000520004c0000f0001c, 0x590002d000620005d000340003800039, 0x590005400023000570000c0004a00062, 0x29000100004a0001f0003c0004300056, 0x300050000430003600062000200001a, 0x1900031000420002a000110000b00042, 0x180002b0001b0000800055000370001b, 0x130000d0002200028000150004900022, 0x160005f0001100030000150005700025, 0x9000470005500026000040001f00054, 0x2d000340001500059000140003600010, 0x0],
  [0x2200060000270003e000090004700031, 0x5a0000b000060005100000000220002e, 0x60003c000120000200018000440000a, 0x1c000410005e000190002b0005d00014, 0x5d000090005700002000250004100027, 0x20003f0002200049000280003600043, 0x6200036000010003f000130000400008, 0x20000420005a000560005b000460002a, 0x270003b0005c00025000150001400013, 0x5c000630002700037000520001800010, 0x1c000140000a000220003d0000f00041, 0x43000130003c000020003f0005a00057, 0x630000d000390000c0004b0002300011, 0x2f0000b000120001b00040000630002e, 0x5000042000070003d00051000590004a, 0x4c0005d0002a0003f000520001d00028, 0x310001c00009000600000f0002000048, 0x5c0004300036000470005a0005b0001c, 0x2f000630001500016000230002900043, 0x0]
]
def f101D_cols : List (List Nat) := [
  [0x470002c0003d, 0x1c000040002b, 0x30001a00049, 0x4c000160001e, 0x2e000420005d, 0x4f0002f00029, 0x210005200031, 0x200004d0004c, 0x3b000480002c, 0x1b0006000045, 0xe0001f, 0xe0001f, 0xe0001f, 0x3a0002000030, 0x3a0002000030, 0x3a0002000030, 0x2a000000003e, 0x2a000000003e, 0x2a000000003e, 0x0],
  [0x3a0005c00044, 0x4b000380002e, 0x330004100033, 0x40000700013, 0x11000460001b, 0x380002f00027, 0x2c0001000047, 0x540001600031, 0x2f0001b0000a, 0x3d000430001a, 0x53000340000f, 0x41000030001e, 0x1d000060003c, 0x180001600043, 0x300002c00021, 0x600005800042, 0x5b0001400049, 0x51000280002d, 0x3d000500005a, 0x0],
  [0x260003f0005c, 0x530004100035, 0x3d0000d00061, 0x2a0003c00010, 0x360000600024, 0x380002200002, 0x560003000056, 0x1c0004e00014, 0x13000310002f, 0x7000330003e, 0xf0003300046, 0x2d0003400008, 0x220003700018, 0x430002c00005, 0x640001f0000f, 0x620005d0002d, 0x3d0003a00038, 0x520004900043, 0x2c0001100064, 0x0],
  [0x80002900061, 0x630002c0002a, 0x3c0003a0005c, 0x460002100064, 0x2d000470002b, 0x370005200013, 0x5000000005f, 0x390000b00045, 0x70005600049, 0x190004300061, 0x340004a00017, 0x60005e0005c, 0x180004900041, 0x46000390003f, 0x4e0001a00032, 0x90000300063, 0x290002e00042, 0x3f000530003e, 0x320001d0002e, 0x0],
  [0xb0000d0001c, 0x270001700045, 0x310002700039, 0x4e000180004b, 0x620004100060, 0xc0000c0003a, 0x22000330000b, 0x26000020001c, 0xe0000500016, 0x1d0004c00010, 0x22000030000f, 0x450000f0004b, 0x2a0004b00048, 0x240001e0004b, 0x4f0003100048, 0x5c0002b00039, 0x440002100024, 0x25000400004f, 0x54000110005c, 0x0],
  [0x5d0001e0003b, 0x5e0001100037, 0x5b0001700059, 0x5b0001f00045, 0xa0000e0000e, 0x120003300046, 0x330000400011, 0xe0005b00041, 0x4b0005800006, 0x2f0005000013, 0x5f0004f00062, 0x410004600053, 0x57000100005e, 0x1b0003700003, 0x3d0001b00012, 0x3f0003d00007, 0x4e0001400010, 0x400001300060, 0x510000d00047, 0x0]
]
def f101DecInv_rows : List Nat := [0x610004a00021000100005300025000300002700063000030000c0002d0005a000600002c000220000e0004b00033000000003f00050000260003d000570005a00048000200002f0003500008000070005f0004d000100005e00053000030002e00031000470001d0001c00019000190000a000600000b0003d0002a00054000420002d00044000430000100060000500002f0001d, 0x16000470005a0005c0000c000220000d000440001d000510000e0004500042000400002c0005500052000180004a00032000630002f000270005300052000110005e0003b0001c000070002c00004000560004b00012000600000800033000610000400016000470003a0000b000340005a000270005d000350003000036000160005000064000310000300008000570006200037, 0xe000280001f00038000140004d0004e0003e00014000470000f000450002e0002f000580000f00019000230003200007000560003300034000470003b0000c0005d000550003400029000020003c0002700024000600004f0001d0002a000230001100042000120006000006000560002b0000c0000c0004e0002c000330001a0004100033000320004400020000190004b0000d, 0x3e00023000500004000029000300002000011000020005e000010004a000420006000031000070004b0002d0004c00047000480000500031000100000e0002d00007000220005900047000500003b0006200020000600003c000410004e000430004c0001100028000630001100003000050005a000030001e000380002d000420003700040000070000c00055000590004d00029, 0x3d0001f0004100022000130001c000120002e0004e000340004d0000b00044000170002f0000b0004e0005500044000200002b0004f00015000430005a00008000050005b0003e0004e00026000320003400001000080004200035000350003d0006300060000190000e000100000f0004f0001a000440005200006000300000b0001d000360003d000620002a000180000300045, 0xb000360004a000180001800056000180000200015000520003900012000010002b0000600045000570002f0001e00025000160000b0000a0001f0004c000390003f000270005a000400003b0005e0003a00000000530004d000590004e000000000c0003900016000010001e0005b000280000c0003e000390001d000150005b0003f0004a0003c0002d0005f000060001600060, 0x120001400002000380003800012000570000000058000610000c000150003900050000060002a0001f0004c000050000300024000030005700054000270004a0003500005000450005a0003400052000320000e00052000140000600025000580004000035000540002000013000640004b0000b00006000480004e0002d0001600059000370006000039000350003a0006100042, 0x2a0005b00002000210001400047000330004d0004d00048000070003100019000630000300020000310000a0001d0001100033000580003a000430003c000450001700009000280004b0002a0000b0003b00004000500003b0002300015000340003d000600004f00044000570003e0003f00022000340000a00061000210003900050000020005e0000000006000040002300043, 0x540000800010000300000a000240001c000460004e0004c000230001100006000570006200021000440000f000410003a00064000230000f0001a00014000230002a000590001500063000080001300004000410002d00054000460002000062000580004f000270003900033000330002e00017000610001c0003f000110001100043000050003d0001a0004b000220001f00040, 0x59000280001b000190001c0000e0002400041000260006300025000370000c0001300037000340003f000480005000000000140005a0005c000440002400054000130001d0005200012000070002500045000000005100004000030004a000230005c0002a000540004d0002a0000200051000120002e000160000500044000340002a000620000000018000060004b0002b0001d, 0x5f0001d00022000370005f00036000640002a0003d0002500012000540002b0005c000640001c00043000000003e0004f0005d00014000130005a0003d000590005a000450004e0004600053000110000d00059000260004a000140005d0003200064000100002c000170001a0005d0003f000200002e000540001b000160000d000060003800002000210003b0000c0001800051, 0x2000120002b000180003e0002e0000c00061000560000f00030000540004f0000300055000010001e0002f000050003200025000480000400005000310004400015000320002e0003a0002e0004900034000030002a0006100046000140001e0000a0001e00006000290001c0001a00011000250001d000520004600034000010003200053000550005200048000020003800006, 0x2b0004000030000370004a0005f00031000590001f00042000100003a0004c0003200026000520001d000560001000027000230001f000500002c0003400044000160000f000070004f0004f0003300064000450003a000590004c000440001b000370004b0003b0006400057000270005a0001c0001f00010000530001c0000f000440000a0003500026000180003b000150002f, 0x4b00027000300001c00047000510003100012000610001d000600001900043000540003b0001c0005a00019000620003d00021000050001f0003e00040000090000d0000600045000190005d0000e00026000010004a00000000030001a000270000e00016000410001f0000800046000440003b000340002b000080003d000560002c000490002d000360000d000210003c0000a, 0x1b0005000030000490000c000220002f000490004400006000430000f0002600064000030002a0005d0003d0001100047000640000b0003d000440000b0003f000210005500034000170002300040000310001f0006100031000470005d0001100011000230005d000560003600009000390002c000070003f000380000e0001a000100000c0003c0002400020000290002500016, 0x210001a000030005b000040000600064000280004200014000000002d0005d000450004b0004b0001e00006000090000b00059000010005e00017000050005c000430000f00000000290000c0002200050000350001c000190002000059000270002c000590004d0001b00005000410000a00053000110001a00052000340004f0005800016000200006400016000450002b0001f, 0xa00024000120001400013000190004d00050000440000600009000100001a00015000100005e0002400037000190004f00002000630001500018000090001e0003e000170003a0001c0001300020000300001d0000c00036000550005b00011000370003f000020001d0001c000420001a0005b0001b000060000b00040000090001600063000170003a000330000f0001a00063, 0x4e000370005e00039000310000b000420004d000500005200020000080000f00007000290001d000300000a0004c000100003400001000190005100064000540002f00053000480003e000090004f00060000230001500037000590001f00012000320002f0002a000640002d00052000350000a0000b000310003b00038000290002f0005a000270005400062000270003d00001, 0x4d000430005b000160000f0003e000400003400002000170004d00049000020001000064000430000800038000020002d000100000e0001c0001f000320005f00016000530005d0003c0002d00057000170000400015000190005000033000530003e00039000060003d0002c000160000b0005500032000620003c00022000600005500028000490001800027000280002300004, 0x21000610000a00008000040004600040000160004e0005e0002e000130001400016000330003c00051000460005c00019000070003300063000530001c0006300050000160002d0005e000120002b00020000010001300017000440003100048000610003200045000120002800009000150005c000530005a000540003600048000610003b0001f0002700045000010004a00009, 0x290001a000480003c0001300041000270003200035000630003c0003900055000170003b0005b000260005500059000330001900050000270000500046000580005b0000c0000a00026000430001e0003a000610000200048000140004f0000b00020000570001d00031000100004c0002a0006100020000190003e0000600036000520004000047000290004b000640003300009, 0x2100030000340004d0004b000100004e000210001a0005b0001c0005d0005b00059000450000a000420001c00045000000002500009000170002b0000e000540004f0004e00057000070000f000610004300052000460004c0001d0005f000000005b00058000420005a0000200028000380005d0004d0004b0001200037000160005d0003500019000430004c0002a0005d0000f, 0x3c000590005a00028000180002a0004f00041000420002c00055000510005200021000320004300009000060002200035000280005e00045000130003f0000d000590002b00032000620000f00017000130000d0002a000580003b000300000200009000460000e000240000c0000b0003a00010000350004a0000b000390004e0000f000560000c000060001000060000460001f, 0x420003c000330002f00051000220000f0000a00020000590000b000410002f000070000a000120004e000320001a0000e000300005700058000020000b0001d0004900001000120004d0003000011000160001a0002600037000320000a000150001f0001e000280005300040000510005c000420004a0001500023000100003600008000220000a0004300033000140003b00015, 0x130003c000370002a0000b000190002f0005a00035000480005000032000050005b0004200037000180005a0003a0000e000350004e0002e0004b0004500063000260000f000270003a00039000020005f000590005b00053000210004800001000250003f0003e00050000220000e000330004d000160005d00003000310004d0006000018000610005d0004e0001c000560001f, 0x5d00051000320000e0005a0004c0004e0002f000640005a000200003a00040000640002c0006200049000270002d0004a00046000230001f0006300008000070001b0002000033000140003c000020003f000500001a000610004c0004600020000520001c00051000360003c000540004600024000550002b0003900057000560001c000560002a000170000900063000490002d, 0x2c0001100038000190002c000280005d0002b000140001600017000040001100057000020002b0000a0001f00022000490000800059000390001c00018000110005200057000020001c0004f00053000090002300032000360000d00016000560002600051000150001700020000120002e0004a000200003a0000f000100001b0002c0005200046000140000b000230004b00042, 0x260003c000380005600008000020003600058000010004a0001e0004b00062000560000d000450003c0005900064000460004e0001d000590000700057000570003800043000180000e00002000060003900028000520000f000610002c0001d0003200023000320002a000270003300033000540005d0003d0003a0003d000520004c0000a0005b000150004b00008000230002e, 0x4c000390004d00037000370005c00052000160001d0000b0005f0001200058000400004b0003b0005f0000a00055000330004000018000100001d0000a0004f000620004a0002a00018000450003100059000190003700034000400004b00014000010004d000370002c00034000240002d000500004c00016000030003c000400003e00009000630004a0001e000430004800026, 0x370003300001000600003c0001a00028000160005d0003e0002b0000800052000410004f0000a00005000220000d0005a00045000030002f0005a000250000600049000020003e0005100016000580005200030000300005100062000360001e00047000150002a0002800004000160001d0005e0004100016000550000b000580002b00030000450002f00028000640001f00021, 0x620004200047000300002b0001f0003a00061000090000e000020002e00025000530002d00047000160000a000270003b0001f000290002c000250004600028000070000c000570004000022000570002500003000400005600063000360002200011000260005d0002a00015000100000700023000590001d0004c00059000640004c0001a0003500027000380002e0003c00062, 0x60003f000580000f000110003a000110005b000580002800057000290001a0002300051000350004100052000180000a0000d00010000280003c000530002a0003c0002a0005d000490001d0003c00059000180000d0004200000000430000f000600004200001000280000b00042000480000000024000470005200014000350000d0001e000460002e00055000110000c00062, 0x1100025000040000a000000003b0002a000130005a0000b0002b000030004f000120000a0003f00025000000003b00003000550002100014000600001800031000540000f000030004f0003b00064000030005b0001c0005800006000570005d00001000320006000043000620003d000450004d000460000c000440000d000290003200004000310003f0005300022000320005e, 0x5c0000c00048000440000e0004c000130005f000090004400063000240005c0000a0000a0000a0005f000640003b00061000010005a0003700053000170003800037000170001000032000440001f000080000000056000140004d000030001c0000c0001b00025000530004f000550003a0005b00017000460006000016000590003d0003f0001d0002a00060000360001000010, 0x40000120001800023000310005f000220003200000000360005a000220002f0003e00005000350000e000410004200035000190002e00056000170005f0003b000480003b00047000430002e0003d000280004c0003b0004c00047000320003400043000480004b000630001d000040000f00001000440002c00026000540003f000610004300006000210000b0003c000030000a, 0x220003f0000f0000100025000000003d000010004c0002600022000110003a000210001b000080001400044000380003c000170004b0004d0000b000350001e00059000020000c000550000f00003000410003200009000250004c0000b0004e000160002a000160002700037000610003f000090000c0005400008000330004d0002d000020000d0003d00029000510001100051, 0x5900059000000004300011000060004a000250000c0003c000000003c00039000310002b000140001c00021000150005e0000d000510003200001000470005e0006400012000300002700019000520004e0001800009000630003b000020003e0005d0004f00023000000005a0005b0004b000130005c000420005f00004000200000b000090004000031000360000b0002f00060, 0x26000090005b000260000d000570003d0005c0003a0005c0003e00027000220000b000610004d000620002f0001800010000550001e00002000290005200024000230000e0005a000090004b0000d0000f000030003c000110004d000050002f0004a0002a000350001b0001600011000140004a0000900039000270004300057000620000a0003e0003c00003000110005b00057, 0xb0003c00042000100005100041000280003600031000250002c0000f0005400006000560000e00035000470004f0000f000060004f0005c00061000030005f0000a0001b0005900011000560002e000220000a0006400002000050001600052000250000d00007000510000a000490004e0000c00005000090004f00047000280005500052000170005b000320001a000130001f, 0x500002000046000010000c000620006300037000420001d0004e0002a0000e000600000b0003500048000060005a00064000510003e0002b000540000800055000590002f0004e0004e0003e0001a000460000f00005000240005300004000430000e00041000220005e0005400025000030005f0005f0001600001000240003a0003e000590001c000460000f000110003500022, 0x610004c0002a00063000300005a00023000100001a000210002e000600004c00047000010002a0006100040000200005e0002800036000410001f0000300007000480001800052000190003800047000100004300051000150000500004000060004a000120002e0002c00011000000000c0005c0001700009000510001d00016000370003f0005e00041000030004c000290000f, 0x420002200061000350004a0005a00039000040001a00018000420000b000530004d00058000140001a0005b0001f0004e00062000210004c000000000b000280002b00061000550004b000270000a000230003a0001d0003f0001d000000002d0003600011000220002c0001300022000250002e00036000010003200017000300000f000390001d000280000d0000b000360005f, 0x55000190005c000380002b0003b0005c0003a0005e000190001800029000400004700033000620002f0005d0002f00057000400002c0000200054000090001e000370000b00058000060005e0005200017000350002c00030000550001200026000380003d000250003d0004f0003e0002e00043000620002100050000140002000045000180003e0001400013000480005b0004e, 0x400001c0004e0002f000560000e000280005300020000350002a000060000c000210003500012000310000a0001b000000002300016000420005a0005200032000280001d0004700007000250002d000300005b0004a000380002b0004d000240000c0003b000510001300023000230000e0005e0004c0002d0004f0004f0001a0005200058000390001f0002f000380002b0005b, 0x110000c00013000300004b000210001a0001600028000210001f00053000630000e0004c00050000450002e00028000550000b00037000170004b0002600055000260000d00002000420004f0005600014000300003d0004b0001200058000390002400030000400002f0005a0005c0000b000080003d0003a0001c0002300048000020002e00006000070001d000320000b00033, 0x150001b000360005b000170001a0003a00022000280004a0003c000410000c00021000060001b000600001d00025000380002000060000510003400033000350005a0002d00059000380003b0002c00005000450002c0004f000560004a0000900015000020005a0000b0000400063000470002f0001800053000170003a0002b000430002e000600000800020000040001900053, 0x340004c0004b0002b0000a0003e0005f000170002900011000310005a0001d00016000350002d0005500054000390004a0003700047000590005b0004400058000290002c000260003c000340004500013000060003a0002800025000610002000045000330003b0003d0004c0005d000190005f00009000360002f0003a0004c0003800046000040005d0002e000470000800059, 0x4a000100000a000590002d0003c00059000540002c0001a0004400022000090005f00042000240004300058000590005a0003f0004200060000530005a0003c0004e0005b0002d000420002600036000020004c0004900023000120002700037000600005e0001c0004c000440004f0001f0001400033000200004d00001000530000f000050005d0005200011000520005f, 0x4f00043000090000d00054000510004100012000540004c000020005a0003c0000d000050000200025000480004a0004b0003b0003e00055000110002c0004a0001200024000550002200055000190005c0000f000280004b0004700044000170004200034000050005e0004500050000280002500025000590000100042000630006000042000230005800053000440000200064, 0x120002e000210005700033000280005e0001f000450000b00036000390001d00021000140004b0000a000060004000061000280000e000100004100013000190003c0004b0001b000110004300021000180002f0002800019000560005300046000630002c000380004e0002c000550000700019000550002a00026000520001a00059000410000f000450000900020000400003b, 0x310005900020000220003c0005100030000050005e000510000f000050003900013000620004500051000070004d0003b00059000410000e000490005a0000f000200002f0005300018000250002c0003e0002f000460003c0001f0004c00001000090001d0004f000430001a0001d000060000a00034000570003b00024000600004c0002300011000110003e000410002900048, 0x1b00037000440001b00005000220002a0005a000050001d00028000630001700056000200005400037000040000f000320000f0000e0003f0004e0004400044000290000d0003a00043000080003e0005d0002f00038000540000e0004b0004a0002e00020000590002d000430003500043000050000b000600005900041000200005e0004f00002000580005b00040000010003f, 0x2200009000470003e00064000390000f00048000410004d0001100059000240001e0000d00059000470002d000240000b00050000640004f0001a00032000530000e000490000c0004d0006400004000590005d000250004e000510005100011000100005e000230003c000530001500032000610004b00022000450004a000260005b0003a00049000080005a000250005d00012, 0x2700027000520005f00049000050005b000250002b00051000200005c000030000c0002d00020000380000e0003f0000b000150002400052000220005c0001400008000240005d00030000540000d0003300012000640003400045000180000900040000030001b000540001f0003c0002b0004700009000360004600058000290002e0005600038000310000100036000630002b, 0x1a0002d0001c00014000140002600014000450004400001000300003f0003600064000150005a000340000d000040004f00001000330001c000060001f000630002300059000320003a000210003800029000000002b0005b0006000053000000000500064000330003e0002a0005700038000250000600064000510002d0005e00022000480002a0005200010000550004c0002f, 0xf00054000450000d0000d0000f000160000000006000400002a00017000300004e000150002e0003a00040000440003d0001400045000520000d0005900056000070000e00048000320005900033000040005a000330002a0003500007000030005e0003600039000410004300027000040004c000450001400059000520004c00020000590002f000320001b000510004e0001a, 0x11000470003a0005500014000300002700026000490001100003000530001b00001000110003d00023000570004100040000480003500011000100003d000370001b0000e0004d00064000520000000039000440000400005000130000700044000130005c000390000100042000550002e0002300024000520002f000200001f0003d0005c0005f0003c000630002c0003200027, 0x230003b000450004e000540004c0005d00051000510003c0004b00014000250005e0003d0000b000140002300033000090003e00004000150001a000430004800018000050000b00008000440000d00021000450004300021000170002200059000110005e000320004b000290000600044000580005d0000e000370000d00032000380003e000560000000055000170004b00039, 0x460004a0002f000280002a0001e000390005c000410006100048000090001500034000280004100024000020004c000010004e000620002a0005d0003800062000390001b0004f00037000250003200045000560002c000230002e0002f0001800003000320005f000640001f0001f000180000c000370001300044000160001600039000360004900063000020002c0003400041, 0x5b000430004900004000390004f0001e0004700063000200004f000290002a00010000290005100045000320004e0000000038000320006000031000140000d000210003d000440000a0002d0000700036000000003b000450004d0000e00017000480004f000390001b0004f00017000490000500018000330000700058000610005a0000800000000250005500002000140005b]
def f101Des_cols : List Nat := [0x2d0001800046000250006000018000430004200050000550003600049000420000c0004f00039000560000100045000020004a0002b0001f0003b00001000340003a000030000d00035000070002f0005d0001400032000080003a0005f0001600030000520001c000620006400031000260003a000010000b0004600047000460001f000600003b0001700063000300005400013, 0x1600027000070005400014000470003d000450004b0002f0000f000080003c0000a0006300003000200000300011000270000d000440005d00047000340005400047000460002d000510005a0001b0005b00050000540003f0001f0001300017000410000e000530003c0002b000480001b00010000540003800053000620003c0002700019000580001e00008000040001600021, 0x5a0004f0004e0001d000340001600025000540001a000610004d000490003600059000600000200043000140005b0005900031000340002c0005400014000060002d0002300042000470003d0004d000040005200009000190005f00018000460004e0003f000000003d0004b0000b0000500037000000005c000620003600044000160004a000200003900049000330005c0000c, 0x30004e0001900035000300002f0001c0001c0005d000120004b0001d0001d000300002a0005900059000540005b000410002400046000450002e0000200023000640005300027000550006200002000230005300054000420004d00049000430005a00031000560000200018000380002b000580002a0001f0004100009000530003b00030000020003a00014000110004e00029, 0x2f0002d00001000400002b0001e0002d0005c0005d000440006200024000050002a00020000250003c0002c0002f0001700000000460002b00018000350000e0005f000170003200059000530004e0003100010000270000800040000440001700005000140003f000120000c000600003c0001f000180000a00025000340000f0004d0005c0000d000060000c000540000c00040, 0x2e00043000000005600063000230005a0000c0002100064000530000c00061000500003700016000470003500060000470003c0002d00062000630001000011000390004f00021000520005d0000f0003f0002600006000620001f00044000050005a00056000240001b00020000500002000015000000003a0000e0005a0004f0004b0004d0001c0002f000130003c0001000062, 0x2100000000260004f00051000020003e00007000530002300057000000005c0005d0001b0004d00014000050002f0000e000610004f00045000610003400007000110004c000340002e000400002600029000610005a000580000a00010000060004b00034000250002f0002b0000f000410005000047000550004b00037000460001b0004200024000250003f000250005700057, 0x14000480003c0003b0001d0005c000170005d0003100042000320005b00000000180004000013000600003b0001e000370004e0000200063000440003b000560003f0003c00029000140001b0001f0005200061000140000d0000d000430000b0000c0000d000410001b000470004e0004500044000400004e00048000270005c000110002d00059000390005f000450004700022, 0x54000420004a0000b0002c0003d0004a0005c00038000190005200048000380002b0001a000040003d0002600005000040004c0005e000600002c0004b0000c0001f0003a000040001b00010000190004c00031000220005f00009000270000e0005e000210004c000400004a0002c000300000d000530003000036000000001e0001e00034000280000000027000340001b00021, 0x10004e000100003c00048000570003b0003e0006300034000060005e000390005c0001f0000c000640005600062000240004a0003200008000620003a000150000b0003d0005900004000000005500050000580003b000260000c0001d000070000f000390003600059000290002800042000350004c0002800031000360004c000090004200029000030005c0001a0000200064, 0x460001e00040000110001200054000330005900062000050003f000120006000027000620000d0004a0005400049000070003f000340001c0001000015000540000000019000600003c0002f0003c0002e000400005d0002900026000590001500020000010001700021000480003a000200002400040000190005d000000001500062000570003b000560003b000160003400044, 0x10000c0005d0005e0002a00025000130005f00057000580000f0005c00018000610005100027000260002a00017000140004d00013000560004e00032000440001400040000350003e0004d000350003b00015000370001400013000450005800058000090000500044000540002e000320002200013000110003d0000f000440002800004000210003d0002d0001f0000200023, 0x4b0002f000530003f0001c00050000000002d000460000100057000630003b0004b0005b000060000c0000900013000220004800039000310004a0004e000140000e00008000230001f0006300047000620002f000130000e000180001800044000250003a00059000010001900062000200004a00006000590002f00024000590001b00057000550001e00040000430003600025, 0x35000200005a0000d00062000280002f0004e00062000100001b0001d000170000100023000460004300006000080001600041000460004d000330000b000200004f00039000430003a0003600058000250004200000000240005a0003d00026000510001f000540000d0004f000500001f0001f00062000360005a000220005f0002800015000040002c00012000240004d00051, 0x20001b000380002a0001000055000060002000026000360002c00043000530001600038000630001e000050001c0001d0005c000450001000054000510000a00001000600006100061000010002f0002d0002c0004d00044000570005d0001d0004700010000280000d000290003c000380004f0000e000450001e0004f00045000160001300017000430002f000460003a00060, 0x580004f00045000240004c0003e0004400011000200001e0004000028000410002a000260004e0000b0004a000240003e000160002e0004d0000c0001800064000280002e000100004e000060006200001000300004400045000300002d000100001d000570003200029000060005000059000510005700045000260001300052000190001b0002e000260000b0005b0002200049, 0x15000320003d000250004a000570004f0004800008000220005e000240000b0001b0001900058000450000b00003000140005c0001d0000b00055000310002300039000440005e00018000490000b0001b0005500016000180004000059000580003700037000270004200017000240004d0004400024000290002e000440002000047000590004200050000150000e000070004d, 0x620000a00025000610000600059000390004c000420003a000290001a0003400041000030004f000550000500025000220005500044000390004a0001e000590004f000130004c00018000310004600056000340004d00028000610002f0003d000060003f0001c0003d000270003f0005800025000190000900023000570005500013000300000e00052000050003a0002d00007, 0xe0002c0004f000430005a00013000570004300031000100004c000350002a0001a00026000190001d0002900056000470001000025000100000d000610001000031000380003f0004c000440001700031000230000600038000560002f0003c0004c000160001b0003b000100002100015000530002e0002f000130003e0000900001000580002800054000150005b0001400020, 0x260005400002000070003900011000080003f0005c0005d000210005800041000080003e0002200044000310003000041000320005000022000340001f0005b000420000f000170003600013000500002b0000100063000090003c00052000300005c0003900044000330003d0003c000380000b0004100055000150000a000440000d0002e000360005600026000440000c00008, 0x2d000180004600025000600001800043000420005000055000070002d0001f00018000390000d00047000020002500004000140001c0005d0004c00003000370004900009000270003a0001c00057000450005000063000200001e0004d000580005b000060002700056000600002b000590005800005000370002f0001600010000550004700033000250005900056000640000d, 0x1600027000070005400014000470003d000450004b0002f0001e00010000130001400061000060004000006000220004e00027000020004d0000b00037000320000b00008000220002900039000070003d000110002100032000170004c0005c0003a000460000b000620000d000390002200050000100004e0000b00053000390002000031000170004f00030000180001f00061, 0x5a0004f0004e0001d000340001600025000540001a00061000350002d000070004d0005b000040002100028000510004d0002e000370001f000320003c000120002200004000610000b0002a00005000100001900024000640004d000600004e000090000c00000000020004800037000190004900000000380005600015000040001f000280005b0002700022000030002f00048, 0x30004e0001900035000300002f0001c0001c0005d00012000310003a0003a00060000540004d0004d00043000510001d000070000800005000250000600004000620002f00010000350005900008000270001d000210003e000050005a00042000390002b0001a0000a000130004e0000d00024000080003600016000360005e00033000560000c0002d0001300001000400002c, 0x2f0002d00001000400002b0001e0002d0005c0005d000440005f000480000a00054000400004a00013000580005e0002e00000000080001c000480003a0002a000530004500031000410001d000090005f00040000370002000036000460005c00014000640000c0005a0003c0004c0006200036000130003200054000090005a0003a0002f0004e0002400048000640004800051, 0x2e00043000000005600063000230005a0000c000210006400041000180005d0003b000090002c00029000050005b000290004f000220005c0005f00030000330004600023000630002c000450003c00032000330001800059000170004600014000390001a0004f000220003b000610003b0000400000000580004600023000460002e0003a00043000500000d000390006000053, 0x2100000000260004f00051000020003e000070005300023000490000000053000550003600035000280000a0005e0001c000590002300005000590003700015000330001a000370002500036000330003f000550003900031000280004000018000620003a00054000210000d0004b00016000610003400015000480001b000100003d0005d0000e000140004b000140001100011, 0x14000480003c0003b0001d0005c000170005d0003100042000640005100000000300001b000260005b000110003c0000900020000060005f000020004c00038000580004f000160003c00007000170001900055000500003400034000420002c0003000041000160002200034000570002a00025000110005700039000200002f00001000440001d00027000410000a0001600002, 0x54000420004a0000b0002c0003d0004a0005c00038000190003f0002b0000b000560003400008000150004c0000a000080001a00050000560001f00017000240005d000490000c000510004000064000010005f000230004d00024000370003800049000400004d00011000430001200026000410000b0002600044000000004f0004f00009000260000000020000090003d00061, 0x10004e000100003c00048000570003b0003e00063000340000c000570000d000530003e0001800063000470005f000480001400031000180005c000490003f0002100052000410000c000000002500011000310002200033000300000f0001c0003c00053000440002900003000630001b0003f0004d000630002b0001500034000360005d0002c000120002f000370000c0005f, 0x460001e000400001100012000540003300059000620000500019000240005b0004e0005f0001a0002f000430002d0000e000580003700054000300003f00032000000004b000560004f00057000260005300036000450003f0003300035000540001b000050000e0004000039000580003b0004f00011000180003d00000000190005300011000330000b000330001f0000900004, 0x10000c0005d0005e0002a00025000130005f00057000580001e00053000300005d0003d0004e0004c000540002e000280001d00039000380002000031000020003c0005b0003a00055000050000a000220005400012000500004c0004a00031000310002d0001900025000100001c00030000450005f00055000020005a000040002600018000610003f00044000550000c00008, 0x4b0002f000530003f0001c00050000000002d000460000100049000610001100031000510000c000180001200026000440000e000460002e00014000200003c0002a00018000040005d0005d0005200059000570004c000380006000060000460002f00058000290000500018000560003b000430001e00029000210000e0001d0003d00011000050004f00051000630001500014, 0x35000200005a0000d00062000280002f0004e0006200010000360003a0002e000020004600027000210000c000100002c0005e000080001d000340002100060000230004600064000490000e000310002f0003e000000002b000390002a00033000150003600010000410005c00061000360003600056000440002e00002000410002600019000180003e000070000e0003a00052, 0x20001b000380002a0001000055000060002000026000360005800021000410002c0000b000610003c0000a000380003a0004a000050003000032000290001e0000300056000590005900004000570004f0004b00005000460002d000450000f0005200050000630004100003000620004e0005c000460002a00031000460000a0001f0000d000250006300050000100002d00047, 0x580004f00045000240004c0003e0004400011000200001e0001b000500001d000540004c00037000160002f000480001700042000250001d000240004800062000130002500030000200001800059000040005b000460004a0005b0004f000400000f0001f00030000030001e0006100029000010001f0002a000590000d00058000310003d0004a0001a00042000290000200022, 0x15000320003d000250004a000570004f00048000080002200057000480001600036000320004b000250001600006000280004a0005700021000350002e00004000460000200050000480005a0002c0000700025000580006000036000350003100012000490005e0001b0000e0004f00052000250004f000030001c000040005b000160001d0005d0004c00019000540002a0003a, 0x620000a00025000610000600059000390004c000420003a0005200034000030001d0000600039000450000a0004a00044000350000200046000140005a0004100023000390001a000480005f0004e0002900006000050003b00055000570002a000180000c00027000020005e0000c0002400054000180002d0004a00011000050000d0005600054000580001e0002d000440002a, 0xe0002c0004f000430005a0001300057000430003100010000330000500054000340004c000320003a000520004700029000300000a000300002700059000300002e00043000580001a000460005c0005f0002700018000160002900057000260000100009000220005d0005000040000040000b0001c000210005f0004500036000060001700026000640001900029000130005b, 0x260005400002000070003900011000080003f0005c0005d000420004b0001d0001000017000440002300062000600001d000310002600001000370005d00047000610002d000450003d0004c0001100047000040005d0002400026000190005b0004100053000250003500002000620004e000370001600015000040003c000040004e0004a000150000b0001a000040004800030, 0x2d0001800046000250006000018000430004200050000550000e0005a0003e000300000d0001a00029000040004a000080003c000540004d0001a0000900040000110001b00010000490000b0002d0004a000110005d0001b0001300005000310003d0001e0005e0001a0004c0000d00029000240001900049000210001f00060000050001600003000140001d0000b0005f0004e, 0x1600027000070005400014000470003d000450004b0002f0003c0002000026000280005d0000c0001b0000c000440003700010000060001d000210004000031000210001800001000160001a0001c0002a000440001f000630005c00001000410001e0002f0003700056000410005300045000610005000057000370005e000270005b0005c0002500046000560002b000550004d, 0x5a0004f0004e0001d000340001600025000540001a00061000050005a0000e00035000510000800042000500003d0003500025000400005d000310004f00036000010000c0005900021000430001400040000640002b00061000050005100009000240003c000000000a0003900049000180003e000000004e0001a0001900018000550002600029000200000200012000500001c, 0x30004e0001900035000300002f0001c0001c0005d00012000620000f0000f0005b000430003500035000210003d0003a00015000180000f0000a000120000c0005c00028000300003a0003500020000370000f0001f0002e00014000390003e0001a0000d0001d000320005f00057000410004f000280004400009000150003b000030000b00048000440000d00006000510003e, 0x2f0002d00001000400002b0001e0002d0005c0005d00044000590002b00014000430001b0002f000260004b000570005c0000000018000540000e00049000190002f000050002e0005e0000f000240004d00036000120001b0000e0004e0004100050000600003c0002e000620004d00056000440005f000300001000036000230002d00050000400000e0001c0005f0001c00052, 0x2e00043000000005600063000230005a0000c00021000640001d0003000055000110001200058000520000a000510005200023000010004a000530002b0003400008000040005f0001f0004a00026000630000200060000350005c0004e000500001a0001d0005c000450005d000510005d0001400000000240002f00008000100004a0002d000630004c0004e00027000470005e, 0x2100000000260004f00051000020003e0000700053000230002d00000000410004500007000050005000014000570003800041000040000f00041000400003f000340004e000400000a0000e0000200032000250001a0005f0003b000360006000059000580001000040000410004800009000510003a00004000390003d000600003f0003500054000130002e000130000100001, 0x14000480003c0003b0001d0005c000170005d0003100042000630003d0000000060000360004c00051000220001300012000600001200053000060001a000430003e00023000420004f0001c0005c00064000250001100006000060003e0004b0005b0001600009000450003a0001f0000800054000550001f000530005b0005000006000040004900020000570003c0001f0000c, 0x54000420004a0000b0002c0003d0004a0005c00038000190001900056000160004700003000100002a0003300014000100004e00026000380005d00045000070004d0001100024000290003600061000040004d00027000050002b00012000160005a000110005200055000200005a0005900016000370005900025000000004600046000360001a000000005b000360003f0004d, 0x10004e000100003c00048000570003b0003e000630003400018000490001a0004100017000300006100029000590002b0003c0002e000480004a0001100058000630002c0005e00024000000002f000440005f00023000020005b0003c0000b000260000b00025000030000f0005b000220000c000520005b0000d000190000900015000350003e00007000500001b0004800041, 0x460001e00040000110001200054000330005900062000050003200048000510003700059000340005e000210005a0001c0003e00040000320002b0005800031000000001700038000230002d000330001d0000e0004a00032000020000a000210000700019000460001100053000240005d0005c00055000130000200000000310005e00001000030004200003000550003600018, 0x10000c0005d0005e0002a00025000130005f00057000580003c000410006000055000150003700033000430005c00050000570004600043000600002e000060004f000470004900035000140002800023000210004800011000010005e0005f0005f0001700018000540005000027000260002a00047000150000a00023000180001a0002b0004d0004b00004000050004800030, 0x4b0002f000530003f0001c00050000000002d00046000010002d0005d00022000620003d0001800030000240004c000230002a00008000250003c000600004f00019000480000c0004d0004500019000350002d000010001600051000510004e00057000240000300019000130001a0005d0002000031000030004000054000490003f000010001e0004600052000590001900013, 0x35000200005a0000d00062000280002f0004e0006200010000070000f0005c00004000270004e0004200018000200005800050000180005700037000630005600004000080006200011000380005f000570002e00000000470001a000430000200054000440005000016000380005100044000440001a000250001c0000c000570001a000310002b000450002a000540002d00058, 0x20001b000380002a0001000055000060002000026000360004b000420001d00058000160005d00013000140000b0000f000140000f0002b00031000160005a00009000380004100041000100002d0000d00062000140004e0004f0004a0003c00019000610005b000160000f0005600057000380002f000080002b000100003c000550004e00014000590004c000600004400016, 0x580004f00045000240004c0003e0004400011000200001e000360003b0003a0004300033000090002c0005e0002b0002e000610000a00057000070000e0005c000390000a0002b000600006000035000100003d0004e0005e0003d0000d000360003c00036000260000f000310005100003000050003600008000290004e000170005c0003f00028000370005d0002c0000c00002, 0x15000320003d000250004a000570004f000480000800022000490002b0002c0000700064000310004a0002c0000c00050000140003b000630003a000250000c0000800006000260000e000390004b0001c0002f00031000510000e0000a0005f000480003e0004200022000460005c00006000540005c0000f0002700018000290001f0004900035000340003100064000320002d, 0x620000a00025000610000600059000390004c000420003a0003f00003000060003a0000c0000d00025000140002f000230003a00006000080003c000440005e00004000460004e0000e0004d000090003f000180001400022000250002d00043000600003c0005e0000a000420003c0004f00010000130001700043000010001e0004e0000b00064000170004f000440000400032, 0xe0002c0004f000430005a0001300057000430003100010000010000a000430000300033000640000f0003f00029000520002b0001e0002b00010000410002b00025000640003e0004e0004e000410004d0003700060000580003f0002d00033000040002d000450003d000610001100014000370002700040000470000a0001500024000250001a0005f000310002c0000d00029, 0x260005400002000070003900011000080003f0005c0005d0001f000310003a000200002e00023000460005f0005b0003a0002e0000d00003000400004d0000b0005900022000050005200001000440005200010000450002b00033000640003d0003a0000b000540003f0000a00056000570004900009000040001400039000180004000028000190004200037000180001c00056]
def f101Cancel_rows : List Nat := [0x3d0004e0005e0002c0003300002000000000c000420005c000490005900017000120003b0005f000290005d000530004e0000f0005b000270001e000180001d0001f0005d0004d000590004600060000520000a0001a0001b0002a000250004d000340004100022, 0x2500052000240001b0003b0004a0000d0005800017000400002b00042000250003c000360002e0003c000190001300061000510002f0000600059000320002500051000410000b0004d0005b000120002200032000380003a000270005e0001a000260005500050, 0x5700040000620003d000070004e000380001a00002000450004c000220001d0000e00030000380002a00020000330001c0004c0003000017000030003f00027000080005b0000000034000270005b00046000400001900015000280004e0001d0003f0004b0000b, 0x800037000510004e0001d000220003000052000100001d000210001a00054000330002800012000000002c00011000470002600032000560003400024000380001f0002500046000450005400030000510005c0000e000640005000033000360003d0003700057, 0x360004900012000190003c0004200054000420000200062000170002e0000a0002b0004a0001a000250000b000030004c0003300021000320003f000300004700038000380001600020000550000f0003b000360002e0002b0003e0001b0005b000570000c0002e, 0x5d000010000d000380001200022000510004300036000380002e0001b0002b00057000420003b0005f000100002e000510003f000380001e00004000530002b0003500002000170002c000090000800047000060003f0004e000290002e0001600001000480002d, 0x22000540004d0003c0001600026000480000d0000a000520000a000350005b0004300029000110004f0002d0003400007000600001d0002c00064000580005b000630004d00044000530000300017000150001a0002d00030000090003300037000110001900049, 0x1b000370003a000060005c000580002e000120003d0001d000240001e0002e000490001b00050000060001e00009000580003b0002c0005d00020000140005c0002e0000f0005c0001d0004a0003e0004f0005b0000e0001f000540002e000130000c0004d00032, 0x580003300017000430002300050000600005800033000090002c00014000410002f000360000b00036000040000c0003b0000f000280000e0001400048000110004f0004f00060000220005900009000500003a0000c00014000190002900046000520000000050, 0x30004500041000010005a000170002c0003400009000620001d00007000230004f0004c000480004800025000130003d0004d000120004e00063000350005d000150003d0000e00051000010004a00010000330002f0004100005000580004c000340003800002, 0x3b0002e00059000500004d00027000000001c0002e000090003f0000b000140005b000010004a0004400035000560000a0004c0002c0003a0002d00057000280005a0005c0004b0000700031000540005a0000f0001000008000360002f00041000350001c0002a, 0x1d0002c0004d000100003a000420001e00001000450004b000310004d0005f0000c0002c000070002b000030001d0004b000460000700060000430000b0000a00055000470004f0001c0004c000120003a000170003900057000390001b00046000070001700020, 0x4c000360003400022000200005c0004e0002a000280002000064000350001e000320003f000630000f0003a000020005c0002a00002000330003c0005a00019000520003c0000900029000320003c000200004f000250002500038000160001f0002c0004e0004e, 0x3000010005100014000630006400061000210001b0005c0004b000140003a0001600004000240001e00005000390005d000580002500015000030000e000380001d0004c000550005a0004100042000390003100053000050000a0005900004000520003b0005b, 0x580005c00009000620002a0003700050000380002e00060000190005f0000b000380005e00032000370005a0003e0000c0003a000610005f000620003100020000510000f0000e0002f00057000060002a000070005d0005b0001e0005c00056000050002e0002b, 0x32000550001700046000120002c0001a000060000300041000370005c00008000280001e000240004d00057000120002f0004e0002f0000d00063000380005a000440001300062000610001f00012000530003a00058000220005d0003b000500004c000000000e, 0x530006200003000200002b000490001d000120000c00032000470003700018000000005b0001e0005a000300005600028000230005300055000420004c00057000170001c00025000290000c0002b000100002d0001300044000310001e0003c00010000100003b, 0x2000057000160003e000370000a00025000310003f000140003f000160004e000390004c00020000030003a0003d000080005d000140003b000030005600062000030001f0002700031000520002100062000450000900029000630004c00022000080003e0002a]
def f101Pure_cols : List Nat := [0x43000370002e000200003000046000560000b0002a00028000410006100020000120000800060000300004100057000400002100031000010003e0005d00017000020003d0001a00000000070001c0000c00034000600002200060000270003e000090004700031, 0x13000640001c00014000570004900055000570004e000350001b0004b0005e000300004a00053000370005c0003f0005100051000210003b00039000510001b0004a0003d00003000200001c000090003400042000350005a0000b000060005100000000220002e, 0x5d000430003c000020000e000550000800046000230004e0003c0001100007000480001d0001b0000a00001000020001500037000410002e000340000b0002f0003a000520002e0000e0003d000590000a0004500013000060003c000120000200018000440000a, 0x4a0004400020000530001c0000c000180005f0003d0002d0000c000250002a000350001b0002900028000540002d000290002a0002300030000030003d0003b0003a0003b000360004e00009000120003f00008000530001c000410005e000190002b0005d00014, 0x2700041000630004f00042000570001e00061000450002b0005b000280000d0004e00026000520001c000170005a0000000006000420002700003000640004a0000d000350003a0002e0001b0001400004000130005f0005d000090005700002000250004100027, 0x52000030003200038000640002400026000500002f0002e00059000350000d00024000610001d0002e0003c000140001d000610001c00045000110001100061000160001b0001f0005e0004d0002d0002e0005a0002e000020003f0002200049000280003600043, 0x2b00027000340004e0002200032000080004b0001400015000100002f0004b0003f0003200038000580004a0003a0005700023000420003800014000540000c0005200044000120001b0000d0001c0001d0004c0004d0006200036000010003f000130000400008, 0x35000340000e0003e0000600012000390003f0004c0002e0001e000140000e00050000080003c00040000360002d0000d0005f0001b0005700007000510004c00055000430000100007000330002d00001000190004800020000420005a000560005b000460002a, 0x12000180000f0000d0004f0000e0003a0003e000430003a000220003b0000d000230000f00044000480006000016000580005a000120001200029000520001800013000520002b0002c0000c000520004c0000f0001c000270003b0005c00025000150001400013, 0x420004900001000340004900061000010004a0002000021000310002600047000350004a000440002c00004000410002e000150002c0005e000340002a0005c0001d00040000590002d000620005d0003400038000390005c000630002700037000520001800010, 0x56000310005e00021000240003b000320005800009000170006400053000380003a000160003a0002200061000310000f000460000c0001e000480003400052000190005e000590005400023000570000c0004a000620001c000140000a000220003d0000f00041, 0x56000310005e00021000240003b000320004b000120002e00063000410000b0000f000420004900001000590002e0002d000080003000013000560000600019000640004900029000100004a0001f0003c000430005600043000130003c000020003f0005a00057, 0x56000310005e00021000240003b0003200031000240005c000610001d000160001e000610001100003000410002500022000180005b0004c000290001800064000610005a0000300050000430003600062000200001a000630000d000390000c0004b0002300011, 0x570002a0001c0002300015000410002f000020004400008000190005c0004d00064000210003e000070000700000000600001d000140003300026000410000000016000010001900031000420002a000110000b000420002f0000b000120001b00040000630002e, 0x570002a0001c0002300015000410002f00004000230001000032000530003500063000630005500015000150000000056000570005000002000330003a000000005800004000180002b0001b0000800055000370001b0005000042000070003d00051000590004a, 0x570002a0001c0002300015000410002f000080004600020000640004100005000610005f000350003f0003f00000000380003b0001100008000020001e000000003100010000130000d00022000280001500049000220004c0005d0002a0003f000520001d00028, 0x17000410004b0005500036000160001800039000130006100013000140002300057000590002f0000e000640003600061000370004b000550003800006000040003e0001e000160005f0001100030000150005700025000310001c00009000600000f0002000048, 0x17000410004b000550003600016000180000d000260005d0002600028000460004900041000280002a000620003d000590004000062000250001600018000100002e0001300009000470005500026000040001f000540005c0004300036000470005a0005b0001c, 0x17000410004b000550003600016000180001a0004c000550004c00050000270002d0005e00013000190005c00052000410005b000590002f000580006000040000530004c0002d0003400015000590001400036000100002f000630001500016000230002900043, 0x0, 0x43000370002e000200003000046000560001600054000500001d0005d000400002400018000560002b0005e0003b0005b000630005f000040002e000450005c000080002a0001d0000000023000270003c0003a0004c0000200047000200004500036000160005c, 0x13000640001c0001400057000490005500049000370000500036000310005700060000140002f000400004a0005800029000290001f000220001a00015000070005e0002a0000f0003b000270002d0003a0001b0003f0002300042000240005200000000020004a, 0x5d000430003c000020000e000550000800027000460003700013000220000e0002b00057000510001e00003000060003f000400003a00053000060002c000570001e000190001c000460000200029000320002a0005f0002400039000070000c0002b000040003c, 0x4a0004400020000530001c0000c0001800059000150005a000180004a000540000500051000160001300032000220001600019000270005b0000c0002a000220001e0002200044000570002d0005a0000c000280000b00043000570003b00031000380003500013, 0x2700041000630004f00042000570001e0005d000250005600051000500001a000370000d0002c00054000450004400000000120003e000370000c000610005e000340000a000580001c0002200064000140005f000470003500036000110000c000140005700020, 0x520000300032000380006400024000260003b0005e0005c0004d000050001a000480005900057000250004f0003c00057000590000b0004a0004400044000550005800007000360004200052000170001c0002e0001c0000c0004b0000200022000260001500063, 0x2b00027000340004e00022000320000800031000280002a000200005e000310001900031000430003e00014000490003b000040003e0001600050000210003000019000460005a0002200041000270002c0004d000520005300015000060004b0000d0001800030, 0x35000340000e0003e00006000120003900019000330005c0003c000280001c0003b000180004f0005b0003d000220002700053000070002d0001c00015000010002500042000050002300035000170000500018000390005b0005d000230000b000290001000032, 0x12000180000f0000d0004f0000e0003a00017000210000f00044000110001a000460002d000020000e00056000420003e0004400048000480003f00019000600004c000190000d000120003c000060004d0004b0002700020000330002f0001400019000130000d, 0x420004900001000340004900061000010002f0004000042000620004c000290000500014000020001f0000c0005e000250003f0004b000490000600043000410000f000360002900017000560003d0003a0004e000530002f00059000200001b000580002b00060, 0x56000310005e00021000240003b000320004b000120002e00063000410000b0000f000420004900001000590002e0002d000080003000013000560000600019000640004900029000100004a0001f0003c000430005600043000130003c000020003f0005a00057, 0x56000310005e00021000240003b0003200031000240005c000610001d000160001e000610001100003000410002500022000180005b0004c000290001800064000610005a0000300050000430003600062000200001a000630000d000390000c0004b0002300011, 0x56000310005e00021000240003b000320006200048000530005d0003a0002c0003c0005900033000090005e0000a00001000480003d000010003f000600006100055000390000f000610002000044000560003b0001d000590004e00027000480002e0000800001, 0x570002a0001c0002300015000410002f00004000230001000032000530003500063000630005500015000150000000056000570005000002000330003a000000005800004000180002b0001b0000800055000370001b0005000042000070003d00051000590004a, 0x570002a0001c0002300015000410002f000080004600020000640004100005000610005f000350003f0003f00000000380003b0001100008000020001e000000003100010000130000d00022000280001500049000220004c0005d0002a0003f000520001d00028, 0x570002a0001c0002300015000410002f000100002700040000630001d0000a0005d000530003a000580005800000000430004c00044000200000800013000000005f000400005f000410004500063000040003e000450003400035000320004b000580004900026, 0x17000410004b000550003600016000180000d000260005d0002600028000460004900041000280002a000620003d000590004000062000250001600018000100002e0001300009000470005500026000040001f000540005c0004300036000470005a0005b0001c, 0x17000410004b000550003600016000180001a0004c000550004c00050000270002d0005e00013000190005c00052000410005b000590002f000580006000040000530004c0002d0003400015000590001400036000100002f000630001500016000230002900043, 0x17000410004b00055000360001600018000340003300045000330003b0004e0005a00050000390004b0004a0002c0005e0004700035000570003100051000360001d00001000170003a00004000290006400044000500005000059000190001f000080002c00063, 0x0, 0x43000370002e000200003000046000560002c000430003b0003a000550001b0004800048000380001c000500004c000470005f0004d00010000530004a0004100020000430002c000000004a0005e00062000580004d0000c000160005b0000a000150001f0002f, 0x13000640001c000140005700049000550002d000090000a0000700062000490005b0003c000280005b000140003e0001600016000170002300003000540001c00049000430004b0005d0005e0001700058000220000c000080005d0000e00058000000000c00028, 0x5d000430003c000020000e00055000080004e000270000900026000440001c000560003b000290005a0000900012000580005b0001e0001d000180004b0002d0001300064000270002f0000a000030003000008000470000e000270002a00048000380001800039, 0x4a0004400020000530001c0000c000180004d0002a0004f000300002f000430000a0002900042000390003100001000420004b000370003d0003000043000230001300023000250001f000170002e0003c00063000370006300011000330005c000210000f0000d, 0x2700041000630004f00042000570001e000550004a000470003d0003b0003400009000270001f00032000050000200000000360002e000120003000055000490000600028000240002700045000600006400047000340000f00015000010004800013000110005b, 0x52000030003200038000640002400026000110005700053000350000a000340002b000410003b0000a000230004f0003b000410002c0005e000460004600025000310001c000440001b000060000e000270001c00027000480002e0000c000020001a0001900059, 0x2b00027000340004e000220003200008000620005000054000400005700062000320002e00064000550003c000110004c0000c0002e00058000110001f0005b000640004e0002e00045000160005e0001200052000060005e00019000240002e0004e0002b00056, 0x35000340000e0003e000060001200039000320000100053000130005000038000110004800023000470005200001000100002f0001c0004f0000b00054000040002f0003e000190004a0003f0000e000190001300053000290003500008000420002c0006000062, 0x12000180000f0000d0004f0000e0003a0002e000420001e0002300022000340002700022000060002a0003800061000550000200056000560003200064000510000100064000410005a000620001e00052000480005e0005b000030005000013000310000d0004e, 0x420004900001000340004900061000010005e0001b0001f0005f00033000520000a0003c000060005d00024000500000a00058000620005a00018000420003a0003c0000e000030000e0001a0000200058000570000b000500001d0005b0003d000170003800047, 0x56000310005e00021000240003b0003200031000240005c000610001d000160001e000610001100003000410002500022000180005b0004c000290001800064000610005a0000300050000430003600062000200001a000630000d000390000c0004b0002300011, 0x56000310005e00021000240003b000320006200048000530005d0003a0002c0003c0005900033000090005e0000a00001000480003d000010003f000600006100055000390000f000610002000044000560003b0001d000590004e00027000480002e0000800001, 0x56000310005e00021000240003b000320005f0002b00041000550000f000580001300041000340001b000500001e000030000e0002a00004000320005100055000250001a0004b000510003b000250001a0005d0002c0001d00040000200001c0004a0003000006, 0x570002a0001c0002300015000410002f000080004600020000640004100005000610005f000350003f0003f00000000380003b0001100008000020001e000000003100010000130000d00022000280001500049000220004c0005d0002a0003f000520001d00028, 0x570002a0001c0002300015000410002f000100002700040000630001d0000a0005d000530003a000580005800000000430004c00044000200000800013000000005f000400005f000410004500063000040003e000450003400035000320004b000580004900026, 0x570002a0001c0002300015000410002f000200004e0001b000610003a00014000550002f000490003e0003e00000000640001a000460001b000200004c000000004d0003600047000160002a0005b00014000070002a000090000f000620002e00017000220001a, 0x17000410004b000550003600016000180001a0004c000550004c00050000270002d0005e00013000190005c00052000410005b000590002f000580006000040000530004c0002d0003400015000590001400036000100002f000630001500016000230002900043, 0x17000410004b00055000360001600018000340003300045000330003b0004e0005a00050000390004b0004a0002c0005e0004700035000570003100051000360001d00001000170003a00004000290006400044000500005000059000190001f000080002c00063, 0x17000410004b000550003600016000180000300001000250000100011000370004f000260004600017000140001f000500000b0000a0002d0005f000150000e0000f000040000e0005800014000030006000025000610004c0001d0003100055000300003e00059, 0x0]
def f101Mixed_rows : List Nat := [0x2a0002a0002a0003a0003a0003a0000000000000000001b0003b00020000210004f0002e0004c000030001c00047000000002a0002a0002a0003a0003a0003a0000000000000000001b0003b00020000210004f0002e0004c000030001c00047000000002a0002a0002a0003a0003a0003a0000000000000000001b0003b00020000210004f0002e0004c000030001c00047, 0x2000020000200000e0000e0000e00060000480004d000520002f00042000160001a000040002c000000000000000000000002000020000200000e0000e0000e00060000480004d000520002f00042000160001a000040002c000000000000000000000002000020000200000e0000e0000e00060000480004d000520002f00042000160001a000040002c, 0x3e0003e0003e0003000030000300001f0001f0001f000450002c0004c00031000290005d0001e000490002b0003d000000003e0003e0003e0003000030000300001f0001f0001f000450002c0004c00031000290005d0001e000490002b0003d000000003e0003e0003e0003000030000300001f0001f0001f000450002c0004c00031000290005d0001e000490002b0003d, 0x2a000150003d000510005b000600000f0003a0001d0002a00057000210004b00016000440001000002000620001e00000000150003d000510005b00060000300003a0001d00041000150005e00043000580000b000220000800001000310000f000000003d000510005b0006000030000180001d00041000530003d0002f000540002c000380001100004000330004b0003a, 0x110003b00050000310004b00058000180000c0000600042000070005800040000570004e0001c0003a0001600041000000003b00050000280004b000580002c0000c000060000300021000360002c000200005e000270000e0001d0000b0005300000000500002800014000580002c00016000060000300034000430001b00016000100002f000460000700041000380005c, 0x390004f0005a0003e0001f0004200026000130003c00003000280005f0005200037000070004c000020005300046000000004f0005a0002d0001f0004200021000130003c0001e000340001400062000290004e0003600026000010005c00023000000005a0002d000490004200021000430003c0001e0000f0001a0000a0003100047000270001b00013000330002e00044, 0x5d0001f0002c0004a0005c000620000300001000220003f00046000320004300064000520004b0002c0002800027000000001f0002c000520005c000620006400001000220002d00015000390005400038000430003d00019000520002f0000d000000002c000520003d000620006400043000220002d0000f00007000130001c0005600038000360002a0003d0005300026, 0x3400033000110001d0004d0005d0005b00040000370003700025000600001c00003000360002300010000500003e000000003300011000490004d0005d0001f000400003700034000340002e000200002b00001000120004f000270005e000580000000011000490003a0005d0001f0002c00037000340003300033000310004e0003000022000060003c0000d000410003f, 0x5c000620006400001000220002d0000e000480001800035000130004f0004300012000150002b00041000490001400000000620006400043000220002d0000f00048000180000800055000280003c00038000060000700030000590003a0004a000000006400043000380002d0000f000050001800008000460003e0002f000140005600002000240001000061000350005c, 0x5d00063000320002b0002400009000510006000018000610000b0000300050000480000d0000900033000450001b0000000063000320003f00024000090004e000600001800006000640001c0001a00014000120004f0004e000260005d0002000000000320003f00029000090004e0004600018000060003400019000070003900005000370002d000460003c0006300008, 0x3c0000f0001d000300000c00003000390005a000490003e0003f0004b00000000640001900017000130006200032000000000f0001d000530000c000030001a0005a000490005e00042000290002c0000000019000520001f0001e0004b0003f000000001d000530002e000030001a00039000490005e0004a00043000560000b000000005200047000210003a0002c00029, 0x1d000530002e000450005d000630001e0003a0004100025000390005e000050000100052000550003a000420002500000000530002e0003e0005d00063000320003a000410005c000550005a0004a0004d0004c0004700061000410004300055000000002e0003e0004200063000320003f000410005c000170006100049000450005f000130002b000640005c0002a00061, 0x5000010000540004e000380005c00028000080002a000120002f000290002a000620001a0001f0000d000420004900000000100005400025000380005c0004f000080002a000450002c0004600059000450003c00056000570002b0005e00037000000005400025000440005c0004f000240002a00045000220001d0000e00026000220000c000620004e00031000270000b, 0x150005500011000410000d0002b00039000480004b0005200018000320003f00062000090005f000420004600016000000005500011000400000d0002b00031000480004b0000f0004d000190000a000350003c00016000130005e0000e00041000000001100040000210002b000310001e0004b0000f000030004c0000500002000330000c000410001800027000170000d, 0x4e000380005c0000b0005300039000530003900048000610002d0005e00049000240004d000390000b000080005e00000000380005c0004f00053000390004800039000480004b00050000090002700037000580004c00048000530002a00027000000005c0004f0002400039000480004b000480004b0000f00010000160001c0000b0003a000600004b00039000450001c, 0x5800052000510002e0004b0003f0000100011000570004c0004a00064000120002a000390002c0002c000330000f000000005200051000400004b0003f0003d000110005700041000500002e0005400003000070003c00029000290003b000350000000051000400004e0003f0003d0001b00057000410005f0002f0004b0000e00033000120000a0005b0005b0005e0005d, 0x400004e0000d0004b0003f0003d00047000600001000034000250002c0002b000120006400005000140000600046000000004e0000d000130003f0003d0001b0006000010000460004c00017000290001800003000540005500025000010004f000000000d00013000140003d0001b0003700010000460004f00050000580005b00004000330000e0001f00017000110001e, 0x1f0001600047000320002a00007000330003b0005e0004e0000e000110000600060000640003c000490003d00003000000001600047000600002a00007000120003b0005e000530000d00024000570000100010000540000a0001d0001b00033000000004700060000100000700012000030005e000530006200013000060004100011000460000e0004500059000370003b]

/-- Concrete `F_101` `(N=6, K=3, D=20, y=7, z=3)` linear MDS-coded PIR scheme (`rate = 60/102 = 10/17`). -/
def f101Scheme : PIRScheme (Fin 101) where
  N := 6
  K := 3
  D := 20
  y := 7
  z := 3
  g n k := ofMod101 (f101G n k)
  P n := rowMat (vecAtList f101P_rows n)
  Q n := colRevMat 7 (vecAtList f101Q_cols n)
  C n := rowMat (vecAtList f101C_rows n)
  Dblk n := colRevMat 3 (vecAtList f101D_cols n)

def f101CancelMat : Nat → Nat → Fin 101 := rowMat f101Cancel_rows
def f101DecInvMat : Nat → Nat → Fin 101 := rowMat f101DecInv_rows

private def desiredEntryNat (row col : Nat) : Nat :=
  let n := row / 10
  let t := row % 10
  let k := col / 20
  let d := col % 20
  if t < 7 then (f101G n k * unpackEntry (vecAtNat (vecAtList f101P_rows n) t) d) % 101
  else (f101G n k * unpackEntry (vecAtNat (vecAtList f101C_rows n) (t - 7)) d) % 101

private def pureEntryNat (row col : Nat) : Nat :=
  let n := row / 7
  let i := row % 7
  let k := col / 20
  let d := col % 20
  (f101G n k * unpackColRev 7 (vecAtNat (vecAtList f101Q_cols n) d) i) % 101

private def mixedEntryNat (row col : Nat) : Nat :=
  let n := row / 3
  let i := row % 3
  let k := col / 20
  let d := col % 20
  (f101G n k * unpackColRev 3 (vecAtNat (vecAtList f101D_cols n) d) i) % 101

private theorem check_des_match :
    (f101Des_cols.length == 60) && checkColsAgainstMat 60 desiredEntryNat 0 f101Des_cols = true := by decide

private theorem check_pure_match :
    (f101Pure_cols.length == 60) && checkColsAgainstMat 42 pureEntryNat 0 f101Pure_cols = true := by decide

private theorem check_mixed_match :
    (f101Mixed_rows.length == 18) && checkRowsAgainstMat 60 mixedEntryNat 0 f101Mixed_rows = true := by decide

private theorem check_dec_inv_ok :
    checkMulId 60 60 f101DecInv_rows f101Des_cols = true := by decide

private theorem check_cancel_ok :
    checkMulEqRow 18 42 60 f101Cancel_rows f101Pure_cols f101Mixed_rows = true := by decide

theorem f101_desired_eq :
    MatEq 60 60 (colRevMat 60 f101Des_cols) (desiredMat f101Scheme) := by
  have h := check_des_match
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  intro r c hr hc
  have hm := checkColsAgainstMat_sound 60 desiredEntryNat 0 f101Des_cols h.2 r c hr (by omega)
  rw [Nat.zero_add] at hm
  unfold colRevMat desiredMat f101Scheme rowMat
  dsimp only
  unfold desiredEntryNat at hm
  dsimp only at hm
  by_cases ht : r % 10 < 7
  · simp only [ht, ↓reduceIte] at hm ⊢
    rw [← ofMod101_mul]
    apply Fin.ext
    change unpackColRev 60 (vecAtNat f101Des_cols c) r % 101 = _ % 101
    rw [hm, Nat.mod_mod]
  · simp only [ht, ↓reduceIte] at hm ⊢
    rw [← ofMod101_mul]
    apply Fin.ext
    change unpackColRev 60 (vecAtNat f101Des_cols c) r % 101 = _ % 101
    rw [hm, Nat.mod_mod]

theorem f101_pure_eq :
    MatEq 42 60 (colRevMat 42 f101Pure_cols) (pureIntMat f101Scheme) := by
  have h := check_pure_match
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  intro r c hr hc
  have hm := checkColsAgainstMat_sound 42 pureEntryNat 0 f101Pure_cols h.2 r c hr (by omega)
  rw [Nat.zero_add] at hm
  unfold pureIntMat f101Scheme
  unfold colRevMat
  dsimp only
  unfold pureEntryNat at hm
  dsimp only at hm
  rw [← ofMod101_mul]
  apply Fin.ext
  change unpackColRev 42 (vecAtNat f101Pure_cols c) r % 101 = _ % 101
  rw [hm, Nat.mod_mod]

theorem f101_mixed_eq :
    MatEq 18 60 (rowMat f101Mixed_rows) (mixedIntMat f101Scheme) := by
  have h := check_mixed_match
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  intro r c hr hc
  have hm := checkRowsAgainstMat_sound 60 mixedEntryNat 0 f101Mixed_rows h.2 r c (by omega) hc
  rw [Nat.zero_add] at hm
  unfold rowMat mixedIntMat f101Scheme colRevMat
  dsimp only
  unfold mixedEntryNat at hm
  dsimp only at hm
  rw [← ofMod101_mul]
  apply Fin.ext
  change unpackEntry (vecAtNat f101Mixed_rows r) c % 101 = _ % 101
  rw [hm, Nat.mod_mod]

theorem f101_dec_cert :
    MatEq (f101Scheme.K * f101Scheme.D) (f101Scheme.K * f101Scheme.D)
      (matMulF (f101Scheme.N * (f101Scheme.y + f101Scheme.z)) f101DecInvMat (desiredMat f101Scheme))
      matIdF := by
  have hmul := checkMulId_sound check_dec_inv_ok
  intro i j hi hj
  change matMulF 60 (rowMat f101DecInv_rows) (desiredMat f101Scheme) i j = matIdF i j
  rw [matMulF_congr (fun _ _ => rfl) (fun t ht => (f101_desired_eq t j ht hj).symm)]
  exact hmul i j hi hj

theorem f101_cancel_cert :
    MatEq (f101Scheme.N * f101Scheme.z) (f101Scheme.K * f101Scheme.D)
      (matMulF (f101Scheme.N * f101Scheme.y) f101CancelMat (pureIntMat f101Scheme))
      (mixedIntMat f101Scheme) := by
  have hmul := checkMulEqRow_sound check_cancel_ok
  intro i j hi hj
  change matMulF 42 (rowMat f101Cancel_rows) (pureIntMat f101Scheme) i j = mixedIntMat f101Scheme i j
  rw [matMulF_congr (fun _ _ => rfl) (fun t ht => (f101_pure_eq t j ht hj).symm)]
  rw [hmul i j hi hj]
  exact f101_mixed_eq i j hi hj

-- ============================================================================
-- Section 5: All `C(6, 3) = 20` Colluding-Triple Flag-Isomorphism Certificates
-- ============================================================================

structure PackedBlkCert where
  srv      : Nat
  α_rows   : List Nat
  α_cols   : List Nat
  αi_rows  : List Nat
  αi_cols  : List Nat
  γ_rows   : List Nat
  γ_cols   : List Nat
  γi_rows  : List Nat
  γi_cols  : List Nat
  β_rows   : List Nat

structure PackedTripleCert where
  n0        : Nat
  n1        : Nat
  n2        : Nat
  M_rows    : List Nat
  M_cols    : List Nat
  Minv_rows : List Nat
  Minv_cols : List Nat
  b0        : PackedBlkCert
  b1        : PackedBlkCert
  b2        : PackedBlkCert

def checkBlkCert (M_cols : List Nat) (b : PackedBlkCert) : Bool :=
  (checkRowEqColRev 7 7 b.α_rows b.α_cols && checkRowEqColRev 7 7 b.αi_rows b.αi_cols) &&
  (checkMulId 7 7 b.α_rows b.αi_cols && checkMulId 7 7 b.αi_rows b.α_cols) &&
  (checkRowEqColRev 3 3 b.γ_rows b.γ_cols && checkRowEqColRev 3 3 b.γi_rows b.γi_cols) &&
  (checkMulId 3 3 b.γ_rows b.γi_cols && checkMulId 3 3 b.γi_rows b.γ_cols) &&
  checkMulEqMul 7 20 7 20 (vecAtList f101P_rows b.srv) M_cols b.α_rows (vecAtList f101Q_cols b.srv) &&
  checkMulEqAdd 3 20 3 7 20 (vecAtList f101C_rows b.srv) M_cols b.γ_rows (vecAtList f101D_cols b.srv) b.β_rows (vecAtList f101Q_cols b.srv)

def checkTripleCert (tc : PackedTripleCert) : Bool :=
  (checkRowEqColRev 20 20 tc.M_rows tc.M_cols && checkRowEqColRev 20 20 tc.Minv_rows tc.Minv_cols) &&
  (checkMulId 20 20 tc.M_rows tc.Minv_cols && checkMulId 20 20 tc.Minv_rows tc.M_cols) &&
  (checkBlkCert tc.M_cols tc.b0 && checkBlkCert tc.M_cols tc.b1 && checkBlkCert tc.M_cols tc.b2)

def blkCertToIso (tc : PackedTripleCert) : FlagIsoWitness (Fin 101) where
  M    := rowMat tc.M_rows
  Minv := rowMat tc.Minv_rows
  α    := fun n => if n = tc.n0 then rowMat tc.b0.α_rows else if n = tc.n1 then rowMat tc.b1.α_rows else rowMat tc.b2.α_rows
  αinv := fun n => if n = tc.n0 then rowMat tc.b0.αi_rows else if n = tc.n1 then rowMat tc.b1.αi_rows else rowMat tc.b2.αi_rows
  γ    := fun n => if n = tc.n0 then rowMat tc.b0.γ_rows else if n = tc.n1 then rowMat tc.b1.γ_rows else rowMat tc.b2.γ_rows
  γinv := fun n => if n = tc.n0 then rowMat tc.b0.γi_rows else if n = tc.n1 then rowMat tc.b1.γi_rows else rowMat tc.b2.γi_rows
  β    := fun n => if n = tc.n0 then rowMat tc.b0.β_rows else if n = tc.n1 then rowMat tc.b1.β_rows else rowMat tc.b2.β_rows

theorem checkBlkCert_sound {M_rows M_cols : List Nat} {b : PackedBlkCert}
    (hMeq : MatEq 20 20 (rowMat M_rows) (colRevMat 20 M_cols))
    (hb : checkBlkCert M_cols b = true) :
    IsMatInv 7 (rowMat b.α_rows) (rowMat b.αi_rows) ∧
    IsMatInv 3 (rowMat b.γ_rows) (rowMat b.γi_rows) ∧
    MatEq 7 20 (matMulF 20 (f101Scheme.P b.srv) (rowMat M_rows)) (matMulF 7 (rowMat b.α_rows) (f101Scheme.Q b.srv)) ∧
    MatEq 3 20 (matMulF 20 (f101Scheme.C b.srv) (rowMat M_rows))
      (matAdd (matMulF 3 (rowMat b.γ_rows) (f101Scheme.Dblk b.srv)) (matMulF 7 (rowMat b.β_rows) (f101Scheme.Q b.srv))) := by
  simp only [checkBlkCert, Bool.and_eq_true] at hb
  rcases hb with ⟨⟨⟨⟨⟨⟨hαeq, hαieq⟩, ⟨hα1, hα2⟩⟩, ⟨hγeq, hγieq⟩⟩, ⟨hγ1, hγ2⟩⟩, hPM⟩, hCM⟩
  have hαe := checkRowEqColRev_sound hαeq
  have hαie := checkRowEqColRev_sound hαieq
  have hγe := checkRowEqColRev_sound hγeq
  have hγie := checkRowEqColRev_sound hγieq
  have hαm1 := checkMulId_sound hα1
  have hαm2 := checkMulId_sound hα2
  have hγm1 := checkMulId_sound hγ1
  have hγm2 := checkMulId_sound hγ2
  have hPMs := checkMulEqMul_sound hPM
  have hCMs := checkMulEqAdd_sound hCM
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j hi hj
    rw [matMulF_congr (fun _ _ => rfl) (fun t ht => hαie t j ht hj)]
    exact hαm1 i j hi hj
  · intro i j hi hj
    rw [matMulF_congr (fun _ _ => rfl) (fun t ht => hαe t j ht hj)]
    exact hαm2 i j hi hj
  · intro i j hi hj
    rw [matMulF_congr (fun _ _ => rfl) (fun t ht => hγie t j ht hj)]
    exact hγm1 i j hi hj
  · intro i j hi hj
    rw [matMulF_congr (fun _ _ => rfl) (fun t ht => hγe t j ht hj)]
    exact hγm2 i j hi hj
  · intro i j hi hj
    unfold f101Scheme; dsimp only
    rw [matMulF_congr (fun _ _ => rfl) (fun t ht => hMeq t j ht hj)]
    exact hPMs i j hi hj
  · intro i j hi hj
    unfold f101Scheme; dsimp only
    rw [matMulF_congr (fun _ _ => rfl) (fun t ht => hMeq t j ht hj)]
    exact hCMs i j hi hj

theorem checkTripleCert_sound (tc : PackedTripleCert) (inI : Nat → Bool)
    (hs0 : tc.b0.srv = tc.n0) (hs1 : tc.b1.srv = tc.n1) (hs2 : tc.b2.srv = tc.n2)
    (hsub : ∀ n, n < 6 → inI n = true → n = tc.n0 ∨ n = tc.n1 ∨ n = tc.n2)
    (hdist01 : tc.n0 ≠ tc.n1) (hdist02 : tc.n0 ≠ tc.n2) (hdist12 : tc.n1 ≠ tc.n2)
    (hcert : checkTripleCert tc = true) :
    ValidFlagIso f101Scheme inI (blkCertToIso tc) := by
  simp only [checkTripleCert, Bool.and_eq_true] at hcert
  rcases hcert with ⟨⟨⟨hMeq, hMieq⟩, ⟨hM1, hM2⟩⟩, ⟨⟨hb0, hb1⟩, hb2⟩⟩
  have hMe := checkRowEqColRev_sound hMeq
  have hMie := checkRowEqColRev_sound hMieq
  have hMm1 := checkMulId_sound hM1
  have hMm2 := checkMulId_sound hM2
  have hb0s := checkBlkCert_sound hMe hb0
  have hb1s := checkBlkCert_sound hMe hb1
  have hb2s := checkBlkCert_sound hMe hb2
  rw [hs0] at hb0s; rw [hs1] at hb1s; rw [hs2] at hb2s
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j hi hj
    change matMulF 20 (rowMat tc.M_rows) (rowMat tc.Minv_rows) i j = matIdF i j
    rw [matMulF_congr (fun _ _ => rfl) (fun t ht => hMie t j ht hj)]
    exact hMm1 i j hi hj
  · intro i j hi hj
    change matMulF 20 (rowMat tc.Minv_rows) (rowMat tc.M_rows) i j = matIdF i j
    rw [matMulF_congr (fun _ _ => rfl) (fun t ht => hMe t j ht hj)]
    exact hMm2 i j hi hj
  · intro n hn hin
    rcases hsub n hn hin with rfl | rfl | rfl
    · simp only [blkCertToIso, ↓reduceIte]; exact hb0s
    · simp only [blkCertToIso, Ne.symm hdist01, ↓reduceIte]; exact hb1s
    · simp only [blkCertToIso, Ne.symm hdist02, Ne.symm hdist12, ↓reduceIte]; exact hb2s

private def tripleCert_0 : PackedTripleCert where
  n0 := 0
  n1 := 1
  n2 := 2
  M_rows := [0x1b0000d0004600032000530002b0004a0003f0000300033000640002e000010003d0004a00018000630004c0003c0002f, 0x10002c00038000530000d0005f00061000070000f0001d0002a000520000d0003e00063000420001400014000090000b, 0x1b000570002f0005d000290004800052000020001d0005d00052000000002100064000040004e0002f0005c0004200005, 0x2e00009000510001c0000c0002800062000250003e000250005f000500002c000460002b0003e00004000360002600030, 0x590005b000250000b0005500029000200000a000380001500043000360002b00058000590000500015000540004a0005c, 0x380001c000120005b0004e0002a000250003300039000420005c0005500011000190001e0001c000060002c000310000e, 0x54000190002d0004f0000000028000550005e00053000380005a0001400006000370002600044000530004e000380001a, 0x2c0001e0002700048000380001a000310003a0004b0001a0000000034000160004300017000280001a00042000450002b, 0x2e000110004300023000550003400016000340005900010000080000500038000510002700008000360003c0006200053, 0x1a0001a000560002400020000620001900030000620001500057000570000800017000570002a0003d000050000500015, 0x4300063000040002c0000100031000020004a0005b000510006200061000250002d000400002d00031000100002a00051, 0x5000340002f000170000300053000240003d0001e0001e000580003c0005b000470000a0003c000090003d0000b00001, 0x200062000280002c00043000500002a0004000025000640000b0005c0004700003000360005f00032000540001200011, 0x80001c00045000520003300057000320004e00039000140001d0006400037000480001c0002e0005300045000520004c, 0x3a0004c0001d0001d0003f0005e0005200014000320003f000010003e000290003a0002c0005f0006000041000280001c, 0x570005c000430000a00001000560005d0000100017000170003600025000480005600036000050000200025000450005d, 0x570006000059000470005a00031000430004f000230004e0005a0001c000280003c0000a000200002300015000360001d, 0x3c000490001b0001f0004d0000d0003300001000530005500019000620004f000590005000051000570002a000030005a, 0x1a0005a000620001f0003000040000210002500012000340001e000640001d0003600032000230005c000130001900052, 0x3f00050000250000900036000590005500001000310005c0001f00016000240004d000360001800005000290002d00006]
  M_cols := [0x2f0000b00005000300005c0000e0001a0002b00053000150005100001000110004c0001c0005d0001d0005a0005200006, 0x3c0000900042000260004a00031000380004500062000050002a0000b000120005200028000450003600003000190002d, 0x4c000140005c00036000540002c0004e000420003c00005000100003d00054000450004100025000150002a0001300029, 0x63000140002f000040001500006000530001a000360003d00031000090003200053000600000200023000570005c00005, 0x18000420004e0003e000050001c0004400028000080002a0002d0003c0005f0002e0005f0000500020000510002300018, 0x4a00063000040002b000590001e00026000170002700057000400000a000360001c0002c000360000a000500003200036, 0x3d0003e00064000460005800019000370004300051000170002d0004700003000480003a000560003c00059000360004d, 0x10000d000210002c0002b0001100006000160003800008000250005b00047000370002900048000280004f0001d00024, 0x2e000520000000050000360005500014000340000500057000610003c0005c000640003e000250001c000620006400016, 0x640002a000520005f000430005c0005a00000000080005700062000580000b0001d00001000360005a000190001e0001f, 0x330001d0005d000250001500042000380001a0001000015000510001e00064000140003f000170004e00055000340005c, 0x30000f0001d0003e0003800039000530004b00059000620005b0001e0002500039000320001700023000530001200031, 0x3f0000700002000250000a000330005e0003a00034000300004a0003d000400004e00014000010004f000010002500001, 0x4a00061000520006200020000250005500031000160001900002000240002a00032000520005d00043000330002100055, 0x2b0005f0004800028000290002a000280001a0003400062000310005300050000570005e00056000310000d0004000059, 0x530000d000290000c000550004e00000000380005500020000010000300043000330003f000010005a0004d0003000036, 0x32000530005d0001c0000b0005b0004f0004800023000240002c000170002c000520001d0000a000470001f0001f00009, 0x46000380002f0005100025000120002d000270004300056000040002f00028000450001d00043000590001b0006200025, 0xd0002c00057000090005b0001c000190001e000110001a0006300034000620001c0004c0005c00060000490005a00050, 0x1b000010001b0002e0005900038000540002c0002e0001a000430000500002000080003a00057000570003c0001a0003f]
  Minv_rows := [0x9000430000900034000610000f0001c00052000340004c0002d00045000210001f00035000480001d000510004c00050, 0x4d0001000008000210003e0004d0001d00062000480001a00019000580002500042000410003a0002a0002f0004900043, 0x11000470005f0004d000310002f0004e0001a0001c0004d000070002b000370004d000200003900064000490003e00038, 0x5400048000330001b000590001e0003f000540005700001000260004b0001200017000410004700040000530003d00011, 0xb0005000043000600001d000270001c0000a000160003200003000520004f00060000320005d0001d000510000f0000b, 0x380003f00017000130002c0002a0002f0002a000640000b000460000f0000c0001a000290001600030000610002e00061, 0x10004000054000120005f0001e0002c00032000510000f0002b0003a0000500034000330005a00028000110002900005, 0x130001b0002d000170000e0004700053000510005f000120001d00040000500003d0002a0000700034000450000f00004, 0x630005a0005d0000f0001d0002b000050003f00016000310003f0003d00047000110003d0005400032000550004c0003f, 0x35000630002a0005300012000310005b00046000330001a000380004b0006200048000620000400016000100003500035, 0x31000290004f0004400001000280004f0000e000220004400003000320001100037000520002f000550004d0004900024, 0x1c0005d0000e0003d00049000630003b000120000700016000330003d0005d000190001f00049000260002c000150001e, 0x4e000380004b00004000310004000061000400001500048000520003000044000270003c00008000470003c0002b00004, 0x12000280004300048000550001e0000a0000d00042000010005300058000450001700052000540003b00012000420003b, 0x310003b000290001200030000050004900057000640000a000540000c0001e0000b000360001600022000430006100022, 0x5d00037000460005e000060004000025000280005a000060002300050000270003e0000d0005900034000620000200060, 0x53000080000400064000640003000035000250002b0000c0003100003000510000c0001f000220005d0003d0004c0004f, 0x40002f0004f0005b000260004f000170004b00051000210001e0004f00061000620003d000170003e0003c000410003d, 0xb0004f0003100006000200001a000050001c000510004a0001100042000490000100039000260005b000620000900022, 0x290002b0002b0002e000090005200051000460005c00007000110003a0002d000600004900022000590001e0004f00014]
  Minv_cols := [0x500004300038000110000b0006100005000040003f00035000240001e000040003b00022000600004f0003d0002200014, 0x4c000490003e0003d0000f0002e000290000f0004c0003500049000150002b0004200061000020004c00041000090004f, 0x510002f00049000530005100061000110004500055000100004d0002c0003c0001200043000620003d0003c000620001e, 0x1d0002a00064000400001d00030000280003400032000160005500026000470003b00022000340005d0003e0005b00059, 0x480003a00039000470005d000160005a0000700054000040002f000490000800054000160005900022000170002600022, 0x350004100020000410003200029000330002a0003d00062000520001f0003c00052000360000d0001f0003d0003900049, 0x1f000420004d00017000600001a000340003d0001100048000370001900027000170000b0003e0000c000620000100060, 0x210002500037000120004f0000c00005000500004700062000110005d00044000450001e000270005100061000490002d, 0x45000580002b0004b000520000f0003a000400003d0004b000320003d00030000580000c00050000030004f000420003a, 0x2d00019000070002600003000460002b0001d0003f00038000030003300052000530005400023000310001e0001100011, 0x4c0001a0004d00001000320000b0000f00012000310001a000440001600048000010000a000060000c000210004a00007, 0x34000480001c000570001600064000510005f000160003300022000070001500042000640005a0002b00051000510005c, 0x52000620001a000540000a0002a00032000510003f000460000e00012000400000d0005700028000250004b0001c00046, 0x1c0001d0004e0003f0001c0002f0002c00053000050005b0004f0003b000610000a000490002500035000170000500051, 0xf0004d0002f0001e000270002a0001e000470002b000310002800063000400001e0000500040000300004f0001a00052, 0x610003e00031000590001d0002c0005f0000e0001d0001200001000490003100055000300000600064000260002000009, 0x34000210004d0001b000600001300012000170000f00053000440003d0000400048000120005e000640005b000060002e, 0x9000080005f000330004300017000540002d0005d0002a0004f0000e0004b000430002900046000040004f000310002b, 0x43000100004700048000500003f000400001b0005a00063000290005d00038000280003b00037000080002f0004f0002b, 0x90004d00011000540000b0003800001000130006300035000310001c0004e00012000310005d00053000040000b00029]
  b0 := ⟨0,
    [0xb0001d000630003c000630003d00059, 0x2200044000520004d00056000640004a, 0x5b0006000063000030000a000430003b, 0x80002a0004100064000140005b0000a, 0x3600004000600003b00032000030004b, 0x640003c0001f00057000640003d0000e, 0x260003c000000006000064000430002c],
    [0x590004a0003b0000a0004b0000e0002c, 0x3d00064000430005b000030003d00043, 0x63000560000a00014000320006400064, 0x3c0004d00003000640003b0005700060, 0x63000520006300041000600001f00000, 0x1d00044000600002a000040003c0003c, 0xb000220005b00008000360006400026],
    [0x3e000050001600035000430001600037, 0x16000030005c0000a000420005d00000, 0x90003700010000420000a0001a00018, 0x2d0000c0002f000350005b0003e00000, 0x60004b0003d0004a00061000010004c, 0x400055000630004c00028000500000d, 0x4e00051000300001900062000140002c],
    [0x370000000018000000004c0000d0002c, 0x160005d0001a0003e000010005000014, 0x43000420000a0005b000610002800062, 0x350000a00042000350004a0004c00019, 0x160005c000100002f0003d0006300030, 0x500003000370000c0004b0005500051, 0x3e00016000090002d00006000040004e],
    [0x150004000037, 0x290003d0002e, 0x110004a00053],
    [0x370002e00053, 0x400003d0004a, 0x150002900011],
    [0x2c000400001b, 0xf000000003c, 0x110002c0000b],
    [0x1b0003c0000b, 0x40000000002c, 0x2c0000f00011],
    [0x5f00052000630002a0002e0005b00024, 0x5b000480000800030000260004900026, 0x5f000180002d000320004c000110003d]⟩
  b1 := ⟨1,
    [0x39000300005d000210004c0003f00053, 0x3b00063000180002e0001a000010002d, 0x590003f000180003e000330002800004, 0x26000300004800053000590004e0004c, 0x6000460001b0002900027000430002f, 0x330003700062000160002c0000a0004a, 0x630006000007000320004d000470003a],
    [0x530002d000040004c0002f0004a0003a, 0x3f00001000280004e000430000a00047, 0x4c0001a0003300059000270002c0004d, 0x210002e0003e00053000290001600032, 0x5d0001800018000480001b0006200007, 0x30000630003f00030000460003700060, 0x390003b0005900026000060003300063],
    [0x1e000580001000044000120001b0003e, 0x390004c000120002f000450001900011, 0x2000038000090005f0005e0003b00033, 0x600002f0002500047000090005d00000, 0x5f0003c0001700030000200001800045, 0x3b00052000300002a00007000190000d, 0x2c000010000c0002e0002a0004d0001d],
    [0x3e000110003300000000450000d0001d, 0x1b000190003b0005d00018000190004d, 0x12000450005e0000900020000070002a, 0x440002f0005f00047000300002a0002e, 0x1000012000090002500017000300000c, 0x580004c000380002f0003c0005200001, 0x1e0003900020000600005f0003b0002c],
    [0x540005d0005b, 0x100003700025, 0x240001700034],
    [0x5b0002500034, 0x5d0003700017, 0x540001000024],
    [0x4a0002f0005e, 0x3f0000800022, 0xa0001c0005f],
    [0x5e000220005f, 0x2f000080001c, 0x4a0003f0000a],
    [0x23000100001b00019000500004f00044, 0x5f00013000190004d0000f0004900034, 0x5a000050000200016000610000e0001a]⟩
  b2 := ⟨2,
    [0x20000570001000041000280003f0003d, 0x1100056000410003e000350000800009, 0x490002700017000250004a000530005c, 0x600004a0001400028000430005500041, 0x440001f0004f000340003d000430002b, 0x28000370003e0004d000580002300041, 0x20002400022000510000a0002600022],
    [0x3d000090005c000410002b0004100022, 0x3f000080005300055000430002300026, 0x28000350004a000430003d000580000a, 0x410003e0002500028000340004d00051, 0x100004100017000140004f0003e00022, 0x5700056000270004a0001f0003700024, 0x20000110004900060000440002800002],
    [0x1600006000010002f000320005e00058, 0x4200061000240002e000100001000039, 0x2d0003f00051000120002a0002c0000f, 0x2b000310004800009000030000f00013, 0x5e0000f0004d00009000380002e00005, 0x530001d0004e000070003d0001c00006, 0x510004f0002000044000320004b00046],
    [0x58000390000f00013000050000600046, 0x5e000100002c0000f0002e0001c0004b, 0x32000100002a00003000380003d00032, 0x2f0002e0001200009000090000700044, 0x10002400051000480004d0004e00020, 0x6000610003f000310000f0001d0004f, 0x16000420002d0002b0005e0005300051],
    [0x500002000014, 0x2d0001f00039, 0x2d0004700002],
    [0x140003900002, 0x200001f00047, 0x500002d0002d],
    [0x41000260003e, 0x31000500003c, 0x320000900023],
    [0x3e0003c00023, 0x260005000009, 0x410003100032],
    [0x55000040004d0005d0004c0006300035, 0x25000140000f0004b000530001100024, 0x2e000300004a00024000370001700004]⟩

private theorem tripleCert_0_ok : checkTripleCert tripleCert_0 = true := by decide

private def tripleCert_1 : PackedTripleCert where
  n0 := 0
  n1 := 1
  n2 := 3
  M_rows := [0x300004100055000340000e0000400045000150001800003000240004e00008000640005a000150001d000000001f00042, 0x11000350006300025000410006200003000220005800009000370000300039000290001c000480000a000560002700062, 0x2a000390000f00014000310005f000570005e0002300041000490000b000380003f0001800053000470003a0001d00006, 0x5f000320001a0000f00056000110003700007000090004f000470004f00011000160002f0005a0005d00016000420002b, 0x40001f000380005b000260005e00030000030003d0004c00047000450000000053000090004b00021000040000900051, 0x54000130005d000030006400014000600003e00041000270004400033000140003a0001d0002000024000640005d00063, 0x3d000040001a00030000020001000033000230004e0004400012000030000d00053000010002a0003b0005f0001d00040, 0x100029000460000f00028000150003a0002700037000430002d000080003a0005e0000f0002b000360003b0001e00011, 0x140005e000230003f0005e00000000180004a000450005e000020001b0002900038000580002b0002000049000110001c, 0x1a00004000410001a0003300063000020001d0005a0000500045000500003b00050000100002700022000630003c00010, 0xa000070000b0001d000430005a0005e00055000500004500029000350001d0004a0001300037000120005f000410004d, 0x5e0005b000580005900024000180005300023000160004b0004c0003c0003b0005e000270002200022000510004100033, 0x32000540003f0004d00032000310001600045000540003f000400003a00025000570002f000210003500048000360000b, 0x360002f00053000620001a000090004a0000e0003b000460000f000200005200024000620005b000020004a0004b0003a, 0x280006100013000540003c000430000000029000260005f0004c0003e0001f0004d0001d000310004d000430000c0001b, 0x500008000530005e00016000300004f0000a00000000220003d00026000640002300026000640004f0004e0004f00001, 0x180001c0006300053000430000e000190001a000520004700020000550005e0002f0002d0000400042000240006200009, 0x3f000140001500055000550003b0005a000440003c000430003c0003c000290004f0004b000220003f000400003100033, 0x3000049000490002d0001b000420002b0002d0000a000490004900052000270004f00005000550000a0003a0001c00008, 0x1600036000130004b000170000b000640004200032000260000600003000630002900001000050001b0001a0002d00000]
  M_cols := [0x4200062000060002b000510006300040000110001c000100004d000330000b0003a0001b0000100009000330000800000, 0x1f000270001d00042000090005d0001d0001e000110003c0004100041000360004b0000c0004f00062000310001c0002d, 0x560003a0001600004000640005f0003b00049000630005f00051000480004a000430004e00024000400003a0001a, 0x1d0000a000470005d00021000240003b000360002000022000120002200035000020004d0004f000420003f0000a0001b, 0x1500048000530005a0004b000200002a0002b0002b000270003700022000210005b000310006400004000220005500005, 0x5a0001c000180002f000090001d000010000f000580001000013000270002f000620001d000260002d0004b0000500001, 0x64000290003f00016000530003a000530005e00038000500004a0005e00057000240004d000230002f0004f0004f00029, 0x800039000380001100000000140000d0003a000290003b0001d0003b00025000520001f000640005e000290002700063, 0x4e000030000b0004f000450003300003000080001b00050000350003c0003a000200003e00026000550003c0005200003, 0x240003700049000470004700044000120002d0000200045000290004c000400000f0004c0003d000200003c0004900006, 0x300009000410004f0004c0002700044000430005e00005000450004b0003f000460005f0002200047000430004900026, 0x180005800023000090003d000410004e00037000450005a0005000016000540003b0002600000000520003c0000a00032, 0x15000220005e00007000030003e00023000270004a0001d0005500023000450000e000290000a0001a000440002d00042, 0x450000300057000370003000060000330003a00018000020005e00053000160004a000000004f000190005a0002b00064, 0x4000620005f000110005e00014000100001500000000630005a00018000310000900043000300000e0003b000420000b, 0xe000410003100056000260006400002000280005e000330004300024000320001a0003c0001600043000550001b00017, 0x3400025000140000f0005b00003000300000f0003f0001a0001d000590004d00062000540005e00053000550002d0004b, 0x55000630000f0001a000380005d0001a0004600023000410000b000580003f00053000130005300063000150004900013, 0x410003500039000320001f0001300004000290005e00004000070005b000540002f00061000080001c000140004900036, 0x30000110002a0005f00004000540003d00001000140001a0000a0005e00032000360002800005000180003f0003000016]
  Minv_rows := [0x49000340001a0002f0004100031000390005c0004f000450005a0003f0002e000520002c0002d000570003e0004900061, 0x4f0001b00020000580001e0001a000050004b0004300034000370002c000120001e000320003b00020000400002d00060, 0x52000110003d000150001b0000b00023000120000d000610002f0003c0002c000260003d000630005d000100000d00036, 0x630002b0001900055000620002d0004d0003f000030000e00061000510002100016000100000700050000250004b00027, 0x1f0003f0003b0000400048000080003f0005e0005f0000c0000e000090003700034000430003f0002b0000e000510004f, 0x4900025000090004400047000370003e000420001600034000210004a000550000d0003300058000120002a0003d0004d, 0x3d0000f000250003c000090005f000290005c00007000020004d0002800035000290002e000640002c0005b0002500059, 0x260003800041000400001f000480000c0003e00002000400001c0001b0002b0002100036000400001c0002f0002600042, 0xa0003700021000480004e0002e0002d0005e0003700048000100004c000400001a000480005b00039000020003e0000f, 0x7000220003f00035000090002b0004b0000d000360002a000110002e0002a000300003a0003a000170001f0005600062, 0x210002200056000580001f000480004a0003d000590002800054000170002e00039000320001b0004d0001e0001d00000, 0x1300034000480002e0001a00023000260000a000500004400033000270006300035000260000000046000210004900018, 0x630005f0001a00014000100004f0003300009000130004700003000280004700024000000006400030000430004c00004, 0x2c000540000c000270005400017000500002f0000300031000180005d000410005c0004c0005a0002d00005000470002e, 0x2e000510002c0004700035000270000600048000600004300020000250005f000560003b00006000080001c0002200060, 0x630003e0005a0006300013000210002a000590004f0002a00040000490000b0004b000170006400041000140000600020, 0x200000a000440004300001000450005e0003d0000a000330002a000420001b0000a00049000300002900025000450002d, 0x300005e0003600007000280005a0002900015000580000e0005e0000f0003400045000330000500051000140005400021, 0x20005d00064000210000d000160004a000430005d000180004600002000520002c0005b000070000d0001b0005000053, 0x36000500000c000520003b0000e00036000230004400017000340005f0000c000370000800007000320005b0000d00014]
  Minv_cols := [0x610006000036000270004f0004d00059000420000f000620000000018000040002e00060000200002d000210005300014, 0x490002d0000d0004b000510003d00025000260003e000560001d000490004c0004700022000060004500054000500000d, 0x3e0004000010000250000e0002a0005b0002f000020001f0001e0002100043000050001c0001400025000140001b0005b, 0x57000200005d000500002b000120002c0001c00039000170004d00046000300002d000080004100029000510000d00032, 0x2d0003b00063000070003f0005800064000400005b0003a0001b00000000640005a000060006400030000050000700007, 0x2c000320003d0001000043000330002e00036000480003a0003200026000000004c0003b0001700049000330005b00008, 0x520001e0002600016000340000d00029000210001a000300003900035000240005c000560004b0000a000450002c00037, 0x2e000120002c000210003700055000350002b000400002a0002e0006300047000410005f0000b0001b00034000520000c, 0x3f0002c0003c00051000090004a000280001b0004c0002e0001700027000280005d0002500049000420000f000020005f, 0x5a000370002f000610000e000210004d0001c00010000110005400033000030001800020000400002a0005e0004600034, 0x4500034000610000e0000c000340000200040000480002a00028000440004700031000430002a000330000e0001800017, 0x4f000430000d000030005f000160000700002000370003600059000500001300003000600004f0000a000580005d00044, 0x5c0004b000120003f0005e000420005c0003e0005e0000d0003d0000a000090002f00048000590003d000150004300023, 0x3900005000230004d0003f0003e000290000c0002d0004b0004a000260003300050000060002a0005e000290004a00036, 0x310001a0000b0002d00008000370005f000480002e0002b00048000230004f000170002700021000450005a000160000e, 0x410001e0001b000620004800047000090001f0004e000090001f0001a0001000054000350001300001000280000d0003b, 0x2f00058000150005500004000440003c000400004800035000580002e0001400027000470006300043000070002100052, 0x1a000200003d000190003b000090002500041000210003f00056000480001a0000c0002c0005a0004400036000640000c, 0x340001b000110002b0003f000250000f00038000370002200022000340005f00054000510003e0000a0005e0005d00050, 0x490004f00052000630001f000490003d000260000a000070002100013000630002c0002e0006300020000300000200036]
  b0 := ⟨0,
    [0xc0004b0001400034000260001800063, 0x470001e0004100050000020003500041, 0x280004100044000220000f000310000a, 0x260004900043000110001b0006200023, 0x620002f0000c0004200035000210000b, 0x15000300002f00023000430002800045, 0x2e00043000160004200052000580000a],
    [0x63000410000a000230000b000450000a, 0x18000350003100062000210002800058, 0x26000020000f0001b000350004300052, 0x34000500002200011000420002300042, 0x140004100044000430000c0002f00016, 0x4b0001e00041000490002f0003000043, 0xc00047000280002600062000150002e],
    [0x5c000460001e000310005a000250002d, 0x41000590003b0002800032000450005f, 0x2d0004f0000400003000610002100058, 0x160000e00043000110004b000050001d, 0x3100010000370001b000320003f00052, 0x230001b000470003f000210004b00033, 0xc0001a00043000580004f0003400034],
    [0x2d0005f000580001d000520003300034, 0x250004500021000050003f0004b00034, 0x5a00032000610004b00032000210004f, 0x310002800003000110001b0003f00058, 0x1e0003b0000400043000370004700043, 0x46000590004f0000e000100001b0001a, 0x5c000410002d0001600031000230000c],
    [0x560001b00009, 0x51000370001e, 0x150003400007],
    [0x90001e00007, 0x1b0003700034, 0x560005100015],
    [0x480002300007, 0x460002400032, 0x30000050002f],
    [0x7000320002f, 0x230002400005, 0x480004600030],
    [0x47000040002400053000610001500062, 0x1c00013000150005c000470003b00028, 0x4b000550005500051000620004900009]⟩
  b1 := ⟨1,
    [0x470003a000320003b000040000e00014, 0x280004100048000080004e0002000042, 0x43000400005c000420005f000200000b, 0x430000a0005f00037000350002f00021, 0x2f000240000700007000510002c00014, 0x1d00044000390000f000310003b00007, 0x53000130004e00012000000001b00007],
    [0x14000420000b00021000140000700007, 0xe00020000200002f0002c0003b0001b, 0x40004e0005f00035000510003100000, 0x3b000080004200037000070000f00012, 0x32000480005c0005f00007000390004e, 0x3a00041000400000a000240004400013, 0x470002800043000430002f0001d00053],
    [0x460004b0003800039000410003f00000, 0x38000470005d0001b0004e0005a0004a, 0x56000600005a0006300020000400002d, 0x390002e0004d000620002c0006400049, 0x4000050004300059000210003a00021, 0x230004b0005c000400004c0005100051, 0x630001e0003b0004000038000180003b],
    [0x4a0002d0004900021000510003b, 0x3f0005a00040000640003a0005100018, 0x410004e000200002c000210004c00038, 0x390001b0006300062000590004000040, 0x380005d0005a0004d000430005c0003b, 0x4b00047000600002e000050004b0001e, 0x46000380005600039000040002300063],
    [0x150002500063, 0xf0004f00034, 0x240002f00048],
    [0x630003400048, 0x250004f0002f, 0x150000f00024],
    [0x70003b00012, 0xb0002000010, 0x270001f00059],
    [0x120001000059, 0x3b000200001f, 0x70000b00027],
    [0x640001e000470005c000490001b00049, 0x1000490001a0005c000420006400062, 0x200059000620005f000300001500011]⟩
  b2 := ⟨3,
    [0xa000460002d0005b000510003100051, 0x400004b0004f000220001a0004300037, 0xe0004b0005e0000d000210003a00038, 0x470001e000060005b0002c0001600058, 0x6000041000130005f000040005600033, 0x57000230000c00024000110002100063, 0x33000020004500026000050002200059],
    [0x51000370003800058000330006300059, 0x31000430003a00016000560002100022, 0x510001a000210002c000040001100005, 0x5b000220000d0005b0005f0002400026, 0x2d0004f0005e00006000130000c00045, 0x460004b0004b0001e000410002300002, 0xa000400000e00047000600005700033],
    [0x5c000310005d0003a00012000310004d, 0x330005d0000b000360001f000400001d, 0x190002600037000540002e0004f00013, 0xb000470002c00000000290004e0002c, 0x630001e0004400051000490001b00022, 0xe00030000100002a000020002000003, 0x62000600003c0004e000120005900015],
    [0x4d0001d000130002c000220000300015, 0x31000400004f0004e0001b0002000059, 0x120001f0002e00029000490000200012, 0x3a000360005400000000510002a0004e, 0x5d0000b000370002c00044000100003c, 0x310005d00026000470001e0003000060, 0x5c00033000190000b000630000e00062],
    [0x460003600017, 0x210004b00051, 0x420003300003],
    [0x170005100003, 0x360004b00033, 0x460002100042],
    [0x290004600026, 0x1c000090005c, 0x10001600013],
    [0x260005c00013, 0x460000900016, 0x290001c00001],
    [0x62000000001c0003b0004d0002a00064, 0x36000200004700038000520006100064, 0x300002600044000480003d0000c00031]⟩

private theorem tripleCert_1_ok : checkTripleCert tripleCert_1 = true := by decide

private def tripleCert_2 : PackedTripleCert where
  n0 := 0
  n1 := 1
  n2 := 4
  M_rows := [0x5d0003c0001f0006400004000530006200064000240005a0004d0001f00043000290001b00045000130002d0002400041, 0x36000100003900007000250001700062000100002900039000540005a000090004400043000350001100021000050002f, 0x22000300005500000000080003100002000440003b00019000390003d0001f0003a00019000570001000007000100004f, 0x150005800027000040005e000590002e000440000f000500000d0002f0005d000220001f0002b000320004a000000005e, 0x38000180003b000410003600013000500004f00047000250001b0000a0005800014000490001a00040000510000a00044, 0x20005c00051000290006000003000270000e0001200064000190005200050000020004500038000510000a0002e00042, 0x23000230005300055000570005c0000a0002900052000580005000022000280002f0000a000540000c00064000590000d, 0x4900007000320004d0005e0005200001000230003500023000190003e0005b000340000d00023000610001e0003b00049, 0x250001300034000520000600046000550001d0001c0001c0004a00034000200000400044000110006100017000550001e, 0x80005b0003b0003e00001000260002f00056000630001c00059000390004800016000140005000034000300003e00008, 0x1800063000520001b000570004f0003b000040004a00018000120000800035000260003d0004900049000510000500046, 0x1e0000b0005a0001c0004a0004b000570004e0005c00016000090005f0002d00048000160006300012000170001e00008, 0x37000160005a0002500027000440003d0000f000600003d00059000440002e000290001b0000700003000170005900010, 0x33000050002b00020000540001c0003500046000160002300010000360004400053000250005a00040000020003000016, 0x14000180001d000230001c0005a000470001a00012000280005c00029000500000c000050003700024000390001400043, 0x2f000300001b000270006100001000550000b00057000400004d000290001b0004c000480003c0002e000020004200058, 0x630002b0003d00045000440002b00052000090002500010000280002a0005f0002400049000260000f00031000580005a, 0x170004c000280005100048000270003c0002d000380003c0006100034000620001b0004b0001800000000440001800039, 0x430000600039000420002700005000610004700051000300005f000610000c00037000520005c0001b0002b0001d00034, 0x500004c0004e00036000070006400010000160001800032000340002b0001000031000640002a00035000400001800040]
  M_cols := [0x410002f0004f0005e00044000420000d000490001e000080004600008000100001600043000580005a000390003400040, 0x240000500010000000000a0002e000590003b000550003e000050001e0005900030000140004200058000180001d00018, 0x2d00021000070004a000510000a000640001e000170003000051000170001700002000390000200031000440002b00040, 0x1300011000100003200040000510000c00061000610003400049000120000300040000240002e0000f000000001b00035, 0x4500035000570002b0001a00038000540002300011000500004900063000070005a000370003c00026000180005c0002a, 0x1b00043000190001f00049000450000a0000d00044000140003d000160001b000250000500048000490004b0005200064, 0x29000440003a0002200014000020002f000340000400016000260004800029000530000c0004c000240001b0003700031, 0x43000090001f0005d0005800050000280005b0002000048000350002d0002e00044000500001b0005f000620000c00010, 0x1f0005a0003d0002f0000a00052000220003e0003400039000080005f000440003600029000290002a00034000610002b, 0x4d00054000390000d0001b0001900050000190004a00059000120000900059000100005c0004d00028000610005f00034, 0x5a000390001900050000250006400058000230001c0001c00018000160003d000230002800040000100003c0003000032, 0x24000290003b0000f000470001200052000350001c000630004a0005c0006000016000120005700025000380005100018, 0x640001000044000440004f0000e00029000230001d00056000040004e0000f000460001a0000b000090002d0004700016, 0x6200062000020002e00050000270000a00001000550002f0003b000570003d000350004700055000520003c0006100010, 0x5300017000310005900013000030005c0005200046000260004f0004b000440001c0005a000010002b000270000500064, 0x400025000080005e0003600060000570005e0000600001000570004a00027000540001c0006100044000480002700007, 0x640000700000000040004100029000550004d000520003e0001b0001c0002500020000230002700045000510004200036, 0x1f0003900055000270003b000510005300032000340003b000520005a0005a0002b0001d0001b0003d00028000390004e, 0x3c000100003000058000180005c0002300007000130005b000630000b000160000500018000300002b0004c000060004c, 0x5d000360002200015000380000200023000490002500008000180001e0003700033000140002f00063000170004300050]
  Minv_rows := [0x30000150006300019000440000c0005d0004300014000350002b000160001b0000300052000500000c00025000020004c, 0x5f0001f00020000070002b00021000170001b00022000220000b000100003a000060003c0005e00051000580003900019, 0x55000550004f000430004000062000500004a0004c0002f0004e0001e0004f000370001c000200006300009000060005e, 0x5700035000040003200013000370003d0000c000410004600025000460004e0004f0001c000550004c000210001400021, 0x5c0005e000180003600047000120002f0000f0000d000500000300043000000003c0000c0005d00060000140002600044, 0x540004600045000330003c00032000420005c0001a00034000070005900013000500005000055000410003c000230003c, 0x430005c00009000100002200030000590001100032000250003e0004400012000250001d0003600003000210004b00000, 0x2e0005f0005a0001a0005c0003e0002e000410000e0002d00050000560004f0000100010000240006200021000430000b, 0x3a00063000120005d000520004d00017000080004f00062000100001f0002e0003f0002d00013000220004c000570001d, 0xb0001c0001b000600004b000510002f0000d0000d0000c000230006000063000170001000056000500002b0003a00014, 0x15000080001900050000610003e00032000420003b0003300000000000000900031000050003400061000350004500021, 0x3700053000060001c000590001100047000480005e00038000150003600058000130005a0001f00039000110004200058, 0x18000570003700001000510005c000550004e0004b00018000480005400030000580002d000150003e000110000d00036, 0x550005b00037000030000200005000350000d00037000000003b0005f000590002d0001b0003400038000460001a0005a, 0x360002a0003a0001f000080000a0003e00027000110003c0000700054000560000e00039000170002600023000470002e, 0x2a00006000320004600042000460004b000560001c0003700017000240001f0001f0003800040000560003e000360005c, 0x5300014000440002700026000450004f0003b0001700040000600000a00054000000003c0003e00040000380003b0001e, 0xe000160001c0000f00057000270005f0001400048000240003a0002b0000e0003e0005a0000600051000100002a00039, 0x600004d00021000300000200007000070001900001000120000a0001600006000550003500020000380005c0002700047, 0x1d00008000490003f0001800063000370001e000180003c0002000020000130002400016000000001c000620000300042]
  Minv_cols := [0x4c000190005e00021000440003c000000000b0001d000140002100058000360005a0002e0005c0001e000390004700042, 0x200039000060001400026000230004b00043000570003a00045000420000d0001a00047000360003b0002a0002700003, 0x25000580000900021000140003c00021000210004c0002b00035000110001100046000230003e00038000100005c00062, 0xc00051000630004c00060000410000300062000220005000061000390003e0003800026000560004000051000380001c, 0x500005e00020000550005d0005500036000240001300056000340001f000150003400017000400003e000060002000000, 0x520003c0001c0001c0000c000500001d000100002d00010000050005a0002d0001b00039000380003c0005a0003500016, 0x300006000370004f0003c0005000025000010003f000170003100013000580002d0000e0001f000000003e0005500024, 0x1b0003a0004f0004e0000000013000120004f0002e0006300009000580003000059000560001f000540000e0000600013, 0x16000100001e00046000430005900044000560001f000600000000036000540005f00054000240000a0002b0001600020, 0x2b0000b0004e0002500003000070003e0005000010000230000000015000480003b0000700017000600003a0000a00020, 0x35000220002f000460005000034000250002d000620000c000330003800018000000003c000370004000024000120003c, 0x14000220004c000410000d0001a000320000e0004f0000d0003b0005e0004b00037000110001c00017000480000100018, 0x430001b0004a0000c0000f0005c0001100041000080000d00042000480004e0000d00027000560003b00014000190001e, 0x5d00017000500003d0002f00042000590002e000170002f000320004700055000350003e0004b0004f0005f0000700037, 0xc0002100062000370001200032000300003e0004d000510003e000110005c000050000a0004600045000270000700063, 0x440002b0004000013000470003c000220005c000520004b00061000590005100002000080004200026000570000200018, 0x190000700043000320003600033000100001a0005d00060000500001c00001000030001f00046000270000f000300003f, 0x63000200004f000040001800045000090005a000120001b000190000600037000370003a00032000440001c0002100049, 0x150001f00055000350005e000460005c0005f000630001c0000800053000570005b0002a0000600014000160004d00008, 0x300005f00055000570005c00054000430002e0003a0000b00015000370001800055000360002a000530000e000600001d]
  b0 := ⟨0,
    [0x5f000180005f0000b0001b0004f00063, 0x20000e00040000150003d000020002e, 0x330001b0005700003000320001500059, 0x620003d0002200007000500005f00063, 0x5c0002f00012000620000c0003d, 0x61000370002a0004600039000000005a, 0x3600037000180003d0004f0004400045],
    [0x630002e00059000630003d0005a00045, 0x4f00002000150005f0000c0000000044, 0x1b0003d000320005000062000390004f, 0xb00015000030000700012000460003d, 0x5f0004000057000220002f0002a00018, 0x180000e0001b0003d0005c0003700037, 0x5f000020003300062000000006100036],
    [0x3c000240004b0000e000120000d0005e, 0x2a0004d0002a0005300018000410005a, 0x100002900031000350002b0003500002, 0x2e0002f000390002100025000040004c, 0x10003f0002800054000530002000034, 0x48000310004a00008000560001200045, 0x2a00063000270003a0003c0005f],
    [0x5e0005a000020004c00034000450005f, 0xd00041000350000400020000120003c, 0x12000180002b0002500053000560003a, 0xe000530003500021000540000800027, 0x4b0002a0003100039000280004a00063, 0x240004d000290002f0003f000310002a, 0x3c0002a000100002e000010004800000],
    [0x190002a0001d, 0x290000900023, 0x70004500057],
    [0x1d0002300057, 0x2a0000900045, 0x190002900007],
    [0xf0004600053, 0x1a0003d0001a, 0x300005700036],
    [0x530001a00036, 0x460003d00057, 0xf0001a00030],
    [0x2a000260004800051000550003c00032, 0x260004800064000550000e0001500040, 0x26000640001900007000260000200057]⟩
  b1 := ⟨1,
    [0x120000e0004100063000230002300028, 0x1b0002a0003f0003f000620001900012, 0x49000080005d00030000400002900034, 0x27000540004e0001e000390005800048, 0x90002c000430002f000180005100018, 0x400026000420003100003000560001e, 0x100004a0001e0004c000400003d00015],
    [0x28000120003400048000180001e00015, 0x2300019000290005800051000560003d, 0x23000620004000039000180000300040, 0x630003f000300001e0002f000310004c, 0x410003f0005d0004e00043000420001e, 0xe0002a00008000540002c000260004a, 0x120001b0004900027000090000400010],
    [0x340003f0000800060000200003a00010, 0x620004b000250003100050000310004b, 0x130003100024000460005d000060001c, 0x49000570002000030000240003a0004f, 0x20000140005000064000580001100007, 0x3c000290003f0003500036000550005a, 0x5c00007000270001c000540005c00014],
    [0x100004b0001c0004f000070005a00014, 0x3a00031000060003a00011000550005c, 0x20000500005d00024000580003600054, 0x6000031000460003000064000350001c, 0x8000250002400020000500003f00027, 0x3f0004b0003100057000140002900007, 0x34000620001300049000200003c0005c],
    [0x2b0006000032, 0x490004300038, 0x53000130002c],
    [0x32000380002c, 0x600004300013, 0x2b0004900053],
    [0x150004700001, 0x2d0002f00021, 0x90002600063],
    [0x10002100063, 0x470002f00026, 0x150002d00009],
    [0x17000090001000009000620004d0000c, 0x490004a00000000300004d0001800010, 0x43000180002b0000c0005b0006100027]⟩
  b2 := ⟨4,
    [0x6000190002e0001500025000550002d, 0x61000480002d0001a0003c0002900031, 0x42000610002f0001f000420000a0004a, 0x26000630005e00043000070003300016, 0x1e00018000000004d000590000a00003, 0xa0003c000470002800029000420003c, 0x5a000100000700027000550006200022],
    [0x2d000310004a00016000030003c00022, 0x55000290000a000330000a0004200062, 0x250003c0004200007000590002900055, 0x150001a0001f000430004d0002800027, 0x2e0002d0002f0005e000000004700007, 0x19000480006100063000180003c00010, 0x60006100042000260001e0000a0005a],
    [0x450002e000180000c0001e0003800053, 0x3e0000d00014000170004f0000200038, 0x4d000040000e00007000220000000043, 0x470001c000580005b000540002800048, 0x110003d0003b00049000440000d00020, 0x3c0003f0005c000510003e0002600019, 0x4c000200005b0004c000310001d0003d],
    [0x5300038000430004800020000190003d, 0x380000200000000280000d000260001d, 0x1e0004f0002200054000440003e00031, 0xc00017000070005b00049000510004c, 0x18000140000e000580003b0005c0005b, 0x2e0000d000040001c0003d0003f00020, 0x450003e0004d00047000110003c0004c],
    [0x400000500062, 0x39000430004c, 0x100001100001],
    [0x620004c00001, 0x50004300011, 0x400003900010],
    [0x540005b0000a, 0x1a0002e0003f, 0x180004e00041],
    [0xa0003f00041, 0x5b0002e0004e, 0x540001a00018],
    [0x900010000380005f0005a0006300047, 0x4e0002f00030000260003a0002f00033, 0x470001d000590000e000150004c00031]⟩

private theorem tripleCert_2_ok : checkTripleCert tripleCert_2 = true := by decide

private def tripleCert_3 : PackedTripleCert where
  n0 := 0
  n1 := 1
  n2 := 5
  M_rows := [0x22000490005d000270001b0006100049000400003200044000260004b0001f0003f000510004f00031000250000a0004a, 0x4e00038000480001b00032000050001a000180003d000160002e00018000220002b000210001100033000640001f00051, 0x4c000430004e00049000250001800005000620005f000230002900006000330004f000570004a00004000380000200021, 0xe0001a0005000053000600005400005000420002e0001a0004f0002500018000310001c0001b0000a000070002b00022, 0x6100013000170002f0003b00035000500005300026000090002800034000410006100011000520001a000260000f00049, 0x5f0005400028000430003b0004d0002c00036000280004d000210002a000290003d00003000240001b000060003f00002, 0x2c0004e00025000210005e0003300021000020002f000390003c000050003800016000190000a0003c0002a0001200050, 0xd000340001c0005e000390001a0000c0002800000000060005b000240003a00038000580002100041000520003100050, 0x3d000530001a000280000800059000320002500045000600004c00052000020001d0002f00004000370001d0001c00015, 0x53000260005200045000390001f000420000c0003800027000520004c000170005c00036000160005c000260000c0004d, 0x50000460000d0005000024000590004b00040000610000d0005d0004e0000000021000310003f000640004e0005d00033, 0x3600034000490002700003000160004a00037000320005d0002900033000230000c0000f000070004700037000620004c, 0x2200014000240003900005000410003300023000150002c00039000480005200022000270005f0002a0003f0004900025, 0x34000200001c000250001a0001700015000490004b0001500056000040003700041000050001b00053000120001d00064, 0x330002a0004a0004c00009000090004d0005e0005800061000380002f0000f0000a00040000580002f000410003900063, 0x1e0002c000320001e00025000420002200016000160004700055000030005f000160002200025000490005c0004b00021, 0x550005700045000220002100027000030000a00001000050005c0001e00042000130004d000040001b0003e0003b00028, 0x29000080004f0001700046000110002800021000360003e0002b000320000d000040002d000580005900023000060000c, 0x2500062000020004b0002100002000300005800062000160003e00027000300001a0003a000520005b0003b0006100040, 0x34000010002f0000700049000000003400024000530001a00023000180000f0002e00023000380000a000210004b00060]
  M_cols := [0x4a00051000210002200049000020005000050000150004d000330004c00025000640006300021000280000c0004000060, 0xa0001f000020002b0000f0003f00012000310001c0000c0005d00062000490001d000390004b0003b00006000610004b, 0x2500064000380000700026000060002a000520001d000260004e000370003f00012000410005c0003e000230003b00021, 0x3100033000040000a0001a0001b0003c00041000370005c00064000470002a000530002f000490001b000590005b0000a, 0x4f000110004a0001b00052000240000a0002100004000160003f000070005f0001b000580002500004000580005200038, 0x5100021000570001c000110000300019000580002f00036000310000f000270000500040000220004d0002d0003a00023, 0x3f0002b0004f00031000610003d00016000380001d0005c000210000c00022000410000a0001600013000040001a0002e, 0x1f0002200033000180004100029000380003a0000200017000000002300052000370000f0005f000420000d000300000f, 0x4b000180000600025000340002a0000500024000520004c0004e0003300048000040002f000030001e000320002700018, 0x260002e000290004f00028000210003c0005b0004c000520005d00029000390005600038000550005c0002b0003e00023, 0x4400016000230001a000090004d000390000600060000270000d0005d0002c000150006100047000050003e000160001a, 0x320003d0005f0002e00026000280002f0000000045000380006100032000150004b000580001600001000360006200053, 0x4000018000620004200053000360000200028000250000c000400003700023000490005e000160000a000210005800024, 0x490001a0000500005000500002c000210000c00032000420004b0004a00033000150004d0002200003000280003000034, 0x61000050001800054000350004d000330001a000590001f00059000160004100017000090004200027000110000200000, 0x1b0003200025000600003b0003b0005e0003900008000390002400003000050001a000090002500021000460002100049, 0x270001b00049000530002f00043000210005e0002800045000500002700039000250004c0001e00022000170004b00007, 0x5d000480004e000500001700028000250001c0001a000520000d00049000240001c0004a00032000450004f000020002f, 0x4900038000430001a00013000540004e000340005300026000460003400014000200002a0002c00057000080006200001, 0x220004e0004c0000e000610005f0002c0000d0003d0005300050000360002200034000330001e00055000290002500034]
  Minv_rows := [0x360005a0005b000370003b0003f0003a00056000100000d000450003e0002f0003c00051000590002200018000230003c, 0xe00023000290003700005000460005b000180005a00051000250002900038000440004f0002000037000170002400045, 0x1700037000600001d0001c00011000000004a00041000430003a0000b000270002d0001d000410003c0001e0000d0001f, 0x300002c0003b0006200045000180000f00060000060000f0002d00045000090002f0003b000010001e000360002600024, 0x35000330004d00042000150004900000000180001a000390002b0006200033000340004d000310000300008000040004b, 0x120005d0003d000640001e000520004a0001100007000440005c00026000150001400004000190003e0004a000500003c, 0x2b0001f00021000200002c0003700032000090004500010000130003c0001b000420005f000390001300047000280003e, 0x560004300021000470003f000440000a0005a000560001f0001c0005300057000150005600022000420005f0005100023, 0x12000400002a0004e0000e00003000580005a0002f00034000270000b0002c0004a000490002a00059000460003300003, 0x26000340001d00022000120005c0001f0001a0003400028000010002d0001c000320001a00061000020000d0004f00050, 0xb0002a0001e000580000800034000430001100004000550000600027000620003b0004f00004000370004a0002300021, 0xa0001d0003d00035000140000f000510000f0004d0003f0003700031000210002f0006300055000330004c000390005f, 0x42000110004800015000310005d0001600018000570000c00062000050005c0002b000010001d00015000610000100007, 0x3f000200005f000340001200005000060000d000590001900000000370003100015000030004d0001b0000c0005c0003a, 0x18000440005100034000600001c000490005b0000d0001f0002c000300002700006000490000600000000010001e0004c, 0x640001e000540000b000490004c0001e0002900057000260004a0000e00062000400001b000320003c0002a0003a00007, 0x200039000020001e0003f0005600037000170000a000460003500021000040002200032000390005c000370002e00026, 0x3a0002d00037000090002b000470003c0002e000580003e0000c0004f000490004c0000600033000620003c000070001a, 0x5a000310003a0004b00026000610002c0001300062000130002e0001e000030003a000330002100039000400000300002, 0x350004a0004b0002800064000540000b0003e000120002e000010001f00051000550002e0003a00062000370005a00004]
  Minv_cols := [0x3c000450001f000240004b0003c0003e000230000300050000210005f000070003a0004c00007000260001a0000200004, 0x23000240000d0002600004000500002800051000330004f0002300039000010005c0001e0003a0002e00007000030005a, 0x18000170001e00036000080004a000470005f000460000d0004a0004c000610000c000010002a000370003c0004000037, 0x22000370003c0001e000030003e000130004200059000020003700033000150001b000000003c0005c000620003900062, 0x59000200004100001000310001900039000220002a0006100004000550001d0004d00006000320003900033000210003a, 0x510004f0001d0003b0004d000040005f00056000490001a0004f000630000100003000490001b0003200006000330002e, 0x3c000440002d0002f000340001400042000150004a000320003b0002f0002b000150000600040000220004c0003a00055, 0x2f00038000270000900033000150001b000570002c0001c00062000210005c00031000270006200004000490000300051, 0x3e000290000b0004500062000260003c000530000b0002d00027000310000500037000300000e000210004f0001e0001f, 0x45000250003a0002d0002b0005c000130001c0002700001000060003700062000000002c0004a000350000c0002e00001, 0xd00051000430000f0003900044000100001f0003400028000550003f0000c000190001f00026000460003e000130002e, 0x100005a00041000060001a0000700045000560002f00034000040004d00057000590000d000570000a000580006200012, 0x56000180004a000600001800011000090005a0005a0001a000110000f000180000d0005b00029000170002e000130003e, 0x3a0005b000000000f000000004a000320000a000580001f00043000510001600006000490001e000370003c0002c0000b, 0x3f00046000110001800049000520003700044000030005c000340000f0005d000050001c0004c00056000470006100054, 0x3b000050001c00045000150001e0002c0003f0000e000120000800014000310001200060000490003f0002b0002600064, 0x37000370001d00062000420006400020000470004e0002200058000350001500034000340000b0001e000090004b00028, 0x5b00029000600003b0004d0003d00021000210002a0001d0001e0003d000480005f000510005400002000370003a0004b, 0x5a00023000370002c000330005d0001f0004300040000340002a0001d0001100020000440001e000390002d000310004a, 0x360000e000170003000035000120002b0005600012000260000b0000a000420003f0001800064000020003a0005a00035]
  b0 := ⟨0,
    [0x3a0003e000480002900008000570001a, 0x36000000004800039000570005b0000a, 0x5800058000270005e000360001800016, 0xf000040001200029000500003600007, 0xc0005600042000310000a000270000f, 0x10002b0004e00005000450000f00043, 0xe00004000240003e000220004100063],
    [0x1a0000a00016000070000f0004300063, 0x570005b0001800036000270000f00041, 0x80005700036000500000a0004500022, 0x29000390005e0002900031000050003e, 0x48000480002700012000420004e00024, 0x3e000000005800004000560002b00004, 0x3a00036000580000f0000c000010000e],
    [0x1b0002c00054000300003e000530000b, 0x31000090002e000050002d0002d0004c, 0x580002a0005e0002b000380001900024, 0x11000020002a00038000460001400016, 0x2800037000340004d0004c0002500004, 0x290001a000030005b000460005b00029, 0x330000f0004800006000620005800013],
    [0xb0004c0002400016000040002900013, 0x530002d0001900014000250005b00058, 0x3e0002d00038000460004c0004600062, 0x30000050002b000380004d0005b00006, 0x540002e0005e0002a000340000300048, 0x2c000090002a00002000370001a0000f, 0x1b000310005800011000280002900033],
    [0x51000090001e, 0x10003e00044, 0x560001900030],
    [0x1e0004400030, 0x90003e00019, 0x510000100056],
    [0x4b000130004c, 0x230003e0005d, 0x2000100004b],
    [0x4c0005d0004b, 0x130003e00010, 0x4b0002300002],
    [0x120005e0005700020000430006000035, 0x29000080001f00035000490002d0003f, 0x1800029000270000e000450002900041]⟩
  b1 := ⟨1,
    [0x37000230003b00044000470004b00028, 0x30005f0001100064000550001900019, 0x43000370000e00016000380003900009, 0x3f0003c0000c000610004c0001b0001d, 0x4b00038000160005f000490002700018, 0x5e0005e0004300027000010000d0003c, 0x63000260000f000140003a000190002d],
    [0x2800019000090001d000180003c0002d, 0x4b00019000390001b000270000d00019, 0x4700055000380004c00049000010003a, 0x440006400016000610005f0002700014, 0x3b000110000e0000c00016000430000f, 0x230005f000370003c000380005e00026, 0x3700003000430003f0004b0005e00063],
    [0x5e0001b00033000180002d000470004d, 0x3e0004c0000d0001a000090004d00062, 0x1b0004d0001400027000250003d0001e, 0x130000d0005c0003d000030000100014, 0x320003f0000200058000510005600026, 0xe00031000630001100022000070001d, 0x9000480003c00036000620004300042],
    [0x4d000620001e00014000260001d00042, 0x470004d0003d00001000560000700043, 0x2d000090002500003000510002200062, 0x180001a000270003d000580001100036, 0x330000d000140005c00002000630003c, 0x1b0004c0004d0000d0003f0003100048, 0x5e0003e0001b00013000320000e00009],
    [0x210006200020, 0x1b000370005b, 0x120005300059],
    [0x200005b00059, 0x620003700053, 0x210001b00012],
    [0x53000170005c, 0x2b000640003c, 0x30003000036],
    [0x5c0003c00036, 0x170006400030, 0x530002b00003],
    [0x200004000021000500000a0005500057, 0xb0002c0003c000300001a0000f0003d, 0x580002a0004f00062000400000f00033]⟩
  b2 := ⟨5,
    [0x320000e000250004300061000510002d, 0x50000100000400005000420000b00003, 0x130000b0003a0001b0005e000420004c, 0x60000900028000250005e0005f00033, 0x63000010002f0005c0001b0004a00018, 0x300006000600002a0005a0001d00021, 0x400051000580003500062000500001d],
    [0x2d000030004c0003300018000210001d, 0x510000b000420005f0004a0001d00050, 0x61000420005e0005e0001b0005a00062, 0x43000050001b000250005c0002a00035, 0x25000040003a000280002f0006000058, 0xe000100000b00009000010000600051, 0x32000500001300006000630000300004],
    [0xa0001c000180001f0004f000590005b, 0x900002000560002e000220002200037, 0x1000620000d000050001d0003300045, 0x5b0004100050000590000b0005e00035, 0x4900050000050004a00053000090003e, 0x3b00011000040004a000000005500062, 0x5500061000150005300004000440004a],
    [0x5b0003700045000350003e000620004a, 0x5900022000330005e000090005500044, 0x4f000220001d0000b000530000000004, 0x1f0002e00005000590004a0004a00053, 0x18000560000d00050000050000400015, 0x1c000020006200041000500001100061, 0xa00009000010005b000490003b00055],
    [0x500002e00059, 0x100004000011, 0x600003400051],
    [0x590001100051, 0x2e0004000034, 0x500001000060],
    [0x5f000420005f, 0x43000240004a, 0x36000460001a],
    [0x5f0004a0001a, 0x420002400046, 0x5f0004300036],
    [0x5c00031000280005a0002b0006300006, 0x3e000330002e0003e000640001c00013, 0x140002f000300003d000520002e0003e]⟩

private theorem tripleCert_3_ok : checkTripleCert tripleCert_3 = true := by decide

private def tripleCert_4 : PackedTripleCert where
  n0 := 0
  n1 := 2
  n2 := 3
  M_rows := [0x80002b00031000380003a0003b000110003a0006300028000510003c000150004a000220003600052000300003700035, 0x1500042000160004e000170000d0005100057000340002a000420003900016000260005600036000180005b000370004b, 0x270005c0003e0004a0002000033000480002100057000020005000048000050001e000180001b0000100030000210001b, 0x210002d0000c00026000590004f00020000280005100021000400003c0000b00011000000003400026000520005200052, 0x360001800002000640004300000000550001000004000150005400028000250004500040000480004c00058000240005c, 0x52000620000200018000530003f00037000180000a0002b0001a0004b0004e0000b0002c0002900021000470002d00057, 0x4a000170002e00022000490003c0002a000510002f00027000480003c000150001200020000170004f000140006400063, 0x350004b0002e0003c0003900012000320005d0005c0000b000140004c0001e00040000610001c00003000540000d00032, 0x160000b0004b0000d000640003e000520005000022000150005f000120003d000060000600058000170003b0000f00052, 0x49000540001e0004e0005000028000550001c0004300023000230005700044000160004b0005900026000420003600061, 0x550003f000360001c0004f0005100002000370001a00000000450005e0001500004000430005d000190004e0000b0001a, 0x3f000630004f000070002c0000d000590000600015000140002300055000260001500017000150000d000090002900031, 0x2e0005600008000630004b000020002f000370001c0000d00055000140000a00026000150002a00052000390005500052, 0x3600026000640000100059000400005300052000210005c000030003a0005f0004a000300001800058000160005900020, 0xa00042000270003800021000460000500061000330004d0000c00048000560002b000200004000015000600005c00036, 0x4e0002c0000f00022000240003e000230002d0003a000640002e0005a0003b0003a000010005000057000220003c0003a, 0x3b0000200050000060005e00048000620001f0005d000030005a0003300043000520000c00064000010000d0006200041, 0x400022000580005a00000000570003700025000100000e0004d000310005c00041000330000c000640004a000070004e, 0xf0000f000070005400043000600003600059000310001c0001f0003a0000f0005a0005c0002c0001500039000460000d, 0x2400062000580002d0000e0006400017000540004800053000280003a000640002d0004200008000330001a000040003d]
  M_cols := [0x350004b0001b000520005c00057000630003200052000610001a000310005200020000360003a000410004e0000d0003d, 0x37000370002100052000240002d000640000d0000f000360000b0002900055000590005c0003c00062000070004600004, 0x300005b0003000052000580004700014000540003b000420004e00009000390001600060000220000d0004a000390001a, 0x520001800001000260004c000210004f000030001700026000190000d0005200058000150005700001000640001500033, 0x36000360001b000340004800029000170001c00058000590005d000150002a000180004000050000640000c0002c00008, 0x22000560001800000000400002c0002000061000060004b0004300017000150003000020000010000c000330005c00042, 0x4a000260001e00011000450000b000120004000006000160000400015000260004a0002b0003a00052000410005a0002d, 0x1500016000050000b000250004e000150001e0003d0004400015000260000a0005f000560003b000430005c0000f00064, 0x3c00039000480003c000280004b0003c0004c00012000570005e00055000140003a000480005a00033000310003a0003a, 0x51000420005000040000540001a00048000140005f00023000450002300055000030000c0002e0005a0004d0001f00028, 0x280002a0000200021000150002b000270000b000150002300000000140000d0005c0004d00064000030000e0001c00053, 0x63000340005700051000040000a0002f0005c00022000430001a000150001c00021000330003a0005d000100003100048, 0x3a0005700021000280001000018000510005d000500001c00037000060003700052000610002d0001f000250005900054, 0x1100051000480002000055000370002a00032000520005500002000590002f00053000050002300062000370003600017, 0x3b0000d000330004f000000003f0003c000120003e00028000510000d0000200040000460003e00048000570006000064, 0x3a0001700020000590004300053000490003900064000500004f0002c0004b0005900021000240005e00000000430000e, 0x380004e0004a000260006400018000220003c0000d0004e0001c0000700063000010003800022000060005a000540002d, 0x31000160003e0000c00002000020002e0002e0004b0001e000360004f0000800064000270000f00050000580000700058, 0x2b000420005c0002d0001800062000170004b0000b000540003f000630005600026000420002c00002000220000f00062, 0x800015000270002100036000520004a000350001600049000550003f0002e000360000a0004e0003b000040000f00024]
  Minv_rows := [0x4b0002b00032000520004d0000e0000c00037000150005b000310004900063000180001200001000560000d0001b00010, 0x370001900036000500005e0003300030000400004f000320003c0003e00007000440002e0004b0005c00046000070002e, 0x29000370004a000400001c0005f00048000480000f00044000480002c0003f000070004e000160005e000050001100064, 0x58000640005f0004f000570004c0000c0005e0005a000600002300051000540004c000350000400046000420005c0002e, 0x150003c0006300034000490001d0002d0003400042000120003100037000640002100053000360004a0004c0003400037, 0x51000480004e0005f0000e00009000080001a000390006200046000430000500018000580003a0002e0000c0005500056, 0x2b000390002d000170005e000630000f0001c00012000480004500008000370000e000290001c0005a0005d0005400042, 0x1c0005e0006200004000640002400017000520002f0001f0001d0002d0002d0005f000180005300064000550003a00060, 0x60000d00060000100005c000300000400045000130001c000380002c0005e00050000480006000010000250003500061, 0x2300003000570005b0003a000340005800006000170001d000380004c000380001e0002b0004d0003a0004b000010002b, 0xa000010000800002000480000c0000b0001e0000400021000010002d000020002a000080005f0005c000590002900021, 0x1d0004300004000530003d0000400012000000000d000330005b000300005a0005d000240004a000050004d0000e00029, 0x5e000380003a0005f0003a0002600044000440000e0001e0004e0004c000280003700064000170004e0001e0000500009, 0x4a00000000460002d0000b000320004c0003300044000200006100063000180004b0005d0003b0001f0001b0000b00030, 0x180004e0001800007000020004900034000120002e0003f0005a000250003e000430004e0001900051000340004100024, 0x4c0003c0002c000150002b0004800054000380005d0004a0004200001000490002b00000000010005c0001d000550003c, 0x130000f00030000180003e00045000420004b0001a0004000014000050001c000430003b0003a00009000430001700026, 0x360002d000310001c0005500006000040002200046000320002c0005800026000490003c0001e0002e000350002c0001e, 0x550004600044000280003b0000600040000090002f000580002e0003c00022000120003b000520002f0004e000400005f, 0x180004600064000070003d000080005700055000340003100029000210000c00058000010003100054000570005a00024]
  Minv_cols := [0x100002e000640002e00037000560004200060000610002b00021000290000900030000240003c000260001e0005f00024, 0x1b00007000110005c0003400055000540003a0003500001000290000e000050000b0004100055000170002c000400005a, 0xd0004600005000420004c0000c0005d00055000250004b000590004d0001e0001b000340001d00043000350004e00057, 0x560005c0005e000460004a0002e0005a00064000100003a0005c000050004e0001f000510005c000090002e0002f00054, 0x10004b0001600004000360003a0001c00053000600004d0005f0004a000170003b00019000010003a0001e0005200031, 0x120002e0004e0003500053000580002900018000480002b0000800024000640005d0004e000000003b0003c0003b00001, 0x1800044000070004c00021000180000e0005f000500001e0002a0005d000370004b000430002b00043000490001200058, 0x63000070003f000540006400005000370002d0005e00038000020005a00028000180003e000490001c00026000220000c, 0x490003e0002c000510003700043000080002d0002c0004c0002d000300004c00063000250000100005000580003c00021, 0x310003c00048000230003100046000450001d0003800038000010005b0004e000610005a00042000140002c0002e00029, 0x5b0003200044000600001200062000480001f0001c0001d00021000330001e000200003f0004a00040000320005800031, 0x150004f0000f0005a0004200039000120002f0001300017000040000d0000e000440002e0005d0001a000460002f00034, 0x3700040000480005e000340001a0001c0005200045000060001e00000000440003300012000380004b000220000900055, 0xc00030000480000c0002d000080000f0001700004000580000b00012000440004c000340005400042000040004000057, 0xe000330005f0004c0001d00009000630002400030000340000c000040002600032000490004800045000060000600008, 0x4d0005e0001c00057000490000e0005e000640005c0003a000480003d0003a0000b000020002b0003e000550003b0003d, 0x5200050000400004f000340005f0001700004000100005b00002000530005f0002d0000700015000180001c0002800007, 0x32000360004a0005f000630004e0002d00062000600005700008000040003a00046000180002c00030000310004400064, 0x2b0001900037000640003c00048000390005e0000d00003000010004300038000000004e0003c0000f0002d0004600046, 0x4b00037000290005800015000510002b0001c00006000230000a0001d0005e0004a000180004c00013000360005500018]
  b0 := ⟨0,
    [0x5a00049000210004200052000550001c, 0x430004e000560006000016000320003b, 0x610001a00013000380004c0003a00050, 0x1300048000470004900056000400003e, 0x5b0001f000080001e0001f0002c00050, 0x54000130004a00008000400000a00044, 0x3b000510001a00033000100002a00033],
    [0x1c0003b000500003e000500004400033, 0x55000320003a000400002c0000a0002a, 0x52000160004c000560001f0004000010, 0x420006000038000490001e0000800033, 0x21000560001300047000080004a0001a, 0x490004e0001a000480001f0001300051, 0x5a0004300061000130005b000540003b],
    [0x1d000090002f0000f000260000b0004d, 0x50000390004e0000a0000f000290002d, 0x1c0003800033000110005f0005f00031, 0x5d0005e0006300029000020002500036, 0x340000a00016000520002f000140005f, 0x350003b0001f000080001d0004e0004a, 0x4b0001e00056000100005b000350005a],
    [0x4d0002d00031000360005f0004a0005a, 0xb000290005f00025000140004e00035, 0x260000f0005f000020002f0001d0005b, 0xf0000a0001100029000520000800010, 0x2f0004e0003300063000160001f00056, 0x900039000380005e0000a0003b0001e, 0x1d000500001c0005d00034000350004b],
    [0x50005f00034, 0x350003100015, 0x2c0003c00007],
    [0x340001500007, 0x5f000310003c, 0x5000350002c],
    [0x24000280002f, 0x130002100059, 0xc0004400002],
    [0x2f0005900002, 0x280002100044, 0x24000130000c],
    [0x24000140002c00004000430005f00017, 0x3800038000370001600051000640005e, 0x11000540002000052000520005e00035]⟩
  b1 := ⟨2,
    [0x2b0002f00025000520003a0005200020, 0x390004d0004b0003c000460000400000, 0x3400006000330000e000580005800050, 0x39000340005a0000a0005f0001b0000a, 0x54000540003900039000600000700061, 0x51000500003c00045000330005900044, 0x170005900015000010005c0005500018],
    [0x2000000000500000a000610004400018, 0x5200004000580001b000070005900055, 0x3a00046000580005f00060000330005c, 0x520003c0000e0000a000390004500001, 0x250004b000330005a000390003c00015, 0x2f0004d0000600034000540005000059, 0x2b000390003400039000540005100017],
    [0x5e00047000620003200059000590002a, 0x640000f0004900001000000003a00055, 0x27000160005d0001a000200005400064, 0x5400052000080000000027000320002d, 0x4b000460005000027000510000a00059, 0x56000170005e0002a000120004f00011, 0x150001e0002c0002e000330002900018],
    [0x2a00055000640002d000590001100018, 0x590003a00054000320000a0004f00029, 0x59000000002000027000510001200033, 0x32000010001a00000000270002a0002e, 0x62000490005d00008000500005e0002c, 0x470000f000160005200046000170001e, 0x5e0006400027000540004b0005600015],
    [0x450003a00012, 0xb0001e0002b, 0x20002600001],
    [0x120002b00001, 0x3a0001e00026, 0x450000b00002],
    [0x110002e00050, 0x5f0003000036, 0x50004b0002d],
    [0x50000360002d, 0x2e000300004b, 0x110005f00005],
    [0x2e0005d0005c000480003a0001c0005a, 0x110004f000480002a000290005e0002b, 0x230000f000250001f0004a0005e0002a]⟩
  b2 := ⟨3,
    [0x1b000330001300008000230002400051, 0x12000020003e0005100021000470002c, 0x2b0002e0001c0004b000640002000064, 0x480002100060000050000a0001700012, 0x35000320000d000060005e000460004c, 0x480005200042000420004c0000c00060, 0x41000180005700039000530004200030],
    [0x510002c00064000120004c0006000030, 0x24000470002000017000460000c00042, 0x2300021000640000a0005e0004c00053, 0x8000510004b00005000060004200039, 0x130003e0001c000600000d0004200057, 0x33000020002e00021000320005200018, 0x1b000120002b00048000350004800041],
    [0x44000050004f0000300016000280004d, 0x150003a000450005d00043000210002a, 0x5e0005a0002900019000290001200014, 0x4900038000580005e000610001c00024, 0x57000250003e0001e0000e0004300012, 0x1b0000c000230005e0005f0004800018, 0x240000a000020002a000470000e00000],
    [0x4d0002a0001400024000120001800000, 0x2800021000120001c00043000480000e, 0x160004300029000610000e0005f00047, 0x30005d000190005e0001e0005e0002a, 0x4f0004500029000580003e0002300002, 0x50003a0005a00038000250000c0000a, 0x44000150005e00049000570001b00024],
    [0x4a0006200017, 0x30002700046, 0x350005d0002d],
    [0x17000460002d, 0x62000270005d, 0x4a0000300035],
    [0x4b0002800011, 0x5a0001c0005a, 0x90001000053],
    [0x110005a00053, 0x280001c00010, 0x4b0005a00009],
    [0x450000f00027000130005d0005e00007, 0x4000300001200048000250004c00049, 0x520005900057000160002b0000e0005b]⟩

private theorem tripleCert_4_ok : checkTripleCert tripleCert_4 = true := by decide

private def tripleCert_5 : PackedTripleCert where
  n0 := 0
  n1 := 2
  n2 := 4
  M_rows := [0x80003200062000310003e00029000220003700038000470002f000330005d000230003c000460005c000070002c0003c, 0x5200048000520003e000050002c0001f000400000d0002b00020000010002500022000450001000043000480001a00004, 0x190003b000120003e000540000d000180004b0000200015000370004c0003300027000220005e0004400006000410004a, 0x570004800037000500002f00064000080002f00045000050002c00022000050005e0000f000630000a000190002900026, 0x3a0001f0000900032000150004400041000390000b0004e000270002e000130005d000420001300048000400001b00040, 0x2b000140002600059000110001f0005300028000070005a0000e000080003f00047000260002a000130002f0004400025, 0x800022000560002e000110002400051000420002d0000b0000f000230001c0002c000340002100020000340004a00061, 0x70000b0002b000360003500062000370005500045000270003e000080004c000530003600002000030004f0006200038, 0x2000051000250002f000060002f0004a0001b0002f0004900000000220005500024000560002e00053000630003200045, 0x4b000010000a0000f000280001c000300005800043000260005c0003a0005e0005b00048000550004c00045000510005f, 0x610003c0003500026000350002600034000160005c0000f000430003200051000210005f00021000120000e0000900042, 0x2f000370005d0005000061000330002c0005c0002c0003500048000000004a0003300039000130000a000460000c0004c, 0x32000070001d000050005e0004b0004b0002b0001400049000220000c00031000620002f00015000090003d0003b0000c, 0x41000450000f00004000440006000011000600003300045000620004e0001a00051000390000c00042000400005200023, 0x33000290004e0005e00022000350003a000550003100019000600002d0002200031000070000d0004a000290004d00002, 0x570003f00058000140004c0001c0002000036000220002a00046000540004b0003a0001d0001600030000560003000043, 0x2200012000460001a000090004e0001c0001a0002e000260003b0003900057000370002a0003d0004a000310003c00002, 0xd0005f000480005a0000b0000b00032000480001c0002e000620003a00040000490001c0004200016000090003800039, 0x2d000120000e000210001c0001c000220006000060000610001f0005e00026000310000c0003200007000240001500021, 0x6000030000120003e00040000170005e00064000280003c0004f000020003e0005700015000600002f0004a000260002b]
  M_cols := [0x3c000040004a0002600040000250006100038000450005f000420004c0000c0002300002000430000200039000210002b, 0x2c0001a00041000290001b000440004a000620003200051000090000c0003b000520004d000300003c000380001500026, 0x7000480000600019000400002f000340004f00063000450000e000460003d0004000029000560003100009000240004a, 0x5c00043000440000a00048000130002000003000530004c000120000a00009000420004a000300004a00016000070002f, 0x46000100005e00063000130002a00021000020002e000550002100013000150000c0000d000160003d000420003200060, 0x3c00045000220000f0004200026000340003600056000480005f000390002f00039000070001d0002a0001c0000c00015, 0x2300022000270005e0005d000470002c00053000240005b00021000330006200051000310003a00037000490003100057, 0x5d000250003300005000130003f0001c0004c000550005e000510004a000310001a000220004b0005700040000260003e, 0x33000010004c000220002e000080002300008000220003a00032000000000c0004e0002d00054000390003a0005e00002, 0x2f00020000370002c000270000e0000f0003e000000005c0004300048000220006200060000460003b000620001f0004f, 0x470002b00015000050004e0005a0000b0002700049000260000f000350004900045000190002a000260002e000610003c, 0x380000d00002000450000b000070002d000450002f000430005c0002c000140003300031000220002e0001c0006000028, 0x37000400004b0002f000390002800042000550001b00058000160005c0002b0006000055000360001a000480006000064, 0x220001f0001800008000410005300051000370004a00030000340002c0004b000110003a000200001c00032000220005e, 0x290002c0000d00064000440001f00024000620002f0001c00026000330004b00060000350001c0004e0000b0001c00017, 0x3e00005000540002f00015000110001100035000060002800035000610005e00044000220004c000090000b0001c00040, 0x310003e0003e0005000032000590002e000360002f0000f000260005000005000040005e000140001a0005a000210003e, 0x620005200012000370000900026000560002b000250000a000350005d0001d0000f0004e0005800046000480000e00012, 0x32000480003b000480001f00014000220000b00051000010003c000370000700045000290003f000120005f0001200030, 0x80005200019000570003a0002b0000800007000200004b000610002f00032000410003300057000220000d0002d00060]
  Minv_rows := [0x580000700049000350002000020000580004d00034000110002c0000c000380005d0003800035000470003b0005b00037, 0x3c000320002e00043000370002d000150003f000170005300007000260005700006000220000000051000400002800022, 0x5800029000280004c0005a000130002e0002300015000250001800003000470003c0005c0000a0005e000170003900048, 0x3e000540003c0003100015000640000b0004d0000400038000130003f00001000620002f000510005b0001c0005000043, 0x220001500030000190001a00024000400000600039000590002c000030003c00012000080002a000610004b000450005a, 0x2000005000420001c000610003d0004d0001c000520003f000600000a00051000120000f0005f0002d000320003800032, 0x220001a00023000070001e000130002b000470001600039000350003600001000080005f000450005000035000550002f, 0x5c000160002c0003b0003f0001c0004a00015000350002f00042000510001a000600001a0001c0002400012000420002f, 0x5c0002c0003d0003f000630003e000260004c00031000410002c000450006100037000510004e00000000460000b00024, 0x41000210004c000350004f0002e0003100018000330004000060000580004d00058000640002d0004500025000090005b, 0xb000430001600011000230004c000400005800016000300001e0002d00058000340005a0001b000610004b000520004f, 0x4400032000380002c0005d0005d00028000190006100034000550001b000570001400016000600003500023000180001c, 0x58000440000d0000c0002e000110004b000150001a0002800014000010001f0002b000350000a0003e000280001100017, 0x2e0004a000340004000036000220005f000010005a0003300058000620000b00007000470001d0001b0004d0004300014, 0x5f0002b000050005a0003d0004b0005100029000160002200011000290001c0000a00064000520001a0004b0003200043, 0x2600059000420002b0003d0001c000410002e000060005a00002000100005700037000000001e000580003a0000600046, 0x1d000410001300001000470002b0001c000300001400062000480002c0000a000380005a0002b0003a000180004200014, 0x1f0003e0000300008000500000b000430004e0000e000030006200002000190002d000330004b0005a000160006000063, 0x2c0005800024000270004100039000050000d00003000560001b0001f00032000100005f000510000c00020000200003f, 0x53000420005c0002a0002600008000050000f0004900017000330001e0003100015000190004700049000400003100018]
  Minv_cols := [0x370002200048000430005a000320002f0002f000240005b0004f0001c0001700014000430004600014000630003f00018, 0x5b000280003900050000450003800055000420000b0000900052000180001100043000320000600042000600002000031, 0x3b00040000170001c0004b00032000350001200046000250004b00023000280004d0004b0003a00018000160002000040, 0x47000510005e0005b000610002d0005000024000000004500061000350003e0001b0001a000580003a0005a0000c00049, 0x35000000000a000510002a0005f000450001c0004e0002d0001b000600000a0001d000520001e0002b0004b0005100047, 0x38000220005c0002f000080000f0005f0001a00051000640005a00016000350004700064000000005a000330005f00019, 0x5d000060003c0006200012000120000800060000370005800034000140002b000070000a00037000380002d0001000015, 0x380005700047000010003c00051000010001a000610004d00058000570001f0000b0001c000570000a000190003200031, 0xc00026000030003f000030000a000360005100045000580002d0001b000010006200029000100002c000020001f0001e, 0x2c0000700018000130002c0006000035000420002c000600001e000550001400058000110000200048000620001b00033, 0x11000530002500038000590003f000390002f000410004000030000340002800033000220005a00062000030005600017, 0x3400017000150000400039000520001600035000310003300016000610001a0005a0001600006000140000e0000300049, 0x4d0003f000230004d000060001c00047000150004c0001800058000190001500001000290002e000300004e0000d0000f, 0x58000150002e0000b000400004d0002b0004a000260003100040000280004b0005f00051000410001c000430000500005, 0x200002d0001300064000240003d000130001c0003e0002e0004c0005d00011000220004b0001c0002b0000b0003900008, 0x20000370005a000150001a000610001e0003f000630004f000230005d0002e000360003d0003d00047000500004100026, 0x35000430004c00031000190001c000070003b0003f00035000110002c0000c000400005a0002b0000100008000270002a, 0x490002e000280003c0003000042000230002c0003d0004c00016000380000d0003400005000420001300003000240005c, 0x700032000290005400015000050001a000160002c000210004300032000440004a0002b00059000410003e0005800042, 0x580003c000580003e0002200020000220005c0005c000410000b00044000580002e0005f000260001d0001f0002c00053]
  b0 := ⟨0,
    [0x5e000270000d0003e00063000400001a, 0x24000010001f0002d000400003300020, 0x380000c0004f000210004a0003400024, 0x35000290002d0000a000440000700047, 0x550000c0001e000500005d0005f00063, 0x4e000380004900012000490001f0005d, 0x17000150001e0002d000330005e00002],
    [0x1a000200002400047000630005d00002, 0x400003300034000070005f0001f0005e, 0x63000400004a000440005d0004900033, 0x3e0002d000210000a00050000120002d, 0xd0001f0004f0002d0001e000490001e, 0x27000010000c000290000c0003800015, 0x5e000240003800035000550004e00017],
    [0x46000030005d0003f0002c0001800033, 0x15000290002a00051000340000200029, 0x47000420002c000460003f0001c00037, 0x2700035000560001e00015000250000b, 0x43000340002c0004c0005a0001500044, 0x310005700015000070003f0004300041, 0x4e0004c00012000490000c0001100051],
    [0x3300029000370000b000440004100051, 0x18000020001c00025000150004300011, 0x2c000340003f000150005a0003f0000c, 0x3f00051000460001e0004c0000700049, 0x5d0002a0002c000560002c0001500012, 0x300029000420003500034000570004c, 0x4600015000470002700043000310004e],
    [0x1a000280003e, 0x46000200003a, 0x270000b00044],
    [0x3e0003a00044, 0x28000200000b, 0x1a0004600027],
    [0x18000530001c, 0x40000030001c, 0x170000f00041],
    [0x1c0001c00041, 0x53000030000f, 0x180004000017],
    [0x4d00022000430001c00016000260002a, 0x2000052000210005b000170005500039, 0xb00018000510003a000090000700028]⟩
  b1 := ⟨2,
    [0x20001e0000900058000130005e00004, 0x370002f0002e0003d000460005a00014, 0x430003800000000150000f000600005e, 0x4500030000430000e0002f0003200056, 0x490003e000190002d000000003500061, 0x54000180002f0001b0005b0005b00025, 0x4a000380002d0005c000090000600053],
    [0x4000140005e00056000610002500053, 0x5e0005a0006000032000350005b00006, 0x13000460000f0002f000000005b00009, 0x580003d000150000e0002d0001b0005c, 0x90002e0000000043000190002f0002d, 0x1e0002f00038000300003e0001800038, 0x200037000430004500049000540004a],
    [0x29000280003d00045000410002600021, 0x14000500000f0002c000600005800042, 0x36000270005600006000570004f00033, 0x570005c000150004b000530003700010, 0xb0000c0001c0000f000560002e00013, 0x4a00057000560000f000570005600018, 0x5d0001c00038000350002d0003b00061],
    [0x21000420003300010000130001800061, 0x26000580004f000370002e000560003b, 0x4100060000570005300056000570002d, 0x450002c000060004b0000f0000f00035, 0x3d0000f00056000150001c0005600038, 0x2800050000270005c0000c000570001c, 0x290001400036000570000b0004a0005d],
    [0x1f000290005b, 0x62000290003b, 0x260000400033],
    [0x5b0003b00033, 0x290002900004, 0x1f0006200026],
    [0x1b0004a00031, 0x280000e00018, 0x22000400002e],
    [0x31000180002e, 0x4a0000e00040, 0x1b0002800022],
    [0x30000590001f0000c00062000540003a, 0xc000530005400045000310003400059, 0x2d0000c00050000530002f000420003c]⟩
  b2 := ⟨4,
    [0x80002000019000250003b0003f00056, 0x4e0004600055000510001b0005f00051, 0x5b0000e0000d00053000380002a00047, 0x1a0000b0000b000110000f000510004d, 0x3900056000210006400046000530000d, 0x60000610001c00049000110006300061, 0x250004e00052000200006000007],
    [0x5600051000470004d0000d0006100007, 0x3f0005f0002a00051000530006300060, 0x3b0001b000380000f000460001100020, 0x25000510005300011000640004900052, 0x19000550000d0000b000210001c0004e, 0x20000460000e0000b000560006100025, 0x80004e0005b0001a000390006000000],
    [0x1000480005e00061000080003900004, 0x1a000600004200013000520004f0002f, 0x160002e0000e00027000420005b0003a, 0x53000010000d00060000270004100015, 0x46000320002a00031000600004600060, 0x410000d000140003f00018000090002d, 0x3c0000100034000390003d0003300022],
    [0x40002f0003a00015000600002d00022, 0x390004f0005b00041000460000900033, 0x800052000420002700060000180003d, 0x61000130002700060000310003f00039, 0x5e000420000e0000d0002a0001400034, 0x48000600002e00001000320000d00001, 0x10001a000160005300046000410003c],
    [0x15000430004f, 0x3e000490000d, 0x130001200004],
    [0x4f0000d00004, 0x430004900012, 0x150003e00013],
    [0x21000310005a, 0x170003d00036, 0x430000100064],
    [0x5a0003600064, 0x310003d00001, 0x210001700043],
    [0xf0003600004000220002e0001700036, 0x6400039000040005f000150004200004, 0xf0005e0002f0006200059000490002f]⟩

private theorem tripleCert_5_ok : checkTripleCert tripleCert_5 = true := by decide

private def tripleCert_6 : PackedTripleCert where
  n0 := 0
  n1 := 2
  n2 := 5
  M_rows := [0x4b0003c0005400002000130005e00050000000003300024000510005e0002a000270001c000430005d00062000470002d, 0x270004d0006000017000560000c0003e0002800011000020000a0004300024000560000a0005500037000090001100055, 0x800059000090003d0005a0002c0004000054000030002000005000500000c0004e00027000390005d000490002e0004f, 0x500003f000640000100058000200004d0003500005000060002c0002f0003a0004a00019000140004c000500000b00018, 0x550000000063000370002200010000140002d0001f0006200055000200001a0001900042000230001f000330000700013, 0x90000c0000c0000f00017000010002e000250003300060000450000e00012000370004a0006400046000300002100022, 0x52000430005d0003400005000130003900052000200000600044000130001e0001c0002b000120000f00010000190004b, 0x10000000008000320004e000030001b0001500047000070005b00060000060006100047000310003f00055000550002e, 0x160003d000460000c00011000000001e00052000600000a00050000450002e0004c000470004b0002e000560001b0004e, 0x1200043000600005c0001f0005a0004e0004f0003e0004800062000300003e00060000480001a00055000110000f00013, 0xf000640003a00049000300006100012000370002d0005b0000d0002100061000250003c00016000420005e0005800037, 0x37000220002000047000090003a000270001700045000090003e00017000210004e0000a00031000590002f0005200027, 0x39000140002800044000210003e000490001800026000430000a0005c000050003d0002f0005f00061000570002b0005b, 0x1b0001000022000190005d00038000210005a00064000460001a00061000330004b0001c000410002500028000540000a, 0x320000c000220001e0003f0001500010000500005300049000370002b00005000250002e00026000080004b000540002b, 0x4a000340002f000190004c00021000480000300027000150005f0001a0002e0004d0003e00011000290001f0001c00039, 0x4a00027000580002100025000560004f0004800000000070001800008000330002500052000520005e0000a0002100018, 0x1c0005d0005800047000460005b00048000200001b000080004f00016000170004c000630005e00060000190004400018, 0xa000400000e000120004200058000370004b0002c000420005200008000320003400014000090003b0002e0001a00018, 0x6400008000220003800025000640000500027000330002500058000570003400006000380001c0000e000430005f00064]
  M_cols := [0x2d000550004f0001800013000220004b0002e0004e0001300037000270005b0000a0002b0003900018000180001800064, 0x47000110002e0000b000070002100019000550001b0000f00058000520002b00054000540001c00021000440001a0005f, 0x620000900049000500003300030000100005500056000110005e0002f00057000280004b0001f0000a000190002e00043, 0x5d000370005d0004c0001f000460000f0003f0002e000550004200059000610002500008000290005e000600003b0000e, 0x43000550003900014000230006400012000310004b0001a00016000310005f000410002600011000520005e000090001c, 0x1c0000a0002700019000420004a0002b0004700047000480003c0000a0002f0001c0002e0003e00052000630001400038, 0x27000560004e0004a00019000370001c000610004c00060000250004e0003d0004b000250004d000250004c0003400006, 0x2a000240000c0003a0001a000120001e000060002e0003e00061000210000500033000050002e00033000170003200034, 0x5e00043000500002f000200000e0001300060000450003000021000170005c000610002b0001a00008000160000800057, 0x510000a000050002c0005500045000440005b00050000620000d0003e0000a0001a000370005f000180004f0005200058, 0x24000020002000006000620006000006000070000a000480005b000090004300046000490001500007000080004200025, 0x330001100003000050001f000330002000047000600003e0002d0004500026000640005300027000000001b0002c00033, 0x2800054000350002d000250005200015000520004f0003700017000180005a000500000300048000200004b00027, 0x500003e000400004d000140002e000390001b0001e0004e0001200027000490002100010000480004f000480003700005, 0x5e0000c0002c0002000010000010001300003000000005a000610003a0003e000380001500021000560005b0005800064, 0x13000560005a000580002200017000050004e000110001f0003000009000210005d0003f0004c00025000460004200025, 0x2000170003d00001000370000f00034000320000c0005c000490004700044000190001e0001900021000470001200038, 0x54000600000900064000630000c0005d0000800046000600003a000200002800022000220002f00058000580000e00022, 0x3c0004d000590003f000000000c00043000000003d00043000640002200014000100000c00034000270005d0004000008, 0x4b0002700008000500005500009000520000100016000120000f00037000390001b000320004a0004a0001c0000a00064]
  Minv_rows := [0x450003500048000580003a000140001f00009000040003d000430005b0005d0003c0002e000290003c000330005a00009, 0xa0002f000130003300038000400003d0005b000260000500047000400004100043000450002c00056000600004e00058, 0x7000040003b0005e0003c000090000e0004b0003f00041000030000800033000020004e0001f0001000030000190000a, 0x600004d000480003b000570002f000630003c000060002c000040004a0001a0000e0000c000220000d000140004f00025, 0x90004700043000290001c0003f0000b0000d00061000260000600042000320005d000420004b000590001d000400001b, 0x2d00012000380002f000320003700053000110002d0006200045000440003f0000a00033000110005e000380000200053, 0xb0002e000160001700047000070000f0004a0005a0000900025000230005b0003b0004d0001b0000e00043000410002f, 0x1b00031000260002f0004700029000260002b0002c000050004c0001c000070000500006000250001a000220000f00025, 0x2e00036000640003d00019000070005800052000580000800059000450006300056000170005f0004a000620002400061, 0x450004d00031000480005900041000560003a00045000070005d000330003700015000210002900062000060005800007, 0x45000550003c0003000013000280001a00046000360003b0004b0001600062000020005d0000c0003d000600004100027, 0x1e0004d0004f0002300055000320002f0004500046000560002300033000560003d0005a0000e0002e0005d0003300009, 0x130000500011000180003d0004e00030000610000d0004f000010000f0000c0006400024000030001c00000000630003b, 0x350001c00009000630002900028000170003d000310005a0002c0005400006000600003a0004c0004c0002c0005300064, 0x580001c0001b000410001100015000420000c0005b00050000030000a0005500033000550002800010000140001600016, 0x4b0001d00026000290004200015000550002a0002500026000540003600029000240005f0005e0003a0004f000500003d, 0x500001f00056000020001e000130005e0005d000550000e000640004a0001e000350005e0000a00010000500005900034, 0x58000520005900019000350004b0002b0004a00011000140000a0001300048000610004800013000180003b0003500054, 0x2400022000260002900034000210003b000020004f0001300032000190003c0005c0003f00005000260000f0002e00047, 0x17000290005000030000250003400002000110002b0002a00054000080004800027000190002d00005000080006000058]
  Minv_cols := [0x9000580000a000250001b000530002f00025000610000700027000090003b00064000160003d00034000540004700058, 0x5a0004e000190004f0004000002000410000f000240005800041000330006300053000160005000059000350002e00060, 0x330006000030000140001d0003800043000220006200006000600005d000000002c000140004f000500003b0000f00008, 0x3c00056000100000d000590005e0000e0001a0004a000620003d0002e0001c0004c000100003a00010000180002600005, 0x290002c0001f000220004b000110001b000250005f000290000c0000e000030004c000280005e0000a00013000050002d, 0x2e000450004e0000c00042000330004d0000600017000210005d0005a000240003a000550005f0005e000480003f00019, 0x3c00043000020000e0005d0000a0003b000050005600015000020003d0006400060000330002400035000610005c00027, 0x5d00041000330001a000320003f0005b00007000630003700062000560000c0000600055000290001e000480003c00048, 0x5b00040000080004a0004200044000230001c000450003300016000330000f000540000a000360004a000130001900008, 0x430004700003000040000600045000250004c000590005d0004b00023000010002c0000300054000640000a0003200054, 0x3d00005000410002c0002600062000090000500008000070003b000560004f0005a00050000260000e00014000130002a, 0x4000260003f00006000610002d0005a0002c000580004500036000460000d000310005b0002500055000110004f0002b, 0x90005b0004b0003c0000d000110004a0002b000520003a0004600045000610003d0000c0002a0005d0004a0000200011, 0x1f0003d0000e000630000b000530000f0002600058000560001a0002f000300001700042000550005e0002b0003b00002, 0x1400040000090002f0003f000370000700029000070004100028000320004e000280001500015000130004b0002100034, 0x3a000380003c000570001c000320004700047000190005900013000550003d0002900011000420001e000350003400025, 0x58000330005e0003b000290002f000170002f0003d0004800030000230001800063000410002900002000190002900030, 0x48000130003b000480004300038000160002600064000310003c0004f00011000090001b0002600056000590002600050, 0x350002f000040004d00047000120002e00031000360004d000550004d000050001c0001c0001d0001f000520002200029, 0x450000a0000700060000090002d0000b0001b0002e00045000450001e0001300035000580004b00050000580002400017]
  b0 := ⟨0,
    [0x40005b0003700027000060004200047, 0xe00001000330001100000000430005f, 0xa0002700034000190003c0001100046, 0x490005c0002200002000630005500032, 0x590002f0003500004000580003600032, 0x240001f0006000027000020001c0001a, 0x3100063000090002700005000250002e],
    [0x470005f0004600032000320001a0002e, 0x42000430001100055000360001c00025, 0x6000000003c00063000580000200005, 0x27000110001900002000040002700027, 0x37000330003400022000350006000009, 0x5b00001000270005c0002f0001f00063, 0x40000e0000a00049000590002400031],
    [0x35000600005f0004e000560000500046, 0x800047000600005900026000130003f, 0x520005e000340002500054000500002c, 0x400005c000260003f000630006100049, 0x2d0003600040000480005f0003100053, 0x10004400017000480003e0005700046, 0x590003b0001d0005600030000140005a],
    [0x460003f0002c0004900053000460005a, 0x5000130005000061000310005700014, 0x560002600054000630005f0003e00030, 0x4e00059000250003f000480004800056, 0x5f00060000340002600040000170001d, 0x60000470005e0005c00036000440003b, 0x350000800052000400002d0000100059],
    [0x1b0005400017, 0x15000530002b, 0x230003e0003d],
    [0x170002b0003d, 0x54000530003e, 0x1b0001500023],
    [0x5e000400004f, 0x530003b00038, 0x2f0002300045],
    [0x4f0003800045, 0x400003b00023, 0x5e000530002f],
    [0x4e000070000f00023000290005700012, 0x22000190002d00014000330003d00052, 0xe000200003d0004a000450001100045]⟩
  b1 := ⟨2,
    [0x3c000500001a0005a000230006400002, 0x3600032000560005a000100001600040, 0x120001a0002100049000550006000054, 0x600001e000020003f00014000560002c, 0x3a00029000050003f000490005a00008, 0x5d00024000020004f000240003500056, 0x3b0002400057000570000c0003200002],
    [0x200040000540002c000080005600002, 0x640001600060000560005a0003500032, 0x2300010000550001400049000240000c, 0x5a0005a000490003f0003f0004f00057, 0x1a000560002100002000050000200057, 0x50000320001a0001e000290002400024, 0x3c0003600012000600003a0005d0003b],
    [0x1d000420002a00051000470000c00031, 0x28000070004400042000130003500057, 0x4f000630004a0002a00011000000005d, 0x4a000300000f000040000b000070003a, 0xd00010000520002b00025000530004d, 0x140003a0003d000170004b000630000d, 0xe00061000640003c000070003800059],
    [0x31000570005d0003a0004d0000d00059, 0xc000350000000007000530006300038, 0x4700013000110000b000250004b00007, 0x51000420002a000040002b000170003c, 0x2a000440004a0000f000520003d00064, 0x42000070006300030000100003a00061, 0x1d000280004f0004a0000d000140000e],
    [0x4a0003400003, 0x260000c00003, 0x10004800027],
    [0x30000300027, 0x340000c00048, 0x4a0002600001],
    [0x420006200058, 0x250004600037, 0xf0001a00052],
    [0x580003700052, 0x62000460001a, 0x42000250000f],
    [0x90002e000480002b0001f0003100001, 0x130001a00017000390002b0005c00036, 0x700042000120003a0005e0002200063]⟩
  b2 := ⟨5,
    [0x4e00010000210000300017000570005a, 0x24000340001f0002200064000180002e, 0x2f00045000380001e0003e0001b00000, 0x400003000630003800035000260005a, 0x46000480001c000410001d0000a00034, 0x11000620000900039000410005c00005, 0x400002e000330002a0001d0000300006],
    [0x5a0002e000000005a000340000500006, 0x57000180001b000260000a0005c00003, 0x17000640003e000350001d000410001d, 0x3000220001e0003800041000390002a, 0x210001f00038000630001c0000900033, 0x1000034000450000300048000620002e, 0x4e000240002f00004000460001100040],
    [0x4c000620000c000400005b0003500022, 0x440002b000350000d0002e0001000003, 0x41000250001300010000000000a00015, 0x530004b0004f0001200054000210004d, 0x1a000380001b0000400051000550004e, 0x50002b0004100063000580001400002, 0x4a000540000500048000330003a00022],
    [0x2200003000150004d0004e0000200022, 0x35000100000a0002100055000140003a, 0x5b0002e0000000054000510005800033, 0x400000d0001000012000040006300048, 0xc00035000130004f0001b0004100005, 0x620002b000250004b000380002b00054, 0x4c0004400041000530001a000050004a],
    [0x1f0005300041, 0x60001b00060, 0x1d000330002e],
    [0x41000600002e, 0x530001b00033, 0x1f000060001d],
    [0x4b000580005c, 0x100004f0004a, 0x29000150000d],
    [0x5c0004a0000d, 0x580004f00015, 0x4b0001000029],
    [0x2a000550005d00044000290001a00019, 0x360002d00013000380003f000200004d, 0x600030000400002000026000270000f]⟩

private theorem tripleCert_6_ok : checkTripleCert tripleCert_6 = true := by decide

private def tripleCert_7 : PackedTripleCert where
  n0 := 0
  n1 := 3
  n2 := 4
  M_rows := [0x3a000590005d000580003b000440004e0000300011000080003c0001a0001d0002b0005b0001d00043000340004700005, 0x1b00054000570003b0005a00049000600003c0005e0005e000120002b0004700053000520003f000120000f0001e00027, 0x1d0005b0002e0002f000110004300028000440000c0005500061000340002b00029000370001f0002d000050004900023, 0x580005e0001f0003f000550002b0002500021000290004e0002f0006100037000560005d0002e00040000160001d00031, 0x300003d0002f00020000190000500051000380004c0002b0001700054000580001600053000160004c0000f000440005b, 0x4d0003b0003a0003d000430005a0003e000520005a0001d0001c00043000540002600034000250003f0002f0003b00056, 0x22000390004c00053000340003a0001400023000150000500061000350003000033000410000b000010004e0003c0005f, 0x1f000390001a0004000038000300005f000480005e0004d0004d0002700053000370005c0001b0004c000200004d00026, 0x2c000490005d0000c0000b00053000220004700002000570001d000020001a0001d000180001e0002f0003b000350003e, 0x24000170002f0005900006000470003f0002c000120000d000630005a0002b00005000630001700020000120005d00061, 0xf000170000f0003d0004f0005900002000490002b0000200018000410004c0001b000260001e0000200020000110002a, 0x5b0005f0000e000350000a0002c00040000180005a0002500056000440001d0002800013000450004d0005c0000b0001b, 0x260001e0000e00023000000003000004000390000700009000560001000058000390004e000200002e0003f0003100017, 0x70004e00029000390000d0000b0005a00017000060005c000240003d000240000a000620005d0004b000410002d00006, 0x520004f000040003e0001b0003800045000050003b000210002800051000130003b000180001000037000440000d0005a, 0x450003700053000240004e0003c000550005b0005f000370006300021000050005d0001700008000510001e000590004b, 0x55000130005a000270000600028000070001b0004e00011000520000b0005800012000030002f0003f0000c0001600002, 0x360002e000620001100029000110003d0001800054000110002c0002a000500002e00056000630003800063000380003d, 0x12000050003900041000430002c000130003800021000560006000061000440004e0003e000220005a0005d0000500024, 0x4f0004a00047000440006100049000510004f000170000f0000800062000010003c00044000340003600031000310001b]
  M_cols := [0x50002700023000310005b000560005f000260003e000610002a0001b00017000060005a0004b000020003d000240001b, 0x470001e000490001d000440003b0003c0004d000350005d000110000b000310002d0000d0005900016000380000500031, 0x340000f00005000160000f0002f0004e000200003b00012000200005c0003f00041000440001e0000c000630005d00031, 0x43000120002d000400004c0003f000010004c0002f00020000020004d0002e0004b00037000510003f000380005a00036, 0x1d0003f0001f0002e00016000250000b0001b0001e000170001e00045000200005d00010000080002f000630002200034, 0x5b00052000370005d0005300034000410005c000180006300026000130004e00062000180001700003000560003e00044, 0x2b000530002900056000160002600033000370001d000050001b00028000390000a0003b0005d000120002e0004e0003c, 0x1d000470002b00037000580005400030000530001a0002b0004c0001d0005800024000130000500058000500004400001, 0x1a0002b000340006100054000430003500027000020005a0004100044000100003d00051000210000b0002a0006100062, 0x3c00012000610002f000170001c000610004d0001d00063000180005600056000240002800063000520002c0006000008, 0x80005e000550004e0002b0001d000050004d000570000d0000200025000090005c00021000370001100011000560000f, 0x110005e0000c000290004c0005a000150005e00002000120002b0005a00007000060003b0005f0004e000540002100017, 0x30003c000440002100038000520002300048000470002c00049000180003900017000050005b0001b00018000380004f, 0x4e000600002800025000510003e000140005f000220003f0000200040000040005a0004500055000070003d0001300051, 0x4400049000430002b000050005a0003a000300005300047000590002c000300000b000380003c00028000110002c00049, 0x3b0005a0001100055000190004300034000380000b000060004f0000a000000000d0001b0004e00006000290004300061, 0x580003b0002f0003f000200003d00053000400000c000590003d0003500023000390003e0002400027000110004100044, 0x5d000570002e0001f0002f0003a0004c0001a0005d0002f0000f0000e0000e0002900004000530005a000620003900047, 0x59000540005b0005e0003d0003b00039000390004900017000170005f0001e0004e0004f00037000130002e000050004a, 0x3a0001b0001d00058000300004d000220001f0002c000240000f0005b000260000700052000450005500036000120004f]
  Minv_rows := [0x60002700003000470006300064000070002d0005600031000590005d0000a000370000500042000440004e0004b0003a, 0x1b00029000170003600025000280001b00017000490000c000580003a000330003c000320000b00017000310005d00046, 0x17000630005b0004700018000240002600061000190002d00022000270004b0002a00046000070004b00059000550002e, 0xa0005e0005a00033000640003d0004500043000060000100001000110005000049000010001f000370001d0005600020, 0x1d0002a0005800057000280001700024000450001d0002f000100005a0003a0002c0003600056000070005e0001e00041, 0x5700033000470005f000500002f0001e000310003e0003b0002e000190000a000160002b000180004e000310000a00048, 0x1d00000000130003c000540005800039000640004b0002d0004300035000470006400011000090000f0005f0002700030, 0x220005c0004c0001500023000400004e0000200006000160001e0002c0000d00038000300001800017000240003400007, 0x6400053000350004300037000310004f000210000d0001d0005e0004d00011000360000c0005e0001a000500005a00044, 0x2d0002a0004100047000200004f000060002800062000220003d000510001e00006000120001b0002b00016000320000e, 0x1000051000230004a00063000090000a000480002c0005d000140002a0004c000390000f000510005d000400004800019, 0x10000560003f000110001a0005200023000030004800062000210005900039000570005c000400005c0000c0002e0001c, 0x3a000290000a00000000090000300005000250004600024000020002d0004e000100000400030000380002a0002900027, 0x2a0005200051000240001900047000290005e00018000540003c000290004e00035000500005500042000070002f0005d, 0x1000600005d000200001300001000500004a0005e0005d0005b0000c00032000060003b0003e000120001e000210003f, 0x1e0002f0006200034000280004c00010000050005f00013000350004400040000450000a0001f0005900010000130003e, 0x510003f0002100042000470001a000190005e0003300001000040004d00030000630003c00018000080000e0005300015, 0x5a0004600044000280000600044000190005e00045000330000c000070004600015000170004e00031000140001500064, 0x3e0002c000290005c0003d000360005c00040000460005d000530000d0000c0003a000480001400037000100003b00041, 0x5f00058000310003200011000540005c00019000510004d00051000530001c0003400055000520006100044000020005b]
  Minv_cols := [0x3a000460002e0002000041000480003000007000440000e000190001c000270005d0003f0003e0001500064000410005b, 0x4b0005d00055000560001e0000a00027000340005a00032000480002e000290002f000210001300053000150003b00002, 0x4e00031000590001d0005e000310005f000240005000016000400000c0002a000070001e000100000e000140001000044, 0x44000170004b00037000070004e0000f000170001a0002b0005d0005c0003800042000120005900008000310003700061, 0x420000b000070001f000560001800009000180005e0001b000510004000030000550003e0001f000180004e0001400052, 0x5000320004600001000360002b00011000300000c000120000f0005c00004000500003b0000a0003c000170004800055, 0x370003c0002a000490002c000160006400038000360000600039000570001000035000060004500063000150003a00034, 0xa000330004b000500003a0000a000470000d000110001e0004c000390004e0004e000320004000030000460000c0001c, 0x5d0003a00027000110005a00019000350002c0004d000510002a000590002d000290000c000440004d000070000d00053, 0x59000580002200001000100002e000430001e0005e0003d0001400021000020003c0005b00035000040000c0005300051, 0x310000c0002d000010002f0003b0002d000160001d000220005d0006200024000540005d0001300001000330005d0004d, 0x560004900019000060001d0003e0004b000060000d000620002c0004800046000180005e0005f00033000450004600051, 0x2d0001700061000430004500031000640000200021000280004800003000250005e0004a000050005e0005e0004000019, 0x70001b0002600045000240001e000390004e0004f000060000a000230000500029000500001000019000190005c0005c, 0x6400028000240003d000170002f0005800040000310004f00009000520000300047000010004c0001a000440003600054, 0x63000250001800064000280005000054000230003700020000630001a0000900019000130002800047000060003d00011, 0x47000360004700033000570005f0003c0001500043000470004a000110000000024000200003400042000280005c00032, 0x3000170005b0005a0005800047000130004c0003500041000230003f0000a000510005d0006200021000440002900031, 0x2700029000630005e0002a00033000000005c000530002a00051000560002900052000600002f0003f000460002c00058, 0x60001b000170000a0001d000570001d00022000640002d00010000100003a0002a000010001e000510005a0003e0005f]
  b0 := ⟨0,
    [0xd00013000100002a0005b0002b00043, 0x270002700005000350004b0003a00013, 0x60004e000430001000017000530005d, 0x6200045000460000d000090001700050, 0x53000330000b00004000240005f00043, 0x2200037000620005d000320001a00008, 0x3700048000470002900009000050000e],
    [0x43000130005d0005000043000080000e, 0x2b0003a00053000170005f0001a00005, 0x5b0004b0001700009000240003200009, 0x2a00035000100000d000040005d00029, 0x100000500043000460000b0006200047, 0x13000270004e00045000330003700048, 0xd000270000600062000530002200037],
    [0x2c000220004900052000300001100043, 0x5900007000020000200056000450005c, 0x230002c000520000700030000100002e, 0x6300005000410003c0003e0005700042, 0x3300049000090005f000000004e00017, 0x34000590002a000450000c0005c00027, 0x6000032000610003a00002000180004a],
    [0x430005c0002e0004200017000270004a, 0x110004500010000570004e0005c00018, 0x3000056000300003e000000000c00002, 0x5200002000070003c0005f000450003a, 0x49000020005200041000090002a00061, 0x22000070002c00005000490005900032, 0x2c000590002300063000330003400060],
    [0x130005c, 0x250005b00052, 0x26000020000a],
    [0x5c000520000a, 0x130005b00002, 0x2500026],
    [0x220004d00015, 0x300004f0000a, 0x37000320004f],
    [0x150000a0004f, 0x4d0004f00032, 0x220003000037],
    [0x4e000390005d00043000600002500010, 0x440004d00030000370005c0003800030, 0x5000340004400055000260005e00057]⟩
  b1 := ⟨3,
    [0x4000140003700007000560003b0004d, 0x41000270001d0000e0005b0004900023, 0x2b000230004b000540004c0003800036, 0x60003400020000610002b000160004f, 0x64000140003200055000130004a00032, 0x2000270005000024000500005c00056, 0x40000200002a0002a0000f0001800046],
    [0x4d00023000360004f000320005600046, 0x3b0004900038000160004a0005c00018, 0x560005b0004c0002b00013000500000f, 0x70000e000540006100055000240002a, 0x370001d0004b0002000032000500002a, 0x14000270002300034000140002700020, 0x4000410002b00006000640000200040],
    [0x13000260005500057000630001c00012, 0x140002b000130001a000040004400043, 0x110001a000080005b000540002f0003c, 0x200003d000260000b0004a0005800035, 0x5c000000002e0004a0000d000000001f, 0x5a00040000270003a00025000350002d, 0x3800016000620003e0004f000080000f],
    [0x12000430003c000350001f0002d0000f, 0x1c000440002f00058000000003500008, 0x6300004000540004a0000d000250004f, 0x570001a0005b0000b0004a0003a0003e, 0x550001300008000260002e0002700062, 0x260002b0001a0003d000000004000016, 0x130001400011000200005c0005a00038],
    [0x31000280004f, 0x510005b00036, 0x1b000420003b],
    [0x4f000360003b, 0x280005b00042, 0x31000510001b],
    [0x200005000030, 0x10003c0001a, 0x600005a00038],
    [0x300001a00038, 0x500003c0005a, 0x200000100060],
    [0x4900028000420003b000590001c00004, 0x6200026000190000a00047000500003c, 0x5f00006000630001d000060000a0000c]⟩
  b2 := ⟨4,
    [0x2c0005c0005f0000600034000480002c, 0x18000220002c0005a0005c0000200013, 0x3600014000500003800048000240004c, 0x9000250001600020000450001500033, 0x31000440001a0005c00024000120001b, 0x550002c0003200061000070000500009, 0x590002d0000000013000350006000056],
    [0x2c000130004c000330001b0000900056, 0x48000020002400015000120000500060, 0x340005c0004800045000240000700035, 0x60005a00038000200005c0006100013, 0x5f0002c00050000160001a0003200000, 0x5c000220001400025000440002c0002d, 0x2c000180003600009000310005500059],
    [0x8000240004000013000160004500042, 0x5200017000440004c000200003d00017, 0x510005a0002000022000100003300034, 0x4a000270005a00053000010002000059, 0x5700033000080000c0005b0005300035, 0x40003c0004b0002c000260003c0000e, 0x80005b0004e000040000e0003d0001c],
    [0x42000170003400059000350000e0001c, 0x450003d0003300020000530003c0003d, 0x160002000010000010005b000260000e, 0x130004c00022000530000c0002c00004, 0x4000044000200005a000080004b0004e, 0x24000170005a00027000330003c0005b, 0x800052000510004a000570000400008],
    [0x5a0004c0004f, 0x290000f0003f, 0x160004f00056],
    [0x4f0003f00056, 0x4c0000f0004f, 0x5a0002900016],
    [0x42000620001d, 0x600004a00049, 0x3f000310004f],
    [0x1d000490004f, 0x620004a00031, 0x42000600003f],
    [0x4c0005d0005f000490000d000000001b, 0x80002f0003b0000c0000f0000c0003b, 0x49000540003d0002e000410000b00022]⟩

private theorem tripleCert_7_ok : checkTripleCert tripleCert_7 = true := by decide

private def tripleCert_8 : PackedTripleCert where
  n0 := 0
  n1 := 3
  n2 := 5
  M_rows := [0x3700026000530004000020000330000c0005d0002a0005900028000630002a0000700018000240004a000250002f00016, 0x5200026000120002f0001a000070003d00018000500001f000200005400032000620004b0003600017000050005300012, 0x150004800012000260003f000580001700049000190002500035000370005f0005a00050000300002a000540000000010, 0x2c000260004300025000020004e0001b000440000a00000000330004c0003400001000610002b00051000120006100045, 0x3000040000130004a0002d00007000230001a0002a0000000049000200004f0004b0002700040000110001e0004400058, 0x200053000560003e000550004c000520004e000630005a00042000340006200008000500003d000510001f0005a00029, 0x50005c0004e0001c00013000550000c0005600063000600003e0003800030000270005000048000360001d000420001f, 0x5d0000e0001c000140003e0002400017000180003c00025000280005e000410003a000190000800027000040003e0001a, 0x2500010000260001d000150005b000550004a000090002a0006100038000420004d000470001d00031000440004e0002b, 0xf000300000b000640001c000120002f0000800011000620000f0005400053000120001a0006000056000320003a0003d, 0x1f00003000350005b0003e0005c0004d0003b0004e000600006100002000390001b00029000400002e00064000260001c, 0x11000450003a0002f0002b000370005e000290004600052000330002a00053000090003e0004700043000440005700027, 0x6300005000160000e00064000270003600006000090002100025000370005e0002a000390001d00029000340003b0001d, 0x800031000000002b000170005200050000550000d000200000b000270004c0003a000290002b00002000600005f0004a, 0x2a0000c0001e00061000540004a00007000250004800013000190001200063000010003600043000350002b0004a00055, 0x4000520004c00058000480001100012000070000c0001f0001b000000001400057000470000400003000290004200013, 0x5900001000040005000038000320004a00012000410004f00020000300003e0002d0004a00000000420000b0003e00033, 0x220004d00045000010002c0003a0001500010000230002d0001a00024000600004d0002c0003000003000140003f00047, 0x460003d00048000520001d00014000640001900016000210003c0000b0006000037000560006000029000600002f00021, 0xc0004f0000a0000000050000350002c00054000490003f00014000140006100030000610004e0001a0003b0001400011]
  M_cols := [0x1600012000100004500058000290001f0001a0002b0003d0001c000270001d0004a000550001300033000470002100011, 0x2f000530000000061000440005a000420003e0004e0003a00026000570003b0005f0004a000420003e0003f0002f00014, 0x250000500054000120001e0001f0001d000040004400032000640004400034000600002b000290000b00014000600003b, 0x4a000170002a000510001100051000360002700031000560002e00043000290000200035000030004200003000290001a, 0x2400036000300002b000400003d00048000080001d0006000040000470001d0002b00043000040000000030000600004e, 0x180004b000500006100027000500005000019000470001a000290003e000390002900036000470004a0002c0005600061, 0x7000620005a000010004b00008000270003a0004d000120001b000090002a0003a00001000570002d0004d0003700030, 0x2a000320005f000340004f000620003000041000420005300039000530005e0004c00063000140003e000600006000061, 0x6300054000370004c0002000034000380005e0003800054000020002a0003700027000120000000030000240000b00014, 0x2800020000350003300049000420003e00028000610000f0006100033000250000b000190001b000200001a0003c00014, 0x590001f0002500000000000005a00060000250002a0006200060000520002100020000130001f0004f0002d000210003f, 0x2a00050000190000a0002a00063000630003c00009000110004e00046000090000d000480000c00041000230001600049, 0x5d0001800049000440001a0004e00056000180004a000080003b000290000600055000250000700012000100001900054, 0xc0003d000170001b00023000520000c00017000550002f0004d0005e000360005000007000120004a00015000640002c, 0x3300007000580004e000070004c00055000240005b000120005c0003700027000520004a00011000320003a0001400035, 0x200001a0003f000020002d00055000130003e000150001c0003e0002b00064000170005400048000380002c0001d00050, 0x400002f00026000250004a0003e0001c000140001d000640005b0002f0000e0002b000610005800050000010005200000, 0x5300012000120004300013000560004e0001c000260000b000350003a00016000000001e0004c0000400045000480000a, 0x2600026000480002600040000530005c0000e0001000030000030004500005000310000c00052000010004d0003d0004f, 0x3700052000150002c0003000002000050005d000250000f0001f0001100063000080002a000040005900022000460000c]
  Minv_rows := [0x370001300015000390003000063000050005d000400000f0004600011000020005d0002a0006100059000430004600059, 0x54000400003200064000100003e0000d0002c0005600026000560000b0005c0002c0001200036000030002e0006400032, 0x600000f0000a0003d0002f0000b0004c00040000260003900031000410001d00027000090000d0005b0004d0005c00045, 0x6000570000a0003c0000c000520003c0004d0002d0000b000150004800027000620003b000070000c0000f0004400026, 0x170003d0003d00026000550000300054000220003d0003b0004a000380001f0002c000570005000039000600002f0000d, 0x5e000080005c0003e000110000d000300004e0001200059000060003a000130002600055000290001b0000a0002800000, 0x410003800049000610005800030000430000d00020000050005d0002a0002800001000140003f000180002f0004900002, 0x130002a0004b0000d0003800000000270004c0002f00011000640004e000620004e00058000360005f0005c000590004a, 0x220006200039000200001d000460006400012000010002600040000390001b0005c0003a0000c0003e000570000300007, 0x4c000230000400006000130005d0001800021000220000c00000000250000c0005c0005e000260000800044000230001f, 0x4f000180001200036000180000f000130001600041000340004c000190005e0004a00052000260002e000080000100034, 0x1e00060000270006100016000290000c000200004100001000400003d00055000080004500023000020005b0002800044, 0x2b00040000050005100058000620002800051000370005b00046000170004a0001e000240005d0002e000140006200062, 0x390004a00020000300004b000350002a0001d0002700055000460005f0001e00050000010005d0003000033000160000d, 0x15000550004c00043000390001900023000470004c000180004c00016000090005f0000900062000050000f0000200028, 0x6000052000180003300041000450002f0004a000020003200054000270003d0004f00035000270001a000510002e0002f, 0x51000320003c000440000c0006100063000470003700024000530005900026000180000d000400002a000590002b0005b, 0x3c0000e000450001b0003400043000270005400004000020004f0000d0002000011000150003c0002b00034000040000b, 0x2c000620004000014000320001500011000440000a0005c00016000400006100010000010003d000560003d0002a00021, 0x1e000040002f0002f00052000560004400063000200000800026000220000e00043000110003a00049000120006000059]
  Minv_cols := [0x590003200045000260000d00000000020004a000070001f0003400044000620000d000280002f0005b0000b0002100059, 0x46000640005c000440002f000280004900059000030002300001000280006200016000020002e0002b000040002a00060, 0x430002e0004d0000f000600000a0002f0005c0005700044000080005b00014000330000f0005100059000340003d00012, 0x59000030005b0000c000390001b000180005f0003e000080002e000020002e00030000050001a0002a0002b0005600049, 0x61000360000d0000700050000290003f000360000c0002600026000230005d0005d0006200027000400003c0003d0003a, 0x2a00012000090003b000570005500014000580003a0005e0005200045000240000100009000350000d000150000100011, 0x5d0002c00027000620002c00026000010004e0005c0005c0004a000080001e000500005f0004f00018000110001000043, 0x20005c0001d000270001f0001300028000620001b0000c0005e000550004a0001e000090003d0002600020000610000e, 0x110000b0004100048000380003a0002a0004e0003900025000190003d000170005f0001600027000590000d0004000022, 0x460005600031000150004a000060005d0006400040000000004c0004000046000460004c00054000530004f0001600026, 0xf00026000390000b0003b000590000500011000260000c00034000010005b00055000180003200024000020005c00008, 0x4000056000260002d0003d00012000200002f0000100022000410004100037000270004c0000200037000040000a00020, 0x5d0002c000400004d000220004e0000d0004c00012000210001600020000510001d000470004a00047000540004400063, 0x50000d0004c0003c000540003000043000270006400018000130000c000280002a000230002f00063000270001100044, 0x630003e0000b00052000030000d0003000000000460005d0000f000290006200035000190004500061000430001500056, 0x30000100002f0000c000550001100058000380001d000130001800016000580004b00039000410000c000340003200052, 0x39000640003d0003c000260003e000610000d0002000006000360006100051000300004300033000440001b000140002f, 0x15000320000a0000a0003d0005c000490004b0003900004000120002700005000200004c000180003c00045000400002f, 0x13000400000f000570003d00008000380002a00062000230001800060000400004a0005500052000320000e0006200004, 0x37000540006000006000170005e0004100013000220004c0004f0001e0002b000390001500060000510003c0002c0001e]
  b0 := ⟨0,
    [0x1600063000360004f0002d0001300011, 0x48000210003300000000410005d00051, 0x5f0001000047000070000d0004700056, 0x55000640003b00030000470000400047, 0x4200043000050004b0005c0002b00062, 0x1a0000a0004a00048000070002700045, 0x510004d00012000610001f000370004d],
    [0x1100051000560004700062000450004d, 0x130005d00047000040002b0002700037, 0x2d000410000d000470005c000070001f, 0x4f0000000007000300004b0004800061, 0x3600033000470003b000050004a00012, 0x63000210001000064000430000a0004d, 0x16000480005f00055000420001a00051],
    [0x4400018000390002e0005a0001200024, 0x280004000050000070004f0005f00046, 0x400002f0000f0005e0002b0005200036, 0x640004e0001a00047000480005c00031, 0x33000520000f000570003d000590002a, 0x500001100041000420001e000050001a, 0xc000470005a0001d000270004a00030],
    [0x240004600036000310002a0001a00030, 0x120005f000520005c00059000050004a, 0x5a0004f0002b000480003d0001e00027, 0x2e000070005e0004700057000420001d, 0x39000500000f0001a0000f000410005a, 0x18000400002f0004e000520001100047, 0x4400028000400006400033000500000c],
    [0x4e0002500029, 0x620001200057, 0x23000530004c],
    [0x29000570004c, 0x250001200053, 0x4e0006200023],
    [0x1d00005, 0xa000190005b, 0x3c0003000055],
    [0x50005b00055, 0x1d0001900030, 0xa0003c],
    [0x33000230002b0002100021000280001d, 0x160000a0005e000530001c0003f00008, 0x50002400056000550000b000020000a]⟩
  b1 := ⟨3,
    [0x220003d00048000060001c0002200006, 0x40000c000620004b000180001700044, 0x3e0003f0003e0003e000600000b00029, 0x2c0001a000410005b0003b0002e00006, 0x2e000480005b00002000420001500028, 0x2d00056000150003e000290004f0003f, 0x61000600002900017000190003b0002a],
    [0x6000440002900006000280003f0002a, 0x22000170000b0002e000150004f0003b, 0x1c00018000600003b000420002900019, 0x60004b0003e0005b000020003e00017, 0x48000620003e000410005b0001500029, 0x3d0000c0003f0001a000480005600060, 0x22000040003e0002c0002e0002d00061],
    [0x43000460005d00036000180002900045, 0xd000390003a00022000090000500033, 0x2e000060006200000000300003400062, 0x5e00038000370003c000080004500053, 0x2d00044000540002b000160002b00057, 0x5700060000100002e0003d0001c00026, 0x50003f0005c00004000480002900002],
    [0x45000330006200053000570002600002, 0x290000500034000450002b0001c00029, 0x18000090003000008000160003d00048, 0x3600022000000003c0002b0002e00004, 0x5d0003a000620003700054000100005c, 0x4600039000060003800044000600003f, 0x430000d0002e0005e0002d0005700005],
    [0x110003f00058, 0x270004d00022, 0x36000440000f],
    [0x58000220000f, 0x3f0004d00044, 0x110002700036],
    [0x4f0001100013, 0xa000220000f, 0x3b000590003c],
    [0x130000f0003c, 0x110002200059, 0x4f0000a0003b],
    [0x3000040000100005000520000800018, 0x1b000590000f0001f000010001900002, 0x420000000018000410004a0005100055]⟩
  b2 := ⟨5,
    [0x3a00021000300001a000640001b00008, 0x1d000510001d00043000510000300049, 0x29000560001d00047000460000d00055, 0x4b000510003b00006000150001600027, 0x300001d000060001c000070003f0003f, 0x300004f000540004e000090000900005, 0x2a000340002f000230000a0003900000],
    [0x80004900055000270003f0000500000, 0x1b000030000d000160003f0000900039, 0x6400051000460001500007000090000a, 0x1a0004300047000060001c0004e00023, 0x300001d0001d0003b00006000540002f, 0x210005100056000510001d0004f00034, 0x3a0001d000290004b00030000300002a],
    [0x430002d0001b0001c0001d0002d00035, 0x63000160001800048000050003a00026, 0x310002a000460002e0003f0005f00056, 0x2e0005500015000050004e0003000012, 0x5f0002200026000190001e0002d0000f, 0x290000b0003d0001800029000090005a, 0x41000120000a0005e0005b0001000012],
    [0x350002600056000120000f0005a00012, 0x2d0003a0005f000300002d0000900010, 0x1d000050003f0004e0001e000290005b, 0x1c000480002e0000500019000180005e, 0x1b000180004600015000260003d0000a, 0x2d000160002a00055000220000b00012, 0x4300063000310002e0005f0002900041],
    [0x2c0004200020, 0x3f0001c0004d, 0x3e0000b00028],
    [0x200004d00028, 0x420001c0000b, 0x2c0003f0003e],
    [0x460001400026, 0x470003b00006, 0x280004c00007],
    [0x260000600007, 0x140003b0004c, 0x460004700028],
    [0xc0001a0003b000520000f0002a0004d, 0x2f00034000400005d0003b0000e00031, 0x570005900028000030000f0004b00051]⟩

private theorem tripleCert_8_ok : checkTripleCert tripleCert_8 = true := by decide

private def tripleCert_9 : PackedTripleCert where
  n0 := 0
  n1 := 4
  n2 := 5
  M_rows := [0x16000380003b0005200036000080005a0001000030000550005a0002c0004b000410003100044000160002c0001300022, 0x2c0002b0002d000120002900035000330005900056000600003e0005500062000050001b0001c00043000000002c00036, 0x1d0004a0004b0005a000420001d000380004600006000320002a000220004c000290004d0003a0001f000470003a0003c, 0x6000600005a0004f0004e000300002a0002400047000510005400054000170001500020000000005a00016000080004e, 0x3b0004a000550004d0000e00016000100002f0000c00049000440004200032000420001e000330002f00055000120005b, 0x340005f000620000a000290000f000220004300033000360004900039000620004d0004a0005e0002f0005a0004e00023, 0xc000590004e000600002b0000f0005400003000560003b000110002d00054000410003a0005f00057000010006200049, 0x28000040002600047000170000b0004a0003d0001e0004a000380003d0000b000570005500019000630001c0001300008, 0x3f0005e0004900005000070002700045000530004c00002000440001c000510003e000370003b000160005a0004500016, 0x1400021000470001f000490006300006000270001d00013000040005f0005d0005e0001b0004f000560000d0004600038, 0x420005c0005b0003d00053000190005f000360002500010000440002f0004b0005d00045000300006100005000550000d, 0x340004e0000c000500005a0000200008000350005c0006100022000140001b00023000430005700058000450000b0001c, 0x3e000160005600019000640005a0002100004000330001e00016000510000300061000190001400048000640001a00058, 0x1100012000340004e0000f000480003f000200005600033000390003a0004f0000a0002a00050000100000f0004600039, 0x500017000570003a0004100027000130003b0005c000600001300027000400001b000570004e0004f0003a0004b0005e, 0x280003e0001d000070004b00051000330001c000540000a0002400021000200006200048000370001c000280005f00013, 0xb0004a000300003e0004200057000370000d0001d000470003e000120004f000250001b00038000150005d0003400054, 0x4200043000530000600036000530003300014000380004b00059000350006100055000000005e000630005b0003900020, 0x80004a0000a0002c00035000570001e000530004c000090005d000240000c0004f000360005b000200003e0002e00043, 0x210005a000300004c0005e0001c00006000210005f0002c0005a000460004c000380003d000420005d0001a0005f00032]
  M_cols := [0x22000360003c0004e0005b00023000490000800016000380000d0001c00058000390005e0001300054000200004300032, 0x130002c0003a00008000120004e00062000130004500046000550000b0001a000460004b0005f00034000390002e0005f, 0x2c000000004700016000550005a000010001c0005a0000d0000500045000640000f0003a000280005d0005b0003e0001a, 0x16000430001f0005a0002f0002f00057000630001600056000610005800048000100004f0001c0001500063000200005d, 0x440001c0003a00000000330005e0005f000190003b0004f000300005700014000500004e00037000380005e0005b00042, 0x310001b0004d000200001e0004a0003a00055000370001b0004500043000190002a00057000480001b00000000360003d, 0x41000050002900015000420004d00041000570003e0005e0005d00023000610000a0001b0006200025000550004f00038, 0x4b000620004c000170003200062000540000b000510005d0004b0001b000030004f00040000200004f000610000c0004c, 0x2c00055000220005400042000390002d0003d0001c0005f0002f00014000510003a000270002100012000350002400046, 0x5a0003e0002a000540004400049000110003800044000040004400022000160003900013000240003e000590005d0005a, 0x5500060000320005100049000360003b0004a000020001300010000610001e00033000600000a000470004b000090002c, 0x300005600006000470000c00033000560001e0004c0001d000250005c00033000560005c000540001d000380004c0005f, 0x100005900046000240002f00043000030003d0005300027000360003500004000200003b0001c0000d000140005300021, 0x5a00033000380002a0001000022000540004a00045000060005f00008000210003f000130003300037000330001e00006, 0x8000350001d00030000160000f0000f0000b000270006300019000020005a0004800027000510005700053000570001c, 0x3600029000420004e0000e000290002b000170000700049000530005a000640000f000410004b0004200036000350005e, 0x52000120005a0004f0004d0000a0006000047000050001f0003d00050000190004e0003a000070003e000060002c0004c, 0x3b0002d0004b0005a00055000620004e0002600049000470005b0000c0005600034000570001d00030000530000a00030, 0x380002b0004a000600004a0005f00059000040005e000210005c0004e0001600012000170003e0004a000430004a0005a, 0x160002c0001d000060003b000340000c000280003f0001400042000340003e0001100005000280000b000420000800021]
  Minv_rows := [0xb0004f0004100062000500004b0000600014000130000a000440001a000460002a000350005100038000440000400022, 0x2f0002400016000490005e000140001600054000570000b00052000290003300039000290005a0005500002000350005b, 0x47000000001f0003e0003c000190005800003000540005400010000100001a00051000230002c0005300014000020001a, 0x130005700022000060003d000280002f0001b0000d0002f0002600026000400000800057000380002f0004c000260002d, 0x3c000070000900039000500000d00038000080001d0005900008000070001a0002f000610004d0001400029000010003b, 0x2e0002e0003f000440006200002000590003d00010000250005e00038000290004f000510003a00052000240003500057, 0x320003b00026000180002600021000070004b00059000400006000054000050004700055000350000a00002000230005c, 0x64000280004400062000560004600012000320002a0002500005000290000500063000030002600003000510000b0003f, 0x2400020000280004a0000b0000a0000000059000480001d00016000020002e0001000038000290004d000450000500029, 0x500000d0002b000500000a00021000250005d000210005c0005d000370000c000430003a0004400017000260005100039, 0x4d000200003f000210002c0005b00016000610004c000310002b000460003a00059000580002000055000640005200017, 0x800029000180001400024000580006400014000390003f000470005c000190005f000110004300054000230003d00049, 0x280005f0004100038000240005f0003c00005000290005a000000002c0002100004000240002300024000480001d0002b, 0x500009000590005a00060000590001c0000b0003800047000410002c0002100001000320003200056000390003c0003e, 0x380001f000530005800035000300000a0000000042000550004f0002900036000260000b000610003000040000200002f, 0x210002e00031000330002f000350003200057000440004a00061000000003500054000080000b00042000220000b00042, 0x1c0003c000050000d00063000300005200015000440003d00044000530004e000420001a000120002d000240003700050, 0x700040000470000a000000003400039000500001f0001f0003b00017000360000f0002d0002e0001d0001f000440000a, 0x41000360005a0004100054000420002d0004e0004b000570001000026000460002d0005a000540004b00015000300000b, 0x290001b000550000d000040002400011000370001400028000370003c0003200047000160000a000040005b0003a00056]
  Minv_cols := [0x220005b0001a0002d0003b000570005c0003f000290003900017000490002b0003e0002f00042000500000a0000b00056, 0x40003500002000260000100035000230000b0000500051000520003d0001d0003c000200000b0003700044000300003a, 0x4400002000140004c000290002400002000510004500026000640002300048000390004000022000240001f000150005b, 0x3800055000530002f00014000520000a000030004d000170005500054000240005600030000420002d0001d0004b00004, 0x510005a0002c000380004d0003a0003500026000290004400020000430002300032000610000b000120002e000540000a, 0x3500029000230005700061000510005500003000380003a000580001100024000320000b000080001a0002d0005a00016, 0x2a0003900051000080002f0004f00047000630001000043000590005f00004000010002600054000420000f0002d00047, 0x46000330001a000400001a0002900005000050002e0000c0003a00019000210002100036000350004e000360004600032, 0x1a000290001000026000070003800054000290000200037000460005c0002c0002c00029000000005300017000260003c, 0x44000520001000026000080005e0006000005000160005d0002b0004700000000410004f00061000440003b0001000037, 0xa0000b000540002f000590002500040000250001d0005c000310003f0005a00047000550004a0003d0001f0005700028, 0x1300057000540000d0001d00010000590002a00048000210004c0003900029000380004200044000440001f0004b00014, 0x1400054000030001b000080003d0004b00032000590005d0006100014000050000b000000005700015000500004e00037, 0x600016000580002f00038000590000700012000000002500016000640003c0001c0000a0003200052000390002d00011, 0x4b0001400019000280000d0000200021000460000a000210005b000580005f00059000300003500030000340004200024, 0x500005e0003c0003d000500006200026000560000b0000a0002c000240002400060000350002f00063000000005400004, 0x62000490003e00006000390004400018000620004a000500002100014000380005a00058000330000d0000a000410000d, 0x41000160001f00022000090003f0002600044000280002b0003f000180004100059000530003100005000470005a00055, 0x4f000240000000057000070002e0003b00028000200000d00020000290005f000090001f0002e0003c00040000360001b, 0xb0002f00047000130003c0002e000320006400024000500004d00008000280000500038000210001c000070004100029]
  b0 := ⟨0,
    [0x61000210000e0000d00063000240001b, 0x190002f0003e00013000010004e0000d, 0xd0000b0004800021000090001a0002e, 0x600049000380003e0001b0005300054, 0x3a0005c0001a00005000040000f00031, 0x160002e0005700055000250005d0003e, 0x40000c00020000110001b000550001d],
    [0x1b0000d0002e00054000310003e0001d, 0x240004e0001a000530000f0005d00055, 0x6300001000090001b00004000250001b, 0xd00013000210003e000050005500011, 0xe0003e00048000380001a0005700020, 0x210002f0000b000490005c0002e0000c, 0x61000190000d000060003a0001600004],
    [0x500043000400004e0001f0003d00020, 0x490004c0001d0004d0003c0002e0002d, 0x4f0002d0004c0005100062000390001c, 0x4c00001000470003e0001e0004600016, 0x1100007000510001a0003b000240005f, 0x140003d000530004f00002000600003e, 0x2500036000240004e000240003100053],
    [0x200002d0001c000160005f0003e00053, 0x3d0002e0003900046000240006000031, 0x1f0003c000620001e0003b0000200024, 0x4e0004d000510003e0001a0004f0004e, 0x400001d0004c00047000510005300024, 0x430004c0002d00001000070003d00036, 0x5000490004f0004c000110001400025],
    [0x160001b, 0x590000e0003f, 0xb0005300005],
    [0x1b0003f00005, 0x160000e00053, 0x590000b],
    [0x410004400041, 0x230005b0003a, 0x25000110002f],
    [0x410003a0002f, 0x440005b00011, 0x410002300025],
    [0x4500014000190005a0005c0004400010, 0x3800031000420005b000320002f00032, 0x3c0002e000150005a0002e0000900031]⟩
  b1 := ⟨4,
    [0x5900042000470004f0002a0005c0003b, 0x90000d0002400024000470002300062, 0x5700031000480002100044000210001c, 0x57000350003c000510001e0000000008, 0x190001a00041000170000e000480001a, 0xa0003a0003b0002900038000440003f, 0x230006300004000140000b0004c00036],
    [0x3b000620001c000080001a0003f00036, 0x5c00023000210000000048000440004c, 0x2a00047000440001e0000e000380000b, 0x4f000240002100051000170002900014, 0x4700024000480003c000410003b00004, 0x420000d00031000350001a0003a00063, 0x59000090005700057000190000a00023],
    [0xd000330003200012000010003700045, 0xc0000d0004a00059000360004d00020, 0xd0002d0004f0002f0004c0003f00044, 0x360001a0004b0001a0002c000610004a, 0x470002a00019000420005e0003e00035, 0x4000170004f0002e0005d0003300015, 0x5a000020001c00021000620003d0002f],
    [0x4500020000440004a00035000150002f, 0x370004d0003f000610003e000330003d, 0x1000360004c0002c0005e0005d00062, 0x12000590002f0001a000420002e00021, 0x320004a0004f0004b000190004f0001c, 0x330000d0002d0001a0002a0001700002, 0xd0000c0000d0003600047000040005a],
    [0x7000040001e, 0xf000570005d, 0x45000380005f],
    [0x1e0005d0005f, 0x40005700038, 0x70000f00045],
    [0x2c0005600059, 0x1000090002b, 0x55000580001b],
    [0x590002b0001b, 0x560000900058, 0x2c0000100055],
    [0x5c0004d00038000090002f0005e0005c, 0x140001800057000320005b0000600050, 0x510001000056000460000f0003f00051]⟩
  b2 := ⟨5,
    [0x2500020000200005b000150001500050, 0x2e000170001a0005c000520005b00005, 0x350000b0005400004000630005f0004a, 0x290003900030000440001c0000000023, 0x59000060003e0004a0002a0003b00028, 0x50000090003d0000f000310003d0005b, 0x2e000240000b0001b0005a0003200037],
    [0x50000050004a00023000280005b00037, 0x150005b0005f000000003b0003d00032, 0x1500052000630001c0002a000310005a, 0x5b0005c00004000440004a0000f0001b, 0x200001a00054000300003e0003d0000b, 0x20000170000b00039000060000900024, 0x250002e000350002900059000500002e],
    [0x3c0002e0000b0000e000030000500047, 0x2e000160004500024000520001900018, 0x5c0004d0000d00047000480000700010, 0x240001f0001d0005a0001d0004100055, 0x120003e00040000600001e000410003c, 0x2b000190001500040000190003b00055, 0x290002d0004200039000340006100008],
    [0x470001800010000550003c0005500008, 0x5000190000700041000410003b00061, 0x300052000480001d0001e0001900034, 0xe00024000470005a000600004000039, 0xb000450000d0001d000400001500042, 0x2e000160004d0001f0003e000190002d, 0x3c0002e0005c00024000120002b00029],
    [0x2f0005000055, 0x570004200026, 0x2c0001200026],
    [0x550002600026, 0x500004200012, 0x2f000570002c],
    [0x280000500032, 0x5e0004600024, 0x5a0005b00059],
    [0x320002400059, 0x5000460005b, 0x280005e0005a],
    [0x5b0004e000330005e000360002f00004, 0xb0000000022000590002c0000100035, 0x1e000420001600028000280001f00036]⟩

private theorem tripleCert_9_ok : checkTripleCert tripleCert_9 = true := by decide

private def tripleCert_10 : PackedTripleCert where
  n0 := 1
  n1 := 2
  n2 := 3
  M_rows := [0x1100053000130002c0003f0002e0003400032000100000b00044000300001600058000020002d0001300035000550002d, 0x5b000460003e0005f0001c00023000260003f0001f0001f0000d0002f000420003c000100004300046000130005000017, 0x130003b0002f000600003d00050000120004100013000000004300056000230000e00061000340002d000610005900057, 0x360001c00060000170000b00051000440004e0002f0001800061000070001f000260001300060000170003a0003b0000c, 0x4c0001500017000390003d0001300056000560005c000590003f0002e00012000530001a0002c000530002c0000e00048, 0x1200045000320001c0004e00062000330003d0005e000490001a000100005400053000260003900035000570005b00062, 0x5d0005c000640004a000030003d00045000300000b000400003f000250005600044000430004900010000210004c00017, 0x350002e0003e00042000640004b0001c000110001f0004600022000340005c0000a0003b000540002c000310001c0005f, 0x6000060000390001b0001c0000e000330002400010000420003c0000200041000390002f0006000037000310002700006, 0x170000b00035000250002200064000610005900049000250000a000190003c0005e00059000020000f000120003800005, 0x4400003000090002a00044000060002a00041000240005800063000330001400036000640005300032000210001200054, 0x570004c000440002c0000f000550005d000220004d00035000270000c000330001d00059000140003c000140002c00030, 0x51000340005400042000390003d000170001d000060004c000500002900048000340001a0004d00012000110001300048, 0x390005700045000420001f0004600060000100005c000100005b0005e0001d000130000c0002600059000310005f0000f, 0x4b000290000b000180003d0004e0000800037000620004d000150000400040000440004d0005f000080002d0000b00025, 0x220002c0001e00037000410003b0004d0002000061000330002c00018000310004d0003a000560003100032000570001d, 0x80001c00019000200001900051000480001e0001f000050000a000630005f0005a0005c0004c0002c0004b000570001a, 0x20004b00063000060003b00051000480005100038000250002b000180001b0001c0004000019000270002f0000d00041, 0x61000630002a0001600058000560005f000320001c000390003f000540000700033000620001500055000460003d0000d, 0x4f00032000410001b000640000c000260005400017000540000f000610004a00064000140003a00029000340005400013]
  M_cols := [0x2d00017000570000c0004800062000170005f00006000050005400030000480000f000250001d0001a000410000d00013, 0x5500050000590003b0000e0005b0004c0001c0002700038000120002c000130005f0000b00057000570000d0003d00054, 0x3500013000610003a0002c0005700021000310003100012000210001400011000310002d000320004b0002f0004600034, 0x13000460002d000170005300035000100002c000370000f000320003c000120005900008000310002c000270005500029, 0x2d0004300034000600002c000390004900054000600000200053000140004d000260005f000560004c00019000150003a, 0x20001000061000130001a00026000430003b0002f0005900064000590001a0000c0004d0003a0005c000400006200014, 0x580003c0000e000260005300053000440000a000390005e000360001d0003400013000440004d0005a0001c0003300064, 0x1600042000230001f0001200054000560005c000410003c0001400033000480001d00040000310005f0001b000070004a, 0x300002f00056000070002e0001000025000340000200019000330000c000290005e000040001800063000180005400061, 0x440000d00043000610003f0001a0003f000220003c0000a0006300027000500005b000150002c0000a0002b0003f0000f, 0xb0001f000000001800059000490004000046000420002500058000350004c000100004d0003300005000250003900054, 0x100001f000130002f0005c0005e0000b0001f0001000049000240004d000060005c00062000610001f000380001c00017, 0x320003f000410004e000560003d0003000011000240005900041000220001d0001000037000200001e000510003200054, 0x340002600012000440005600033000450001c00033000610002a0005d0001700060000080004d00048000480005f00026, 0x2e00023000500005100013000620003d0004b0000e0006400006000550003d000460004e0003b0005100051000560000c, 0x3f0001c0003d0000b0003d0004e00003000640001c00022000440000f000390001f0003d00041000190003b0005800064, 0x2c0005f0006000017000390001c0004a000420001b000250002a0002c000420004200018000370002000006000160001b, 0x130003e0002f000600001700032000640003e0003900035000090004400054000450000b0001e00019000630002a00041, 0x53000460003b0001c00015000450005c0002e000600000b000030004c0003400057000290002c0001c0004b0006300032, 0x110005b00013000360004c000120005d000350006000017000440005700051000390004b000220000800002000610004f]
  Minv_rows := [0x5c000420005500058000250003f0001c00043000210004700024000310001f000300005b0001200049000070000e00018, 0x1c0005d000410004c000550002b0005e0003600058000100005b0000a0001e0001b000320005e000100004a0003c0005f, 0x4f0004b000010003d0003200017000280004f000410004b0004300014000070002b000400003700049000530002700023, 0x4c0001c0001a0001900035000640000e000620003b0000d00025000470005e00033000120000500059000360004b00009, 0xd0005d0003b00064000490002a00058000510005c0001300021000020001200060000090001a00009000480005900012, 0x40002900040000210003c000270004900006000120005c000120002f0002b0003b000310005800013000230002400019, 0x440004a00035000310003c000610005c00027000360001f0005b0004b000570004200032000570003700005000360000d, 0x30001f0002700007000580004d000500004b0003c0001000043000190001b0000f000480005a00060000530004b0003b, 0x2000470000d0003d00028000540005c00055000170003f0004a000580005100064000250005f000370001c0000000001, 0xa0005d0003e0004a0000e000290005f00047000080004c0002b000380005e00047000420000f000040002a0001400001, 0x3d0005f000550001a000070004d000180005400018000620002c00019000450004d000030001f000530005a000200005b, 0xd0004e0000b000390000800025000590002500026000300002200036000440001a000370004b0005e0003b0005700026, 0x40004c0005e00010000550001c0001a000470001a000280002b000360005d0001e00025000050004d000590001f00063, 0xc0000a00043000640003f00008000030003d000050003c0002c000150000f00058000560005e0006200046000250004a, 0x37000320004f0002f000600006400054000580001400001000110005c00007000200003b0005000049000260004100055, 0x2f000330003d000390004a0002c000170002b000610003000003000600005a0003f000430003f000560002f000030002d, 0x620003500035000390000c0000a00060000610002d0002a0002b0000600042000010002f000630003900041000140003a, 0x190003b000000001b00003000620001c000550000f0004600061000200000c00047000400001a0000200023000320005f, 0x270004b0006000059000490003f0005d0005b0004800030000160000b000120001d000410001c00024000050002b00060, 0x270005f0005e0003f00053000460004b000390004d0003b0002c0005c0002a000150003b00013000220001f0001d00045]
  Minv_cols := [0x180005f000230000900012000190000d0003b00001000010005b00026000630004a000550002d0003a0005f0006000045, 0xe0003c000270004b0005900024000360004b000000001400020000570001f00025000410000300014000320002b0001d, 0x70004a0005300036000480002300005000530001c0002a0005a0003b0005900046000260002f0004100023000050001f, 0x49000100004900059000090001300037000600003700004000530005e0004d00062000490005600039000020002400022, 0x120005e00037000050001a00058000570005a0005f0000f0001f0004b000050005e000500003f000630001a0001c00013, 0x5b000320004000012000090003100032000480002500042000030003700025000560003b000430002f00040000410003b, 0x300001b0002b00033000600003b000420000f00064000470004d0001a0001e00058000200003f00001000470001d00015, 0x1f0001e000070005e000120002b000570001b000510005e00045000440005d0000f000070005a000420000c000120002a, 0x310000a0001400047000020002f0004b000190005800038000190003600036000150005c0006000006000200000b0005c, 0x240005b000430002500021000120005b000430004a0002b0002c000220002b0002c00011000030002b00061000160002c, 0x47000100004b0000d000130005c0001f000100003f0004c0006200030000280003c00001000300002a00046000300003b, 0x2100058000410003b0005c00012000360003c000170000800018000260001a0000500014000610002d0000f000480004d, 0x43000360004f000620005100006000270004b00055000470005400025000470003d000580002b00061000550005b00039, 0x1c0005e000280000e00058000490005c000500005c0005f00018000590001a000030005400017000600001c0005d0004b, 0x3f0002b00017000640002a00027000610004d00054000290004d000250001c00008000640002c0000a000620003f00046, 0x25000550003200035000490003c0003c00058000280000e0000700008000550003f000600004a0000c000030004900053, 0x580004c0003d00019000640002100031000070003d0004a0001a0003900010000640002f00039000390001b000590003f, 0x5500041000010001a0003b0004000035000270000d0003e000550000b0005e000430004f0003d0003500000000600005e, 0x420005d0004b0001c0005d000290004a0001f000470005d0005f0004e0004c0000a0003200033000350003b0004b0005f, 0x5c0001c0004f0004c0000d000040004400003000020000a0003d0000d000040000c000370002f00062000190002700027]
  b0 := ⟨1,
    [0x240000700037000360001e0004200039, 0x2800004000080001100020000010001f, 0x3e000360005b00027000310005a0001c, 0x28000580000e00035000310006400007, 0x6000059000320000a000500006000041, 0x10000330005a0000b00032000060000c, 0x1d0004f00048000090005e0003100020],
    [0x390001f0001c00007000410000c00020, 0x42000010005a00064000600000600031, 0x1e00020000310003100050000320005e, 0x360001100027000350000a0000b00009, 0x37000080005b0000e000320005a00048, 0x700004000360005800059000330004f, 0x24000280003e0002800060000100001d],
    [0x200011000580000c00063000560005e, 0x1d0001f0005500039000520005700037, 0x1800013000220002c000030005d0002c, 0x59000410001e0002800011000500003a, 0x2f0002c000220005d00044000600001b, 0x30006100005000130004a0002200037, 0x20000030005c0000a000200005300004],
    [0x5e000370002c0003a0001b0003700004, 0x56000570005d00050000600002200053, 0x63000520000300011000440004a00020, 0xc000390002c000280005d000130000a, 0x5800055000220001e00022000050005c, 0x110001f00013000410002c0006100003, 0x20001d00018000590002f0000300020],
    [0x610002700006, 0x1a0002600025, 0x3f0002a0001e],
    [0x6000250001e, 0x27000260002a, 0x610001a0003f],
    [0xb0005100012, 0x14000270000d, 0x3c0001600002],
    [0x120000d00002, 0x510002700016, 0xb000140003c],
    [0x2200057000130005b0002b0003300041, 0x27000440003f00034000380003900057, 0xb000520002f000080003b0000d00026]⟩
  b1 := ⟨2,
    [0x1c0001b0005d0001f00002000180000d, 0x2c0005a0005c0002c000170004d0003f, 0x30001300027000290001b0004a0001a, 0x330001a000460000c0005b0001400012, 0x560002e0004e000420003a0001700054, 0x480000100014000420000b0005800008, 0x100002400038000040000c0002d0004e],
    [0xd0003f0001a0001200054000080004e, 0x180004d0004a0001400017000580002d, 0x2000170001b0005b0003a0000b0000c, 0x1f0002c000290000c000420004200004, 0x5d0005c00027000460004e0001400038, 0x1b0005a000130001a0002e0000100024, 0x1c0002c0000300033000560004800010],
    [0x25000580003b0001a000570004500058, 0x24000550002500009000020004f00050, 0x5d00042000020002200028000000000f, 0x40005d000390003e000390002f0005e, 0x410000d000400003000021000210004d, 0x36000300001f0002d0000b0004c00059, 0xc000150003200031000110000800003],
    [0x58000500000f0005e0004d0005900003, 0x450004f000000002f000210004c00008, 0x57000020002800039000210000b00011, 0x1a00009000220003e000300002d00031, 0x3b000250000200039000400001f00032, 0x5800055000420005d0000d0003000015, 0x25000240005d0000400041000360000c],
    [0x270005e00052, 0x170006300020, 0x39000520004b],
    [0x52000200004b, 0x5e0006300052, 0x270001700039],
    [0x1d0003700015, 0x1b0004a0005d, 0x3f000090000e],
    [0x150005d0000e, 0x370004a00009, 0x1d0001b0003f],
    [0x56000550005c0004a000280005f0003e, 0x2f00025000200000a00007000600002f, 0x5c000490003f0000b000620001200037]⟩
  b2 := ⟨3,
    [0xa000350000f000520002d0001d00034, 0x320003c0004300010000060000d0005b, 0x340005f000450004d0002c0001900056, 0x1a0000f0002a000000005a0000b00063, 0x5b0004c000040000a0003a0003b0001a, 0x2b00037000450003b0001c0005000053, 0x3a0000f0000f00043000080004700015],
    [0x340005b00056000630001a0005300015, 0x1d0000d000190000b0003b0005000047, 0x2d000060002c0005a0003a0001c00008, 0x52000100004d000000000a0003b00043, 0xf00043000450002a00004000450000f, 0x350003c0005f0000f0004c000370000f, 0xa00032000340001a0005b0002b0003a],
    [0x61000420001c0001f000550002b0003c, 0x3b000540000b000600003f0003f0005c, 0x330001e00034000250004b0004e00040, 0xc000020001700053000450004e00047, 0x6200043000570002e000350004700042, 0x300001500051000220000f0005a0000f, 0x5a0003c0002a000460001e000500001d],
    [0x3c0005c0004000047000420000f0001d, 0x2b0003f0004e0004e000470005a00050, 0x550003f0004b00045000350000f0001e, 0x1f0006000025000530002e0002200046, 0x1c0000b000340001700057000510002a, 0x42000540001e0000200043000150003c, 0x610003b000330000c00062000300005a],
    [0x5c0002500028, 0xd000270001b, 0x1e000230004e],
    [0x280001b0004e, 0x250002700023, 0x5c0000d0001e],
    [0x640004800043, 0x240002f0002a, 0x410006200064],
    [0x430002a00064, 0x480002f00062, 0x640002400041],
    [0x5b000440001f0005c0003e000130005e, 0x1d000030001400053000540001500004, 0x2600039000390004a000100000400037]⟩

private theorem tripleCert_10_ok : checkTripleCert tripleCert_10 = true := by decide

private def tripleCert_11 : PackedTripleCert where
  n0 := 1
  n1 := 2
  n2 := 4
  M_rows := [0x5f0001f0003a00023000160004a000610005a0001f0003c000030000e0001800026000430005c0002c00034000400003c, 0x570001c000410004d0001c000460002d0001d000080004e0001300031000120005b000620000b00064000550001c0000e, 0x630003d0004b0002500029000130004d000520005a00032000170001c0002d00035000110005f0001e00047000210005b, 0x5100020000530005d0000f00064000520003200043000590000c000600001c00039000490004b0005d0000a0001500026, 0x3000340005e00062000070005f000090002c0005c0000d000280005600060000180000c0001900035000390000b00032, 0x310003d0000d000470001c00051000610000100007000240003c00014000510005d00020000640001b0001b0000100019, 0x5800004000450003500020000210005a0004000017000290003b0002f0003c0003d0005e0000e000630003f0002700050, 0x2e0000d000550005e0004a0000b000200003d00001000600004100028000120001a000490003700031000460000c00023, 0x1b000450005900032000430005d0003000029000480000e00031000180002b000140004a00063000190003c000040000b, 0x440001500061000290004b0004a0004d00008000330004f000310004d0004c000550005e0004500036000590003200010, 0x3b00007000120004d00015000210000c0000e0005d00014000220000d0001f000350001b0003c0001a000630003600002, 0xe0001a0002500007000600000f0002a0000d000500000200051000350001d00048000560001c000310001f000060002c, 0xa000110001f0001700049000110002900064000310002c00005000530003600052000300004300051000160004000037, 0xd00036000440000f0002f0005a00051000540006000000000460002c0003000003000490003c000010005a0000400002, 0x60000060003100031000410005f00010000320001400029000120000f000020002c0000b000640005a0000b000060003e, 0x1800010000350002c0003e00053000590001b00052000020004700022000470000f00025000340005a000140001c00033, 0x360003d0003600050000190004800030000110000b0001000003000010002c0000d0005e0004b0005a0001f0000900000, 0x5600003000350005c00041000130004c0000f000050005200020000540000b00037000100005300031000250001300013, 0x5a0001a000460003a0002a00027000110001e00055000430004c0002e00016000530001f0002c000310000b0005800062, 0x5c0003f0003f000560005c00033000490004b0001e00032000120002d000590004f0003a0005d000180001c0005700003]
  M_cols := [0x3c0000e0005b00026000320001900050000230000b00010000020002c00037000020003e0003300000000130006200003, 0x400001c00021000150000b00001000270000c000040003200036000060004000004000060001c00009000130005800057, 0x3400055000470000a000390001b0003f000460003c00059000630001f000160005a0000b000140001f000250000b0001c, 0x2c000640001e0005d000350001b000630003100019000360001a0003100051000010005a0005a0005a000310003100018, 0x5c0000b0005f0004b00019000640000e0003700063000450003c0001c000430003c00064000340004b000530002c0005d, 0x430006200011000490000c000200005e000490004a0005e0001b0005600030000490000b000250005e000100001f0003a, 0x260005b0003500039000180005d0003d0001a0001400055000350004800052000030002c0000f0000d00037000530004f, 0x18000120002d0001c00060000510003c000120002b0004c0001f0001d000360003000002000470002c0000b0001600059, 0xe000310001c0006000056000140002f00028000180004d0000d00035000530002c0000f0002200001000540002e0002d, 0x300013000170000c000280003c0003b00041000310003100022000510000500046000120004700003000200004c00012, 0x3c0004e00032000590000d0002400029000600000e0004f00014000020002c00000000290000200010000520004300032, 0x1f000080005a000430005c00007000170000100048000330005d00050000310006000014000520000b00005000550001e, 0x5a0001d00052000320002c00001000400003d00029000080000e0000d0006400054000320001b000110000f0001e0004b, 0x610002d0004d0005200009000610005a00020000300004d0000c0002a00029000510001000059000300004c0001100049, 0x4a0004600013000640005f00051000210000b0005d0004a000210000f000110005a0005f0005300048000130002700033, 0x160001c000290000f000070001c000200004a000430004b0001500060000490002f000410003e00019000410002a0005c, 0x230004d000250005d0006200047000350005e00032000290004d00007000170000f000310002c000500005c0003a00056, 0x3a000410004b000530005e0000d0004500055000590006100012000250001f0004400031000350003600035000460003f, 0x1f0001c0003d00020000340003d000040000d0004500015000070001a000110003600006000100003d000030001a0003f, 0x5f0005700063000510000300031000580002e0001b000440003b0000e0000a0000d000600001800036000560005a0005c]
  Minv_rows := [0x3a00021000350004c00048000240005c0005e0003b0001000063000210003f0005c000520001e0005400039000270000e, 0x52000300002000022000590005b0003100036000450006200061000520004a000510001e00045000300003e0004700009, 0x190000b0005a00056000200003100021000320005500055000300005d0005a0001f0005f0003400026000500004a0003a, 0x4c0000a0005d0005a0004f0002e0000a00059000200001e00005000420003e000260005500042000180001e0001500005, 0x12000220001d0005c000190004b000270001c0001f0001f000100006300027000540002a0001d0005f00035000550001e, 0x5800060000370003d0006200022000010004e00031000190005c0005d0000e0005d0002f0003e00036000530003f0001e, 0x2d0001d00016000180002d000500003100004000090000500035000410000b000480000a000200003a000170001e0003b, 0x59000630005600024000140000e000400001e000560003c000640003b00020000180002e0002d00017000540002a00025, 0x3d0002e0003c000430001e0001c0003d0005b00034000440004f0002700036000500002b0005d0002c0003d0006100057, 0x1b00039000250002c0000b0002d0004b0000a00036000540003e0005b00052000570004c000540001f000520004300009, 0x4f0000b00047000360000300029000370002d0005c000570005d000480004f0003100016000430003000050000340001e, 0x19000540002f00011000100001300025000620000f000050003d0005e0002a000340001600056000390000a000550000b, 0x590001e000060004d000550000300045000550005400027000520005a00032000270002b000040003e0002a0002c0005f, 0x3e00008000340005d0001f0003e00033000420005e0004f00004000250005500035000270005800010000640002a00047, 0x5f0001c0003a000210000c0001500047000080003b0001c0001b000180003f0005f000560001700028000410003300043, 0xd000180001600011000120004d000130002f0000e000320004f000370004e0001b000580000300022000640005900029, 0x600003c0001200064000090004e0001c000570003a0000f00005000180000c000380000c000220000c000190002d00061, 0x120005d000440003f0001f0005b000550002400028000250002f0005b0001b0000000028000120000800043000250001a, 0x540000300004000270003200001000250003d0002b000330000800047000380000c00028000050000a0001c0005c00018, 0x1e0002f0004900009000250005400034000100001e0001c0002700064000350005c0001400057000460003a0003e0003c]
  Minv_cols := [0xe000090003a000050001e0001e0003b0002500057000090001e0000b0005f000470004300029000610001a000180003c, 0x27000470004a00015000550003f0001e0002a000610004300034000550002c0002a00033000590002d000250005c0003e, 0x390003e000500001e000350005300017000540003d00052000500000a0002a00064000410006400019000430001c0003a, 0x540003000026000180005f000360003a000170002c0001f00030000390003e0001000028000220000c000080000a00046, 0x1e0004500034000420001d0003e000200002d0005d0005400043000560000400058000170000300022000120000500057, 0x520001e0005f000550002a0002f0000a0002e0002b0004c00016000160002b0002700056000580000c000280002800014, 0x5c000510001f00026000540005d00048000180005000057000310003400027000350005f0001b00038000000000c0005c, 0x3f0004a0005a0003e000270000e0000b0002000036000520004f0002a00032000550003f0004e0000c0001b0003800035, 0x21000520005d00042000630005d000410003b000270005b000480005e0005a000250001800037000180005b0004700064, 0x63000610003000005000100005c00035000640004f0003e0005d0003d00052000040001b0004f000050002f0000800027, 0x1000062000550001e0001f00019000050003c00044000540005700005000270004f0001c000320000f00025000330001c, 0x3b0004500055000200001f00031000090005600034000360005c0000f000540005e0003b0000e0003a000280002b0001e, 0x5e0003600032000590001c0004e000040001e0005b0000a0002d000620005500042000080002f00057000240003d00010, 0x5c00031000210000a000270000100031000400003d0004b0003700025000450003300047000130001c000550002500034, 0x240005b000310002e0004b00022000500000e0001c0002d0002900013000030003e000150004d0004e0005b0000100054, 0x4800059000200004f00019000620002d000140001e0000b0000300010000550001f0000c00012000090001f0003200025, 0x4c00022000560005a0005c0003d0001800024000430002c00036000110004d0005d0002100011000640003f0002700009, 0x35000200005a0005d0001d0003700016000560003c00025000470002f00006000340003a0001600012000440000400049, 0x21000300000b0000a00022000600001d000630002e000390000b000540001e000080001c000180003c0005d000030002f, 0x3a00052000190004c00012000580002d000590003d0001b0004f00019000590003e0005f0000d0006000012000540001e]
  b0 := ⟨1,
    [0x490002a000060000b0005a0003d00002, 0x2d000090002a000340001b0002600030, 0x64000550001b0000a0005e0005a00009, 0x5c0002b000410000b0003b0001700004, 0x3e000560005c00007000540004c00000, 0x3d000340000d0001800052000530001d, 0x1a000120005f00012000290000b0004c],
    [0x2000300000900004000000001d0004c, 0x3d000260005a000170004c000530000b, 0x5a0001b0005e0003b000540005200029, 0xb000340000a0000b000070001800012, 0x60002a0001b000410005c0000d0005f, 0x2a00009000550002b000560003400012, 0x490002d000640005c0003e0003d0001a],
    [0x390003e0002d0003e000590000700051, 0x46000310002e000000004e000530005e, 0x9000260005200039000550005c00059, 0x630004400015000080002f0000e0005c, 0x150004c000530000500047000590001c, 0x11000480001f000400002a000450004a, 0x38000140004400039000340002e00045],
    [0x510005e000590005c0001c0004a00045, 0x7000530005c0000e00059000450002e, 0x590004e000550002f000470002a00034, 0x3e000000003900008000050004000039, 0x2d0002e0005200015000530001f00044, 0x3e0003100026000440004c0004800014, 0x39000460000900063000150001100038],
    [0x350006200047, 0x530000400020, 0x2000630001d],
    [0x47000200001d, 0x620000400063, 0x350005300002],
    [0x360000f00055, 0x450005300062, 0x2c000110001b],
    [0x55000620001b, 0xf0005300011, 0x36000450002c],
    [0x4a000200003f0005c000320000c00010, 0x510000e0004c00019000600005b0003e, 0x3000260005b00063000500000100006]⟩
  b1 := ⟨2,
    [0x13000560005900002000330004b0004a, 0x55000610003c00056000400005f00049, 0x170005700060000050005c0000e00016, 0x90000900033000640001b0006000036, 0x6200026000220002b00032000320003d, 0x9000180005f000200004d000270002b, 0x160003c000270001a000490001b0005b],
    [0x4a0004900016000360003d0002b0005b, 0x4b0005f0000e0006000032000270001b, 0x33000400005c0001b000320004d00049, 0x20005600005000640002b000200001a, 0x590003c0006000033000220005f00027, 0x5600061000570000900026000180003c, 0x13000550001700009000620000900016],
    [0x370000b0005500017000640000400002, 0x560006400009000210004c0005a0000e, 0x1d00063000050001900013000420003a, 0x44000010005d000580003f000350000b, 0x100005f0002400049000570000a00012, 0x2f000570002700008000060005000014, 0x490000a00059000160005e0005a00004],
    [0x20000e0003a0000b000120001400004, 0x40005a00042000350000a000500005a, 0x640004c000130003f00057000060005e, 0x17000210001900058000490000800016, 0x5500009000050005d000240002700059, 0xb0006400063000010005f000570000a, 0x37000560001d00044000100002f00049],
    [0x290004d00049, 0x280003a00051, 0x240000d00055],
    [0x490005100055, 0x4d0003a0000d, 0x290002800024],
    [0x580004d00039, 0x490000e00006, 0x180002e00028],
    [0x390000600028, 0x4d0000e0002e, 0x580004900018],
    [0x280002300052000520002a0004000029, 0x4a0001b000290004100040000140000e, 0x3000170000b00030000380002400011]⟩
  b2 := ⟨4,
    [0x130005c000250004000016000350004a, 0x2600017000200001f000370002900056, 0x5b000510005b00062000430001100039, 0x490002b00010000370002c0002200057, 0x5000020000510000b000410001200045, 0x440002d0002e000510003d0001300010, 0x2b000430003c000080001e0000600063],
    [0x4a000560003900057000450001000063, 0x35000290001100022000120001300006, 0x1600037000430002c000410003d0001e, 0x400001f00062000370000b0005100008, 0x25000200005b00010000510002e0003c, 0x5c00017000510002b000200002d00043, 0x13000260005b0004900050000440002b],
    [0x8000290003200038000390000c00040, 0x60000520000900025000450003800064, 0x5000450001f0003d000190001800031, 0x40000110002d000400002e0000c0000d, 0x330001c0003e00044000510000900064, 0x470002100034000520005a0004f0003c, 0x14000640004c0004b00034000490000d],
    [0x4000064000310000d000640003c0000d, 0xc00038000180000c000090004f00049, 0x3900045000190002e000510005a00034, 0x38000250003d0004000044000520004b, 0x32000090001f0002d0003e000340004c, 0x290005200045000110001c0002100064, 0x8000600000500040000330004700014],
    [0x1b0000b00013, 0x5d0004f0002e, 0x420002000018],
    [0x130002e00018, 0xb0004f00020, 0x1b0005d00042],
    [0x5b000220002a, 0x63000000003d, 0x310000600063],
    [0x2a0003d00063, 0x220000000006, 0x5b0006300031],
    [0x200004f00012000530002d0005e00012, 0x410002a0003a00030000390005600046, 0xf00016000280005f000610003100020]⟩

private theorem tripleCert_11_ok : checkTripleCert tripleCert_11 = true := by decide

private def tripleCert_12 : PackedTripleCert where
  n0 := 1
  n1 := 2
  n2 := 5
  M_rows := [0x1f00030000560005f00048000440006200063000370002e0004100049000500005b0002f0003900017000420004500022, 0x460002d00047000020002c0003900011000080001b0004b00022000230001c00032000510000600030000550002e00014, 0x4a0002d0001c000410001f0001600009000510003500006000260000b000390001d000430003a00013000340000600032, 0x1e0001a000030002900001000230001a000610005000001000010005e0004000010000260001a0003000018000080002c, 0x3a000640005f00030000310005b00003000120002a0002500048000370004e00007000430004f0005d000590005600014, 0x62000110005e00001000240002300055000640000000053000330004000001000310002f000450005a0003e0003600008, 0x470004c00033000270004000048000500005d0005c000310004500045000540000d000290001d000590000b0006400062, 0x2f000000003f0005b0002200002000220000e000560003f0002b00064000290001900001000080002e000240003400019, 0x1a0005900045000450005a0003f000320005d00052000280000100025000410004a0000b0002000054000220004d00045, 0x10000220001c0001400002000550004e000360004c0001e00002000090002f0005800050000300003c00058000350002d, 0x2e0005a0003e0004100010000590005f0003000022000140004800018000210005d000110001d00049000600005700003, 0x57000150001d0002d0004f000160002e0004b0004500062000600003d0002d0003300062000640004a0000c0005100030, 0x4000590003000057000300003e0003e00002000520003c0004d0000d0005500008000080004b0004a00036000640000e, 0x1c000360005c000320005e00035000330001800054000630001d00027000430004800038000150003e000500005200008, 0x3b0005e000170001d00023000210003f000220005c0001b0002e0005400050000640004b0000a0004d000620005500049, 0x5500034000570000c00053000630004f00012000460001f0001c0002b000090003f000590002c000070005f000150000f, 0x4c000580003a00045000530005000018000340002f0004c000500000d000210001c000270002300013000080001b00004, 0x34000530005c00039000310000600024000470004d000510003b000240004e000260003c0005000062000360001c0005e, 0x3d0002d000310005e0005e0000d00055000280001c0005a0000e0001b000130002300045000270004a000500003000011, 0x160004d000610005400029000000001f00057000380005d00000000250000a000250000a0003300021000580002000005]
  M_cols := [0x2200014000320002c00014000080006200019000450002d00003000300000e00008000490000f000040005e0001100005, 0x450002e0000600008000560003600064000340004d000350005700051000640005200055000150001b0001c0003000020, 0x42000550003400018000590003e0000b000240002200058000600000c0003600050000620005f00008000360005000058, 0x170003000013000300005d0005a000590002e000540003c000490004a0004a0003e0004d0000700013000620004a00021, 0x39000060003a0001a0004f000450001d0000800020000300001d000640004b000150000a0002c00023000500002700033, 0x2f000510004300026000430002f00029000010000b00050000110006200008000380004b00059000270003c000450000a, 0x5b000320001d0001000007000310000d000190004a000580005d000330000800048000640003f0001c000260002300025, 0x500001c00039000400004e000010005400029000410002f000210002d00055000430005000009000210004e000130000a, 0x49000230000b0005e000370004000045000640002500009000180003d0000d00027000540002b0000d000240001b00025, 0x410002200026000010004800033000450002b000010000200048000600004d0001d0002e0001c000500003b0000e00000, 0x2e0004b00006000010002500053000310003f000280001e00014000620003c000630001b0001f0004c000510005a0005d, 0x370001b00035000500002a000000005c00056000520004c000220004500052000540005c000460002f0004d0001c00038, 0x6300008000510006100012000640005d0000e0005d00036000300004b0000200018000220001200034000470002800057, 0x6200011000090001a00003000550005000022000320004e0005f0002e0003e000330003f0004f0001800024000550001f, 0x440003900016000230005b0002300048000020003f0005500059000160003e00035000210006300050000060000d00000, 0x480002c0001f00001000310002400040000220005a00002000100004f000300005e000230005300053000310005e00029, 0x5f0000200041000290003000001000270005b0004500014000410002d00057000320001d0000c00045000390005e00054, 0x56000470001c000030005f0005e000330003f000450001c0003e0001d000300005c00017000570003a0005c0003100061, 0x300002d0002d0001a00064000110004c0000000059000220005a0001500059000360005e0003400058000530002d0004d, 0x1f000460004a0001e0003a00062000470002f0001a000100002e00057000040001c0003b000550004c000340003d00016]
  Minv_rows := [0x60000600003f00046000210005e00046000190001b0001e00028000640002b00063000620001e0005c000360001a00055, 0x1b000630004c000120005900018000490002a0002400004000160001f0001400061000450000a0002f00040000260005f, 0x250003a0001d0005600000000500000b000490001b000470002500057000040004b000530000c00008000320002700064, 0x3600003000430002b0004a0005e000390002e00047000410003e0000400061000440003b000580000b000410004d00052, 0x60002e0004c0005800027000550002d0001500023000620002100021000570005e0004200054000090003a0004d0001d, 0x100034000110002900034000220002400033000090002400040000080004b0000b0001700045000110005b0004000007, 0x570000500042000010001a00056000430003b0005a00011000440004f0004e00010000360002500015000350002e00016, 0x460003c000000000800042000040003d000620005b0005000056000210004e0001e0005100027000560005d0001400034, 0x2300012000110004d0003800057000220005f0001f0004400002000500003900031000000001a0004900002000290005a, 0x47000460004100036000500004f0001d00044000030005e00035000090002200053000360001c0005b000470004d, 0x37000480000f0002c00052000570000b0000800019000310002c00012000070001d000640003b0000f0005a0005300036, 0x250005d0004e000450000a000120000800046000370000f0001a000200003d0004300000000400004c000330002600064, 0x1000042000550004d0000f00029000340003d000480003b0004a0003a000640003d0003600015000580002a0002300034, 0x3a000070005b000550002f0003a0005a000260004c0003a0003d0002d0003c0001700061000460000100041000410005b, 0x40004d0001f00037000150002400005000330004b0002f0005200060000470005c0000e00048000050001d0002600023, 0x300005900045000450005f000080000b00018000450001500020000240001a0004b0004e000490000e0002e000280000b, 0x3e00037000310004a00020000260002900034000100005e000240005d0003e0001600034000080002200028000470001c, 0x130005d0005e0005f000140004300044000150005b00059000230003a0005e000360004a0004b00046000280000200057, 0x2800000000430002f0003a0004a0005e0001b000000001f000270001d000310003300020000580000e00039000510002b, 0x1e000150003b0000a0001500019000140001200025000580003f0003d00046000070003500041000320003e0006000026]
  Minv_cols := [0x550005f00064000520001d0000700016000340005a0004d0003600064000340005b000230000b0001c000570002b00026, 0x1a00026000270004d0004d000400002e00014000290004700053000260002300041000260002800047000020005100060, 0x360004000032000410003a0005b000350005d000020005b0005a000330002a000410001d0002e0002800028000390003e, 0x5c0002f000080000b00009000110001500056000490001c0000f0004c0005800001000050000e00022000460000e00032, 0x1e0000a0000c00058000540004500025000270001a000360003b0004000015000460004800049000080004b0005800041, 0x6200045000530003b000420001700036000510000000053000640000000036000610000e0004e000340004a0002000035, 0x63000610004b000440005e0000b000100001e00031000220001d000430003d000170005c0004b00016000360003300007, 0x2b000140000400061000570004b0004e0004e0003900009000070003d000640003c000470001a0003e0005e0003100046, 0x640001f000570000400021000080004f00021000500003500012000200003a0002d00060000240005d0003a0001d0003d, 0x2800016000250003e00021000400004400056000020005e0002c0001a0004a0003d00052000200002400023000270003f, 0x1e000040004700041000620002400011000500004400003000310000f0003b0003a0002f000150005e000590001f00058, 0x1b000240001b0004700023000090005a0005b0001f000440001900037000480004c0004b00045000100005b0000000025, 0x190002a000490002e00015000330003b000620005f0001d00008000460003d00026000330001800034000150001b00012, 0x46000490000b000390002d00024000430003d000220004f0000b00008000340005a000050000b00029000440005e00014, 0x5e00018000500005e0005500022000560000400057000500005700012000290003a000240000800026000430004a00019, 0x2100059000000004a00027000340001a000420003800036000520000a0000f0002f000150005f00020000140003a00015, 0x4600012000560002b000580002900001000080004d000410002c000450004d0005500037000450004a0005f0002f0000a, 0x3f0004c0001d000430004c00011000420000000011000460000f0004e000550005b0001f00045000310005e000430003b, 0x60000630003a000030002e00034000050003c0001200047000480005d00042000070004d00059000370005d0000000015, 0x600001b00025000360000600001000570004600023000000003700025000100003a00004000300003e00013000280001e]
  b0 := ⟨1,
    [0x2c000380005a0005a000320002c00014, 0x4000520003c0000500030000270004d, 0x400004d00035000370000d0005a00044, 0x220003c0001d000090002c0003c0000c, 0x10000590004f00007000080004800049, 0x7000140001100023000260003e00014, 0x11000120002e0002a000010002e00043],
    [0x140004d000440000c000490001400043, 0x2c000270005a0003c000480003e0002e, 0x32000300000d0002c000080002600001, 0x5a00005000370000900007000230002a, 0x5a0003c000350001d0004f000110002e, 0x38000520004d0003c000590001400012, 0x2c000040004000022000100000700011],
    [0x1c00011000410003c000550004c00004, 0x4d00039000250005700046000140000b, 0x3b0005a0000c0004900007000560005d, 0x2600042000610005400003000170003d, 0x380001c000560002a000050001100055, 0x60000310004300027000620004c00054, 0x14000410005000005000040004000014],
    [0x40000b0005d0003d000550005400014, 0x4c000140005600017000110004c00040, 0x55000460000700003000050006200004, 0x3c0005700049000540002a0002700005, 0x41000250000c00061000560004300050, 0x11000390005a000420001c0003100041, 0x1c0004d0003b00026000380006000014],
    [0x490000500038, 0x210005900056, 0x90000f00006],
    [0x380005600006, 0x5000590000f, 0x490002100009],
    [0x620002d00010, 0x3c000310003b, 0x30000170005d],
    [0x100003b0005d, 0x2d0003100017, 0x620003c00030],
    [0x590003200038000050002c0005700038, 0x17000200002d0001c000000000800042, 0x380004d0000e0001b0000a000580001b]⟩
  b1 := ⟨2,
    [0x100004b000120000c000510001000027, 0x350002f0004300054000600000200035, 0x5000590004900031000390002d0002f, 0xe0002c0002d00012000460001f00021, 0x5a0001800000000100000e0000d0005c, 0x5d000470005e00042000580001800010, 0x330005d0002000034000620002600010],
    [0x27000350002f000210005c0001000010, 0x10000020002d0001f0000d0001800026, 0x510006000039000460000e0005800062, 0xc000540003100012000100004200034, 0x1200043000490002d000000005e00020, 0x4b0002f000590002c00018000470005d, 0x1000035000050000e0005a0005d00033],
    [0x22000390002600030000140002b0001b, 0xe0004e000250002f000220000e0001d, 0x20000030003c00024000580000000008, 0x1300027000180004800020000520004f, 0x5b00035000040005c0000b0004b00039, 0x5f000080002700033000170003600061, 0x2c000600003e00015000030002c00000],
    [0x1b0001d000080004f000390006100000, 0x2b0000e00000000520004b000360002c, 0x140002200058000200000b0001700003, 0x300002f00024000480005c0003300015, 0x26000250003c0001800004000270003e, 0x390004e0000300027000350000800060, 0x220000e00020000130005b0005f0002c],
    [0x530001a00045, 0x10000100024, 0x40000800052],
    [0x450002400052, 0x1a0000100008, 0x530000100004],
    [0x5f0002b0004a, 0x540000900024, 0x1f0003c0001b],
    [0x4a000240001b, 0x2b000090003c, 0x5f000540001f],
    [0x2a000630000b000090003c000150005a, 0x1b00033000260002b0004d0005000001, 0x47000130002300032000500001d0004b]⟩
  b2 := ⟨5,
    [0x3b0002300025000560001b000050005a, 0x2b00030000060001b0002d000210003c, 0x150003c0006400017000370003e0000c, 0x2e0003a000070003000011000610003d, 0x4a0001e00049000490001d0000b0001c, 0x5f000330002b000230002e0001900023, 0x5800007000640002b000410003800055],
    [0x5a0003c0000c0003d0001c0002300055, 0x5000210003e000610000b0001900038, 0x1b0002d00037000110001d0002e00041, 0x560001b000170003000049000230002b, 0x25000060006400007000490002b00064, 0x23000300003c0003a0001e0003300007, 0x3b0002b000150002e0004a0005f00058],
    [0x630000f000470002e0002d0004c00029, 0x200001800028000230004f0003900019, 0x580004c0003a0002d000180004c00006, 0x510001f0004500056000030006400010, 0x43000210002d0005d00053000100001a, 0x38000530006000023000110001100007, 0x30003a0005c00057000440005600048],
    [0x290001900006000100001a0000700048, 0x4c000390004c00064000100001100056, 0x2d0004f0001800003000530001100044, 0x2e000230002d000560005d0002300057, 0x47000280003a000450002d000600005c, 0xf000180004c0001f00021000530003a, 0x63000200005800051000430003800003],
    [0x4a000460000c, 0x26000130003b, 0x4e0003c00041],
    [0xc0003b00041, 0x46000130003c, 0x4a000260004e],
    [0x210001500050, 0x470000f0000d, 0x5e000250003a],
    [0x500000d0003a, 0x150000f00025, 0x21000470005e],
    [0x1d000010002e000370003b0002200027, 0x44000280004600043000280006200012, 0x33000070001c000500005d0002400048]⟩

private theorem tripleCert_12_ok : checkTripleCert tripleCert_12 = true := by decide

private def tripleCert_13 : PackedTripleCert where
  n0 := 1
  n1 := 3
  n2 := 4
  M_rows := [0x570002a00036000530005d0000a00032000350001b000530001f0002c0002c0000e000130001500015000100002d00021, 0x540000c0000d000160005c0002300018000220001a00000000300001400009000360000800053000350001a0005100047, 0x52000160002b0003f000330005500043000020005c000260002d00051000240004f00005000630000b000030003e0000e, 0x420001d00051000480002700010000270004a0002e0005b0004f000470001c0005d000200006300012000350003200050, 0x14000320001f000140005000008000610002700032000450002e00040000430000c000070002c00012000270004a00063, 0x30000280001a0000c000640005700044000290005300044000440006400014000620002a0002e000290000e0005300003, 0x8000130001a0004f00057000610003c00064000080003f0003b000300004d000310005e0001300029000380002b00062, 0x3c000320002b0006200027000020003800043000190001f000000004900023000490002b0002b0001100006000540002a, 0x300015000090003500049000090003100023000400003b00009000470005b00040000500004500019000090001100004, 0x4000052000170000b000010006000013000580004400049000350003200025000250004600010000160003a0006300015, 0x220000e0003e0002d000370003e00037000110005a00010000090000b000260000d000380004e000540002e0003500006, 0x30000590001c0003e0003b0000e0002a000170000e0000f000360000d00044000460003a0000200024000210005b0005d, 0x32000210003300048000570006300035000500000100000000490000d0005f0002e0002b0002a00014000010002000009, 0x290002c0002600003000550003f0005f0004600000000000000f00017000020003a00007000130002b00061000060005c, 0x130004400050000360000c000490002f000370004d00046000460004b0005a000570003f0004f00061000310002e00036, 0x1400021000310000b0003700002000290005c000000004d0000e0000c0002900050000500000e00054000100005300036, 0x30000050001a000500001f000320002e00048000410003b000210000a000570002a0001100009000330001e0003f00064, 0x310003e000030002600032000230001f0002100007000620003e00028000520002600011000210000b0001d0001e0005d, 0x3a000220005a0002b0002100006000460001900023000250000e00022000100004c000640002f0003500018000330002b, 0x3b000180003a000410003e0002500043000170002200015000370003b000440001900050000130003d000620001f00006]
  M_cols := [0x21000470000e000500006300003000620002a0000400015000060005d000090005c0003600036000640005d0002b00006, 0x2d000510003e000320004a000530002b000540001100063000350005b00020000060002e000530003f0001e000330001f, 0x100001a0000300035000270000e0003800006000090003a0002e00021000010006100031000100001e0001d0001800062, 0x15000350000b000120001200029000290001100019000160005400024000140002b0006100054000330000b000350003d, 0x150005300063000630002c0002e000130002b00045000100004e000020002a000130004f0000e00009000210002f00013, 0x13000080000500020000070002a0005e0002b0005000046000380003a0002b000070003f0005000011000110006400050, 0xe000360004f0005d0000c00062000310004900040000250000d000460002e0003a00057000500002a000260004c00019, 0x2c00009000240001c00043000140004d000230005b0002500026000440005f000020005a0002900057000520001000044, 0x2c0001400051000470004000064000300004900047000320000b0000d0000d000170004b0000c0000a00028000220003b, 0x1f000300002d0004f0002e000440003b0000000009000350000900036000490000f000460000e000210003e0000e00037, 0x5300000000260005b00045000440003f0001f0003b00049000100000f0000000000000460004d0003b000620002500015, 0x1b0001a0005c0002e0003200053000080001900040000440005a0000e00001000000004d0000000041000070002300022, 0x3500022000020004a00027000290006400043000230005800011000170005000046000370005c00048000210001900017, 0x3200018000430002700061000440003c000380003100013000370002a000350005f0002f000290002e0001f0004600043, 0xa0002300055000100000800057000610000200009000600003e0000e000630003f000490000200032000230000600025, 0x5d0005c0003300027000500006400057000270004900001000370003b00057000550000c000370001f00032000210003e, 0x53000160003f00048000140000c0004f00062000350000b0002d0003e0004800003000360000b00050000260002b00041, 0x360000d0002b000510001f0001a0001a0002b00009000170003e0001c000330002600050000310001a000030005a0003a, 0x2a0000c000160001d0003200028000130003200015000520000e00059000210002c0004400021000050003e0002200018, 0x570005400052000420001400030000080003c000030004000022000300003200029000130001400030000310003a0003b]
  Minv_rows := [0x2100061000340004500019000290000a0004b0004800050000080003c000590004b000310004c0003c000410001600002, 0x5200008000220001200038000300004800013000550005d00029000100003e000570002c00011000280004d0000d00056, 0x29000560004d00033000450002b0005c0004a00012000230002f00005000120001c0002e000110005d0003d000530004b, 0x380001a00015000420004300039000140006200058000070005c00017000530000c0002c0004a00060000490004200005, 0x5000490004d000250005800054000420001000055000410004c0003c000260002b000450003000002000030001300038, 0x48000230003c0004f0001c0002000026000130003a000450002a000240001400048000190005100016000530001a00021, 0x240005d000110004f0004a0005d000120002e0002a0004c0002a0006200055000330001900055000260001a0004400026, 0x510000e000170000300036000310003e00056000110006300011000110004a0000c0003e000620005d0004a0005c00044, 0x130006000023000230000a0000700060000550003300049000220000f000250002b00040000110003100055000140002a, 0x170002e00042000310001200018000160005f000150002f0004f000530003b0005c00016000260003c000560001e0002a, 0x1700009000320005a0001e000070001d00047000430004b000630003e0003d000090000b00004000070004a0004c00060, 0x1b000630004a0000e00048000440004f0005f0002e00012000030000300014000120004d000640000a0001d0000b0005f, 0x34000350000e000380001800015000250000700016000370001b00034000360003d0005e0001e000380000d00022, 0x4f0004f0004c000400004a0003500025000390003c0002f00041000160002b00045000300000200040000630004f0002b, 0x5c00051000440004a000370004700005000470001f0005b00000000140002100029000190000a0003d0004c0005800026, 0x28000290005a0004f00064000240006100055000240003c0005000021000250004700024000630002700012000120002f, 0x3f000560005c0002f000060005f0000b0004e000320004900052000580004d0001d00001000000004100039000280001b, 0x4d000370003f00008000550004b00029000180002300047000530005b0004b000530001f0001c00030000360000f0003c, 0x4e000230000b000160003a000550003200023000150003800009000460001a00042000300002700044000640001e0004f, 0x5800054000300003c000420003a0001c0001e00053000220004e0004e0001f0001b00062000560002e000090002c0000a]
  Minv_cols := [0x2000560004b00005000380002100026000440002a0002a000600005f000220002b000260002f0001b0003c0004f0000a, 0x160000d0005300042000130001a000440005c000140001e0004c0000b0000d0004f0005800012000280000f0001e0002c, 0x410004d0003d0004900003000530001a0004a00055000560004a0001d00038000630004c0001200039000360006400009, 0x3c000280005d000600000200016000260005d000310003c000070000a0001e000400003d000270004100030000440002e, 0x4c00011000110004a00030000510005500062000110002600004000640005e000020000a00063000000001c0002700056, 0x310002c0002e0002c0004500019000190003e00040000160000b0004d0003d000300001900024000010001f0003000062, 0x4b000570001c0000c0002b00048000330000c0002b0005c0000900012000360004500029000470001d00053000420001b, 0x590003e00012000530002600014000550004a000250003b0003d00014000340002b00021000250004d0004b0001a0001f, 0x3c0001000005000170003c0002400062000110000f000530003e000030001b000160001400021000580005b000460004e, 0x8000290002f0005c0004c0002a0002a00011000220004f0006300003000370004100000000500005200053000090004e, 0x500005d000230000700041000450004c00063000490002f0004b00012000160002f0005b0003c00049000470003800022, 0x48000550001200058000550003a0002a000110003300015000430002e000070003c0001f0002400032000230001500053, 0x4b000130004a0006200010000130002e00056000550005f000470005f000250003900047000550004e00018000230001e, 0xa000480005c000140004200026000120003e00060000160001d0004f000150002500005000610000b00029000320001c, 0x29000300002b0003900054000200005d0003100007000180000700044000180003500047000240005f0004b000550003a, 0x19000380004500043000580001c0004a000360000a000120001e00048000380004a000370006400006000550003a00042, 0x45000120003300042000250004f0004f0000300023000310005a0000e0000e000400004a0004f0002f00008000160003c, 0x34000220004d000150004d0003c00011000170002300042000320004a000350004c000440005a0005c0003f0000b00030, 0x6100008000560001a00049000230005d0000e000600002e0000900063000340004f000510002900056000370002300054, 0x21000520002900038000050004800024000510001300017000170001b000000004f0005c000280003f0004d0004e00058]
  b0 := ⟨1,
    [0x3600040000170005300022000370003c, 0x2c000310003f000550005e000590005e, 0xc00032000050003d000050006300063, 0x130003a0000800039000580004c00064, 0x510001c00009000240000e0004b00032, 0x4a00032000630002e00050000190001c, 0x5c00024000010003b000200002e00062],
    [0x3c0005e0006300064000320001c00062, 0x3700059000630004c0004b000190002e, 0x220005e00005000580000e0005000020, 0x53000550003d00039000240002e0003b, 0x170003f0000500008000090006300001, 0x4000031000320003a0001c0003200024, 0x360002c0000c00013000510004a0005c],
    [0x160000600035000310003d0000800020, 0x430001d0001700057000580006300060, 0x3600043000160004b0001d0002b0005f, 0x3a00028000110001a000360002300005, 0x9000120002200021000400003300026, 0x42000190000d00020000520003500042, 0x32000080004c000200004d0001a00013],
    [0x20000600005f00005000260004200013, 0x8000630002b0002300033000350001a, 0x3d000580001d0003600040000520004d, 0x31000570004b0001a000210002000020, 0x35000170001600011000220000d0004c, 0x60001d0004300028000120001900008, 0x1600043000360003a000090004200032],
    [0x4c0004000038, 0x5000420002b, 0x1b0003100015],
    [0x380002b00015, 0x400004200031, 0x4c000050001b],
    [0x60000f0003e, 0x10000200036, 0x100004300043],
    [0x3e0003600043, 0xf0000200043, 0x60000100010],
    [0x3f000210000200055000170002f00034, 0x90003400018000400005c0005f00005, 0x1700009000540005b000450002500046]⟩
  b1 := ⟨3,
    [0x5e0000f0004f00017000170004700060, 0x1d00021000530001a000050005900034, 0x2800028000010002b000340005c00008, 0x1b0004d000220002f0003c0000400051, 0x450000a0005600051000500004600022, 0x26000020001c000120002e0000200010, 0x18000030004f00000000590003800058],
    [0x60000340000800051000220001000058, 0x47000590005c00004000460000200038, 0x1700005000340003c000500002e00059, 0x170001a0002b0002f000510001200000, 0x4f000530000100022000560001c0004f, 0xf00021000280004d0000a0000200003, 0x5e0001d000280001b000450002600018],
    [0x550004700022000270001f0001d00059, 0x1d0002d00032000380001f0005900045, 0x5e00041000270004e000460002a00001, 0x21000450001b00015000230002f00020, 0x70005c0003800010000260002e00001, 0x1e0001d0000c00008000330004300037, 0x570000d0001e00052000320003000008],
    [0x59000450000100020000010003700008, 0x1d000590002a0002f0002e0004300030, 0x1f0001f0004600023000260003300032, 0x27000380004e00015000100000800052, 0x2200032000270001b000380000c0001e, 0x470002d00041000450005c0001d0000d, 0x550001d0005e00021000070001e00057],
    [0x510004000021, 0x4700010, 0x400001e00000],
    [0x210001000000, 0x40000470001e, 0x510000000040],
    [0x180000200061, 0x21000410002d, 0x180005000001],
    [0x610002d00001, 0x20004100050, 0x180002100018],
    [0x5e0002400049000220004a0001100009, 0x10003c0000f0001f00012000120002b, 0x30004d0001c00059000300003c0003f]⟩
  b2 := ⟨4,
    [0x5c00059000320005d000240005700059, 0xd00014000000005a000010001400057, 0x27000350001a0000500025000360005e, 0x270004a0000b0005f000360000200062, 0x18000010001d0001b0001a0004300021, 0x330001e0003100015000430001200018, 0x45000430000b0002b0003d0000c00035],
    [0x59000570005e00062000210001800035, 0x5700014000360000200043000120000c, 0x240000100025000360001a000430003d, 0x5d0005a000050005f0001b000150002b, 0x32000000001a0000b0001d000310000b, 0x5900014000350004a000010001e00043, 0x5c0000d0002700027000180003300045],
    [0x290001e0000f00035000250004400019, 0x11000460004400053000090001600027, 0x4e00018000610004f000450005400048, 0x4f0004d00061000200000b000540001a, 0x2d0001f0000e00001000330005a00026, 0xb0004c0002a00030000280004d0001f, 0x5d00049000070003f00055000280003c],
    [0x1900027000480001a000260001f0003c, 0x440001600054000540005a0004d00028, 0x2500009000450000b000330002800055, 0x35000530004f0002000001000300003f, 0xf0004400061000610000e0002a00007, 0x1e00046000180004d0001f0004c00049, 0x29000110004e0004f0002d0000b0005d],
    [0x550002d00050, 0x3c0002200028, 0x56000230002e],
    [0x50000280002e, 0x2d0002200023, 0x550003c00056],
    [0x580004500032, 0x450004100061, 0x2f000430002b],
    [0x32000610002b, 0x450004100043, 0x58000450002f],
    [0x1000002000220003400038000050002c, 0x280002a00027000380004a0004d0000e, 0x320006400053000060002b000080001d]⟩

private theorem tripleCert_13_ok : checkTripleCert tripleCert_13 = true := by decide

private def tripleCert_14 : PackedTripleCert where
  n0 := 1
  n1 := 3
  n2 := 5
  M_rows := [0x120004900018000140001b0003400023000550003500022000620000f000620003d000440002f0002f0000a0000400011, 0x220002a0001f000280003f00063000220003000049000270005900037000300003a000570005400054000450004e0003b, 0x37000110002900062000210001a0000600049000280001e00056000540001e000640000a000460003d0004f0001000053, 0x58000060001e000070002f000100005a0001b00037000020000500031000190003400033000430001b000630000100020, 0x630002f0001a0006000024000020001c000090003800025000190001c000480004c0001c000210000b0001f0000a0000f, 0x480001b0005f000100004200055000360001800026000620003b0001d00033000180000a00025000060005b0002f00021, 0x3600029000200003e0005e000640003900050000640004b0001d0001c00030000130002c0004700034000460003700020, 0x560005200045000030004a0003a0002a0006200000000610000a000230004300024000040003600040000490002e00031, 0x160001f000220005c000490002c0002800026000350000e000010004c0005400031000510005800027000120002f0002f, 0xf0002600036000500001b0001d0002c0001b000470002d000520000000032000250004d0001100044000180002f0001b, 0xe0000900045000170004800025000130000500031000420003d0002e000410003c0001b00033000150005a0005d0004d, 0x610005b000470003d0002a0003d000480003a0001e0002b000530003d00011000540004e0005c0004100007000400005e, 0x50000450002400047000330005e0001d0003e0003a0002f0001d000370004100011000060003b0005a0002e000370005b, 0x11000080002f000460000d0006000064000460002200060000150002e000550000300061000040004200042000070002f, 0x31000400005e0003d0004d0002f00058000300000d000510001a0000d0002c0003400004000520001e0004d0005300037, 0x3e000010000f0000c000090001e0000500043000260001700023000040005800021000560000500039000640004a00060, 0x17000300001500064000440000400062000070001600029000640000b0000f000060001f00048000460005d0001a00009, 0x5f00020000380005f000410001d000360004a00045000040004a000380003100014000110001e0003e000490000900009, 0x1d000410005600013000550005e000390000b000550001e00029000070003b00059000120001b00003000540005e00014, 0x60002f0000e000570005200059000200004d0001600022000320003a0005a000290002d00050000110002e000470000c]
  M_cols := [0x110003b00053000200000f0002100020000310002f0001b0004d0005e0005b0002f00037000600000900009000140000c, 0x40004e00010000010000a0002f000370002e0002f0002f0005d000400003700007000530004a0001a000090005e00047, 0xa000450004f000630001f0005b000460004900012000180005a000070002e000420004d000640005d00049000540002e, 0x2f000540003d0001b0000b000060003400040000270004400015000410005a000420001e00039000460003e0000300011, 0x2f000540004600043000210002500047000360005800011000330005c0003b000040005200005000480001e0001b00050, 0x44000570000a000330001c0000a0002c00004000510004d0001b0004e000060006100004000560001f00011000120002d, 0x3d0003a00064000340004c00018000130002400031000250003c000540001100003000340002100006000140005900029, 0x62000300001e00019000480003300030000430005400032000410001100041000550002c000580000f000310003b0005a, 0xf0003700054000310001c0001d0001c000230004c000000002e0003d000370002e0000d000040000b00038000070003a, 0x62000590005600005000190003b0001d0000a00001000520003d000530001d000150001a00023000640004a0002900032, 0x22000270001e0000200025000620004b000610000e0002d000420002b0002f00060000510001700029000040001e00022, 0x35000490002800037000380002600064000000003500047000310001e0003a000220000d0002600016000450005500016, 0x5500030000490001b00009000180005000062000260001b000050003a0003e000460003000043000070004a0000b0004d, 0x2300022000060005a0001c00036000390002a000280002c00013000480001d00064000580000500062000360003900020, 0x34000630001a000100000200055000640003a0002c0001d000250003d0005e000600002f0001e000040001d0005e00059, 0x1b0003f000210002f00024000420005e0004a000490001b000480002a000330000d0004d0000900044000410005500052, 0x1400028000620000700060000100003e000030005c00050000170003d00047000460003d0000c000640005f0001300057, 0x180001f000290001e0001a0005f000200004500022000360004500047000240002f0005e0000f0001500038000560000e, 0x490002a00011000060002f0001b00029000520001f00026000090005b000450000800040000010003000020000410002f, 0x1200022000370005800063000480003600056000160000f0000e000610005000011000310003e000170005f0001d00006]
  Minv_rows := [0x4e00015000460005a000190005c000200002400049000410004a000320005b0003d0002c00044000420001a0005c0004b, 0x4000600004f0002f00022000220006400042000330003f0005c0000b000210002d000410004500064000100004600040, 0x3d0000a000620001a000150002b000060000b0000800009000530005c0002b000610005f00008000410001e000640000b, 0x58000000003600047000030002a000110004b000620003400054000580005c0005f0004b00048000370002d0005700046, 0x2b00021000550005c000290002c00063000400003f000050005200042000130002c00037000140004800046000050005c, 0x2a000340006300055000100000f000440004b0005800013000270000c000420001900038000280003500017000610004c, 0x480004f00017000110001b000240001d000490002d00021000520002a0004f00013000200003400055000270004a00050, 0x4d0004d000140005c0005c000620004a00010000490001f000580000f0001f00004000630002d0002c000550004f0003f, 0x460005c0003c000340002f0000c000250004b0000b000020003c00047000450002100008000430003f00045000040005a, 0x3900033000290001600028000250003800058000440003d0000e000130004900023000360003c0001d000420001e00045, 0x43000580001f0001200049000390003b0005d0002b000280002b0001c000390004e0004f00044000440001c0000600013, 0x4000007000300003800043000570000000023000190003f00045000590003a000110002d000360000e00029000530004e, 0x410005d0004e000300002700054000500002500012000100004b0002f0000f0005600005000310004b0001a000190001f, 0x530005200063000340000a00047000320000b0002e00039000120002d00013000170004700044000520000e0001800040, 0xb00030000320003e0005e0002800055000580005b000090005d0000d0004f00034000620003b00023000460003700044, 0x3e00057000320002c000380002a0005f00029000040003d0003e0001c0000600008000340003200000000490004f00047, 0x170003c000470001c0001a00018000300001f0002d0003a00055000540006200017000240006100004000150003400016, 0x4e000430003400042000330005c000100003a00022000580000b0000400027000350003e0001b00033000300003f00034, 0x300003f0003a0001700057000450003800048000220000c00045000190005600064000230001c000480000d0000300049, 0x32000350005a0003a0005b000480003c0000600043000600000b000610005b0005e0003200024000350003b0003d00013]
  Minv_cols := [0x4b000400000b000460005c0004c000500003f0005a00045000130004e0001f00040000440004700016000340004900013, 0x5c00046000640005700005000610004a0004f000040001e00006000530001900018000370004f000340003f000030003d, 0x1a000100001e0002d0004600017000270005500045000420001c000290001a0000e000460004900015000300000d0003b, 0x420006400041000370004800035000550002c0003f0001d000440000e0004b00052000230000000004000330004800035, 0x440004500008000480001400028000340002d000430003c000440003600031000440003b00032000610001b0001c00024, 0x2c000410005f0004b0003700038000200006300008000360004f0002d00005000470006200034000240003e0002300032, 0x3d0002d000610005f0002c00019000130000400021000230004e00011000560001700034000080001700035000640005e, 0x5b000210002b0005c00013000420004f0001f0004500049000390003a0000f000130004f000060006200027000560005b, 0x320000b0005c00058000420000c0002a0000f00047000130001c000590002f0002d0000d0001c00054000040001900061, 0x4a0005c0005300054000520002700052000580003c0000e0002b000450004b000120005d0003e000550000b000450000b, 0x410003f00009000340000500013000210001f000020003d000280003f0001000039000090003d0003a000580000c00060, 0x490003300008000620003f000580002d000490000b000440002b00019000120002e0005b000040002d000220002200043, 0x24000420000b0004b000400004b00049000100004b000580005d00023000250000b00058000290001f0003a0004800006, 0x2000064000060001100063000440001d0004a00025000380003b000000005000032000550005f0003000010000380003c, 0x5c000220002b0002a0002c0000f00024000620000c0002500039000570005400047000280002a000180005c0004500048, 0x1900022000150000300029000100001b0005c0002f000280004900043000270000a0005e000380001a00033000570005b, 0x5a0002f0001a000470005c00055000110005c0003400016000120003800030000340003e0002c0001c00042000170003a, 0x460004f0006200036000550006300017000140003c000290001f000300004e00063000320003200047000340003a0005a, 0x15000600000a0000000021000340004f0004d0005c0003300058000070005d0005200030000570003c000430003f00035, 0x4e000040003d000580002b0002a000480004d0004600039000430004000041000530000b0003e000170004e0003000032]
  b0 := ⟨1,
    [0x440004d0002f0003a0002d0002b0000b, 0x57000570003d000310000a0002f00045, 0x4700052000470001b00059000370000c, 0x430003a0000000031000400004900037, 0x15000010003500010000510004f00030, 0x2500037000110002a000540004900034, 0x3a000580000d0005f0001e0001e00057],
    [0xb000450000c00037000300003400057, 0x2b0002f00037000490004f000490001e, 0x2d0000a000590004000051000540001e, 0x3a000310001b00031000100002a0005f, 0x2f0003d000470000000035000110000d, 0x4d00057000520003a000010003700058, 0x4400057000470004300015000250003a],
    [0x550001400003000140005d0005a0003d, 0x480004e0001d00044000150003000019, 0x90003f000200004c000250004d00002, 0x57000360004c000160002d0000f00061, 0x9000490005f0001500061000230003d, 0x33000240000300023000620003800054, 0x3a0001200028000590000d0005000038],
    [0x3d0001900002000610003d0005400038, 0x5a000300004d0000f000230003800050, 0x5d00015000250002d00061000620000d, 0x14000440004c00016000150002300059, 0x30001d000200004c0005f0000300028, 0x140004e0003f00036000490002400012, 0x5500048000090005700009000330003a],
    [0x1d0002500018, 0x160005d, 0x2f0003e00034],
    [0x180005d00034, 0x25000160003e, 0x1d000000002f],
    [0x560004b00057, 0x440005700032, 0x3a0000f0000e],
    [0x57000320000e, 0x4b000570000f, 0x56000440003a],
    [0x140004d000550005a000260002200032, 0x200010000240000c000010003b00053, 0x14000390005a000090004b0002100049]⟩
  b1 := ⟨3,
    [0x20001f000040001b0004a0001300027, 0x460003a000260004900032000120004d, 0x1700034000420004a000240003400014, 0x4f000620005f0001a0005d0005f00016, 0x5000060000e0000c00022000200001f, 0x140001c0001a0005f0001e000500004e, 0x400004e000270005d0005c0003f00058],
    [0x270004d00014000160001f0004e00058, 0x1300012000340005f00020000500003f, 0x4a00032000240005d000220001e0005c, 0x1b000490004a0001a0000c0005f0005d, 0x400026000420005f0000e0001a00027, 0x1f0003a0003400062000060001c0004e, 0x200046000170004f000050001400040],
    [0x2a000590006300017000330002100046, 0x3800006000070004f000590002d00025, 0x41000100001300020000200004000034, 0x2300018000190002b000220004a0003b, 0x4200040000260005300064000320000e, 0x70001a0004b0005200019000000002c, 0x4c0002b000430005e000140000700037],
    [0x4600025000340003b0000e0002c00037, 0x210002d000400004a000320000000007, 0x33000590002000022000640001900014, 0x170004f000200002b00053000520005e, 0x63000070001300019000260004b00043, 0x59000060001000018000400001a0002b, 0x2a00038000410002300042000070004c],
    [0x460000c0001d, 0x64000030005d, 0x140004c00019],
    [0x1d0005d00019, 0xc000030004c, 0x460006400014],
    [0x2c0002300018, 0x250003100006, 0x3e000440001c],
    [0x18000060001c, 0x230003100044, 0x2c000250003e],
    [0x20005800015000380002d000120004a, 0x4f000540002000046000160002b0001a, 0x2b00056000230000700042000520005a]⟩
  b2 := ⟨5,
    [0x4d0003e0003f0001a000470004b00008, 0x550001000040000440004b0002a0002f, 0x1c000160005200060000520003e00010, 0x23000100005e000010004b000390002d, 0x61000640002d0001d0000900041, 0xa0001b0000f0001a000160004000060, 0x130004c0005400033000000002d00036],
    [0x80002f000100002d000410006000036, 0x4b0002a0003e0003900009000400002d, 0x470004b000520004b0001d0001600000, 0x1a0004400060000010002d0001a00033, 0x3f00040000520005e000640000f00054, 0x3e000100001600010000610001b0004c, 0x4d000550001c00023000000000a00013],
    [0x5e00038000300002e000350001f00004, 0x1e00064000140002e000030001d00053, 0xf0002f0002900044000120006200028, 0x11000270002b0001a000110001d00005, 0x2700047000440000a00000000280003d, 0x2a000030006300012000030000500002, 0x14000080003e0004a0004d0001f0005b],
    [0x40005300028000050003d000020005b, 0x1f0001d000620001d00028000050001f, 0x3500003000120001100000000030004d, 0x2e0002e000440001a0000a000120004a, 0x3000014000290002b00044000630003e, 0x38000640002f00027000470000300008, 0x5e0001e0000f00011000270002a00014],
    [0x430003d0001b, 0x570004d00024, 0x2a0004a00015],
    [0x1b0002400015, 0x3d0004d0004a, 0x43000570002a],
    [0x3f0006400001, 0x4e0004200057, 0x560004f00029],
    [0x10005700029, 0x64000420004f, 0x3f0004e00056],
    [0xf0001a000610004f000580001b00043, 0x50000240002d00027000640002800026, 0x1c0002b0005f000600003d0000f00003]⟩

private theorem tripleCert_14_ok : checkTripleCert tripleCert_14 = true := by decide

private def tripleCert_15 : PackedTripleCert where
  n0 := 1
  n1 := 4
  n2 := 5
  M_rows := [0x130005f0000a0002000006000510002f0000500059000200000400028000490001f00042000050001b000280002200005, 0x620000200006000080006200015000390002e000290002e0004e000490004e00002000510005d0001c0000d0004c00017, 0x1a00002000330002d000620004f0002d000260003200063000240004f00024000430001c0003d0000c000270000b00056, 0x630001800016000550000c000400003d000200002a0002400004000620006300044000010004000030000590001700045, 0x1100014000450000c00052000310000200009000630005c000070000b000050001200006000430005b000140001a00064, 0x4300061000610000200043000360003d0002b0000b000040004c000560003e0002b0004c0002200023000050002e0005a, 0x6000056000310004a0005b0004c00057000000002f00010000100003d0005000011000010006000064000000003e00019, 0xe0004400057000260002300001000220001f0000e000530003c0001b00029000450003d00038000620001a0004600033, 0x4d0002c0003c000050003d0002600038000190005300053000080002d0001300052000550003f00056000230001c0002d, 0x400002f0001b000110001600005000060001300023000160000a000600004d00062000520003e00001000560003f0003a, 0x1a000360004c0001100026000400001600015000230005a00044000180005a0004d00025000410005f00056000400000d, 0x70000300025000400005300063000170005600048000570004c000360000f000420004c0002b00017000400004b00032, 0x3e000200000e0002400005000500005f000320004f000010002f000250001600021000000002500038000080003600016, 0x3b000160003400000000640001200003000280001f0000c0002f0003f0003b0003f00012000510001d0001d0004c00035, 0x4e0005400012000230004000004000430000b00035000100005d0003e0004d0002400062000090004d0001a0003e00053, 0x3b000570002c00013000040004c0003f000140005800003000160000a000280005a0003d0002100043000640005d00023, 0x5a0000d000290004c0003f000280001f0001e00063000240000500057000240005600032000050001a000130005000043, 0x39000230003100036000610006200012000360003d0004a000460000900043000260001c000300003a0002a0003200013, 0x3d00023000410000f000630005a000010005400029000550004c00026000290004a00041000480000a0003a0004b0005b, 0x490005d0004f000110001b0001a00016000610001400013000320005b0001e0004e000040000b0004e000120002100047]
  M_cols := [0x5000170005600045000640005a00019000330002d0003a0000d000320001600035000530002300043000130005b00047, 0x220004c0000b000170001a0002e0003e000460001c0003f000400004b000360004c0003e0005d00050000320004b00021, 0x280000d00027000590001400005000000001a00023000560005600040000080001d0001a00064000130002a0003a00012, 0x1b0001c0000c000300005b00023000640006200056000010005f00017000380001d0004d000430001a0003a0000a0004e, 0x50005d0003d00040000430002200060000380003f0003e000410002b000250005100009000210000500030000480000b, 0x42000510001c00001000060004c000010003d0005500052000250004c0000000012000620003d000320001c0004100004, 0x1f000020004300044000120002b000110004500052000620004d00042000210003f000240005a00056000260004a0004e, 0x490004e0002400063000050003e0005000029000130004d0005a0000f000160003b0004d000280002400043000290001e, 0x28000490004f000620000b000560003d0001b0002d000600001800036000250003f0003e0000a0005700009000260005b, 0x40004e0002400004000070004c000100003c000080000a000440004c0002f0002f0005d0001600005000460004c00032, 0x200002e00063000240005c00004000100005300053000160005a00057000010000c0001000003000240004a0005500013, 0x5900029000320002a000630000b0002f0000e000530002300023000480004f0001f0003500058000630003d0002900014, 0x50002e0002600020000090002b000000001f0001900013000150005600032000280000b000140001e000360005400061, 0x2f000390002d0003d000020003d0005700022000380000600016000170005f00003000430003f0001f000120000100016, 0x51000150004f0004000031000360004c00001000260000500040000630005000012000040004c00028000620005a0001a, 0x600062000620000c00052000430005b000230003d000160002600053000050006400040000040003f00061000630001b, 0x20000080002d000550000c000020004a0002600005000110001100040000240000000023000130004c000360000f00011, 0xa000060003300016000450006100031000570003c0001b0004c000250000e00034000120002c0002900031000410004f, 0x5f000020000200018000140006100056000440002c0002f0003600003000200001600054000570000d00023000230005d, 0x13000620001a000630001100043000600000e0004d000400001a000070003e0003b0004e0003b0005a000390003d00049]
  Minv_rows := [0x1900059000620005d0002100042000140002d000050002f00003000490002e000220005c000220002c0001a0003b0005a, 0x3d000340002c00025000050002e000150003900041000210001200027000160002b00044000150002700047000540003c, 0x5f0000f000030001f000440005f00004000090005100057000020003b0001f000480003c000070002400031000120004e, 0x340002e00027000300002600027000140002b000060002700021000240002d000560001e000450003c000020001100017, 0x2d0002b00001000000004400016000260003100025000340001800025000370000d000100003b000520000a0003000038, 0x10000250001100051000410002600051000240003f0003f000350001a0001000042000210002a000030004c0000b00008, 0x3a0001800030000630004f00016000200002c000040003700013000340004800058000390006000064000380006000016, 0x5a000120000d00028000400000b00048000610004f00056000170003e0004a0002b0004d0001e000140000e0000a00055, 0x600003a0002a0002b00036000630004900001000560000d000150000a00041000540002f0003f0004c000540000300032, 0x480003d00010000280005200039000620000d00052000310003f0000100013000310000300027000360002f000560001b, 0x4b00048000290004f0000f0003f000400001c000640003c000350003f000640005f0005f0000000018000160003f0004c, 0x1a00006000120004b000560003d0003300059000260000400054000590003300021000030001900043000150002c0004e, 0x630001d000070001a0001c0004b000430005b000510000d00054000080003d0005f000240003900031000640005c00045, 0x3e000620005d0000a0003f00042000090004d000200003d000410001000022000060001000044000610002b0000f0000f, 0x3f0001f0005b000500003a0004c0002b0004500050000000002c0002c000610001100039000320005f000450005200054, 0x5d000550002d000590002c000260001c0002f0004e0001a000540001e0005a0003b0004f000010004b0000d0000f00059, 0x320006200015000580004c000370002f000620002e0002a00061000030005c0001100013000470001a0003b0003200018, 0x40000300053000140001f0003000028000570002a0003000016000320003a0003e0006400045000610004600016, 0x58000140005b000510001400007000310000a0001d000140005d000190001900007000600000b0000b000110000300060, 0x210003d0005d00011000020005e000050005f00041000520000e0004900038000590001900063000390000d0001400007]
  Minv_cols := [0x5a0003c0004e0001700038000080001600055000320001b0004c0004e000450000f000540005900018000160006000007, 0x3b000540001200011000300000b000600000a00003000560003f0002c0005c0000f000520000f00032000460000300014, 0x1a0004700031000020000a0004c000380000e000540002f0001600015000640002b000450000d0003b00061000110000d, 0x2c00027000240003c000520000300064000140004c00036000180004300031000610005f0004b0001a000450000b00039, 0x220001500007000450003b0002a000600001e0003f0002700000000190003900044000320000100047000640000b00063, 0x5c000440003c0001e0001000021000390004d0002f000030005f000030002400010000390004f000130003e0006000019, 0x220002b00048000560000d00042000580002b00054000310005f000210005f00006000110003b000110003a0000700059, 0x2e000160001f0002d0003700010000480004a000410001300064000330003d00022000610005a0005c000320001900038, 0x49000270003b00024000250001a000340003e0000a000010003f0005900008000100002c0001e00003000160001900049, 0x300012000020002100018000350001300017000150003f000350005400054000410002c0005400061000300005d0000e, 0x2f000210005700027000340003f00037000560000d000310003c000040000d0003d000000001a0002a0002a0001400052, 0x5000410005100006000250003f000040004f000560005200064000260005100020000500004e0002e000570001d00041, 0x2d00039000090002b00031000240002c00061000010000d0001c000590005b0004d000450002f00062000280000a0005f, 0x14000150000400014000260005100020000480004900062000400003300043000090002b0001c0002f000300003100005, 0x420002e0005f000270001600026000160000b00063000390003f0003d0004b000420004c00026000370001f000070005e, 0x2100005000440002600044000410004f0004000036000520000f000560001c0003f0003a0002c0004c000140001400002, 0x5d000250001f00030000000005100063000280002b000280004f0004b0001a0000a000500005900058000530005100011, 0x620002c00003000270000100011000300000d0002a000100002900012000070005d0005b0002d00015000030005b0005d, 0x59000340000f0002e0002b0002500018000120003a0003d00048000060001d000620001f000550006200004000140003d, 0x190003d0005f000340002d000100003a0005a00060000480004b0001a000630003e0003f0005d00032000000005800021]
  b0 := ⟨1,
    [0xf000490005b000480003b0001b00027, 0x6000054000040003a0000e0003600023, 0x2e000060004d00044000360003d00017, 0x370002e0005200014000110000900059, 0x1e00025000590004c0002d0002a00015, 0x3d00043000370005e0002d000380002f, 0x10000230000700044000270005400061],
    [0x27000230001700059000150002f00061, 0x1b000360003d000090002a0003800054, 0x3b0000e00036000110002d0002d00027, 0x480003a00044000140004c0005e00044, 0x5b000040004d00052000590003700007, 0x4900054000060002e000250004300023, 0xf000600002e000370001e0003d00010],
    [0x500002e00046000300002f0000900041, 0x22000470000c00046000190002c00049, 0x32000370003600026000470005300021, 0x31000110004100004000030005d00034, 0x210003a0001900046000050000c0005b, 0x1d0000000029000190002d0003300026, 0x8000200003400018000110001d00004],
    [0x410004900021000340005b0002600004, 0x90002c000530005d0000c000330001d, 0x2f000190004700003000050002d00011, 0x30000460002600004000460001900018, 0x460000c0003600041000190002900034, 0x2e0004700037000110003a0000000020, 0x50000220003200031000210001d00008],
    [0x150000900020, 0x570005c0005e, 0xf0002100029],
    [0x200005e00029, 0x90005c00021, 0x15000570000f],
    [0x190000500030, 0x610002e00048, 0x37000280004a],
    [0x30000480004a, 0x50002e00028, 0x190006100037],
    [0x270001a0005800036000420002c00035, 0x1c00052000460002d0002e0001500046, 0x4c0003b00035000240000c0003d0004b]⟩
  b1 := ⟨4,
    [0x5000260001d00050000550001900051, 0x16000240004000010000510005500031, 0x2500019000580003800024000540003b, 0xd0005d000310002d000230001c0000f, 0x420001d0000000021000570000300051, 0xb00040000630003b0005c0005e00049, 0x2f0002a00034000440005c0001d0003e],
    [0x51000310003b0000f00051000490003e, 0x1900055000540001c000030005e0001d, 0x55000510002400023000570005c0005c, 0x5000010000380002d000210003b00044, 0x1d000400005800031000000006300034, 0x2600024000190005d0001d000400002a, 0x500016000250000d000420000b0002f],
    [0x43000030001c000440001c0001800050, 0xe0002100032000560001b0005400050, 0x40003c0000600001000610000d00018, 0x550001300002000560001a000040005d, 0x540005f0004e000070003d0006200000, 0x3800059000490003a000060004f00036, 0x3b0003f000360001c0004e000140003a],
    [0x5000050000180005d00000000360003a, 0x18000540000d00004000620004f00014, 0x1c0001b000610001a0003d000060004e, 0x44000560000100056000070003a0001c, 0x1c0003200006000020004e0004900036, 0x3000210003c000130005f000590003f, 0x430000e000040005500054000380003b],
    [0x400000200055, 0x460004a0000c, 0x27000390004e],
    [0x550000c0004e, 0x20004a00039, 0x400004600027],
    [0x340006100050, 0x5d0005200049, 0x590001c0000d],
    [0x50000490000d, 0x61000520001c, 0x340005d00059],
    [0x560002d0003600062000480000500037, 0xc0004700047000260004f0004b00021, 0x2200007000590004700053000440004b]⟩
  b2 := ⟨5,
    [0x2b0003000019000490005f000020000e, 0x540005e0005b0002a00016000190005e, 0x3700016000300002f0002f0005e0005a, 0x250006000028000460003e0003900029, 0x45000200001100013000220002600006, 0x26000170003500016000240005700053, 0x2b0005a000480003f0000e0001700035],
    [0xe0005e0005a00029000060005300035, 0x2000190005e00039000260005700017, 0x5f000160002f0003e00022000240000e, 0x490002a0002f0004600013000160003f, 0x190005b0003000028000110003500048, 0x300005e000160006000020000170005a, 0x2b00054000370002500045000260002b],
    [0x610000f000190004f00057000350002e, 0x400031000230004100009000300005a, 0x4700060000100001c0000f000400001a, 0x30000160002300012000560004e00049, 0x26000350004500040000090001d00003, 0x15000470005c0004e0001f000460003f, 0x56000590003a0004a0000d0000b00044],
    [0x2e0005a0001a00049000030003f00044, 0x3500030000400004e0001d000460000b, 0x57000090000f00056000090001f0000d, 0x4f000410001c00012000400004e0004a, 0x19000230001000023000450005c0003a, 0xf000310006000016000350004700059, 0x61000040004700030000260001500056],
    [0xb0004e00064, 0x2f0000c00014, 0x1f0002000047],
    [0x640001400047, 0x4e0000c00020, 0xb0002f0001f],
    [0x350000e00002, 0x5a0000a00019, 0x5c0000d00019],
    [0x20001900019, 0xe0000a0000d, 0x350005a0005c],
    [0x4a000000000e000580005e0000800009, 0x38000100004300061000310001200059, 0x3300000000110002900041000420005e]⟩

private theorem tripleCert_15_ok : checkTripleCert tripleCert_15 = true := by decide

private def tripleCert_16 : PackedTripleCert where
  n0 := 2
  n1 := 3
  n2 := 4
  M_rows := [0x23000510004e0001a00015000520005e0000d0000900060000160005000020000570000d0001c0002e0005f000250005c, 0x520001a00058000030003d000310003e00061000510005d000560002f0000d00023000280004800048000400003500045, 0x70000d0005a0002000059000180003e00018000490005600007000230000e000110004c000070004c0004d0002b00005, 0x5c000610001700051000310001000061000320003a000590004d00062000400005300001000340004700063000230001f, 0x5700056000070003f00019000570003d00001000340006200025000250003a0002e0003200020000100004c000260004a, 0x560005b0000a00059000360006400036000170004200059000080005f0001c00033000150003b000210001d0004e00024, 0x200037000580000900053000000004c000580001400055000600000b000290000600026000190003200010000550002e, 0x3c0001f0001c0002100045000580000c000560005000010000460002f0004200064000380001800048000060002800056, 0x4f0005f0004b000420005a000560002f00043000240003f000620002f00043000300006000057000640002a0001500025, 0x56000610000800006000500002e0003300031000190000000007000540002300038000640005b000290005c0004900007, 0x3f000330000b000620003c0005300024000010003d000300001a0003700041000140001e00029000510001a0004000042, 0x4c0001f000400003e00003000490005a0005f000490004c000620000b000640000900022000600001d0005a0002f0004a, 0x2c00056000050001e0005c0002b0002d000210004100061000420001e000200006400024000310005400053000020002c, 0x4c0003d0001300015000280003600025000490004d00024000500003b000610005e0003c0004d0005c0000b0001b00044, 0x4c000120004c000630002c000170002700026000100003c00016000050001d000130003e0002e00058000470001e0002d, 0x25000500004f000510000e00028000500002500042000250002e0001c0005200034000590002f0002c000480004100057, 0x250002a00043000320001400046000640001600047000640004800022000300005d0001e0003e00043000170000100015, 0x640004e000340004b000040005400057000060001d0005d000010000b00020000540003c0004a0005f0003a0004e00050, 0x62000150003b00020000170002600019000380004200039000600001c00025000360001c000110001b0002d000540001d, 0x4c000590004c000190003f000050001400031000030004f0001a00037000160000c000000001b000500003b0001800009]
  M_cols := [0x5c00045000050001f0004a000240002e000560002500007000420004a0002c000440002d0005700015000500001d00009, 0x25000350002b00023000260004e00055000280001500049000400002f000020001b0001e00041000010004e0005400018, 0x5f000400004d000630004c0001d00010000060002a0005c0001a0005a000530000b0004700048000170003a0002d0003b, 0x2e000480004c00047000100002100032000480006400029000510001d000540005c000580002c000430005f0001b00050, 0x1c000480000700034000200003b0001900018000570005b0002900060000310004d0002e0002f0003e0004a000110001b, 0xd000280004c000010003200015000260003800060000640001e00022000240003c0003e000590001e0003c0001c00000, 0x570002300011000530002e00033000060006400030000380001400009000640005e00013000340005d00054000360000c, 0x200000d0000e000400003a0001c00029000420004300023000410006400020000610001d0005200030000200002500016, 0x500002f0002300062000250005f0000b0002f0002f00054000370000b0001e0003b000050001c000220000b0001c00037, 0x1600056000070004d0002500008000600004600062000070001a000620004200050000160002e0004800001000600001a, 0x600005d0005600059000620005900055000100003f00000000300004c00061000240003c00025000640005d000390004f, 0x900051000490003a0003400042000140005000024000190003d00049000410004d0001000042000470001d0004200003, 0xd000610001800032000010001700058000560004300031000010005f0002100049000260002500016000060003800031, 0x5e0003e0003e000610003d000360004c0000c0002f00033000240005a0002d00025000270005000064000570001900014, 0x5200031000180001000057000640000000058000560002e00053000490002b00036000170002800046000540002600005, 0x150003d0005900031000190003600053000450005a000500003c000030005c000280002c0000e0001400004000170003f, 0x1a0000300020000510003f0005900009000210004200006000620003e0001e000150006300051000320004b0002000019, 0x4e000580005a00017000070000a000580001c0004b000080000b0004000005000130004c0004f00043000340003b0004c, 0x510001a0000d00061000560005b000370001f0005f00061000330001f000560003d00012000500002a0004e0001500059, 0x2300052000070005c0005700056000020003c0004f000560003f0004c0002c0004c0004c000250002500064000620004c]
  Minv_rows := [0x5400056000250003e0001b00024000190002b00049000410004700029000380003c000290005d000080003f0000d0003c, 0x250000b0004e00045000070002d000220003b000580003d0001f0000d00026000510003c000230004f00045000490001a, 0xe0000a000610000000046000430005b000350004e0004c0001700046000470003d000520002a000430003f0004500028, 0x290000d0005d0000300030000630002400053000120000c0005c000610004a0002700006000050001f00037000510003f, 0x2f0004b0001f0004a000400001d000490005b0005b0000600036000400000e000210002e000490003d000400004a00028, 0x60000400000600056000040003e00050000020001700016000460000c0005d0001000022000430005500014000430005e, 0x180002c0002f0004c000410002c00049000440000900001000240005c000540004900008000390000a00016000600002a, 0x3b000510004b000100003a000360002e00027000550002c000550005100014000240003e0005100028000040003100061, 0x55000440001300041000430002e0000b0002c0002e0001a0003e0001f00005000270004f0005b0000a000450004c00017, 0x2f0000e000020000b00056000540001400015000190002f000340005d000350000300005000550001500026000220002d, 0x550000b0000f0006300031000410003f0002900037000100000300047000200000900032000510000e00015000000005f, 0x180004000006000450005f0000000005000040000a00025000130003f00029000290000d0001a00015000130001600018, 0x39000550001b0002e0001c000320001e0005a00028000100001f0004700014000530000b0002e0000e000230002300060, 0x50000390003900043000210001c000250005700001000230000a00040000440005a000240005f000090001f0001300034, 0x4b0006300062000270001b000330000900004000340002a0000f000220003200038000610003b0000d00063000160005f, 0x44000120005a00025000090000200015000330001500021000280004900032000300002c0005600008000630002b00006, 0x26000480005c0002a0005c0005c0004700059000260003e00011000000005900049000280001f0003900026000630005a, 0x14000440001b000220004f0001e0004000047000330001500001000370000c000430001e00017000580000f0004800035, 0x25000180002a0006400006000230000f000580001e000070000d00056000230000800052000030002b0005c00012, 0x3c0000b000640002c000330002000064000430004f0004e000310004f0000a0003c0003a0005b000040001f0005900049]
  Minv_cols := [0x3c0001a000280003f000280005e0002a00061000170002d0005f0001800060000340005f000060005a000350001200049, 0xd0004900045000510004a0004300060000310004c0002200000000160002300013000160002b00063000480005c00059, 0x3f000450003f000370004000014000160000400045000260001500013000230001f0006300063000260000f0002b0001f, 0x80004f000430001f0003d000550000a000280000a000150000e000150000e000090000d0000800039000580000300004, 0x5d000230002a00005000490004300039000510005b00055000510001a0002e0005f0003b000560001f00017000520005b, 0x290003c00052000060002e00022000080003e0004f00005000320000d0000b00024000610002c000280001e000080003a, 0x3c000510003d000270002100010000490002400027000030000900029000530005a00038000300004900043000230003c, 0x3800026000470004a0000e0005d00054000140000500035000200002900014000440003200032000590000c000560000a, 0x290000d0004600061000400000c0005c000510001f0005d000470003f0004700040000220004900000000370000d0004f, 0x470001f000170005c000360004600024000550003e0003400003000130001f0000a0000f0002800011000010000700031, 0x410003d0004c0000c0000600016000010002c0001a0002f000100002500010000230002a000210003e000150001e0004e, 0x49000580004e000120005b0001700009000550002e00019000370000a000280000100034000150002600033000580004f, 0x2b0003b00035000530005b0000200044000270002c0001500029000040005a00057000040003300059000470000f00043, 0x19000220005b000240004900050000490002e0000b000140003f000050001e00025000090001500047000400002300064, 0x240002d00043000630001d0003e0002c000360002e000540004100000000320001c00033000020005c0001e0000600020, 0x1b0000700046000300004000004000410003a0004300056000310005f0001c000210001b000090005c0004f0006400033, 0x3e0004500000000030004a000560004c00010000410000b00063000450002e0004300027000250002a000220002a0002c, 0x250004e000610005d0001f000060002f0004b00013000020000f000060001b00039000620005a0005c0001b0001800064, 0x560000b0000a0000d0004b000400002c00051000440000e0000b00040000550003900063000120004800044000250000b, 0x54000250000e000290002f00060000180003b000550002f000550001800039000500004b000440002600014000000003c]
  b0 := ⟨2,
    [0x29000610001000023000250000e00056, 0x32000580001b00036000090001d00039, 0x190001f00047000490003a0001500046, 0x4300047000530001200063000190005b, 0x610002b0004e0002a000630005700002, 0x3c00004000020003f000420000d0005c, 0x54000110003c00034000010002500057],
    [0x5600039000460005b000020005c00057, 0xe0001d0001500019000570000d00025, 0x25000090003a00063000630004200001, 0x230003600049000120002a0003f00034, 0x100001b00047000530004e000020003c, 0x61000580001f000470002b0000400011, 0x29000320001900043000610003c00054],
    [0x21000470000f0003c000160003d00015, 0x430002d000160002f000390000d00053, 0x2a000240004900015000060000900033, 0x2800052000490004e0004a000520004d, 0x610005d0004000025000060001800033, 0x100000f0000f00026000420005300018, 0x490005f0006400057000630000500059],
    [0x1500053000330004d000330001800059, 0x3d0000d0000900052000180005300005, 0x1600039000060004a000060004200063, 0x3c0002f000150004e000250002600057, 0xf000160004900049000400000f00064, 0x470002d00024000520005d0000f0005f, 0x21000430002a00028000610001000049],
    [0x580004100054, 0x200001d0000f, 0x320001400002],
    [0x540000f00002, 0x410001d00014, 0x580002000032],
    [0xb0002a00044, 0x310003e00007, 0x53000160002f],
    [0x44000070002f, 0x2a0003e00016, 0xb0003100053],
    [0x450003800026000270000d000050004b, 0x200005e0005c000240002c0003200052, 0x360005c000140005b000300003000027]⟩
  b1 := ⟨3,
    [0x70000400059000080001c0003100033, 0x31000610002e00009000260002300042, 0x5f00012000520003c000230004200014, 0x64000250002b0001a00041000350000f, 0xc0004f0004e0003e0002c000630005d, 0x3900047000060005a0001e0003600011, 0x5500058000410006100037000560002e],
    [0x3300042000140000f0005d000110002e, 0x31000230004200035000630003600056, 0x1c0002600023000410002c0001e00037, 0x8000090003c0001a0003e0005a00061, 0x590002e000520002b0004e0000600041, 0x40006100012000250004f0004700058, 0x7000310005f000640000c0003900055],
    [0x480002600014000140003b0001a00035, 0x1000380001c0003400030000150004e, 0x4700035000200000d0004b0003900032, 0x5c000100002d00060000310004d00027, 0x180002e0005c00044000170003400061, 0x5a000410002400001000360001600029, 0x4f000420001400041000290003b00022],
    [0x350004e0003200027000610002900022, 0x1a00015000390004d00034000160003b, 0x3b000300004b00031000170003600029, 0x14000340000d00060000440000100041, 0x140001c000200002d0005c0002400014, 0x260003800035000100002e0004100042, 0x4800001000470005c000180005a0004f],
    [0x570000600011, 0x510005d0004d, 0x480005b0003c],
    [0x110004d0003c, 0x60005d0005b, 0x570005100048],
    [0x60001200022, 0x570004800038, 0x3b000600003a],
    [0x22000380003a, 0x120004800060, 0x6000570003b],
    [0x480002f000540002d000170005d00049, 0x2e000080002400048000550003f00045, 0x60002f0000000055000570000c00008]⟩
  b2 := ⟨4,
    [0x4a0005e0005d0005c0004b000200003f, 0xd00045000100003b000440001a00048, 0x4800058000180002e000000004b0000a, 0x380004b000370000b00006000500003d, 0xc0005b00014000600001c0003f00053, 0x600002600020000100005e0002500025, 0x4700054000150005c000400004d0002b],
    [0x3f000480000a0003d00053000250002b, 0x200001a0004b000500003f000250004d, 0x4b0004400000000060001c0005e00040, 0x5c0003b0002e0000b00060000100005c, 0x5d000100001800037000140002000015, 0x5e00045000580004b0005b0002600054, 0x4a0000d00048000380000c0006000047],
    [0x5e0003200025000520003d0003e00061, 0x5e000410003800054000140006200029, 0x110004c0005f00023000200002d0001c, 0x270003a0000100055000250006000058, 0x61000230005400015000540001500060, 0x1400053000220005900049000610005d, 0x2b000580000100014000080006200050],
    [0x61000290001c00058000600005d00050, 0x3e000620002d00060000150006100062, 0x3d000140002000025000540004900008, 0x52000540002300055000150005900014, 0x25000380005f00001000540002200001, 0x32000410004c0003a000230005300058, 0x5e0005e000110002700061000140002b],
    [0xf0004700044, 0x1f0001300003, 0x290002b00025],
    [0x440000300025, 0x47000130002b, 0xf0001f00029],
    [0x2b0005c0001d, 0x2c0004e00023, 0x150000f00050],
    [0x1d0002300050, 0x5c0004e0000f, 0x2b0002c00015],
    [0x5000200002200006000300005a00010, 0x3900018000110003f000480000000047, 0xc0000d00059000060001b0003000010]⟩

private theorem tripleCert_16_ok : checkTripleCert tripleCert_16 = true := by decide

private def tripleCert_17 : PackedTripleCert where
  n0 := 2
  n1 := 3
  n2 := 5
  M_rows := [0x5b000140001b0002a0002400015000310003a0004b0000000034000640004100052000560002c000170003d0002b0003c, 0x3a0002000022000340004a000330001100021000240004f000210005e000170003000001000230004a0005d0005b0000d, 0x100011000360000300030000120004b00048000610003900019000190000000046000330003000050000140005100030, 0x1f0005b0003e0005b0003c0002e000020000d00028000240000f0005b0001700059000560002300029000270000f0002b, 0x60005b000620002c0003d000060004c0000b00044000340005100035000020003e0002f0000e0000f000120000e00046, 0x2c000370005c000350004c0005f0000a0005100010000180003e00018000460004c0003b0002a0002900029000380002a, 0x20002d00015000510004d000400003e0002d0001c0001100057000340002600019000480004a000390000a0004500015, 0x80001e0001b000310004b000510003c0000b00060000620001c0002b0005c000060003a000160003300025000010003e, 0x70003500064000170000100021000640001b0002f0001c000080001a00043000420000e0005f000480003c0006000011, 0xf00058000140000d000010004a00052000210001700030000400001200048000510001800013000340001e0001b00048, 0x20001600061000310000100009000470005e00014000380005a000450005a0001b000550000d00051000090000900054, 0x3a0004e0001a000190004c000280005c00054000180002a00053000470000c000220002000034000160005a000170005d, 0x2a000600003000024000200001000019000130004d0003a0003500052000470004e00014000520002f0003b0004d00038, 0x580005900001000500000c0000f0000d000620005b000020004e0005d0000e000230000a0001a0004300014000340003b, 0x50005c000430004d000480005400045000360002d0003a0002b00017000230001b000580005f000440000b0000f00056, 0xe00032000040003400005000280003a0002a000430000d0002800000000390002c0003a0006100015000010001e0004b, 0x4b000430005e00045000480001a0005f0005400035000560003a000440000a000480000f0005a0005f00029000300000d, 0x380001d000620004b0003f00039000580005d0001100018000050004200005000320000a000100005e000500004700026, 0x31000040006000025000390002b00034000110003a000360004f000340000f00060000640001200018000090001f00026, 0x400038000230003b0001800063000390004600016000180004500034000190003400034000530003900036000310005c]
  M_cols := [0x3c0000d000300002b000460002a000150003e0001100048000540005d000380003b000560004b0000d00026000260005c, 0x2b0005b000510000f0000e000380004500001000600001b00009000170004d000340000f0001e00030000470001f00031, 0x3d0005d000140002700012000290000a000250003c0001e000090005a0003b000140000b0000100029000500000900036, 0x170004a00050000290000f000290003900033000480003400051000160002f0004300044000150005f0005e0001800039, 0x2c0002300030000230000e0002a0004a000160005f000130000d00034000520001a0005f000610005a000100001200053, 0x560000100033000560002f0003b000480003a0000e000180005500020000140000a000580003a0000f0000a0006400034, 0x520003000046000590003e0004c000190000600042000510001b000220004e000230001b0002c00048000320006000034, 0x410001700000000170000200046000260005c00043000480005a0000c000470000e00023000390000a000050000f00019, 0x640005e000190005b0003500018000340002b0001a000120004500047000520005d000170000000044000420003400034, 0x3400021000190000f000510003e000570001c00008000400005a00053000350004e0002b000280003a000050004f00045, 0x4f0003900024000340001800011000620001c00030000380002a0003a000020003a0000d00056000180003600018, 0x4b00024000610002800044000100001c000600002f0001700014000180004d0005b0002d0004300035000110003a00016, 0x3a00021000480000d0000b000510002d0000b0001b000210005e000540001300062000360002a000540005d0001100046, 0x31000110004b000020004c0000a0003e0003c0006400052000470005c000190000d000450003a0005f000580003400039, 0x1500033000120002e000060005f0004000051000210004a0000900028000100000f00054000280001a000390002b00063, 0x240004a000300003c0003d0004c0004d0004b0000100001000010004c000200000c0004800005000480003f0003900018, 0x2a00034000030005b0002c000350005100031000170000d000310001900024000500004d00034000450004b000250003b, 0x1b00022000360003e000620005c000150001b0006400014000610001a000300000100043000040005e000620006000023, 0x1400020000110005b0005b000370002d0001e0003500058000160004e00060000590005c00032000430001d0000400038, 0x5b0003a000010001f000060002c0000200008000070000f000020003a0002a00058000050000e0004b000380003100004]
  Minv_rows := [0x35000410001900021000310000b00032000630001b0004800033000240003d000160001800036000390000e0000d00001, 0xc00046000190001e0001e00064000100002f0003800022000560002f0002100007000250005d0003700035000640002b, 0x120006400058000630003b000450004b0004b000570001300007000200004b00006000410000e00020000300006300057, 0x5300013000590004b000180004500044000000005b0003d000040005a0001d000440003200025000040001e0004b00033, 0x59000070003f0000600049000010004d0003e000270000d000610001a0000f000150003d0001600036000560002700056, 0x1600024000530003b000430004f000200000e000150002c0003f0004b0003d0005d000100004e000040002f0002800005, 0x280005d0000e000080005f0004d000080001b000030002300000000640003500009000460002f00011000510000b00046, 0x180003a000550000800051000150000d00015000210004f00058000610003c0001b000060003500008000030006400030, 0x700062000300001d0004d0002c0001400048000340003000036000240001a00013000130004000037000210005300064, 0x5000460003b0005400014000640001600051000300001f0001700058000420003d000420005500000000390003e00050, 0x550000b000270004f0002700008000220002700037000310003d00028000550000c00001000040001b0000e0003f00021, 0x6100013000170003100018000330001e00048000640005e0003a000240004200040000320000300001000330004b00027, 0x2a00043000090001b0005900053000100005300028000560002c00055000110003a0004a0004d00047000310000f0005f, 0x1d0006000016000540004d0002d000240000b000550001700028000130000c0000900028000590006000005000030003a, 0x60000540005f00046000610004a0005d00033000500002700055000190004a000170005c0003800054000640002000005, 0x270002d0006000000000390004e00007000080005600063000060005c0002c000440002a000210000d0005b000330001b, 0x5e0005f000590000400032000200005c000180002900042000370002300004000550005e0000a000230003e0003f0005e, 0x1f0002400038000380002c0003a0000c00064000570003400050000250002a00054000360004a00062000070001800057, 0x9000550001f0000e00020000200000a000640003a0001a00009000560000b000050003e000050001d000030002700053, 0x42000220005b0005e0000d000140000d0005a000410004e0000f00002000260005f000210005a00042000590004200008]
  Minv_cols := [0x10002b000570003300056000050004600030000640005000021000270005f0003a000050001b0005e000570005300008, 0xd00064000630004b00027000280000b00064000530003e0003f0004b0000f0000300020000330003f000180002700042, 0xe00035000300001e000560002f000510000300021000390000e000330003100005000640005b0003e000070000300059, 0x390003700020000040003600004000110000800037000000001b000010004700060000540000d00023000620001d00042, 0x360005d0000e00025000160004e0002f00035000400005500004000030004d0005900038000210000a0004a000050005a, 0x180002500041000320003d000100004600006000130004200001000320004a000280005c0002a0005e000360003e00021, 0x16000070000600044000150005d000090001b000130003d0000c000400003a0000900017000440005500054000050005f, 0x3d000210004b0001d0000f0003d000350003c0001a000420005500042000110000c0004a0002c000040002a0000b00026, 0x240002f000200005a0001a0004b0006400061000240005800028000240005500013000190005c00023000250005600002, 0x33000560000700004000610003f000000005800036000170003d0003a0002c0002800055000060003700050000090000f, 0x4800022000130003d0000d0002c000230004f000300001f000310005e0005600017000270006300042000340001a0004e, 0x1b00038000570005b00027000150000300021000340003000037000640002800055000500005600029000570003a00041, 0x630002f0004b000000003e0000e0001b0001500048000510002700048000530000b00033000080001800064000640005a, 0x32000100004b000440004d00020000080000d0001400016000220001e00010000240005d000070005c0000c0000a0000d, 0xb000640004500045000010004f0004d000150002c000640000800033000530002d0004a0004e000200003a0002000014, 0x310001e0003b0001800049000430005f000510004d000140002700018000590004d0006100039000320002c000200000d, 0x210001e000630004b000060003b00008000080001d000540004f000310001b00054000460000000004000380000e0005e, 0x190001900058000590003f000530000e00055000300003b000270001700009000160005f0006000059000380001f0005b, 0x4100046000640001300007000240005d0003a00062000460000b000130004300060000540002d0005f000240005500022, 0x350000c000120005300059000160002800018000070000500055000610002a0001d00060000270005e0001f0000900042]
  b0 := ⟨2,
    [0x310005f0001f0002300035000150001f, 0x190003f0004e000140005e0004400032, 0x130000100053000290001e000630002b, 0x1f0005e0005e000480003f0005d00062, 0x560003100039000610002d000020005d, 0x5f00014000560002500013000090005b, 0x54000370003d000420003c0005e00061],
    [0x1f000320002b000620005d0005b00061, 0x1500044000630005d00002000090005e, 0x350005e0001e0003f0002d000130003c, 0x23000140002900048000610002500042, 0x1f0004e000530005e00039000560003d, 0x5f0003f000010005e000310001400037, 0x3100019000130001f000560005f00054],
    [0x50004800040000020002a00060, 0x290001a00026000590000a000530002c, 0x5e0000b0004400004000280000d0005e, 0x64000100003800055000250000400061, 0x7000350002d0003f000360000100053, 0x240000c0005200055000640003400059, 0x10001500002000210002b0000500053],
    [0x600002c0005e00061000530005900053, 0x2a000530000d00004000010003400005, 0x20000a000280002500036000640002b, 0x400005900004000550003f0005500021, 0x480002600044000380002d0005200002, 0x50001a0000b00010000350000c00015, 0x290005e00064000070002400001],
    [0x2000390000f, 0x44000320004a, 0x450002400016],
    [0xf0004a00016, 0x390003200024, 0x20004400045],
    [0x19000320000d, 0x30005e00054, 0x1e0004d00022],
    [0xd0005400022, 0x320005e0004d, 0x19000030001e],
    [0x2b000630001b0001c0002c0001800047, 0x360005f000470000b0002f0000d00042, 0x2b000530000900006000510006200024]⟩
  b1 := ⟨3,
    [0x1000140004f00050000140003400055, 0x17000490005900016000060002b00047, 0x4e000610004500053000440005100027, 0x380002200051000260000c0002d00036, 0x2b00024000150001b0005a0004000024, 0x34000450006300008000520004000058, 0x51000180005f0004f0001f0000c0000f],
    [0x5500047000270003600024000580000f, 0x340002b000510002d00040000400000c, 0x1400006000440000c0005a000520001f, 0x500001600053000260001b000080004f, 0x4f00059000450005100015000630005f, 0x14000490006100022000240004500018, 0x1000170004e000380002b0003400051],
    [0x3a0000e0001600042000250001900005, 0x39000600003d000580000c0000800001, 0x8000610005f0003c000100003500033, 0x620003f0000e00044000580000800035, 0x5b00044000050003f000090004900026, 0x56000620005b000490002a0001100005, 0x2b0000900019000440002e0003700032],
    [0x5000010003300035000260000500032, 0x19000080003500008000490001100037, 0x250000c0001000058000090002a0002e, 0x42000580003c000440003f0004900044, 0x160003d0005f0000e000050005b00019, 0xe00060000610003f000440006200009, 0x3a0003900008000620005b000560002b],
    [0xa0002f00011, 0x70004200057, 0x4a000600003b],
    [0x11000570003b, 0x2f0004200060, 0xa000070004a],
    [0x160002d00026, 0x340000900017, 0x10003f0005a],
    [0x26000170005a, 0x2d000090003f, 0x160003400001],
    [0x4d00028000120000b0002f000060001a, 0x300001f00047000140005d0001800050, 0x3a000580005f0003b00047000120003b]⟩
  b2 := ⟨5,
    [0x5d00017000490001b000420005900021, 0x4b000440004000018000260000900052, 0x2d000100001d00007000260004d00014, 0x190004c000360000e000110005000037, 0x4f000120006100042000450002400032, 0xe0002a0004200039000590004f00049, 0x500026000000006100039000420003c],
    [0x2100052000140003700032000490003c, 0x59000090004d00050000240004f00042, 0x42000260002600011000450005900039, 0x1b00018000070000e000420003900061, 0x49000400001d00036000610004200000, 0x1700044000100004c000120002a00026, 0x5d0004b0002d000190004f0000e00005],
    [0x4900012000350002b0002b0002b, 0x11000040000e00025000300004800037, 0x5b0002c0001d00046000230003e00029, 0x4800038000150002a000570002b00063, 0x2a0003e0000600043000180005000059, 0x5700048000460001000001000380000d, 0x4a000430001a00032000590000100059],
    [0x2b000370002900063000590000d00059, 0x2b000480003e0002b000500003800001, 0x2b000300002300057000180000100059, 0x3500025000460002a000430001000032, 0x120000e0001d0001500006000460001a, 0x49000040002c000380003e0004800043, 0x110005b000480002a000570004a],
    [0x1f000600003c, 0x540004400019, 0x380002f00036],
    [0x3c0001900036, 0x60000440002f, 0x1f0005400038],
    [0x540002e00052, 0x260003c0003e, 0x1a0004000018],
    [0x520003e00018, 0x2e0003c00040, 0x54000260001a],
    [0x31000110003d00061000250002400050, 0x5800058000240004500034000600002b, 0x2e000510003c0001f000160000e0003f]⟩

private theorem tripleCert_17_ok : checkTripleCert tripleCert_17 = true := by decide

private def tripleCert_18 : PackedTripleCert where
  n0 := 2
  n1 := 4
  n2 := 5
  M_rows := [0x2000050000220001c000440003e0004a00005000560005f0003300053000640003f0000700032000540004e0002200022, 0x120002a0005b000000005b000020005e000560004d0002f0001f00014000030000c00054000610005a0002f0002f00039, 0x6100010000250003f000350004f000340001f0002400034000400000b000010005700023000490001a0001d0000600013, 0x3a00049000560001b0004a000480002b00020000290006300051000190005b0001b000310000b0001c000530003400003, 0x34000600002f0004e00053000420005e00050000110003c00011000530002c0005d000130003a00053000510000600046, 0x42000180004400047000310001e000220000e000190003b0000e0003b0004f0004a0005c0004000022000430004700013, 0x140005a0002d0005e000440001000036000630001e0000c000020005a0004d0002600050000580003a000390000200041, 0x1f000610003f0004e0003d0005700025000630005a000280006400049000070002a0001c000580002900042000530002f, 0x12000110004e000100002d0004300055000630004d00023000020006200000000300003b0002d0004f00008000110000a, 0x2a00009000330003b0004f000030004b0001d0004f000380002a0003200054000330001f00057000220003d0002e00009, 0x27000080000b0002e0003e0003e000620005700029000170004a0005200050000530003400007000410000f000270005f, 0x180006000035000410002f00060000080003d000350005c000200005f0000d00035000500005c0002a000240003e00050, 0x45000420002b000610005d00041000070003b000180001900000000560004a000030002a0004c00028000040001900017, 0x1f000280005e0000b0000d0001e0000900056000100001a0002c0004b000250004400038000080000d000130002c00060, 0x600019000170005e00031000450001d000150004d0000b0006000005000140002400058000570000d000040003200050, 0xb00049000000002400044000240003a000510005f0005b000050005900041000330004c0005900027000540004100063, 0x1c00057000050004b000020001f000220002200026000340003400064000610002700007000100004300062000460000d, 0xc00025000150004700016000610002200052000620001100009000030003d00022000390005b00028000150003f0002b, 0x1400017000020002000001000580006100031000360004b000100003f000060002300027000570000c000470006200052, 0xd000580005c000520006400001000290004c00041000560004e00003000190000f00014000530002500057000150000a]
  M_cols := [0x220003900013000030004600013000410002f0000a000090005f00050000170006000050000630000d0002b000520000a, 0x220002f000060003400006000470000200053000110002e000270003e000190002c0003200041000460003f0006200015, 0x4e0002f0001d0005300051000430003900042000080003d0000f000240000400013000040005400062000150004700057, 0x540005a0001a0001c00053000220003a000290004f00022000410002a000280000d0000d0002700043000280000c00025, 0x3200061000490000b0003a0004000058000580002d00057000070005c0004c000080005700059000100005b0005700053, 0x7000540002300031000130005c000500001c0003b0001f00034000500002a00038000580004c00007000390002700014, 0x3f0000c000570001b0005d0004a000260002a00030000330005300035000030004400024000330002700022000230000f, 0x6400003000010005b0002c0004f0004d000070000000054000500000d0004a000250001400041000610003d0000600019, 0x53000140000b00019000530003b0005a000490006200032000520005f000560004b000050005900064000030003f00003, 0x330001f0004000051000110000e0000200064000020002a0004a00020000000002c00060000050003400009000100004e, 0x5f0002f00034000630003c0003b0000c000280002300038000170005c000190001a0000b0005b00034000110004b00056, 0x560004d000240002900011000190001e0005a0004d0004f000290003500018000100004d0005f00026000620003600041, 0x5000560001f00020000500000e0006300063000630001d000570003d0003b0005600015000510002200052000310004c, 0x4a0005e000340002b0005e000220003600025000550004b000620000800007000090001d0003a00022000220006100029, 0x3e000020004f00048000420001e000100005700043000030003e00060000410001e00045000240001f000610005800001, 0x440005b000350004a0005300031000440003d0002d0004f0003e0002f0005d0000d000310004400002000160000100064, 0x1c000000003f0001b0004e000470005e0004e000100003b0002e00041000610000b0005e000240004b000470002000052, 0x220005b00025000560002f000440002d0003f0004e000330000b000350002b0005e00017000000000500015000020005c, 0x500002a000100004900060000180005a00061000110000900008000600004200028000190004900057000250001700058, 0x2000012000610003a0003400042000140001f000120002a0002700018000450001f000060000b0001c0000c000140000d]
  Minv_rows := [0x62000080000d00025000210003f000240004c000080000f000330001700062000190001f0003d0000a000270002400011, 0x47000080002d000260001c0002c000350004c0002a000110005e000050003d000060005f000600003f000570000e0003a, 0x62000220004c0003a000160006100052000330002700015000610003e00033000530003f0001b0001f0003d0001a0000e, 0x4100064000550004800020000640001d000020004b0001b00055000600005200048000470001c0001e0004800041, 0x3e000120002000059000090003200028000460005b0003200004000140002c0002d000320000b0000a00031000500003f, 0x18000290004a0005b000450004c000570005500051000140002f000060000a00034000420000b0002f0005c0005500061, 0x1e0004b00005000100001b0004d0000a0001b0006400035000120004e000350002200062000380000f000120000000032, 0x4000003000180004800018000430003f000620000b0000a0002b0004600000000090003e000510001600013000250000a, 0x38000360002f0001a0002b000310005c00053000050001e000420001f000430002d0005e0003f00012000430001500004, 0x3d00034000630001000016000530005a0002400031000350001100053000190001d000140005800030000340003900064, 0x110002e0000800040000210005400008000250004400052000610001e0000800032000530002b00033000460005e0001d, 0x20001f0001b0002a000330005b0005e00054000500000d0002a0000c0004b000530001d000190004d0000c0002700003, 0x39000000000f0005c0005d0003d0004d000480004700036000240001a00045000210001e0002000018000530000a00024, 0x2c0005e000520000b000240000500039000150005c0003c0001f000080003b0004e0005800026000400004b0003b00018, 0x39000440002100028000240001f0004d000080003300024000140006100040000470005e000370000500023000210002f, 0x210001b0004a0002b0000500048000480005a0005b000480001400004000470001c00027000360005b000510004a00016, 0x180000c00001000630002b000040001600009000540003f000460003f0004a0004e000240004d0004f000500001800025, 0x5700061000480000300061000100004a000580004d0004a000340004f000120005b0005700063000580005d0003f00032, 0x58000070003f000620002d0000300046000380003600005000040002d0002e0005800016000320001c000340004400057, 0x5700046000010004f00046000140004e00004000620003a0003e00048000060004b0000b0005c0000a000250002f00056]
  Minv_cols := [0x110003a0000e000410003f00061000320000a00004000640001d0000300024000180002f0001600025000320005700056, 0x240000e0001a000480005000055000000002500015000390005e000270000a0003b000210004a000180003f000440002f, 0x27000570003d0001e000310005c00012000130004300034000460000c000530004b0002300051000500005d0003400025, 0xa0003f0001f0001c0000a0002f0000f000160001200030000330004d0001800040000050005b0004f000580001c0000a, 0x3d000600001b000470000b0000b00038000510003f000580002b00019000200002600037000360004d00063000320005c, 0x1f0005f0003f000480003200042000620003e0005e00014000530001d0001e000580005e000270002400057000160000b, 0x190000600053000520002d0003400022000090002d0001d0003200053000210004e000470001c0004e0005b000580004b, 0x620003d00033000600002c0000a00035000000004300019000080004b000450003b00040000470004a000120002e00006, 0x17000050003e0005500014000060004e000460001f000530001e0000c0001a0000800061000040003f0004f0002d00048, 0x330005e000610001b000040002f000120002b0004200011000610002a000240001f00014000140004600034000040003e, 0xf00011000150004b0003200014000350000a0001e00035000520000d000360003c00024000480003f0004a000050003a, 0x80002a00027000020005b00051000640000b00005000310004400050000470005c000330005b000540004d0003600062, 0x4c0004c000330001d00046000550001b00062000530002400025000540004800015000080005a00009000580003800004, 0x2400035000520006400028000570000a0003f0005c0005a000080005e0004d000390004d00048000160004a000460004e, 0x3f0002c0006100020000320004c0004d000430003100053000540005b0003d000050001f0004800004000100000300014, 0x210001c000160004800009000450001b000180002b0001600021000330005d0002400024000050002b000610002d00046, 0x25000260003a00055000590005b00010000480001a00010000400002a0005c0000b000280002b0006300003000620004f, 0xd0002d0004c00064000200004a00005000180002f00063000080001b0000f00052000210004a00001000480003f00001, 0x800008000220004100012000290004b0000300036000340002e0001f000000005e000440001b0000c000610000700046, 0x620004700062000000003e000180001e00040000380003d0001100002000390002c000390002100018000570005800057]
  b0 := ⟨2,
    [0x600039000440005f000080005f00060, 0x110005f0003e0003f000050005600010, 0x2800025000330000b000420004c00033, 0x610005b000030003700018000230000e, 0x33000480004e00012000270001700045, 0x5700036000530004600057000460003b, 0x23000380001000056000230003e00022],
    [0x6000010000330000e000450003b00022, 0x5f000560004c0002300017000460003e, 0x8000050004200018000270005700023, 0x5f0003f0000b00037000120004600056, 0x440003e00033000030004e0005300010, 0x390005f000250005b000480003600038, 0x6000110002800061000330005700023],
    [0x410000d00009000280000c000240003b, 0x4c00045000210005c0002c0002900063, 0x51000530000e00036000150000c00057, 0x3b00005000540001e000180003f00031, 0x250001f0004e0004e000140000b0005b, 0x570001e00063000640000a0000500003, 0x510001c0002000000000410001e00052],
    [0x3b0006300057000310005b0000300052, 0x24000290000c0003f0000b000050001e, 0xc0002c0001500018000140000a00041, 0x280005c000360001e0004e0006400000, 0x9000210000e000540004e0006300020, 0xd0004500053000050001f0001e0001c, 0x410004c000510003b000250005700051],
    [0x1c0001400007, 0x33000540003c, 0x440002c0004a],
    [0x70003c0004a, 0x14000540002c, 0x1c0003300044],
    [0x620001100010, 0x4c000330003a, 0xf0006400034],
    [0x100003a00034, 0x110003300064, 0x620004c0000f],
    [0x4c0002e0001a0005000016000410000a, 0x620000b00037000150002d0003500050, 0x31000260003b00033000420001e0004c]⟩
  b1 := ⟨4,
    [0x230005400040000420002d0000500047, 0x250001b0005e00003000490004000002, 0x48000360004800039000510000e0005e, 0x540004c000480000900055000000000f, 0x340000d0005e0003c000430003600062, 0x5f000040001c000130001b0004600054, 0x2c00036000310001c0002a0002c00004],
    [0x47000020005e0000f000620005400004, 0x5000400000e0000000036000460002c, 0x2d000490005100055000430001b0002a, 0x420000300039000090003c000130001c, 0x400005e00048000480005e0001c00031, 0x540001b000360004c0000d0000400036, 0x23000250004800054000340005f0002c],
    [0x150003f000540001f0003f0003c00033, 0x70005a0003b00040000430004d00050, 0x28000180000e000110005f0001e0002e, 0xf00048000290005a0000b0005500056, 0x40004b0000800040000070000c00031, 0x51000250002f00060000560004200004, 0x350004300059000460005f0004700023],
    [0x33000500002e00056000310000400023, 0x3c0004d0001e000550000c0004200047, 0x3f000430005f0000b00007000560005f, 0x1f00040000110005a000400006000046, 0x540003b0000e00029000080002f00059, 0x3f0005a00018000480004b0002500043, 0x1500007000280000f000040005100035],
    [0x2e0002d, 0x560001800019, 0x420001a00062],
    [0x2d0001900062, 0x2e000180001a, 0x5600042],
    [0x2d0006100003, 0x2e0003d00029, 0x58000250000a],
    [0x3000290000a, 0x610003d00025, 0x2d0002e00058],
    [0x2e0004b0005500019000240005800050, 0xf00026000200005b00026000390002f, 0x240005a000350003e000640003c00054]⟩
  b2 := ⟨5,
    [0x60000630005c0002500042000310003d, 0xb000480002d00039000170006100015, 0x500001100049000290004d0005100000, 0x50000310005a0001d0004c0000700046, 0x3c0004100026000610000d0002000057, 0xc000000004f0003f000080002000023, 0x400004000610004b000270002d00018],
    [0x3d000150000000046000570002300018, 0x3100061000510000700020000200002d, 0x42000170004d0004c0000d0000800027, 0x2500039000290001d000610003f0004b, 0x5c0002d000490005a000260004f00061, 0x63000480001100031000410000000004, 0x600000b00050000500003c0000c00004],
    [0x480005a000050004d0005c0000f00051, 0x5c000050003e00046000490003600041, 0x5a000170004c0003a000390004e00029, 0x5c000410004700038000120004a00041, 0x5b0000e0000a0000c000210001600005, 0x3c000580005d00020000450004f00022, 0x1b00021000150002c000470004d00027],
    [0x51000410002900041000050002200027, 0xf000360004e0004a000160004f0004d, 0x5c000490003900012000210004500047, 0x4d000460003a000380000c000200002c, 0x50003e0004c000470000a0005d00015, 0x5a0000500017000410000e0005800021, 0x480005c0005a0005c0005b0003c0001b],
    [0x90001b00007, 0x540002500054, 0x62000290001a],
    [0x7000540001a, 0x1b0002500029, 0x90005400062],
    [0x550003700014, 0x220003500059, 0x5a0005a0002b],
    [0x14000590002b, 0x37000350005a, 0x55000220005a],
    [0x1c0002a0003900051000590001c00051, 0x2a0000f0005c00006000080002f00057, 0x61000180005300045000280001c0003a]⟩

private theorem tripleCert_18_ok : checkTripleCert tripleCert_18 = true := by decide

private def tripleCert_19 : PackedTripleCert where
  n0 := 3
  n1 := 4
  n2 := 5
  M_rows := [0x160000c00038000340001b00064000540003b000090004100032000000003f0000b0002b0000d0002c0000b0002600018, 0xa000390000f000300000200040000320000400016000180003c0001a0004400057000320002e0000000029000330001d, 0x1c000500003c0004300004000220003700005000550005d0002a0002b0001000016000510005200012000420001f00014, 0x34000420005e0004b0004c000480001b00007000330001b0002b0003a00048000330004c0003b0004f00019000640005b, 0x320002b00062000240003c00024000580000a0003c0005f0004f000130005e000140004500014000020003c0002e00018, 0x1900055000500003700011000360004600059000290003d00053000380004f0005e00014000190001c0001f0005200042, 0x2a000560001c0005a000570000d0001d000330000f0003b000080000e0004f0004a00027000340004e000150004f00012, 0xc000150003300000000140002700011000350003f0001b000490003b00026000640002c00001000110004e0006100029, 0x390003a00039000520005f0003d0002c0002d00039000520002e0003300025000190001d0003e0005a000570003900041, 0x4d00052000630003d0003a0001b0002a000480006000059000620005b00008000080004b0005c000560000b0001800023, 0x3e000260005f0000600015000370002f0003b00002000340000400034000310003f0000d0005600007000290000e00064, 0x280001500002000610003d000600005f0002e000270000f00049000590003600007000420005300019000080004300033, 0x80005b0001700021000190001200041000480003b0003f0002e000400005e0001300039000000003a0005e0003800000, 0x4d00052000260000a0002000027000420005600037000290002c0004c00011000220003d000460001d000130000100010, 0x4000200003a0001b0001c00042000540000200032000010005c0002900033000240006100044000440003a0004700001, 0x2300030000470001600059000050001a000300005f00032000360005400010000490001700029000150005b000130000a, 0x3000013000630001d00027000270001400030000610002400036000010005500049000200004200033000120000700059, 0xa0003100060000540001d00017000100001f0004500002000270002c0002f0003d0001f0003700057000600002900012, 0x620005b0004d00005000550003a0001300054000090001f0005d00047000440004f0003c0001c000230000b0005f0002d, 0x510004b000140002e0004700038000260000d000030000d0001300061000490005f000220001a00029000370000a0000e]
  M_cols := [0x180001d000140005b00018000420001200029000410002300064000330000000010000010000a00059000120002d0000e, 0x26000330001f000640002e000520004f0006100039000180000e000430003800001000470001300007000290005f0000a, 0xb0002900042000190003c0001f000150004e000570000b00029000080005e000130003a0005b00012000600000b00037, 0x2c00000000120004f000020001c0004e000110005a0005600007000190003a0001d000440001500033000570002300029, 0xd0002e000520003b000140001900034000010003e0005c00056000530000000046000440002900042000370001c0001a, 0x2b00032000510004c0004500014000270002c0001d0004b0000d00042000390003d0006100017000200001f0003c00022, 0xb000570001600033000140005e0004a0006400019000080003f0000700013000220002400049000490003d0004f0005f, 0x3f0004400010000480005e0004f0004f00026000250000800031000360005e000110003300010000550002f0004400049, 0x1a0002b0003a00013000380000e0003b000330005b0003400059000400004c0002900054000010002c0004700061, 0x320003c0002a0002b0004f0005300008000490002e0006200004000490002e0002c0005c0003600036000270005d00013, 0x41000180005d0001b0005f0003d0003b0001b0005200059000340000f0003f00029000010003200024000020001f0000d, 0x90001600055000330003c000290000f0003f000390006000002000270003b00037000320005f00061000450000900003, 0x3b0000400005000070000a0005900033000350002d000480003b0002e00048000560000200030000300001f000540000d, 0x5400032000370001b00058000460001d000110002c0002a0002f0005f0004100042000540001a00014000100001300026, 0x6400040000220004800024000360000d000270003d0001b00037000600001200027000420000500027000170003a00038, 0x1b00002000040004c0003c0001100057000140005f0003a000150003d00019000200001c00059000270001d0005500047, 0x3400030000430004b00024000370005a00000000520003d0000600061000210000a0001b000160001d00054000050002e, 0x380000f0003c0005e00062000500001c0003300039000630005f0000200017000260003a0004700063000600004d00014, 0xc0003900050000420002b0005500056000150003a0005200026000150005b00052000200003000013000310005b0004b, 0x160000a0001c0003400032000190002a0000c000390004d0003e00028000080004d0000400023000300000a0006200051]
  Minv_rows := [0x700006000400000b000470000f000600000d0000e0004b000110004d000190001a000260001500034000060001600059, 0x2b00004000620006400041000550002c000570001e00048000460003700010000310005b0003d0005c000290003d0005b, 0x5c000120001e000150001c0005b0001d0004e0004c000500002700004000390005e0005d0000e000520005f0000f00041, 0x2400054000160004e00040000530001c00053000440003e0003e00005000230001e0005d0004a00017000180001a0004c, 0x600003e000570003a0006200004000390000c000250004f00010000640005800044000390003d00033000510004300037, 0xc0004800024000510000f0003b000190004500029000220002000062000140005700048000350000a0001b0002a, 0x550003000053000390002b000140000e000450004700000000410002c0004d000590001a00006000640005f0005c0004a, 0x1100051000560004300047000040002e00026000330003800024000230001f000590003e0004100056000310000800029, 0x4b000080003f00041000430003e0000b0004f0001b000530000c0000f000230004f0001700048000620004f000250002e, 0x300003200048000430005200051000550000700055000380000b00008000080001f00013000560003c0005b0005c0001f, 0x2e00054000130005e0004100041000470002c000570004f000240001a000070003d0002e0004e0003c0004a0006200009, 0x3a0004300001000140004a000170000b000530001c0000f000250004b0002f000380001300005000120000e0003f00005, 0x5d0000a0001000042000610004c0001b00046000100002f0004a000290003a0004100052000010004f0004a0006400047, 0x540000c0005200005000020004b0001f000270004d0003a0000d000390001500023000330001100005000140002600009, 0x21000460005f000250004e00017000270000f000160000c0005000025000630003b0000d00012000390001a000290004d, 0x100001a000320001a000360005e0003f000470003b0002a00047000120005a00007000160001f00053000320005800022, 0x210004d00004000150005d00020000250004c0001600021000110002d0000b000610004b00045000280005d000400001d, 0x53000200001d000300002a00054000440005d0000a000160001c00045000090000c000190004b00006000550004d0004f, 0x1e0005d000430003b000180004b0005d0001f0004e000010002a0005a000440001100063000120005200034000130004e, 0x4e000420003e0000700051000380005c00022000410002d00032000370000000045000380005400049000310004700020]
  Minv_cols := [0x590005b000410004c000370002a0004a000290002e0001f000090000500047000090004d000220001d0004f0004e00020, 0x160003d0000f0001a000430001b0005c00008000250005c000620003f00064000260002900058000400004d0001300047, 0x6000290005f00018000510000a0005f000310004f0005b0004a0000e0004a000140001a000320005d000550003400031, 0x340005c000520001700033000350006400056000620003c0003c000120004f00005000390005300028000060005200049, 0x150003d0000e0004a0003d00048000060004100048000560004e000050000100011000120001f000450004b0001200054, 0x260005b0005d0005d00039000570001a0003e00017000130002e0001300052000330000d000160004b000190006300038, 0x1a000310005e0001e000440001400059000590004f0001f0003d0003800041000230003b00007000610000c0001100045, 0x1900010000390002300058000620004d0001f0002300008000070002f0003a00015000630005a0000b000090004400000, 0x4d00037000040000500064000200002c000230000f000080001a0004b000290003900025000120002d000450005a00037, 0x1100046000270003e000100002200041000240000c0000b00024000250004a0000d0005000047000110001c0002a00032, 0x4b00048000500003e0004f00029000000003800053000380004f0000f0002f0003a0000c0002a0002100016000010002d, 0xe0001e0004c00044000250004500047000330001b00055000570001c000100004d000160003b000160000a0004e00041, 0xd000570004e000530000c0001900045000260004f000070002c0005300046000270000f000470004c0005d0001f00022, 0x600002c0001d0001c000390003b0000e0002e0000b00055000470000b0001b0001f000270003f00025000440005d0005c, 0xf000550005b00053000040000f00014000040003e0005100041000170004c0004b000170005e00020000540004b00038, 0x47000410001c0004000062000510002b000470004300052000410004a00061000020004e000360005d0002a0001800051, 0xb00064000150004e0003a00024000390004300041000430005e000140004200005000250001a00015000300003b00007, 0x40000620001e00016000570004800053000560003f00048000130000100010000520005f00032000040001d000430003e, 0x60000400012000540003e0000c0003000051000080003200054000430000a0000c000460001a0004d000200005d00042, 0x70002b0005c00024000600000000055000110004b000300002e0003a0005d00054000210001000021000530001e0004e]
  b0 := ⟨3,
    [0x16000470003400010000510004e0004e, 0x4c000140000f0003d000500003e0004b, 0x560001f0001c00038000090001e00048, 0x390000700008000640003b0004100032, 0x4800039000470004f0004d0005b00051, 0x43000410001b0000200030000440003c, 0x5a000390001200063000170000c00031],
    [0x4e0004b0004800032000510003c00031, 0x4e0003e0001e000410005b000440000c, 0x5100050000090003b0004d0003000017, 0x100003d00038000640004f0000200063, 0x340000f0001c00008000470001b00012, 0x47000140001f00007000390004100039, 0x160004c000560003900048000430005a],
    [0x260005000033000040001f0003000040, 0x61000000002e0001a0002f0005800052, 0x350005300000000420002e0001600008, 0x3d0002f000100002e00019000490001b, 0x3a000360001500011000340004600037, 0x330002c0000f000620003f0000500009, 0x520005e00038000200003b0004f00012],
    [0x4000052000080001b000370000900012, 0x3000058000160004900046000050004f, 0x1f0002f0002e00019000340003f0003b, 0x40001a000420002e000110006200020, 0x330002e0000000010000150000f00038, 0x5000000000530002f000360002c0005e, 0x2600061000350003d0003a0003300052],
    [0x2e0002b00021, 0x3f000540003e, 0x120000100035],
    [0x210003e00035, 0x2b0005400001, 0x2e0003f00012],
    [0x150004800052, 0x13000110000b, 0x370003e00059],
    [0x520000b00059, 0x48000110003e, 0x150001300037],
    [0x2300040000480004b00046000300004a, 0x37000360002200009000010002e00052, 0x3b000320002d00061000460001200023]⟩
  b1 := ⟨4,
    [0x39000610000000058000520000300004, 0x30000210002900020000330004d0005d, 0x310003a0003300053000130004700044, 0x410001e0003b00057000420001b00022, 0x49000130000500029000320003d00003, 0x6200022000000002e000550002b0000e, 0x57000300001e0003d0002f0005500035],
    [0x40005d0004400022000030000e00035, 0x30004d000470001b0003d0002b00055, 0x5200033000130004200032000550002f, 0x58000200005300057000290002e0003d, 0x29000330003b00005000000001e, 0x61000210003a0001e000130002200030, 0x39000300003100041000490006200057],
    [0x230001d0003c0001f000280003700015, 0x390005b0000b000480004d0001f00059, 0x20001c0006000053000510002d00021, 0x4000450003a0003000013000120004e, 0x390004e0004b00063000630003a0002a, 0x380002500051000320000e0002f00027, 0x100004a00010000540001d000180004b],
    [0x1500059000210004e0002a000270004b, 0x370001f0002d000120003a0002f00018, 0x280004d0005100013000630000e0001d, 0x1f000480005300030000630003200054, 0x3c0000b000600003a0004b0005100010, 0x1d0005b0001c000450004e000250004a, 0x23000390000200004000390003800010],
    [0x200000c0003e, 0x320005900035, 0x530002a00045],
    [0x3e0003500045, 0xc000590002a, 0x200003200053],
    [0x170002200004, 0x1e0001b00052, 0x10001900048],
    [0x40005200048, 0x220001b00019, 0x170001e00001],
    [0x5800047000590005d0001f0003a0004f, 0x170003e0006200023000290000900063, 0xd0003e000090005d0000b0004100062]⟩
  b2 := ⟨5,
    [0x20000550001d0001b000460005800054, 0x1b0002e0005d0005a0000b0000300025, 0x3700050000140002d000370000400055, 0x420000f0002d000450003b0000800009, 0x900051000250000d0005a0003300056, 0x580005c0002700004000440002500055, 0x3400011000380004d0003a0001e00043],
    [0x54000250005500009000560005500043, 0x5800003000040000800033000250001e, 0x460000b000370003b0005a000440003a, 0x1b0005a0002d000450000d000040004d, 0x1d0005d000140002d000250002700038, 0x550002e000500000f000510005c00011, 0x200001b0003700042000090005800034],
    [0x590000300020000640005b0002e0005a, 0x5c000030002400008000100005400060, 0x4a000460005f000390004a0005f0001e, 0x5700036000370003e000040005f0000a, 0xf0002500029000330005c0001000064, 0x26000620005d0000d0003d0004f00055, 0x29000320000e00059000040001a0000c],
    [0x5a000600001e0000a00064000550000c, 0x2e000540005f0005f000100004f0001a, 0x5b000100004a000040005c0003d00004, 0x6400008000390003e000330000d00059, 0x20000240005f00037000290005d0000e, 0x3000030004600036000250006200032, 0x590005c0004a000570000f0002600029],
    [0x350005b00029, 0x480001600062, 0x480000200020],
    [0x290006200020, 0x5b0001600002, 0x350004800048],
    [0x70000d0001e, 0x5d0002b00002, 0x230005000052],
    [0x1e0000200052, 0xd0002b00050, 0x70005d00023],
    [0x160004c00038000260005b0000f0002d, 0x1b0004b000260003e000030002b00017, 0x5d000580004a000340001c0001700053]⟩

private theorem tripleCert_19_ok : checkTripleCert tripleCert_19 = true := by decide

/-- Number of servers in `{0, 1, 2, 3, 4, 5}` selected by `inI : Nat → Bool`. -/
def count6 (inI : Nat → Bool) : Nat :=
  (if inI 0 then 1 else 0) + (if inI 1 then 1 else 0) + (if inI 2 then 1 else 0) +
  (if inI 3 then 1 else 0) + (if inI 4 then 1 else 0) + (if inI 5 then 1 else 0)

theorem f101_all_20_triples_valid (inI : Nat → Bool) (h3 : count6 inI = 3) :
    ∃ w : FlagIsoWitness (Fin 101), ValidFlagIso f101Scheme inI w := by
  unfold count6 at h3
  match h0 : inI 0, h1 : inI 1, h2 : inI 2, h3' : inI 3, h4 : inI 4, h5 : inI 5 with
  | false, false, false, false, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, false, false, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, true, false, false, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, true, false, false, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, true, false, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, true, false, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, true, true, false, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, true, true, false, false, false =>
    refine ⟨blkCertToIso tripleCert_0, checkTripleCert_sound tripleCert_0 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_0_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | false, false, false, true, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, false, true, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, true, false, true, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, true, false, true, false, false =>
    refine ⟨blkCertToIso tripleCert_1, checkTripleCert_sound tripleCert_1 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_1_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | false, false, true, true, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, true, true, false, false =>
    refine ⟨blkCertToIso tripleCert_4, checkTripleCert_sound tripleCert_4 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_4_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | false, true, true, true, false, false =>
    refine ⟨blkCertToIso tripleCert_10, checkTripleCert_sound tripleCert_10 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_10_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | true, true, true, true, false, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, false, false, true, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, false, false, true, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, true, false, false, true, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, true, false, false, true, false =>
    refine ⟨blkCertToIso tripleCert_2, checkTripleCert_sound tripleCert_2 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_2_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | false, false, true, false, true, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, true, false, true, false =>
    refine ⟨blkCertToIso tripleCert_5, checkTripleCert_sound tripleCert_5 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_5_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | false, true, true, false, true, false =>
    refine ⟨blkCertToIso tripleCert_11, checkTripleCert_sound tripleCert_11 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_11_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | true, true, true, false, true, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, false, true, true, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, false, true, true, false =>
    refine ⟨blkCertToIso tripleCert_7, checkTripleCert_sound tripleCert_7 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_7_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | false, true, false, true, true, false =>
    refine ⟨blkCertToIso tripleCert_13, checkTripleCert_sound tripleCert_13 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_13_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | true, true, false, true, true, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, true, true, true, false =>
    refine ⟨blkCertToIso tripleCert_16, checkTripleCert_sound tripleCert_16 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_16_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | true, false, true, true, true, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, true, true, true, true, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, true, true, true, true, false => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, false, false, false, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, false, false, false, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, true, false, false, false, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, true, false, false, false, true =>
    refine ⟨blkCertToIso tripleCert_3, checkTripleCert_sound tripleCert_3 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_3_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | false, false, true, false, false, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, true, false, false, true =>
    refine ⟨blkCertToIso tripleCert_6, checkTripleCert_sound tripleCert_6 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_6_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | false, true, true, false, false, true =>
    refine ⟨blkCertToIso tripleCert_12, checkTripleCert_sound tripleCert_12 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_12_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | true, true, true, false, false, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, false, true, false, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, false, true, false, true =>
    refine ⟨blkCertToIso tripleCert_8, checkTripleCert_sound tripleCert_8 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_8_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | false, true, false, true, false, true =>
    refine ⟨blkCertToIso tripleCert_14, checkTripleCert_sound tripleCert_14 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_14_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | true, true, false, true, false, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, true, true, false, true =>
    refine ⟨blkCertToIso tripleCert_17, checkTripleCert_sound tripleCert_17 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_17_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | true, false, true, true, false, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, true, true, true, false, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, true, true, true, false, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, false, false, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, false, false, true, true =>
    refine ⟨blkCertToIso tripleCert_9, checkTripleCert_sound tripleCert_9 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_9_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | false, true, false, false, true, true =>
    refine ⟨blkCertToIso tripleCert_15, checkTripleCert_sound tripleCert_15 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_15_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | true, true, false, false, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, true, false, true, true =>
    refine ⟨blkCertToIso tripleCert_18, checkTripleCert_sound tripleCert_18 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_18_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | true, false, true, false, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, true, true, false, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, true, true, false, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, false, true, true, true =>
    refine ⟨blkCertToIso tripleCert_19, checkTripleCert_sound tripleCert_19 inI rfl rfl rfl ?_ (by decide) (by decide) (by decide) tripleCert_19_ok⟩
    intro n hn hin
    have hn6 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | simp_all
  | true, false, false, true, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, true, false, true, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, true, false, true, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, false, true, true, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, false, true, true, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | false, true, true, true, true, true => simp [h0, h1, h2, h3', h4, h5] at h3
  | true, true, true, true, true, true => simp [h0, h1, h2, h3', h4, h5] at h3

-- ============================================================================
-- Section 6: Headline Theorem `T1l` — Unconditional `F_101` Certified PIR Existence
-- ============================================================================

/-- **Theorem T1l (In-Kernel Certified `F_101` `(M=2, N=6, K=3, T=3)` Rate-`10/17` PIR Existence):**
    Unconditionally establishes inside the Lean 4.35.0 kernel (zero `sorry`, zero `native_decide`,
    zero external oracles!) the constructive existence of a linear MDS-coded PIR scheme over
    `SimpleField (Fin 101)` with `(N=6, K=3, D=20, y=7, z=3)` such that:
    1. **Rate strictly beats `4/7`:** `(K * D) / (N * (2y + z)) = 60 / 102 = 10 / 17 > 4 / 7`.
    2. **Exact Zero-Error Decoding:** For EVERY valid invertible randomness `r`, EVERY database
       `(W1, W2)`, and BOTH desired files `θ ∈ {false, true}`, `pirDecode` recovers the exact
       desired file symbol-for-symbol.
    3. **Exact Information-Theoretic `T = 3` Collusion Privacy:** For EVERY 3-subset `inI` of the
       6 servers (`20/20` triples), there exists a kernel-certified flag isomorphism `w` whose
       explicit randomness map `Ψ_I` is a two-sided bijection on `ValidRand` mapping the `θ = false`
       query tuple onto the `θ = true` query tuple entry-for-entry on all 3 colluding servers! -/
theorem t1l_f101_t3_k3_e6_certified_pir_existence :
    ∃ (sc : PIRScheme (Fin 101)) (Cancel DecInv : Nat → Nat → Fin 101),
      sc.N = 6 ∧ sc.K = 3 ∧ sc.D = 20 ∧ sc.y = 7 ∧ sc.z = 3 ∧
      (sc.K * sc.D) * 7 > (sc.N * (2 * sc.y + sc.z)) * 4 ∧
      (∀ (r : PIRRand (Fin 101)), ValidRand sc r →
        ∀ (W1 W2 : Nat → Nat → Fin 101) (θ : Bool) (k d : Nat),
          k < sc.K → d < sc.D →
          pirDecode sc Cancel DecInv θ r
            (ansBlk1 sc θ r W1) (ansBlk2 sc θ r W2) (ansBlk3 sc θ r W1 W2) k d =
          (if θ then W2 k d else W1 k d)) ∧
      (∀ (inI : Nat → Bool), count6 inI = 3 →
        ∃ (w : FlagIsoWitness (Fin 101)),
          ValidFlagIso sc inI w ∧
          (∀ r, ValidRand sc r → ValidRand sc (psiFwd sc inI w r) ∧ ValidRand sc (psiInv sc inI w r)) ∧
          (∀ r, RandEq sc (psiInv sc inI w (psiFwd sc inI w r)) r ∧
                RandEq sc (psiFwd sc inI w (psiInv sc inI w r)) r) ∧
          (∀ r n, n < sc.N → inI n = true →
            MatEq sc.y sc.D (qBlk1 sc true (psiFwd sc inI w r) n) (qBlk1 sc false r n) ∧
            MatEq sc.y sc.D (qBlk2 sc true (psiFwd sc inI w r) n) (qBlk2 sc false r n) ∧
            MatEq sc.z sc.D (qBlk3File1 sc true (psiFwd sc inI w r) n) (qBlk3File1 sc false r n) ∧
            MatEq sc.z sc.D (qBlk3File2 sc true (psiFwd sc inI w r) n) (qBlk3File2 sc false r n))) := by
  refine ⟨f101Scheme, f101CancelMat, f101DecInvMat, rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro r hr W1 W2 θ k d hk hd
    exact pir_zero_error_decoding_exact f101Scheme (by decide) (by decide) (by decide)
      f101CancelMat f101DecInvMat f101_cancel_cert f101_dec_cert r hr W1 W2 θ k d hk hd
  · intro inI h3
    obtain ⟨w, hw⟩ := f101_all_20_triples_valid inI h3
    obtain ⟨hpres, hbij, hid⟩ := pir_exact_t_privacy_bijection f101Scheme inI w hw
    exact ⟨w, hw, hpres, hbij, hid⟩

end
end TriadFrontier.PIRF101Cert
