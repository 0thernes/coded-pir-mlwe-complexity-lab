module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore
public import TriadFrontier.ShannonCapacity

/-!
# Infinite-Family Zero-Reals Symbolic Lovász Shannon Capacity for Paley / Conference Graphs (`T3l`)

Zero-Mathlib, zero-real-number, first-principles Lean 4.35.0 formalization of the **entire infinite
family** of self-complementary conference / Paley graph Shannon capacities (`CS-CMP-012`):
1. **General Exact Ordered Quadratic Ring `QuadInt D` (`Z[√D]`):**
   Exact integer arithmetic & sign order `qnonneg D (a, b)` (meaning `a + b√D ≥ 0`) with zero real numbers.
2. **Universal Symbolic 2-Block `Z[√p]` SOS Factorization for EVERY Conference Graph `(4k+1, 2k, k-1, k)`:**
   For EVERY `k ≥ 1` (`p = 4k + 1`) and EVERY symmetric loopless `2k`-regular graph `G` satisfying
   `A^2 + A - k I = k J`, the explicit matrix `R = 2p A + p(1+√p) I - (p+√p) J ∈ Z[√p]^{p × p}`
   satisfies `R^T R = 2p √p R` symbolically, giving the exact 2-block positive-weight SOS identity:
   `8 k p^2 √p · M_{p+1} = 8 k p^2 · h h^T + (√p - 1) · R̃^T R̃`.
   Kronecker-power lifting proves **`s * s ≤ (4k + 1)^t`** for EVERY `t : Nat` and EVERY independent
   set of size `s` in `G^{⊠ t}`!
3. **Universal Self-Complementary Lower Bound (`self_comp_indep_lift`):**
   Every `n`-vertex self-complementary graph `G` (admitting an anti-automorphism bijection `φ`)
   contains an explicit `n`-element independent set `{(x, φ(x))}` in `G^{⊠ 2}`, lifting to
   **`α(G^{⊠ 2m}) ≥ n^m`** for EVERY `m : Nat`!
4. **Infinite Exact Capacity Theorem `Θ(G) = √(4k+1)` + Concrete Paley Instances `P_5, P_13, P_17`:**
   Combines (2) and (3) to prove exact `α(G^{⊠ 2m}) = (4k+1)^m` and `s^2 ≤ (4k+1)^t` for EVERY
   self-complementary conference graph, instantiated concretely in Lean for `P_5 = C_5`, `P_13`, and `P_17`!
-/

namespace TriadFrontier.PaleyCapacity

open TriadFrontier.AlgebraCore
open TriadFrontier.ShannonCapacity

@[expose] public section

-- ============================================================================
-- Section 1: Exact Ordered Quadratic Integer Ring `QuadInt D` (`Z[√D]`)
-- ============================================================================

/-- Element `a + b√D` of the exact quadratic ring `Z[√D]` (zero real numbers!). -/
structure QuadInt (D : Nat) where
  a : Int
  b : Int
  deriving DecidableEq

def qzero (D : Nat) : QuadInt D := ⟨0, 0⟩
def qone (D : Nat) : QuadInt D := ⟨1, 0⟩
def qofInt (D : Nat) (n : Int) : QuadInt D := ⟨n, 0⟩
def qsqrt (D : Nat) : QuadInt D := ⟨0, 1⟩
def qadd {D : Nat} (x y : QuadInt D) : QuadInt D := ⟨x.a + y.a, x.b + y.b⟩
def qneg {D : Nat} (x : QuadInt D) : QuadInt D := ⟨-x.a, -x.b⟩
def qsub {D : Nat} (x y : QuadInt D) : QuadInt D := ⟨x.a - y.a, x.b - y.b⟩
def qmul {D : Nat} (x y : QuadInt D) : QuadInt D :=
  ⟨x.a * y.a + (D : Int) * x.b * y.b, x.a * y.b + x.b * y.a⟩

def qpow {D : Nat} (x : QuadInt D) : Nat → QuadInt D
  | 0 => qone D
  | k + 1 => qmul (qpow x k) x

def sumQ {D : Nat} : Nat → (Nat → QuadInt D) → QuadInt D
  | 0, _ => qzero D
  | k + 1, f => qadd (sumQ k f) (f k)

def prodQ {D : Nat} : Nat → (Nat → QuadInt D) → QuadInt D
  | 0, _ => qone D
  | k + 1, f => qmul (prodQ k f) (f k)

theorem qext {D : Nat} {x y : QuadInt D} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; simp only [QuadInt.mk.injEq]; exact ⟨ha, hb⟩

private theorem int_mlc (x y z : Int) : x * (y * z) = y * (x * z) := by
  rw [← Int.mul_assoc, Int.mul_comm x y, Int.mul_assoc]

private theorem int_mul_neg_sq (d x : Int) : d * (-x) * (-x) = d * x * x := by
  rw [Int.mul_neg (d * (-x)) x, Int.mul_neg d x, Int.neg_mul, Int.neg_neg]

private theorem nat_pos_pow (a : Nat) (ha : 0 < a) : ∀ n : Nat, 0 < a ^ n
  | 0 => by simp
  | n + 1 => Nat.mul_pos (nat_pos_pow a ha n) ha

private theorem int_poly3 (x y z a b c : Int) :
    (x + y - z) * (a + b - c) =
    x * a + x * b - x * c + y * a + y * b - y * c - z * a - z * b + z * c := by
  rw [Int.sub_mul, Int.add_mul, Int.mul_sub, Int.mul_add, Int.mul_sub, Int.mul_add,
      Int.mul_sub, Int.mul_add]; omega

private theorem int_poly2 (d x y : Int) :
    d * (x - 1) * (y - 1) = d * x * y - d * x - d * y + d := by
  rw [Int.mul_sub, Int.mul_one, Int.mul_sub d x 1, Int.mul_one, Int.sub_mul]; omega

private theorem int_poly32 (x y z a : Int) :
    (x + y - z) * (a - 1) = x * a + y * a - z * a - x - y + z := by
  rw [Int.mul_sub, Int.mul_one, Int.sub_mul, Int.add_mul]; omega

private theorem int_poly23 (a x y z : Int) :
    (a - 1) * (x + y - z) = a * x + a * y - a * z - x - y + z := by
  rw [Int.sub_mul, Int.one_mul, Int.mul_sub, Int.mul_add]; omega

theorem qadd_comm {D : Nat} (x y : QuadInt D) : qadd x y = qadd y x :=
  qext (Int.add_comm ..) (Int.add_comm ..)

theorem qadd_assoc {D : Nat} (x y z : QuadInt D) : qadd (qadd x y) z = qadd x (qadd y z) :=
  qext (Int.add_assoc ..) (Int.add_assoc ..)

theorem qzero_add {D : Nat} (x : QuadInt D) : qadd (qzero D) x = x :=
  qext (Int.zero_add ..) (Int.zero_add ..)

theorem qadd_zero {D : Nat} (x : QuadInt D) : qadd x (qzero D) = x :=
  qext (Int.add_zero ..) (Int.add_zero ..)

theorem qmul_comm {D : Nat} (x y : QuadInt D) : qmul x y = qmul y x := by
  apply qext
  · simp only [qmul]
    have h1 : x.a * y.a = y.a * x.a := Int.mul_comm ..
    have h2 : (D : Int) * x.b * y.b = (D : Int) * y.b * x.b := by
      rw [Int.mul_assoc, Int.mul_comm x.b y.b, ← Int.mul_assoc]
    omega
  · simp only [qmul]
    rw [Int.mul_comm x.a y.b, Int.mul_comm x.b y.a, Int.add_comm]

theorem qmul_assoc {D : Nat} (x y z : QuadInt D) : qmul (qmul x y) z = qmul x (qmul y z) := by
  apply qext <;> simp only [qmul]
  · rw [Int.add_mul, Int.mul_add (D : Int), Int.add_mul, Int.mul_add, Int.mul_add]
    have e1 : x.a * y.a * z.a = x.a * (y.a * z.a) := Int.mul_assoc ..
    have e2 : (D : Int) * x.b * y.b * z.a = (D : Int) * x.b * (y.b * z.a) := Int.mul_assoc ..
    have e3 : (D : Int) * (x.a * y.b) * z.b = x.a * ((D : Int) * y.b * z.b) := by
      simp only [Int.mul_assoc]; rw [int_mlc (D : Int) x.a]
    have e4 : (D : Int) * (x.b * y.a) * z.b = (D : Int) * x.b * (y.a * z.b) := by
      simp only [Int.mul_assoc]
    omega
  · rw [Int.add_mul, Int.add_mul, Int.mul_add, Int.mul_add]
    have e1 : x.a * y.a * z.b = x.a * (y.a * z.b) := Int.mul_assoc ..
    have e2 : (D : Int) * x.b * y.b * z.b = x.b * ((D : Int) * y.b * z.b) := by
      simp only [Int.mul_assoc]; rw [int_mlc (D : Int) x.b]
    have e3 : x.a * y.b * z.a = x.a * (y.b * z.a) := Int.mul_assoc ..
    have e4 : x.b * y.a * z.a = x.b * (y.a * z.a) := Int.mul_assoc ..
    omega

theorem qone_mul {D : Nat} (x : QuadInt D) : qmul (qone D) x = x :=
  qext (by simp [qmul, qone]) (by simp [qmul, qone])

theorem qmul_one {D : Nat} (x : QuadInt D) : qmul x (qone D) = x := by
  rw [qmul_comm, qone_mul]

theorem qzero_mul {D : Nat} (x : QuadInt D) : qmul (qzero D) x = qzero D :=
  qext (by simp [qmul, qzero]) (by simp [qmul, qzero])

theorem qmul_zero {D : Nat} (x : QuadInt D) : qmul x (qzero D) = qzero D := by
  rw [qmul_comm, qzero_mul]

theorem qmul_add {D : Nat} (x y z : QuadInt D) : qmul x (qadd y z) = qadd (qmul x y) (qmul x z) := by
  apply qext <;> simp only [qmul, qadd]
  · rw [Int.mul_add, Int.mul_add]; omega
  · rw [Int.mul_add, Int.mul_add]; omega

theorem qadd_mul {D : Nat} (x y z : QuadInt D) : qmul (qadd x y) z = qadd (qmul x z) (qmul y z) := by
  rw [qmul_comm, qmul_add, qmul_comm z x, qmul_comm z y]

theorem qneg_mul {D : Nat} (x y : QuadInt D) : qmul (qneg x) y = qneg (qmul x y) := by
  apply qext <;> simp only [qmul, qneg]
  · rw [Int.neg_mul, Int.mul_neg, Int.neg_mul]; omega
  · rw [Int.neg_mul, Int.neg_mul]; omega

theorem qmul_neg {D : Nat} (x y : QuadInt D) : qmul x (qneg y) = qneg (qmul x y) := by
  rw [qmul_comm, qneg_mul, qmul_comm]

theorem qsub_eq {D : Nat} (x y : QuadInt D) : qsub x y = qadd x (qneg y) :=
  qext (by simp [qsub, qadd, qneg]; omega) (by simp [qsub, qadd, qneg]; omega)

theorem qadd_neg {D : Nat} (x : QuadInt D) : qadd x (qneg x) = qzero D :=
  qext (by simp [qadd, qneg, qzero]; omega) (by simp [qadd, qneg, qzero]; omega)

theorem sumQ_congr {D : Nat} {N : Nat} {f g : Nat → QuadInt D}
    (h : ∀ i, i < N → f i = g i) : sumQ N f = sumQ N g := by
  induction N with
  | zero => rfl
  | succ k ih => simp only [sumQ]; rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem sumQ_add {D : Nat} (N : Nat) (f g : Nat → QuadInt D) :
    sumQ N (fun i => qadd (f i) (g i)) = qadd (sumQ N f) (sumQ N g) := by
  induction N with
  | zero => exact (qzero_add _).symm
  | succ k ih =>
    simp only [sumQ, ih]
    rw [qadd_assoc, ← qadd_assoc (sumQ k g), qadd_comm (sumQ k g) (f k), qadd_assoc (f k), ← qadd_assoc]

theorem sumQ_mul_left {D : Nat} (N : Nat) (c : QuadInt D) (f : Nat → QuadInt D) :
    sumQ N (fun i => qmul c (f i)) = qmul c (sumQ N f) := by
  induction N with
  | zero => exact (qmul_zero c).symm
  | succ k ih => simp only [sumQ, ih, qmul_add]

theorem sumQ_mul_right {D : Nat} (N : Nat) (c : QuadInt D) (f : Nat → QuadInt D) :
    sumQ N (fun i => qmul (f i) c) = qmul (sumQ N f) c := by
  induction N with
  | zero => exact (qzero_mul c).symm
  | succ k ih => simp only [sumQ, ih, qadd_mul]

theorem sumQ_zero {D : Nat} (N : Nat) : sumQ N (fun _ => qzero D) = qzero D := by
  induction N with
  | zero => rfl
  | succ k ih => simp only [sumQ, ih, qzero_add]

theorem sumQ_swap {D : Nat} (M N : Nat) (f : Nat → Nat → QuadInt D) :
    sumQ M (fun i => sumQ N (fun j => f i j)) = sumQ N (fun j => sumQ M (fun i => f i j)) := by
  induction M with
  | zero => simp only [sumQ, sumQ_zero]
  | succ m ihm => simp only [sumQ, ihm, ← sumQ_add]

theorem sumQ_mul_factor {D : Nat} (A B : Nat) (f g : Nat → QuadInt D) :
    sumQ (A * B) (fun s => qmul (f (s / B)) (g (s % B))) = qmul (sumQ A f) (sumQ B g) := by
  induction A with
  | zero => simp [sumQ, qzero_mul]
  | succ a ih =>
    have hadd : ∀ (base len : Nat) (h : Nat → QuadInt D),
        sumQ (base + len) h = qadd (sumQ base h) (sumQ len (fun j => h (base + j))) := by
      intro base len h
      induction len with
      | zero => simp [sumQ, qadd_zero]
      | succ l ihl => rw [Nat.add_succ, sumQ, ihl, sumQ, qadd_assoc]
    rw [Nat.succ_mul, hadd (a * B) B, ih, sumQ, qadd_mul]
    congr 1
    cases B with
    | zero => simp [sumQ, qmul_zero]
    | succ b' =>
      have hB : 0 < b' + 1 := Nat.zero_lt_succ b'
      rw [← sumQ_mul_left]
      apply sumQ_congr
      intro j hj
      have hd : (a * (b' + 1) + j) / (b' + 1) = a := by
        rw [Nat.mul_comm a (b' + 1), Nat.mul_add_div hB, Nat.div_eq_of_lt hj, Nat.add_zero]
      have hm : (a * (b' + 1) + j) % (b' + 1) = j := by
        rw [Nat.mul_comm a (b' + 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      rw [hd, hm]

/-- Exact integer non-negativity predicate `a + b√D ≥ 0` in `Z[√D]` (zero real numbers!). -/
def qnonneg (D : Nat) (x : QuadInt D) : Prop :=
  (0 ≤ x.a ∧ 0 ≤ x.b) ∨
  (0 ≤ x.a ∧ x.b < 0 ∧ (D : Int) * x.b * x.b ≤ x.a * x.a) ∨
  (x.a < 0 ∧ 0 ≤ x.b ∧ x.a * x.a ≤ (D : Int) * x.b * x.b)

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -x := by omega
    have := Int.mul_nonneg h' h'
    rwa [Int.neg_mul, Int.mul_neg, Int.neg_neg] at this

private theorem int_mul_le_of_sq {u v : Int} (hu : 0 ≤ u) (hv : 0 ≤ v) (hsq : u * u ≤ v * v) : u ≤ v := by
  by_cases h : u ≤ v
  · exact h
  · have hlt : v < u := by omega
    have hdiff : 0 < (u - v) * (u + v) := Int.mul_pos (by omega) (by omega)
    have hid : (u - v) * (u + v) = u * u - v * v := by
      rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm v u]; omega
    omega

theorem qnonneg_zero (D : Nat) : qnonneg D (qzero D) := by
  unfold qnonneg qzero; exact Or.inl ⟨Int.le_refl 0, Int.le_refl 0⟩

theorem qnonneg_sq (D : Nat) (x : QuadInt D) : qnonneg D (qmul x x) := by
  unfold qnonneg; dsimp only [qmul]
  -- x^2 = (a^2 + D b^2) + (2ab) √D, and (a^2 + D b^2)^2 - D (2ab)^2 = (a^2 - D b^2)^2 ≥ 0!
  have ha0 : 0 ≤ x.a * x.a + (D : Int) * x.b * x.b := by
    have h1 := int_sq_nonneg x.a
    have h2 : 0 ≤ (D : Int) * (x.b * x.b) := Int.mul_nonneg (Int.natCast_nonneg D) (int_sq_nonneg x.b)
    rw [Int.mul_assoc]; omega
  by_cases hb : 0 ≤ x.a * x.b + x.b * x.a
  · exact Or.inl ⟨ha0, hb⟩
  · right; left
    refine ⟨ha0, by omega, ?_⟩
    let u := x.a * x.a
    let v := (D : Int) * x.b * x.b
    have h1 : (D : Int) * (x.a * x.b + x.b * x.a) * (x.a * x.b + x.b * x.a) = 4 * (u * v) := by
      dsimp only [u, v]
      have hcomm : x.a * x.b + x.b * x.a = 2 * (x.a * x.b) := by rw [Int.mul_comm x.b x.a, Int.two_mul]
      rw [hcomm]
      have hl : (D : Int) * (2 * (x.a * x.b)) * (2 * (x.a * x.b)) =
          4 * ((x.a * x.a) * ((D : Int) * x.b * x.b)) := by
        simp only [Int.mul_assoc]
        calc (D : Int) * (2 * (x.a * (x.b * (2 * (x.a * x.b)))))
            = 2 * ((D : Int) * (x.a * (x.b * (2 * (x.a * x.b))))) := int_mlc ..
          _ = 2 * (2 * ((D : Int) * (x.a * (x.b * (x.a * x.b))))) := by
              congr 1
              rw [int_mlc (x.b) 2, int_mlc x.a 2, int_mlc (D : Int) 2]
          _ = 4 * (x.a * (x.a * ((D : Int) * (x.b * x.b)))) := by
              rw [← Int.mul_assoc 2 2]
              have h4 : (2 : Int) * 2 = 4 := rfl
              rw [h4]; congr 1
              rw [int_mlc x.b x.a, int_mlc (D : Int) x.a, int_mlc (D : Int) x.a]
      exact hl
    have h2 : (u + v) * (u + v) - 4 * (u * v) = (u - v) * (u - v) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm v u]; omega
    have h3 := int_sq_nonneg (u - v)
    change (D : Int) * (x.a * x.b + x.b * x.a) * (x.a * x.b + x.b * x.a) ≤ (u + v) * (u + v)
    rw [h1]; omega

theorem qnonneg_add (D : Nat) (x y : QuadInt D) (hx : qnonneg D x) (hy : qnonneg D y) :
    qnonneg D (qadd x y) := by
  have hD : 0 ≤ (D : Int) := Int.natCast_nonneg D
  -- Helper: if 0 ≤ u1, u2, v1, v2 and D v1^2 ≤ u1^2 and D v2^2 ≤ u2^2 then D (v1+v2)^2 ≤ (u1+u2)^2
  have hcomb_ge : ∀ u1 u2 v1 v2 : Int, 0 ≤ u1 → 0 ≤ u2 → 0 ≤ v1 → 0 ≤ v2 →
      (D : Int) * v1 * v1 ≤ u1 * u1 → (D : Int) * v2 * v2 ≤ u2 * u2 →
      (D : Int) * (v1 + v2) * (v1 + v2) ≤ (u1 + u2) * (u1 + u2) := by
    intro u1 u2 v1 v2 hu1 hu2 hv1 hv2 h1 h2
    have hcross_sq : ((D : Int) * v1 * v2) * ((D : Int) * v1 * v2) ≤ (u1 * u2) * (u1 * u2) := by
      have hL : ((D : Int) * v1 * v2) * ((D : Int) * v1 * v2) =
          ((D : Int) * v1 * v1) * ((D : Int) * v2 * v2) := by
        simp only [Int.mul_assoc]; congr 2
        rw [int_mlc v2 (D : Int), int_mlc v1 (D : Int)]; congr 1; rw [int_mlc v2 v1]
      have hR : (u1 * u2) * (u1 * u2) = (u1 * u1) * (u2 * u2) := by
        simp only [Int.mul_assoc]; congr 1; rw [int_mlc u2 u1]
      rw [hL, hR]
      have h1nn : 0 ≤ (D : Int) * v1 * v1 := Int.mul_nonneg (Int.mul_nonneg hD hv1) hv1
      have h2nn : 0 ≤ (D : Int) * v2 * v2 := Int.mul_nonneg (Int.mul_nonneg hD hv2) hv2
      exact Int.le_trans (Int.mul_le_mul_of_nonneg_right h1 h2nn)
        (Int.mul_le_mul_of_nonneg_left h2 (Int.mul_nonneg hu1 hu1))
    have hcross : (D : Int) * v1 * v2 ≤ u1 * u2 :=
      int_mul_le_of_sq (Int.mul_nonneg (Int.mul_nonneg hD hv1) hv2) (Int.mul_nonneg hu1 hu2) hcross_sq
    have hE1 : (D : Int) * (v1 + v2) * (v1 + v2) =
        (D : Int) * v1 * v1 + 2 * ((D : Int) * v1 * v2) + (D : Int) * v2 * v2 := by
      rw [Int.mul_add (D : Int) v1 v2, Int.add_mul, Int.mul_add, Int.mul_add]
      have hm : (D : Int) * v2 * v1 = (D : Int) * v1 * v2 := by
        rw [Int.mul_assoc, Int.mul_comm v2 v1, ← Int.mul_assoc]
      omega
    have hE2 : (u1 + u2) * (u1 + u2) = u1 * u1 + 2 * (u1 * u2) + u2 * u2 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm u2 u1]; omega
    rw [hE1, hE2]; omega
  -- Helper: if 0 ≤ u1, u2, v1, v2 and u1^2 ≤ D v1^2 and u2^2 ≤ D v2^2 then (u1+u2)^2 ≤ D (v1+v2)^2
  have hcomb_le : ∀ u1 u2 v1 v2 : Int, 0 ≤ u1 → 0 ≤ u2 → 0 ≤ v1 → 0 ≤ v2 →
      u1 * u1 ≤ (D : Int) * v1 * v1 → u2 * u2 ≤ (D : Int) * v2 * v2 →
      (u1 + u2) * (u1 + u2) ≤ (D : Int) * (v1 + v2) * (v1 + v2) := by
    intro u1 u2 v1 v2 hu1 hu2 hv1 hv2 h1 h2
    have hcross_sq : (u1 * u2) * (u1 * u2) ≤ ((D : Int) * v1 * v2) * ((D : Int) * v1 * v2) := by
      have hL : (u1 * u2) * (u1 * u2) = (u1 * u1) * (u2 * u2) := by
        simp only [Int.mul_assoc]; congr 1; rw [int_mlc u2 u1]
      have hR : ((D : Int) * v1 * v2) * ((D : Int) * v1 * v2) =
          ((D : Int) * v1 * v1) * ((D : Int) * v2 * v2) := by
        simp only [Int.mul_assoc]; congr 2
        rw [int_mlc v2 (D : Int), int_mlc v1 (D : Int)]; congr 1; rw [int_mlc v2 v1]
      rw [hL, hR]
      exact Int.le_trans (Int.mul_le_mul_of_nonneg_right h1 (Int.mul_nonneg hu2 hu2))
        (Int.mul_le_mul_of_nonneg_left h2 (Int.mul_nonneg (Int.mul_nonneg hD hv1) hv1))
    have hcross : u1 * u2 ≤ (D : Int) * v1 * v2 :=
      int_mul_le_of_sq (Int.mul_nonneg hu1 hu2) (Int.mul_nonneg (Int.mul_nonneg hD hv1) hv2) hcross_sq
    have hE1 : (D : Int) * (v1 + v2) * (v1 + v2) =
        (D : Int) * v1 * v1 + 2 * ((D : Int) * v1 * v2) + (D : Int) * v2 * v2 := by
      rw [Int.mul_add (D : Int) v1 v2, Int.add_mul, Int.mul_add, Int.mul_add]
      have hm : (D : Int) * v2 * v1 = (D : Int) * v1 * v2 := by
        rw [Int.mul_assoc, Int.mul_comm v2 v1, ← Int.mul_assoc]
      omega
    have hE2 : (u1 + u2) * (u1 + u2) = u1 * u1 + 2 * (u1 * u2) + u2 * u2 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm u2 u1]; omega
    rw [hE1, hE2]; omega
  -- Opposite-sign cancellation helper:
  have hopp : ∀ a1 b1 a2 b2 : Int,
      0 ≤ a1 → b1 < 0 → (D : Int) * b1 * b1 ≤ a1 * a1 →
      a2 < 0 → 0 ≤ b2 → a2 * a2 ≤ (D : Int) * b2 * b2 →
      qnonneg D ⟨a1 + a2, b1 + b2⟩ := by
    intro a1 b1 a2 b2 ha1 hb1 h1 ha2 hb2 h2
    unfold qnonneg; dsimp only
    by_cases hsa : 0 ≤ a1 + a2
    · by_cases hsb : 0 ≤ b1 + b2
      · exact Or.inl ⟨hsa, hsb⟩
      · right; left; refine ⟨hsa, by omega, ?_⟩
        by_cases hok : (D : Int) * (b1 + b2) * (b1 + b2) ≤ (a1 + a2) * (a1 + a2)
        · exact hok
        · exfalso
          have hstrict : (a1 + a2) * (a1 + a2) < (D : Int) * (-(b1 + b2)) * (-(b1 + b2)) := by
            rw [int_mul_neg_sq]; omega
          have hlt : (a1 + a2) * (a1 + a2) ≤ (D : Int) * (-(b1 + b2)) * (-(b1 + b2)) := by omega
          have h2' : (-a2) * (-a2) ≤ (D : Int) * b2 * b2 := by
            rwa [Int.neg_mul, Int.mul_neg, Int.neg_neg]
          have h1' : (D : Int) * (-b1) * (-b1) ≤ a1 * a1 := by
            rwa [int_mul_neg_sq]
          let S := a1 + a2
          let U2 := -a2
          let T := -(b1 + b2)
          have hcross_sq : (S * U2) * (S * U2) ≤ ((D : Int) * T * b2) * ((D : Int) * T * b2) := by
            have hL : (S * U2) * (S * U2) = (S * S) * (U2 * U2) := by
              simp only [Int.mul_assoc]; congr 1; rw [int_mlc U2 S]
            have hR : ((D : Int) * T * b2) * ((D : Int) * T * b2) =
                ((D : Int) * T * T) * ((D : Int) * b2 * b2) := by
              simp only [Int.mul_assoc]; congr 2
              rw [int_mlc b2 (D : Int), int_mlc T (D : Int)]; congr 1; rw [int_mlc b2 T]
            rw [hL, hR]
            exact Int.le_trans (Int.mul_le_mul_of_nonneg_right hlt (Int.mul_nonneg (by omega) (by omega)))
              (Int.mul_le_mul_of_nonneg_left h2' (Int.mul_nonneg (Int.mul_nonneg hD (by omega)) (by omega)))
          have hcross : S * U2 ≤ (D : Int) * T * b2 :=
            int_mul_le_of_sq (Int.mul_nonneg hsa (by omega)) (Int.mul_nonneg (Int.mul_nonneg hD (by omega)) hb2) hcross_sq
          have hE1 : (D : Int) * (T + b2) * (T + b2) =
              (D : Int) * T * T + 2 * ((D : Int) * T * b2) + (D : Int) * b2 * b2 := by
            rw [Int.mul_add (D : Int) T b2, Int.add_mul, Int.mul_add, Int.mul_add]
            have hm : (D : Int) * b2 * T = (D : Int) * T * b2 := by
              rw [Int.mul_assoc, Int.mul_comm b2 T, ← Int.mul_assoc]
            omega
          have hE2 : (S + U2) * (S + U2) = S * S + 2 * (S * U2) + U2 * U2 := by
            rw [Int.add_mul S U2 (S + U2), Int.mul_add S S U2, Int.mul_add U2 S U2, Int.mul_comm U2 S]; omega
          have hSA : S + U2 = a1 := by dsimp only [S, U2]; omega
          have hTB : T + b2 = -b1 := by dsimp only [T]; omega
          rw [hSA] at hE2; rw [hTB] at hE1
          dsimp only [S, U2, T] at hstrict h2' hcross hE1 hE2
          omega
    · by_cases hsb : 0 ≤ b1 + b2
      · right; right; refine ⟨by omega, hsb, ?_⟩
        by_cases hok : (a1 + a2) * (a1 + a2) ≤ (D : Int) * (b1 + b2) * (b1 + b2)
        · exact hok
        · exfalso
          have hstrict : (D : Int) * (b1 + b2) * (b1 + b2) < (-(a1 + a2)) * (-(a1 + a2)) := by
            rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]; omega
          let S := -(a1 + a2)
          let T := b1 + b2
          have h1' : (D : Int) * (-b1) * (-b1) ≤ a1 * a1 := by
            rwa [int_mul_neg_sq]
          have hcross_sq : ((D : Int) * T * (-b1)) * ((D : Int) * T * (-b1)) ≤ (S * a1) * (S * a1) := by
            have hL : ((D : Int) * T * (-b1)) * ((D : Int) * T * (-b1)) =
                ((D : Int) * T * T) * ((D : Int) * (-b1) * (-b1)) := by
              simp only [Int.mul_assoc]; congr 2
              rw [int_mlc (-b1) (D : Int), int_mlc T (D : Int)]; congr 1; rw [int_mlc (-b1) T]
            have hR : (S * a1) * (S * a1) = (S * S) * (a1 * a1) := by
              simp only [Int.mul_assoc]; congr 1; rw [int_mlc a1 S]
            rw [hL, hR]
            exact Int.le_trans (Int.mul_le_mul_of_nonneg_right (by dsimp only [S, T]; omega) (Int.mul_nonneg (Int.mul_nonneg hD (by omega)) (by omega)))
              (Int.mul_le_mul_of_nonneg_left h1' (Int.mul_nonneg (by omega) (by omega)))
          have hcross : (D : Int) * T * (-b1) ≤ S * a1 :=
            int_mul_le_of_sq (Int.mul_nonneg (Int.mul_nonneg hD hsb) (by omega)) (Int.mul_nonneg (by omega) ha1) hcross_sq
          have hE1 : (D : Int) * (T + (-b1)) * (T + (-b1)) =
              (D : Int) * T * T + 2 * ((D : Int) * T * (-b1)) + (D : Int) * (-b1) * (-b1) := by
            rw [Int.mul_add (D : Int) T (-b1), Int.add_mul ((D : Int) * T) ((D : Int) * (-b1)) (T + (-b1)),
                Int.mul_add ((D : Int) * T) T (-b1), Int.mul_add ((D : Int) * (-b1)) T (-b1)]
            have hm : (D : Int) * (-b1) * T = (D : Int) * T * (-b1) := by
              rw [Int.mul_assoc, Int.mul_comm (-b1) T, ← Int.mul_assoc]
            omega
          have hE2 : (S + a1) * (S + a1) = S * S + 2 * (S * a1) + a1 * a1 := by
            rw [Int.add_mul S a1 (S + a1), Int.mul_add S S a1, Int.mul_add a1 S a1, Int.mul_comm a1 S]; omega
          have hSA : S + a1 = -a2 := by dsimp only [S]; omega
          have hTB : T + (-b1) = b2 := by dsimp only [T]; omega
          rw [hSA, Int.neg_mul, Int.mul_neg, Int.neg_neg] at hE2; rw [hTB] at hE1
          dsimp only [S, T] at hstrict hcross hE1 hE2
          omega
      · exfalso
        have hltA : a1 * a1 < (-a2) * (-a2) := by
          have : 0 < ((-a2) - a1) * ((-a2) + a1) := Int.mul_pos (by omega) (by omega)
          have hid : ((-a2) - a1) * ((-a2) + a1) = (-a2) * (-a2) - a1 * a1 := by
            rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm a1 (-a2)]; omega
          omega
        have hleB : (D : Int) * b2 * b2 ≤ (D : Int) * (-b1) * (-b1) := by
          have hb2le : b2 * b2 ≤ (-b1) * (-b1) := by
            have : 0 ≤ ((-b1) - b2) * ((-b1) + b2) := Int.mul_nonneg (by omega) (by omega)
            have hid : ((-b1) - b2) * ((-b1) + b2) = (-b1) * (-b1) - b2 * b2 := by
              rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm b2 (-b1)]; omega
            omega
          rw [Int.mul_assoc, Int.mul_assoc]
          exact Int.mul_le_mul_of_nonneg_left hb2le hD
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at hltA
        rw [int_mul_neg_sq] at hleB
        omega
  -- Now dispatch all 3 × 3 cases of hx and hy!
  rcases hx with ⟨hxa, hxb⟩ | ⟨hxa, hxb, hxsq⟩ | ⟨hxa, hxb, hxsq⟩ <;>
  rcases hy with ⟨hya, hyb⟩ | ⟨hya, hyb, hysq⟩ | ⟨hya, hyb, hysq⟩
  · unfold qnonneg; dsimp only [qadd]; exact Or.inl ⟨by omega, by omega⟩
  · unfold qnonneg; dsimp only [qadd]
    by_cases hsb : 0 ≤ x.b + y.b
    · exact Or.inl ⟨by omega, hsb⟩
    · right; left; refine ⟨by omega, by omega, ?_⟩
      have ha_le : y.a * y.a ≤ (x.a + y.a) * (x.a + y.a) := by
        have : 0 ≤ x.a * (x.a + 2 * y.a) := Int.mul_nonneg hxa (by omega)
        have hid : (x.a + y.a) * (x.a + y.a) = y.a * y.a + x.a * (x.a + 2 * y.a) := by
          rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_comm y.a x.a, Int.two_mul, Int.mul_add]; omega
        omega
      have hb_le : (D : Int) * (x.b + y.b) * (x.b + y.b) ≤ (D : Int) * y.b * y.b := by
        have h1 : (-(x.b + y.b)) * (-(x.b + y.b)) ≤ (-y.b) * (-y.b) := by
          have : 0 ≤ ((-y.b) - (-(x.b + y.b))) * ((-y.b) + (-(x.b + y.b))) :=
            Int.mul_nonneg (by omega) (by omega)
          have hid : ((-y.b) - (-(x.b + y.b))) * ((-y.b) + (-(x.b + y.b))) =
              (-y.b) * (-y.b) - (-(x.b + y.b)) * (-(x.b + y.b)) := by
            rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm (-(x.b + y.b)) (-y.b)]; omega
          omega
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.neg_mul, Int.mul_neg, Int.neg_neg] at h1
        rw [Int.mul_assoc, Int.mul_assoc]
        exact Int.mul_le_mul_of_nonneg_left h1 hD
      omega
  · unfold qnonneg; dsimp only [qadd]
    by_cases hsa : 0 ≤ x.a + y.a
    · exact Or.inl ⟨hsa, by omega⟩
    · right; right; refine ⟨by omega, by omega, ?_⟩
      have ha_le : (x.a + y.a) * (x.a + y.a) ≤ y.a * y.a := by
        have h1 : (-(x.a + y.a)) * (-(x.a + y.a)) ≤ (-y.a) * (-y.a) := by
          have : 0 ≤ ((-y.a) - (-(x.a + y.a))) * ((-y.a) + (-(x.a + y.a))) :=
            Int.mul_nonneg (by omega) (by omega)
          have hid : ((-y.a) - (-(x.a + y.a))) * ((-y.a) + (-(x.a + y.a))) =
              (-y.a) * (-y.a) - (-(x.a + y.a)) * (-(x.a + y.a)) := by
            rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm (-(x.a + y.a)) (-y.a)]; omega
          omega
        rwa [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.neg_mul, Int.mul_neg, Int.neg_neg] at h1
      have hb_le : (D : Int) * y.b * y.b ≤ (D : Int) * (x.b + y.b) * (x.b + y.b) := by
        have h1 : y.b * y.b ≤ (x.b + y.b) * (x.b + y.b) := by
          have : 0 ≤ x.b * (x.b + 2 * y.b) := Int.mul_nonneg hxb (by omega)
          have hid : (x.b + y.b) * (x.b + y.b) = y.b * y.b + x.b * (x.b + 2 * y.b) := by
            rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_comm y.b x.b, Int.two_mul, Int.mul_add]; omega
          omega
        rw [Int.mul_assoc, Int.mul_assoc]
        exact Int.mul_le_mul_of_nonneg_left h1 hD
      omega
  · unfold qnonneg; dsimp only [qadd]
    by_cases hsb : 0 ≤ x.b + y.b
    · exact Or.inl ⟨by omega, hsb⟩
    · right; left; refine ⟨by omega, by omega, ?_⟩
      have ha_le : x.a * x.a ≤ (x.a + y.a) * (x.a + y.a) := by
        have : 0 ≤ y.a * (y.a + 2 * x.a) := Int.mul_nonneg hya (by omega)
        have hid : (x.a + y.a) * (x.a + y.a) = x.a * x.a + y.a * (y.a + 2 * x.a) := by
          rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add, Int.two_mul, Int.mul_add, Int.mul_comm y.a x.a]; omega
        omega
      have hb_le : (D : Int) * (x.b + y.b) * (x.b + y.b) ≤ (D : Int) * x.b * x.b := by
        have h1 : (-(x.b + y.b)) * (-(x.b + y.b)) ≤ (-x.b) * (-x.b) := by
          have : 0 ≤ ((-x.b) - (-(x.b + y.b))) * ((-x.b) + (-(x.b + y.b))) :=
            Int.mul_nonneg (by omega) (by omega)
          have hid : ((-x.b) - (-(x.b + y.b))) * ((-x.b) + (-(x.b + y.b))) =
              (-x.b) * (-x.b) - (-(x.b + y.b)) * (-(x.b + y.b)) := by
            rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm (-(x.b + y.b)) (-x.b)]; omega
          omega
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.neg_mul, Int.mul_neg, Int.neg_neg] at h1
        rw [Int.mul_assoc, Int.mul_assoc]
        exact Int.mul_le_mul_of_nonneg_left h1 hD
      omega
  · unfold qnonneg; dsimp only [qadd]
    right; left; refine ⟨by omega, by omega, ?_⟩
    have h1 : (D : Int) * (-x.b) * (-x.b) ≤ x.a * x.a := by rwa [int_mul_neg_sq]
    have h2 : (D : Int) * (-y.b) * (-y.b) ≤ y.a * y.a := by rwa [int_mul_neg_sq]
    have hc := hcomb_ge x.a y.a (-x.b) (-y.b) hxa hya (by omega) (by omega) h1 h2
    have hneg : (-x.b) + (-y.b) = -(x.b + y.b) := by omega
    rw [hneg, int_mul_neg_sq] at hc; exact hc
  · exact hopp x.a x.b y.a y.b hxa hxb hxsq hya hyb hysq
  · unfold qnonneg; dsimp only [qadd]
    by_cases hsa : 0 ≤ x.a + y.a
    · exact Or.inl ⟨hsa, by omega⟩
    · right; right; refine ⟨by omega, by omega, ?_⟩
      have ha_le : (x.a + y.a) * (x.a + y.a) ≤ x.a * x.a := by
        have h1 : (-(x.a + y.a)) * (-(x.a + y.a)) ≤ (-x.a) * (-x.a) := by
          have : 0 ≤ ((-x.a) - (-(x.a + y.a))) * ((-x.a) + (-(x.a + y.a))) :=
            Int.mul_nonneg (by omega) (by omega)
          have hid : ((-x.a) - (-(x.a + y.a))) * ((-x.a) + (-(x.a + y.a))) =
              (-x.a) * (-x.a) - (-(x.a + y.a)) * (-(x.a + y.a)) := by
            rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm (-(x.a + y.a)) (-x.a)]; omega
          omega
        rwa [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.neg_mul, Int.mul_neg, Int.neg_neg] at h1
      have hb_le : (D : Int) * x.b * x.b ≤ (D : Int) * (x.b + y.b) * (x.b + y.b) := by
        have h1 : x.b * x.b ≤ (x.b + y.b) * (x.b + y.b) := by
          have : 0 ≤ y.b * (y.b + 2 * x.b) := Int.mul_nonneg hyb (by omega)
          have hid : (x.b + y.b) * (x.b + y.b) = x.b * x.b + y.b * (y.b + 2 * x.b) := by
            rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add, Int.two_mul, Int.mul_add, Int.mul_comm y.b x.b]; omega
          omega
        rw [Int.mul_assoc, Int.mul_assoc]
        exact Int.mul_le_mul_of_nonneg_left h1 hD
      omega
  · rw [qadd_comm]; exact hopp y.a y.b x.a x.b hya hyb hysq hxa hxb hxsq
  · unfold qnonneg; dsimp only [qadd]
    right; right; refine ⟨by omega, by omega, ?_⟩
    have h1 : (-x.a) * (-x.a) ≤ (D : Int) * x.b * x.b := by rwa [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have h2 : (-y.a) * (-y.a) ≤ (D : Int) * y.b * y.b := by rwa [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have hc := hcomb_le (-x.a) (-y.a) x.b y.b (by omega) (by omega) hxb hyb h1 h2
    have hneg : (-x.a) + (-y.a) = -(x.a + y.a) := by omega
    rw [hneg, Int.neg_mul, Int.mul_neg, Int.neg_neg] at hc; exact hc

theorem qnonneg_mul (D : Nat) (x y : QuadInt D) (hx : qnonneg D x) (hy : qnonneg D y) :
    qnonneg D (qmul x y) := by
  have hD : 0 ≤ (D : Int) := Int.natCast_nonneg D
  -- Write qmul x y = (x.a * y.a + D x.b y.b, x.a y.b + x.b y.a) and check signs cleanly!
  -- Actually use: norm(x * y) = norm(x) * norm(y)!
  have hnorm : (x.a * y.a + (D : Int) * x.b * y.b) * (x.a * y.a + (D : Int) * x.b * y.b) -
      (D : Int) * (x.a * y.b + x.b * y.a) * (x.a * y.b + x.b * y.a) =
      (x.a * x.a - (D : Int) * x.b * x.b) * (y.a * y.a - (D : Int) * y.b * y.b) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add (D : Int), Int.add_mul, Int.mul_add, Int.mul_add,
        Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have e1 : (x.a * y.a) * (x.a * y.a) = (x.a * x.a) * (y.a * y.a) := by
      simp only [Int.mul_assoc]; congr 1; rw [int_mlc y.a x.a]
    have e2 : ((D : Int) * x.b * y.b) * ((D : Int) * x.b * y.b) =
        ((D : Int) * x.b * x.b) * ((D : Int) * y.b * y.b) := by
      simp only [Int.mul_assoc]; congr 2
      rw [int_mlc y.b (D : Int), int_mlc x.b (D : Int)]; congr 1; rw [int_mlc y.b x.b]
    have e3 : (D : Int) * (x.a * y.b) * (x.a * y.b) = (x.a * x.a) * ((D : Int) * y.b * y.b) := by
      simp only [Int.mul_assoc]; rw [int_mlc (D : Int) x.a]; congr 1
      rw [int_mlc y.b x.a, int_mlc (D : Int) x.a]
    have e4 : (D : Int) * (x.b * y.a) * (x.b * y.a) = ((D : Int) * x.b * x.b) * (y.a * y.a) := by
      simp only [Int.mul_assoc]; congr 2; rw [int_mlc y.a x.b]
    have e5 : (x.a * y.a) * ((D : Int) * x.b * y.b) = (D : Int) * (x.a * y.b) * (x.b * y.a) := by
      simp only [Int.mul_assoc]
      rw [int_mlc y.a (D : Int), int_mlc x.a (D : Int)]; congr 2
      rw [int_mlc y.a x.b, Int.mul_comm y.a y.b, int_mlc x.b y.b]
    have e6' : ((D : Int) * x.b * y.b) * (x.a * y.a) = (x.a * y.a) * ((D : Int) * x.b * y.b) :=
      Int.mul_comm ..
    have e7 : (D : Int) * (x.b * y.a) * (x.a * y.b) = (D : Int) * (x.a * y.b) * (x.b * y.a) := by
      rw [Int.mul_assoc, Int.mul_comm (x.b * y.a) (x.a * y.b), ← Int.mul_assoc]
    rw [e1, e2, e3, e4, e6', e7, e5]; omega
  have hmul_natA : ∀ (c : Int) (z : QuadInt D), 0 ≤ c → qnonneg D z → qnonneg D (qmul ⟨c, 0⟩ z) := by
    intro c z hc hz
    have hsimp : qmul ⟨c, 0⟩ z = ⟨c * z.a, c * z.b⟩ := by
      apply qext <;> simp [qmul]
    rw [hsimp]
    rcases hz with ⟨za, zb⟩ | ⟨za, zb, zsq⟩ | ⟨za, zb, zsq⟩
    · exact Or.inl ⟨Int.mul_nonneg hc za, Int.mul_nonneg hc zb⟩
    · by_cases hc0 : c = 0
      · subst hc0; simp only [Int.zero_mul]; exact qnonneg_zero D
      · right; left; refine ⟨Int.mul_nonneg hc za, Int.mul_neg_of_pos_of_neg (by omega) zb, ?_⟩
        have hL : (D : Int) * (c * z.b) * (c * z.b) = (c * c) * ((D : Int) * z.b * z.b) := by
          simp only [Int.mul_assoc]
          rw [int_mlc (D : Int) c]; congr 1
          rw [int_mlc z.b c, int_mlc (D : Int) c]
        have hR : (c * z.a) * (c * z.a) = (c * c) * (z.a * z.a) := by
          simp only [Int.mul_assoc]; congr 1; rw [int_mlc z.a c]
        rw [hL, hR]; exact Int.mul_le_mul_of_nonneg_left zsq (int_sq_nonneg c)
    · by_cases hc0 : c = 0
      · subst hc0; simp only [Int.zero_mul]; exact qnonneg_zero D
      · right; right; refine ⟨Int.mul_neg_of_pos_of_neg (by omega) za, Int.mul_nonneg hc zb, ?_⟩
        have hL : (c * z.a) * (c * z.a) = (c * c) * (z.a * z.a) := by
          simp only [Int.mul_assoc]; congr 1; rw [int_mlc z.a c]
        have hR : (D : Int) * (c * z.b) * (c * z.b) = (c * c) * ((D : Int) * z.b * z.b) := by
          simp only [Int.mul_assoc]
          rw [int_mlc (D : Int) c]; congr 1
          rw [int_mlc z.b c, int_mlc (D : Int) c]
        rw [hL, hR]; exact Int.mul_le_mul_of_nonneg_left zsq (int_sq_nonneg c)
  have hmul_natB : ∀ (c : Int) (z : QuadInt D), 0 ≤ c → qnonneg D z → qnonneg D (qmul ⟨0, c⟩ z) := by
    intro c z hc hz
    have hsimp : qmul ⟨0, c⟩ z = ⟨(D : Int) * c * z.b, c * z.a⟩ := by
      apply qext <;> simp [qmul]
    rw [hsimp]
    rcases hz with ⟨za, zb⟩ | ⟨za, zb, zsq⟩ | ⟨za, zb, zsq⟩
    · exact Or.inl ⟨Int.mul_nonneg (Int.mul_nonneg hD hc) zb, Int.mul_nonneg hc za⟩
    · by_cases hc0 : c = 0
      · subst hc0; simp only [Int.mul_zero, Int.zero_mul]; exact qnonneg_zero D
      · by_cases hD0 : (D : Int) = 0
        · rw [hD0, Int.zero_mul, Int.zero_mul]; unfold qnonneg; dsimp only; exact Or.inl ⟨Int.le_refl 0, Int.mul_nonneg hc za⟩
        · right; right
          refine ⟨Int.mul_neg_of_pos_of_neg (Int.mul_pos (by omega) (by omega)) zb,
                  Int.mul_nonneg hc za, ?_⟩
          have hL : ((D : Int) * c * z.b) * ((D : Int) * c * z.b) =
              ((D : Int) * (c * c)) * ((D : Int) * z.b * z.b) := by
            simp only [Int.mul_assoc]; congr 2
            rw [int_mlc z.b (D : Int), int_mlc c (D : Int)]; congr 1; rw [int_mlc z.b c]
          have hR : (D : Int) * (c * z.a) * (c * z.a) = ((D : Int) * (c * c)) * (z.a * z.a) := by
            simp only [Int.mul_assoc]; congr 2; rw [int_mlc z.a c]
          rw [hL, hR]
          exact Int.mul_le_mul_of_nonneg_left zsq (Int.mul_nonneg hD (int_sq_nonneg c))
    · by_cases hc0 : c = 0
      · subst hc0; simp only [Int.mul_zero, Int.zero_mul]; exact qnonneg_zero D
      · right; left
        refine ⟨Int.mul_nonneg (Int.mul_nonneg hD hc) zb,
                Int.mul_neg_of_pos_of_neg (by omega) za, ?_⟩
        have hL : (D : Int) * (c * z.a) * (c * z.a) = ((D : Int) * (c * c)) * (z.a * z.a) := by
          simp only [Int.mul_assoc]; congr 2; rw [int_mlc z.a c]
        have hR : ((D : Int) * c * z.b) * ((D : Int) * c * z.b) =
            ((D : Int) * (c * c)) * ((D : Int) * z.b * z.b) := by
          simp only [Int.mul_assoc]; congr 2
          rw [int_mlc z.b (D : Int), int_mlc c (D : Int)]; congr 1; rw [int_mlc z.b c]
        rw [hL, hR]
        exact Int.mul_le_mul_of_nonneg_left zsq (Int.mul_nonneg hD (int_sq_nonneg c))
  -- Dispatch the 9 cases (cases 1..5 use hmul_natA/B, leaving ONLY the 4 mixed-sign cases using hnorm!)
  rcases hx with ⟨hxa, hxb⟩ | ⟨hxa, hxb, hxsq⟩ | ⟨hxa, hxb, hxsq⟩
  · have hdecomp : x = qadd ⟨x.a, 0⟩ ⟨0, x.b⟩ := qext (by simp [qadd]) (by simp [qadd])
    rw [hdecomp, qadd_mul]
    exact qnonneg_add D _ _ (hmul_natA x.a y hxa hy) (hmul_natB x.b y hxb hy)
  · rcases hy with ⟨hya, hyb⟩ | ⟨hya, hyb, hysq⟩ | ⟨hya, hyb, hysq⟩
    · rw [qmul_comm]
      have hdecomp : y = qadd ⟨y.a, 0⟩ ⟨0, y.b⟩ := qext (by simp [qadd]) (by simp [qadd])
      rw [hdecomp, qadd_mul]
      exact qnonneg_add D _ _ (hmul_natA y.a x hya (Or.inr (Or.inl ⟨hxa, hxb, hxsq⟩)))
        (hmul_natB y.b x hyb (Or.inr (Or.inl ⟨hxa, hxb, hxsq⟩)))
    · unfold qnonneg; dsimp only [qmul]
      have ha' : 0 ≤ x.a * y.a + (D : Int) * x.b * y.b := by
        have h1 := Int.mul_nonneg hxa hya
        have hxb_yb : (-x.b) * (-y.b) = x.b * y.b := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
        have h2 : 0 ≤ (D : Int) * ((-x.b) * (-y.b)) := Int.mul_nonneg hD (Int.mul_nonneg (by omega) (by omega))
        rw [hxb_yb, ← Int.mul_assoc] at h2; omega
      have hprod_nn : 0 ≤ (x.a * x.a - (D : Int) * x.b * x.b) * (y.a * y.a - (D : Int) * y.b * y.b) :=
        Int.mul_nonneg (by omega) (by omega)
      by_cases hb' : 0 ≤ x.a * y.b + x.b * y.a
      · exact Or.inl ⟨ha', hb'⟩
      · right; left; exact ⟨ha', by omega, by omega⟩
    · unfold qnonneg; dsimp only [qmul]
      have hb' : 0 ≤ x.a * y.b + x.b * y.a := by
        have h1 := Int.mul_nonneg hxa hyb
        have h2 : 0 ≤ (-x.b) * (-y.a) := Int.mul_nonneg (by omega) (by omega)
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at h2; omega
      have hprod_np : (x.a * x.a - (D : Int) * x.b * x.b) * (y.a * y.a - (D : Int) * y.b * y.b) ≤ 0 := by
        have := Int.mul_nonneg (by omega : 0 ≤ x.a * x.a - (D : Int) * x.b * x.b)
                               (by omega : 0 ≤ (D : Int) * y.b * y.b - y.a * y.a)
        rw [Int.mul_sub] at this; rw [Int.mul_sub]; omega
      by_cases ha' : 0 ≤ x.a * y.a + (D : Int) * x.b * y.b
      · exact Or.inl ⟨ha', hb'⟩
      · right; right; exact ⟨by omega, hb', by omega⟩
  · rcases hy with ⟨hya, hyb⟩ | ⟨hya, hyb, hysq⟩ | ⟨hya, hyb, hysq⟩
    · rw [qmul_comm]
      have hdecomp : y = qadd ⟨y.a, 0⟩ ⟨0, y.b⟩ := qext (by simp [qadd]) (by simp [qadd])
      rw [hdecomp, qadd_mul]
      exact qnonneg_add D _ _ (hmul_natA y.a x hya (Or.inr (Or.inr ⟨hxa, hxb, hxsq⟩)))
        (hmul_natB y.b x hyb (Or.inr (Or.inr ⟨hxa, hxb, hxsq⟩)))
    · unfold qnonneg; dsimp only [qmul]
      have hb' : 0 ≤ x.a * y.b + x.b * y.a := by
        have h1 : 0 ≤ (-x.a) * (-y.b) := Int.mul_nonneg (by omega) (by omega)
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at h1
        have h2 := Int.mul_nonneg hxb hya; omega
      have hprod_np : (x.a * x.a - (D : Int) * x.b * x.b) * (y.a * y.a - (D : Int) * y.b * y.b) ≤ 0 := by
        have := Int.mul_nonneg (by omega : 0 ≤ (D : Int) * x.b * x.b - x.a * x.a)
                               (by omega : 0 ≤ y.a * y.a - (D : Int) * y.b * y.b)
        rw [Int.sub_mul] at this; rw [Int.sub_mul]; omega
      by_cases ha' : 0 ≤ x.a * y.a + (D : Int) * x.b * y.b
      · exact Or.inl ⟨ha', hb'⟩
      · right; right; exact ⟨by omega, hb', by omega⟩
    · unfold qnonneg; dsimp only [qmul]
      have ha' : 0 ≤ x.a * y.a + (D : Int) * x.b * y.b := by
        have h1 : 0 ≤ (-x.a) * (-y.a) := Int.mul_nonneg (by omega) (by omega)
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at h1
        have h2 := Int.mul_nonneg (Int.mul_nonneg hD hxb) hyb; omega
      have hprod_nn : 0 ≤ (x.a * x.a - (D : Int) * x.b * x.b) * (y.a * y.a - (D : Int) * y.b * y.b) := by
        have := Int.mul_nonneg (by omega : 0 ≤ (D : Int) * x.b * x.b - x.a * x.a)
                               (by omega : 0 ≤ (D : Int) * y.b * y.b - y.a * y.a)
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub] at this
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
      by_cases hb' : 0 ≤ x.a * y.b + x.b * y.a
      · exact Or.inl ⟨ha', hb'⟩
      · right; left; exact ⟨ha', by omega, by omega⟩

theorem qnonneg_sum (D N : Nat) (f : Nat → QuadInt D) (h : ∀ i, i < N → qnonneg D (f i)) :
    qnonneg D (sumQ N f) := by
  induction N with
  | zero => exact qnonneg_zero D
  | succ k ih =>
    simp only [sumQ]
    exact qnonneg_add D _ _ (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h k (Nat.lt_succ_self k))

theorem qnonneg_prod (D N : Nat) (f : Nat → QuadInt D) (h : ∀ i, i < N → qnonneg D (f i)) :
    qnonneg D (prodQ N f) := by
  induction N with
  | zero => unfold prodQ qone qnonneg; dsimp only; exact Or.inl ⟨by omega, by omega⟩
  | succ k ih =>
    simp only [prodQ]
    exact qnonneg_mul D _ _ (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h k (Nat.lt_succ_self k))

-- ============================================================================
-- Section 2: Symbolic Conference Graph SOS Factorization (`∀ k ≥ 1, p = 4k+1`)
-- ============================================================================

/-- Integer adjacency indicator of graph `adj`. -/
def adjInt (adj : Nat → Nat → Bool) (i j : Nat) : Int :=
  if adj i j then 1 else 0

/-- Exact integer Kronecker delta. -/
def deltaInt (i j : Nat) : Int :=
  if i = j then 1 else 0

/-- Integer finite sum `∑_{r < N} f r`. -/
def sumIntC : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumIntC n f + f n

/-- Strongly regular conference graph `(4k+1, 2k, k-1, k)`:
    symmetric, loopless, `2k`-regular, and `A^2 + A - k I = k J`. -/
def IsConferenceGraph (k : Nat) (adj : Nat → Nat → Bool) : Prop :=
  let p := 4 * k + 1
  1 ≤ k ∧
  (∀ i j, i < p → j < p → adj i j = adj j i) ∧
  (∀ i, i < p → adj i i = false) ∧
  (∀ i, i < p → sumIntC p (fun r => adjInt adj i r) = (2 * k : Int)) ∧
  (∀ i j, i < p → j < p →
    sumIntC p (fun r => adjInt adj i r * adjInt adj r j) + adjInt adj i j - (k : Int) * deltaInt i j = (k : Int))

/-- Exact `Z[√p]` projector matrix `R = 2p A + p(1 + √p) I - (p + √p) J` on `Fin p × Fin p`. -/
def confR (k : Nat) (adj : Nat → Nat → Bool) (i j : Nat) : QuadInt (4 * k + 1) :=
  let p : Int := (4 * k + 1 : Int)
  ⟨2 * p * adjInt adj i j + p * deltaInt i j - p, p * deltaInt i j - 1⟩

/-- Scaled Lovász umbrella Gram matrix `8 k p^2 √p · M_{p+1} ∈ Z[√p]^{(p+1)×(p+1)}`
    (index 0 = handle, indices `1..p` = graph vertices `0..p-1`). -/
def confGram (k : Nat) (adj : Nat → Nat → Bool) (u v : Nat) : QuadInt (4 * k + 1) :=
  let p : Int := (4 * k + 1 : Int)
  if u = 0 ∧ v = 0 then ⟨8 * (k : Int) * p * p * p, 0⟩
  else if u = 0 ∨ v = 0 then ⟨0, 8 * (k : Int) * p * p⟩
  else if u = v then ⟨0, 8 * (k : Int) * p * p⟩
  else if adj (u - 1) (v - 1) then ⟨4 * p * p * p, -(4 * p * p)⟩
  else qzero (4 * k + 1)

/-- Handle vector `h = (√p, 1, 1, ..., 1) ∈ Z[√p]^{p+1}`. -/
def confHandle (k : Nat) (u : Nat) : QuadInt (4 * k + 1) :=
  if u = 0 then qsqrt (4 * k + 1) else qone (4 * k + 1)

/-- Augmented `R̃ ∈ Z[√p]^{p × (p+1)}` (`0` on handle column 0, `confR` on vertex columns `1..p`). -/
def confRTilde (k : Nat) (adj : Nat → Nat → Bool) (r u : Nat) : QuadInt (4 * k + 1) :=
  if u = 0 then qzero (4 * k + 1) else confR k adj r (u - 1)

/-- Weight `w_s ∈ Z[√p]` for the `p + 1` SOS terms (`s = 0` handle weight `8 k p^2`, `s = 1..p` weight `√p - 1`). -/
def confWeight (k : Nat) (s : Nat) : QuadInt (4 * k + 1) :=
  let p : Int := (4 * k + 1 : Int)
  if s = 0 then ⟨8 * (k : Int) * p * p, 0⟩ else ⟨-1, 1⟩

/-- Row `s` of the `(p + 1) × (p + 1)` SOS factor matrix `Z`: row `0` = `h`, row `r+1` = `R̃_r`. -/
def confFactor (k : Nat) (adj : Nat → Nat → Bool) (s u : Nat) : QuadInt (4 * k + 1) :=
  if s = 0 then confHandle k u else confRTilde k adj (s - 1) u

theorem confWeight_nonneg (k : Nat) (hk : 1 ≤ k) (s : Nat) : qnonneg (4 * k + 1) (confWeight k s) := by
  unfold confWeight
  by_cases hs : s = 0
  · simp only [hs, ↓reduceIte]
    unfold qnonneg; dsimp only
    exact Or.inl ⟨by
      have hp : 0 ≤ (4 * (k : Int) + 1) := by omega
      have hk0 : 0 ≤ (k : Int) := Int.natCast_nonneg k
      exact Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by omega) hk0) hp) hp, Int.le_refl 0⟩
  · simp only [hs, ↓reduceIte]
    unfold qnonneg; dsimp only
    right; right
    refine ⟨by omega, by omega, by omega⟩

private theorem sumIntC_congr (N : Nat) (f g : Nat → Int) (h : ∀ i, i < N → f i = g i) :
    sumIntC N f = sumIntC N g := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [sumIntC]; rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

private theorem sumIntC_add (N : Nat) (f g : Nat → Int) :
    sumIntC N (fun i => f i + g i) = sumIntC N f + sumIntC N g := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [sumIntC, ih]; omega

private theorem sumIntC_sub (N : Nat) (f g : Nat → Int) :
    sumIntC N (fun i => f i - g i) = sumIntC N f - sumIntC N g := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [sumIntC, ih]; omega

private theorem sumIntC_mul_left (N : Nat) (c : Int) (f : Nat → Int) :
    sumIntC N (fun i => c * f i) = c * sumIntC N f := by
  induction N with
  | zero => simp [sumIntC]
  | succ n ih => simp only [sumIntC, ih, Int.mul_add]

private theorem sumIntC_const (N : Nat) (c : Int) : sumIntC N (fun _ => c) = (N : Int) * c := by
  induction N with
  | zero => simp [sumIntC]
  | succ n ih => simp only [sumIntC, ih, Int.natCast_succ, Int.add_mul, Int.one_mul]

private theorem sumIntC_delta (N j : Nat) (hj : j < N) (f : Nat → Int) :
    sumIntC N (fun r => deltaInt r j * f r) = f j := by
  induction N with
  | zero => omega
  | succ n ih =>
    simp only [sumIntC]
    cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with
    | inl heq =>
      subst heq
      have hz : sumIntC j (fun r => deltaInt r j * f r) = 0 := by
        rw [sumIntC_congr j _ (fun _ => 0) (fun r hr => by
          have hne : r ≠ j := by omega
          simp [deltaInt, hne])]
        rw [sumIntC_const, Int.mul_zero]
      rw [hz, Int.zero_add]; unfold deltaInt; simp only [↓reduceIte, Int.one_mul]
    | inr hlt =>
      have hne : n ≠ j := by omega
      have h0 : deltaInt n j = 0 := by unfold deltaInt; simp [hne]
      rw [h0, Int.zero_mul, Int.add_zero]
      exact ih hlt

private theorem sumQ_proj (D N : Nat) (f : Nat → QuadInt D) :
    sumQ N f = ⟨sumIntC N (fun i => (f i).a), sumIntC N (fun i => (f i).b)⟩ := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [sumQ, sumIntC, ih, qadd]

/-- **Key Symbolic Conference Matrix Identity:**
    For EVERY conference graph `(4k+1, 2k, k-1, k)`, the `p × p` matrix `R = 2p A + p(1+√p) I - (p+√p) J`
    satisfies `∑_{r < p} R_{r, i} * R_{r, j} = (2 p √p) * R_{i, j}` identically in `Z[√p]`! -/
theorem confR_sq_eq (k : Nat) (adj : Nat → Nat → Bool) (hG : IsConferenceGraph k adj)
    (i j : Nat) (hi : i < 4 * k + 1) (hj : j < 4 * k + 1) :
    sumQ (4 * k + 1) (fun r => qmul (confR k adj r i) (confR k adj r j)) =
    qmul ⟨0, 2 * (4 * (k : Int) + 1)⟩ (confR k adj i j) := by
  obtain ⟨_, hsym, _, hreg, hsrg⟩ := hG
  let pN := 4 * k + 1
  let p : Int := 4 * (k : Int) + 1
  have hpcast : ((4 * k + 1 : Nat) : Int) = p := by dsimp only [p]; omega
  rw [sumQ_proj]
  have hSumA_i : sumIntC pN (fun r => adjInt adj r i) = 2 * (k : Int) := by
    rw [sumIntC_congr pN _ (fun r => adjInt adj i r) (fun r hr => by
      unfold adjInt; rw [hsym r i hr hi])]
    exact hreg i hi
  have hSumA_j : sumIntC pN (fun r => adjInt adj r j) = 2 * (k : Int) := by
    rw [sumIntC_congr pN _ (fun r => adjInt adj j r) (fun r hr => by
      unfold adjInt; rw [hsym r j hr hj])]
    exact hreg j hj
  have hSumA2 : sumIntC pN (fun r => adjInt adj r i * adjInt adj r j) =
      (k : Int) + (k : Int) * deltaInt i j - adjInt adj i j := by
    have hcon := sumIntC_congr pN (fun r => adjInt adj r i * adjInt adj r j)
      (fun r => adjInt adj i r * adjInt adj r j) (fun r hr => by
        unfold adjInt; rw [hsym r i hr hi])
    rw [hcon]; have h := hsrg i j hi hj; dsimp only [pN]; omega
  have hSumDi : sumIntC pN (fun r => deltaInt r i) = 1 := by
    have h := sumIntC_delta pN i hi (fun _ => 1)
    simpa [Int.mul_one] using h
  have hSumDj : sumIntC pN (fun r => deltaInt r j) = 1 := by
    have h := sumIntC_delta pN j hj (fun _ => 1)
    simpa [Int.mul_one] using h
  have hSumDiDj : sumIntC pN (fun r => deltaInt r i * deltaInt r j) = deltaInt i j := by
    exact sumIntC_delta pN i hi (fun r => deltaInt r j)
  have hSumADj : sumIntC pN (fun r => adjInt adj r i * deltaInt r j) = adjInt adj i j := by
    have h := sumIntC_delta pN j hj (fun r => adjInt adj r i)
    rw [sumIntC_congr pN _ (fun r => deltaInt r j * adjInt adj r i) (fun r _ => Int.mul_comm ..)]
    rw [h]; unfold adjInt; rw [hsym j i hj hi]
  have hSumDiA : sumIntC pN (fun r => deltaInt r i * adjInt adj r j) = adjInt adj i j :=
    sumIntC_delta pN i hi (fun r => adjInt adj r j)
  have hSum1 : sumIntC pN (fun _ => (1 : Int)) = p := by
    rw [sumIntC_const, Int.mul_one]; exact hpcast
  let Aij := adjInt adj i j
  let Dij := deltaInt i j
  apply qext
  · simp only [qmul, confR, hpcast]
    have hterm : ∀ r, r < pN →
        (2 * p * adjInt adj r i + p * deltaInt r i - p) *
          (2 * p * adjInt adj r j + p * deltaInt r j - p) +
        p * (p * deltaInt r i - 1) * (p * deltaInt r j - 1) =
        (4 * p * p) * (adjInt adj r i * adjInt adj r j) +
        (2 * p * p) * (adjInt adj r i * deltaInt r j) +
        (2 * p * p) * (deltaInt r i * adjInt adj r j) +
        (p * p + p * p * p) * (deltaInt r i * deltaInt r j) -
        (2 * p * p) * adjInt adj r i -
        (2 * p * p) * adjInt adj r j -
        (2 * p * p) * deltaInt r i -
        (2 * p * p) * deltaInt r j +
        (p * p + p) * 1 := by
      intro r _
      let ai := adjInt adj r i; let aj := adjInt adj r j
      let di := deltaInt r i; let dj := deltaInt r j
      change (2 * p * ai + p * di - p) * (2 * p * aj + p * dj - p) +
          p * (p * di - 1) * (p * dj - 1) =
          (4 * p * p) * (ai * aj) + (2 * p * p) * (ai * dj) + (2 * p * p) * (di * aj) +
          (p * p + p * p * p) * (di * dj) - (2 * p * p) * ai - (2 * p * p) * aj -
          (2 * p * p) * di - (2 * p * p) * dj + (p * p + p) * 1
      rw [int_poly3, int_poly2]
      have s1 : 2 * p * ai * (2 * p * aj) = 4 * p * p * (ai * aj) := by
        simp only [Int.mul_assoc]
        rw [int_mlc ai 2, int_mlc p 2, ← Int.mul_assoc 2 2]
        have h4 : (2 : Int) * 2 = 4 := rfl
        rw [h4]; congr 2; rw [int_mlc ai p]
      have s2 : 2 * p * ai * (p * dj) = 2 * p * p * (ai * dj) := by
        simp only [Int.mul_assoc]; congr 2; rw [int_mlc ai p]
      have s3 : 2 * p * ai * p = 2 * p * p * ai := by
        simp only [Int.mul_assoc]; congr 2; rw [Int.mul_comm ai p]
      have s4 : p * di * (2 * p * aj) = 2 * p * p * (di * aj) := by
        simp only [Int.mul_assoc]; rw [int_mlc di 2, int_mlc p 2]; congr 2; rw [int_mlc di p]
      have s5 : p * di * (p * dj) = p * p * (di * dj) := by
        simp only [Int.mul_assoc]; congr 1; rw [int_mlc di p]
      have s6 : p * di * p = p * p * di := by
        simp only [Int.mul_assoc]; congr 1; rw [Int.mul_comm di p]
      have s7 : p * (2 * p * aj) = 2 * p * p * aj := by
        simp only [Int.mul_assoc]; rw [int_mlc p 2]
      have s8 : p * (p * dj) = p * p * dj := by simp only [Int.mul_assoc]
      have s9 : p * (p * di) * (p * dj) = p * p * p * (di * dj) := by
        simp only [Int.mul_assoc]; congr 2; rw [int_mlc di p]
      have s10 : p * (p * di) = p * p * di := by simp only [Int.mul_assoc]
      rw [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
      have hadd1 : (p * p + p * p * p) * (di * dj) = p * p * (di * dj) + p * p * p * (di * dj) :=
        Int.add_mul ..
      have hadd2 : (2 * p * p) * di = p * p * di + p * p * di := by
        rw [Int.two_mul, Int.add_mul, Int.add_mul]
      have hadd3 : (2 * p * p) * dj = p * p * dj + p * p * dj := by
        rw [Int.two_mul, Int.add_mul, Int.add_mul]
      have hadd4 : (p * p + p) * 1 = p * p + p := Int.mul_one _
      rw [hadd1, hadd2, hadd3, hadd4]; omega
    change sumIntC pN (fun r => (2 * p * adjInt adj r i + p * deltaInt r i - p) *
        (2 * p * adjInt adj r j + p * deltaInt r j - p) +
        p * (p * deltaInt r i - 1) * (p * deltaInt r j - 1)) =
      0 * (2 * p * Aij + p * Dij - p) + p * (2 * p) * (p * Dij - 1)
    rw [sumIntC_congr pN _ _ hterm]
    repeat (first | rw [sumIntC_add] | rw [sumIntC_sub])
    repeat rw [sumIntC_mul_left]
    rw [hSumA2, hSumADj, hSumDiA, hSumDiDj, hSumA_i, hSumA_j, hSumDi, hSumDj, hSum1]
    have h4k : 4 * (k : Int) = p - 1 := by dsimp only [p]; omega
    have hRHS : 0 * (2 * p * Aij + p * Dij - p) + p * (2 * p) * (p * Dij - 1) =
        2 * p * p * p * Dij - 2 * p * p := by
      rw [Int.zero_mul, Int.zero_add, Int.mul_sub, Int.mul_one]
      have c1 : p * (2 * p) * (p * Dij) = 2 * p * p * p * Dij := by
        simp only [Int.mul_assoc]; rw [int_mlc p 2]
      have c2 : p * (2 * p) = 2 * p * p := by
        simp only [Int.mul_assoc]; rw [int_mlc p 2]
      rw [c1, c2]
    change (4 * p * p) * ((k : Int) + (k : Int) * Dij - Aij) +
        (2 * p * p) * Aij + (2 * p * p) * Aij + (p * p + p * p * p) * Dij -
        (2 * p * p) * (2 * (k : Int)) - (2 * p * p) * (2 * (k : Int)) -
        (2 * p * p) * 1 - (2 * p * p) * 1 + (p * p + p) * p =
        0 * (2 * p * Aij + p * Dij - p) + p * (2 * p) * (p * Dij - 1)
    rw [hRHS]
    have e1 : 4 * p * p * ((k : Int) + (k : Int) * Dij - Aij) =
        p * p * (p - 1) + p * p * (p - 1) * Dij - 4 * p * p * Aij := by
      rw [Int.mul_sub, Int.mul_add]
      have a1 : 4 * p * p * (k : Int) = p * p * (4 * (k : Int)) := by
        simp only [Int.mul_assoc]; rw [Int.mul_comm 4, Int.mul_assoc, Int.mul_assoc, Int.mul_comm (k : Int) 4]
      have a2 : 4 * p * p * ((k : Int) * Dij) = p * p * (4 * (k : Int)) * Dij := by
        rw [← Int.mul_assoc, a1]
      rw [a1, a2, h4k]
    have e2 : 2 * p * p * (2 * (k : Int)) = p * p * (p - 1) := by
      have : 2 * p * p * (2 * (k : Int)) = p * p * (4 * (k : Int)) := by
        simp only [Int.mul_assoc]
        calc 2 * (p * (p * (2 * (k : Int))))
            = 2 * (2 * (p * (p * (k : Int)))) := by congr 1; rw [int_mlc p 2, int_mlc p 2]
          _ = 4 * (p * (p * (k : Int))) := by rw [← Int.mul_assoc 2 2]; rfl
          _ = p * (p * (4 * (k : Int))) := by rw [int_mlc 4 p, int_mlc 4 p]
      rw [this, h4k]
    rw [e1, e2]
    have hD1 : (p * p + p * p * p) * Dij = p * p * Dij + p * p * p * Dij := Int.add_mul ..
    have hD2 : p * p * (p - 1) * Dij = p * p * p * Dij - p * p * Dij := by
      rw [Int.mul_sub, Int.mul_one, Int.sub_mul]
    have hP1 : p * p * (p - 1) = p * p * p - p * p := by rw [Int.mul_sub, Int.mul_one]
    have hP2 : (p * p + p) * p = p * p * p + p * p := by rw [Int.add_mul]
    have hA1 : 4 * p * p * Aij = 2 * p * p * Aij + 2 * p * p * Aij := by
      have h42 : (4 : Int) = 2 + 2 := rfl
      rw [h42, Int.add_mul, Int.add_mul, Int.add_mul]
    have h2p2 : 2 * p * p = p * p + p * p := by rw [Int.two_mul, Int.add_mul]
    have h2p3D : 2 * p * p * p * Dij = p * p * p * Dij + p * p * p * Dij := by
      rw [Int.two_mul, Int.add_mul, Int.add_mul, Int.add_mul]
    rw [hD1, hD2, hP1, hP2, hA1, h2p3D, h2p2, Int.mul_one]; omega
  · simp only [qmul, confR]
    have hterm : ∀ r, r < pN →
        (2 * p * adjInt adj r i + p * deltaInt r i - p) * (p * deltaInt r j - 1) +
        (p * deltaInt r i - 1) * (2 * p * adjInt adj r j + p * deltaInt r j - p) =
        (2 * p * p) * (adjInt adj r i * deltaInt r j) +
        (2 * p * p) * (deltaInt r i * adjInt adj r j) +
        (2 * p * p) * (deltaInt r i * deltaInt r j) -
        (2 * p) * adjInt adj r i -
        (2 * p) * adjInt adj r j -
        (p * p + p) * deltaInt r i -
        (p * p + p) * deltaInt r j +
        (2 * p) * 1 := by
      intro r _
      let ai := adjInt adj r i; let aj := adjInt adj r j
      let di := deltaInt r i; let dj := deltaInt r j
      change (2 * p * ai + p * di - p) * (p * dj - 1) + (p * di - 1) * (2 * p * aj + p * dj - p) =
          (2 * p * p) * (ai * dj) + (2 * p * p) * (di * aj) + (2 * p * p) * (di * dj) -
          (2 * p) * ai - (2 * p) * aj - (p * p + p) * di - (p * p + p) * dj + (2 * p) * 1
      rw [int_poly32, int_poly23]
      have s1 : 2 * p * ai * (p * dj) = 2 * p * p * (ai * dj) := by
        simp only [Int.mul_assoc]; congr 2; rw [int_mlc ai p]
      have s2 : p * di * (p * dj) = p * p * (di * dj) := by
        simp only [Int.mul_assoc]; congr 1; rw [int_mlc di p]
      have s3 : p * (p * dj) = p * p * dj := by simp only [Int.mul_assoc]
      have s4 : p * di * (2 * p * aj) = 2 * p * p * (di * aj) := by
        simp only [Int.mul_assoc]; rw [int_mlc di 2, int_mlc p 2]; congr 2; rw [int_mlc di p]
      have s5 : p * di * p = p * p * di := by simp only [Int.mul_assoc]; congr 1; rw [Int.mul_comm di p]
      have s6 : (2 * p * p) * (di * dj) = p * p * (di * dj) + p * p * (di * dj) := by
        rw [Int.two_mul, Int.add_mul, Int.add_mul]
      have s7 : (p * p + p) * di = p * p * di + p * di := Int.add_mul ..
      have s8 : (p * p + p) * dj = p * p * dj + p * dj := Int.add_mul ..
      have s9 : (2 * p) * 1 = p + p := by rw [Int.mul_one, Int.two_mul]
      rw [s1, s2, s3, s4, s5, s6, s7, s8, s9]; omega
    change sumIntC pN (fun r => (2 * p * adjInt adj r i + p * deltaInt r i - p) * (p * deltaInt r j - 1) +
        (p * deltaInt r i - 1) * (2 * p * adjInt adj r j + p * deltaInt r j - p)) =
      0 * (p * Dij - 1) + 2 * p * (2 * p * Aij + p * Dij - p)
    rw [sumIntC_congr pN _ _ hterm]
    repeat (first | rw [sumIntC_add] | rw [sumIntC_sub])
    repeat rw [sumIntC_mul_left]
    rw [hSumADj, hSumDiA, hSumDiDj, hSumA_i, hSumA_j, hSumDi, hSumDj, hSum1]
    have h4k : 4 * (k : Int) = p - 1 := by dsimp only [p]; omega
    have hA : 2 * p * (2 * (k : Int)) = p * (p - 1) := by
      have : 2 * p * (2 * (k : Int)) = p * (4 * (k : Int)) := by
        simp only [Int.mul_assoc]
        calc 2 * (p * (2 * (k : Int))) = 2 * (2 * (p * (k : Int))) := by congr 1; rw [int_mlc p 2]
          _ = 4 * (p * (k : Int)) := by rw [← Int.mul_assoc 2 2]; rfl
          _ = p * (4 * (k : Int)) := int_mlc ..
      rw [this, h4k]
    have hRHS : 0 * (p * Dij - 1) + 2 * p * (2 * p * Aij + p * Dij - p) =
        4 * p * p * Aij + 2 * p * p * Dij - 2 * p * p := by
      rw [Int.zero_mul, Int.zero_add, Int.mul_sub, Int.mul_add]
      have c1 : 2 * p * (2 * p * Aij) = 4 * p * p * Aij := by
        simp only [Int.mul_assoc]; rw [int_mlc p 2, ← Int.mul_assoc 2 2]; rfl
      have c2 : 2 * p * (p * Dij) = 2 * p * p * Dij := by simp only [Int.mul_assoc]
      rw [c1, c2]
    change (2 * p * p) * Aij + (2 * p * p) * Aij + (2 * p * p) * Dij -
        (2 * p) * (2 * (k : Int)) - (2 * p) * (2 * (k : Int)) -
        (p * p + p) * 1 - (p * p + p) * 1 + (2 * p) * p =
        0 * (p * Dij - 1) + 2 * p * (2 * p * Aij + p * Dij - p)
    rw [hRHS, hA]
    have hP : p * (p - 1) = p * p - p := by rw [Int.mul_sub, Int.mul_one]
    have h4A : 4 * p * p * Aij = 2 * p * p * Aij + 2 * p * p * Aij := by
      have h42 : (4 : Int) = 2 + 2 := rfl
      rw [h42, Int.add_mul, Int.add_mul, Int.add_mul]
    have h2p2 : 2 * p * p = p * p + p * p := by rw [Int.two_mul, Int.add_mul]
    rw [hP, h4A, h2p2, Int.mul_one]; omega

/-- **Universal Symbolic 2-Block `Z[√p]` SOS Factorization (`confGram_sos_exact`):**
    For EVERY `k ≥ 1` (`p = 4k + 1`) and EVERY conference graph `(4k+1, 2k, k-1, k)`,
    `confGram k adj u v = ∑_{s < p+1} confWeight k s * confFactor k adj s u * confFactor k adj s v`
    for ALL `u, v < p + 1`! -/
theorem confGram_sos_exact (k : Nat) (adj : Nat → Nat → Bool) (hG : IsConferenceGraph k adj)
    (u v : Nat) (hu : u < 4 * k + 2) (hv : v < 4 * k + 2) :
    confGram k adj u v =
    sumQ (4 * k + 2) (fun s => qmul (confWeight k s) (qmul (confFactor k adj s u) (confFactor k adj s v))) := by
  let pN := 4 * k + 1
  let p : Int := 4 * (k : Int) + 1
  have hpcast : ((4 * k + 1 : Nat) : Int) = p := by dsimp only [p]; omega
  have hsplit : ∀ (N : Nat) (f : Nat → QuadInt pN),
      sumQ (N + 1) f = qadd (f 0) (sumQ N (fun r => f (r + 1))) := by
    intro N f
    induction N with
    | zero => simp [sumQ, qzero_add, qadd_zero]
    | succ n ih =>
      simp only [sumQ] at ih ⊢
      rw [ih, qadd_assoc]
  rw [show 4 * k + 2 = pN + 1 from rfl, hsplit pN]
  have hs0 : qmul (confWeight k 0) (qmul (confFactor k adj 0 u) (confFactor k adj 0 v)) =
      qmul ⟨8 * (k : Int) * p * p, 0⟩ (qmul (confHandle k u) (confHandle k v)) := rfl
  have htail : sumQ pN (fun r => qmul (confWeight k (r + 1))
        (qmul (confFactor k adj (r + 1) u) (confFactor k adj (r + 1) v))) =
      qmul ⟨-1, 1⟩ (sumQ pN (fun r => qmul (confRTilde k adj r u) (confRTilde k adj r v))) := by
    rw [← sumQ_mul_left]
    apply sumQ_congr
    intro r _
    simp only [confWeight, confFactor, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [hs0, htail]
  by_cases hu0 : u = 0
  · subst hu0
    have hrt0 : sumQ pN (fun r => qmul (confRTilde k adj r 0) (confRTilde k adj r v)) = qzero pN := by
      rw [sumQ_congr (g := fun _ => qzero pN) (fun r _ => by simp [confRTilde, qzero_mul]; rfl), sumQ_zero]
    rw [hrt0, qmul_zero, qadd_zero]
    by_cases hv0 : v = 0
    · subst hv0
      apply qext
      · simp [confGram, confHandle, qsqrt, qmul, hpcast]; dsimp only [p]
      · simp [confGram, confHandle, qsqrt, qmul]
    · apply qext <;> simp [confGram, hv0, confHandle, qsqrt, qone, qmul]
      rfl
  · by_cases hv0 : v = 0
    · subst hv0
      have hrt0 : sumQ pN (fun r => qmul (confRTilde k adj r u) (confRTilde k adj r 0)) = qzero pN := by
        rw [sumQ_congr (g := fun _ => qzero pN) (fun r _ => by simp [confRTilde, qmul_zero]; rfl), sumQ_zero]
      rw [hrt0, qmul_zero, qadd_zero]
      apply qext <;> simp [confGram, hu0, confHandle, qsqrt, qone, qmul]
      rfl
    · have hi : u - 1 < pN := by omega
      have hj : v - 1 < pN := by omega
      have hsumR : sumQ pN (fun r => qmul (confRTilde k adj r u) (confRTilde k adj r v)) =
          qmul ⟨0, 2 * p⟩ (confR k adj (u - 1) (v - 1)) := by
        rw [sumQ_congr (g := fun r => qmul (confR k adj r (u - 1)) (confR k adj r (v - 1)))
              (fun r _ => by simp [confRTilde, hu0, hv0])]
        exact confR_sq_eq k adj hG (u - 1) (v - 1) hi hj
      rw [hsumR]
      have hh : qmul (confHandle k u) (confHandle k v) = qone pN := by
        simp [confHandle, hu0, hv0, qone_mul]; rfl
      rw [hh, qmul_one]
      let Aij := adjInt adj (u - 1) (v - 1)
      let Dij := deltaInt (u - 1) (v - 1)
      have hprod : qadd ⟨8 * (k : Int) * p * p, 0⟩
          (qmul ⟨-1, 1⟩ (qmul ⟨0, 2 * p⟩ (confR k adj (u - 1) (v - 1)))) =
          ⟨4 * p * p * p * Aij, 8 * (k : Int) * p * p * Dij - 4 * p * p * Aij⟩ := by
        apply qext <;> simp only [qadd, qmul, confR, hpcast]
        · have h1 : (-1 : Int) * (0 * (2 * p * Aij + p * Dij - p) + p * (2 * p) * (p * Dij - 1)) =
              2 * p * p - 2 * p * p * p * Dij := by
            rw [Int.zero_mul, Int.zero_add, Int.mul_sub, Int.mul_one, Int.neg_mul, Int.one_mul]
            have c : p * (2 * p) * (p * Dij) = 2 * p * p * p * Dij := by
              simp only [Int.mul_assoc]; rw [int_mlc p 2]
            have c2 : p * (2 * p) = 2 * p * p := by
              rw [Int.mul_comm p (2 * p), Int.mul_assoc]
            rw [c, c2]; omega
          have h2 : p * 1 * (0 * (p * Dij - 1) + 2 * p * (2 * p * Aij + p * Dij - p)) =
              4 * p * p * p * Aij + 2 * p * p * p * Dij - 2 * p * p * p := by
            rw [Int.mul_one, Int.zero_mul, Int.zero_add, Int.mul_sub, Int.mul_add, Int.mul_sub, Int.mul_add]
            have c1 : p * (2 * p * (2 * p * Aij)) = 4 * p * p * p * Aij := by
              simp only [Int.mul_assoc]
              rw [int_mlc p 2, int_mlc p 2, int_mlc p 2, ← Int.mul_assoc 2 2]; rfl
            have c2 : p * (2 * p * (p * Dij)) = 2 * p * p * p * Dij := by
              simp only [Int.mul_assoc]; rw [int_mlc p 2]
            have c3 : p * (2 * p * p) = 2 * p * p * p := by
              simp only [Int.mul_assoc]; rw [int_mlc p 2]
            rw [c1, c2, c3]
          have h3 : 8 * (k : Int) * p * p = 2 * p * p * p - 2 * p * p := by
            have h8k : 8 * (k : Int) = 2 * p - 2 := by dsimp only [p]; omega
            calc 8 * (k : Int) * p * p = (2 * p - 2) * p * p := by rw [h8k]
              _ = 2 * p * p * p - 2 * p * p := by rw [Int.sub_mul, Int.sub_mul]
          change 8 * (k : Int) * p * p +
              ((-1 : Int) * (0 * (2 * p * Aij + p * Dij - p) + p * (2 * p) * (p * Dij - 1)) +
               p * 1 * (0 * (p * Dij - 1) + 2 * p * (2 * p * Aij + p * Dij - p))) =
              4 * p * p * p * Aij
          rw [h1, h2, h3]; omega
        · have h1 : (-1 : Int) * (0 * (p * Dij - 1) + 2 * p * (2 * p * Aij + p * Dij - p)) =
              2 * p * p - 4 * p * p * Aij - 2 * p * p * Dij := by
            rw [Int.zero_mul, Int.zero_add, Int.mul_sub, Int.mul_add, Int.neg_mul, Int.one_mul]
            have c1 : 2 * p * (2 * p * Aij) = 4 * p * p * Aij := by
              simp only [Int.mul_assoc]; rw [int_mlc p 2, ← Int.mul_assoc 2 2]; rfl
            have c2 : 2 * p * (p * Dij) = 2 * p * p * Dij := by simp only [Int.mul_assoc]
            rw [c1, c2]; omega
          have h2 : 1 * (0 * (2 * p * Aij + p * Dij - p) + p * (2 * p) * (p * Dij - 1)) =
              2 * p * p * p * Dij - 2 * p * p := by
            rw [Int.one_mul, Int.zero_mul, Int.zero_add, Int.mul_sub, Int.mul_one]
            have c1 : p * (2 * p) * (p * Dij) = 2 * p * p * p * Dij := by
              simp only [Int.mul_assoc]; rw [int_mlc p 2]
            have c2 : p * (2 * p) = 2 * p * p := by
              rw [Int.mul_comm p (2 * p), Int.mul_assoc]
            rw [c1, c2]
          have h3 : 8 * (k : Int) * p * p * Dij = 2 * p * p * p * Dij - 2 * p * p * Dij := by
            have h8k : 8 * (k : Int) = 2 * p - 2 := by dsimp only [p]; omega
            calc 8 * (k : Int) * p * p * Dij = (2 * p - 2) * p * p * Dij := by rw [h8k]
              _ = 2 * p * p * p * Dij - 2 * p * p * Dij := by rw [Int.sub_mul, Int.sub_mul, Int.sub_mul]
          change 0 + ((-1 : Int) * (0 * (p * Dij - 1) + 2 * p * (2 * p * Aij + p * Dij - p)) +
              1 * (0 * (2 * p * Aij + p * Dij - p) + p * (2 * p) * (p * Dij - 1))) =
              8 * (k : Int) * p * p * Dij - 4 * p * p * Aij
          rw [h1, h2, h3]; omega
      rw [hprod]
      -- Now match against `confGram k adj u v` by splitting on `u = v` and `adj (u-1) (v-1)`!
      unfold confGram
      simp only [hu0, hv0, and_false, or_false, ↓reduceIte]
      by_cases huv : u = v
      · subst huv
        have hloopless : adj (u - 1) (u - 1) = false := hG.2.2.1 (u - 1) hi
        have hA0 : Aij = 0 := by dsimp only [Aij, adjInt]; rw [hloopless]; rfl
        have hD1 : Dij = 1 := by dsimp only [Dij, deltaInt]; simp
        simp only [↓reduceIte, hA0, hD1, Int.mul_zero, Int.mul_one, Int.sub_zero]; rfl
      · have hne1 : u - 1 ≠ v - 1 := by omega
        have hD0 : Dij = 0 := by dsimp only [Dij, deltaInt]; simp [hne1]
        simp only [huv, ↓reduceIte, hD0, Int.mul_zero, Int.zero_sub]
        cases hadj : adj (u - 1) (v - 1)
        · have hA0 : Aij = 0 := by dsimp only [Aij, adjInt]; rw [hadj]; rfl
          simp [hA0, qzero]
        · have hA1 : Aij = 1 := by dsimp only [Aij, adjInt]; rw [hadj]; rfl
          simp [hA1, Int.mul_one]; exact ⟨rfl, rfl⟩

-- ============================================================================
-- Section 3: Kronecker Tensor Lift → Universal Upper Bound `s^2 ≤ (4k+1)^t`
-- ============================================================================

/-- Embed `x ∈ [0, p^t)` into `[0, (p+1)^t)` by shifting every base-`p` digit `d ↦ d + 1`. -/
def embedConf (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, x => embedConf p t (x / p) * (p + 1) + (x % p + 1)

theorem embedConf_lt (p : Nat) (hp : 0 < p) : ∀ (t x : Nat), x < p ^ t → embedConf p t x < (p + 1) ^ t
  | 0, _, _ => by simp [embedConf]
  | t + 1, x, hx => by
    simp only [embedConf, Nat.pow_succ]
    have hq : x / p < p ^ t := Nat.div_lt_of_lt_mul (by rwa [Nat.pow_succ, Nat.mul_comm] at hx)
    have hr : x % p + 1 < p + 1 := Nat.add_lt_add_right (Nat.mod_lt x hp) 1
    have ih := embedConf_lt p hp t (x / p) hq
    calc embedConf p t (x / p) * (p + 1) + (x % p + 1)
        < embedConf p t (x / p) * (p + 1) + (p + 1) := Nat.add_lt_add_left hr _
      _ = (embedConf p t (x / p) + 1) * (p + 1) := (Nat.succ_mul ..).symm
      _ ≤ (p + 1) ^ t * (p + 1) := Nat.mul_le_mul_right (p + 1) ih

theorem embedConf_digit (p : Nat) (hp : 0 < p) :
    ∀ (t x d : Nat), d < t → digit (p + 1) (embedConf p t x) d = digit p x d + 1
  | 0, _, _, hd => by omega
  | t + 1, x, d, hd => by
    have hp1 : 0 < p + 1 := Nat.zero_lt_succ p
    cases d with
    | zero =>
      simp only [digit, Nat.pow_zero, Nat.div_one, embedConf]
      rw [Nat.mul_comm (embedConf p t (x / p)) (p + 1), Nat.mul_add_mod,
          Nat.mod_eq_of_lt (Nat.add_lt_add_right (Nat.mod_lt x hp) 1)]
    | succ d' =>
      simp only [digit, Nat.pow_succ', ← Nat.div_div_eq_div_mul, embedConf]
      rw [Nat.mul_comm (embedConf p t (x / p)) (p + 1), Nat.mul_add_div hp1,
          Nat.div_eq_of_lt (Nat.add_lt_add_right (Nat.mod_lt x hp) 1), Nat.add_zero]
      exact embedConf_digit p hp t (x / p) d' (by omega)

/-- Kronecker product entry of `confGram` at power `t`: `∏_{d < t} confGram (digit (p+1) u d) (digit (p+1) v d)`. -/
def confGramPow (k : Nat) (adj : Nat → Nat → Bool) (t u v : Nat) : QuadInt (4 * k + 1) :=
  prodQ t (fun d => confGram k adj (digit (4 * k + 2) u d) (digit (4 * k + 2) v d))

/-- Kronecker product SOS weight on `s < (p+1)^t`. -/
def confWeightPow (k : Nat) (t s : Nat) : QuadInt (4 * k + 1) :=
  prodQ t (fun d => confWeight k (digit (4 * k + 2) s d))

/-- Kronecker product SOS factor on `s, u < (p+1)^t`. -/
def confFactorPow (k : Nat) (adj : Nat → Nat → Bool) (t s u : Nat) : QuadInt (4 * k + 1) :=
  prodQ t (fun d => confFactor k adj (digit (4 * k + 2) s d) (digit (4 * k + 2) u d))

theorem confGramPow_sos (k : Nat) (adj : Nat → Nat → Bool) (hG : IsConferenceGraph k adj) :
    ∀ (t u v : Nat), u < (4 * k + 2) ^ t → v < (4 * k + 2) ^ t →
      confGramPow k adj t u v =
      sumQ ((4 * k + 2) ^ t) (fun s =>
        qmul (confWeightPow k t s) (qmul (confFactorPow k adj t s u) (confFactorPow k adj t s v)))
  | 0, _, _, _, _ => by
    simp only [confGramPow, confWeightPow, confFactorPow, Nat.pow_zero, prodQ, sumQ, qzero_add, qone_mul]
  | t + 1, u, v, hu, hv => by
    let q := 4 * k + 2
    have hq : 0 < q := by omega
    have hqt : 0 < q ^ t := nat_pos_pow q hq t
    have hu_hi : u / q ^ t < q := Nat.div_lt_of_lt_mul (by rwa [Nat.pow_succ] at hu)
    have hv_hi : v / q ^ t < q := Nat.div_lt_of_lt_mul (by rwa [Nat.pow_succ] at hv)
    have hu_lo : u % q ^ t < q ^ t := Nat.mod_lt u hqt
    have hv_lo : v % q ^ t < q ^ t := Nat.mod_lt v hqt
    have hdig_lo : ∀ (x d : Nat), d < t → digit q (x % q ^ t) d = digit q x d := by
      intro x d hd
      simp only [digit]
      have hdiv : q ^ t = q ^ d * (q * q ^ (t - 1 - d)) := by
        rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
      have hqd : 0 < q ^ d := nat_pos_pow q hq d
      have hx := Nat.div_add_mod x (q ^ t)
      have hmod_div : x / q ^ d = (x / q ^ t) * (q * q ^ (t - 1 - d)) + (x % q ^ t) / q ^ d := by
        calc x / q ^ d = (q ^ t * (x / q ^ t) + x % q ^ t) / q ^ d := by rw [hx]
          _ = (q ^ d * ((x / q ^ t) * (q * q ^ (t - 1 - d))) + x % q ^ t) / q ^ d := by
              rw [hdiv]; congr 2; simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ = (x / q ^ t) * (q * q ^ (t - 1 - d)) + (x % q ^ t) / q ^ d := Nat.mul_add_div hqd _ _
      symm
      rw [hmod_div, Nat.mul_comm (x / q ^ t), Nat.mul_assoc q, Nat.mul_add_mod]
    have hdig_hi : ∀ x : Nat, x < q ^ (t + 1) → digit q x t = x / q ^ t := by
      intro x hx
      simp only [digit]
      exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rwa [Nat.pow_succ] at hx))
    have hstepG : confGramPow k adj (t + 1) u v =
        qmul (confGramPow k adj t (u % q ^ t) (v % q ^ t)) (confGram k adj (u / q ^ t) (v / q ^ t)) := by
      unfold confGramPow
      change prodQ (t + 1) (fun d => confGram k adj (digit q u d) (digit q v d)) = _
      simp only [prodQ, hdig_hi u hu, hdig_hi v hv]
      congr 1
      have hcon : ∀ d, d < t →
          confGram k adj (digit q u d) (digit q v d) =
          confGram k adj (digit q (u % q ^ t) d) (digit q (v % q ^ t) d) := by
        intro d hd; rw [hdig_lo u d hd, hdig_lo v d hd]
      have hp : ∀ (m : Nat) (f g : Nat → QuadInt (4 * k + 1)),
          (∀ d, d < m → f d = g d) → prodQ m f = prodQ m g := by
        intro m f g h
        induction m with
        | zero => rfl
        | succ m' ihm => simp only [prodQ]; rw [ihm (fun d hd => h d (Nat.lt_succ_of_lt hd)), h m' (Nat.lt_succ_self m')]
      exact hp t _ _ hcon
    rw [hstepG, confGramPow_sos k adj hG t (u % q ^ t) (v % q ^ t) hu_lo hv_lo,
        confGram_sos_exact k adj hG (u / q ^ t) (v / q ^ t) hu_hi hv_hi]
    rw [Nat.pow_succ, Nat.mul_comm (q ^ t) q, qmul_comm, ← sumQ_mul_factor q (q ^ t)]
    apply sumQ_congr
    intro s hs
    have hs_hi : s / q ^ t < q := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hs)
    have hsd_hi : digit q s t = s / q ^ t := by
      simp only [digit]; exact Nat.mod_eq_of_lt hs_hi
    have hprod_eq : ∀ (f : Nat → QuadInt (4 * k + 1)),
        prodQ t (fun d => f (digit q (s % q ^ t) d)) = prodQ t (fun d => f (digit q s d)) := by
      intro f
      have hp : ∀ (m : Nat) (g1 g2 : Nat → QuadInt (4 * k + 1)),
          (∀ d, d < m → g1 d = g2 d) → prodQ m g1 = prodQ m g2 := by
        intro m g1 g2 h
        induction m with
        | zero => rfl
        | succ m' ihm => simp only [prodQ]; rw [ihm (fun d hd => h d (Nat.lt_succ_of_lt hd)), h m' (Nat.lt_succ_self m')]
      exact hp t _ _ (fun d hd => by rw [hdig_lo s d hd])
    have hwf : confWeightPow k (t + 1) s =
        qmul (confWeightPow k t (s % q ^ t)) (confWeight k (s / q ^ t)) := by
      unfold confWeightPow
      change prodQ (t + 1) (fun d => confWeight k (digit q s d)) = _
      simp only [prodQ, hsd_hi]; rw [hprod_eq]
    have hfu : confFactorPow k adj (t + 1) s u =
        qmul (confFactorPow k adj t (s % q ^ t) (u % q ^ t)) (confFactor k adj (s / q ^ t) (u / q ^ t)) := by
      unfold confFactorPow
      change prodQ (t + 1) (fun d => confFactor k adj (digit q s d) (digit q u d)) = _
      simp only [prodQ, hsd_hi, hdig_hi u hu]
      congr 1
      have hp : ∀ (m : Nat) (g1 g2 : Nat → QuadInt (4 * k + 1)),
          (∀ d, d < m → g1 d = g2 d) → prodQ m g1 = prodQ m g2 := by
        intro m g1 g2 h
        induction m with
        | zero => rfl
        | succ m' ihm => simp only [prodQ]; rw [ihm (fun d hd => h d (Nat.lt_succ_of_lt hd)), h m' (Nat.lt_succ_self m')]
      exact hp t _ _ (fun d hd => by rw [hdig_lo s d hd, hdig_lo u d hd])
    have hfv : confFactorPow k adj (t + 1) s v =
        qmul (confFactorPow k adj t (s % q ^ t) (v % q ^ t)) (confFactor k adj (s / q ^ t) (v / q ^ t)) := by
      unfold confFactorPow
      change prodQ (t + 1) (fun d => confFactor k adj (digit q s d) (digit q v d)) = _
      simp only [prodQ, hsd_hi, hdig_hi v hv]
      congr 1
      have hp : ∀ (m : Nat) (g1 g2 : Nat → QuadInt (4 * k + 1)),
          (∀ d, d < m → g1 d = g2 d) → prodQ m g1 = prodQ m g2 := by
        intro m g1 g2 h
        induction m with
        | zero => rfl
        | succ m' ihm => simp only [prodQ]; rw [ihm (fun d hd => h d (Nat.lt_succ_of_lt hd)), h m' (Nat.lt_succ_self m')]
      exact hp t _ _ (fun d hd => by rw [hdig_lo s d hd, hdig_lo v d hd])
    rw [hwf, hfu, hfv]
    let a1 := confWeight k (s / q ^ t)
    let b1 := confFactor k adj (s / q ^ t) (u / q ^ t)
    let c1 := confFactor k adj (s / q ^ t) (v / q ^ t)
    let a2 := confWeightPow k t (s % q ^ t)
    let b2 := confFactorPow k adj t (s % q ^ t) (u % q ^ t)
    let c2 := confFactorPow k adj t (s % q ^ t) (v % q ^ t)
    change qmul (qmul a1 (qmul b1 c1)) (qmul a2 (qmul b2 c2)) =
      qmul (qmul a2 a1) (qmul (qmul b2 b1) (qmul c2 c1))
    rw [qmul_comm a2 a1, qmul_comm b2 b1, qmul_comm c2 c1]
    rw [qmul_assoc a1, ← qmul_assoc (qmul b1 c1) a2, qmul_comm (qmul b1 c1) a2,
        qmul_assoc a2 (qmul b1 c1), ← qmul_assoc a1 a2]
    congr 1
    rw [qmul_assoc b1 c1, ← qmul_assoc c1 b2, qmul_comm c1 b2, qmul_assoc b2 c1, ← qmul_assoc b1 b2]

/-- **Universal Conference-Graph Lovász Upper Bound (`lovasz_conference_strong_pow_upper`):**
    For EVERY `k ≥ 1` (`p = 4k + 1`), EVERY conference graph `(4k+1, 2k, k-1, k)`, EVERY `t : Nat`,
    and EVERY independent set `f` of size `m` in `G^{⊠ t}`: **`m * m ≤ (4k + 1) ^ t`** (zero reals!). -/
theorem lovasz_conference_strong_pow_upper (k : Nat) (adj : Nat → Nat → Bool)
    (hG : IsConferenceGraph k adj) (t m : Nat) (f : Nat → Nat)
    (hInd : IsIndepSet ((4 * k + 1) ^ t) (strongPowAdj (4 * k + 1) adj t) m f) :
    m * m ≤ (4 * k + 1) ^ t := by
  let p := 4 * k + 1
  let pI : Int := 4 * (k : Int) + 1
  let C : Int := 8 * (k : Int) * pI * pI
  have hpcast : ((4 * k + 1 : Nat) : Int) = pI := by dsimp only [pI]; omega
  have hk : 1 ≤ k := hG.1
  have hp : 0 < p := by omega
  have hCpos : 0 < C := by
    dsimp only [C, pI]
    have h1 : (0 : Int) < 8 * (k : Int) := by omega
    have h2 : (0 : Int) < 4 * (k : Int) + 1 := by omega
    exact Int.mul_pos (Int.mul_pos h1 h2) h2
  -- Test vector `x = e_0 - ∑_{i < m} e_{embedConf p t (f i)}`!
  have hQ_nonneg : qnonneg p (sumQ ((p + 1) ^ t) (fun s =>
      let lin := qsub (confFactorPow k adj t s 0)
                      (sumQ m (fun i => confFactorPow k adj t s (embedConf p t (f i))))
      qmul (confWeightPow k t s) (qmul lin lin))) := by
    apply qnonneg_sum
    intro s _
    apply qnonneg_mul
    · exact qnonneg_prod p t _ (fun d _ => confWeight_nonneg k hk _)
    · exact qnonneg_sq p _
  -- Expand the quadratic form via `confGramPow_sos`:
  have hQ_eq : sumQ ((p + 1) ^ t) (fun s =>
      let lin := qsub (confFactorPow k adj t s 0)
                      (sumQ m (fun i => confFactorPow k adj t s (embedConf p t (f i))))
      qmul (confWeightPow k t s) (qmul lin lin)) =
      qadd (qsub (confGramPow k adj t 0 0)
                 (qadd (sumQ m (fun i => confGramPow k adj t 0 (embedConf p t (f i))))
                       (sumQ m (fun j => confGramPow k adj t (embedConf p t (f j)) 0))))
           (sumQ m (fun i => sumQ m (fun j => confGramPow k adj t (embedConf p t (f i)) (embedConf p t (f j))))) := by
    have hterm : ∀ s : Nat,
        let z0 := confFactorPow k adj t s 0
        let z (i : Nat) := confFactorPow k adj t s (embedConf p t (f i))
        let w := confWeightPow k t s
        qmul w (qmul (qsub z0 (sumQ m z)) (qsub z0 (sumQ m z))) =
        qadd (qsub (qmul w (qmul z0 z0))
                   (qadd (sumQ m (fun i => qmul w (qmul z0 (z i))))
                         (sumQ m (fun j => qmul w (qmul (z j) z0)))))
             (sumQ m (fun i => sumQ m (fun j => qmul w (qmul (z i) (z j))))) := by
      intro s
      let z0 := confFactorPow k adj t s 0
      let z := fun i => confFactorPow k adj t s (embedConf p t (f i))
      let w := confWeightPow k t s
      let S := sumQ m z
      have h1 : sumQ m (fun i => qmul w (qmul z0 (z i))) = qmul w (qmul z0 S) := by
        rw [sumQ_mul_left, sumQ_mul_left]
      have h2 : sumQ m (fun j => qmul w (qmul (z j) z0)) = qmul w (qmul S z0) := by
        rw [sumQ_mul_left, sumQ_mul_right]
      have h3 : sumQ m (fun i => sumQ m (fun j => qmul w (qmul (z i) (z j)))) = qmul w (qmul S S) := by
        rw [sumQ_congr (fun i _ => by rw [sumQ_mul_left, sumQ_mul_left]), sumQ_mul_left, sumQ_mul_right]
      change qmul w (qmul (qsub z0 S) (qsub z0 S)) =
        qadd (qsub (qmul w (qmul z0 z0))
          (qadd (sumQ m (fun i => qmul w (qmul z0 (z i))))
                (sumQ m (fun j => qmul w (qmul (z j) z0)))))
          (sumQ m (fun i => sumQ m (fun j => qmul w (qmul (z i) (z j)))))
      rw [h1, h2, h3]
      simp only [qsub_eq, qadd_mul, qmul_add, qneg_mul, qmul_neg]
      apply qext <;> simp only [qadd, qneg] <;> omega
    rw [sumQ_congr (fun s _ => hterm s)]
    rw [sumQ_add]
    have hsub_sum : ∀ (N : Nat) (A B : Nat → QuadInt p),
        sumQ N (fun s => qsub (A s) (B s)) = qsub (sumQ N A) (sumQ N B) := by
      intro N A B
      induction N with
      | zero => rfl
      | succ n ih =>
        simp only [sumQ, ih]
        apply qext <;> simp only [qadd, qsub] <;> omega
    rw [hsub_sum, sumQ_add]
    rw [sumQ_swap ((p + 1) ^ t) m, sumQ_swap ((p + 1) ^ t) m]
    rw [sumQ_swap ((p + 1) ^ t) m]
    have h0lt : 0 < (p + 1) ^ t := nat_pos_pow (p + 1) (by omega) t
    have hG00 := (confGramPow_sos k adj hG t 0 0 h0lt h0lt).symm
    have hG0i : sumQ m (fun i => sumQ ((p + 1) ^ t) (fun s =>
        qmul (confWeightPow k t s) (qmul (confFactorPow k adj t s 0) (confFactorPow k adj t s (embedConf p t (f i)))))) =
        sumQ m (fun i => confGramPow k adj t 0 (embedConf p t (f i))) :=
      sumQ_congr (fun i hi => (confGramPow_sos k adj hG t 0 (embedConf p t (f i)) h0lt
        (embedConf_lt p hp t (f i) (hInd.1 i hi))).symm)
    have hGj0 : sumQ m (fun j => sumQ ((p + 1) ^ t) (fun s =>
        qmul (confWeightPow k t s) (qmul (confFactorPow k adj t s (embedConf p t (f j))) (confFactorPow k adj t s 0)))) =
        sumQ m (fun j => confGramPow k adj t (embedConf p t (f j)) 0) :=
      sumQ_congr (fun j hj => (confGramPow_sos k adj hG t (embedConf p t (f j)) 0
        (embedConf_lt p hp t (f j) (hInd.1 j hj)) h0lt).symm)
    have hGij : sumQ m (fun i => sumQ ((p + 1) ^ t) (fun s =>
        sumQ m (fun j => qmul (confWeightPow k t s)
          (qmul (confFactorPow k adj t s (embedConf p t (f i))) (confFactorPow k adj t s (embedConf p t (f j))))))) =
        sumQ m (fun i => sumQ m (fun j => confGramPow k adj t (embedConf p t (f i)) (embedConf p t (f j)))) := by
      apply sumQ_congr; intro i hi
      rw [sumQ_swap ((p + 1) ^ t) m]
      apply sumQ_congr; intro j hj
      exact (confGramPow_sos k adj hG t (embedConf p t (f i)) (embedConf p t (f j))
        (embedConf_lt p hp t (f i) (hInd.1 i hi)) (embedConf_lt p hp t (f j) (hInd.1 j hj))).symm
    rw [hG00, hG0i, hGj0, hGij]
  rw [hQ_eq] at hQ_nonneg
  have hG00_val : confGramPow k adj t 0 0 = qpow ⟨C * pI, 0⟩ t := by
    unfold confGramPow
    have hdig0 : ∀ d, digit (4 * k + 2) 0 d = 0 := fun d => by simp [digit]
    have hstep : ∀ n : Nat, prodQ n (fun d => confGram k adj (digit (4 * k + 2) 0 d) (digit (4 * k + 2) 0 d)) =
        qpow ⟨C * pI, 0⟩ n := by
      intro n
      induction n with
      | zero => rfl
      | succ n' ihn =>
        simp only [prodQ, qpow]
        rw [ihn]
        simp only [hdig0, confGram, and_self, ↓reduceIte]
        rfl
    exact hstep t
  have hG_diag : ∀ (i : Nat), i < m →
      confGramPow k adj t 0 (embedConf p t (f i)) = qpow ⟨0, C⟩ t ∧
      confGramPow k adj t (embedConf p t (f i)) 0 = qpow ⟨0, C⟩ t ∧
      confGramPow k adj t (embedConf p t (f i)) (embedConf p t (f i)) = qpow ⟨0, C⟩ t := by
    intro i _
    have hdig0 : ∀ d, digit (4 * k + 2) 0 d = 0 := fun d => by simp [digit]
    have hne0 : ∀ d, d < t → digit (4 * k + 2) (embedConf p t (f i)) d ≠ 0 := by
      intro d hd; change digit (p + 1) (embedConf p t (f i)) d ≠ 0
      rw [embedConf_digit p hp t (f i) d hd]; omega
    have hp_const : ∀ (g : Nat → QuadInt p), (∀ d, d < t → g d = ⟨0, C⟩) → prodQ t g = qpow ⟨0, C⟩ t := by
      intro g hg
      have hgen : ∀ n : Nat, (∀ d, d < n → g d = ⟨0, C⟩) → prodQ n g = qpow ⟨0, C⟩ n := by
        intro n hn
        induction n with
        | zero => rfl
        | succ n' ihn => simp only [prodQ, qpow, ihn (fun d hd => hn d (Nat.lt_succ_of_lt hd)), hn n' (Nat.lt_succ_self n')]
      exact hgen t hg
    refine ⟨hp_const _ (fun d hd => ?_), hp_const _ (fun d hd => ?_), hp_const _ (fun d hd => ?_)⟩
    · rw [hdig0 d]; unfold confGram; simp only [hne0 d hd, and_false, true_or, ↓reduceIte]; rfl
    · rw [hdig0 d]; unfold confGram; simp only [hne0 d hd, false_and, or_true, ↓reduceIte]; rfl
    · unfold confGram; simp only [hne0 d hd, and_self, or_self, ↓reduceIte]; rfl
  have hG_off : ∀ (i j : Nat), i < m → j < m → i ≠ j →
      confGramPow k adj t (embedConf p t (f i)) (embedConf p t (f j)) = qzero p := by
    intro i j hi hj hne
    have hne_f : f i ≠ f j := hInd.2.1 i j hi hj hne
    have hnotadj : strongPowAdj p adj t (f i) (f j) = false := hInd.2.2 i j hi hj hne
    unfold strongPowAdj at hnotadj
    have hbeq : (f i == f j) = false := beq_false_of_ne hne_f
    rw [hbeq] at hnotadj
    simp only [Bool.false_eq_true, ↓reduceIte] at hnotadj
    have hex : ∃ d, d < t ∧ digit p (f i) d ≠ digit p (f j) d ∧
        adj (digit p (f i) d) (digit p (f j) d) = false := by
      have hgo : ∀ n : Nat, strongPowAdjGo p adj (f i) (f j) n = false →
          ∃ d, d < n ∧ digit p (f i) d ≠ digit p (f j) d ∧ adj (digit p (f i) d) (digit p (f j) d) = false := by
        intro n
        induction n with
        | zero => intro h; simp [strongPowAdjGo] at h
        | succ n' ihn =>
          intro h
          simp only [strongPowAdjGo, Bool.and_eq_false_iff, Bool.or_eq_false_iff] at h
          cases h with
          | inl hhere =>
            exact ⟨n', Nat.lt_succ_self n', ne_of_beq_false hhere.1, hhere.2⟩
          | inr hprev =>
            obtain ⟨d, hd, h1, h2⟩ := ihn hprev
            exact ⟨d, Nat.lt_succ_of_lt hd, h1, h2⟩
      exact hgo t hnotadj
    obtain ⟨d, hd, hne_d, hadj_d⟩ := hex
    have hzero_d : confGram k adj (digit (p + 1) (embedConf p t (f i)) d)
        (digit (p + 1) (embedConf p t (f j)) d) = qzero p := by
      rw [embedConf_digit p hp t (f i) d hd, embedConf_digit p hp t (f j) d hd]
      unfold confGram
      simp [hne_d, hadj_d]; rfl
    have hprod0 : ∀ (n : Nat) (g : Nat → QuadInt p), (∃ c, c < n ∧ g c = qzero p) → prodQ n g = qzero p := by
      intro n g
      induction n with
      | zero => rintro ⟨_, h, _⟩; omega
      | succ n' ihn =>
        rintro ⟨c, hc, hzc⟩
        simp only [prodQ]
        cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hc) with
        | inl heq => subst heq; rw [hzc, qmul_zero]
        | inr hlt => rw [ihn ⟨c, hlt, hzc⟩, qzero_mul]
    exact hprod0 t _ ⟨d, hd, hzero_d⟩
  -- Substitute all 4 blocks into `hQ_nonneg`:
  -- Result: `qpow ⟨C * p, 0⟩ t - m * qpow ⟨0, C⟩ t ≥ 0`!
  have hsum_const : ∀ (n : Nat) (v : QuadInt p), sumQ n (fun _ => v) = qmul ⟨(n : Int), 0⟩ v := by
    intro n v
    induction n with
    | zero => apply qext <;> simp [sumQ, qzero, qmul]
    | succ n' ihn =>
      simp only [sumQ, ihn]
      apply qext <;> simp only [qadd, qmul, Int.natCast_succ, Int.add_mul, Int.one_mul] <;> omega
  have hsum0i : sumQ m (fun i => confGramPow k adj t 0 (embedConf p t (f i))) =
      qmul ⟨(m : Int), 0⟩ (qpow ⟨0, C⟩ t) := by
    rw [sumQ_congr (fun i hi => (hG_diag i hi).1), hsum_const]
  have hsumj0 : sumQ m (fun j => confGramPow k adj t (embedConf p t (f j)) 0) =
      qmul ⟨(m : Int), 0⟩ (qpow ⟨0, C⟩ t) := by
    rw [sumQ_congr (fun j hj => (hG_diag j hj).2.1), hsum_const]
  have hsumij : sumQ m (fun i => sumQ m (fun j => confGramPow k adj t (embedConf p t (f i)) (embedConf p t (f j)))) =
      qmul ⟨(m : Int), 0⟩ (qpow ⟨0, C⟩ t) := by
    have hrow : ∀ i, i < m →
        sumQ m (fun j => confGramPow k adj t (embedConf p t (f i)) (embedConf p t (f j))) = qpow ⟨0, C⟩ t := by
      intro i hi
      have hsingle : ∀ (N : Nat) (idx : Nat) (g : Nat → QuadInt p),
          idx < N → (∀ j, j < N → j ≠ idx → g j = qzero p) → sumQ N g = g idx := by
        intro N idx g hidx hz
        induction N with
        | zero => omega
        | succ n' ihn =>
          simp only [sumQ]
          cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hidx) with
          | inl heq =>
            subst heq
            rw [sumQ_congr (fun j hj => hz j (Nat.lt_succ_of_lt hj) (by omega)), sumQ_zero, qzero_add]
          | inr hlt =>
            rw [hz n' (Nat.lt_succ_self n') (by omega), qadd_zero]
            exact ihn hlt (fun j hj hne => hz j (Nat.lt_succ_of_lt hj) hne)
      rw [hsingle m i _ hi (fun j hj hne => hG_off i j hi hj (fun h => hne h.symm))]
      exact (hG_diag i hi).2.2
    rw [sumQ_congr hrow, hsum_const]
  rw [hG00_val, hsum0i, hsumj0, hsumij] at hQ_nonneg
  -- Simplify `G00 - (m*qpow + m*qpow) + m*qpow = qpow ⟨C*p, 0⟩ t - m * qpow ⟨0, C⟩ t`!
  have hsimp : qadd (D := p) (qsub (qpow ⟨C * pI, 0⟩ t) (qadd (qmul ⟨(m : Int), 0⟩ (qpow ⟨0, C⟩ t)) (qmul ⟨(m : Int), 0⟩ (qpow ⟨0, C⟩ t))))
      (qmul ⟨(m : Int), 0⟩ (qpow ⟨0, C⟩ t)) =
      qsub (qpow ⟨C * pI, 0⟩ t) (qmul ⟨(m : Int), 0⟩ (qpow ⟨0, C⟩ t)) := by
    apply qext <;> simp only [qadd, qsub] <;> omega
  rw [hsimp] at hQ_nonneg
  -- Factor `C^t` out of BOTH `qpow ⟨C*p, 0⟩ t` and `qpow ⟨0, C⟩ t`!
  -- Notice `⟨C * p, 0⟩ = ⟨C, 0⟩ * ⟨p, 0⟩` and `⟨0, C⟩ = ⟨C, 0⟩ * ⟨0, 1⟩`!
  have hqpow_mul : ∀ (x y : QuadInt p) (n : Nat), qpow (qmul x y) n = qmul (qpow x n) (qpow y n) := by
    intro x y n
    induction n with
    | zero => exact (qone_mul _).symm
    | succ n' ihn =>
      simp only [qpow, ihn]
      rw [qmul_assoc (qpow x n'), ← qmul_assoc (qpow y n') x, qmul_comm (qpow y n') x,
          qmul_assoc x (qpow y n'), ← qmul_assoc (qpow x n') x]
  have hCpow_int : ∀ (c : Int) (n : Nat), qpow (D := p) ⟨c, 0⟩ n = ⟨c ^ n, 0⟩ := by
    intro c n
    induction n with
    | zero => simp [qpow, qone]
    | succ n' ihn => simp only [qpow, ihn, qmul, Int.pow_succ]; apply qext <;> simp
  have hL_fact : qpow (D := p) ⟨C * pI, 0⟩ t = qmul ⟨C ^ t, 0⟩ (qpow ⟨pI, 0⟩ t) := by
    rw [← hCpow_int C t, ← hqpow_mul]; congr 1; apply qext <;> simp [qmul]
  have hR_fact : qpow (D := p) ⟨0, C⟩ t = qmul ⟨C ^ t, 0⟩ (qpow ⟨0, 1⟩ t) := by
    rw [← hCpow_int C t, ← hqpow_mul]; congr 1; apply qext <;> simp [qmul]
  have hsqrt_pow : ∀ n : Nat,
      (qpow (D := p) ⟨0, 1⟩ (2 * n) = ⟨pI ^ n, 0⟩) ∧
      (qpow (D := p) ⟨0, 1⟩ (2 * n + 1) = ⟨0, pI ^ n⟩) := by
    intro n
    induction n with
    | zero => exact ⟨rfl, by simp [qpow, qone_mul]⟩
    | succ n' ihn =>
      obtain ⟨heven, hodd⟩ := ihn
      have h2s : 2 * (n' + 1) = (2 * n' + 1) + 1 := by omega
      have h2s1 : 2 * (n' + 1) + 1 = 2 * (n' + 1) + 1 := rfl
      have hev' : qpow (D := p) ⟨0, 1⟩ (2 * (n' + 1)) = ⟨pI ^ (n' + 1), 0⟩ := by
        rw [h2s, qpow, hodd]
        apply qext
        · simp only [qmul, Int.zero_mul, Int.zero_add, Int.mul_one, Int.pow_succ]
          dsimp only [p]; rw [hpcast, Int.mul_comm pI]
        · simp [qmul]
      have hodd' : qpow (D := p) ⟨0, 1⟩ (2 * (n' + 1) + 1) = ⟨0, pI ^ (n' + 1)⟩ := by
        rw [h2s1, qpow, hev']
        apply qext <;> simp [qmul]
      exact ⟨hev', hodd'⟩
  have hC_pow_pos : ∀ n : Nat, (0 : Int) < C ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n' ih => rw [Int.pow_succ]; exact Int.mul_pos ih hCpos
  have hCt_pos : (0 : Int) < C ^ t := hC_pow_pos t
  have hpI_pos : (0 : Int) < pI := by dsimp only [pI]; omega
  have hpI_pow_pos : ∀ n : Nat, (0 : Int) < pI ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n' ih => rw [Int.pow_succ]; exact Int.mul_pos ih hpI_pos
  have hp_pow_nat : ∀ n : Nat, pI ^ n = ((p ^ n : Nat) : Int) := by
    intro n
    induction n with
    | zero => rfl
    | succ n' ih => rw [Int.pow_succ, Nat.pow_succ, Int.natCast_mul, ih, ← hpcast]
  have hpt_nat : (pI ^ t) = ((p ^ t : Nat) : Int) := hp_pow_nat t
  rw [hL_fact, hR_fact, hCpow_int pI t] at hQ_nonneg
  have hpar : t = 2 * (t / 2) ∨ t = 2 * (t / 2) + 1 := by omega
  cases hpar with
  | inl hev =>
    let q := t / 2
    have hteq : t = 2 * q := hev
    rw [hteq] at hQ_nonneg hCt_pos hpt_nat ⊢
    rw [(hsqrt_pow q).1] at hQ_nonneg
    have heval : qsub (D := p) (qmul ⟨C ^ (2 * q), 0⟩ ⟨pI ^ (2 * q), 0⟩)
        (qmul ⟨(m : Int), 0⟩ (qmul ⟨C ^ (2 * q), 0⟩ ⟨pI ^ q, 0⟩)) =
        ⟨(C ^ (2 * q) * pI ^ q) * (pI ^ q - (m : Int)), 0⟩ := by
      apply qext <;> simp [qsub, qmul]
      have hpp : pI ^ (2 * q) = pI ^ q * pI ^ q := by rw [← Int.pow_add]; congr 1; omega
      rw [hpp, Int.mul_sub]
      have a1 : C ^ (2 * q) * (pI ^ q * pI ^ q) = C ^ (2 * q) * pI ^ q * pI ^ q := (Int.mul_assoc ..).symm
      have a2 : (m : Int) * (C ^ (2 * q) * pI ^ q) = C ^ (2 * q) * pI ^ q * (m : Int) := Int.mul_comm ..
      rw [a1, a2]
    rw [heval] at hQ_nonneg
    have ha_nn : 0 ≤ (C ^ (2 * q) * pI ^ q) * (pI ^ q - (m : Int)) := by
      rcases hQ_nonneg with ⟨h, _⟩ | ⟨h, _, _⟩ | ⟨hneg, _, h⟩
      · exact h
      · exact h
      · exfalso
        dsimp only at hneg h
        have hpos : 0 < (-((C ^ (2 * q) * pI ^ q) * (pI ^ q - (m : Int)))) *
                        (-((C ^ (2 * q) * pI ^ q) * (pI ^ q - (m : Int)))) :=
          Int.mul_pos (by omega) (by omega)
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at hpos
        simp at h; omega
    have hfac_pos : 0 < C ^ (2 * q) * pI ^ q := Int.mul_pos hCt_pos (hpI_pow_pos q)
    have hm_le : (m : Int) ≤ pI ^ q := by
      by_cases hle : (m : Int) ≤ pI ^ q
      · exact hle
      · have := Int.mul_neg_of_pos_of_neg hfac_pos (by omega : pI ^ q - (m : Int) < 0)
        omega
    have hm_nat : m ≤ p ^ q := by
      rw [hp_pow_nat q] at hm_le; omega
    calc m * m ≤ p ^ q * p ^ q := Nat.mul_le_mul hm_nat hm_nat
      _ = p ^ (2 * q) := by rw [← Nat.pow_add]; congr 1; omega
  | inr hodd =>
    let q := t / 2
    have hteq : t = 2 * q + 1 := hodd
    rw [hteq] at hQ_nonneg hCt_pos hpt_nat ⊢
    rw [(hsqrt_pow q).2] at hQ_nonneg
    have heval : qsub (D := p) (qmul ⟨C ^ (2 * q + 1), 0⟩ ⟨pI ^ (2 * q + 1), 0⟩)
        (qmul ⟨(m : Int), 0⟩ (qmul ⟨C ^ (2 * q + 1), 0⟩ ⟨0, pI ^ q⟩)) =
        ⟨C ^ (2 * q + 1) * pI ^ (2 * q + 1), -((m : Int) * (C ^ (2 * q + 1) * pI ^ q))⟩ := by
      apply qext <;> simp [qsub, qmul]
    rw [heval] at hQ_nonneg
    cases m with
    | zero => exact Nat.zero_le _
    | succ m' =>
      have hnegb : -(((m' + 1 : Nat) : Int) * (C ^ (2 * q + 1) * pI ^ q)) < 0 := by
        have hpos := Int.mul_pos (by omega : (0 : Int) < ((m' + 1 : Nat) : Int))
          (Int.mul_pos hCt_pos (hpI_pow_pos q))
        omega
      have hsq : pI * (-(((m' + 1 : Nat) : Int) * (C ^ (2 * q + 1) * pI ^ q))) *
          (-(((m' + 1 : Nat) : Int) * (C ^ (2 * q + 1) * pI ^ q))) ≤
          (C ^ (2 * q + 1) * pI ^ (2 * q + 1)) * (C ^ (2 * q + 1) * pI ^ (2 * q + 1)) := by
        rcases hQ_nonneg with ⟨_, hb⟩ | ⟨_, _, h⟩ | ⟨_, hb, _⟩
        · dsimp only at hb; omega
        · dsimp only at h; dsimp only [p] at h; rwa [hpcast] at h
        · dsimp only at hb; omega
      let K := C ^ (2 * q + 1) * pI ^ q
      have hKpos : 0 < K := Int.mul_pos hCt_pos (hpI_pow_pos q)
      have hK2p_pos : 0 < (K * K) * pI := Int.mul_pos (Int.mul_pos hKpos hKpos) hpI_pos
      have hL_eq : pI * (-(((m' + 1 : Nat) : Int) * K)) * (-(((m' + 1 : Nat) : Int) * K)) =
          ((K * K) * pI) * (((m' + 1 : Nat) : Int) * ((m' + 1 : Nat) : Int)) := by
        rw [int_mul_neg_sq]
        simp only [Int.mul_assoc]
        calc pI * (((m' + 1 : Nat) : Int) * (K * (((m' + 1 : Nat) : Int) * K)))
            = ((m' + 1 : Nat) : Int) * (pI * (K * (((m' + 1 : Nat) : Int) * K))) := int_mlc ..
          _ = ((m' + 1 : Nat) : Int) * (((m' + 1 : Nat) : Int) * (pI * (K * K))) := by
              congr 1; rw [int_mlc K ((m' + 1 : Nat) : Int), int_mlc pI ((m' + 1 : Nat) : Int)]
          _ = K * (K * (pI * (((m' + 1 : Nat) : Int) * ((m' + 1 : Nat) : Int)))) := by
              rw [← Int.mul_assoc (((m' + 1 : Nat) : Int)), Int.mul_comm _ (pI * (K * K)),
                  Int.mul_comm pI (K * K)]
              simp only [Int.mul_assoc]
      have hR_eq : (C ^ (2 * q + 1) * pI ^ (2 * q + 1)) * (C ^ (2 * q + 1) * pI ^ (2 * q + 1)) =
          ((K * K) * pI) * pI ^ (2 * q + 1) := by
        have hp_split : pI ^ (2 * q + 1) = pI ^ q * pI ^ (q + 1) := by rw [← Int.pow_add]; congr 1; omega
        have hp_split2 : pI ^ (q + 1) * pI ^ (q + 1) = pI * pI ^ (2 * q + 1) := by
          rw [← Int.pow_add, Int.mul_comm pI, ← Int.pow_succ]; congr 1; omega
        have hstep1 : C ^ (2 * q + 1) * pI ^ (2 * q + 1) = K * pI ^ (q + 1) := by
          dsimp only [K]; rw [hp_split, Int.mul_assoc]
        rw [hstep1]
        calc (K * pI ^ (q + 1)) * (K * pI ^ (q + 1))
            = (K * K) * (pI ^ (q + 1) * pI ^ (q + 1)) := by
              simp only [Int.mul_assoc]; congr 1; rw [int_mlc (pI ^ (q + 1)) K]
          _ = (K * K) * (pI * pI ^ (2 * q + 1)) := by rw [hp_split2]
          _ = (K * K * pI) * pI ^ (2 * q + 1) := (Int.mul_assoc ..).symm
      change pI * (-(((m' + 1 : Nat) : Int) * K)) * (-(((m' + 1 : Nat) : Int) * K)) ≤ _ at hsq
      rw [hL_eq, hR_eq] at hsq
      have hle_int : ((m' + 1 : Nat) : Int) * ((m' + 1 : Nat) : Int) ≤ pI ^ (2 * q + 1) := by
        by_cases h : ((m' + 1 : Nat) : Int) * ((m' + 1 : Nat) : Int) ≤ pI ^ (2 * q + 1)
        · exact h
        · have := Int.mul_neg_of_pos_of_neg hK2p_pos
            (by omega : pI ^ (2 * q + 1) - ((m' + 1 : Nat) : Int) * ((m' + 1 : Nat) : Int) < 0)
          rw [Int.mul_sub] at this; omega
      rw [hpt_nat] at hle_int
      have hcast : ((m' + 1 : Nat) : Int) * ((m' + 1 : Nat) : Int) = (((m' + 1) * (m' + 1) : Nat) : Int) :=
        (Int.natCast_mul ..).symm
      rw [hcast] at hle_int
      dsimp only [p] at hle_int
      omega

-- ============================================================================
-- Section 4: Universal Self-Complementary Lower Bound & Paley Graphs P_5, P_13, P_17
-- ============================================================================

/-- Self-complement anti-automorphism `φ` on `(n, adj)`: bijective on `[0, n)` swapping edges/non-edges. -/
def IsSelfCompMap (n : Nat) (adj : Nat → Nat → Bool) (φ : Nat → Nat) : Prop :=
  (∀ x, x < n → φ x < n) ∧
  (∀ x y, x < n → y < n → x ≠ y → φ x ≠ φ y) ∧
  (∀ x y, x < n → y < n → x ≠ y → adj (φ x) (φ y) = !adj x y)

/-- **Universal Lovász Self-Complementary Lower Bound (`self_comp_indep_lift`):**
    For EVERY graph `(n, adj)` (`n ≥ 1`) with a self-complement map `φ`,
    `{(x, φ x) : x < n}` is an `n`-element independent set in `G^{⊠ 2}`, lifting to
    `α(G^{⊠ 2m}) ≥ n ^ m` for EVERY `m : Nat`! -/
theorem self_comp_indep_lift (n : Nat) (adj : Nat → Nat → Bool) (φ : Nat → Nat)
    (hn : 0 < n) (hφ : IsSelfCompMap n adj φ) (m : Nat) :
    ∃ f : Nat → Nat, IsIndepSet (n ^ (2 * m)) (strongPowAdj n adj (2 * m)) (n ^ m) f := by
  let ind2 : Nat → Nat := fun x => x * n + φ x
  have hind2 : IsIndepSet (n ^ 2) (strongPowAdj n adj 2) n ind2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      dsimp only [ind2]
      have hfx := hφ.1 x hx
      rw [Nat.pow_two]
      calc x * n + φ x < x * n + n := Nat.add_lt_add_left hfx _
        _ = (x + 1) * n := (Nat.succ_mul ..).symm
        _ ≤ n * n := Nat.mul_le_mul_right n hx
    · intro x y hx hy hne heq
      dsimp only [ind2] at heq
      have hdiv := congrArg (· / n) heq
      rw [Nat.mul_comm x n, Nat.mul_comm y n, Nat.mul_add_div hn, Nat.mul_add_div hn,
          Nat.div_eq_of_lt (hφ.1 x hx), Nat.div_eq_of_lt (hφ.1 y hy), Nat.add_zero, Nat.add_zero] at hdiv
      exact hne hdiv
    · intro x y hx hy hne
      have hne_ind : ind2 x ≠ ind2 y := by
        intro heq
        have hdiv := congrArg (· / n) heq
        dsimp only [ind2] at hdiv
        rw [Nat.mul_comm x n, Nat.mul_comm y n, Nat.mul_add_div hn, Nat.mul_add_div hn,
            Nat.div_eq_of_lt (hφ.1 x hx), Nat.div_eq_of_lt (hφ.1 y hy), Nat.add_zero, Nat.add_zero] at hdiv
        exact hne hdiv
      unfold strongPowAdj
      rw [beq_false_of_ne hne_ind]
      simp only [Bool.false_eq_true, ↓reduceIte, strongPowAdjGo, digit, Nat.pow_zero, Nat.pow_one, Nat.div_one]
      dsimp only [ind2]
      have h0x : (x * n + φ x) % n = φ x := by
        rw [Nat.mul_comm x n, Nat.mul_add_mod, Nat.mod_eq_of_lt (hφ.1 x hx)]
      have h0y : (y * n + φ y) % n = φ y := by
        rw [Nat.mul_comm y n, Nat.mul_add_mod, Nat.mod_eq_of_lt (hφ.1 y hy)]
      have h1x : (x * n + φ x) / n % n = x := by
        rw [Nat.mul_comm x n, Nat.mul_add_div hn, Nat.div_eq_of_lt (hφ.1 x hx), Nat.add_zero, Nat.mod_eq_of_lt hx]
      have h1y : (y * n + φ y) / n % n = y := by
        rw [Nat.mul_comm y n, Nat.mul_add_div hn, Nat.div_eq_of_lt (hφ.1 y hy), Nat.add_zero, Nat.mod_eq_of_lt hy]
      rw [h0x, h0y, h1x, h1y, beq_false_of_ne hne, beq_false_of_ne (hφ.2.1 x y hx hy hne), hφ.2.2 x y hx hy hne]
      cases adj x y <;> rfl
  exact ⟨liftIndep2 n n ind2 m, indep_lift_even_pow n n adj ind2 hn hn hind2 m⟩

/-- Concrete Paley graph `P_p` adjacency (`p = 4k+1` prime): `i ~ j` iff `i ≠ j` and `(i - j) mod p` is a nonzero square. -/
def isQuadRes (p d : Nat) : Bool :=
  (List.range p).any (fun x => x != 0 && (x * x) % p == d)

def paleyAdj (p i j : Nat) : Bool :=
  if i == j then false else isQuadRes p ((i + p - j % p) % p)

def paley13Adj (i j : Nat) : Bool := paleyAdj 13 i j
def paley17Adj (i j : Nat) : Bool := paleyAdj 17 i j

/-- Fast decidable checker certifying `IsConferenceGraph k adj`. -/
def checkConferenceGraph (k : Nat) (adj : Nat → Nat → Bool) : Bool :=
  let p := 4 * k + 1
  (1 ≤ k) &&
  (List.range p).all (fun i =>
    !adj i i &&
    (sumIntC p (fun r => adjInt adj i r) == (2 * k : Int)) &&
    (List.range p).all (fun j =>
      (adj i j == adj j i) &&
      (sumIntC p (fun r => adjInt adj i r * adjInt adj r j) + adjInt adj i j - (k : Int) * deltaInt i j == (k : Int))))

theorem isConferenceGraph_of_check (k : Nat) (adj : Nat → Nat → Bool)
    (h : checkConferenceGraph k adj = true) : IsConferenceGraph k adj := by
  unfold checkConferenceGraph at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
             Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨hk, hall⟩ := h
  refine ⟨hk, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj; exact (((hall i hi).2 j hj).1)
  · intro i hi; exact (hall i hi).1.1
  · intro i hi; exact (hall i hi).1.2
  · intro i j hi hj; exact (((hall i hi).2 j hj).2)

def checkSelfCompMap (n : Nat) (adj : Nat → Nat → Bool) (φ : Nat → Nat) : Bool :=
  (List.range n).all (fun x =>
    (φ x < n) &&
    (List.range n).all (fun y =>
      (x == y) || ((φ x != φ y) && (adj (φ x) (φ y) == !adj x y))))

theorem isSelfCompMap_of_check (n : Nat) (adj : Nat → Nat → Bool) (φ : Nat → Nat)
    (h : checkSelfCompMap n adj φ = true) : IsSelfCompMap n adj φ := by
  unfold checkSelfCompMap at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
             decide_eq_true_eq, bne_iff_ne, beq_iff_eq] at h
  refine ⟨fun x hx => (h x hx).1, ?_, ?_⟩
  · intro x y hx hy hne
    cases (h x hx).2 y hy with
    | inl heq => exact False.elim (hne heq)
    | inr hok => exact hok.1
  · intro x y hx hy hne
    cases (h x hx).2 y hy with
    | inl heq => exact False.elim (hne heq)
    | inr hok => exact hok.2

theorem paley5_isConference : IsConferenceGraph 1 c5Adj :=
  isConferenceGraph_of_check 1 c5Adj (by decide)

theorem paley13_isConference : IsConferenceGraph 3 paley13Adj :=
  isConferenceGraph_of_check 3 paley13Adj (by decide)

theorem paley17_isConference : IsConferenceGraph 4 paley17Adj :=
  isConferenceGraph_of_check 4 paley17Adj (by decide)

theorem paley13_selfComp : IsSelfCompMap 13 paley13Adj (fun x => (2 * x) % 13) :=
  isSelfCompMap_of_check 13 paley13Adj (fun x => (2 * x) % 13) (by decide)

theorem paley17_selfComp : IsSelfCompMap 17 paley17Adj (fun x => (3 * x) % 17) :=
  isSelfCompMap_of_check 17 paley17Adj (fun x => (3 * x) % 17) (by decide)

/-- **Theorem T3l (Infinite-Family Zero-Reals Symbolic Lovász Shannon Capacity `Θ(G) = √(4k+1)`):**
    1. **Universal Conference-Graph Upper Bound (`∀ k ≥ 1, ∀ G` conference graph `(4k+1, 2k, k-1, k)`):**
       Via our symbolic 2-block `Z[√(4k+1)]` SOS identity (`R^T R = 2p √p R`), EVERY independent set
       of size `m` in `G^{⊠ t}` satisfies **`m * m ≤ (4k + 1)^t`** for ALL `t : Nat` (ZERO real numbers!).
    2. **Universal Self-Complementary Lower Bound (`∀ n ≥ 1, ∀ G ≅ Ḡ`):**
       `α(G^{⊠ 2m}) ≥ n ^ m` for ALL `m : Nat`.
    3. **Exact Infinite-Family Shannon Capacity (`Θ(G) = √(4k+1)`):**
       For EVERY self-complementary conference graph `G` on `p = 4k + 1` vertices,
       `α(G^{⊠ 2m}) = p^m` AND `s^2 ≤ p^t`, concretely instantiated in Lean for **`P_13`** (`Θ(P_13) = √13`)
       and **`P_17`** (`Θ(P_17) = √17`), generalizing `C_5 = P_5` to infinitely many graphs! -/
theorem t3l_infinite_paley_conference_shannon_capacity :
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
        IsIndepSet (17 ^ (2 * m)) (strongPowAdj 17 paley17Adj (2 * m)) (17 ^ m) f)) :=
  ⟨lovasz_conference_strong_pow_upper,
   self_comp_indep_lift,
   ⟨lovasz_conference_strong_pow_upper 3 paley13Adj paley13_isConference,
    self_comp_indep_lift 13 paley13Adj (fun x => (2 * x) % 13) (by decide) paley13_selfComp⟩,
   ⟨lovasz_conference_strong_pow_upper 4 paley17Adj paley17_isConference,
    self_comp_indep_lift 17 paley17Adj (fun x => (3 * x) % 17) (by decide) paley17_selfComp⟩⟩

end
end TriadFrontier.PaleyCapacity
