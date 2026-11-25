module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

/-!
# Algebraic Core for `TriadFrontier` (Zero-Mathlib Lean 4.35.0)

Provides self-contained commutative ring (`CommRing`), field (`SimpleField`),
finite summation (`sumNat`, `sumInt`, `sumR`), binomial coefficients (`chooseNat`),
and polynomial evaluation (`evalPoly`) primitives with zero external dependencies.
-/

namespace TriadFrontier.AlgebraCore

@[expose] public section

/-- Commutative ring with unity (zero-Mathlib). -/
class CommRing (R : Type) extends Add R, Sub R, Mul R, Neg R, Zero R, One R where
  add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, 0 + a = a
  add_neg : ∀ a : R, a + (-a) = 0
  sub_eq : ∀ a b : R, a - b = a + (-b)
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, 1 * a = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c

/-- Field class extending `CommRing` with `0 ≠ 1` and multiplicative inverses. -/
class SimpleField (F : Type) extends CommRing F where
  inv : F → F
  zero_ne_one : (0 : F) ≠ (1 : F)
  mul_inv_cancel : ∀ a : F, a ≠ 0 → a * inv a = 1

/-- Derived commutative ring identities. -/
theorem add_zero {R : Type} [CommRing R] (a : R) : a + 0 = a := by
  rw [CommRing.add_comm, CommRing.zero_add]

theorem mul_one {R : Type} [CommRing R] (a : R) : a * 1 = a := by
  rw [CommRing.mul_comm, CommRing.one_mul]

theorem right_distrib {R : Type} [CommRing R] (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [CommRing.mul_comm, CommRing.left_distrib, CommRing.mul_comm c a, CommRing.mul_comm c b]

theorem neg_add {R : Type} [CommRing R] (a : R) : (-a) + a = 0 := by
  rw [CommRing.add_comm, CommRing.add_neg]

theorem add_left_cancel {R : Type} [CommRing R] {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : (-a) + (a + b) = (-a) + (a + c) := congrArg (fun x => (-a) + x) h
  rw [← CommRing.add_assoc, ← CommRing.add_assoc, neg_add, CommRing.zero_add, CommRing.zero_add] at h1
  exact h1

theorem mul_zero {R : Type} [CommRing R] (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← CommRing.left_distrib, CommRing.zero_add, add_zero]
  exact add_left_cancel h

theorem zero_mul {R : Type} [CommRing R] (a : R) : 0 * a = 0 := by
  rw [CommRing.mul_comm, mul_zero]

theorem neg_eq_of_add_eq_zero {R : Type} [CommRing R] {a b : R} (h : a + b = 0) : b = -a := by
  have h1 : a + b = a + (-a) := by rw [h, CommRing.add_neg]
  exact add_left_cancel h1

theorem mul_neg {R : Type} [CommRing R] (a b : R) : a * (-b) = -(a * b) := by
  apply neg_eq_of_add_eq_zero
  rw [← CommRing.left_distrib, CommRing.add_neg, mul_zero]

theorem neg_mul {R : Type} [CommRing R] (a b : R) : (-a) * b = -(a * b) := by
  rw [CommRing.mul_comm, mul_neg, CommRing.mul_comm]

theorem neg_neg {R : Type} [CommRing R] (a : R) : -(-a) = a := by
  symm; apply neg_eq_of_add_eq_zero; exact neg_add a

theorem neg_zero {R : Type} [CommRing R] : -(0 : R) = 0 := by
  symm; apply neg_eq_of_add_eq_zero; exact CommRing.zero_add 0

theorem neg_add_distrib {R : Type} [CommRing R] (a b : R) : -(a + b) = (-a) + (-b) := by
  symm; apply neg_eq_of_add_eq_zero
  calc (a + b) + ((-a) + (-b))
      = (a + (-a)) + (b + (-b)) := by
        rw [CommRing.add_assoc, ← CommRing.add_assoc b (-a) (-b), CommRing.add_comm b (-a),
            CommRing.add_assoc (-a) b (-b), ← CommRing.add_assoc]
    _ = 0 + 0 := by rw [CommRing.add_neg, CommRing.add_neg]
    _ = 0 := CommRing.zero_add 0

theorem sub_self {R : Type} [CommRing R] (a : R) : a - a = 0 := by
  rw [CommRing.sub_eq, CommRing.add_neg]

theorem eq_of_sub_eq_zero {R : Type} [CommRing R] {a b : R} (h : a - b = 0) : a = b := by
  rw [CommRing.sub_eq] at h
  have h1 : (a + (-b)) + b = 0 + b := congrArg (fun x => x + b) h
  rw [CommRing.add_assoc, neg_add, add_zero, CommRing.zero_add] at h1
  exact h1

theorem field_mul_eq_zero {F : Type} [SimpleField F] {a b : F} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have h1 : (SimpleField.inv a) * (a * b) = (SimpleField.inv a) * 0 := congrArg _ h
    rw [← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv a) a,
        SimpleField.mul_inv_cancel a ha, CommRing.one_mul, mul_zero] at h1
    exact h1

/-- Ring power `a^k`. -/
def rPow {R : Type} [CommRing R] (a : R) : Nat → R
  | 0 => 1
  | k + 1 => rPow a k * a

theorem rPow_zero {R : Type} [CommRing R] (a : R) : rPow a 0 = 1 := rfl
theorem rPow_succ {R : Type} [CommRing R] (a : R) (k : Nat) : rPow a (k + 1) = rPow a k * a := rfl

theorem rPow_add {R : Type} [CommRing R] (a : R) (m n : Nat) :
    rPow a (m + n) = rPow a m * rPow a n := by
  induction n with
  | zero => simp [rPow, mul_one]
  | succ k ih =>
    rw [Nat.add_succ, rPow_succ, rPow_succ, ih, CommRing.mul_assoc]

theorem rPow_mul {R : Type} [CommRing R] (a : R) (m n : Nat) :
    rPow a (m * n) = rPow (rPow a m) n := by
  induction n with
  | zero => simp [rPow]
  | succ k ih =>
    rw [Nat.mul_succ, rPow_add, ih, rPow_succ]

/-- Generic finite ring sum `∑_{i=0}^{n-1} f i`. -/
def sumR {R : Type} [CommRing R] : Nat → (Nat → R) → R
  | 0, _ => 0
  | k + 1, f => sumR k f + f k

theorem sumR_zero_fn {R : Type} [CommRing R] (n : Nat) : sumR n (fun _ => (0 : R)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumR, ih, add_zero]

theorem sumR_congr {R : Type} [CommRing R] {n : Nat} {f g : Nat → R}
    (h : ∀ i, i < n → f i = g i) : sumR n f = sumR n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumR]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem sumR_add {R : Type} [CommRing R] (n : Nat) (f g : Nat → R) :
    sumR n (fun i => f i + g i) = sumR n f + sumR n g := by
  induction n with
  | zero => simp [sumR, add_zero]
  | succ k ih =>
    simp only [sumR, ih]
    rw [CommRing.add_assoc, ← CommRing.add_assoc (sumR k g) (f k) (g k),
        CommRing.add_comm (sumR k g) (f k), CommRing.add_assoc (f k) (sumR k g) (g k),
        ← CommRing.add_assoc]

theorem sumR_neg {R : Type} [CommRing R] (n : Nat) (f : Nat → R) :
    sumR n (fun i => -(f i)) = -(sumR n f) := by
  induction n with
  | zero => simp [sumR, neg_zero]
  | succ k ih => simp only [sumR, ih, neg_add_distrib]

theorem sumR_split {R : Type} [CommRing R] (m n : Nat) (f : Nat → R) :
    sumR (m + n) f = sumR m f + sumR n (fun i => f (m + i)) := by
  induction n with
  | zero => simp [sumR, add_zero]
  | succ k ih =>
    rw [Nat.add_succ, sumR, sumR, ih, CommRing.add_assoc]

theorem sumR_mul_left {R : Type} [CommRing R] (n : Nat) (c : R) (f : Nat → R) :
    c * sumR n f = sumR n (fun i => c * f i) := by
  induction n with
  | zero => simp [sumR, mul_zero]
  | succ k ih => simp only [sumR, CommRing.left_distrib, ih]

/-- Natural and integer finite sums. -/
def sumNat : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k + 1, f => sumNat k f + f k

def sumInt : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | k + 1, f => sumInt k f + f k

theorem sumInt_add (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i + g i) = sumInt n f + sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, ih]; omega

theorem sumInt_sub (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i - g i) = sumInt n f - sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, ih]; omega

theorem sumInt_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    c * sumInt n f = sumInt n (fun i => c * f i) := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih => simp only [sumInt, Int.mul_add, ih]

theorem sumInt_congr {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    sumInt n f = sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumInt]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem sumInt_zero_fn (n : Nat) : sumInt n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumInt, ih]

theorem sumNat_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNat]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem sumNat_le {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i ≤ g i) :
    sumNat n f ≤ sumNat n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [sumNat]
    exact Nat.add_le_add (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h k (Nat.lt_succ_self k))

/-- Binomial coefficient `chooseNat n k = C(n, k)`. -/
def chooseNat : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => chooseNat n k + chooseNat n (k + 1)

theorem chooseNat_self (n : Nat) : chooseNat n n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hgt : ∀ a b, a < b → chooseNat a b = 0 := by
      intro a
      induction a with
      | zero => intro b hb; cases b with | zero => omega | succ m => rfl
      | succ a ih2 =>
        intro b hb
        cases b with
        | zero => omega
        | succ m =>
          simp only [chooseNat]
          rw [ih2 m (by omega), ih2 (m + 1) (by omega)]
    simp only [chooseNat, ih, hgt k (k + 1) (Nat.lt_succ_self k)]

theorem chooseNat_absorption (n k : Nat) :
    (k + 1) * chooseNat (n + 1) (k + 1) = (n + 1) * chooseNat n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ m => simp [chooseNat]
  | succ m ih =>
    cases k with
    | zero =>
      simp only [chooseNat]
      have h1 : ∀ t, chooseNat t 1 = t := by
        intro t; induction t with
        | zero => rfl
        | succ r ihr => simp [chooseNat, ihr, Nat.add_comm]
      rw [h1 m]; omega
    | succ r =>
      have h1 : (r + 1) * chooseNat (m + 1) (r + 1) = (m + 1) * chooseNat m r := ih r
      have h2 : (r + 2) * chooseNat (m + 1) (r + 2) = (m + 1) * chooseNat m (r + 1) := ih (r + 1)
      have hpas1 : chooseNat (m + 2) (r + 2) = chooseNat (m + 1) (r + 1) + chooseNat (m + 1) (r + 2) := rfl
      have hpas2 : chooseNat (m + 1) (r + 1) = chooseNat m r + chooseNat m (r + 1) := rfl
      change (r + 2) * chooseNat (m + 2) (r + 2) = (m + 2) * chooseNat (m + 1) (r + 1)
      rw [hpas1, Nat.mul_add, h2]
      have hsplit : (r + 2) * chooseNat (m + 1) (r + 1) = (r + 1) * chooseNat (m + 1) (r + 1) + chooseNat (m + 1) (r + 1) :=
        Nat.succ_mul (r + 1) (chooseNat (m + 1) (r + 1))
      rw [hsplit, h1, hpas2]
      have hR1 : (m + 2) * (chooseNat m r + chooseNat m (r + 1))
               = (m + 1) * chooseNat m r + chooseNat m r + ((m + 1) * chooseNat m (r + 1) + chooseNat m (r + 1)) := by
        rw [Nat.mul_add, Nat.succ_mul (m + 1), Nat.succ_mul (m + 1)]
      omega

/-- Exact `CommRing Int` instance. -/
instance instCommRingInt : CommRing Int where
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_neg := Int.add_right_neg
  sub_eq := fun _ _ => Int.sub_eq_add_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  left_distrib := Int.mul_add

/-- Pairwise distinctness predicate on lists. -/
def PairwiseNeq {α : Type} : List α → Prop
  | [] => True
  | x :: xs => (∀ y ∈ xs, x ≠ y) ∧ PairwiseNeq xs

end
end TriadFrontier.AlgebraCore
