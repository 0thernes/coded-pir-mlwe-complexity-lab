module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore
public import TriadFrontier.KoszulTensor
public import TriadFrontier.StrassenWinograd
public import TriadFrontier.BrockettDobkin

/-!
# Multivariate Schwartz–Zippel & Two-Sided Strassen–Brockett–Dobkin MatMul Sandwich (`T3k`)

Zero-Mathlib, characteristic-free Lean 4.35.0 formalization over **EVERY `SimpleField F` (incl. `F_2`)**:
1. **Multivariate Schwartz–Zippel Lemma (`schwartz_zippel_root_bound`, `schwartz_zippel_nonvanishing`):**
   Any nonzero `n`-variate polynomial `P ∈ F[x_1,...,x_n]` of total degree `≤ d` has at most
   `d * |S|^{n-1}` roots in any finite grid `S^n` (`Nodup S`), and whenever `d < |S|`,
   `∃ a ∈ S^n, P(a) ≠ 0`. Closes the formal algebraic foundation of both Pillar I's deterministic
   zero-error PIR existence proof (Theorem 2.4) and Polynomial Identity Testing (`CS-012`, `VP` vs `VNP`).
2. **Kronecker Tensor-Rank Submultiplicativity & Two-Sided Strassen–Brockett–Dobkin Sandwich:**
   Proves `rank_F(⟨m1*m2, k1*k2, p1*p2⟩) ≤ rank_F(⟨m1,k1,p1⟩) * rank_F(⟨m2,k2,p2⟩)` and
   transposition symmetry `rank_F(⟨m,k,p⟩) = rank_F(⟨p,k,m⟩)` over EVERY `SimpleField F`,
   establishing the exact two-sided asymptotic sandwich for EVERY `k : Nat` and EVERY field `F`:
   `2 * 4^k - 2^k ≤ rank_F(⟨2^k, 2^k, 2^k⟩) ≤ 7^k`!
-/

namespace TriadFrontier.AlgebraicComplexity

open TriadFrontier.AlgebraCore
open TriadFrontier.KoszulTensor
open TriadFrontier.StrassenWinograd
open TriadFrontier.BrockettDobkin

@[expose] public section

-- ============================================================================
-- Section 1: Univariate Polynomials & Lagrange Root Bound over ANY SimpleField F
-- ============================================================================

/-- Evaluate univariate polynomial `c_0 + c_1 x + ... + c_d x^d` at `x : F`. -/
def evalUni {F : Type} [SimpleField F] : List F → F → F
  | [], _ => 0
  | c :: cs, x => c + x * evalUni cs x

/-- Predicate: univariate polynomial has at least one nonzero coefficient. -/
def uniNonZero {F : Type} [SimpleField F] : List F → Prop
  | [] => False
  | c :: cs => c ≠ 0 ∨ uniNonZero cs

/-- Predicate: all coefficients in the list are zero. -/
def uniTrimZero {F : Type} [SimpleField F] : List F → Prop
  | [] => True
  | c :: cs => c = 0 ∧ uniTrimZero cs

theorem evalUni_of_trimZero {F : Type} [SimpleField F] :
    ∀ (p : List F) (x : F), uniTrimZero p → evalUni p x = 0
  | [], _, _ => rfl
  | c :: cs, x, ⟨hc, hcs⟩ => by
    simp only [evalUni, hc, evalUni_of_trimZero cs x hcs, mul_zero, add_zero]

theorem uniNonZero_or_trimZero {F : Type} [SimpleField F] (p : List F) :
    uniNonZero p ∨ uniTrimZero p := by
  induction p with
  | nil => exact Or.inr trivial
  | cons c cs ih =>
    by_cases hc : c = 0
    · cases ih with
      | inl hnz => exact Or.inl (Or.inr hnz)
      | inr hz => exact Or.inr ⟨hc, hz⟩
    · exact Or.inl (Or.inl hc)

theorem not_uniNonZero_and_trimZero {F : Type} [SimpleField F] :
    ∀ (p : List F), uniNonZero p → uniTrimZero p → False
  | [], h, _ => h
  | _ :: _, Or.inl hc, ⟨h0, _⟩ => hc h0
  | _ :: cs, Or.inr hnz, ⟨_, hz⟩ => not_uniNonZero_and_trimZero cs hnz hz

/-- Horner / synthetic division of `p` by `(X - r)`: returns `(quotient, remainder)`. -/
def hornerDiv {F : Type} [SimpleField F] (r : F) : List F → List F × F
  | [] => ([], 0)
  | c :: cs =>
    let (q, rem) := hornerDiv r cs
    (rem :: q, c + r * rem)

theorem hornerDiv_spec {F : Type} [SimpleField F] (r : F) (p : List F) :
    (hornerDiv r p).2 = evalUni p r ∧
    ∀ x : F, evalUni p x = (x - r) * evalUni (hornerDiv r p).1 x + (hornerDiv r p).2 := by
  induction p with
  | nil =>
    refine ⟨rfl, fun x => ?_⟩
    simp only [hornerDiv, evalUni, mul_zero, add_zero]
  | cons c cs ih =>
    simp only [hornerDiv, evalUni]
    obtain ⟨hrem, heval⟩ := ih
    constructor
    · rw [hrem]
    · intro x
      rw [heval x]
      let q := (hornerDiv r cs).1
      let rem := (hornerDiv r cs).2
      change c + x * ((x - r) * evalUni q x + rem) = (x - r) * (rem + x * evalUni q x) + (c + r * rem)
      have h1 : x * ((x - r) * evalUni q x + rem) = (x - r) * (x * evalUni q x) + x * rem := by
        rw [CommRing.left_distrib]
        congr 1
        rw [← CommRing.mul_assoc, CommRing.mul_comm x (x - r), CommRing.mul_assoc]
      have h2 : (x - r) * (rem + x * evalUni q x) = (x - r) * rem + (x - r) * (x * evalUni q x) :=
        CommRing.left_distrib ..
      have h3 : (x - r) * rem + r * rem = x * rem := by
        rw [CommRing.sub_eq, right_distrib, neg_mul, CommRing.add_assoc,
            CommRing.add_comm (-(r * rem)) (r * rem), CommRing.add_neg, add_zero]
      rw [h1, h2, ← h3]
      let A := (x - r) * (x * evalUni q x)
      let B := (x - r) * rem
      let C := r * rem
      change c + (A + (B + C)) = (B + A) + (c + C)
      rw [CommRing.add_comm B A, CommRing.add_assoc A B (c + C),
          CommRing.add_comm c (A + (B + C)), CommRing.add_assoc A (B + C) c,
          CommRing.add_assoc B C c, CommRing.add_comm C c]

/-- Degree bound for a univariate polynomial: trailing coefficients beyond index `d` are zero. -/
def uniDegLe {F : Type} [SimpleField F] : Nat → List F → Prop
  | _, [] => True
  | 0, _ :: cs => uniTrimZero cs
  | d + 1, _ :: cs => uniDegLe d cs

theorem hornerDiv_deg_drop {F : Type} [SimpleField F] (r : F) :
    ∀ (d : Nat) (p : List F), uniDegLe (d + 1) p → uniDegLe d (hornerDiv r p).1
  | _, [], _ => by simp [hornerDiv, uniDegLe]
  | 0, _ :: cs, hdeg => by
    cases cs with
    | nil => simp [hornerDiv, uniDegLe, uniTrimZero]
    | cons c1 cs1 =>
      have htz : uniTrimZero cs1 := hdeg
      have haux : ∀ l : List F, uniTrimZero l → uniTrimZero (hornerDiv r l).1 ∧ (hornerDiv r l).2 = 0 := by
        intro l hl
        induction l with
        | nil => exact ⟨trivial, rfl⟩
        | cons a as iha =>
          obtain ⟨ha0, has0⟩ := hl
          obtain ⟨hq0, hr0⟩ := iha has0
          simp [hornerDiv, ha0, hr0, mul_zero, add_zero, uniTrimZero, hq0]
      obtain ⟨hq1, hr1⟩ := haux cs1 htz
      simp [hornerDiv, uniDegLe, uniTrimZero, hr1, hq1]
  | d + 1, _ :: cs, hdeg => by
    simp only [hornerDiv, uniDegLe]
    exact hornerDiv_deg_drop r d cs hdeg

theorem evalUni_ne_zero_of_deg0 {F : Type} [SimpleField F] (p : List F) (x : F)
    (hnz : uniNonZero p) (hd0 : uniDegLe 0 p) : evalUni p x ≠ 0 := by
  cases p with
  | nil => exact False.elim hnz
  | cons c cs =>
    have htz : uniTrimZero cs := hd0
    have hc : c ≠ 0 := by
      cases hnz with
      | inl h => exact h
      | inr hcs => exact False.elim (not_uniNonZero_and_trimZero cs hcs htz)
    simp only [evalUni, evalUni_of_trimZero cs x htz, mul_zero, add_zero]
    exact hc

/-- Distinct elements list predicate (`Nodup`). -/
def ListNodup {α : Type} : List α → Prop
  | [] => True
  | x :: xs => (∀ y, y ∈ xs → y ≠ x) ∧ ListNodup xs

/-- Count roots of `f : F → F` in a list `S : List F` (using standard `Classical.propDecidable`). -/
noncomputable def countRootsList {F : Type} [SimpleField F] (f : F → F) : List F → Nat
  | [] => 0
  | x :: xs => @ite _ (f x = 0) (Classical.propDecidable _) 1 0 + countRootsList f xs

theorem countRootsList_le_length {F : Type} [SimpleField F] (f : F → F) (S : List F) :
    countRootsList f S ≤ S.length := by
  induction S with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [countRootsList, List.length_cons]
    by_cases h : f x = 0
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, ↓reduceIte]; omega

theorem countRootsList_congr {F : Type} [SimpleField F] {f g : F → F} {S : List F}
    (h : ∀ x, x ∈ S → (f x = 0 ↔ g x = 0)) :
    countRootsList f S = countRootsList g S := by
  induction S with
  | nil => rfl
  | cons x xs ih =>
    simp only [countRootsList]
    have hx := h x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    rw [hxs]
    by_cases hf : f x = 0
    · have hg : g x = 0 := hx.mp hf; simp only [hf, hg, ↓reduceIte]
    · have hg : g x ≠ 0 := fun h' => hf (hx.mpr h'); simp only [hf, hg, ↓reduceIte]

/-- **Lagrange Root Bound over ANY `SimpleField F`:**
    Any nonzero univariate polynomial `p` of degree `≤ d` has at most `d` roots in any `Nodup` list `S`. -/
theorem lagrange_root_bound {F : Type} [SimpleField F] :
    ∀ (d : Nat) (p : List F) (S : List F),
      ListNodup S → uniNonZero p → uniDegLe d p →
      countRootsList (evalUni p) S ≤ d := by
  intro d
  induction d with
  | zero =>
    intro p S hnodup hnz hd0
    clear hnodup
    induction S with
    | nil => exact Nat.le_refl 0
    | cons x xs ih =>
      simp only [countRootsList]
      have hne := evalUni_ne_zero_of_deg0 p x hnz hd0
      simp only [hne, ↓reduceIte, Nat.zero_add]
      exact ih
  | succ d ih =>
    intro p S hnodup hnz hdeg
    induction S with
    | nil => exact Nat.zero_le _
    | cons r rs ihrs =>
      obtain ⟨hnotmem, hnodup_rs⟩ := hnodup
      simp only [countRootsList]
      by_cases hr : evalUni p r = 0
      · simp only [hr, ↓reduceIte]
        obtain ⟨hrem, heval⟩ := hornerDiv_spec r p
        let q := (hornerDiv r p).1
        have hrem0 : (hornerDiv r p).2 = 0 := by rw [hrem, hr]
        have hq_deg : uniDegLe d q := hornerDiv_deg_drop r d p hdeg
        have hq_nz : uniNonZero q := by
          cases uniNonZero_or_trimZero q with
          | inl h => exact h
          | inr hq0 =>
            have hback : ∀ l : List F, uniTrimZero (hornerDiv r l).1 → (hornerDiv r l).2 = 0 → uniTrimZero l := by
              intro l
              induction l with
              | nil => intros; trivial
              | cons c cs ihc =>
                intro hq' hr'
                simp only [hornerDiv] at hq' hr'
                obtain ⟨hrem_cs0, hq_cs0⟩ := hq'
                have hc0 : c = 0 := by rw [hrem_cs0, mul_zero, add_zero] at hr'; exact hr'
                exact ⟨hc0, ihc hq_cs0 hrem_cs0⟩
            exact False.elim (not_uniNonZero_and_trimZero p hnz (hback p hq0 hrem0))
        have hiff : ∀ y, y ∈ rs → (evalUni p y = 0 ↔ evalUni q y = 0) := by
          intro y hy
          have hne : y ≠ r := hnotmem y hy
          have hsub_ne : y - r ≠ 0 := by
            intro hz
            have heq : y = r := by
              have := congrArg (fun z => z + r) hz
              rw [CommRing.zero_add, CommRing.sub_eq, CommRing.add_assoc,
                  CommRing.add_comm (-r) r, CommRing.add_neg, add_zero] at this
              exact this
            exact hne heq
          have he := heval y
          rw [hrem0, add_zero] at he
          rw [he]
          constructor
          · intro hp0
            have := congrArg (fun z => SimpleField.inv (y - r) * z) hp0
            rw [mul_zero, ← CommRing.mul_assoc, CommRing.mul_comm (SimpleField.inv (y - r)),
                SimpleField.mul_inv_cancel (y - r) hsub_ne, CommRing.one_mul] at this
            exact this
          · intro hq0; rw [hq0, mul_zero]
        rw [countRootsList_congr hiff]
        have hle := ih q rs hnodup_rs hq_nz hq_deg
        omega
      · simp only [hr, ↓reduceIte, Nat.zero_add]
        exact ihrs hnodup_rs

-- ============================================================================
-- Section 2: Multivariate Polynomials (Inductive!) & Full Schwartz–Zippel (∀ F)
-- ============================================================================

/-- Inductive representation of `n`-variate polynomials over `F`:
    - `const c : MPoly F 0` (0-variable scalar);
    - `zero : MPoly F (n + 1)` (zero polynomial in `x_0, ..., x_n`);
    - `cons c cs : MPoly F (n + 1)` representing `c(x_1..x_n) + x_0 * cs(x_0..x_n)`. -/
inductive MPoly (F : Type) : Nat → Type where
  | const : F → MPoly F 0
  | zero  : {n : Nat} → MPoly F (n + 1)
  | cons  : {n : Nat} → MPoly F n → MPoly F (n + 1) → MPoly F (n + 1)

/-- Evaluate an `n`-variate polynomial at `a : Fin n → F` (structurally recursive!). -/
def mpEval {F : Type} [SimpleField F] : {n : Nat} → MPoly F n → (Fin n → F) → F
  | 0, MPoly.const c, _ => c
  | _ + 1, MPoly.zero, _ => 0
  | n + 1, MPoly.cons c cs, a =>
    mpEval c (fun i => a ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩) +
    a ⟨0, Nat.zero_lt_succ n⟩ * mpEval cs a

/-- Syntactic non-zero predicate on `MPoly F n`. -/
def mpNonZero {F : Type} [SimpleField F] : {n : Nat} → MPoly F n → Prop
  | 0, MPoly.const c => c ≠ 0
  | _ + 1, MPoly.zero => False
  | _ + 1, MPoly.cons c cs => mpNonZero c ∨ mpNonZero cs

/-- Total degree `≤ d` predicate on `MPoly F n`. -/
def mpDegLe {F : Type} [SimpleField F] : {n : Nat} → Nat → MPoly F n → Prop
  | 0, _, MPoly.const _ => True
  | _ + 1, _, MPoly.zero => True
  | _ + 1, 0, MPoly.cons c cs => mpDegLe 0 c ∧ ¬ mpNonZero cs
  | _ + 1, d + 1, MPoly.cons c cs => mpDegLe (d + 1) c ∧ mpDegLe d cs

/-- Convert an `(n+1)`-variate polynomial evaluated at tail `a' : Fin n → F` into a univariate `List F`. -/
def mpToUni {F : Type} [SimpleField F] {n : Nat} (a' : Fin n → F) : MPoly F (n + 1) → List F
  | MPoly.zero => []
  | MPoly.cons c cs => mpEval c a' :: mpToUni a' cs

theorem mpEval_of_not_nonZero {F : Type} [SimpleField F] :
    ∀ {n : Nat} (P : MPoly F n) (a : Fin n → F), ¬ mpNonZero P → mpEval P a = 0
  | 0, MPoly.const c, _, h => by
    by_cases hc : c = 0
    · exact hc
    · exact False.elim (h hc)
  | _ + 1, MPoly.zero, _, _ => rfl
  | _ + 1, MPoly.cons c cs, a, h => by
    simp only [mpEval]
    rw [mpEval_of_not_nonZero c _ (fun h1 => h (Or.inl h1)),
        mpEval_of_not_nonZero cs a (fun h2 => h (Or.inr h2)), mul_zero, add_zero]

theorem mpToUni_eval {F : Type} [SimpleField F] {n : Nat} (a' : Fin n → F) (x0 : F) :
    ∀ (P : MPoly F (n + 1)),
      mpEval P (fun i => if h : i.val = 0 then x0 else a' ⟨i.val - 1, by omega⟩) =
      evalUni (mpToUni a' P) x0
  | MPoly.zero => by simp [mpEval, mpToUni, evalUni]
  | MPoly.cons c cs => by
    simp only [mpEval, mpToUni, evalUni, ↓reduceDIte]
    congr 1
    exact congrArg (x0 * ·) (mpToUni_eval a' x0 cs)

theorem mpToUni_trimZero {F : Type} [SimpleField F] {n : Nat} (a' : Fin n → F) :
    ∀ (P : MPoly F (n + 1)), ¬ mpNonZero P → uniTrimZero (mpToUni a' P)
  | MPoly.zero, _ => by simp [mpToUni, uniTrimZero]
  | MPoly.cons c cs, h => by
    simp only [mpToUni, uniTrimZero]
    exact ⟨mpEval_of_not_nonZero c a' (fun h1 => h (Or.inl h1)),
           mpToUni_trimZero a' cs (fun h2 => h (Or.inr h2))⟩

/-- Extract leading `x_0`-degree `k ≤ d` and nonzero coefficient `Q : MPoly F n` of degree `≤ d - k`. -/
theorem mp_extract_lead {F : Type} [SimpleField F] {n : Nat} :
    ∀ (d : Nat) (P : MPoly F (n + 1)),
      mpNonZero P → mpDegLe d P →
      ∃ (k : Nat) (Q : MPoly F n),
        k ≤ d ∧ mpNonZero Q ∧ mpDegLe (d - k) Q ∧
        ∀ (a' : Fin n → F),
          uniDegLe k (mpToUni a' P) ∧ (mpEval Q a' ≠ 0 → uniNonZero (mpToUni a' P))
  | _, MPoly.zero, hnz, _ => False.elim hnz
  | 0, MPoly.cons c cs, hnz, hdeg => by
    obtain ⟨hcdeg, hcs0⟩ := hdeg
    have hcnz : mpNonZero c := by
      cases hnz with
      | inl h => exact h
      | inr h => exact False.elim (hcs0 h)
    refine ⟨0, c, Nat.le_refl 0, hcnz, hcdeg, fun a' => ?_⟩
    simp only [mpToUni, uniDegLe, uniNonZero]
    exact ⟨mpToUni_trimZero a' cs hcs0, fun hne => Or.inl hne⟩
  | d + 1, MPoly.cons c cs, hnz, hdeg => by
    obtain ⟨hcdeg, hcsdeg⟩ := hdeg
    by_cases hcs_nz : mpNonZero cs
    · obtain ⟨k, Q, hkd, hQnz, hQdeg, hspec⟩ := mp_extract_lead d cs hcs_nz hcsdeg
      refine ⟨k + 1, Q, Nat.succ_le_succ hkd, hQnz, by simpa [Nat.succ_sub_succ] using hQdeg, fun a' => ?_⟩
      simp only [mpToUni, uniDegLe, uniNonZero]
      exact ⟨(hspec a').1, fun hQ => Or.inr ((hspec a').2 hQ)⟩
    · have hcnz : mpNonZero c := by
        cases hnz with
        | inl h => exact h
        | inr h => exact False.elim (hcs_nz h)
      refine ⟨0, c, Nat.zero_le _, hcnz, hcdeg, fun a' => ?_⟩
      simp only [mpToUni, uniDegLe, uniNonZero]
      exact ⟨mpToUni_trimZero a' cs hcs_nz, fun hne => Or.inl hne⟩

/-- Generic sum of a `Nat`-valued function over all tuples in the grid `S^n`. -/
def sumGrid {α : Type} (S : List α) : {n : Nat} → ((Fin n → α) → Nat) → Nat
  | 0, g => g (fun i => False.elim (Nat.not_lt_zero i.val i.isLt))
  | n + 1, g =>
    let rec go : List α → Nat
      | [] => 0
      | x :: xs =>
        sumGrid S (n := n) (fun a' => g (fun i =>
          if h : i.val = 0 then x else a' ⟨i.val - 1, by omega⟩)) + go xs
    go S

/-- Exact count of roots of `f : (Fin n → F) → F` in `S^n` (expressed cleanly via `sumGrid`). -/
noncomputable def countGridRoots {F : Type} [SimpleField F] (S : List F) {n : Nat}
    (f : (Fin n → F) → F) : Nat :=
  sumGrid S (fun a => @ite _ (f a = 0) (Classical.propDecidable _) 1 0)

theorem sumGrid_congr {α : Type} (S : List α) :
    ∀ {n : Nat} (g1 g2 : (Fin n → α) → Nat),
      (∀ a, (∀ i, a i ∈ S) → g1 a = g2 a) → sumGrid S g1 = sumGrid S g2
  | 0, g1, g2, h => by
    simp only [sumGrid]
    exact h _ (fun i => False.elim (Nat.not_lt_zero i.val i.isLt))
  | n + 1, g1, g2, h => by
    simp only [sumGrid]
    have hgo : ∀ L : List α, (∀ x, x ∈ L → x ∈ S) →
        sumGrid.go S n g1 L = sumGrid.go S n g2 L := by
      intro L hL
      induction L with
      | nil => simp [sumGrid.go]
      | cons x xs ih =>
        simp only [sumGrid.go]
        rw [sumGrid_congr S _ _ (fun a' ha' => h _ (fun i => by
              by_cases h0 : i.val = 0
              · simp only [h0, ↓reduceDIte]; exact hL x (List.mem_cons_self ..)
              · simp only [h0, ↓reduceDIte]; exact ha' _)),
            ih (fun y hy => hL y (List.mem_cons_of_mem x hy))]
    exact hgo S (fun _ hx => hx)

theorem sumGrid_le {α : Type} (S : List α) :
    ∀ {n : Nat} (g1 g2 : (Fin n → α) → Nat),
      (∀ a, (∀ i, a i ∈ S) → g1 a ≤ g2 a) → sumGrid S g1 ≤ sumGrid S g2
  | 0, g1, g2, h => by
    simp only [sumGrid]
    exact h _ (fun i => False.elim (Nat.not_lt_zero i.val i.isLt))
  | n + 1, g1, g2, h => by
    simp only [sumGrid]
    have hgo : ∀ L : List α, (∀ x, x ∈ L → x ∈ S) →
        sumGrid.go S n g1 L ≤ sumGrid.go S n g2 L := by
      intro L hL
      induction L with
      | nil => simp [sumGrid.go]
      | cons x xs ih =>
        simp only [sumGrid.go]
        exact Nat.add_le_add
          (sumGrid_le S _ _ (fun a' ha' => h _ (fun i => by
            by_cases h0 : i.val = 0
            · simp only [h0, ↓reduceDIte]; exact hL x (List.mem_cons_self ..)
            · simp only [h0, ↓reduceDIte]; exact ha' _)))
          (ih (fun y hy => hL y (List.mem_cons_of_mem x hy)))
    exact hgo S (fun _ hx => hx)

theorem sumGrid_add {α : Type} (S : List α) :
    ∀ {n : Nat} (g1 g2 : (Fin n → α) → Nat),
      sumGrid S (fun a => g1 a + g2 a) = sumGrid S g1 + sumGrid S g2
  | 0, _, _ => by simp [sumGrid]
  | n + 1, g1, g2 => by
    simp only [sumGrid]
    have hgo : ∀ L : List α,
        sumGrid.go S n (fun a => g1 a + g2 a) L = sumGrid.go S n g1 L + sumGrid.go S n g2 L := by
      intro L
      induction L with
      | nil => simp [sumGrid.go]
      | cons x xs ih =>
        simp only [sumGrid.go, sumGrid_add S, ih]; omega
    exact hgo S

theorem sumGrid_const {α : Type} (S : List α) (c : Nat) :
    ∀ n : Nat, sumGrid S (n := n) (fun _ => c) = c * S.length ^ n
  | 0 => by simp [sumGrid]
  | n + 1 => by
    simp only [sumGrid]
    have hgo : ∀ L : List α, sumGrid.go S n (fun _ => c) L = L.length * (c * S.length ^ n) := by
      intro L
      induction L with
      | nil => simp [sumGrid.go]
      | cons x xs ih =>
        simp only [sumGrid.go, sumGrid_const S c n, ih, List.length_cons, Nat.succ_mul]
        omega
    rw [hgo S, Nat.pow_succ]
    simp only [Nat.mul_left_comm, Nat.mul_comm]

theorem sumGrid_mul_left {α : Type} (S : List α) (c : Nat) :
    ∀ {n : Nat} (g : (Fin n → α) → Nat), sumGrid S (fun a => c * g a) = c * sumGrid S g
  | 0, _ => by simp [sumGrid]
  | n + 1, g => by
    simp only [sumGrid]
    have hgo : ∀ L : List α, sumGrid.go S n (fun a => c * g a) L = c * sumGrid.go S n g L := by
      intro L
      induction L with
      | nil => simp [sumGrid.go]
      | cons x xs ih => simp only [sumGrid.go, sumGrid_mul_left S c, ih, Nat.mul_add]
    exact hgo S

/-- Fubini swap: counting roots in `S^{n+1}` equals summing `countRootsList` over tail tuples `a' ∈ S^n`. -/
theorem countGridRoots_succ_fubini {F : Type} [SimpleField F] (S : List F) (n : Nat)
    (f : (Fin (n + 1) → F) → F) :
    countGridRoots S f =
    sumGrid S (n := n) (fun a' => countRootsList (fun x => f (fun i =>
      if h : i.val = 0 then x else a' ⟨i.val - 1, by omega⟩)) S) := by
  unfold countGridRoots
  simp only [sumGrid]
  have hgo : ∀ L : List F,
      sumGrid.go S n (fun a => @ite _ (f a = 0) (Classical.propDecidable _) 1 0) L =
      sumGrid S (n := n) (fun a' => countRootsList (fun x => f (fun i =>
        if h : i.val = 0 then x else a' ⟨i.val - 1, by omega⟩)) L) := by
    intro L
    induction L with
    | nil =>
      simp only [sumGrid.go, countRootsList]
      rw [sumGrid_const S 0 n, Nat.zero_mul]
    | cons x xs ih =>
      simp only [sumGrid.go, countRootsList, sumGrid_add, ih]
  exact hgo S

/-- **Multivariate Schwartz–Zippel Lemma over EVERY `SimpleField F` (including `F_2`!):**
    For EVERY `n : Nat`, EVERY `Nodup` list `S : List F`, and EVERY nonzero `P : MPoly F n`
    of total degree `≤ d`:
    `|S| * |{ a ∈ S^n : P(a) = 0 }| ≤ d * |S|^n`. -/
theorem schwartz_zippel_root_bound {F : Type} [SimpleField F] :
    ∀ (n d : Nat) (S : List F) (P : MPoly F n),
      ListNodup S → mpNonZero P → mpDegLe d P →
      S.length * countGridRoots S (mpEval P) ≤ d * S.length ^ n := by
  intro n
  induction n with
  | zero =>
    intro d S P _ hnz _
    cases P with
    | const c =>
      unfold countGridRoots sumGrid
      have hne : c ≠ 0 := hnz
      simp only [mpEval, hne, ↓reduceIte, Nat.mul_zero, Nat.zero_le]
  | succ n ih =>
    intro d S P hnodup hnz hdeg
    obtain ⟨k, Q, hkd, hQnz, hQdeg, hspec⟩ := mp_extract_lead d P hnz hdeg
    rw [countGridRoots_succ_fubini]
    have hpt : ∀ a' : Fin n → F, (∀ i, a' i ∈ S) →
        countRootsList (fun x => mpEval P (fun i =>
          if h : i.val = 0 then x else a' ⟨i.val - 1, by omega⟩)) S ≤
        (@ite _ (mpEval Q a' = 0) (Classical.propDecidable _) S.length 0) + k := by
      intro a' _
      obtain ⟨huni_deg, huni_nz⟩ := hspec a'
      by_cases hQ0 : mpEval Q a' = 0
      · simp only [hQ0, ↓reduceIte]
        have hle := countRootsList_le_length
          (fun x => mpEval P (fun i => if h : i.val = 0 then x else a' ⟨i.val - 1, by omega⟩)) S
        omega
      · simp only [hQ0, ↓reduceIte, Nat.zero_add]
        have hcongr : countRootsList
            (fun x => mpEval P (fun i => if h : i.val = 0 then x else a' ⟨i.val - 1, by omega⟩)) S =
            countRootsList (evalUni (mpToUni a' P)) S :=
          countRootsList_congr (fun x _ => by rw [mpToUni_eval a' x P])
        rw [hcongr]
        exact lagrange_root_bound k _ S hnodup (huni_nz hQ0) huni_deg
    have hsum1 := sumGrid_le S _ _ hpt
    rw [sumGrid_add, sumGrid_const S k n] at hsum1
    have hQsum : sumGrid S (n := n) (fun a' => @ite _ (mpEval Q a' = 0) (Classical.propDecidable _) S.length 0) =
        S.length * countGridRoots S (mpEval Q) := by
      unfold countGridRoots
      rw [← sumGrid_mul_left]
      apply sumGrid_congr
      intro a' _
      by_cases h : mpEval Q a' = 0
      · simp only [h, ↓reduceIte, Nat.mul_one]
      · simp only [h, ↓reduceIte, Nat.mul_zero]
    rw [hQsum] at hsum1
    have hih := ih (d - k) S Q hnodup hQnz hQdeg
    have hcomb : (d - k) * S.length ^ n + k * S.length ^ n = d * S.length ^ n := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hkd]
    have hstep : sumGrid S (n := n) (fun a' => countRootsList (fun x => mpEval P (fun i =>
        if h : i.val = 0 then x else a' ⟨i.val - 1, by omega⟩)) S) ≤ d * S.length ^ n := by
      omega
    rw [Nat.pow_succ, Nat.mul_comm (S.length ^ n) S.length]
    calc S.length * sumGrid S (n := n) (fun a' => countRootsList (fun x => mpEval P (fun i =>
            if h : i.val = 0 then x else a' ⟨i.val - 1, by omega⟩)) S)
        ≤ S.length * (d * S.length ^ n) := Nat.mul_le_mul_left S.length hstep
      _ = d * (S.length * S.length ^ n) := by simp only [Nat.mul_left_comm]

private theorem nat_pos_pow (a : Nat) (ha : 0 < a) : ∀ n : Nat, 0 < a ^ n
  | 0 => by simp
  | n + 1 => Nat.mul_pos (nat_pos_pow a ha n) ha

/-- Non-vanishing corollary (`schwartz_zippel_nonvanishing`): if `deg(P) < |S|` (`Nodup S`),
    there EXISTS a grid point `a ∈ S^n` with `mpEval P a ≠ 0`! -/
theorem schwartz_zippel_nonvanishing {F : Type} [SimpleField F] (n d : Nat) (S : List F) (P : MPoly F n)
    (hnodup : ListNodup S) (hnz : mpNonZero P) (hdeg : mpDegLe d P) (hS : d < S.length) :
    ∃ a : Fin n → F, (∀ i, a i ∈ S) ∧ mpEval P a ≠ 0 := by
  have hbound := schwartz_zippel_root_bound n d S P hnodup hnz hdeg
  have hSpos : 0 < S.length := by omega
  have hpow_pos : 0 < S.length ^ n := nat_pos_pow S.length hSpos n
  have hstrict : countGridRoots S (mpEval P) < S.length ^ n := by
    by_cases hlt : countGridRoots S (mpEval P) < S.length ^ n
    · exact hlt
    · have hge : S.length ^ n ≤ countGridRoots S (mpEval P) := by omega
      have h1 : S.length * S.length ^ n ≤ S.length * countGridRoots S (mpEval P) :=
        Nat.mul_le_mul_left S.length hge
      have h2 : d * S.length ^ n < S.length * S.length ^ n :=
        Nat.mul_lt_mul_of_pos_right hS hpow_pos
      omega
  by_cases hex : ∃ a : Fin n → F, (∀ i, a i ∈ S) ∧ mpEval P a ≠ 0
  · exact hex
  · exfalso
    have hall0 : ∀ a : Fin n → F, (∀ i, a i ∈ S) → mpEval P a = 0 := by
      intro a ha
      by_cases hz : mpEval P a = 0
      · exact hz
      · exact False.elim (hex ⟨a, ha, hz⟩)
    have hfull : countGridRoots S (mpEval P) = S.length ^ n := by
      unfold countGridRoots
      rw [sumGrid_congr S _ (fun _ => 1) (fun a ha => by simp only [hall0 a ha, ↓reduceIte])]
      rw [sumGrid_const S 1 n, Nat.one_mul]
    omega

-- ============================================================================
-- Section 3: Kronecker Submultiplicativity & Two-Sided Strassen–Brockett–Dobkin Sandwich
-- ============================================================================

/-- **Transposition Symmetry (`rectMatMul_transpose`):**
    `rank_F(⟨m, k, p⟩) = rank_F(⟨p, k, m⟩)` over EVERY `SimpleField F` (completing `S_3` symmetry!). -/
theorem rectMatMul_transpose {F : Type} [SimpleField F] (m k p r : Nat)
    (hr : HasTensorRankAtMost (m * k) (k * p) (m * p) r
      (fun a b c => intToR (R := F) (rectMatMulTensor m k p a b c))) :
    HasTensorRankAtMost (p * k) (k * m) (p * m) r
      (fun a b c => intToR (R := F) (rectMatMulTensor p k m a b c)) := by
  obtain ⟨U, V, W, hT⟩ := hr
  refine ⟨fun s a => V s ((a % k) * p + a / k),
          fun s b => U s ((b % m) * k + b / m),
          fun s c => W s ((c % m) * p + c / m), ?_⟩
  intro a b c ha hb hc
  have hm : 0 < m := by cases m with | zero => simp at hb | succ _ => exact Nat.zero_lt_succ _
  have hk : 0 < k := by cases k with | zero => simp at ha | succ _ => exact Nat.zero_lt_succ _
  have hp : 0 < p := by cases p with | zero => simp at ha | succ _ => exact Nat.zero_lt_succ _
  have ha_q : a / k < p := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at ha)
  have ha_r : a % k < k := Nat.mod_lt a hk
  have hb_q : b / m < k := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hb)
  have hb_r : b % m < m := Nat.mod_lt b hm
  have hc_q : c / m < p := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hc)
  have hc_r : c % m < m := Nat.mod_lt c hm
  have ha' : (b % m) * k + b / m < m * k := by
    calc (b % m) * k + b / m < (b % m) * k + k := Nat.add_lt_add_left hb_q _
      _ = (b % m + 1) * k := (Nat.succ_mul ..).symm
      _ ≤ m * k := Nat.mul_le_mul_right k hb_r
  have hb' : (a % k) * p + a / k < k * p := by
    calc (a % k) * p + a / k < (a % k) * p + p := Nat.add_lt_add_left ha_q _
      _ = (a % k + 1) * p := (Nat.succ_mul ..).symm
      _ ≤ k * p := Nat.mul_le_mul_right p ha_r
  have hc' : (c % m) * p + c / m < m * p := by
    calc (c % m) * p + c / m < (c % m) * p + p := Nat.add_lt_add_left hc_q _
      _ = (c % m + 1) * p := (Nat.succ_mul ..).symm
      _ ≤ m * p := Nat.mul_le_mul_right p hc_r
  have hEq := hT ((b % m) * k + b / m) ((a % k) * p + a / k) ((c % m) * p + c / m) ha' hb' hc'
  dsimp only at hEq ⊢
  have hcomm : sumR r (fun s => V s ((a % k) * p + a / k) * U s ((b % m) * k + b / m) * W s ((c % m) * p + c / m)) =
      sumR r (fun s => U s ((b % m) * k + b / m) * V s ((a % k) * p + a / k) * W s ((c % m) * p + c / m)) :=
    sumR_congr (fun s _ => by rw [CommRing.mul_comm (V s _) (U s _)])
  rw [hcomm, ← hEq]
  congr 1
  unfold rectMatMulTensor
  have h1 : ((b % m) * k + b / m) / k = b % m := by
    rw [Nat.mul_comm (b % m) k, Nat.mul_add_div hk, Nat.div_eq_of_lt hb_q, Nat.add_zero]
  have h2 : ((b % m) * k + b / m) % k = b / m := by
    rw [Nat.mul_comm (b % m) k, Nat.mul_add_mod, Nat.mod_eq_of_lt hb_q]
  have h3 : ((a % k) * p + a / k) / p = a % k := by
    rw [Nat.mul_comm (a % k) p, Nat.mul_add_div hp, Nat.div_eq_of_lt ha_q, Nat.add_zero]
  have h4 : ((a % k) * p + a / k) % p = a / k := by
    rw [Nat.mul_comm (a % k) p, Nat.mul_add_mod, Nat.mod_eq_of_lt ha_q]
  have h5 : ((c % m) * p + c / m) / p = c % m := by
    rw [Nat.mul_comm (c % m) p, Nat.mul_add_div hp, Nat.div_eq_of_lt hc_q, Nat.add_zero]
  have h6 : ((c % m) * p + c / m) % p = c / m := by
    rw [Nat.mul_comm (c % m) p, Nat.mul_add_mod, Nat.mod_eq_of_lt hc_q]
  simp only [h1, h2, h3, h4, h5, h6, ha_q, ha_r, hb_q, hb_r, hc_q, hc_r, true_and]
  have hiff : (a / k = c / m ∧ a % k = b / m ∧ b % m = c % m) ↔
      (b % m = c % m ∧ b / m = a % k ∧ a / k = c / m) :=
    ⟨fun ⟨x, y, z⟩ => ⟨z, y.symm, x⟩, fun ⟨x, y, z⟩ => ⟨z, y.symm, x⟩⟩
  split <;> split
  · rfl
  · rename_i h1 h2; exact False.elim (h2 (hiff.mp h1))
  · rename_i h1 h2; exact False.elim (h1 (hiff.mpr h2))
  · rfl

private theorem sumR_split_mul {R : Type} [CommRing R] (A B : Nat) (f : Nat → R) :
    sumR (A * B) f = sumR A (fun q => sumR B (fun r => f (q * B + r))) := by
  induction A with
  | zero => simp [sumR]
  | succ a ih =>
    have hadd : ∀ (base len : Nat) (g : Nat → R),
        sumR (base + len) g = sumR base g + sumR len (fun r => g (base + r)) := by
      intro base len g
      induction len with
      | zero => simp [sumR, add_zero]
      | succ l ihl => rw [Nat.add_succ, sumR, ihl, sumR, CommRing.add_assoc]
    rw [Nat.succ_mul, hadd (a * B) B f, ih, sumR]

/-- **Kronecker Tensor-Rank Submultiplicativity over EVERY `SimpleField F`:**
    `rank_F(⟨m1*m2, k1*k2, p1*p2⟩) ≤ rank_F(⟨m1, k1, p1⟩) * rank_F(⟨m2, k2, p2⟩)`! -/
theorem rectMatMul_kronecker_rank {F : Type} [SimpleField F]
    (m1 k1 p1 m2 k2 p2 r1 r2 : Nat)
    (hm2 : 0 < m2) (hk2 : 0 < k2) (hp2 : 0 < p2)
    (h1 : HasTensorRankAtMost (m1 * k1) (k1 * p1) (m1 * p1) r1
      (fun a b c => intToR (R := F) (rectMatMulTensor m1 k1 p1 a b c)))
    (h2 : HasTensorRankAtMost (m2 * k2) (k2 * p2) (m2 * p2) r2
      (fun a b c => intToR (R := F) (rectMatMulTensor m2 k2 p2 a b c))) :
    HasTensorRankAtMost ((m1 * m2) * (k1 * k2)) ((k1 * k2) * (p1 * p2)) ((m1 * m2) * (p1 * p2)) (r1 * r2)
      (fun a b c => intToR (R := F) (rectMatMulTensor (m1 * m2) (k1 * k2) (p1 * p2) a b c)) := by
  obtain ⟨U1, V1, W1, hT1⟩ := h1
  obtain ⟨U2, V2, W2, hT2⟩ := h2
  let a1 (a : Nat) : Nat := (a / (k1 * k2) / m2) * k1 + (a % (k1 * k2) / k2)
  let a2 (a : Nat) : Nat := (a / (k1 * k2) % m2) * k2 + (a % (k1 * k2) % k2)
  let b1 (b : Nat) : Nat := (b / (p1 * p2) / k2) * p1 + (b % (p1 * p2) / p2)
  let b2 (b : Nat) : Nat := (b / (p1 * p2) % k2) * p2 + (b % (p1 * p2) % p2)
  let c1 (c : Nat) : Nat := (c / (p1 * p2) / m2) * p1 + (c % (p1 * p2) / p2)
  let c2 (c : Nat) : Nat := (c / (p1 * p2) % m2) * p2 + (c % (p1 * p2) % p2)
  refine ⟨fun s a => U1 (s / r2) (a1 a) * U2 (s % r2) (a2 a),
          fun s b => V1 (s / r2) (b1 b) * V2 (s % r2) (b2 b),
          fun s c => W1 (s / r2) (c1 c) * W2 (s % r2) (c2 c), ?_⟩
  intro a b c ha hb hc
  have hk1 : 0 < k1 := by cases k1 with | zero => simp at ha | succ _ => exact Nat.zero_lt_succ _
  have hm1 : 0 < m1 := by cases m1 with | zero => simp at ha | succ _ => exact Nat.zero_lt_succ _
  have hp1 : 0 < p1 := by cases p1 with | zero => simp at hb | succ _ => exact Nat.zero_lt_succ _
  have hk12 : 0 < k1 * k2 := Nat.mul_pos hk1 hk2
  have hp12 : 0 < p1 * p2 := Nat.mul_pos hp1 hp2
  have ha_row : a / (k1 * k2) < m1 * m2 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at ha)
  have ha_col : a % (k1 * k2) < k1 * k2 := Nat.mod_lt a hk12
  have hb_row : b / (p1 * p2) < k1 * k2 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hb)
  have hb_col : b % (p1 * p2) < p1 * p2 := Nat.mod_lt b hp12
  have hc_row : c / (p1 * p2) < m1 * m2 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hc)
  have hc_col : c % (p1 * p2) < p1 * p2 := Nat.mod_lt c hp12
  have ha1 : a1 a < m1 * k1 := by
    have hq : a / (k1 * k2) / m2 < m1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm m2 m1]; exact ha_row)
    have hr : a % (k1 * k2) / k2 < k1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm k2 k1]; exact ha_col)
    dsimp only [a1]
    calc _ < (a / (k1 * k2) / m2) * k1 + k1 := Nat.add_lt_add_left hr _
      _ = (a / (k1 * k2) / m2 + 1) * k1 := (Nat.succ_mul ..).symm
      _ ≤ m1 * k1 := Nat.mul_le_mul_right k1 hq
  have ha2 : a2 a < m2 * k2 := by
    have hq : a / (k1 * k2) % m2 < m2 := Nat.mod_lt _ hm2
    have hr : a % (k1 * k2) % k2 < k2 := Nat.mod_lt _ hk2
    dsimp only [a2]
    calc _ < (a / (k1 * k2) % m2) * k2 + k2 := Nat.add_lt_add_left hr _
      _ = (a / (k1 * k2) % m2 + 1) * k2 := (Nat.succ_mul ..).symm
      _ ≤ m2 * k2 := Nat.mul_le_mul_right k2 hq
  have hb1 : b1 b < k1 * p1 := by
    have hq : b / (p1 * p2) / k2 < k1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm k2 k1]; exact hb_row)
    have hr : b % (p1 * p2) / p2 < p1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p2 p1]; exact hb_col)
    dsimp only [b1]
    calc _ < (b / (p1 * p2) / k2) * p1 + p1 := Nat.add_lt_add_left hr _
      _ = (b / (p1 * p2) / k2 + 1) * p1 := (Nat.succ_mul ..).symm
      _ ≤ k1 * p1 := Nat.mul_le_mul_right p1 hq
  have hb2 : b2 b < k2 * p2 := by
    have hq : b / (p1 * p2) % k2 < k2 := Nat.mod_lt _ hk2
    have hr : b % (p1 * p2) % p2 < p2 := Nat.mod_lt _ hp2
    dsimp only [b2]
    calc _ < (b / (p1 * p2) % k2) * p2 + p2 := Nat.add_lt_add_left hr _
      _ = (b / (p1 * p2) % k2 + 1) * p2 := (Nat.succ_mul ..).symm
      _ ≤ k2 * p2 := Nat.mul_le_mul_right p2 hq
  have hc1 : c1 c < m1 * p1 := by
    have hq : c / (p1 * p2) / m2 < m1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm m2 m1]; exact hc_row)
    have hr : c % (p1 * p2) / p2 < p1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p2 p1]; exact hc_col)
    dsimp only [c1]
    calc _ < (c / (p1 * p2) / m2) * p1 + p1 := Nat.add_lt_add_left hr _
      _ = (c / (p1 * p2) / m2 + 1) * p1 := (Nat.succ_mul ..).symm
      _ ≤ m1 * p1 := Nat.mul_le_mul_right p1 hq
  have hc2 : c2 c < m2 * p2 := by
    have hq : c / (p1 * p2) % m2 < m2 := Nat.mod_lt _ hm2
    have hr : c % (p1 * p2) % p2 < p2 := Nat.mod_lt _ hp2
    dsimp only [c2]
    calc _ < (c / (p1 * p2) % m2) * p2 + p2 := Nat.add_lt_add_left hr _
      _ = (c / (p1 * p2) % m2 + 1) * p2 := (Nat.succ_mul ..).symm
      _ ≤ m2 * p2 := Nat.mul_le_mul_right p2 hq
  cases r2 with
  | zero =>
    have hz2 := hT2 0 0 0 (Nat.mul_pos hm2 hk2) (Nat.mul_pos hk2 hp2) (Nat.mul_pos hm2 hp2)
    simp only [sumR, rectMatMulTensor, Nat.zero_div, Nat.zero_mod, hm2, hk2, hp2, and_self,
               ↓reduceIte, intToR, natToR, CommRing.zero_add] at hz2
    exact False.elim (SimpleField.zero_ne_one hz2.symm)
  | succ r2' =>
    have hr2pos : 0 < r2' + 1 := Nat.zero_lt_succ r2'
    dsimp only
    rw [sumR_split_mul r1 (r2' + 1)]
    have hmull : ∀ (N : Nat) (z : F) (f : Nat → F), z * sumR N f = sumR N (fun s => z * f s) := by
      intro N z f
      induction N with
      | zero => simp [sumR, mul_zero]
      | succ n ihn => simp only [sumR, ← ihn, CommRing.left_distrib]
    have hfact : sumR r1 (fun s1 => sumR (r2' + 1) (fun s2 =>
        U1 ((s1 * (r2' + 1) + s2) / (r2' + 1)) (a1 a) * U2 ((s1 * (r2' + 1) + s2) % (r2' + 1)) (a2 a) *
        (V1 ((s1 * (r2' + 1) + s2) / (r2' + 1)) (b1 b) * V2 ((s1 * (r2' + 1) + s2) % (r2' + 1)) (b2 b)) *
        (W1 ((s1 * (r2' + 1) + s2) / (r2' + 1)) (c1 c) * W2 ((s1 * (r2' + 1) + s2) % (r2' + 1)) (c2 c)))) =
        sumR r1 (fun s1 => U1 s1 (a1 a) * V1 s1 (b1 b) * W1 s1 (c1 c)) *
        sumR (r2' + 1) (fun s2 => U2 s2 (a2 a) * V2 s2 (b2 b) * W2 s2 (c2 c)) := by
      have hinner : ∀ s1, s1 < r1 →
          sumR (r2' + 1) (fun s2 =>
            U1 ((s1 * (r2' + 1) + s2) / (r2' + 1)) (a1 a) * U2 ((s1 * (r2' + 1) + s2) % (r2' + 1)) (a2 a) *
            (V1 ((s1 * (r2' + 1) + s2) / (r2' + 1)) (b1 b) * V2 ((s1 * (r2' + 1) + s2) % (r2' + 1)) (b2 b)) *
            (W1 ((s1 * (r2' + 1) + s2) / (r2' + 1)) (c1 c) * W2 ((s1 * (r2' + 1) + s2) % (r2' + 1)) (c2 c))) =
          (U1 s1 (a1 a) * V1 s1 (b1 b) * W1 s1 (c1 c)) *
          sumR (r2' + 1) (fun s2 => U2 s2 (a2 a) * V2 s2 (b2 b) * W2 s2 (c2 c)) := by
        intro s1 _
        rw [hmull]
        apply sumR_congr
        intro s2 hs2
        have hd : (s1 * (r2' + 1) + s2) / (r2' + 1) = s1 := by
          rw [Nat.mul_comm s1 (r2' + 1), Nat.mul_add_div hr2pos, Nat.div_eq_of_lt hs2, Nat.add_zero]
        have hm : (s1 * (r2' + 1) + s2) % (r2' + 1) = s2 := by
          rw [Nat.mul_comm s1 (r2' + 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hs2]
        rw [hd, hm]
        let u1 := U1 s1 (a1 a); let u2 := U2 s2 (a2 a)
        let v1 := V1 s1 (b1 b); let v2 := V2 s2 (b2 b)
        let w1 := W1 s1 (c1 c); let w2 := W2 s2 (c2 c)
        change (u1 * u2) * (v1 * v2) * (w1 * w2) = (u1 * v1 * w1) * (u2 * v2 * w2)
        calc (u1 * u2) * (v1 * v2) * (w1 * w2)
            = ((u1 * v1) * (u2 * v2)) * (w1 * w2) := by
              congr 1
              rw [CommRing.mul_assoc u1 u2, ← CommRing.mul_assoc u2 v1, CommRing.mul_comm u2 v1,
                  CommRing.mul_assoc v1 u2, ← CommRing.mul_assoc u1 v1]
          _ = (u1 * v1 * w1) * (u2 * v2 * w2) := by
              rw [CommRing.mul_assoc (u1 * v1), ← CommRing.mul_assoc (u2 * v2) w1,
                  CommRing.mul_comm (u2 * v2) w1, CommRing.mul_assoc w1 (u2 * v2),
                  ← CommRing.mul_assoc (u1 * v1) w1]
      rw [sumR_congr hinner]
      have hmulr : ∀ (N : Nat) (f : Nat → F) (z : F), sumR N (fun s => f s * z) = sumR N f * z := by
        intro N f z
        induction N with
        | zero => simp [sumR, zero_mul]
        | succ n ihn => simp only [sumR, ihn, right_distrib]
      exact hmulr r1 _ _
    have hEq1 := hT1 (a1 a) (b1 b) (c1 c) ha1 hb1 hc1
    have hEq2 := hT2 (a2 a) (b2 b) (c2 c) ha2 hb2 hc2
    dsimp only at hEq1 hEq2
    rw [hfact, ← hEq1, ← hEq2]
    have hmul_int : ∀ x y : Int, intToR (R := F) x * intToR (R := F) y = intToR (R := F) (x * y) :=
      fun x y => (intToR_mul (R := F) x y).symm
    rw [hmul_int]
    congr 1
    unfold rectMatMulTensor
    have ha1_d : a1 a / k1 = a / (k1 * k2) / m2 := by
      dsimp only [a1]
      have hr : a % (k1 * k2) / k2 < k1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm k2 k1]; exact ha_col)
      rw [Nat.mul_comm _ k1, Nat.mul_add_div hk1, Nat.div_eq_of_lt hr, Nat.add_zero]
    have ha1_m : a1 a % k1 = a % (k1 * k2) / k2 := by
      dsimp only [a1]
      have hr : a % (k1 * k2) / k2 < k1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm k2 k1]; exact ha_col)
      rw [Nat.mul_comm _ k1, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have ha2_d : a2 a / k2 = a / (k1 * k2) % m2 := by
      dsimp only [a2]
      rw [Nat.mul_comm _ k2, Nat.mul_add_div hk2, Nat.div_eq_of_lt (Nat.mod_lt _ hk2), Nat.add_zero]
    have ha2_m : a2 a % k2 = a % (k1 * k2) % k2 := by
      dsimp only [a2]
      rw [Nat.mul_comm _ k2, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ hk2)]
    have hb1_d : b1 b / p1 = b / (p1 * p2) / k2 := by
      dsimp only [b1]
      have hr : b % (p1 * p2) / p2 < p1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p2 p1]; exact hb_col)
      rw [Nat.mul_comm _ p1, Nat.mul_add_div hp1, Nat.div_eq_of_lt hr, Nat.add_zero]
    have hb1_m : b1 b % p1 = b % (p1 * p2) / p2 := by
      dsimp only [b1]
      have hr : b % (p1 * p2) / p2 < p1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p2 p1]; exact hb_col)
      rw [Nat.mul_comm _ p1, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have hb2_d : b2 b / p2 = b / (p1 * p2) % k2 := by
      dsimp only [b2]
      rw [Nat.mul_comm _ p2, Nat.mul_add_div hp2, Nat.div_eq_of_lt (Nat.mod_lt _ hp2), Nat.add_zero]
    have hb2_m : b2 b % p2 = b % (p1 * p2) % p2 := by
      dsimp only [b2]
      rw [Nat.mul_comm _ p2, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ hp2)]
    have hc1_d : c1 c / p1 = c / (p1 * p2) / m2 := by
      dsimp only [c1]
      have hr : c % (p1 * p2) / p2 < p1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p2 p1]; exact hc_col)
      rw [Nat.mul_comm _ p1, Nat.mul_add_div hp1, Nat.div_eq_of_lt hr, Nat.add_zero]
    have hc1_m : c1 c % p1 = c % (p1 * p2) / p2 := by
      dsimp only [c1]
      have hr : c % (p1 * p2) / p2 < p1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p2 p1]; exact hc_col)
      rw [Nat.mul_comm _ p1, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have hc2_d : c2 c / p2 = c / (p1 * p2) % m2 := by
      dsimp only [c2]
      rw [Nat.mul_comm _ p2, Nat.mul_add_div hp2, Nat.div_eq_of_lt (Nat.mod_lt _ hp2), Nat.add_zero]
    have hc2_m : c2 c % p2 = c % (p1 * p2) % p2 := by
      dsimp only [c2]
      rw [Nat.mul_comm _ p2, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ hp2)]
    have ha1_lt1 : a / (k1 * k2) / m2 < m1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm m2 m1]; exact ha_row)
    have ha1_lt2 : a % (k1 * k2) / k2 < k1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm k2 k1]; exact ha_col)
    have ha2_lt1 : a / (k1 * k2) % m2 < m2 := Nat.mod_lt _ hm2
    have ha2_lt2 : a % (k1 * k2) % k2 < k2 := Nat.mod_lt _ hk2
    have hb1_lt1 : b / (p1 * p2) / k2 < k1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm k2 k1]; exact hb_row)
    have hb1_lt2 : b % (p1 * p2) / p2 < p1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p2 p1]; exact hb_col)
    have hb2_lt1 : b / (p1 * p2) % k2 < k2 := Nat.mod_lt _ hk2
    have hb2_lt2 : b % (p1 * p2) % p2 < p2 := Nat.mod_lt _ hp2
    have hc1_lt1 : c / (p1 * p2) / m2 < m1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm m2 m1]; exact hc_row)
    have hc1_lt2 : c % (p1 * p2) / p2 < p1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p2 p1]; exact hc_col)
    have hc2_lt1 : c / (p1 * p2) % m2 < m2 := Nat.mod_lt _ hm2
    have hc2_lt2 : c % (p1 * p2) % p2 < p2 := Nat.mod_lt _ hp2
    simp only [ha1_d, ha1_m, ha2_d, ha2_m, hb1_d, hb1_m, hb2_d, hb2_m, hc1_d, hc1_m, hc2_d, hc2_m,
               ha_row, ha_col, hb_row, hb_col, hc_row, hc_col,
               ha1_lt1, ha1_lt2, ha2_lt1, ha2_lt2, hb1_lt1, hb1_lt2, hb2_lt1, hb2_lt2,
               hc1_lt1, hc1_lt2, hc2_lt1, hc2_lt2, true_and]
    have heq_divmod : ∀ (x y d : Nat), (x = y) ↔ (x / d = y / d ∧ x % d = y % d) := by
      intro x y d
      constructor
      · intro h; subst h; exact ⟨rfl, rfl⟩
      · intro ⟨hd, hm⟩
        have hx := Nat.div_add_mod x d
        have hy := Nat.div_add_mod y d
        rw [hd, hm] at hx
        omega
    have eA := heq_divmod (a / (k1 * k2)) (c / (p1 * p2)) m2
    have eB := heq_divmod (a % (k1 * k2)) (b / (p1 * p2)) k2
    have eC := heq_divmod (b % (p1 * p2)) (c % (p1 * p2)) p2
    by_cases h11 : a / (k1 * k2) / m2 = c / (p1 * p2) / m2 <;>
    by_cases h12 : a / (k1 * k2) % m2 = c / (p1 * p2) % m2 <;>
    by_cases h21 : a % (k1 * k2) / k2 = b / (p1 * p2) / k2 <;>
    by_cases h22 : a % (k1 * k2) % k2 = b / (p1 * p2) % k2 <;>
    by_cases h31 : b % (p1 * p2) / p2 = c % (p1 * p2) / p2 <;>
    by_cases h32 : b % (p1 * p2) % p2 = c % (p1 * p2) % p2 <;>
    simp only [eA, eB, eC, h11, h12, h21, h22, h31, h32,
               and_true, and_false, ↓reduceIte, Int.mul_one, Int.mul_zero]

/-- **Strassen's 1969 Recursive Upper Bound over EVERY `SimpleField F` (`strassen_power_upper_bound`):**
    For EVERY `k : Nat` and EVERY field `F` (including `F_2`!),
    `rank_F(⟨2^k, 2^k, 2^k⟩) ≤ 7^k`! -/
theorem strassen_power_upper_bound (F : Type) [SimpleField F] (k : Nat) :
    HasTensorRankAtMost (2 ^ k * 2 ^ k) (2 ^ k * 2 ^ k) (2 ^ k * 2 ^ k) (7 ^ k)
      (fun a b c => intToR (R := F) (matMulTensor (2 ^ k) a b c)) := by
  have hrect : ∀ j : Nat,
      HasTensorRankAtMost (2 ^ j * 2 ^ j) (2 ^ j * 2 ^ j) (2 ^ j * 2 ^ j) (7 ^ j)
        (fun a b c => intToR (R := F) (rectMatMulTensor (2 ^ j) (2 ^ j) (2 ^ j) a b c)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, fun a b c ha hb hc => ?_⟩
      have ha0 : a = 0 := by simp at ha; omega
      have hb0 : b = 0 := by simp at hb; omega
      have hc0 : c = 0 := by simp at hc; omega
      subst ha0 hb0 hc0
      simp [sumR, rectMatMulTensor, intToR, natToR, CommRing.zero_add, CommRing.one_mul]
    | succ j' ih =>
      have h2 : HasTensorRankAtMost (2 * 2) (2 * 2) (2 * 2) 7
          (fun a b c => intToR (R := F) (rectMatMulTensor 2 2 2 a b c)) := by
        obtain ⟨U, V, W, hT⟩ := strassen_rank_le_seven F
        refine ⟨U, V, W, fun a b c ha hb hc => ?_⟩
        dsimp only
        rw [rectMatMulTensor_eq_matMul2 a b c ha hb hc]
        exact hT a b c ha hb hc
      have hkr := rectMatMul_kronecker_rank (2 ^ j') (2 ^ j') (2 ^ j') 2 2 2 (7 ^ j') 7
        (by decide) (by decide) (by decide) ih h2
      simpa [Nat.pow_succ] using hkr
  obtain ⟨U, V, W, hT⟩ := hrect k
  refine ⟨U, V, W, fun a b c ha hb hc => ?_⟩
  dsimp only
  rw [← rectMatMulTensor_eq_square (2 ^ k) a b c ha hb hc]
  exact hT a b c ha hb hc

/-- **Theorem T3k (Field-Universal Multivariate Schwartz–Zippel Lemma & Strassen–Brockett–Dobkin Two-Sided Sandwich):**
    Over **EVERY `SimpleField F` (including `F_2`!)**:
    1. **Multivariate Schwartz–Zippel Root Bound (`∀ n, d, S, P`):**
       `|S| * |{a ∈ S^n : P(a) = 0}| ≤ d * |S|^n` for every nonzero `n`-variate polynomial `P` of degree `≤ d`.
    2. **Combinatorial Non-Vanishing (`d < |S| ⇒ ∃ a ∈ S^n, P(a) ≠ 0`):**
       Closes the formal algebraic foundation of Pillar I's deterministic zero-error PIR existence proof and PIT (`CS-012`).
    3. **Full `S_3` Transposition Symmetry & Kronecker Submultiplicativity:**
       `rank_F(⟨m,k,p⟩) = rank_F(⟨p,k,m⟩)` and `rank_F(⟨m1*m2,k1*k2,p1*p2⟩) ≤ r1 * r2`.
    4. **Two-Sided Strassen–Brockett–Dobkin Asymptotic Sandwich (`∀ k : Nat`, `∀ F`):**
       `2 * 4^k - 2^k ≤ rank_F(⟨2^k, 2^k, 2^k⟩) ≤ 7^k` (certifying `ω ≤ log_2 7` alongside Brockett–Dobkin)! -/
theorem t3k_schwartz_zippel_and_strassen_sandwich :
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
        2 * 4 ^ k - 2 ^ k ≤ r) := by
  refine ⟨fun _ _ => schwartz_zippel_root_bound,
          fun _ _ => schwartz_zippel_nonvanishing,
          fun _ _ => rectMatMul_transpose, ?_⟩
  intro F _ k
  refine ⟨strassen_power_upper_bound F k, fun r hr => ?_⟩
  have hpos : 1 ≤ 2 ^ k := nat_pos_pow 2 (by decide) k
  have hbd := t3i_brockett_dobkin_rectangular_and_quadratic_matmul_bound.2.1 F (2 ^ k) r hpos hr
  have h4 : ∀ j : Nat, 4 ^ j = 2 ^ j * 2 ^ j := by
    intro j
    induction j with
    | zero => rfl
    | succ j' ih =>
      rw [Nat.pow_succ, ih, Nat.pow_succ]
      have h42 : (4 : Nat) = 2 * 2 := rfl
      rw [h42]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  rw [h4 k, ← Nat.mul_assoc]
  exact hbd

end
end TriadFrontier.AlgebraicComplexity
