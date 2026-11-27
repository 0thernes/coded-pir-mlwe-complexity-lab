module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore
public import TriadFrontier.KoszulTensor
public import TriadFrontier.PIRProtocol
public import TriadFrontier.StrassenWinograd
public import TriadFrontier.BrockettDobkin
public import TriadFrontier.AlgebraicComplexity

/-!
# Bläser's `5/2 m² - 3m` Matrix Multiplication Lower Bound Over EVERY Field `F` (`T3m`, `CS-004`)

Zero-Mathlib, characteristic-free Lean 4.35.0 formalization over **EVERY `SimpleField F` (including `F_2`!)**
of **Markus Bläser's (FOCS 1999) `5/2 m² - 3m` matrix multiplication tensor rank lower bound**
(following Landsberg, `arXiv:cs/0703059` §6.1–6.2, generalized completely characteristic-free via
explicit `{0,1}`-matrix unimodular commutator pairs and a 3-stage univariate Kronecker rational
function tower `F ↪ F(t_1) ↪ F(t_1)(t_2) ↪ F(t_1)(t_2)(t_3)`):

1. **Univariate Polynomials `Poly F` & Rational Function Field `SimpleField (RatFunc F)`:**
   Constructive integral domain (`pMul_ne_zero` via max nonzero degree) and quotient field `RatFunc F`
   with injective embeddings `ratConst : F → RatFunc F` and `ratPolyEmbed : Poly F → RatFunc F`.
2. **Characteristic-Free Cofactor Determinant `detM` & Two-Sided Gauss-Jordan Inverse:**
   Full alternating row-multilinear determinant (`detM_row_add`, `detM_row_scale`, `detM_row_swap`,
   `detM_row_add_mul`, `detM_blockDiag`, `detM_first_k_cols_id`), two-sided Gauss-Jordan inverse
   `isMatInv_of_detM_ne_zero`, and full-row-rank column-basis extraction `col_basis_of_right_inv`.
3. **Explicit `{0, 1}`-Matrix Invertible-Commutator Pair `(commPairX m, commPairY m)` for ALL `m ≥ 2`:**
   Block-diagonal assembly of `2 × 2` and `3 × 3` unimodular pairs with `detM m [X_m, Y_m] = 1` over `ℤ`,
   hence invertible over **EVERY `SimpleField F` including `F_2`**!
4. **Landsberg–Bläser Degree-`m` Subset Selection (`exists_le_m_subset_det_ne_zero`):**
   Base-`(m + 1)` Kronecker substitution over `Poly F ↪ RatFunc F` proving that whenever an `n`-matrix
   linear span contains an invertible `m × m` matrix, at most `m` generators already span an invertible
   matrix over `RatFunc F`!
5. **Strassen's Commutator Equation (`strassen_commutator_bound`):**
   If `A_0, A_1, A_2 ∈ K^{n × n}` lie in a `q`-dimensional rank-1 span with `A_0` and
   `A_1 A_0⁻¹ A_2 - A_2 A_0⁻¹ A_1` invertible, then `n ≤ 2 * (q - n)` (i.e. `3 n ≤ 2 q`).
6. **Headline Theorem `t3m_blaser_five_halves_matmul_bound`:**
   For ALL `m ≥ 1` and EVERY `SimpleField F` (including `F_2`!),
     `5 * m * m - 6 * m ≤ 2 * r`,
   strictly surpassing BOTH `T3i`'s `2m² - m` (for all `m ≥ 5`) AND Brockett–Dobkin / Alder–Strassen's
   `2m² - 1` (for all `m ≥ 6`, e.g. `m = 6 → r ≥ 72 > 71`), and tightening the power-of-2 Strassen
   sandwich to `5 * 4^k - 6 * 2^k ≤ 2 * rank_F(⟨2^k, 2^k, 2^k⟩) ≤ 2 * 7^k`!
-/

namespace TriadFrontier.BlaserLowerBound

open TriadFrontier.AlgebraCore
open TriadFrontier.KoszulTensor
open TriadFrontier.PIRProtocol
open TriadFrontier.StrassenWinograd
open TriadFrontier.BrockettDobkin
open TriadFrontier.AlgebraicComplexity

@[expose] public section

-- ============================================================================
-- Section 0: Small Ring & Sum Helpers
-- ============================================================================

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

theorem sumR_single {R : Type} [CommRing R] (n k : Nat) (v : R) (hk : k < n) :
    sumR n (fun i => if i = k then v else 0) = v := by
  have h : ∀ m : Nat, sumR m (fun i => if i = k then v else 0) = if k < m then v else 0 := by
    intro m
    induction m with
    | zero => simp [sumR]
    | succ j ih =>
      simp only [sumR, ih]
      by_cases hjk : j = k
      · subst hjk
        have h1 : ¬ (j < j) := Nat.lt_irrefl j
        have h2 : j < j + 1 := Nat.lt_succ_self j
        rw [ite_f h1, ite_t h2, ite_t rfl, CommRing.zero_add]
      · have hiff : (k < j + 1) ↔ (k < j) := by omega
        rw [ite_f hjk, add_zero]
        by_cases hlt : k < j
        · rw [ite_t hlt, ite_t (hiff.mpr hlt)]
        · rw [ite_f hlt, ite_f (fun h' => hlt (hiff.mp h'))]
  rw [h n, ite_t hk]

theorem sumR_rev {R : Type} [CommRing R] :
    ∀ (n : Nat) (f : Nat → R), sumR n (fun i => f (n - 1 - i)) = sumR n f
  | 0, _ => rfl
  | n + 1, f => by
    have hsplit : sumR (n + 1) (fun i => f (n - i)) = f n + sumR n (fun i => f (n - 1 - i)) := by
      have h0 : sumR (1 + n) (fun i => f (n - i)) =
          sumR 1 (fun i => f (n - i)) + sumR n (fun i => f (n - (1 + i))) :=
        sumR_split 1 n (fun i => f (n - i))
      have h1n : 1 + n = n + 1 := Nat.add_comm 1 n
      rw [h1n] at h0
      rw [h0]
      simp only [sumR, CommRing.zero_add, Nat.sub_zero]
      congr 1
      apply sumR_congr; intro i _
      have heq : n - (1 + i) = n - 1 - i := by omega
      rw [heq]
    change sumR (n + 1) (fun i => f (n + 1 - 1 - i)) = sumR n f + f n
    have hnorm : sumR (n + 1) (fun i => f (n + 1 - 1 - i)) = sumR (n + 1) (fun i => f (n - i)) :=
      sumR_congr (fun i _ => congrArg f (by omega))
    rw [hnorm, hsplit, sumR_rev n f, CommRing.add_comm]

/-- Characteristic-free double-sum antisymmetry cancellation (zero division by 2; works over `F_2`!). -/
theorem sumR_antisym {R : Type} [CommRing R] :
    ∀ (n : Nat) (f : Nat → Nat → R),
      (∀ p q, p < n → q < n → f p q = -(f q p)) →
      (∀ p, p < n → f p p = 0) →
      sumR n (fun p => sumR n (fun q => f p q)) = 0
  | 0, _, _, _ => rfl
  | n + 1, f, hanti, hdiag => by
    simp only [sumR]
    rw [sumR_add, hdiag n (Nat.lt_succ_self n), add_zero]
    have hsub := sumR_antisym n f
      (fun p q hp hq => hanti p q (Nat.lt_succ_of_lt hp) (Nat.lt_succ_of_lt hq))
      (fun p hp => hdiag p (Nat.lt_succ_of_lt hp))
    rw [hsub, CommRing.zero_add, ← sumR_add]
    have hzero : sumR n (fun p => f p n + f n p) = sumR n (fun _ => (0 : R)) := by
      apply sumR_congr; intro p hp
      rw [hanti p n (Nat.lt_succ_of_lt hp) (Nat.lt_succ_self n), neg_add]
    rw [hzero, sumR_zero_fn]

theorem sumR_sub {R : Type} [CommRing R] (n : Nat) (f g : Nat → R) :
    sumR n (fun i => f i - g i) = sumR n f - sumR n g := by
  rw [CommRing.sub_eq, ← sumR_neg, ← sumR_add]
  exact sumR_congr (fun i _ => CommRing.sub_eq (f i) (g i))

theorem matMulF_sub_right {R : Type} [CommRing R] (k : Nat) (A B C : Nat → Nat → R) (i j : Nat) :
    matMulF k A (matSub B C) i j = matMulF k A B i j - matMulF k A C i j := by
  unfold matMulF matSub
  rw [← sumR_sub]
  exact sumR_congr (fun t _ => mul_sub_r (A i t) (B t j) (C t j))

/-- Matrix commutator `[A, B] = A B - B A`. -/
def matComm {R : Type} [CommRing R] (m : Nat) (A B : Nat → Nat → R) : Nat → Nat → R :=
  matSub (matMulF m A B) (matMulF m B A)

/-- Ring homomorphism structure between `CommRing`s. -/
structure RingHom (R S : Type) [CommRing R] [CommRing S] where
  toFun : R → S
  map_zero : toFun 0 = 0
  map_one : toFun 1 = 1
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_neg : ∀ a, toFun (-a) = -(toFun a)
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b

theorem RingHom.map_sub {R S : Type} [CommRing R] [CommRing S] (φ : RingHom R S) (a b : R) :
    φ.toFun (a - b) = φ.toFun a - φ.toFun b := by
  rw [CommRing.sub_eq, CommRing.sub_eq, φ.map_add, φ.map_neg]

theorem RingHom.map_sumR {R S : Type} [CommRing R] [CommRing S] (φ : RingHom R S)
    (n : Nat) (f : Nat → R) :
    φ.toFun (sumR n f) = sumR n (fun i => φ.toFun (f i)) := by
  induction n with
  | zero => exact φ.map_zero
  | succ k ih => simp only [sumR, φ.map_add, ih]

theorem RingHom.map_matMulF {R S : Type} [CommRing R] [CommRing S] (φ : RingHom R S)
    (k : Nat) (A B : Nat → Nat → R) (i j : Nat) :
    φ.toFun (matMulF k A B i j) = matMulF k (fun r c => φ.toFun (A r c)) (fun r c => φ.toFun (B r c)) i j := by
  unfold matMulF
  rw [φ.map_sumR]
  exact sumR_congr (fun t _ => φ.map_mul (A i t) (B t j))

theorem RingHom.map_matIdF {R S : Type} [CommRing R] [CommRing S] (φ : RingHom R S) (i j : Nat) :
    φ.toFun (matIdF (R := R) i j) = matIdF (R := S) i j := by
  unfold matIdF
  by_cases h : i = j
  · rw [ite_t h, ite_t h, φ.map_one]
  · rw [ite_f h, ite_f h, φ.map_zero]

theorem RingHom.map_isMatInv {R S : Type} [CommRing R] [CommRing S] (φ : RingHom R S)
    {d : Nat} {A Ainv : Nat → Nat → R} (h : IsMatInv d A Ainv) :
    IsMatInv d (fun r c => φ.toFun (A r c)) (fun r c => φ.toFun (Ainv r c)) := by
  constructor
  · intro i j hi hj
    rw [← φ.map_matMulF, h.1 i j hi hj, φ.map_matIdF]
  · intro i j hi hj
    rw [← φ.map_matMulF, h.2 i j hi hj, φ.map_matIdF]

-- ============================================================================
-- Section 1: Univariate Polynomials `Poly F` & Rational Function Field `RatFunc F`
-- ============================================================================

structure Poly (F : Type) where
  bound : Nat
  coeff : Nat → F

def pAt {F : Type} [SimpleField F] (p : Poly F) (k : Nat) : F :=
  if k < p.bound then p.coeff k else 0

def pEq {F : Type} [SimpleField F] (p q : Poly F) : Prop :=
  ∀ k, pAt p k = pAt q k

def pZero {F : Type} [SimpleField F] : Poly F := ⟨0, fun _ => 0⟩
def pOne {F : Type} [SimpleField F] : Poly F := ⟨1, fun _ => 1⟩
def pConst {F : Type} [SimpleField F] (c : F) : Poly F := ⟨1, fun _ => c⟩
def pMono {F : Type} [SimpleField F] (d : Nat) : Poly F := ⟨d + 1, fun k => if k = d then 1 else 0⟩

def pAdd {F : Type} [SimpleField F] (p q : Poly F) : Poly F :=
  ⟨max p.bound q.bound, fun k => pAt p k + pAt q k⟩

def pNeg {F : Type} [SimpleField F] (p : Poly F) : Poly F :=
  ⟨p.bound, fun k => -(pAt p k)⟩

def pMul {F : Type} [SimpleField F] (p q : Poly F) : Poly F :=
  ⟨p.bound + q.bound, fun k => sumR (k + 1) (fun i => pAt p i * pAt q (k - i))⟩

def pNonZero {F : Type} [SimpleField F] (p : Poly F) : Prop :=
  ∃ k, pAt p k ≠ 0

theorem pAt_pZero {F : Type} [SimpleField F] (k : Nat) : pAt (pZero (F := F)) k = 0 := by
  unfold pAt pZero; simp

theorem pAt_pOne {F : Type} [SimpleField F] (k : Nat) :
    pAt (pOne (F := F)) k = if k = 0 then 1 else 0 := by
  unfold pAt pOne
  cases k with
  | zero => simp
  | succ _ => simp

theorem pAt_pConst {F : Type} [SimpleField F] (c : F) (k : Nat) :
    pAt (pConst c) k = if k = 0 then c else 0 := by
  unfold pAt pConst
  cases k with
  | zero => simp
  | succ _ => simp

theorem pAt_pMono {F : Type} [SimpleField F] (d k : Nat) :
    pAt (pMono (F := F) d) k = if k = d then 1 else 0 := by
  unfold pAt pMono
  by_cases hk : k = d
  · subst hk; simp
  · by_cases hlt : k < d + 1
    · simp [hlt, hk]
    · simp [hlt, hk]

theorem pAt_pAdd {F : Type} [SimpleField F] (p q : Poly F) (k : Nat) :
    pAt (pAdd p q) k = pAt p k + pAt q k := by
  change (if k < max p.bound q.bound then pAt p k + pAt q k else 0) = pAt p k + pAt q k
  by_cases h : k < max p.bound q.bound
  · rw [ite_t h]
  · rw [ite_f h]
    have h1 : ¬ (k < p.bound) := by omega
    have h2 : ¬ (k < q.bound) := by omega
    unfold pAt
    rw [ite_f h1, ite_f h2, add_zero]

theorem pAt_pNeg {F : Type} [SimpleField F] (p : Poly F) (k : Nat) :
    pAt (pNeg p) k = -(pAt p k) := by
  change (if k < p.bound then -(pAt p k) else 0) = -(pAt p k)
  by_cases h : k < p.bound
  · rw [ite_t h]
  · rw [ite_f h]
    unfold pAt
    rw [ite_f h, neg_zero]

theorem pAt_pMul {F : Type} [SimpleField F] (p q : Poly F) (k : Nat) :
    pAt (pMul p q) k = sumR (k + 1) (fun i => pAt p i * pAt q (k - i)) := by
  change (if k < p.bound + q.bound then sumR (k + 1) (fun i => pAt p i * pAt q (k - i)) else 0) =
    sumR (k + 1) (fun i => pAt p i * pAt q (k - i))
  by_cases h : k < p.bound + q.bound
  · rw [ite_t h]
  · rw [ite_f h]
    symm
    have hz : sumR (k + 1) (fun i => pAt p i * pAt q (k - i)) = sumR (k + 1) (fun _ => (0 : F)) := by
      apply sumR_congr; intro i hi
      by_cases hip : i < p.bound
      · have hkq : ¬ (k - i < q.bound) := by omega
        unfold pAt; rw [ite_f hkq, mul_zero]
      · unfold pAt; rw [ite_f hip, zero_mul]
    rw [hz, sumR_zero_fn]

theorem pEq_refl {F : Type} [SimpleField F] (p : Poly F) : pEq p p := fun _ => rfl
theorem pEq_symm {F : Type} [SimpleField F] {p q : Poly F} (h : pEq p q) : pEq q p := fun k => (h k).symm
theorem pEq_trans {F : Type} [SimpleField F] {p q r : Poly F} (h1 : pEq p q) (h2 : pEq q r) : pEq p r :=
  fun k => (h1 k).trans (h2 k)

theorem pAdd_congr {F : Type} [SimpleField F] {p1 p2 q1 q2 : Poly F}
    (hp : pEq p1 p2) (hq : pEq q1 q2) : pEq (pAdd p1 q1) (pAdd p2 q2) := by
  intro k; rw [pAt_pAdd, pAt_pAdd, hp k, hq k]

theorem pNeg_congr {F : Type} [SimpleField F] {p1 p2 : Poly F} (hp : pEq p1 p2) :
    pEq (pNeg p1) (pNeg p2) := by
  intro k; rw [pAt_pNeg, pAt_pNeg, hp k]

theorem pMul_congr {F : Type} [SimpleField F] {p1 p2 q1 q2 : Poly F}
    (hp : pEq p1 p2) (hq : pEq q1 q2) : pEq (pMul p1 q1) (pMul p2 q2) := by
  intro k; rw [pAt_pMul, pAt_pMul]
  exact sumR_congr (fun i _ => by rw [hp i, hq (k - i)])

theorem pAdd_assoc {F : Type} [SimpleField F] (a b c : Poly F) :
    pEq (pAdd (pAdd a b) c) (pAdd a (pAdd b c)) := by
  intro k; simp only [pAt_pAdd, CommRing.add_assoc]

theorem pAdd_comm {F : Type} [SimpleField F] (a b : Poly F) :
    pEq (pAdd a b) (pAdd b a) := by
  intro k; simp only [pAt_pAdd, CommRing.add_comm]

theorem pZero_add {F : Type} [SimpleField F] (a : Poly F) :
    pEq (pAdd pZero a) a := by
  intro k; rw [pAt_pAdd, pAt_pZero, CommRing.zero_add]

theorem pAdd_neg {F : Type} [SimpleField F] (a : Poly F) :
    pEq (pAdd a (pNeg a)) pZero := by
  intro k; rw [pAt_pAdd, pAt_pNeg, pAt_pZero, CommRing.add_neg]

theorem pMul_comm {F : Type} [SimpleField F] (a b : Poly F) :
    pEq (pMul a b) (pMul b a) := by
  intro k
  rw [pAt_pMul, pAt_pMul, ← sumR_rev (k + 1) (fun i => pAt a i * pAt b (k - i))]
  apply sumR_congr; intro i hi
  have h1 : k + 1 - 1 - i = k - i := by omega
  have h2 : k - (k - i) = i := by omega
  rw [h1, h2, CommRing.mul_comm]

theorem pOne_mul {F : Type} [SimpleField F] (a : Poly F) :
    pEq (pMul pOne a) a := by
  intro k
  rw [pAt_pMul]
  have h : sumR (k + 1) (fun i => pAt pOne i * pAt a (k - i)) =
      sumR (k + 1) (fun i => if i = 0 then pAt a k else 0) := by
    apply sumR_congr; intro i _
    rw [pAt_pOne]
    by_cases hi : i = 0
    · subst hi; simp [CommRing.one_mul]
    · simp [hi, zero_mul]
  rw [h, sumR_single (k + 1) 0 (pAt a k) (Nat.zero_lt_succ k)]

theorem pZero_mul {F : Type} [SimpleField F] (a : Poly F) :
    pEq (pMul pZero a) pZero := by
  intro k; rw [pAt_pMul, pAt_pZero]
  have h : sumR (k + 1) (fun i => pAt pZero i * pAt a (k - i)) = sumR (k + 1) (fun _ => (0 : F)) :=
    sumR_congr (fun i _ => by rw [pAt_pZero, zero_mul])
  rw [h, sumR_zero_fn]

theorem pLeft_distrib {F : Type} [SimpleField F] (a b c : Poly F) :
    pEq (pMul a (pAdd b c)) (pAdd (pMul a b) (pMul a c)) := by
  intro k
  rw [pAt_pMul, pAt_pAdd, pAt_pMul, pAt_pMul, ← sumR_add]
  exact sumR_congr (fun i _ => by rw [pAt_pAdd, CommRing.left_distrib])

theorem pRight_distrib {F : Type} [SimpleField F] (a b c : Poly F) :
    pEq (pMul (pAdd a b) c) (pAdd (pMul a c) (pMul b c)) :=
  pEq_trans (pMul_comm _ _) (pEq_trans (pLeft_distrib _ _ _) (pAdd_congr (pMul_comm _ _) (pMul_comm _ _)))

theorem pMul_neg {F : Type} [SimpleField F] (a b : Poly F) :
    pEq (pMul a (pNeg b)) (pNeg (pMul a b)) := by
  intro k; rw [pAt_pMul, pAt_pNeg, pAt_pMul, ← sumR_neg]
  exact sumR_congr (fun i _ => by rw [pAt_pNeg, mul_neg])

theorem pNeg_mul {F : Type} [SimpleField F] (a b : Poly F) :
    pEq (pMul (pNeg a) b) (pNeg (pMul a b)) :=
  pEq_trans (pMul_comm _ _) (pEq_trans (pMul_neg _ _) (pNeg_congr (pMul_comm _ _)))

theorem pMul_assoc {F : Type} [SimpleField F] (a b c : Poly F) :
    pEq (pMul (pMul a b) c) (pMul a (pMul b c)) := by
  intro k
  rw [pAt_pMul, pAt_pMul]
  have hL : sumR (k + 1) (fun i => pAt (pMul a b) i * pAt c (k - i)) =
      sumR (k + 1) (fun i => sumR (k + 1) (fun j => if j ≤ i then pAt a j * pAt b (i - j) * pAt c (k - i) else 0)) := by
    apply sumR_congr; intro i hi
    rw [pAt_pMul, sumR_mul_right]
    have hsplit : k + 1 = (i + 1) + (k - i) := by omega
    have hR : sumR (k + 1) (fun j => if j ≤ i then pAt a j * pAt b (i - j) * pAt c (k - i) else 0) =
        sumR (i + 1) (fun j => if j ≤ i then pAt a j * pAt b (i - j) * pAt c (k - i) else 0) +
        sumR (k - i) (fun t => if i + 1 + t ≤ i then pAt a (i + 1 + t) * pAt b (i - (i + 1 + t)) * pAt c (k - i) else 0) := by
      rw [hsplit, sumR_split (i + 1) (k - i)]
    rw [hR]
    have h1 : sumR (i + 1) (fun j => if j ≤ i then pAt a j * pAt b (i - j) * pAt c (k - i) else 0) =
        sumR (i + 1) (fun j => pAt a j * pAt b (i - j) * pAt c (k - i)) :=
      sumR_congr (fun j hj => ite_t (by omega))
    have h2 : sumR (k - i) (fun t => if i + 1 + t ≤ i then pAt a (i + 1 + t) * pAt b (i - (i + 1 + t)) * pAt c (k - i) else 0) = 0 := by
      rw [sumR_congr (fun t _ => ite_f (by omega)), sumR_zero_fn]
    rw [h1, h2, add_zero]
  rw [hL, sumR_swap]
  apply sumR_congr; intro j hj
  rw [pAt_pMul, sumR_mul_left]
  have hsplit : k + 1 = j + (k - j + 1) := by omega
  have hL2 : sumR (k + 1) (fun i => if j ≤ i then pAt a j * pAt b (i - j) * pAt c (k - i) else 0) =
      sumR j (fun i => if j ≤ i then pAt a j * pAt b (i - j) * pAt c (k - i) else 0) +
      sumR (k - j + 1) (fun t => if j ≤ j + t then pAt a j * pAt b (j + t - j) * pAt c (k - (j + t)) else 0) := by
    rw [hsplit, sumR_split j (k - j + 1)]
  rw [hL2]
  have h1 : sumR j (fun i => if j ≤ i then pAt a j * pAt b (i - j) * pAt c (k - i) else 0) = 0 := by
    rw [sumR_congr (fun i hi => ite_f (by omega)), sumR_zero_fn]
  rw [h1, CommRing.zero_add]
  apply sumR_congr; intro t _
  have hle : j ≤ j + t := by omega
  rw [ite_t hle]
  have hs1 : j + t - j = t := by omega
  have hs2 : k - (j + t) = k - j - t := by omega
  rw [hs1, hs2, CommRing.mul_assoc]

theorem pOne_nz {F : Type} [SimpleField F] : pNonZero (pOne (F := F)) :=
  ⟨0, by rw [pAt_pOne]; simp [Ne.symm SimpleField.zero_ne_one]⟩

theorem pNonZero_congr {F : Type} [SimpleField F] {p q : Poly F} (h : pEq p q) :
    pNonZero p ↔ pNonZero q :=
  ⟨fun ⟨k, hk⟩ => ⟨k, by rw [← h k]; exact hk⟩, fun ⟨k, hk⟩ => ⟨k, by rw [h k]; exact hk⟩⟩

/-- Integral domain: product of nonzero polynomials over any `SimpleField F` is nonzero. -/
theorem pMul_ne_zero {F : Type} [SimpleField F] {p q : Poly F}
    (hp : pNonZero p) (hq : pNonZero q) : pNonZero (pMul p q) := by
  have hmax : ∀ (f : Poly F), pNonZero f → ∃ d, pAt f d ≠ 0 ∧ ∀ k, d < k → pAt f k = 0 := by
    intro f hf
    have haux : ∀ n : Nat, (∃ k, k < n ∧ pAt f k ≠ 0) → (∀ k, n ≤ k → pAt f k = 0) →
        ∃ d, pAt f d ≠ 0 ∧ ∀ k, d < k → pAt f k = 0 := by
      intro n
      induction n with
      | zero => intro ⟨_, hk, _⟩ _; omega
      | succ m ih =>
        intro hex hvan
        by_cases hm : pAt f m = 0
        · apply ih
          · obtain ⟨k, hk, hknz⟩ := hex
            by_cases hkm : k = m
            · subst hkm; exact absurd hm hknz
            · exact ⟨k, by omega, hknz⟩
          · intro k hk
            by_cases hkm : k = m
            · subst hkm; exact hm
            · exact hvan k (by omega)
        · exact ⟨m, hm, fun k hk => hvan k (by omega)⟩
    obtain ⟨k0, hk0⟩ := hf
    have hk0_lt : k0 < f.bound := Classical.byContradiction fun hge => by
      unfold pAt at hk0
      rw [ite_f hge] at hk0
      exact hk0 rfl
    exact haux f.bound ⟨k0, hk0_lt, hk0⟩ (fun k hk => by unfold pAt; exact ite_f (by omega))
  obtain ⟨dp, hdp_nz, hdp_max⟩ := hmax p hp
  obtain ⟨dq, hdq_nz, hdq_max⟩ := hmax q hq
  refine ⟨dp + dq, ?_⟩
  rw [pAt_pMul]
  have hsingle : sumR (dp + dq + 1) (fun i => pAt p i * pAt q (dp + dq - i)) =
      sumR (dp + dq + 1) (fun i => if i = dp then pAt p dp * pAt q dq else 0) := by
    apply sumR_congr; intro i _
    by_cases hid : i = dp
    · rw [hid]
      have hsub : dp + dq - dp = dq := by omega
      rw [ite_t rfl, hsub]
    · rw [ite_f hid]
      by_cases hgt : dp < i
      · rw [hdp_max i hgt, zero_mul]
      · rw [hdq_max (dp + dq - i) (by omega), mul_zero]
  rw [hsingle, sumR_single (dp + dq + 1) dp _ (by omega)]
  exact field_mul_ne_zero hdp_nz hdq_nz

theorem pEq_zero_of_not_nz {F : Type} [SimpleField F] {p : Poly F} (h : ¬ pNonZero p) : pEq p pZero := by
  intro k
  rw [pAt_pZero]
  exact Classical.byContradiction fun hne => h ⟨k, hne⟩

theorem pMul_cancel_right {F : Type} [SimpleField F] {a b c : Poly F}
    (hc : pNonZero c) (h : pEq (pMul a c) (pMul b c)) : pEq a b := by
  let diff := pAdd a (pNeg b)
  have h0 : pEq (pMul diff c) pZero := by
    have h1 := pRight_distrib a (pNeg b) c
    have h2 := pAdd_congr h (pNeg_mul b c)
    intro k
    rw [h1 k, h2 k, pAt_pAdd, pAt_pNeg, CommRing.add_neg, pAt_pZero]
  have hdiff0 : ¬ pNonZero diff := by
    intro hnz
    obtain ⟨k, hk⟩ := pMul_ne_zero hnz hc
    rw [h0 k, pAt_pZero] at hk
    exact hk rfl
  intro k
  have hk := pEq_zero_of_not_nz hdiff0 k
  rw [pAt_pAdd, pAt_pNeg, pAt_pZero] at hk
  exact eq_of_sub_eq_zero (by rw [CommRing.sub_eq]; exact hk)

structure RawFrac (F : Type) [SimpleField F] where
  num : Poly F
  den : Poly F
  den_nz : pNonZero den

def ratRel {F : Type} [SimpleField F] (a b : RawFrac F) : Prop :=
  pEq (pMul a.num b.den) (pMul b.num a.den)

theorem ratRel_equiv {F : Type} [SimpleField F] : Equivalence (ratRel (F := F)) where
  refl _ := pEq_refl _
  symm h := pEq_symm h
  trans {a b c} h1 h2 := by
    apply pMul_cancel_right b.den_nz
    have s1 : pEq (pMul (pMul a.num c.den) b.den) (pMul (pMul a.num b.den) c.den) :=
      pEq_trans (pMul_assoc _ _ _) (pEq_trans (pMul_congr (pEq_refl _) (pMul_comm _ _)) (pEq_symm (pMul_assoc _ _ _)))
    have s2 : pEq (pMul (pMul a.num b.den) c.den) (pMul (pMul b.num a.den) c.den) :=
      pMul_congr h1 (pEq_refl _)
    have s3 : pEq (pMul (pMul b.num a.den) c.den) (pMul (pMul b.num c.den) a.den) :=
      pEq_trans (pMul_assoc _ _ _) (pEq_trans (pMul_congr (pEq_refl _) (pMul_comm _ _)) (pEq_symm (pMul_assoc _ _ _)))
    have s4 : pEq (pMul (pMul b.num c.den) a.den) (pMul (pMul c.num b.den) a.den) :=
      pMul_congr h2 (pEq_refl _)
    have s5 : pEq (pMul (pMul c.num b.den) a.den) (pMul (pMul c.num a.den) b.den) :=
      pEq_trans (pMul_assoc _ _ _) (pEq_trans (pMul_congr (pEq_refl _) (pMul_comm _ _)) (pEq_symm (pMul_assoc _ _ _)))
    exact pEq_trans s1 (pEq_trans s2 (pEq_trans s3 (pEq_trans s4 s5)))

def rawFracSetoid (F : Type) [SimpleField F] : Setoid (RawFrac F) :=
  ⟨ratRel, ratRel_equiv⟩

/-- Field of univariate rational functions `F(t)` over ANY `SimpleField F`. -/
def RatFunc (F : Type) [SimpleField F] : Type :=
  Quotient (rawFracSetoid F)

def ratMk {F : Type} [SimpleField F] (a : RawFrac F) : RatFunc F :=
  Quotient.mk (rawFracSetoid F) a

def ratAddRaw {F : Type} [SimpleField F] (a b : RawFrac F) : RawFrac F :=
  ⟨pAdd (pMul a.num b.den) (pMul b.num a.den), pMul a.den b.den, pMul_ne_zero a.den_nz b.den_nz⟩

def ratNegRaw {F : Type} [SimpleField F] (a : RawFrac F) : RawFrac F :=
  ⟨pNeg a.num, a.den, a.den_nz⟩

def ratMulRaw {F : Type} [SimpleField F] (a b : RawFrac F) : RawFrac F :=
  ⟨pMul a.num b.num, pMul a.den b.den, pMul_ne_zero a.den_nz b.den_nz⟩

noncomputable def ratInvRaw {F : Type} [SimpleField F] (a : RawFrac F) : RawFrac F :=
  @dite _ (pNonZero a.num) (Classical.propDecidable _)
    (fun h => ⟨a.den, a.num, h⟩)
    (fun _ => ⟨pZero, pOne, pOne_nz⟩)

theorem ratAddRaw_resp {F : Type} [SimpleField F] {a1 a2 b1 b2 : RawFrac F}
    (ha : ratRel a1 a2) (hb : ratRel b1 b2) : ratRel (ratAddRaw a1 b1) (ratAddRaw a2 b2) := by
  unfold ratRel ratAddRaw
  dsimp only
  have hL : pEq (pMul (pAdd (pMul a1.num b1.den) (pMul b1.num a1.den)) (pMul a2.den b2.den))
      (pAdd (pMul (pMul a1.num a2.den) (pMul b1.den b2.den))
            (pMul (pMul b1.num b2.den) (pMul a1.den a2.den))) := by
    apply pEq_trans (pRight_distrib _ _ _)
    apply pAdd_congr
    · intro k
      have e := pEq_trans (pMul_assoc a1.num b1.den (pMul a2.den b2.den))
        (pEq_trans (pMul_congr (pEq_refl _) (pEq_trans (pEq_symm (pMul_assoc b1.den a2.den b2.den))
          (pEq_trans (pMul_congr (pMul_comm b1.den a2.den) (pEq_refl _)) (pMul_assoc a2.den b1.den b2.den))))
          (pEq_symm (pMul_assoc a1.num a2.den (pMul b1.den b2.den))))
      exact e k
    · intro k
      have e := pEq_trans (pMul_assoc b1.num a1.den (pMul a2.den b2.den))
        (pEq_trans (pMul_congr (pEq_refl _) (pEq_trans (pEq_symm (pMul_assoc a1.den a2.den b2.den))
          (pMul_comm (pMul a1.den a2.den) b2.den)))
          (pEq_symm (pMul_assoc b1.num b2.den (pMul a1.den a2.den))))
      exact e k
  have hR : pEq (pMul (pAdd (pMul a2.num b2.den) (pMul b2.num a2.den)) (pMul a1.den b1.den))
      (pAdd (pMul (pMul a2.num a1.den) (pMul b1.den b2.den))
            (pMul (pMul b2.num b1.den) (pMul a1.den a2.den))) := by
    apply pEq_trans (pRight_distrib _ _ _)
    apply pAdd_congr
    · intro k
      have e := pEq_trans (pMul_assoc a2.num b2.den (pMul a1.den b1.den))
        (pEq_trans (pMul_congr (pEq_refl _) (pEq_trans (pEq_symm (pMul_assoc b2.den a1.den b1.den))
          (pEq_trans (pMul_congr (pMul_comm b2.den a1.den) (pEq_refl _))
            (pEq_trans (pMul_assoc a1.den b2.den b1.den) (pMul_congr (pEq_refl _) (pMul_comm b2.den b1.den))))))
          (pEq_symm (pMul_assoc a2.num a1.den (pMul b1.den b2.den))))
      exact e k
    · intro k
      have e := pEq_trans (pMul_assoc b2.num a2.den (pMul a1.den b1.den))
        (pEq_trans (pMul_congr (pEq_refl _) (pEq_trans (pEq_symm (pMul_assoc a2.den a1.den b1.den))
          (pEq_trans (pMul_comm (pMul a2.den a1.den) b1.den) (pMul_congr (pEq_refl _) (pMul_comm a2.den a1.den)))))
          (pEq_symm (pMul_assoc b2.num b1.den (pMul a1.den a2.den))))
      exact e k
  exact pEq_trans hL (pEq_trans (pAdd_congr (pMul_congr ha (pEq_refl _)) (pMul_congr hb (pEq_refl _))) (pEq_symm hR))

theorem ratNegRaw_resp {F : Type} [SimpleField F] {a b : RawFrac F} (h : ratRel a b) :
    ratRel (ratNegRaw a) (ratNegRaw b) :=
  pEq_trans (pNeg_mul a.num b.den) (pEq_trans (pNeg_congr h) (pEq_symm (pNeg_mul b.num a.den)))

theorem ratMulRaw_resp {F : Type} [SimpleField F] {a1 a2 b1 b2 : RawFrac F}
    (ha : ratRel a1 a2) (hb : ratRel b1 b2) : ratRel (ratMulRaw a1 b1) (ratMulRaw a2 b2) := by
  unfold ratRel ratMulRaw
  dsimp only
  have hL : pEq (pMul (pMul a1.num b1.num) (pMul a2.den b2.den))
      (pMul (pMul a1.num a2.den) (pMul b1.num b2.den)) :=
    pEq_trans (pMul_assoc a1.num b1.num _)
      (pEq_trans (pMul_congr (pEq_refl _) (pEq_trans (pEq_symm (pMul_assoc b1.num a2.den b2.den))
        (pEq_trans (pMul_congr (pMul_comm b1.num a2.den) (pEq_refl _)) (pMul_assoc a2.den b1.num b2.den))))
        (pEq_symm (pMul_assoc a1.num a2.den _)))
  have hR : pEq (pMul (pMul a2.num b2.num) (pMul a1.den b1.den))
      (pMul (pMul a2.num a1.den) (pMul b2.num b1.den)) :=
    pEq_trans (pMul_assoc a2.num b2.num _)
      (pEq_trans (pMul_congr (pEq_refl _) (pEq_trans (pEq_symm (pMul_assoc b2.num a1.den b1.den))
        (pEq_trans (pMul_congr (pMul_comm b2.num a1.den) (pEq_refl _)) (pMul_assoc a1.den b2.num b1.den))))
        (pEq_symm (pMul_assoc a2.num a1.den _)))
  exact pEq_trans hL (pEq_trans (pMul_congr ha hb) (pEq_symm hR))

theorem ratInvRaw_resp {F : Type} [SimpleField F] {a b : RawFrac F} (h : ratRel a b) :
    ratRel (ratInvRaw a) (ratInvRaw b) := by
  have hiff : pNonZero a.num ↔ pNonZero b.num := by
    constructor
    · intro ha
      have h1 := (pNonZero_congr h).mp (pMul_ne_zero ha b.den_nz)
      exact Classical.byContradiction fun hb => by
        obtain ⟨k, hk⟩ := h1
        have hz := pMul_congr (pEq_zero_of_not_nz hb) (pEq_refl a.den) k
        rw [pZero_mul a.den k, pAt_pZero] at hz
        exact hk hz
    · intro hb
      have h1 := (pNonZero_congr h).mpr (pMul_ne_zero hb a.den_nz)
      exact Classical.byContradiction fun ha => by
        obtain ⟨k, hk⟩ := h1
        have hz := pMul_congr (pEq_zero_of_not_nz ha) (pEq_refl b.den) k
        rw [pZero_mul b.den k, pAt_pZero] at hz
        exact hk hz
  unfold ratInvRaw
  by_cases ha : pNonZero a.num
  · have hb : pNonZero b.num := hiff.mp ha
    simp only [ha, hb, ↓reduceDIte, ratRel]
    exact pEq_trans (pMul_comm a.den b.num) (pEq_trans (pEq_symm h) (pMul_comm a.num b.den))
  · have hb : ¬ pNonZero b.num := fun h' => ha (hiff.mpr h')
    simp only [ha, hb, ↓reduceDIte]
    exact pEq_refl _

noncomputable instance instSimpleFieldRatFunc (F : Type) [SimpleField F] : SimpleField (RatFunc F) where
  add := Quotient.lift₂ (fun a b => ratMk (ratAddRaw a b))
    (fun _ _ _ _ ha hb => Quotient.sound (ratAddRaw_resp ha hb))
  neg := Quotient.lift (fun a => ratMk (ratNegRaw a))
    (fun _ _ h => Quotient.sound (ratNegRaw_resp h))
  sub a b := Quotient.lift₂ (fun x y => ratMk (ratAddRaw x (ratNegRaw y)))
    (fun _ _ _ _ ha hb => Quotient.sound (ratAddRaw_resp ha (ratNegRaw_resp hb))) a b
  mul := Quotient.lift₂ (fun a b => ratMk (ratMulRaw a b))
    (fun _ _ _ _ ha hb => Quotient.sound (ratMulRaw_resp ha hb))
  zero := ratMk ⟨pZero, pOne, pOne_nz⟩
  one := ratMk ⟨pOne, pOne, pOne_nz⟩
  inv := Quotient.lift (fun a => ratMk (ratInvRaw a))
    (fun _ _ h => Quotient.sound (ratInvRaw_resp h))
  add_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun x y z => ?_
    apply Quotient.sound
    change ratRel _ _; unfold ratRel ratAddRaw; dsimp only
    have hL : pEq (pMul (pAdd (pMul (pAdd (pMul x.num y.den) (pMul y.num x.den)) z.den)
                               (pMul z.num (pMul x.den y.den)))
                        (pMul x.den (pMul y.den z.den)))
                  (pMul (pAdd (pAdd (pMul (pMul x.num y.den) z.den) (pMul (pMul y.num x.den) z.den))
                               (pMul z.num (pMul x.den y.den)))
                        (pMul (pMul x.den y.den) z.den)) :=
      pMul_congr (pAdd_congr (pRight_distrib _ _ _) (pEq_refl _)) (pEq_symm (pMul_assoc _ _ _))
    have hR : pEq (pMul (pAdd (pMul x.num (pMul y.den z.den))
                               (pMul (pAdd (pMul y.num z.den) (pMul z.num y.den)) x.den))
                        (pMul (pMul x.den y.den) z.den))
                  (pMul (pAdd (pMul (pMul x.num y.den) z.den)
                               (pAdd (pMul (pMul y.num x.den) z.den) (pMul z.num (pMul x.den y.den))))
                        (pMul (pMul x.den y.den) z.den)) := by
      apply pMul_congr _ (pEq_refl _)
      apply pAdd_congr (pEq_symm (pMul_assoc _ _ _))
      apply pEq_trans (pRight_distrib _ _ _)
      apply pAdd_congr
      · exact pEq_trans (pMul_assoc y.num z.den x.den)
          (pEq_trans (pMul_congr (pEq_refl _) (pMul_comm z.den x.den)) (pEq_symm (pMul_assoc y.num x.den z.den)))
      · exact pEq_trans (pMul_assoc z.num y.den x.den) (pMul_congr (pEq_refl _) (pMul_comm y.den x.den))
    exact pEq_trans hL (pEq_trans (pMul_congr (pAdd_assoc _ _ _) (pEq_refl _)) (pEq_symm hR))
  add_comm a b := by
    refine Quotient.inductionOn₂ a b fun x y => ?_
    apply Quotient.sound
    change ratRel _ _; unfold ratRel ratAddRaw; dsimp only
    exact pMul_congr (pAdd_comm _ _) (pMul_comm _ _)
  zero_add a := by
    refine Quotient.inductionOn a fun x => ?_
    apply Quotient.sound
    change ratRel _ _; unfold ratRel ratAddRaw; dsimp only
    apply pEq_trans (pMul_congr (pEq_trans (pAdd_congr (pZero_mul _) (pMul_comm _ _))
      (pEq_trans (pZero_add _) (pOne_mul _))) (pEq_refl _))
    exact pMul_congr (pEq_refl _) (pEq_symm (pOne_mul _))
  add_neg a := by
    refine Quotient.inductionOn a fun x => ?_
    apply Quotient.sound
    change ratRel _ _; unfold ratRel ratAddRaw ratNegRaw; dsimp only
    have hnum : pEq (pAdd (pMul x.num x.den) (pMul (pNeg x.num) x.den)) pZero :=
      pEq_trans (pAdd_congr (pEq_refl _) (pNeg_mul _ _)) (pAdd_neg _)
    exact pEq_trans (pMul_congr hnum (pEq_refl _)) (pEq_trans (pZero_mul _) (pEq_symm (pZero_mul _)))
  sub_eq a b := by
    refine Quotient.inductionOn₂ a b fun _ _ => rfl
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun x y z => ?_
    apply Quotient.sound
    change ratRel _ _; unfold ratRel ratMulRaw; dsimp only
    exact pMul_congr (pMul_assoc _ _ _) (pEq_symm (pMul_assoc _ _ _))
  mul_comm a b := by
    refine Quotient.inductionOn₂ a b fun x y => ?_
    apply Quotient.sound
    change ratRel _ _; unfold ratRel ratMulRaw; dsimp only
    exact pMul_congr (pMul_comm _ _) (pMul_comm _ _)
  one_mul a := by
    refine Quotient.inductionOn a fun x => ?_
    apply Quotient.sound
    change ratRel _ _; unfold ratRel ratMulRaw; dsimp only
    exact pMul_congr (pOne_mul _) (pEq_symm (pOne_mul _))
  left_distrib a b c := by
    refine Quotient.inductionOn₃ a b c fun x y z => ?_
    apply Quotient.sound
    change ratRel _ _; unfold ratRel ratMulRaw ratAddRaw; dsimp only
    have h1 : pEq (pMul (pMul x.num (pAdd (pMul y.num z.den) (pMul z.num y.den)))
                        (pMul (pMul x.den y.den) (pMul x.den z.den)))
                  (pMul (pAdd (pMul (pMul x.num y.num) (pMul x.den z.den))
                              (pMul (pMul x.num z.num) (pMul x.den y.den)))
                        (pMul x.den (pMul y.den z.den))) := by
      have hL : pEq (pMul (pMul x.num (pAdd (pMul y.num z.den) (pMul z.num y.den)))
                          (pMul (pMul x.den y.den) (pMul x.den z.den)))
                    (pAdd (pMul (pMul x.num (pMul y.num z.den)) (pMul (pMul x.den y.den) (pMul x.den z.den)))
                          (pMul (pMul x.num (pMul z.num y.den)) (pMul (pMul x.den y.den) (pMul x.den z.den)))) :=
        pEq_trans (pMul_congr (pLeft_distrib _ _ _) (pEq_refl _)) (pRight_distrib _ _ _)
      have hR : pEq (pMul (pAdd (pMul (pMul x.num y.num) (pMul x.den z.den))
                                (pMul (pMul x.num z.num) (pMul x.den y.den)))
                          (pMul x.den (pMul y.den z.den)))
                    (pAdd (pMul (pMul (pMul x.num y.num) (pMul x.den z.den)) (pMul x.den (pMul y.den z.den)))
                          (pMul (pMul (pMul x.num z.num) (pMul x.den y.den)) (pMul x.den (pMul y.den z.den)))) :=
        pRight_distrib _ _ _
      apply pEq_trans hL (pEq_trans _ (pEq_symm hR))
      -- Helper to rearrange 5-factor polynomial products cleanly via associativity + commutativity
      have hswap4 : ∀ u v w t : Poly F, pEq (pMul (pMul u v) (pMul w t)) (pMul (pMul u w) (pMul v t)) := fun u v w t =>
        pEq_trans (pMul_assoc u v _)
          (pEq_trans (pMul_congr (pEq_refl _) (pEq_trans (pEq_symm (pMul_assoc v w t))
            (pEq_trans (pMul_congr (pMul_comm v w) (pEq_refl _)) (pMul_assoc w v t))))
            (pEq_symm (pMul_assoc u w _)))
      apply pAdd_congr
      · exact pEq_trans (pMul_congr (pEq_symm (pMul_assoc _ _ _)) (pMul_comm _ _))
          (pEq_trans (hswap4 (pMul x.num y.num) z.den (pMul x.den z.den) (pMul x.den y.den))
            (pMul_congr (pEq_refl _) (pEq_trans (pMul_comm z.den (pMul x.den y.den)) (pMul_assoc x.den y.den z.den))))
      · exact pEq_trans (pMul_congr (pEq_symm (pMul_assoc _ _ _)) (pEq_refl _))
          (pEq_trans (hswap4 (pMul x.num z.num) y.den (pMul x.den y.den) (pMul x.den z.den))
            (pMul_congr (pEq_refl _) (pEq_trans (pEq_symm (pMul_assoc y.den x.den z.den))
              (pEq_trans (pMul_congr (pMul_comm y.den x.den) (pEq_refl _)) (pMul_assoc x.den y.den z.den)))))
    exact h1
  zero_ne_one := by
    intro h
    have hr : ratRel (F := F) ⟨pZero, pOne, pOne_nz⟩ ⟨pOne, pOne, pOne_nz⟩ := Quotient.exact h
    have h0 := hr 0
    rw [pZero_mul pOne 0, pOne_mul pOne 0, pAt_pZero, pAt_pOne] at h0
    simp only [↓reduceIte] at h0
    exact SimpleField.zero_ne_one h0
  mul_inv_cancel a ha := by
    revert ha
    refine Quotient.inductionOn a fun x hx => ?_
    have hnz : pNonZero x.num := Classical.byContradiction fun hz => by
      apply hx
      apply Quotient.sound
      change ratRel _ _; unfold ratRel; dsimp only
      exact pEq_trans (pMul_congr (pEq_zero_of_not_nz hz) (pEq_refl _))
        (pEq_trans (pZero_mul _) (pEq_symm (pZero_mul _)))
    apply Quotient.sound
    change ratRel _ _; unfold ratRel ratMulRaw ratInvRaw
    simp only [hnz, ↓reduceDIte]
    exact pEq_trans (pMul_comm _ pOne) (pEq_trans (pOne_mul _)
      (pEq_trans (pMul_comm x.num x.den) (pEq_symm (pOne_mul _))))

/-- Ring homomorphism `ratConstHom : F → RatFunc F` embedding constants into `F(t)`. -/
def ratConst {F : Type} [SimpleField F] (c : F) : RatFunc F :=
  Quotient.mk (rawFracSetoid F) ⟨pConst c, pOne, pOne_nz⟩

/-- Embedding `ratPolyEmbed : Poly F → RatFunc F`. -/
def ratPolyEmbed {F : Type} [SimpleField F] (p : Poly F) : RatFunc F :=
  Quotient.mk (rawFracSetoid F) ⟨p, pOne, pOne_nz⟩

theorem ratPolyEmbed_add {F : Type} [SimpleField F] (p q : Poly F) :
    ratPolyEmbed (pAdd p q) = ratPolyEmbed p + ratPolyEmbed q := by
  unfold ratPolyEmbed
  apply Quotient.sound
  change ratRel _ _; unfold ratRel ratAddRaw; dsimp only
  have h1 : pEq (pMul (pAdd p q) (pMul pOne pOne)) (pAdd p q) :=
    pEq_trans (pMul_comm _ _) (pEq_trans (pMul_congr (pOne_mul _) (pEq_refl _)) (pOne_mul _))
  have h2 : pEq (pMul (pAdd (pMul p pOne) (pMul q pOne)) pOne) (pAdd p q) :=
    pEq_trans (pMul_comm _ _) (pEq_trans (pOne_mul _)
      (pAdd_congr (pEq_trans (pMul_comm _ _) (pOne_mul _)) (pEq_trans (pMul_comm _ _) (pOne_mul _))))
  exact pEq_trans h1 (pEq_symm h2)

theorem ratPolyEmbed_neg {F : Type} [SimpleField F] (p : Poly F) :
    ratPolyEmbed (pNeg p) = -(ratPolyEmbed p) := rfl

theorem ratPolyEmbed_mul {F : Type} [SimpleField F] (p q : Poly F) :
    ratPolyEmbed (pMul p q) = ratPolyEmbed p * ratPolyEmbed q := by
  unfold ratPolyEmbed
  apply Quotient.sound
  change ratRel _ _; unfold ratRel ratMulRaw; dsimp only
  exact pEq_trans (pMul_congr (pEq_refl _) (pOne_mul _)) (pEq_refl _)

theorem ratPolyEmbed_zero {F : Type} [SimpleField F] :
    ratPolyEmbed (pZero (F := F)) = 0 := rfl

theorem ratPolyEmbed_one {F : Type} [SimpleField F] :
    ratPolyEmbed (pOne (F := F)) = 1 := rfl

theorem ratPolyEmbed_eq_zero {F : Type} [SimpleField F] {p : Poly F}
    (h : ratPolyEmbed p = 0) : ∀ k, pAt p k = 0 := by
  have hr : ratRel ⟨p, pOne, pOne_nz⟩ ⟨pZero, pOne, pOne_nz⟩ := Quotient.exact h
  intro k
  have hk := hr k
  rw [pMul_comm p pOne k, pOne_mul p k, pZero_mul pOne k, pAt_pZero] at hk
  exact hk

def ratConstHom (F : Type) [SimpleField F] : RingHom F (RatFunc F) where
  toFun := ratConst
  map_zero := by
    unfold ratConst
    apply Quotient.sound
    change ratRel _ _; unfold ratRel; dsimp only
    intro k; rw [pAt_pMul, pAt_pMul]
    apply sumR_congr; intro i _; rw [pAt_pConst, pAt_pZero]
    by_cases h : i = 0 <;> simp [h]
  map_one := by
    unfold ratConst
    apply Quotient.sound
    change ratRel _ _; unfold ratRel; dsimp only
    intro k; rw [pAt_pMul, pAt_pMul]
    apply sumR_congr; intro i _; rw [pAt_pConst, pAt_pOne, pAt_pOne]
  map_add a b := by
    change ratPolyEmbed (pConst (a + b)) = ratPolyEmbed (pConst a) + ratPolyEmbed (pConst b)
    rw [← ratPolyEmbed_add]
    unfold ratPolyEmbed
    apply Quotient.sound
    intro k; rw [pAt_pMul, pAt_pMul]
    apply sumR_congr; intro i _
    rw [pAt_pConst, pAt_pAdd, pAt_pConst, pAt_pConst]
    by_cases h : i = 0 <;> simp [h, add_zero]
  map_neg a := by
    change ratPolyEmbed (pConst (-a)) = -(ratPolyEmbed (pConst a))
    rw [← ratPolyEmbed_neg]
    unfold ratPolyEmbed
    apply Quotient.sound
    intro k; rw [pAt_pMul, pAt_pMul]
    apply sumR_congr; intro i _
    rw [pAt_pConst, pAt_pNeg, pAt_pConst]
    by_cases h : i = 0 <;> simp [h, neg_zero]
  map_mul a b := by
    change ratPolyEmbed (pConst (a * b)) = ratPolyEmbed (pConst a) * ratPolyEmbed (pConst b)
    rw [← ratPolyEmbed_mul]
    unfold ratPolyEmbed
    apply Quotient.sound
    intro k; rw [pAt_pMul, pAt_pMul]
    apply sumR_congr; intro i _
    have hpc : pAt (pMul (pConst a) (pConst b)) i = pAt (pConst (a * b)) i := by
      rw [pAt_pMul, pAt_pConst]
      cases i with
      | zero => simp [sumR, pAt_pConst, CommRing.zero_add]
      | succ i' =>
        have hz : sumR (i' + 2) (fun j => pAt (pConst a) j * pAt (pConst b) (i' + 1 - j)) =
            sumR (i' + 2) (fun _ => (0 : F)) := by
          apply sumR_congr; intro j _
          rw [pAt_pConst, pAt_pConst]
          by_cases hj : j = 0
          · subst hj; simp [mul_zero]
          · simp [hj, zero_mul]
        rw [hz, sumR_zero_fn]; simp
    rw [hpc]

-- ============================================================================
-- Section 2: Characteristic-Free Cofactor Determinant `detM` & Gauss-Jordan
-- ============================================================================

def minorMat {R : Type} (A : Nat → Nat → R) (col r c : Nat) : R :=
  A (r + 1) (skipIdx col c)

def detM {R : Type} [CommRing R] : Nat → (Nat → Nat → R) → R
  | 0, _ => 1
  | m + 1, A =>
    sumR (m + 1) (fun j => (if j % 2 = 0 then A 0 j else -(A 0 j)) * detM m (minorMat A j))

theorem detM_congr {R : Type} [CommRing R] :
    ∀ (m : Nat) {A B : Nat → Nat → R}, MatEq m m A B → detM m A = detM m B
  | 0, _, _, _ => rfl
  | m + 1, A, B, h => by
    simp only [detM]
    apply sumR_congr; intro j hj
    have h0 : A 0 j = B 0 j := h 0 j (Nat.zero_lt_succ m) hj
    have hmin : MatEq m m (minorMat A j) (minorMat B j) := by
      intro r c hr hc
      unfold minorMat skipIdx
      by_cases hcj : c < j
      · rw [ite_t hcj]; exact h (r + 1) c (by omega) (by omega)
      · rw [ite_f hcj]; exact h (r + 1) (c + 1) (by omega) (by omega)
    rw [h0, detM_congr m hmin]

theorem detM_map {R S : Type} [CommRing R] [CommRing S] (φ : RingHom R S) :
    ∀ (m : Nat) (A : Nat → Nat → R),
      φ.toFun (detM m A) = detM m (fun r c => φ.toFun (A r c))
  | 0, _ => φ.map_one
  | m + 1, A => by
    simp only [detM]
    rw [φ.map_sumR]
    apply sumR_congr; intro j _
    rw [φ.map_mul, detM_map φ m (minorMat A j)]
    congr 1
    by_cases h : j % 2 = 0
    · rw [ite_t h, ite_t h]
    · rw [ite_f h, ite_f h, φ.map_neg]

def setRow {R : Type} (r : Nat) (v : Nat → R) (A : Nat → Nat → R) (i j : Nat) : R :=
  if i = r then v j else A i j

theorem detM_row_add {R : Type} [CommRing R] :
    ∀ (m r : Nat) (v w : Nat → R) (A : Nat → Nat → R), r < m →
      detM m (setRow r (fun j => v j + w j) A) =
      detM m (setRow r v A) + detM m (setRow r w A)
  | 0, _, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | m + 1, 0, v, w, A, _ => by
    simp only [detM]
    rw [← sumR_add]
    apply sumR_congr; intro j _
    have hm1 : minorMat (setRow 0 (fun c => v c + w c) A) j = minorMat A j := by
      funext r c; unfold minorMat setRow; simp
    have hm2 : minorMat (setRow 0 v A) j = minorMat A j := by
      funext r c; unfold minorMat setRow; simp
    have hm3 : minorMat (setRow 0 w A) j = minorMat A j := by
      funext r c; unfold minorMat setRow; simp
    rw [hm1, hm2, hm3]
    unfold setRow; simp only [↓reduceIte]
    by_cases hj : j % 2 = 0
    · simp only [hj, ↓reduceIte, right_distrib]
    · simp only [hj, ↓reduceIte, neg_add_distrib, right_distrib]
  | m + 1, r + 1, v, w, A, hr => by
    simp only [detM]
    rw [← sumR_add]
    apply sumR_congr; intro j _
    have h0 : ∀ u : Nat → R, setRow (r + 1) u A 0 j = A 0 j := fun _ => by unfold setRow; simp
    rw [h0, h0, h0]
    have hmin : ∀ u : Nat → R, minorMat (setRow (r + 1) u A) j = setRow r (fun c => u (skipIdx j c)) (minorMat A j) := by
      intro u; funext i c; unfold minorMat setRow
      by_cases hi : i = r
      · subst hi; simp
      · simp [hi]
    rw [hmin, hmin, hmin, detM_row_add m r _ _ (minorMat A j) (by omega), CommRing.left_distrib]

theorem detM_row_scale {R : Type} [CommRing R] :
    ∀ (m r : Nat) (α : R) (v : Nat → R) (A : Nat → Nat → R), r < m →
      detM m (setRow r (fun j => α * v j) A) = α * detM m (setRow r v A)
  | 0, _, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | m + 1, 0, α, v, A, _ => by
    simp only [detM]
    rw [sumR_mul_left]
    apply sumR_congr; intro j _
    have hm1 : minorMat (setRow 0 (fun c => α * v c) A) j = minorMat A j := by
      funext r c; unfold minorMat setRow; simp
    have hm2 : minorMat (setRow 0 v A) j = minorMat A j := by
      funext r c; unfold minorMat setRow; simp
    rw [hm1, hm2]
    unfold setRow; simp only [↓reduceIte]
    by_cases hj : j % 2 = 0
    · simp only [hj, ↓reduceIte, CommRing.mul_assoc]
    · simp only [hj, ↓reduceIte, ← mul_neg, CommRing.mul_assoc]
  | m + 1, r + 1, α, v, A, hr => by
    simp only [detM]
    rw [sumR_mul_left]
    apply sumR_congr; intro j _
    have h0 : ∀ u : Nat → R, setRow (r + 1) u A 0 j = A 0 j := fun _ => by unfold setRow; simp
    rw [h0, h0]
    have hmin : ∀ u : Nat → R, minorMat (setRow (r + 1) u A) j = setRow r (fun c => u (skipIdx j c)) (minorMat A j) := by
      intro u; funext i c; unfold minorMat setRow
      by_cases hi : i = r
      · subst hi; simp
      · simp [hi]
    rw [hmin, hmin, detM_row_scale m r α _ (minorMat A j) (by omega)]
    rw [← CommRing.mul_assoc, CommRing.mul_comm _ α, CommRing.mul_assoc]

theorem detM_zero_row {R : Type} [CommRing R] (m r : Nat) (A : Nat → Nat → R) (hr : r < m)
    (hz : ∀ j, j < m → A r j = 0) : detM m A = 0 := by
  have heq : MatEq m m A (setRow r (fun j => (0 : R) * A r j) A) := by
    intro i j hi hj
    unfold setRow
    by_cases hir : i = r
    · rw [hir, ite_t rfl]; dsimp only; rw [zero_mul, hz j hj]
    · rw [ite_f hir]
  rw [detM_congr m heq, detM_row_scale m r 0 (A r) A hr, zero_mul]

theorem detM_row_sum {R : Type} [CommRing R] (m r n : Nat) (c : Nat → R)
    (v : Nat → Nat → R) (A : Nat → Nat → R) (hr : r < m) :
    detM m (setRow r (fun j => sumR n (fun i => c i * v i j)) A) =
    sumR n (fun i => c i * detM m (setRow r (v i) A)) := by
  induction n with
  | zero =>
    simp only [sumR]
    apply detM_zero_row m r _ hr
    intro j _; unfold setRow; simp
  | succ k ih =>
    simp only [sumR]
    rw [detM_row_add m r _ _ A hr, ih, detM_row_scale m r (c k) (v k) A hr]

theorem detM_eq_zero_of_adj_dup {R : Type} [CommRing R] :
    ∀ (m r : Nat) (A : Nat → Nat → R), r + 1 < m →
      (∀ j, j < m → A r j = A (r + 1) j) → detM m A = 0
  | 0, _, _, hr, _ => by omega
  | 1, _, _, hr, _ => by omega
  | m + 2, 0, A, _, hdup => by
    simp only [detM]
    let sgn (k : Nat) (x : R) : R := if k % 2 = 0 then x else -x
    let F (p q : Nat) : R :=
      if p = q then 0
      else if p < q then sgn p (A 0 p) * (sgn (q - 1) (A 1 q) * detM m (minorMat (minorMat A p) (q - 1)))
      else sgn p (A 0 p) * (sgn q (A 1 q) * detM m (minorMat (minorMat A p) q))
    have hrew : sumR (m + 2) (fun j => sgn j (A 0 j) * sumR (m + 1) (fun k => sgn k (minorMat A j 0 k) * detM m (minorMat (minorMat A j) k))) =
        sumR (m + 2) (fun p => sumR (m + 2) (fun q => F p q)) := by
      apply sumR_congr; intro p hp
      rw [sumR_mul_left]
      have hp_le : p ≤ m + 1 := by omega
      rw [sumR_extract (m + 1) p (F p) hp_le]
      have hFp : F p p = 0 := by dsimp only [F]; rw [ite_t rfl]
      rw [hFp, CommRing.zero_add]
      apply sumR_congr; intro k hk
      dsimp only [F, minorMat, skipIdx]
      by_cases hkp : k < p
      · have hne : p ≠ k := by omega
        have hnotlt : ¬ (p < k) := by omega
        rw [ite_t hkp, ite_f hne, ite_f hnotlt]
      · have hne : p ≠ k + 1 := by omega
        have hlt : p < k + 1 := by omega
        have hsub : k + 1 - 1 = k := by omega
        rw [ite_f hkp, ite_f hne, ite_t hlt, hsub]
    change sumR (m + 2) (fun j => sgn j (A 0 j) * sumR (m + 1) (fun k => sgn k (minorMat A j 0 k) * detM m (minorMat (minorMat A j) k))) = 0
    rw [hrew]
    apply sumR_antisym (m + 2) F
    · intro p q hp hq
      have hminor_comm : ∀ a b, a < b → MatEq m m (minorMat (minorMat A a) (b - 1)) (minorMat (minorMat A b) a) := by
        intro a b hab r c _ _
        unfold minorMat skipIdx
        by_cases hca : c < a
        · have hcb : c < b - 1 := by omega
          have hcb2 : c < b := by omega
          simp only [hcb, hca, hcb2, ↓reduceIte]
        · by_cases hcb : c < b - 1
          · have hcb2 : c + 1 < b := by omega
            simp only [hcb, hca, hcb2, ↓reduceIte]
          · have hnot1 : ¬ (c + 1 < a) := by omega
            have hnot2 : ¬ (c + 1 < b) := by omega
            simp only [hcb, hnot1, hca, hnot2, ↓reduceIte]
      have hsgn_pred : ∀ t (x : R), 1 ≤ t → sgn (t - 1) x = -(sgn t x) := by
        intro t x ht
        dsimp only [sgn]
        by_cases he : t % 2 = 0
        · have ho : (t - 1) % 2 ≠ 0 := by omega
          rw [ite_t he, ite_f ho]
        · have he2 : (t - 1) % 2 = 0 := by omega
          rw [ite_f he, ite_t he2, neg_neg]
      dsimp only [F]
      by_cases hpq : p = q
      · subst hpq; simp [neg_zero]
      · by_cases hlt : p < q
        · have hne2 : q ≠ p := Ne.symm hpq
          have hnotlt2 : ¬ (q < p) := by omega
          rw [ite_f hpq, ite_t hlt, ite_f hne2, ite_f hnotlt2]
          rw [detM_congr m (hminor_comm p q hlt), hsgn_pred q (A 1 q) (by omega)]
          rw [← hdup p hp, ← hdup q hq]
          rw [neg_mul, mul_neg, ← CommRing.mul_assoc, ← CommRing.mul_assoc, CommRing.mul_comm (sgn p (A 0 p)) (sgn q (A 0 q))]
        · have hlt2 : q < p := by omega
          have hne2 : q ≠ p := Ne.symm hpq
          rw [ite_f hpq, ite_f hlt, ite_f hne2, ite_t hlt2]
          rw [detM_congr m (hminor_comm q p hlt2), hsgn_pred p (A 1 p) (by omega)]
          rw [← hdup p hp, ← hdup q hq]
          rw [neg_mul, mul_neg, neg_neg, ← CommRing.mul_assoc, ← CommRing.mul_assoc, CommRing.mul_comm (sgn p (A 0 p)) (sgn q (A 0 q))]
    · intro p _; dsimp only [F]; rw [ite_t rfl]
  | m + 2, r + 1, A, hr, hdup => by
    rw [detM]
    have hz : sumR (m + 2) (fun j => (if j % 2 = 0 then A 0 j else -(A 0 j)) * detM (m + 1) (minorMat A j)) =
        sumR (m + 2) (fun _ => (0 : R)) := by
      apply sumR_congr; intro j _
      have hmin : detM (m + 1) (minorMat A j) = 0 := by
        apply detM_eq_zero_of_adj_dup (m + 1) r (minorMat A j) (by omega)
        intro c hc
        unfold minorMat skipIdx
        by_cases hcj : c < j
        · rw [ite_t hcj]; exact hdup c (by omega)
        · rw [ite_f hcj]; exact hdup (c + 1) (by omega)
      rw [hmin, mul_zero]
    rw [hz, sumR_zero_fn]

def swapRows {R : Type} (r1 r2 : Nat) (A : Nat → Nat → R) (i j : Nat) : R :=
  if i = r1 then A r2 j else if i = r2 then A r1 j else A i j

theorem detM_swap_adj {R : Type} [CommRing R] (m r : Nat) (A : Nat → Nat → R) (hr : r + 1 < m) :
    detM m (swapRows r (r + 1) A) = -(detM m A) := by
  let u := A r
  let v := A (r + 1)
  let B := setRow r (fun j => u j + v j) (setRow (r + 1) (fun j => u j + v j) A)
  have hB0 : detM m B = 0 := by
    apply detM_eq_zero_of_adj_dup m r B hr
    intro j _; unfold B setRow; simp
  have h1 : detM m B =
      detM m (setRow r u (setRow (r + 1) (fun j => u j + v j) A)) +
      detM m (setRow r v (setRow (r + 1) (fun j => u j + v j) A)) :=
    detM_row_add m r u v _ (by omega)
  have hcomm_set : ∀ (f g : Nat → R),
      MatEq m m (setRow r f (setRow (r + 1) g A)) (setRow (r + 1) g (setRow r f A)) := by
    intro f g i j _ _
    unfold setRow
    by_cases h1 : i = r
    · rw [h1]; simp
    · by_cases h2 : i = r + 1
      · rw [h2]; simp
      · simp [h1, h2]
  have h2a : detM m (setRow r u (setRow (r + 1) (fun j => u j + v j) A)) =
      detM m (setRow (r + 1) u (setRow r u A)) + detM m (setRow (r + 1) v (setRow r u A)) := by
    rw [detM_congr m (hcomm_set u _), detM_row_add m (r + 1) u v _ hr]
  have h2b : detM m (setRow r v (setRow (r + 1) (fun j => u j + v j) A)) =
      detM m (setRow (r + 1) u (setRow r v A)) + detM m (setRow (r + 1) v (setRow r v A)) := by
    rw [detM_congr m (hcomm_set v _), detM_row_add m (r + 1) u v _ hr]
  have huu : detM m (setRow (r + 1) u (setRow r u A)) = 0 := by
    apply detM_eq_zero_of_adj_dup m r _ hr
    intro j _; unfold setRow; simp
  have hvv : detM m (setRow (r + 1) v (setRow r v A)) = 0 := by
    apply detM_eq_zero_of_adj_dup m r _ hr
    intro j _; unfold setRow; simp
  have huv : detM m (setRow (r + 1) v (setRow r u A)) = detM m A := by
    apply detM_congr m; intro i j _ _; unfold setRow u v
    by_cases h1 : i = r + 1
    · rw [h1]; simp
    · by_cases h2 : i = r
      · rw [h2]; simp
      · simp [h1, h2]
  have hvu : detM m (setRow (r + 1) u (setRow r v A)) = detM m (swapRows r (r + 1) A) := by
    apply detM_congr m; intro i j _ _; unfold setRow swapRows u v
    by_cases h1 : i = r + 1
    · rw [h1]; simp
    · by_cases h2 : i = r
      · rw [h2]; simp
      · simp [h1, h2]
  rw [h2a, h2b, huu, hvv, huv, hvu, CommRing.zero_add, add_zero] at h1
  rw [hB0] at h1
  exact neg_eq_of_add_eq_zero h1.symm

theorem detM_swap_rows {R : Type} [CommRing R] (m r1 r2 : Nat) (A : Nat → Nat → R)
    (hr1 : r1 < m) (hr2 : r2 < m) (hne : r1 ≠ r2) :
    detM m (swapRows r1 r2 A) = -(detM m A) := by
  have hlt_case : ∀ (d : Nat) (a : Nat) (M : Nat → Nat → R), a + d + 1 < m →
      detM m (swapRows a (a + d + 1) M) = -(detM m M) := by
    intro d
    induction d with
    | zero =>
      intro a M ha
      simpa [Nat.add_zero] using detM_swap_adj m a M (by omega)
    | succ d' ih =>
      intro a M ha
      -- `swap(a, a+d'+2) = swap(a+d'+1, a+d'+2) ∘ swap(a, a+d'+1) ∘ swap(a+d'+1, a+d'+2)`
      let M1 := swapRows (a + d' + 1) (a + d' + 2) M
      let M2 := swapRows a (a + d' + 1) M1
      let M3 := swapRows (a + d' + 1) (a + d' + 2) M2
      have hadd : a + (d' + 1) + 1 = a + d' + 2 := by omega
      rw [hadd]
      have heq : MatEq m m (swapRows a (a + d' + 2) M) M3 := by
        intro i j _ _
        unfold M3 M2 M1 swapRows
        have na1 : a ≠ a + d' + 1 := by omega
        have na2 : a ≠ a + d' + 2 := by omega
        have n1a : a + d' + 1 ≠ a := by omega
        have n12 : a + d' + 1 ≠ a + d' + 2 := by omega
        have n2a : a + d' + 2 ≠ a := by omega
        have n21 : a + d' + 2 ≠ a + d' + 1 := by omega
        by_cases h1 : i = a
        · rw [h1]; simp [na1, na2]
        · by_cases h2 : i = a + d' + 1
          · rw [h2, ite_f n1a, ite_f n12, ite_t rfl, ite_f n2a, ite_f n21, ite_f n21, ite_t rfl]
          · by_cases h3 : i = a + d' + 2
            · rw [h3, ite_f n2a, ite_t rfl, ite_f n21, ite_t rfl, ite_f n1a, ite_t rfl, ite_f na1, ite_f na2]
            · simp [h1, h2, h3]
      rw [detM_congr m heq]
      have s3 := detM_swap_adj m (a + d' + 1) M2 (by omega)
      have s2 := ih a M1 (by omega)
      have s1 := detM_swap_adj m (a + d' + 1) M (by omega)
      change detM m (swapRows (a + d' + 1) (a + d' + 1 + 1) M2) = -(detM m M)
      rw [s3, s2, s1, neg_neg]
  by_cases hlt : r1 < r2
  · have hEq : r2 = r1 + (r2 - r1 - 1) + 1 := by omega
    rw [hEq]
    exact hlt_case (r2 - r1 - 1) r1 A (by omega)
  · have hlt2 : r2 < r1 := by omega
    have hsym : MatEq m m (swapRows r1 r2 A) (swapRows r2 r1 A) := by
      intro i j _ _; unfold swapRows
      by_cases h1 : i = r1
      · subst h1; simp [hne]
      · by_cases h2 : i = r2
        · subst h2; simp [h1]
        · simp [h1, h2]
    rw [detM_congr m hsym]
    have hEq : r1 = r2 + (r1 - r2 - 1) + 1 := by omega
    rw [hEq]
    exact hlt_case (r1 - r2 - 1) r2 A (by omega)

theorem detM_eq_zero_of_dup_rows {R : Type} [CommRing R] (m r1 r2 : Nat) (A : Nat → Nat → R)
    (hr1 : r1 < m) (hr2 : r2 < m) (hne : r1 ≠ r2) (hdup : ∀ j, j < m → A r1 j = A r2 j) :
    detM m A = 0 := by
  by_cases hlt : r1 < r2
  · by_cases hadj : r2 = r1 + 1
    · subst hadj; exact detM_eq_zero_of_adj_dup m r1 A hr2 hdup
    · have hsw := detM_swap_rows m (r1 + 1) r2 A (by omega) hr2 (by omega)
      have hz : detM m (swapRows (r1 + 1) r2 A) = 0 := by
        apply detM_eq_zero_of_adj_dup m r1 _ (by omega)
        intro j hj; unfold swapRows
        simp [hne, hdup j hj]
      rw [hz] at hsw
      exact neg_eq_zero_iff.mp hsw.symm
  · have hlt2 : r2 < r1 := by omega
    by_cases hadj : r1 = r2 + 1
    · subst hadj; exact detM_eq_zero_of_adj_dup m r2 A hr1 (fun j hj => (hdup j hj).symm)
    · have hsw := detM_swap_rows m (r2 + 1) r1 A (by omega) hr1 (by omega)
      have hz : detM m (swapRows (r2 + 1) r1 A) = 0 := by
        apply detM_eq_zero_of_adj_dup m r2 _ (by omega)
        intro j hj; unfold swapRows
        have n2 : r2 ≠ r1 := Ne.symm hne
        simp [n2, (hdup j hj).symm]
      rw [hz] at hsw
      exact neg_eq_zero_iff.mp hsw.symm

theorem detM_row_add_mul {R : Type} [CommRing R] (m r1 r2 : Nat) (α : R) (A : Nat → Nat → R)
    (hr1 : r1 < m) (hr2 : r2 < m) (hne : r1 ≠ r2) :
    detM m (setRow r2 (fun j => A r2 j + α * A r1 j) A) = detM m A := by
  rw [detM_row_add m r2 (A r2) (fun j => α * A r1 j) A hr2,
      detM_row_scale m r2 α (A r1) A hr2]
  have h1 : detM m (setRow r2 (A r2) A) = detM m A := by
    apply detM_congr m; intro i j _ _; unfold setRow
    by_cases h : i = r2
    · subst h; simp
    · simp [h]
  have h2 : detM m (setRow r2 (A r1) A) = 0 := by
    apply detM_eq_zero_of_dup_rows m r1 r2 _ hr1 hr2 hne
    intro j _; unfold setRow; simp [hne]
  rw [h1, h2, mul_zero, add_zero]

theorem detM_id {R : Type} [CommRing R] : ∀ m : Nat, detM m (matIdF (R := R)) = 1
  | 0 => rfl
  | m + 1 => by
    simp only [detM]
    have hsingle : sumR (m + 1) (fun j => (if j % 2 = 0 then matIdF (R := R) 0 j else -(matIdF (R := R) 0 j)) *
        detM m (minorMat (matIdF (R := R)) j)) =
        sumR (m + 1) (fun j => if j = 0 then 1 * detM m (minorMat (matIdF (R := R)) 0) else 0) := by
      apply sumR_congr; intro j _
      unfold matIdF
      by_cases hj : j = 0
      · subst hj; simp
      · have hne : (0 : Nat) ≠ j := Ne.symm hj
        simp only [hne, hj, ↓reduceIte, neg_zero]
        by_cases he : j % 2 = 0
        · rw [ite_t he, zero_mul]
        · rw [ite_f he, zero_mul]
    rw [hsingle, sumR_single (m + 1) 0 _ (Nat.zero_lt_succ m), CommRing.one_mul]
    have hmin : MatEq m m (minorMat (matIdF (R := R)) 0) matIdF := by
      intro r c _ _; unfold minorMat skipIdx matIdF
      have h0 : ¬ (c < 0) := Nat.not_lt_zero c
      simp [h0]
    rw [detM_congr m hmin, detM_id m]

theorem detM_zero_col0 {R : Type} [CommRing R] :
    ∀ (m : Nat) (A : Nat → Nat → R), 1 ≤ m → (∀ r, r < m → A r 0 = 0) → detM m A = 0
  | 0, _, hm, _ => by omega
  | 1, A, _, hz => by
    simp [detM, sumR, CommRing.zero_add, hz 0 (by omega), zero_mul]
  | m + 2, A, _, hz => by
    rw [detM]
    have h0 : sumR (m + 2) (fun j => (if j % 2 = 0 then A 0 j else -(A 0 j)) * detM (m + 1) (minorMat A j)) =
        sumR (m + 2) (fun _ => (0 : R)) := by
      apply sumR_congr; intro j _
      cases j with
      | zero => simp [hz 0 (by omega), zero_mul]
      | succ j' =>
        have hmin0 : detM (m + 1) (minorMat A (j' + 1)) = 0 := by
          apply detM_zero_col0 (m + 1) (minorMat A (j' + 1)) (by omega)
          intro r hr
          unfold minorMat skipIdx
          simp [hz (r + 1) (by omega)]
        rw [hmin0, mul_zero]
    rw [h0, sumR_zero_fn]

theorem detM_col0_e0 {R : Type} [CommRing R] (m : Nat) (A : Nat → Nat → R)
    (h00 : A 0 0 = 1) (hcol0 : ∀ r, r < m → A (r + 1) 0 = 0) :
    detM (m + 1) A = detM m (minorMat A 0) := by
  simp only [detM]
  have hsingle : sumR (m + 1) (fun j => (if j % 2 = 0 then A 0 j else -(A 0 j)) * detM m (minorMat A j)) =
      sumR (m + 1) (fun j => if j = 0 then detM m (minorMat A 0) else 0) := by
    apply sumR_congr; intro j _
    cases j with
    | zero => simp [h00, CommRing.one_mul]
    | succ j' =>
      have hne : j' + 1 ≠ 0 := Nat.succ_ne_zero j'
      rw [ite_f hne]
      cases m with
      | zero => omega
      | succ m' =>
        have hmin0 : detM (m' + 1) (minorMat A (j' + 1)) = 0 := by
          apply detM_zero_col0 (m' + 1) (minorMat A (j' + 1)) (by omega)
          intro r hr; unfold minorMat skipIdx; simp [hcol0 r hr]
        rw [hmin0, mul_zero]
  rw [hsingle, sumR_single (m + 1) 0 _ (Nat.zero_lt_succ m)]

theorem detM_first_k_cols_id {R : Type} [CommRing R] :
    ∀ (k m : Nat) (A : Nat → Nat → R), k ≤ m →
      (∀ i j, i < m → j < k → A i j = matIdF i j) →
      detM m A = detM (m - k) (fun r c => A (k + r) (k + c))
  | 0, m, A, _, _ => by
    simp only [Nat.sub_zero, Nat.zero_add]
  | k + 1, 0, _, hk, _ => by omega
  | k + 1, m + 1, A, hk, hcols => by
    have h00 : A 0 0 = 1 := by simpa [matIdF] using hcols 0 0 (by omega) (by omega)
    have hcol0 : ∀ r, r < m → A (r + 1) 0 = 0 := by
      intro r hr; simpa [matIdF] using hcols (r + 1) 0 (by omega) (by omega)
    rw [detM_col0_e0 m A h00 hcol0]
    have hmin_cols : ∀ i j, i < m → j < k → minorMat A 0 i j = matIdF i j := by
      intro i j hi hj
      unfold minorMat skipIdx
      have h0 : ¬ (j < 0) := Nat.not_lt_zero j
      rw [ite_f h0, hcols (i + 1) (j + 1) (by omega) (by omega)]
      unfold matIdF; simp
    have ih := detM_first_k_cols_id k m (minorMat A 0) (by omega) hmin_cols
    rw [ih]
    have hsub : m + 1 - (k + 1) = m - k := by omega
    rw [hsub]
    apply detM_congr (m - k)
    intro r c _ _; unfold minorMat skipIdx; dsimp only
    have h0 : ¬ (k + c < 0) := Nat.not_lt_zero _
    rw [ite_f h0]
    have h1 : k + r + 1 = k + 1 + r := by omega
    have h2 : k + c + 1 = k + 1 + c := by omega
    rw [h1, h2]

/-- Block-diagonal matrix `diag(A, B)` with top-left block size `a × a`. -/
def blockDiag {R : Type} [CommRing R] (a : Nat) (A B : Nat → Nat → R) (i j : Nat) : R :=
  if i < a ∧ j < a then A i j
  else if a ≤ i ∧ a ≤ j then B (i - a) (j - a)
  else 0

theorem detM_blockDiag {R : Type} [CommRing R] :
    ∀ (a b : Nat) (A B : Nat → Nat → R),
      detM (a + b) (blockDiag a A B) = detM a A * detM b B
  | 0, b, _, B => by
    rw [Nat.zero_add, detM, CommRing.one_mul]
    apply detM_congr b
    intro i j _ _; unfold blockDiag; simp
  | a + 1, b, A, B => by
    have hadd : a + 1 + b = (a + b) + 1 := by omega
    rw [hadd]
    simp only [detM]
    have hsplit : a + b + 1 = (a + 1) + b := by omega
    have hLsplit : sumR (a + b + 1) (fun j => (if j % 2 = 0 then blockDiag (a + 1) A B 0 j else -(blockDiag (a + 1) A B 0 j)) *
          detM (a + b) (minorMat (blockDiag (a + 1) A B) j)) =
        sumR (a + 1) (fun j => (if j % 2 = 0 then blockDiag (a + 1) A B 0 j else -(blockDiag (a + 1) A B 0 j)) *
          detM (a + b) (minorMat (blockDiag (a + 1) A B) j)) +
        sumR b (fun t => (if (a + 1 + t) % 2 = 0 then blockDiag (a + 1) A B 0 (a + 1 + t) else -(blockDiag (a + 1) A B 0 (a + 1 + t))) *
          detM (a + b) (minorMat (blockDiag (a + 1) A B) (a + 1 + t))) := by
      rw [hsplit, sumR_split (a + 1) b]
    rw [hLsplit]
    have htail : sumR b (fun t =>
        (if (a + 1 + t) % 2 = 0 then blockDiag (a + 1) A B 0 (a + 1 + t) else -(blockDiag (a + 1) A B 0 (a + 1 + t))) *
        detM (a + b) (minorMat (blockDiag (a + 1) A B) (a + 1 + t))) = 0 := by
      have hz : ∀ t, t < b →
          (if (a + 1 + t) % 2 = 0 then blockDiag (a + 1) A B 0 (a + 1 + t) else -(blockDiag (a + 1) A B 0 (a + 1 + t))) *
          detM (a + b) (minorMat (blockDiag (a + 1) A B) (a + 1 + t)) = 0 := by
        intro t _
        have hbd : blockDiag (a + 1) A B 0 (a + 1 + t) = 0 := by
          unfold blockDiag; split <;> (try omega); split <;> (try omega); rfl
        rw [hbd, neg_zero]
        by_cases he : (a + 1 + t) % 2 = 0
        · rw [ite_t he, zero_mul]
        · rw [ite_f he, zero_mul]
      rw [sumR_congr hz, sumR_zero_fn]
    rw [htail, add_zero, sumR_mul_right]
    apply sumR_congr; intro j hj
    have h0j : blockDiag (a + 1) A B 0 j = A 0 j := by
      unfold blockDiag; exact ite_t ⟨Nat.zero_lt_succ a, hj⟩
    have hmin : MatEq (a + b) (a + b) (minorMat (blockDiag (a + 1) A B) j) (blockDiag a (minorMat A j) B) := by
      intro r c _ _
      unfold minorMat blockDiag skipIdx
      by_cases hra : r < a
      · by_cases hca : c < a
        · have hr1 : r + 1 < a + 1 := by omega
          by_cases hcj : c < j
          · have hc1 : c < a + 1 := by omega
            simp only [hcj, hr1, hc1, hra, hca, and_self, ↓reduceIte]
          · have hc1 : c + 1 < a + 1 := by omega
            simp only [hcj, hr1, hc1, hra, hca, and_self, ↓reduceIte]
        · have hnot1 : ¬ (c < j) := by omega
          have hnot2 : ¬ (r + 1 < a + 1 ∧ c + 1 < a + 1) := by omega
          have hnot3 : ¬ (a + 1 ≤ r + 1 ∧ a + 1 ≤ c + 1) := by omega
          have hnot4 : ¬ (r < a ∧ c < a) := by omega
          have hnot5 : ¬ (a ≤ r ∧ a ≤ c) := by omega
          rw [ite_f hnot1, ite_f hnot2, ite_f hnot3, ite_f hnot4, ite_f hnot5]
      · by_cases hca : c < a
        · have hnot2 : ¬ (r + 1 < a + 1 ∧ (if c < j then c else c + 1) < a + 1) := by omega
          have hnot3 : ¬ (a + 1 ≤ r + 1 ∧ a + 1 ≤ (if c < j then c else c + 1)) := by split <;> omega
          have hnot4 : ¬ (r < a ∧ c < a) := by omega
          have hnot5 : ¬ (a ≤ r ∧ a ≤ c) := by omega
          rw [ite_f hnot2, ite_f hnot3, ite_f hnot4, ite_f hnot5]
        · have hnot1 : ¬ (c < j) := by omega
          have hnot2 : ¬ (r + 1 < a + 1 ∧ c + 1 < a + 1) := by omega
          have hge1 : a + 1 ≤ r + 1 ∧ a + 1 ≤ c + 1 := by omega
          have hnot4 : ¬ (r < a ∧ c < a) := by omega
          have hge2 : a ≤ r ∧ a ≤ c := by omega
          rw [ite_f hnot1, ite_f hnot2, ite_t hge1, ite_f hnot4, ite_t hge2]
          have hs1 : r + 1 - (a + 1) = r - a := by omega
          have hs2 : c + 1 - (a + 1) = c - a := by omega
          rw [hs1, hs2]
    rw [h0j, detM_congr (a + b) hmin, detM_blockDiag a b (minorMat A j) B, CommRing.mul_assoc]

-- Elementary row-operation matrices (reused for BOTH `isMatInv_of_detM_ne_zero` AND `col_basis_of_right_inv`!)

private def elemSwap {R : Type} [CommRing R] (r1 r2 i j : Nat) : R :=
  if i = r1 then matIdF r2 j else if i = r2 then matIdF r1 j else matIdF i j

private theorem elemSwap_mul {R : Type} [CommRing R] (m r1 r2 : Nat) (A : Nat → Nat → R)
    (hr1 : r1 < m) (hr2 : r2 < m) :
    ∀ i j, i < m → matMulF m (elemSwap r1 r2) A i j = swapRows r1 r2 A i j := by
  intro i j hi
  unfold elemSwap swapRows
  by_cases h1 : i = r1
  · subst h1
    have hc : matMulF m (fun a b => if a = i then matIdF r2 b else if a = r2 then matIdF i b else matIdF a b) A i j =
        matMulF m matIdF A r2 j := by
      unfold matMulF; apply sumR_congr; intro t _; simp
    rw [hc, matMulF_id_left m A hr2, ite_t rfl]
  · by_cases h2 : i = r2
    · subst h2
      have hc : matMulF m (fun a b => if a = r1 then matIdF i b else if a = i then matIdF r1 b else matIdF a b) A i j =
          matMulF m matIdF A r1 j := by
        unfold matMulF; apply sumR_congr; intro t _; simp [h1]
      rw [hc, matMulF_id_left m A hr1, ite_f h1, ite_t rfl]
    · have hc : matMulF m (fun a b => if a = r1 then matIdF r2 b else if a = r2 then matIdF r1 b else matIdF a b) A i j =
          matMulF m matIdF A i j := by
        unfold matMulF; apply sumR_congr; intro t _; simp [h1, h2]
      rw [hc, matMulF_id_left m A hi, ite_f h1, ite_f h2]

private theorem isMatInv_elemSwap {R : Type} [CommRing R] (m r1 r2 : Nat)
    (hr1 : r1 < m) (hr2 : r2 < m) :
    IsMatInv m (elemSwap (R := R) r1 r2) (elemSwap r1 r2) := by
  have hsq : MatEq m m (matMulF m (elemSwap (R := R) r1 r2) (elemSwap r1 r2)) matIdF := by
    intro i j hi _
    rw [elemSwap_mul m r1 r2 _ hr1 hr2 i j hi]
    unfold swapRows elemSwap
    by_cases h1 : i = r1
    · subst h1
      by_cases h12 : i = r2
      · subst h12; simp
      · have h21 : r2 ≠ i := Ne.symm h12
        simp [h21]
    · by_cases h2 : i = r2
      · subst h2; simp [h1]
      · simp [h1, h2]
  exact ⟨hsq, hsq⟩

private def elemScale {R : Type} [CommRing R] (r : Nat) (α : R) (i j : Nat) : R :=
  if i = r then (if j = r then α else 0) else matIdF i j

private theorem elemScale_mul {R : Type} [CommRing R] (m r : Nat) (α : R) (A : Nat → Nat → R)
    (hr : r < m) :
    ∀ i j, i < m → matMulF m (elemScale r α) A i j = setRow r (fun c => α * A r c) A i j := by
  intro i j hi
  unfold elemScale setRow
  by_cases h : i = r
  · subst h
    rw [ite_t rfl]
    unfold matMulF
    have hs : sumR m (fun t => (if i = i then if t = i then α else 0 else matIdF i t) * A t j) =
        sumR m (fun t => if t = i then α * A i j else 0) := by
      apply sumR_congr; intro t _
      by_cases ht : t = i
      · subst ht; simp
      · simp [ht, zero_mul]
    rw [hs, sumR_single m i _ hr]
  · rw [ite_f h]
    have hc : matMulF m (fun a b => if a = r then if b = r then α else 0 else matIdF a b) A i j =
        matMulF m matIdF A i j := by
      unfold matMulF; apply sumR_congr; intro t _; simp [h]
    rw [hc, matMulF_id_left m A hi]

private theorem isMatInv_elemScale {F : Type} [SimpleField F] (m r : Nat) (α : F)
    (hr : r < m) (hα : α ≠ 0) :
    IsMatInv m (elemScale r α) (elemScale r (SimpleField.inv α)) := by
  constructor
  · intro i j hi _
    rw [elemScale_mul m r α _ hr i j hi]
    unfold setRow elemScale matIdF
    by_cases h : i = r
    · subst h
      by_cases hj : j = i
      · subst hj; simp [SimpleField.mul_inv_cancel α hα]
      · have hne : i ≠ j := Ne.symm hj
        simp [hj, hne, mul_zero]
    · simp [h]
  · intro i j hi _
    rw [elemScale_mul m r (SimpleField.inv α) _ hr i j hi]
    unfold setRow elemScale matIdF
    by_cases h : i = r
    · subst h
      by_cases hj : j = i
      · subst hj; simp [CommRing.mul_comm (SimpleField.inv α) α, SimpleField.mul_inv_cancel α hα]
      · have hne : i ≠ j := Ne.symm hj
        simp [hj, hne, mul_zero]
    · simp [h]

private def elemAddMul {R : Type} [CommRing R] (r1 r2 : Nat) (α : R) (i j : Nat) : R :=
  if i = r2 then matIdF r2 j + (if j = r1 then α else 0) else matIdF i j

private theorem elemAddMul_mul {R : Type} [CommRing R] (m r1 r2 : Nat) (α : R) (A : Nat → Nat → R)
    (hr1 : r1 < m) (hr2 : r2 < m) :
    ∀ i j, i < m → matMulF m (elemAddMul r1 r2 α) A i j =
      setRow r2 (fun c => A r2 c + α * A r1 c) A i j := by
  intro i j hi
  unfold elemAddMul setRow
  by_cases h : i = r2
  · subst h
    rw [ite_t rfl]
    unfold matMulF
    have hsplit : sumR m (fun t => (if i = i then matIdF i t + if t = r1 then α else 0 else matIdF i t) * A t j) =
        sumR m (fun t => matIdF i t * A t j) + sumR m (fun t => if t = r1 then α * A r1 j else 0) := by
      rw [← sumR_add]
      apply sumR_congr; intro t _
      simp only [↓reduceIte, right_distrib]
      congr 1
      by_cases ht : t = r1
      · subst ht; simp
      · simp [ht, zero_mul]
    rw [hsplit, show sumR m (fun t => matIdF i t * A t j) = matMulF m matIdF A i j from rfl,
        matMulF_id_left m A hr2, sumR_single m r1 _ hr1]
  · rw [ite_f h]
    have hc : matMulF m (fun a b => if a = r2 then matIdF r2 b + if b = r1 then α else 0 else matIdF a b) A i j =
        matMulF m matIdF A i j := by
      unfold matMulF; apply sumR_congr; intro t _; simp [h]
    rw [hc, matMulF_id_left m A hi]

private theorem isMatInv_elemAddMul {R : Type} [CommRing R] (m r1 r2 : Nat) (α : R)
    (hr1 : r1 < m) (hr2 : r2 < m) (hne : r1 ≠ r2) :
    IsMatInv m (elemAddMul r1 r2 α) (elemAddMul r1 r2 (-α)) := by
  have h1 : ∀ (c : R), MatEq m m (matMulF m (elemAddMul r1 r2 c) (elemAddMul r1 r2 (-c))) matIdF := by
    intro c i j hi _
    rw [elemAddMul_mul m r1 r2 c _ hr1 hr2 i j hi]
    unfold setRow elemAddMul
    by_cases h : i = r2
    · subst h
      simp only [↓reduceIte, hne]
      by_cases hj : j = r1
      · subst hj
        have hne2 : i ≠ j := Ne.symm hne
        simp [matIdF, hne2, CommRing.add_assoc, neg_add, add_zero, mul_one]
      · have hne2 : r1 ≠ j := Ne.symm hj
        simp [matIdF, hj, hne2, mul_zero, add_zero]
    · simp [h]
  refine ⟨h1 α, ?_⟩
  have h2 := h1 (-α)
  intro i j hi hj
  have := h2 i j hi hj
  rw [neg_neg] at this
  exact this

/-- Eliminate column `k` in rows `0..lim-1` (`≠ k`) of `M` assuming `M k k = 1`, tracking `IsMatInv` & `detM`. -/
private theorem elim_col_rows {F : Type} [SimpleField F] (m k : Nat) (hk : k < m) :
    ∀ (lim : Nat) (M : Nat → Nat → F), lim ≤ m → M k k = 1 →
      ∃ (E Einv : Nat → Nat → F),
        IsMatInv m E Einv ∧
        detM m (matMulF m E M) = detM m M ∧
        (∀ i j, i < m → (M k j = 0 → matMulF m E M i j = M i j)) ∧
        (∀ i, i < lim → matMulF m E M i k = matIdF i k) ∧
        (∀ i, lim ≤ i → i < m → matMulF m E M i k = M i k)
  | 0, M, _, _ => by
    refine ⟨matIdF, matIdF, ⟨fun i j hi _ => matMulF_id_left m matIdF hi, fun i j hi _ => matMulF_id_left m matIdF hi⟩,
            detM_congr m (fun i j hi _ => matMulF_id_left m M hi),
            fun i j hi _ => matMulF_id_left m M hi,
            fun _ hi => absurd hi (Nat.not_lt_zero _),
            fun i _ hi => matMulF_id_left m M hi⟩
  | lim + 1, M, hlim, hkk => by
    obtain ⟨E0, E0inv, hInv0, hdet0, hzero0, hbelow0, habove0⟩ :=
      elim_col_rows m k hk lim M (by omega) hkk
    let M0 := matMulF m E0 M
    have hM0kk : M0 k k = 1 := by
      dsimp only [M0]
      by_cases hkl : k < lim
      · rw [hbelow0 k hkl]; simp [matIdF]
      · rw [habove0 k (by omega) hk, hkk]
    by_cases hlk : lim = k
    · refine ⟨E0, E0inv, hInv0, hdet0, hzero0, ?_, fun i hi hlt => habove0 i (by omega) hlt⟩
      intro i hi
      by_cases hil : i < lim
      · exact hbelow0 i hil
      · have hik : i = k := by omega
        subst hik; simpa [matIdF] using hM0kk
    · let α := -(M0 lim k)
      let E1 := elemAddMul k lim α
      let E1inv := elemAddMul k lim (-α)
      have hInv1 : IsMatInv m E1 E1inv := isMatInv_elemAddMul m k lim α hk (by omega) (Ne.symm hlk)
      refine ⟨matMulF m E1 E0, matMulF m E0inv E1inv, isMatInv_mul hInv1 hInv0, ?_, ?_, ?_, ?_⟩
      · have hprod : MatEq m m (matMulF m (matMulF m E1 E0) M)
            (setRow lim (fun c => M0 lim c + α * M0 k c) M0) := by
          intro i j hi _
          rw [matMulF_assoc]
          exact elemAddMul_mul m k lim α M0 hk (by omega) i j hi
        rw [detM_congr m hprod, detM_row_add_mul m k lim α M0 hk (by omega) (Ne.symm hlk), hdet0]
      · intro i j hi hkj0
        rw [matMulF_assoc, elemAddMul_mul m k lim α M0 hk (by omega) i j hi]
        unfold setRow
        have hM0kj : M0 k j = 0 := by dsimp only [M0]; rw [hzero0 k j hk hkj0, hkj0]
        by_cases hil : i = lim
        · subst hil; rw [ite_t rfl]; dsimp only [M0] at hM0kj ⊢; rw [hM0kj, mul_zero, add_zero, hzero0 i j hi hkj0]
        · rw [ite_f hil]; dsimp only [M0]; exact hzero0 i j hi hkj0
      · intro i hi
        rw [matMulF_assoc, elemAddMul_mul m k lim α M0 hk (by omega) i k (by omega)]
        unfold setRow
        by_cases hil : i = lim
        · subst hil
          rw [ite_t rfl]; dsimp only; rw [hM0kk, mul_one]
          dsimp only [α]
          rw [CommRing.add_neg]
          unfold matIdF; exact (ite_f hlk).symm
        · rw [ite_f hil]
          exact hbelow0 i (by omega)
      · intro i hi hlt
        rw [matMulF_assoc, elemAddMul_mul m k lim α M0 hk (by omega) i k hlt]
        unfold setRow
        have hne : i ≠ lim := by omega
        rw [ite_f hne]
        exact habove0 i (by omega) hlt

/-- **Two-Sided Gauss-Jordan Inverse Theorem over EVERY `SimpleField F`:**
    `detM m A ≠ 0 → ∃ Ainv, IsMatInv m A Ainv`! -/
theorem isMatInv_of_detM_ne_zero {F : Type} [SimpleField F] (m : Nat) (A : Nat → Nat → F)
    (hdet : detM m A ≠ 0) : ∃ Ainv : Nat → Nat → F, IsMatInv m A Ainv := by
  have hstep : ∀ k : Nat, k ≤ m →
      ∃ (L Linv : Nat → Nat → F),
        IsMatInv m L Linv ∧
        detM m (matMulF m L A) ≠ 0 ∧
        (∀ i j, i < m → j < k → matMulF m L A i j = matIdF i j) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨matIdF, matIdF,
              ⟨fun i j hi _ => matMulF_id_left m matIdF hi, fun i j hi _ => matMulF_id_left m matIdF hi⟩,
              by rw [detM_congr m (fun i j hi _ => matMulF_id_left m A hi)]; exact hdet,
              fun _ _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ k' ih =>
      intro hk
      obtain ⟨L0, L0inv, hInv0, hdet0, hcols0⟩ := ih (by omega)
      let M0 := matMulF m L0 A
      -- Must exist a nonzero pivot in column `k'` at some row `p ≥ k'`!
      have hpiv : ∃ p, k' ≤ p ∧ p < m ∧ M0 p k' ≠ 0 := Classical.byContradiction fun hnone => by
        have hzero : ∀ r, r < m - k' → M0 (k' + r) (k' + 0) = 0 := by
          intro r hr
          rw [Nat.add_zero]
          exact Classical.byContradiction fun hne => hnone ⟨k' + r, by omega, by omega, hne⟩
        have hd := detM_first_k_cols_id k' m M0 (by omega) hcols0
        have hd0 := detM_zero_col0 (m - k') (fun r c => M0 (k' + r) (k' + c)) (by omega) hzero
        rw [hd0] at hd
        exact hdet0 hd
      obtain ⟨p, hkp, hpm, hpne⟩ := hpiv
      -- 1. Swap rows `k'` and `p`
      let Es := elemSwap (R := F) k' p
      let L1 := matMulF m Es L0
      let L1inv := matMulF m L0inv Es
      have hInv1 : IsMatInv m L1 L1inv := isMatInv_mul (isMatInv_elemSwap m k' p (by omega) hpm) hInv0
      have hM1_eq : MatEq m m (matMulF m L1 A) (swapRows k' p M0) := by
        intro i j hi _
        rw [matMulF_assoc]; exact elemSwap_mul m k' p M0 (by omega) hpm i j hi
      have hdet1 : detM m (matMulF m L1 A) ≠ 0 := by
        rw [detM_congr m hM1_eq]
        by_cases heq : k' = p
        · subst heq
          have hid : MatEq m m (swapRows k' k' M0) M0 := by
            intro i j _ _; unfold swapRows; by_cases h : i = k' <;> simp [h]
          rw [detM_congr m hid]; exact hdet0
        · rw [detM_swap_rows m k' p M0 (by omega) hpm heq]
          intro hz; exact hdet0 (neg_eq_zero_iff.mp hz)
      have hcols1 : ∀ i j, i < m → j < k' → matMulF m L1 A i j = matIdF i j := by
        intro i j hi hj
        rw [hM1_eq i j hi (by omega)]
        unfold swapRows
        by_cases h1 : i = k'
        · rw [h1, ite_t rfl]; dsimp only [M0]; rw [hcols0 p j hpm hj]; unfold matIdF
          have n1 : p ≠ j := by omega
          have n2 : k' ≠ j := by omega
          rw [ite_f n1, ite_f n2]
        · by_cases h2 : i = p
          · rw [h2, ite_f (by rw [← h2]; exact h1), ite_t rfl]; dsimp only [M0]; rw [hcols0 k' j (by omega) hj]; unfold matIdF
            have n1 : k' ≠ j := by omega
            have n2 : p ≠ j := by omega
            rw [ite_f n1, ite_f n2]
          · rw [ite_f h1, ite_f h2]; exact hcols0 i j hi hj
      let M1 := matMulF m L1 A
      have hM1kk : M1 k' k' ≠ 0 := by
        dsimp only [M1]; rw [hM1_eq k' k' (by omega) (by omega)]
        unfold swapRows; rw [ite_t rfl]; exact hpne
      -- 2. Scale row `k'` by `inv (M1 k' k')`
      let α := SimpleField.inv (M1 k' k')
      have hαne : α ≠ 0 := by
        intro hz
        have hc := SimpleField.mul_inv_cancel (M1 k' k') hM1kk
        change M1 k' k' * α = 1 at hc
        rw [hz, mul_zero] at hc
        exact SimpleField.zero_ne_one hc
      let Esc := elemScale k' α
      let EscInv := elemScale k' (SimpleField.inv α)
      let L2 := matMulF m Esc L1
      let L2inv := matMulF m L1inv EscInv
      have hInv2 : IsMatInv m L2 L2inv := isMatInv_mul (isMatInv_elemScale m k' α (by omega) hαne) hInv1
      have hM2_eq : MatEq m m (matMulF m L2 A) (setRow k' (fun c => α * M1 k' c) M1) := by
        intro i j hi _
        rw [matMulF_assoc]; exact elemScale_mul m k' α M1 (by omega) i j hi
      have hdet2 : detM m (matMulF m L2 A) ≠ 0 := by
        rw [detM_congr m hM2_eq, detM_row_scale m k' α (M1 k') M1 (by omega)]
        have hM1s : detM m (setRow k' (M1 k') M1) = detM m M1 :=
          detM_congr m (fun i j _ _ => by unfold setRow; by_cases h : i = k' <;> simp [h])
        rw [hM1s]
        exact field_mul_ne_zero hαne hdet1
      let M2 := matMulF m L2 A
      have hM2kk : M2 k' k' = 1 := by
        dsimp only [M2]; rw [hM2_eq k' k' (by omega) (by omega)]
        unfold setRow; rw [ite_t rfl]; dsimp only; rw [CommRing.mul_comm]
        exact SimpleField.mul_inv_cancel (M1 k' k') hM1kk
      have hcols2 : ∀ i j, i < m → j < k' → M2 i j = matIdF i j := by
        intro i j hi hj
        dsimp only [M2]; rw [hM2_eq i j hi (by omega)]
        unfold setRow
        by_cases h : i = k'
        · rw [h, ite_t rfl]; dsimp only [M1]; rw [hcols1 k' j (by omega) hj]
          unfold matIdF; have hne : k' ≠ j := by omega
          rw [ite_f hne, mul_zero]
        · rw [ite_f h]; exact hcols1 i j hi hj
      -- 3. Eliminate all other rows in column `k'`
      obtain ⟨Ee, EeInv, hInvE, hdetE, hzeroE, hcolE, _⟩ :=
        elim_col_rows m k' (by omega) m M2 (Nat.le_refl m) hM2kk
      refine ⟨matMulF m Ee L2, matMulF m L2inv EeInv, isMatInv_mul hInvE hInv2, ?_, ?_⟩
      · have heq : MatEq m m (matMulF m (matMulF m Ee L2) A) (matMulF m Ee M2) :=
          fun i j _ _ => matMulF_assoc m m Ee L2 A i j
        rw [detM_congr m heq, hdetE]; exact hdet2
      · intro i j hi hj
        rw [matMulF_assoc]
        by_cases hjk : j = k'
        · subst hjk; exact hcolE i hi
        · have hjlt : j < k' := by omega
          have hM2kj : M2 k' j = 0 := by
            rw [hcols2 k' j (by omega) hjlt]; unfold matIdF; exact ite_f (by omega)
          rw [hzeroE i j hi hM2kj]; exact hcols2 i j hi hjlt
  obtain ⟨L, Linv, hInvL, _, hLA⟩ := hstep m (Nat.le_refl m)
  -- `L * A = I_m` and `IsMatInv m L Linv` ⇒ `A = Linv` ⇒ `A * L = I_m`!
  have hALinv : MatEq m m A Linv := by
    intro i j hi hj
    calc A i j = matMulF m matIdF A i j := (matMulF_id_left m A hi).symm
      _ = matMulF m (matMulF m Linv L) A i j := matMulF_congr (fun t ht => (hInvL.2 i t hi ht).symm) (fun _ _ => rfl)
      _ = matMulF m Linv (matMulF m L A) i j := matMulF_assoc m m Linv L A i j
      _ = matMulF m Linv matIdF i j := matMulF_congr (fun _ _ => rfl) (fun t ht => hLA t j ht hj)
      _ = Linv i j := matMulF_id_right m Linv hj
  refine ⟨L, ?_, hLA⟩
  intro i j hi hj
  rw [matMulF_congr (fun t ht => hALinv i t hi ht) (fun _ _ => rfl)]
  exact hInvL.2 i j hi hj

/-- **Column-Basis Selection from Right-Inverse (`col_basis_of_right_inv`):**
    If `P ∈ F^{n × q}` and `R ∈ F^{q × n}` satisfy `P · R = I_n`, then `n ≤ q` and there exists a
    bijection `π` of `{0..q-1}` and `PI_inv ∈ F^{n × n}` such that the first `n` permuted columns
    `P_I i j := P i (π j)` satisfy `IsMatInv n P_I PI_inv`! -/
theorem col_basis_of_right_inv {F : Type} [SimpleField F] (n q : Nat) (P R : Nat → Nat → F)
    (hPR : MatEq n n (matMulF q P R) matIdF) :
    n ≤ q ∧
    ∃ (π πInv : Nat → Nat) (PI_inv : Nat → Nat → F),
      (∀ t, t < q → π t < q ∧ πInv t < q ∧ π (πInv t) = t ∧ πInv (π t) = t) ∧
      IsMatInv n (fun i j => P i (π j)) PI_inv := by
  have hnq : n ≤ q := matRankFactor_le q n P R hPR
  have hstep : ∀ k : Nat, k ≤ n →
      ∃ (π πInv : Nat → Nat) (L Linv : Nat → Nat → F),
        (∀ t, t < q → π t < q ∧ πInv t < q ∧ π (πInv t) = t ∧ πInv (π t) = t) ∧
        IsMatInv n L Linv ∧
        (∀ i j, i < n → j < k → matMulF n L (fun r c => P r (π c)) i j = matIdF i j) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨id, id, matIdF, matIdF, fun t ht => ⟨ht, ht, rfl, rfl⟩,
              ⟨fun i j hi _ => matMulF_id_left n matIdF hi, fun i j hi _ => matMulF_id_left n matIdF hi⟩,
              fun _ _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ k' ih =>
      intro hk
      obtain ⟨π0, π0Inv, L0, L0inv, hbij0, hInv0, hcols0⟩ := ih (by omega)
      let P0 : Nat → Nat → F := fun r c => P r (π0 c)
      let M0 : Nat → Nat → F := matMulF n L0 P0
      -- `M0 * (R_perm * L0inv) = L0 * (P * R) * L0inv = I_n`, so row `k'` of `M0` has a nonzero entry at some col `p ≥ k'`!
      have hM0R : MatEq n n (matMulF q M0 (fun t j => matMulF n (fun a b => R (π0 a) b) L0inv t j)) matIdF := by
        intro i j hi hj
        have hPR0 : MatEq n n (matMulF q P0 (fun t b => R (π0 t) b)) matIdF := by
          intro a b ha hb
          -- Bijection sum invariance over `π0` on `{0..q-1}`
          have hsum_bij : ∀ (f : Nat → F), sumR q (fun t => f (π0 t)) = sumR q f := by
            intro f
            have hgen : ∀ (L : List Nat), ListNodup L → (∀ x, x ∈ L → x < q) →
                ∀ (g : Nat → F), (∀ t, t < q → t ∉ L → g t = 0) →
                sumR q (fun t => g (π0 t)) = sumR q g := by
              intro L
              induction L with
              | nil =>
                intro _ _ g hg
                have h1 : sumR q (fun t => g (π0 t)) = 0 := by
                  rw [sumR_congr (fun t ht => hg (π0 t) (hbij0 t ht).1 (by simp)), sumR_zero_fn]
                have h2 : sumR q g = 0 := by
                  rw [sumR_congr (fun t ht => hg t ht (by simp)), sumR_zero_fn]
                rw [h1, h2]
              | cons x xs ihL =>
                intro ⟨hnotmem, hnd⟩ hbd g hg
                let gx : Nat → F := fun t => if t = x then g x else 0
                let gr : Nat → F := fun t => if t = x then 0 else g t
                have hdecomp : ∀ t, g t = gx t + gr t := fun t => by
                  dsimp only [gx, gr]; by_cases h : t = x <;> simp [h, add_zero, CommRing.zero_add]
                have hL1 : sumR q (fun t => g (π0 t)) = sumR q (fun t => gx (π0 t)) + sumR q (fun t => gr (π0 t)) := by
                  rw [← sumR_add]; exact sumR_congr (fun t _ => hdecomp (π0 t))
                have hR1 : sumR q g = sumR q gx + sumR q gr := by
                  rw [← sumR_add]; exact sumR_congr (fun t _ => hdecomp t)
                have hxlt : x < q := hbd x (List.mem_cons_self ..)
                have hgx1 : sumR q (fun t => gx (π0 t)) = g x := by
                  have hc : sumR q (fun t => gx (π0 t)) = sumR q (fun t => if t = π0Inv x then g x else 0) := by
                    apply sumR_congr; intro t ht; dsimp only [gx]
                    by_cases h1 : π0 t = x
                    · have h2 : t = π0Inv x := by rw [← h1, (hbij0 t ht).2.2.2]
                      rw [ite_t h1, ite_t h2]
                    · have h2 : t ≠ π0Inv x := fun heq => h1 (by rw [heq, (hbij0 x hxlt).2.2.1])
                      rw [ite_f h1, ite_f h2]
                  rw [hc, sumR_single q (π0Inv x) (g x) (hbij0 x hxlt).2.1]
                have hgx2 : sumR q gx = g x := sumR_single q x (g x) hxlt
                have hgr_eq := ihL hnd (fun y hy => hbd y (List.mem_cons_of_mem x hy)) gr (fun t ht htn => by
                  dsimp only [gr]
                  by_cases htx : t = x
                  · rw [ite_t htx]
                  · rw [ite_f htx]; exact hg t ht (fun hm => by cases hm with | head => exact htx rfl | tail _ h' => exact htn h'))
                rw [hL1, hR1, hgx1, hgx2, hgr_eq]
            have hrange_nd : ∀ m : Nat, ListNodup (List.range m) := by
              intro m
              induction m with
              | zero => simp [ListNodup]
              | succ m' ihm =>
                rw [List.range_succ]
                have happ : ∀ (l : List Nat) (a : Nat), ListNodup l → (∀ y, y ∈ l → y ≠ a) → ListNodup (l ++ [a]) := by
                  intro l
                  induction l with
                  | nil => intro a _ _; simp [ListNodup]
                  | cons u us ihu =>
                    intro a ⟨h1, h2⟩ h3
                    refine ⟨fun y hy => ?_, ihu a h2 (fun y hy => h3 y (List.mem_cons_of_mem u hy))⟩
                    cases List.mem_append.mp hy with
                    | inl hm => exact h1 y hm
                    | inr hm =>
                      have hya : y = a := by simpa using hm
                      subst hya; exact Ne.symm (h3 u (List.mem_cons_self ..))
                exact happ (List.range m') m' ihm (fun y hy => by have := List.mem_range.mp hy; omega)
            exact hgen (List.range q) (hrange_nd q) (fun x hx => List.mem_range.mp hx) f
              (fun t ht hnot => absurd (List.mem_range.mpr ht) hnot)
          unfold matMulF P0
          rw [hsum_bij (fun t => P a t * R t b)]
          exact hPR a b ha hb
        calc matMulF q M0 (fun t j => matMulF n (fun a b => R (π0 a) b) L0inv t j) i j
            = matMulF n (matMulF q M0 (fun a b => R (π0 a) b)) L0inv i j := (matMulF_assoc q n M0 _ L0inv i j).symm
          _ = matMulF n (matMulF n L0 (matMulF q P0 (fun a b => R (π0 a) b))) L0inv i j :=
                matMulF_congr (fun t _ => matMulF_assoc n q L0 P0 _ i t) (fun _ _ => rfl)
          _ = matMulF n (matMulF n L0 matIdF) L0inv i j :=
                matMulF_congr (fun t ht => matMulF_congr (fun _ _ => rfl) (fun s hs => hPR0 s t hs ht)) (fun _ _ => rfl)
          _ = matMulF n L0 L0inv i j :=
                matMulF_congr (fun t ht => matMulF_id_right n L0 ht) (fun _ _ => rfl)
          _ = matIdF i j := hInv0.1 i j hi hj
      have hkk1 : matMulF q M0 (fun t j => matMulF n (fun a b => R (π0 a) b) L0inv t j) k' k' = 1 := by
        simpa [matIdF] using hM0R k' k' (by omega) (by omega)
      have hne1 : sumR q (fun t => M0 k' t * matMulF n (fun a b => R (π0 a) b) L0inv t k') ≠ 0 := by
        rw [show sumR q (fun t => M0 k' t * matMulF n (fun a b => R (π0 a) b) L0inv t k') = 1 from hkk1]
        exact Ne.symm SimpleField.zero_ne_one
      obtain ⟨p, hpq, hterm⟩ := exists_nonzero_of_sumR_ne_zero q _ hne1
      have hM0kp : M0 k' p ≠ 0 := by intro hz; rw [hz, zero_mul] at hterm; exact hterm rfl
      have hkp : k' ≤ p := Classical.byContradiction fun hlt => by
        have hz := hcols0 k' p (by omega) (by omega)
        unfold matIdF at hz
        have hne : k' ≠ p := by omega
        rw [ite_f hne] at hz
        exact hM0kp hz
      -- Swap columns `k'` and `p` in `π0`!
      let sw (t : Nat) : Nat := if t = k' then p else if t = p then k' else t
      let π1 (t : Nat) : Nat := π0 (sw t)
      let π1Inv (t : Nat) : Nat := sw (π0Inv t)
      have hsw_inv : ∀ t, sw (sw t) = t := fun t => by
        dsimp only [sw]
        by_cases h1 : t = k'
        · subst h1; by_cases h2 : t = p <;> simp [h2]
        · by_cases h2 : t = p
          · subst h2; simp [h1]
          · simp [h1, h2]
      have hsw_lt : ∀ t, t < q → sw t < q := fun t ht => by
        dsimp only [sw]; by_cases h1 : t = k'
        · rw [ite_t h1]; exact hpq
        · by_cases h2 : t = p
          · rw [ite_f h1, ite_t h2]; omega
          · rw [ite_f h1, ite_f h2]; exact ht
      have hbij1 : ∀ t, t < q → π1 t < q ∧ π1Inv t < q ∧ π1 (π1Inv t) = t ∧ π1Inv (π1 t) = t := by
        intro t ht
        refine ⟨(hbij0 (sw t) (hsw_lt t ht)).1, hsw_lt (π0Inv t) (hbij0 t ht).2.1, ?_, ?_⟩
        · dsimp only [π1, π1Inv]; rw [hsw_inv, (hbij0 t ht).2.2.1]
        · dsimp only [π1, π1Inv]; rw [(hbij0 (sw t) (hsw_lt t ht)).2.2.2, hsw_inv]
      let P1 : Nat → Nat → F := fun r c => P r (π1 c)
      let M1 : Nat → Nat → F := matMulF n L0 P1
      have hM1_eq : ∀ i j, M1 i j = M0 i (sw j) := fun i j => rfl
      have hM1kk : M1 k' k' ≠ 0 := by rw [hM1_eq]; dsimp only [sw]; simp [hM0kp]
      have hcols1 : ∀ i j, i < n → j < k' → M1 i j = matIdF i j := by
        intro i j hi hj
        rw [hM1_eq]; dsimp only [sw]
        have n1 : j ≠ k' := by omega
        have n2 : j ≠ p := by omega
        rw [ite_f n1, ite_f n2]; exact hcols0 i j hi hj
      -- Scale row `k'` and eliminate all other rows in column `k'`
      let α := SimpleField.inv (M1 k' k')
      have hαne : α ≠ 0 := by
        intro hz; have hc := SimpleField.mul_inv_cancel (M1 k' k') hM1kk
        change M1 k' k' * α = 1 at hc; rw [hz, mul_zero] at hc; exact SimpleField.zero_ne_one hc
      let Esc := elemScale k' α
      let EscInv := elemScale k' (SimpleField.inv α)
      let L2 := matMulF n Esc L0
      let L2inv := matMulF n L0inv EscInv
      have hInv2 : IsMatInv n L2 L2inv := isMatInv_mul (isMatInv_elemScale n k' α (by omega) hαne) hInv0
      let M2 := matMulF n L2 P1
      have hM2_eq : ∀ i j, i < n → M2 i j = setRow k' (fun c => α * M1 k' c) M1 i j := by
        intro i j hi; dsimp only [M2, L2]; rw [matMulF_assoc]; exact elemScale_mul n k' α M1 (by omega) i j hi
      have hM2kk : M2 k' k' = 1 := by
        rw [hM2_eq k' k' (by omega)]; unfold setRow; rw [ite_t rfl]; dsimp only; rw [CommRing.mul_comm]
        exact SimpleField.mul_inv_cancel (M1 k' k') hM1kk
      have hcols2 : ∀ i j, i < n → j < k' → M2 i j = matIdF i j := by
        intro i j hi hj
        rw [hM2_eq i j hi]; unfold setRow
        by_cases h : i = k'
        · rw [h, ite_t rfl]; dsimp only; rw [hcols1 k' j (by omega) hj]; unfold matIdF
          rw [ite_f (by omega), mul_zero]
        · rw [ite_f h]; exact hcols1 i j hi hj
      obtain ⟨Ee, EeInv, hInvE, _, hzeroE, hcolE, _⟩ :=
        elim_col_rows n k' (by omega) n M2 (Nat.le_refl n) hM2kk
      refine ⟨π1, π1Inv, matMulF n Ee L2, matMulF n L2inv EeInv, hbij1, isMatInv_mul hInvE hInv2, ?_⟩
      intro i j hi hj
      rw [matMulF_assoc]
      by_cases hjk : j = k'
      · subst hjk; exact hcolE i hi
      · have hjlt : j < k' := by omega
        have hM2kj : M2 k' j = 0 := by rw [hcols2 k' j (by omega) hjlt]; unfold matIdF; exact ite_f (by omega)
        rw [hzeroE i j hi hM2kj]; exact hcols2 i j hi hjlt
  obtain ⟨π, πInv, L, Linv, hbij, hInvL, hLP⟩ := hstep n (Nat.le_refl n)
  have hPLinv : MatEq n n (fun i j => P i (π j)) Linv := by
    intro i j hi hj
    calc P i (π j) = matMulF n matIdF (fun r c => P r (π c)) i j := (matMulF_id_left n _ hi).symm
      _ = matMulF n (matMulF n Linv L) (fun r c => P r (π c)) i j :=
            matMulF_congr (fun t ht => (hInvL.2 i t hi ht).symm) (fun _ _ => rfl)
      _ = matMulF n Linv (matMulF n L (fun r c => P r (π c))) i j := matMulF_assoc n n Linv L _ i j
      _ = matMulF n Linv matIdF i j := matMulF_congr (fun _ _ => rfl) (fun t ht => hLP t j ht hj)
      _ = Linv i j := matMulF_id_right n Linv hj
  refine ⟨hnq, π, πInv, L, hbij, ?_, hLP⟩
  intro i j hi hj
  rw [matMulF_congr (fun t ht => hPLinv i t hi ht) (fun _ _ => rfl)]
  exact hInvL.2 i j hi hj

-- ============================================================================
-- Section 3: Explicit `{0, 1}`-Matrix Invertible-Commutator Pair (`∀ m ≥ 2, ∀ F`)
-- ============================================================================

def commX2 {R : Type} [CommRing R] (i j : Nat) : R :=
  if i = 0 ∧ j = 0 then 1 else 0

def commY2 {R : Type} [CommRing R] (i j : Nat) : R :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0

def commX3 {R : Type} [CommRing R] (i j : Nat) : R :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) then 1 else 0

def commY3 {R : Type} [CommRing R] (i j : Nat) : R :=
  if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 2) then 1 else 0

/-- Explicit `{0, 1}`-matrix pair `(commPairX m, commPairY m)` with `detM m [X, Y] = 1` over `ℤ`
    (hence invertible over **EVERY `SimpleField F`, including `F_2`!**) for ALL `m ≥ 2`. -/
def commPairX {R : Type} [CommRing R] : Nat → Nat → Nat → R
  | 0 => fun _ _ => 0
  | 1 => fun _ _ => 0
  | 2 => commX2
  | 3 => commX3
  | m + 4 => blockDiag 2 commX2 (commPairX (m + 2))

def commPairY {R : Type} [CommRing R] : Nat → Nat → Nat → R
  | 0 => fun _ _ => 0
  | 1 => fun _ _ => 0
  | 2 => commY2
  | 3 => commY3
  | m + 4 => blockDiag 2 commY2 (commPairY (m + 2))

theorem matMulF_blockDiag {R : Type} [CommRing R] (a b : Nat) (A1 A2 B1 B2 : Nat → Nat → R) :
    MatEq (a + b) (a + b)
      (matMulF (a + b) (blockDiag a A1 B1) (blockDiag a A2 B2))
      (blockDiag a (matMulF a A1 A2) (matMulF b B1 B2)) := by
  intro i j hi hj
  unfold matMulF
  rw [sumR_split a b]
  by_cases hia : i < a
  · by_cases hja : j < a
    · have htail : sumR b (fun t => blockDiag a A1 B1 i (a + t) * blockDiag a A2 B2 (a + t) j) = 0 := by
        rw [sumR_congr (fun t _ => by unfold blockDiag; split <;> (try omega); split <;> (try omega); rw [zero_mul]), sumR_zero_fn]
      rw [htail, add_zero]
      unfold blockDiag; rw [ite_t ⟨hia, hja⟩]
      apply sumR_congr; intro t ht
      rw [ite_t ⟨hia, ht⟩, ite_t ⟨ht, hja⟩]
    · have h1 : sumR a (fun t => blockDiag a A1 B1 i t * blockDiag a A2 B2 t j) = 0 := by
        rw [sumR_congr (fun t ht => by
          have hb : blockDiag a A2 B2 t j = 0 := by unfold blockDiag; split <;> (try omega); split <;> (try omega); rfl
          rw [hb, mul_zero]), sumR_zero_fn]
      have h2 : sumR b (fun t => blockDiag a A1 B1 i (a + t) * blockDiag a A2 B2 (a + t) j) = 0 := by
        rw [sumR_congr (fun t _ => by unfold blockDiag; split <;> (try omega); split <;> (try omega); rw [zero_mul]), sumR_zero_fn]
      rw [h1, h2, add_zero]
      unfold blockDiag; split <;> (try omega); split <;> (try omega); rfl
  · by_cases hja : j < a
    · have h1 : sumR a (fun t => blockDiag a A1 B1 i t * blockDiag a A2 B2 t j) = 0 := by
        rw [sumR_congr (fun t _ => by unfold blockDiag; split <;> (try omega); split <;> (try omega); rw [zero_mul]), sumR_zero_fn]
      have h2 : sumR b (fun t => blockDiag a A1 B1 i (a + t) * blockDiag a A2 B2 (a + t) j) = 0 := by
        rw [sumR_congr (fun t _ => by
          unfold blockDiag; split <;> (try omega)
          have hb2 : blockDiag a A2 B2 (a + t) j = 0 := by unfold blockDiag; split <;> (try omega); split <;> (try omega); rfl
          unfold blockDiag at hb2; rw [hb2, mul_zero]), sumR_zero_fn]
      rw [h1, h2, add_zero]
      unfold blockDiag; split <;> (try omega); split <;> (try omega); rfl
    · have h1 : sumR a (fun t => blockDiag a A1 B1 i t * blockDiag a A2 B2 t j) = 0 := by
        rw [sumR_congr (fun t _ => by unfold blockDiag; split <;> (try omega); split <;> (try omega); rw [zero_mul]), sumR_zero_fn]
      rw [h1, CommRing.zero_add]
      unfold blockDiag
      have hnot : ¬ (i < a ∧ j < a) := by omega
      have hge : a ≤ i ∧ a ≤ j := by omega
      rw [ite_f hnot, ite_t hge]
      apply sumR_congr; intro t _
      have ha1 : ¬ (i < a ∧ a + t < a) := by omega
      have ha2 : a ≤ i ∧ a ≤ a + t := by omega
      have hb1 : ¬ (a + t < a ∧ j < a) := by omega
      have hb2 : a ≤ a + t ∧ a ≤ j := by omega
      have hsub : a + t - a = t := by omega
      rw [ite_f ha1, ite_t ha2, ite_f hb1, ite_t hb2, hsub]

theorem matComm_blockDiag {R : Type} [CommRing R] (a b : Nat) (X1 Y1 X2 Y2 : Nat → Nat → R) :
    MatEq (a + b) (a + b)
      (matComm (a + b) (blockDiag a X1 X2) (blockDiag a Y1 Y2))
      (blockDiag a (matComm a X1 Y1) (matComm b X2 Y2)) := by
  intro i j hi hj
  unfold matComm matSub
  rw [matMulF_blockDiag a b X1 Y1 X2 Y2 i j hi hj, matMulF_blockDiag a b Y1 X1 Y2 X2 i j hi hj]
  unfold blockDiag
  by_cases h1 : i < a ∧ j < a
  · rw [ite_t h1, ite_t h1, ite_t h1]
  · by_cases h2 : a ≤ i ∧ a ≤ j
    · rw [ite_f h1, ite_f h1, ite_f h1, ite_t h2, ite_t h2, ite_t h2]
    · rw [ite_f h1, ite_f h1, ite_f h1, ite_f h2, ite_f h2, ite_f h2, sub_self]

theorem detM_comm2 {R : Type} [CommRing R] :
    detM 2 (matComm 2 (commX2 (R := R)) commY2) = 1 := by
  have hc00 : matComm 2 (commX2 (R := R)) commY2 0 0 = 0 := by
    simp [matComm, matSub, matMulF, sumR, commX2, commY2, mul_zero, zero_mul, add_zero, sub_self]
  have hc01 : matComm 2 (commX2 (R := R)) commY2 0 1 = 1 := by
    simp [matComm, matSub, matMulF, sumR, commX2, commY2, mul_zero, add_zero, CommRing.zero_add, CommRing.one_mul, CommRing.sub_eq, neg_zero]
  have hc10 : matComm 2 (commX2 (R := R)) commY2 1 0 = -(1 : R) := by
    simp [matComm, matSub, matMulF, sumR, commX2, commY2, mul_zero, zero_mul, add_zero, CommRing.zero_add, CommRing.one_mul, CommRing.sub_eq]
  have hc11 : matComm 2 (commX2 (R := R)) commY2 1 1 = 0 := by
    simp [matComm, matSub, matMulF, sumR, commX2, commY2, mul_zero, zero_mul, add_zero, sub_self]
  simp [detM, sumR, minorMat, skipIdx, hc00, hc01, hc10, hc11,
        mul_zero, add_zero, CommRing.zero_add, mul_one, mul_neg, neg_neg]

theorem detM_comm3 {R : Type} [CommRing R] :
    detM 3 (matComm 3 (commX3 (R := R)) commY3) = 1 := by
  -- Compute each entry over `Int` via `intToR` so `decide` handles arithmetic cleanly!
  let Z : Nat → Nat → Int := fun i j =>
    matComm 3 (commX3 (R := Int)) commY3 i j
  have hZ : detM 3 Z = 1 := by
    -- Explicit 3×3 expansion over Int
    have h00 : Z 0 0 = 0 := by decide
    have h01 : Z 0 1 = 0 := by decide
    have h02 : Z 0 2 = -1 := by decide
    have h10 : Z 1 0 = 1 := by decide
    have h11 : Z 1 1 = 0 := by decide
    have h12 : Z 1 2 = 1 := by decide
    have h20 : Z 2 0 = -1 := by decide
    have h21 : Z 2 1 = -1 := by decide
    have h22 : Z 2 2 = 0 := by decide
    simp [detM, sumR, minorMat, skipIdx, h00, h01, h02, h10, h11, h12, h20, h21, h22]
  let φ : RingHom Int R :=
    ⟨intToR, intToR_zero, intToR_one, intToR_add, intToR_neg, intToR_mul⟩
  have hmap : MatEq 3 3 (fun i j => φ.toFun (Z i j)) (matComm 3 (commX3 (R := R)) commY3) := by
    intro i j _ _
    have hX : ∀ r c, φ.toFun (commX3 (R := Int) r c) = commX3 (R := R) r c := by
      intro r c; unfold commX3; split <;> simp [φ, intToR_one, intToR_zero]
    have hY : ∀ r c, φ.toFun (commY3 (R := Int) r c) = commY3 (R := R) r c := by
      intro r c; unfold commY3; split <;> simp [φ, intToR_one, intToR_zero]
    dsimp only [Z, matComm, matSub]
    rw [φ.map_sub, φ.map_matMulF, φ.map_matMulF]
    congr 1
    · exact matMulF_congr (fun t _ => hX i t) (fun t _ => hY t j)
    · exact matMulF_congr (fun t _ => hY i t) (fun t _ => hX t j)
  rw [← detM_congr 3 hmap, ← detM_map φ 3 Z, hZ, φ.map_one]

theorem detM_commPair {R : Type} [CommRing R] :
    ∀ m : Nat, 2 ≤ m → detM m (matComm m (commPairX (R := R) m) (commPairY m)) = 1
  | 0, hm => by omega
  | 1, hm => by omega
  | 2, _ => detM_comm2
  | 3, _ => detM_comm3
  | m + 4, _ => by
    simp only [commPairX, commPairY]
    have hadd : m + 4 = 2 + (m + 2) := by omega
    rw [hadd]
    rw [detM_congr (2 + (m + 2)) (matComm_blockDiag 2 (m + 2) commX2 commY2 (commPairX (m + 2)) (commPairY (m + 2)))]
    rw [detM_blockDiag 2 (m + 2), detM_comm2, detM_commPair (m + 2) (by omega), CommRing.one_mul]

-- ============================================================================
-- Section 4: Landsberg–Bläser Degree-`m` Subset Selection (Lemma 6.4)
-- ============================================================================

def sumList {R : Type} [CommRing R] : List R → R
  | [] => 0
  | x :: xs => x + sumList xs

theorem sumList_append {R : Type} [CommRing R] (l1 l2 : List R) :
    sumList (l1 ++ l2) = sumList l1 + sumList l2 := by
  induction l1 with
  | nil => simp [sumList, CommRing.zero_add]
  | cons x xs ih => simp only [List.cons_append, sumList, ih, CommRing.add_assoc]

theorem sumList_mul_left {R : Type} [CommRing R] (c : R) (l : List R) :
    c * sumList l = sumList (l.map (fun x => c * x)) := by
  induction l with
  | nil => simp [sumList, mul_zero]
  | cons x xs ih => simp only [List.map_cons, sumList, CommRing.left_distrib, ih]

theorem sumList_mul_right {R : Type} [CommRing R] (c : R) (l : List R) :
    sumList l * c = sumList (l.map (fun x => x * c)) := by
  induction l with
  | nil => simp [sumList, zero_mul]
  | cons x xs ih => simp only [List.map_cons, sumList, right_distrib, ih]

theorem sumList_map_add {R : Type} [CommRing R] {α : Type} (l : List α) (f g : α → R) :
    sumList (l.map (fun x => f x + g x)) = sumList (l.map f) + sumList (l.map g) := by
  induction l with
  | nil => simp [sumList, add_zero]
  | cons x xs ih =>
    simp only [List.map_cons, sumList, ih]
    rw [CommRing.add_assoc, ← CommRing.add_assoc (g x), CommRing.add_comm (g x) (sumList (xs.map f)),
        CommRing.add_assoc (sumList (xs.map f)), ← CommRing.add_assoc]

theorem sumList_map_zero {R : Type} [CommRing R] {α : Type} (l : List α) :
    sumList (l.map (fun _ => (0 : R))) = 0 := by
  induction l with
  | nil => rfl
  | cons _ xs ih => simp [sumList, ih, add_zero]

theorem sumList_map_congr {R : Type} [CommRing R] {α : Type} {l : List α} {f g : α → R}
    (h : ∀ x, x ∈ l → f x = g x) :
    sumList (l.map f) = sumList (l.map g) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, sumList]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem sumList_swap {R : Type} [CommRing R] {α β : Type} (l1 : List α) (l2 : List β) (f : α → β → R) :
    sumList (l1.map fun a => sumList (l2.map fun b => f a b)) =
    sumList (l2.map fun b => sumList (l1.map fun a => f a b)) := by
  induction l1 with
  | nil => simp [sumList, sumList_map_zero]
  | cons a as ih => simp only [List.map_cons, sumList, ih, sumList_map_add]

theorem sumList_flatMap {R : Type} [CommRing R] {α β : Type} (l : List α) (g : α → List β) (f : β → R) :
    sumList ((l.flatMap g).map f) = sumList (l.map fun a => sumList ((g a).map f)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.flatMap_cons, List.map_append, sumList_append, List.map_cons, sumList, ih]

theorem sumList_map_range {R : Type} [CommRing R] (n : Nat) (f : Nat → R) :
    sumList ((List.range n).map f) = sumR n f := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, sumList_append, ih]
    simp [sumR, sumList, add_zero]

theorem sumList_ringHom {R S : Type} [CommRing R] [CommRing S] (φ : RingHom R S) (l : List R) :
    φ.toFun (sumList l) = sumList (l.map φ.toFun) := by
  induction l with
  | nil => exact φ.map_zero
  | cons x xs ih => simp only [List.map_cons, sumList, φ.map_add, ih]

theorem exists_mem_ne_zero_of_sumList {R : Type} [CommRing R] {α : Type} (l : List α) (f : α → R)
    (h : sumList (l.map f) ≠ 0) : ∃ x, x ∈ l ∧ f x ≠ 0 := by
  induction l with
  | nil => exact absurd rfl h
  | cons a as ih =>
    simp only [List.map_cons, sumList] at h
    by_cases ha : f a = 0
    · rw [ha, CommRing.zero_add] at h
      obtain ⟨x, hx, hne⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem a hx, hne⟩
    · exact ⟨a, List.mem_cons_self .., ha⟩

-- All `k`-tuples in `{0..n-1}`, insertion sort, dedup, Kronecker base-`(m+1)` encoding

def allTuples (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range n).flatMap (fun i => (allTuples n k).map (fun t => i :: t))

theorem allTuples_len (n : Nat) : ∀ k t, t ∈ allTuples n k → t.length = k
  | 0, t, h => by
    have : t = [] := by simpa [allTuples] using h
    subst this; rfl
  | k + 1, t, h => by
    simp only [allTuples, List.mem_flatMap, List.mem_map] at h
    obtain ⟨i, _, t', ht', rfl⟩ := h
    simp [allTuples_len n k t' ht']

def prodTuple {R : Type} [CommRing R] (v : Nat → R) : List Nat → R
  | [] => 1
  | i :: t => v i * prodTuple v t

def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertNat x ys

def sortNat : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (sortNat xs)

def isSortedNat : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: ys => x ≤ y ∧ isSortedNat (y :: ys)

theorem insertNat_len (x : Nat) (l : List Nat) : (insertNat x l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih => unfold insertNat; split <;> simp [ih]

theorem sortNat_len (l : List Nat) : (sortNat l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sortNat, insertNat_len, ih]

theorem insertNat_sorted (x : Nat) : ∀ l : List Nat, isSortedNat l → isSortedNat (insertNat x l)
  | [], _ => trivial
  | [y], _ => by
    unfold insertNat; by_cases h : x ≤ y
    · simp [h, isSortedNat]
    · simp only [h, ↓reduceIte, insertNat, isSortedNat]; exact ⟨by omega, trivial⟩
  | y :: z :: zs, ⟨hyz, hzs⟩ => by
    unfold insertNat
    by_cases hxy : x ≤ y
    · simp [hxy, isSortedNat, hyz, hzs]
    · simp only [hxy, ↓reduceIte]
      have hsub := insertNat_sorted x (z :: zs) hzs
      unfold insertNat at hsub ⊢
      by_cases hxz : x ≤ z
      · simp only [hxz, ↓reduceIte] at hsub ⊢
        exact ⟨by omega, hsub⟩
      · simp only [hxz, ↓reduceIte] at hsub ⊢
        exact ⟨hyz, hsub⟩

theorem sortNat_sorted (l : List Nat) : isSortedNat (sortNat l) := by
  induction l with
  | nil => trivial
  | cons x xs ih => exact insertNat_sorted x (sortNat xs) ih

theorem prodTuple_insert {R : Type} [CommRing R] (v : Nat → R) (x : Nat) (l : List Nat) :
    prodTuple v (insertNat x l) = v x * prodTuple v l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    unfold insertNat
    by_cases h : x ≤ y
    · simp [h, prodTuple]
    · simp only [h, ↓reduceIte, prodTuple, ih]
      rw [← CommRing.mul_assoc, CommRing.mul_comm (v y) (v x), CommRing.mul_assoc]

theorem prodTuple_sort {R : Type} [CommRing R] (v : Nat → R) (l : List Nat) :
    prodTuple v (sortNat l) = prodTuple v l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [sortNat, prodTuple_insert, ih, prodTuple]

def dedupList {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then dedupList xs else x :: dedupList xs

theorem mem_dedupList {α : Type} [DecidableEq α] (l : List α) (x : α) :
    x ∈ dedupList l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedupList]
  | cons a as ih =>
    unfold dedupList
    by_cases h : a ∈ as
    · simp only [h, ↓reduceIte, ih, List.mem_cons]
      exact ⟨fun hm => Or.inr hm, fun hm => by cases hm with | inl e => subst e; exact h | inr m => exact m⟩
    · simp only [h, ↓reduceIte, List.mem_cons, ih]

theorem nodup_dedupList {α : Type} [DecidableEq α] (l : List α) : ListNodup (dedupList l) := by
  induction l with
  | nil => trivial
  | cons a as ih =>
    unfold dedupList
    by_cases h : a ∈ as
    · simp [h, ih]
    · simp only [h, ↓reduceIte, ListNodup]
      exact ⟨fun y hy hya => by subst hya; exact h ((mem_dedupList as y).mp hy), ih⟩

theorem dedupList_len_le {α : Type} [DecidableEq α] (l : List α) : (dedupList l).length ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a as ih =>
    unfold dedupList; by_cases h : a ∈ as <;> simp [h] <;> omega

theorem sumList_single_nodup {R : Type} [CommRing R] {α : Type} [DecidableEq α]
    (l : List α) (x : α) (v : R) (hnd : ListNodup l) (hmem : x ∈ l) :
    sumList (l.map fun y => if x = y then v else 0) = v := by
  induction l with
  | nil => simp at hmem
  | cons a as ih =>
    obtain ⟨hnot, hnda⟩ := hnd
    simp only [List.map_cons, sumList]
    by_cases hxa : x = a
    · subst hxa
      rw [ite_t rfl]
      have hz : sumList (as.map fun y => if x = y then v else 0) = 0 := by
        rw [sumList_map_congr (fun y hy => ite_f (Ne.symm (hnot y hy))), sumList_map_zero]
      rw [hz, add_zero]
    · rw [ite_f hxa, CommRing.zero_add]
      have hxin : x ∈ as := by cases hmem with | head => exact absurd rfl hxa | tail _ hm => exact hm
      exact ih hnda hxin

def idxOfNat : List Nat → Nat → Nat
  | [], _ => 0
  | y :: ys, x => if x = y then 0 else idxOfNat ys x + 1

def countInNat (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if y = x then 1 else 0) + countInNat x ys

theorem countInNat_le_len (x : Nat) (l : List Nat) : countInNat x l ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons y ys ih => unfold countInNat; split <;> simp <;> omega

theorem countInNat_zero_of_not_mem (x : Nat) (l : List Nat) (h : x ∉ l) : countInNat x l = 0 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    unfold countInNat
    have hne : y ≠ x := fun e => h (by subst e; exact List.mem_cons_self ..)
    rw [ite_f hne, Nat.zero_add]
    exact ih (fun m => h (List.mem_cons_of_mem y m))

theorem countInNat_pos_of_mem (x : Nat) (l : List Nat) (h : x ∈ l) : 0 < countInNat x l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    unfold countInNat
    cases h with
    | head => simp; omega
    | tail _ hm => have := ih hm; split <;> omega

theorem sorted_eq_of_countInNat : ∀ (l1 l2 : List Nat),
    isSortedNat l1 → isSortedNat l2 → (∀ x, countInNat x l1 = countInNat x l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, hc => by
    have h1 := hc y; simp [countInNat] at h1; omega
  | x :: xs, [], _, _, hc => by
    have h1 := hc x; simp [countInNat] at h1
  | x :: xs, y :: ys, hs1, hs2, hc => by
    have hmin_le : ∀ a l, isSortedNat (a :: l) → ∀ z, z ∈ a :: l → a ≤ z := by
      intro a l
      induction l generalizing a with
      | nil =>
        intro _ z hz
        have hza : z = a := by simpa using hz
        omega
      | cons b bs ihb =>
        intro ⟨hab, hbs⟩ z hz
        cases hz with
        | head => exact Nat.le_refl a
        | tail _ hm => exact Nat.le_trans hab (ihb b hbs z hm)
    have hx_in : x ∈ y :: ys := Classical.byContradiction fun hnot => by
      have h0 := countInNat_zero_of_not_mem x (y :: ys) hnot
      have hp := countInNat_pos_of_mem x (x :: xs) (List.mem_cons_self ..)
      rw [hc x] at hp; omega
    have hy_in : y ∈ x :: xs := Classical.byContradiction fun hnot => by
      have h0 := countInNat_zero_of_not_mem y (x :: xs) hnot
      have hp := countInNat_pos_of_mem y (y :: ys) (List.mem_cons_self ..)
      rw [← hc y] at hp; omega
    have hxy : x = y := Nat.le_antisymm (hmin_le x xs hs1 y hy_in) (hmin_le y ys hs2 x hx_in)
    subst hxy
    have hs1' : isSortedNat xs := by cases xs with | nil => trivial | cons _ _ => exact hs1.2
    have hs2' : isSortedNat ys := by cases ys with | nil => trivial | cons _ _ => exact hs2.2
    have hctail : ∀ z, countInNat z xs = countInNat z ys := by
      intro z; have hcz := hc z; simp only [countInNat] at hcz; omega
    rw [sorted_eq_of_countInNat xs ys hs1' hs2' hctail]

theorem base_repr_inj (B : Nat) (hB : 2 ≤ B) :
    ∀ (L : Nat) (d1 d2 : Nat → Nat),
      (∀ k, k < L → d1 k < B ∧ d2 k < B) →
      sumNat L (fun k => d1 k * B ^ k) = sumNat L (fun k => d2 k * B ^ k) →
      ∀ k, k < L → d1 k = d2 k
  | 0, _, _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | L + 1, d1, d2, hlt, heq, k, hk => by
    have hsplit : ∀ (N : Nat) (d : Nat → Nat), sumNat (N + 1) (fun i => d i * B ^ i) =
        d 0 + B * sumNat N (fun i => d (i + 1) * B ^ i) := by
      intro N d
      induction N with
      | zero => simp [sumNat]
      | succ j ihj =>
        change sumNat (j + 1) (fun i => d i * B ^ i) + d (j + 1) * B ^ (j + 1) =
               d 0 + B * (sumNat j (fun i => d (i + 1) * B ^ i) + d (j + 1) * B ^ j)
        rw [ihj, Nat.mul_add, Nat.add_assoc]
        congr 1
        rw [Nat.pow_succ, Nat.mul_comm (B ^ j) B, ← Nat.mul_assoc, Nat.mul_comm (d (j + 1)) B, Nat.mul_assoc]
    rw [hsplit L d1, hsplit L d2] at heq
    have hBpos : 0 < B := by omega
    have h0eq : d1 0 = d2 0 := by
      have hm := congrArg (· % B) heq
      rw [Nat.add_comm (d1 0), Nat.add_comm (d2 0), Nat.mul_add_mod, Nat.mul_add_mod,
          Nat.mod_eq_of_lt (hlt 0 (Nat.zero_lt_succ L)).1,
          Nat.mod_eq_of_lt (hlt 0 (Nat.zero_lt_succ L)).2] at hm
      exact hm
    have hqeq : sumNat L (fun i => d1 (i + 1) * B ^ i) = sumNat L (fun i => d2 (i + 1) * B ^ i) := by
      have hd := congrArg (· / B) heq
      rw [Nat.add_comm (d1 0), Nat.add_comm (d2 0),
          Nat.mul_add_div hBpos, Nat.mul_add_div hBpos,
          Nat.div_eq_of_lt (hlt 0 (Nat.zero_lt_succ L)).1,
          Nat.div_eq_of_lt (hlt 0 (Nat.zero_lt_succ L)).2,
          Nat.add_zero, Nat.add_zero] at hd
      exact hd
    cases k with
    | zero => exact h0eq
    | succ k' =>
      exact base_repr_inj B hB L (fun i => d1 (i + 1)) (fun i => d2 (i + 1))
        (fun i hi => hlt (i + 1) (Nat.succ_lt_succ hi)) hqeq k' (Nat.lt_of_succ_lt_succ hk)

def sumNatList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNatList xs

def kroneckerCode (m : Nat) (S μ : List Nat) : Nat :=
  sumNatList (μ.map fun i => (m + 1) ^ (idxOfNat S i))

theorem kroneckerCode_eq_digit_sum (m : Nat) (S : List Nat) (hnd : ListNodup S) :
    ∀ μ : List Nat, (∀ x, x ∈ μ → x ∈ S) →
      kroneckerCode m S μ = sumNat S.length (fun k => countInNat (S.getD k 0) μ * (m + 1) ^ k) := by
  have hgetIdx : ∀ (L : List Nat), ListNodup L → ∀ x, x ∈ L →
      idxOfNat L x < L.length ∧ L.getD (idxOfNat L x) 0 = x ∧
      ∀ k, k < L.length → (L.getD k 0 = x ↔ k = idxOfNat L x) := by
    intro L
    induction L with
    | nil => intro _ _ hm; simp at hm
    | cons a as ih =>
      intro ⟨hnot, hnda⟩ x hm
      unfold idxOfNat
      by_cases hxa : x = a
      · subst hxa
        simp only [↓reduceIte]
        refine ⟨Nat.zero_lt_succ _, by simp, fun k hk => ?_⟩
        cases k with
        | zero => simp
        | succ k' =>
          have hmem : as.getD k' 0 ∈ as := by
            have hk' : k' < as.length := Nat.lt_of_succ_lt_succ hk
            have hgm : ∀ (L : List Nat) (t : Nat), t < L.length → L.getD t 0 ∈ L := by
              intro L; induction L with
              | nil => intro _ ht; simp at ht
              | cons u us ihu =>
                intro t ht; cases t with
                | zero => exact List.mem_cons_self ..
                | succ t' => exact List.mem_cons_of_mem u (ihu t' (Nat.lt_of_succ_lt_succ ht))
            exact hgm as k' hk'
          have hne := hnot (as.getD k' 0) hmem
          simp only [List.getD_cons_succ, Nat.succ_ne_zero, iff_false]
          exact hne
      · have hxin : x ∈ as := by cases hm with | head => exact absurd rfl hxa | tail _ h' => exact h'
        obtain ⟨hlt, hget, hiff⟩ := ih hnda x hxin
        simp only [hxa, ↓reduceIte]
        refine ⟨Nat.succ_lt_succ hlt, by simpa using hget, fun k hk => ?_⟩
        cases k with
        | zero => simp [Ne.symm hxa]
        | succ k' =>
          simp only [List.getD_cons_succ, Nat.succ_inj]
          exact hiff k' (Nat.lt_of_succ_lt_succ hk)
  intro μ hsupp
  induction μ with
  | nil =>
    simp only [kroneckerCode, List.map_nil, sumNatList]
    symm
    have hz : sumNat S.length (fun k => countInNat (S.getD k 0) [] * (m + 1) ^ k) = sumNat S.length (fun _ => 0) :=
      sumNat_congr (fun k _ => by simp [countInNat])
    rw [hz]
    have h0 : ∀ n : Nat, sumNat n (fun _ => 0) = 0 := by
      intro n; induction n with | zero => rfl | succ j ihj => simp [sumNat, ihj]
    exact h0 S.length
  | cons x xs ih =>
    have hxS : x ∈ S := hsupp x (List.mem_cons_self ..)
    have hxsS : ∀ y, y ∈ xs → y ∈ S := fun y hy => hsupp y (List.mem_cons_of_mem x hy)
    have hstep : kroneckerCode m S (x :: xs) = (m + 1) ^ (idxOfNat S x) + kroneckerCode m S xs := rfl
    rw [hstep, ih hxsS]
    obtain ⟨hidx_lt, _, hiff⟩ := hgetIdx S hnd x hxS
    have hadd_sum : ∀ (n : Nat) (f g : Nat → Nat), sumNat n (fun k => f k + g k) = sumNat n f + sumNat n g := by
      intro n f g; induction n with | zero => rfl | succ j ihj => simp [sumNat, ihj]; omega
    have hsingle_nat : ∀ (n j v : Nat), j < n → sumNat n (fun k => if k = j then v else 0) = v := by
      intro n j v hj
      have h : ∀ t : Nat, sumNat t (fun k => if k = j then v else 0) = if j < t then v else 0 := by
        intro t; induction t with
        | zero => simp [sumNat]
        | succ u ihu =>
          simp only [sumNat, ihu]
          by_cases huj : u = j
          · subst huj; simp
          · have h1 : (j < u + 1) ↔ (j < u) := by omega
            simp [huj, h1]
      rw [h n, ite_t hj]
    have hrew : sumNat S.length (fun k => countInNat (S.getD k 0) (x :: xs) * (m + 1) ^ k) =
        sumNat S.length (fun k => (if k = idxOfNat S x then (m + 1) ^ (idxOfNat S x) else 0) +
          countInNat (S.getD k 0) xs * (m + 1) ^ k) := by
      apply sumNat_congr; intro k hk
      have hc : countInNat (S.getD k 0) (x :: xs) =
          (if x = S.getD k 0 then 1 else 0) + countInNat (S.getD k 0) xs := rfl
      rw [hc, Nat.add_mul]
      congr 1
      by_cases hke : k = idxOfNat S x
      · subst hke
        have heq : x = S.getD (idxOfNat S x) 0 := ((hiff (idxOfNat S x) hidx_lt).mpr rfl).symm
        rw [ite_t heq, ite_t rfl, Nat.one_mul]
      · have hne : x ≠ S.getD k 0 := fun e => hke ((hiff k hk).mp e.symm)
        rw [ite_f hne, ite_f hke, Nat.zero_mul]
    rw [hrew, hadd_sum, hsingle_nat S.length (idxOfNat S x) _ hidx_lt]

theorem kroneckerCode_inj (m : Nat) (S : List Nat) (hnd : ListNodup S)
    (μ1 μ2 : List Nat) (hs1 : isSortedNat μ1) (hs2 : isSortedNat μ2)
    (hl1 : μ1.length = m) (hl2 : μ2.length = m)
    (hsup1 : ∀ x, x ∈ μ1 → x ∈ S) (hsup2 : ∀ x, x ∈ μ2 → x ∈ S)
    (hcode : kroneckerCode m S μ1 = kroneckerCode m S μ2) : μ1 = μ2 := by
  by_cases hm0 : m = 0
  · subst hm0
    cases μ1 with
    | nil => cases μ2 with | nil => rfl | cons _ _ => simp at hl2
    | cons _ _ => simp at hl1
  · rw [kroneckerCode_eq_digit_sum m S hnd μ1 hsup1,
        kroneckerCode_eq_digit_sum m S hnd μ2 hsup2] at hcode
    have hdigits := base_repr_inj (m + 1) (by omega) S.length
      (fun k => countInNat (S.getD k 0) μ1) (fun k => countInNat (S.getD k 0) μ2)
      (fun k _ => ⟨by have := countInNat_le_len (S.getD k 0) μ1; omega,
                   by have := countInNat_le_len (S.getD k 0) μ2; omega⟩)
      hcode
    apply sorted_eq_of_countInNat μ1 μ2 hs1 hs2
    intro x
    by_cases hx : x ∈ S
    · -- Find `k < S.length` with `S.getD k 0 = x`
      have hfind : ∀ (L : List Nat), x ∈ L → ∃ k, k < L.length ∧ L.getD k 0 = x := by
        intro L
        induction L with
        | nil => intro h; simp at h
        | cons a as ihs =>
          intro h
          cases h with
          | head => exact ⟨0, Nat.zero_lt_succ _, rfl⟩
          | tail _ hm =>
            obtain ⟨k, hk, heq⟩ := ihs hm
            exact ⟨k + 1, Nat.succ_lt_succ hk, by simpa using heq⟩
      obtain ⟨k, hk, hget⟩ := hfind S hx
      rw [← hget]
      exact hdigits k hk
    · rw [countInNat_zero_of_not_mem x μ1 (fun hm => hx (hsup1 x hm)),
          countInNat_zero_of_not_mem x μ2 (fun hm => hx (hsup2 x hm))]

def matSubRows {R : Type} (k : Nat) (t : List Nat) (M : Nat → Nat → Nat → R)
    (A : Nat → Nat → R) (r c : Nat) : R :=
  if r < k then M (t.getD (k - 1 - r) 0) r c else A r c

theorem detM_row_lin_expand {R : Type} [CommRing R] (m n : Nat) (v : Nat → R)
    (M : Nat → Nat → Nat → R) :
    ∀ (k : Nat) (A : Nat → Nat → R), k ≤ m →
      detM m (fun r c => if r < k then sumR n (fun i => v i * M i r c) else A r c) =
      sumList ((allTuples n k).map fun t => prodTuple v t * detM m (matSubRows k t M A))
  | 0, A, _ => by
    simp only [allTuples, List.map_cons, List.map_nil, sumList, prodTuple, CommRing.one_mul, add_zero]
    apply detM_congr m; intro r c _ _; unfold matSubRows; simp
  | k + 1, A, hk => by
    have hset : MatEq m m
        (fun r c => if r < k + 1 then sumR n (fun i => v i * M i r c) else A r c)
        (setRow k (fun c => sumR n (fun i => v i * M i k c))
          (fun r c => if r < k then sumR n (fun i => v i * M i r c) else A r c)) := by
      intro r c _ _; unfold setRow
      by_cases hrk : r = k
      · subst hrk; simp
      · have hiff : (r < k + 1) ↔ (r < k) := by omega
        simp [hrk, hiff]
    rw [detM_congr m hset, detM_row_sum m k n v (fun i c => M i k c) _ (by omega)]
    rw [← sumList_map_range n]
    simp only [allTuples, sumList_flatMap]
    apply sumList_map_congr; intro i _
    have hmat : MatEq m m
        (setRow k (fun c => M i k c) (fun r c => if r < k then sumR n (fun j => v j * M j r c) else A r c))
        (fun r c => if r < k then sumR n (fun j => v j * M j r c) else setRow k (fun c => M i k c) A r c) := by
      intro r c _ _; unfold setRow
      by_cases hrk : r = k
      · subst hrk; simp
      · by_cases hlt : r < k <;> simp [hrk, hlt]
    rw [detM_congr m hmat, detM_row_lin_expand m n v M k (setRow k (fun c => M i k c) A) (by omega),
        sumList_mul_left, List.map_map, List.map_map]
    apply sumList_map_congr; intro t _
    dsimp only [Function.comp, prodTuple]
    rw [← CommRing.mul_assoc]
    congr 1
    apply detM_congr m; intro r c _ _
    unfold matSubRows setRow
    by_cases hrk : r = k
    · subst hrk; simp
    · by_cases hlt : r < k
      · have hlt1 : r < k + 1 := by omega
        have hsub : k + 1 - 1 - r = (k - 1 - r) + 1 := by omega
        rw [ite_t hlt, ite_t hlt1, hsub]; rfl
      · have hnot1 : ¬ (r < k + 1) := by omega
        simp [hlt, hnot1, hrk]

theorem detM_lincomb_grouped {F R : Type} [SimpleField F] [CommRing R] (φ : RingHom F R)
    (m n : Nat) (M : Nat → Nat → Nat → F) (v : Nat → R) :
    let allT := allTuples n m
    let uSorts := dedupList (allT.map sortNat)
    let mCoeff (μ : List Nat) : F :=
      sumList (allT.map fun t => if sortNat t = μ then detM m (matSubRows m t M (fun _ _ => 0)) else 0)
    detM m (fun r c => sumR n (fun i => v i * φ.toFun (M i r c))) =
    sumList (uSorts.map fun μ => prodTuple v μ * φ.toFun (mCoeff μ)) := by
  intro allT uSorts mCoeff
  have hexp := detM_row_lin_expand m n v (fun i r c => φ.toFun (M i r c)) m (fun _ _ => 0) (Nat.le_refl m)
  have hL : detM m (fun r c => sumR n (fun i => v i * φ.toFun (M i r c))) =
      detM m (fun r c => if r < m then sumR n (fun i => v i * φ.toFun (M i r c)) else 0) :=
    detM_congr m (fun r c hr _ => (ite_t hr).symm)
  rw [hL, hexp]
  have hR : sumList (uSorts.map fun μ => prodTuple v μ * φ.toFun (mCoeff μ)) =
      sumList (uSorts.map fun μ => sumList (allT.map fun t =>
        if sortNat t = μ then prodTuple v μ * φ.toFun (detM m (matSubRows m t M (fun _ _ => 0))) else 0)) := by
    apply sumList_map_congr; intro μ _
    dsimp only [mCoeff]
    rw [sumList_ringHom, sumList_mul_left, List.map_map, List.map_map]
    apply sumList_map_congr; intro t _
    dsimp only [Function.comp]
    by_cases h : sortNat t = μ
    · rw [ite_t h, ite_t h]
    · rw [ite_f h, ite_f h, φ.map_zero, mul_zero]
  rw [hR, sumList_swap]
  apply sumList_map_congr; intro t ht
  have hmem : sortNat t ∈ uSorts := (mem_dedupList (allT.map sortNat) _).mpr (List.mem_map_of_mem ht)
  have hnd : ListNodup uSorts := nodup_dedupList _
  have hfix : sumList (uSorts.map fun μ =>
        if sortNat t = μ then prodTuple v μ * φ.toFun (detM m (matSubRows m t M (fun _ _ => 0))) else 0) =
      sumList (uSorts.map fun μ =>
        if sortNat t = μ then prodTuple v (sortNat t) * φ.toFun (detM m (matSubRows m t M (fun _ _ => 0))) else 0) := by
    apply sumList_map_congr; intro μ _
    by_cases h : sortNat t = μ
    · rw [h]
    · rw [ite_f h, ite_f h]
  rw [hfix, sumList_single_nodup uSorts (sortNat t) _ hnd hmem, prodTuple_sort]
  congr 1
  rw [detM_map φ m]
  apply detM_congr m; intro r c hr _
  unfold matSubRows; dsimp only; rw [ite_t hr, ite_t hr]

private def sumPolyBy {F : Type} [SimpleField F] (f : List Nat → Poly F) : List (List Nat) → Poly F
  | [] => pZero
  | μ :: μs => pAdd (f μ) (sumPolyBy f μs)

/-- **Landsberg–Bläser Degree-`m` Subset Selection Lemma (Lemma 6.4, over ANY `SimpleField F`):**
    If `a_0 M_0 + ... + a_{n-1} M_{n-1}` is invertible (`detM m ≠ 0`), then there exist a subset
    `S` of at most `m` indices (`S.length ≤ m`) and coefficients `x : Nat → RatFunc F` supported
    ONLY on `S` such that `∑_{i < n} x_i · ratConst(M_i)` is invertible over `RatFunc F`! -/
theorem exists_le_m_subset_det_ne_zero {F : Type} [SimpleField F] (m n : Nat)
    (M : Nat → Nat → Nat → F) (a : Nat → F)
    (hdet : detM m (fun r c => sumR n (fun i => a i * M i r c)) ≠ 0) :
    ∃ (S : List Nat) (x : Nat → RatFunc F),
      S.length ≤ m ∧
      (∀ i, i ∉ S → x i = 0) ∧
      detM m (fun r c => sumR n (fun i => x i * ratConst (M i r c))) ≠ 0 := by
  let allT := allTuples n m
  let uSorts := dedupList (allT.map sortNat)
  let mCoeff (μ : List Nat) : F :=
    sumList (allT.map fun t => if sortNat t = μ then detM m (matSubRows m t M (fun _ _ => 0)) else 0)
  -- Step 1: Identify a monomial `μ* ∈ uSorts` with `mCoeff μ* ≠ 0` using `φ = id` on `F`
  let idHom : RingHom F F := ⟨id, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  have hid := detM_lincomb_grouped idHom m n M a
  dsimp only [idHom, id] at hid
  rw [hid] at hdet
  obtain ⟨μstar, hμ_mem, hterm_nz⟩ := exists_mem_ne_zero_of_sumList uSorts _ hdet
  have hcoeff_nz : mCoeff μstar ≠ 0 := by
    intro hz; dsimp only [mCoeff, allT] at hz; rw [hz, mul_zero] at hterm_nz; exact hterm_nz rfl
  have hμ_info : ∀ μ, μ ∈ uSorts → μ.length = m ∧ isSortedNat μ := by
    intro μ hμ
    have hmap := (mem_dedupList _ _).mp hμ
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmap
    exact ⟨by rw [sortNat_len, allTuples_len n m t ht], sortNat_sorted t⟩
  obtain ⟨hμstar_len, hμstar_sorted⟩ := hμ_info μstar hμ_mem
  -- Step 2: Set `S := dedupList μstar` (`S.length ≤ m`, `ListNodup S`) and Kronecker powers in `Poly F`
  let S := dedupList μstar
  have hS_len : S.length ≤ m := by rw [← hμstar_len]; exact dedupList_len_le μstar
  have hS_nd : ListNodup S := nodup_dedupList μstar
  have hμstar_sup : ∀ x, x ∈ μstar → x ∈ S := fun x hx => (mem_dedupList μstar x).mpr hx
  let vPoly (i : Nat) : Poly F :=
    if i ∈ S then pMono ((m + 1) ^ (idxOfNat S i)) else pZero
  let xRat (i : Nat) : RatFunc F := ratPolyEmbed (vPoly i)
  refine ⟨S, xRat, hS_len, ?_, ?_⟩
  · intro i hi
    dsimp only [xRat, vPoly]; rw [ite_f hi]; exact ratPolyEmbed_zero
  · -- Evaluate `detM m (∑ xRat i * ratConst (M i))` via `detM_lincomb_grouped` over `RatFunc F`!
    have hexpR := detM_lincomb_grouped (ratConstHom F) m n M xRat
    change detM m (fun r c => sumR n (fun i => xRat i * (ratConstHom F).toFun (M i r c))) ≠ 0
    rw [hexpR]
    -- Show each `prodTuple xRat μ * ratConst (mCoeff μ)` equals `ratPolyEmbed (...)`!
    have hprod_poly : ∀ (l : List Nat),
        (∃ z, z ∈ l ∧ z ∉ S) → prodTuple xRat l = 0 := by
      intro l ⟨z, hz, hzn⟩
      induction l with
      | nil => simp at hz
      | cons u us ihu =>
        simp only [prodTuple]
        cases hz with
        | head =>
          have hu0 : xRat z = 0 := by dsimp only [xRat, vPoly]; rw [ite_f hzn]; exact ratPolyEmbed_zero
          rw [hu0, zero_mul]
        | tail _ hm => rw [ihu hm, mul_zero]
    have hprod_mono : ∀ (l : List Nat), (∀ z, z ∈ l → z ∈ S) →
        prodTuple xRat l = ratPolyEmbed (pMono (kroneckerCode m S l)) := by
      intro l
      induction l with
      | nil =>
        intro _
        simp only [prodTuple, kroneckerCode, List.map_nil, sumNatList]
        unfold ratPolyEmbed
        apply Quotient.sound
        change ratRel _ _; unfold ratRel; dsimp only
        intro k; rw [pAt_pMul, pAt_pMul]
        apply sumR_congr; intro i _; rw [pAt_pOne, pAt_pMono]
      | cons u us ihu =>
        intro hsup
        have huS : u ∈ S := hsup u (List.mem_cons_self ..)
        simp only [prodTuple, kroneckerCode, List.map_cons, sumNatList]
        rw [ihu (fun z hz => hsup z (List.mem_cons_of_mem u hz))]
        have hxu : xRat u = ratPolyEmbed (pMono ((m + 1) ^ (idxOfNat S u))) := by
          dsimp only [xRat, vPoly]; rw [ite_t huS]
        rw [hxu, ← ratPolyEmbed_mul]
        unfold ratPolyEmbed
        apply Quotient.sound
        have hmul_mono : ∀ a b : Nat, pEq (pMul (pMono (F := F) a) (pMono b)) (pMono (a + b)) := by
          intro a b k
          rw [pAt_pMul, pAt_pMono]
          by_cases hkab : k = a + b
          · subst hkab
            have hs : sumR (a + b + 1) (fun i => pAt (pMono (F := F) a) i * pAt (pMono b) (a + b - i)) =
                sumR (a + b + 1) (fun i => if i = a then 1 else 0) := by
              apply sumR_congr; intro i _
              rw [pAt_pMono, pAt_pMono]
              by_cases hia : i = a
              · rw [hia]; have hsub : a + b - a = b := by omega
                simp [hsub, CommRing.one_mul]
              · simp [hia, zero_mul]
            rw [hs, sumR_single (a + b + 1) a 1 (by omega), ite_t rfl]
          · rw [ite_f hkab]
            have hs : sumR (k + 1) (fun i => pAt (pMono (F := F) a) i * pAt (pMono b) (k - i)) =
                sumR (k + 1) (fun _ => (0 : F)) := by
              apply sumR_congr; intro i _
              rw [pAt_pMono, pAt_pMono]
              by_cases hia : i = a
              · rw [hia]; have hne : k - a ≠ b := by omega
                simp [hne, mul_zero]
              · simp [hia, zero_mul]
            rw [hs, sumR_zero_fn]
        exact pMul_congr (hmul_mono _ _) (pEq_refl _)
    -- Pull the entire `sumList` over `uSorts` into a single `Poly F` via `ratPolyEmbed`!
    let termPoly (μ : List Nat) : Poly F :=
      if ∀ z, z ∈ μ → z ∈ S then pMul (pMono (kroneckerCode m S μ)) (pConst (mCoeff μ)) else pZero
    have hsum_embed : ∀ L : List (List Nat),
        sumList (L.map fun μ => prodTuple xRat μ * ratConst (mCoeff μ)) = ratPolyEmbed (sumPolyBy termPoly L) := by
      intro L
      induction L with
      | nil => exact ratPolyEmbed_zero.symm
      | cons μ μs ih =>
        simp only [List.map_cons, sumList, sumPolyBy, ratPolyEmbed_add, ih]
        congr 1
        dsimp only [termPoly]
        by_cases hsup : ∀ z, z ∈ μ → z ∈ S
        · rw [ite_t hsup, hprod_mono μ hsup, ratPolyEmbed_mul]; rfl
        · rw [ite_f hsup, ratPolyEmbed_zero]
          have hex : ∃ z, z ∈ μ ∧ z ∉ S := Classical.byContradiction fun hall =>
            hsup (fun z hz => Classical.byContradiction fun hn => hall ⟨z, hz, hn⟩)
          rw [hprod_poly μ hex, zero_mul]
    rw [show sumList (uSorts.map fun μ => prodTuple xRat μ * (ratConstHom F).toFun (mCoeff μ)) =
             ratPolyEmbed (sumPolyBy termPoly uSorts) from hsum_embed uSorts]
    -- Show `pAt (sumPolyBy termPoly uSorts) (kroneckerCode m S μstar) = mCoeff μstar ≠ 0`!
    let Dstar := kroneckerCode m S μstar
    have hcoeff_Dstar : ∀ L : List (List Nat), ListNodup L → (∀ μ, μ ∈ L → μ.length = m ∧ isSortedNat μ) →
        pAt (sumPolyBy termPoly L) Dstar = if μstar ∈ L then mCoeff μstar else 0 := by
      intro L
      induction L with
      | nil => intro _ _; simp [sumPolyBy, pAt_pZero]
      | cons μ μs ih =>
        intro ⟨hnot, hnd⟩ hinf
        simp only [sumPolyBy, pAt_pAdd]
        rw [ih hnd (fun y hy => hinf y (List.mem_cons_of_mem μ hy))]
        have hterm_at : pAt (termPoly μ) Dstar = if μ = μstar then mCoeff μstar else 0 := by
          dsimp only [termPoly]
          by_cases hsup : ∀ z, z ∈ μ → z ∈ S
          · rw [ite_t hsup, pAt_pMul]
            have hsingle : sumR (Dstar + 1) (fun i => pAt (pMono (kroneckerCode m S μ)) i * pAt (pConst (mCoeff μ)) (Dstar - i)) =
                if kroneckerCode m S μ = Dstar then mCoeff μ else 0 := by
              have hrew : sumR (Dstar + 1) (fun i => pAt (pMono (kroneckerCode m S μ)) i * pAt (pConst (mCoeff μ)) (Dstar - i)) =
                  sumR (Dstar + 1) (fun i => if i = Dstar then (if kroneckerCode m S μ = Dstar then mCoeff μ else 0) else 0) := by
                apply sumR_congr; intro i hi
                rw [pAt_pMono, pAt_pConst]
                by_cases hid : i = Dstar
                · subst hid
                  have hs0 : Dstar - Dstar = 0 := Nat.sub_self Dstar
                  rw [hs0, ite_t rfl, ite_t rfl]
                  by_cases hc : kroneckerCode m S μ = Dstar
                  · rw [hc, ite_t rfl, ite_t rfl, CommRing.one_mul]
                  · have hc' : Dstar ≠ kroneckerCode m S μ := Ne.symm hc
                    rw [ite_f hc, ite_f hc', zero_mul]
                · have hne0 : Dstar - i ≠ 0 := by omega
                  rw [ite_f hne0, ite_f hid, mul_zero]
              rw [hrew, sumR_single (Dstar + 1) Dstar _ (Nat.lt_succ_self Dstar)]
            rw [hsingle]
            by_cases hμeq : μ = μstar
            · subst hμeq; simp [Dstar]
            · have hcode_ne : kroneckerCode m S μ ≠ Dstar := by
                intro hceq
                obtain ⟨hl, hs⟩ := hinf μ (List.mem_cons_self ..)
                exact hμeq (kroneckerCode_inj m S hS_nd μ μstar hs hμstar_sorted hl hμstar_len hsup hμstar_sup hceq)
              rw [ite_f hcode_ne, ite_f hμeq]
          · rw [ite_f hsup, pAt_pZero]
            by_cases hμeq : μ = μstar
            · subst hμeq; exact absurd hμstar_sup hsup
            · rw [ite_f hμeq]
        rw [hterm_at]
        by_cases hμeq : μ = μstar
        · subst hμeq
          have hnotin : μ ∉ μs := fun hm => hnot μ hm rfl
          rw [ite_t rfl, ite_f hnotin, ite_t (List.mem_cons_self ..), add_zero]
        · rw [ite_f hμeq, CommRing.zero_add]
          have hiff : (μstar ∈ μ :: μs) ↔ (μstar ∈ μs) := by
            simp [List.mem_cons, Ne.symm hμeq]
          by_cases hm : μstar ∈ μs
          · rw [ite_t hm, ite_t (hiff.mpr hm)]
          · rw [ite_f hm, ite_f (fun h => hm (hiff.mp h))]
    intro hz
    have h0 := ratPolyEmbed_eq_zero hz Dstar
    rw [hcoeff_Dstar uSorts (nodup_dedupList _) hμ_info, ite_t hμ_mem] at h0
    exact hcoeff_nz h0

-- ============================================================================
-- Section 5: Strassen's Commutator Equation (`strassen_commutator_bound`)
-- ============================================================================

/-- Partition `{0..q-1}` into indices satisfying `P` vs `¬ P`. -/
private noncomputable def filterRange (q : Nat) (P : Nat → Prop) : List Nat :=
  (List.range q).filter (fun s => @decide (P s) (Classical.propDecidable _))

private theorem sumR_partition {F : Type} [SimpleField F] (q : Nat) (P : Nat → Prop) (f : Nat → F) :
    let L0 := filterRange q P
    let L1 := filterRange q (fun s => ¬ P s)
    L0.length + L1.length = q ∧
    (∀ t, t < L0.length → L0.getD t 0 < q ∧ P (L0.getD t 0)) ∧
    (∀ t, t < L1.length → L1.getD t 0 < q ∧ ¬ P (L1.getD t 0)) ∧
    sumR q f = sumR L0.length (fun t => f (L0.getD t 0)) + sumR L1.length (fun t => f (L1.getD t 0)) := by
  have haux : ∀ n : Nat,
      let L0 := filterRange n P
      let L1 := filterRange n (fun s => ¬ P s)
      L0.length + L1.length = n ∧
      (∀ t, t < L0.length → L0.getD t 0 < n ∧ P (L0.getD t 0)) ∧
      (∀ t, t < L1.length → L1.getD t 0 < n ∧ ¬ P (L1.getD t 0)) ∧
      sumR n f = sumR L0.length (fun t => f (L0.getD t 0)) + sumR L1.length (fun t => f (L1.getD t 0)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
      simp [filterRange, sumR, add_zero]
    | succ m ih =>
      obtain ⟨hlen, h0, h1, hsum⟩ := ih
      have hfil_succ : ∀ (Q : Nat → Prop),
          filterRange (m + 1) Q =
          if @decide (Q m) (Classical.propDecidable _) then filterRange m Q ++ [m] else filterRange m Q := by
        intro Q
        unfold filterRange
        rw [List.range_succ, List.filter_append]
        by_cases hq : Q m
        · simp [hq]
        · simp [hq]
      have hget_append_end : ∀ (L : List Nat) (a t : Nat),
          (L ++ [a]).getD t 0 = if t < L.length then L.getD t 0 else if t = L.length then a else 0 := by
        intro L a t
        induction L generalizing t with
        | nil => cases t with | zero => simp | succ _ => simp
        | cons x xs ihL =>
          cases t with
          | zero => simp
          | succ t' =>
            simp only [List.cons_append, List.getD_cons_succ, List.length_cons, ihL t']
            by_cases h1 : t' < xs.length
            · rw [ite_t h1, ite_t (Nat.succ_lt_succ h1)]
            · rw [ite_f h1, ite_f (by omega : ¬ (t' + 1 < xs.length + 1))]
              by_cases h2 : t' = xs.length
              · rw [ite_t h2, ite_t (by omega : t' + 1 = xs.length + 1)]
              · rw [ite_f h2, ite_f (by omega : ¬ (t' + 1 = xs.length + 1))]
      by_cases hpm : P m
      · have hL0 : filterRange (m + 1) P = filterRange m P ++ [m] := by rw [hfil_succ]; simp [hpm]
        have hL1 : filterRange (m + 1) (fun s => ¬ P s) = filterRange m (fun s => ¬ P s) := by rw [hfil_succ]; simp [hpm]
        rw [hL0, hL1]
        refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_, ?_⟩
        · intro t ht
          rw [hget_append_end]
          by_cases hlt : t < (filterRange m P).length
          · rw [ite_t hlt]; have := h0 t hlt; exact ⟨by omega, this.2⟩
          · have heq : t = (filterRange m P).length := by simp at ht; omega
            rw [ite_f hlt, ite_t heq]; exact ⟨Nat.lt_succ_self m, hpm⟩
        · intro t ht; have := h1 t ht; exact ⟨by omega, this.2⟩
        · rw [List.length_append, List.length_singleton, sumR, hsum]
          have hc : sumR ((filterRange m P).length + 1) (fun t => f ((filterRange m P ++ [m]).getD t 0)) =
              sumR (filterRange m P).length (fun t => f ((filterRange m P).getD t 0)) + f m := by
            simp only [sumR]
            congr 1
            · exact sumR_congr (fun t ht => by rw [hget_append_end, ite_t ht])
            · rw [hget_append_end, ite_f (Nat.lt_irrefl _), ite_t rfl]
          rw [hc, CommRing.add_assoc, CommRing.add_comm _ (f m), ← CommRing.add_assoc]
      · have hL0 : filterRange (m + 1) P = filterRange m P := by rw [hfil_succ]; simp [hpm]
        have hL1 : filterRange (m + 1) (fun s => ¬ P s) = filterRange m (fun s => ¬ P s) ++ [m] := by rw [hfil_succ]; simp [hpm]
        rw [hL0, hL1]
        refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_, ?_⟩
        · intro t ht; have := h0 t ht; exact ⟨by omega, this.2⟩
        · intro t ht
          rw [hget_append_end]
          by_cases hlt : t < (filterRange m (fun s => ¬ P s)).length
          · rw [ite_t hlt]; have := h1 t hlt; exact ⟨by omega, this.2⟩
          · have heq : t = (filterRange m (fun s => ¬ P s)).length := by simp at ht; omega
            rw [ite_f hlt, ite_t heq]; exact ⟨Nat.lt_succ_self m, hpm⟩
        · rw [List.length_append, List.length_singleton, sumR, hsum, CommRing.add_assoc]
          congr 1
          have hc : sumR ((filterRange m (fun s => ¬ P s)).length + 1)
              (fun t => f ((filterRange m (fun s => ¬ P s) ++ [m]).getD t 0)) =
              sumR (filterRange m (fun s => ¬ P s)).length (fun t => f ((filterRange m (fun s => ¬ P s)).getD t 0)) + f m := by
            simp only [sumR]
            congr 1
            · exact sumR_congr (fun t ht => by rw [hget_append_end, ite_t ht])
            · rw [hget_append_end, ite_f (Nat.lt_irrefl _), ite_t rfl]
          rw [hc]
  exact haux q

/-- **Strassen's Commutator Equation (`strassen_commutator_bound`, Theorem 6.1):**
    Over **ANY `SimpleField K` (including `F_2`!)**, if `A0, A1, A2 ∈ K^{n × n}` lie in a `q`-term
    rank-1 span `A_t = ∑_{s < q} c_t s * (P · s) ⊗ (Q s ·)` with `A0` invertible and
    `A1 · A0⁻¹ · A2 - A2 · A0⁻¹ · A1` invertible, then **`n ≤ q` AND `n ≤ 2 * (q - n)`**
    (i.e. `3 * n ≤ 2 * q`)! -/
theorem strassen_commutator_bound {K : Type} [SimpleField K] (n q : Nat)
    (c0 c1 c2 : Nat → K) (P Q A0 A1 A2 A0inv Cinv : Nat → Nat → K)
    (hA0 : ∀ i j, i < n → j < n → A0 i j = sumR q (fun s => c0 s * P i s * Q s j))
    (hA1 : ∀ i j, i < n → j < n → A1 i j = sumR q (fun s => c1 s * P i s * Q s j))
    (hA2 : ∀ i j, i < n → j < n → A2 i j = sumR q (fun s => c2 s * P i s * Q s j))
    (hInv0 : IsMatInv n A0 A0inv)
    (hInvC : IsMatInv n (matSub (matMulF n (matMulF n A1 A0inv) A2)
                                (matMulF n (matMulF n A2 A0inv) A1)) Cinv) :
    n ≤ q ∧ n ≤ 2 * (q - n) := by
  -- 1. Partition `{0..q-1}` into `S0` (`c0 s ≠ 0`, size `q0`) and `S1` (`c0 s = 0`, size `q1`)
  let L0 := filterRange q (fun s => c0 s ≠ 0)
  let L1 := filterRange q (fun s => ¬ (c0 s ≠ 0))
  have hpart0 := sumR_partition q (fun s => c0 s ≠ 0) (fun s => c0 s * P 0 s * Q s 0)
  have hqlen : L0.length + L1.length = q := hpart0.1
  have hL0_nz : ∀ t, t < L0.length → c0 (L0.getD t 0) ≠ 0 := fun t ht => (hpart0.2.1 t ht).2
  have hL1_z : ∀ t, t < L1.length → c0 (L1.getD t 0) = 0 := fun t ht =>
    Classical.byContradiction fun hne => (hpart0.2.2.1 t ht).2 hne
  let q0 := L0.length
  let q1 := L1.length
  -- Unpermuted rescaled factors on `S0` and `S1`
  let P0raw (i t : Nat) : K := c0 (L0.getD t 0) * P i (L0.getD t 0)
  let Q0raw (t j : Nat) : K := Q (L0.getD t 0) j
  let l1raw (t : Nat) : K := c1 (L0.getD t 0) * SimpleField.inv (c0 (L0.getD t 0))
  let l2raw (t : Nat) : K := c2 (L0.getD t 0) * SimpleField.inv (c0 (L0.getD t 0))
  let P1 (i t : Nat) : K := P i (L1.getD t 0)
  let Q1 (t j : Nat) : K := Q (L1.getD t 0) j
  let d1 (t : Nat) : K := c1 (L1.getD t 0)
  let d2 (t : Nat) : K := c2 (L1.getD t 0)
  have hA0raw : MatEq n n A0 (matMulF q0 P0raw Q0raw) := by
    intro i j hi hj
    rw [hA0 i j hi hj, (sumR_partition q (fun s => c0 s ≠ 0) (fun s => c0 s * P i s * Q s j)).2.2.2]
    have hz1 : sumR q1 (fun t => c0 (L1.getD t 0) * P i (L1.getD t 0) * Q (L1.getD t 0) j) = 0 := by
      rw [sumR_congr (fun t ht => by rw [hL1_z t ht, zero_mul, zero_mul]), sumR_zero_fn]
    rw [hz1, add_zero]; rfl
  -- 2. Apply `col_basis_of_right_inv` to `P0raw * (Q0raw * A0inv) = I_n`!
  have hP0R : MatEq n n (matMulF q0 P0raw (matMulF n Q0raw A0inv)) matIdF := by
    intro i j hi hj
    rw [← matMulF_assoc q0 n P0raw Q0raw A0inv i j,
        matMulF_congr (fun t ht => (hA0raw i t hi ht).symm) (fun _ _ => rfl)]
    exact hInv0.1 i j hi hj
  obtain ⟨hnq0, π, πInv, PI_inv, hbij, hPI⟩ := col_basis_of_right_inv n q0 P0raw (matMulF n Q0raw A0inv) hP0R
  -- Permuted `S0` factors so columns `0..n-1` of `P0` form `P_I` with inverse `PI_inv`!
  let P0 (i t : Nat) : K := P0raw i (π t)
  let Q0 (t j : Nat) : K := Q0raw (π t) j
  let l1 (t : Nat) : K := l1raw (π t)
  let l2 (t : Nat) : K := l2raw (π t)
  have hsum_perm : ∀ (f : Nat → K), sumR q0 (fun t => f (π t)) = sumR q0 f := by
    intro f
    -- Bijection sum invariance on `{0..q0-1}`
    have hgen : ∀ (L : List Nat), ListNodup L → (∀ x, x ∈ L → x < q0) →
        ∀ (g : Nat → K), (∀ t, t < q0 → t ∉ L → g t = 0) →
        sumR q0 (fun t => g (π t)) = sumR q0 g := by
      intro L
      induction L with
      | nil =>
        intro _ _ g hg
        rw [sumR_congr (fun t ht => hg (π t) (hbij t ht).1 (by simp)), sumR_zero_fn,
            sumR_congr (fun t ht => hg t ht (by simp)), sumR_zero_fn]
      | cons x xs ihL =>
        intro ⟨hnotmem, hnd⟩ hbd g hg
        let gx : Nat → K := fun t => if t = x then g x else 0
        let gr : Nat → K := fun t => if t = x then 0 else g t
        have hd : ∀ t, g t = gx t + gr t := fun t => by dsimp only [gx, gr]; by_cases h : t = x <;> simp [h, add_zero, CommRing.zero_add]
        have hL1' : sumR q0 (fun t => g (π t)) = sumR q0 (fun t => gx (π t)) + sumR q0 (fun t => gr (π t)) := by
          rw [← sumR_add]; exact sumR_congr (fun t _ => hd (π t))
        have hR1' : sumR q0 g = sumR q0 gx + sumR q0 gr := by
          rw [← sumR_add]; exact sumR_congr (fun t _ => hd t)
        have hxlt : x < q0 := hbd x (List.mem_cons_self ..)
        have hgx1 : sumR q0 (fun t => gx (π t)) = g x := by
          have hc : sumR q0 (fun t => gx (π t)) = sumR q0 (fun t => if t = πInv x then g x else 0) := by
            apply sumR_congr; intro t ht; dsimp only [gx]
            by_cases h1 : π t = x
            · rw [ite_t h1, ite_t (by rw [← h1, (hbij t ht).2.2.2])]
            · rw [ite_f h1, ite_f (fun e => h1 (by rw [e, (hbij x hxlt).2.2.1]))]
          rw [hc, sumR_single q0 (πInv x) (g x) (hbij x hxlt).2.1]
        have hgr := ihL hnd (fun y hy => hbd y (List.mem_cons_of_mem x hy)) gr (fun t ht htn => by
          dsimp only [gr]; by_cases htx : t = x
          · rw [ite_t htx]
          · rw [ite_f htx]; exact hg t ht (fun hm => by cases hm with | head => exact htx rfl | tail _ h' => exact htn h'))
        rw [hL1', hR1', hgx1, sumR_single q0 x (g x) hxlt, hgr]
    have hndR : ∀ m : Nat, ListNodup (List.range m) := by
      intro m; induction m with
      | zero => trivial
      | succ m' ihm =>
        rw [List.range_succ]
        have happ : ∀ (l : List Nat) (a : Nat), ListNodup l → (∀ y, y ∈ l → y ≠ a) → ListNodup (l ++ [a]) := by
          intro l; induction l with
          | nil => intro _ _ _; simp [ListNodup]
          | cons u us ihu =>
            intro a ⟨h1, h2⟩ h3
            refine ⟨fun y hy => ?_, ihu a h2 (fun y hy => h3 y (List.mem_cons_of_mem u hy))⟩
            cases List.mem_append.mp hy with
            | inl hm => exact h1 y hm
            | inr hm =>
              have hya : y = a := by simpa using hm
              subst hya; exact Ne.symm (h3 u (List.mem_cons_self ..))
        exact happ _ m' ihm (fun y hy => by have := List.mem_range.mp hy; omega)
    exact hgen (List.range q0) (hndR q0) (fun x hx => List.mem_range.mp hx) f
      (fun t ht hnot => absurd (List.mem_range.mpr ht) hnot)
  have hA0_eq : MatEq n n A0 (matMulF q0 P0 Q0) := by
    intro i j hi hj
    rw [hA0raw i j hi hj]
    exact (hsum_perm (fun t => P0raw i t * Q0raw t j)).symm
  let A1_0 (i j : Nat) : K := sumR q0 (fun t => P0 i t * (l1 t * Q0 t j))
  let A2_0 (i j : Nat) : K := sumR q0 (fun t => P0 i t * (l2 t * Q0 t j))
  let A1_1 (i j : Nat) : K := sumR q1 (fun t => P1 i t * (d1 t * Q1 t j))
  let A2_1 (i j : Nat) : K := sumR q1 (fun t => P1 i t * (d2 t * Q1 t j))
  have hA_split : ∀ (c : Nat → K) (l : Nat → K) (d : Nat → K) (A : Nat → Nat → K),
      (∀ t, t < q0 → l t = c (L0.getD (π t) 0) * SimpleField.inv (c0 (L0.getD (π t) 0))) →
      (∀ t, t < q1 → d t = c (L1.getD t 0)) →
      (∀ i j, i < n → j < n → A i j = sumR q (fun s => c s * P i s * Q s j)) →
      ∀ i j, i < n → j < n →
        A i j = sumR q0 (fun t => P0 i t * (l t * Q0 t j)) + sumR q1 (fun t => P1 i t * (d t * Q1 t j)) := by
    intro c l d A hl hd hA i j hi hj
    rw [hA i j hi hj, (sumR_partition q (fun s => c0 s ≠ 0) (fun s => c s * P i s * Q s j)).2.2.2]
    congr 1
    · rw [← hsum_perm (fun t => c (L0.getD t 0) * P i (L0.getD t 0) * Q (L0.getD t 0) j)]
      apply sumR_congr; intro t ht
      rw [hl t ht]
      dsimp only [P0, Q0, P0raw, Q0raw]
      have hnz := hL0_nz (π t) (hbij t ht).1
      let a := c0 (L0.getD (π t) 0)
      let ia := SimpleField.inv a
      let cc := c (L0.getD (π t) 0)
      let pp := P i (L0.getD (π t) 0)
      let qq := Q (L0.getD (π t) 0) j
      change cc * pp * qq = (a * pp) * ((cc * ia) * qq)
      symm
      calc (a * pp) * ((cc * ia) * qq)
          = (a * ia) * (cc * pp * qq) := by
            rw [← CommRing.mul_assoc (a * pp), CommRing.mul_assoc a pp,
                CommRing.mul_comm pp (cc * ia), ← CommRing.mul_assoc a (cc * ia),
                CommRing.mul_comm cc ia, ← CommRing.mul_assoc a ia,
                CommRing.mul_assoc (a * ia) cc, CommRing.mul_assoc (a * ia)]
        _ = 1 * (cc * pp * qq) := by rw [SimpleField.mul_inv_cancel a hnz]
        _ = cc * pp * qq := CommRing.one_mul _
    · apply sumR_congr; intro t ht
      rw [hd t ht]; dsimp only [P1, Q1]
      rw [← CommRing.mul_assoc, CommRing.mul_comm (P i _) (c _)]
  have hA1_eq : MatEq n n A1 (matAdd A1_0 A1_1) := hA_split c1 l1 d1 A1 (fun _ _ => rfl) (fun _ _ => rfl) hA1
  have hA2_eq : MatEq n n A2 (matAdd A2_0 A2_1) := hA_split c2 l2 d2 A2 (fun _ _ => rfl) (fun _ _ => rfl) hA2
  -- 3. Explicit rank-`k0 = q0 - n` factorization of `I_{q0} - E` where `E = Q0 * A0inv * P0`!
  let k0 := q0 - n
  let E : Nat → Nat → K := matMulF n (matMulF n Q0 A0inv) P0
  have hP0E : MatEq n q0 (matMulF q0 P0 E) P0 := by
    intro i s hi _
    dsimp only [E]
    have h1 : ∀ t, t < n → matMulF q0 P0 (matMulF n Q0 A0inv) i t = matIdF i t := by
      intro t ht
      rw [← matMulF_assoc q0 n P0 Q0 A0inv,
          matMulF_congr (fun r hr => (hA0_eq i r hi hr).symm) (fun _ _ => rfl)]
      exact hInv0.1 i t hi ht
    rw [← matMulF_assoc q0 n P0 (matMulF n Q0 A0inv) P0,
        matMulF_congr h1 (fun _ _ => rfl),
        matMulF_id_left n P0 hi]
  let UE (t u : Nat) : K :=
    if t < n then -(matMulF n PI_inv (fun i u' => P0 i (n + u')) t u) else matIdF (t - n) u
  let VE (u s : Nat) : K := matIdF (n + u) s - E (n + u) s
  have hIE_fact : MatEq q0 q0 (matSub matIdF E) (matMulF k0 UE VE) := by
    intro t s ht _
    by_cases htn : t < n
    · -- Use `P0 * (I - E) = 0`, split into `0..n-1` and `n..q0-1`, multiply on left by `PI_inv`!
      have hzero : ∀ i, i < n →
          sumR n (fun r => P0 i r * (matIdF r s - E r s)) +
          sumR k0 (fun u => P0 i (n + u) * VE u s) = 0 := by
        intro i hi
        have hsplit : q0 = n + k0 := by omega
        have hsum : sumR q0 (fun r => P0 i r * (matIdF r s - E r s)) = 0 := by
          have h1 : sumR q0 (fun r => P0 i r * (matIdF r s - E r s)) =
              matMulF q0 P0 matIdF i s - matMulF q0 P0 E i s := by
            unfold matMulF; rw [← sumR_sub]
            exact sumR_congr (fun r _ => mul_sub_r ..)
          by_cases hsq : s < q0
          · rw [h1, matMulF_id_right q0 P0 hsq, hP0E i s hi hsq, sub_self]
          · exfalso; omega
        rw [hsplit, sumR_split n k0] at hsum
        exact hsum
      have hmul : sumR n (fun i => PI_inv t i *
          (sumR n (fun r => P0 i r * (matIdF r s - E r s)) + sumR k0 (fun u => P0 i (n + u) * VE u s))) = 0 := by
        rw [sumR_congr (fun i hi => by rw [hzero i hi, mul_zero]), sumR_zero_fn]
      have hL1 : sumR n (fun i => PI_inv t i * sumR n (fun r => P0 i r * (matIdF r s - E r s))) =
          matIdF t s - E t s := by
        calc sumR n (fun i => PI_inv t i * sumR n (fun r => P0 i r * (matIdF r s - E r s)))
            = sumR n (fun i => sumR n (fun r => (PI_inv t i * P0 i r) * (matIdF r s - E r s))) :=
              sumR_congr (fun i _ => by rw [sumR_mul_left]; exact sumR_congr (fun r _ => (CommRing.mul_assoc ..).symm))
          _ = sumR n (fun r => sumR n (fun i => (PI_inv t i * P0 i r) * (matIdF r s - E r s))) := sumR_swap n n _
          _ = sumR n (fun r => matMulF n PI_inv P0 t r * (matIdF r s - E r s)) :=
              sumR_congr (fun r _ => (sumR_mul_right n _ _).symm)
          _ = sumR n (fun r => matIdF t r * (matIdF r s - E r s)) :=
              sumR_congr (fun r hr => by rw [hPI.2 t r htn hr])
          _ = matMulF n matIdF (fun r _ => matIdF r s - E r s) t s := rfl
          _ = matIdF t s - E t s := matMulF_id_left n _ htn
      have hL2 : sumR n (fun i => PI_inv t i * sumR k0 (fun u => P0 i (n + u) * VE u s)) =
          -(matMulF k0 UE VE t s) := by
        unfold matMulF
        rw [← sumR_neg]
        calc sumR n (fun i => PI_inv t i * sumR k0 (fun u => P0 i (n + u) * VE u s))
            = sumR n (fun i => sumR k0 (fun u => (PI_inv t i * P0 i (n + u)) * VE u s)) :=
              sumR_congr (fun i _ => by rw [sumR_mul_left]; exact sumR_congr (fun u _ => (CommRing.mul_assoc ..).symm))
          _ = sumR k0 (fun u => sumR n (fun i => (PI_inv t i * P0 i (n + u)) * VE u s)) := sumR_swap n k0 _
          _ = sumR k0 (fun u => matMulF n PI_inv (fun i u' => P0 i (n + u')) t u * VE u s) :=
              sumR_congr (fun u _ => (sumR_mul_right n _ _).symm)
          _ = sumR k0 (fun u => -(UE t u * VE u s)) := by
              apply sumR_congr; intro u _
              dsimp only [UE]; rw [ite_t htn, neg_mul, neg_neg]
      have hsp : sumR n (fun i => PI_inv t i *
          (sumR n (fun r => P0 i r * (matIdF r s - E r s)) + sumR k0 (fun u => P0 i (n + u) * VE u s))) =
          (matIdF t s - E t s) + (-(matMulF k0 UE VE t s)) := by
        rw [← hL1, ← hL2, ← sumR_add]
        exact sumR_congr (fun i _ => CommRing.left_distrib ..)
      rw [hsp] at hmul
      exact eq_of_sub_eq_zero (by rw [CommRing.sub_eq]; exact hmul)
    · -- `t ≥ n`: `UE t u = matIdF (t - n) u`, directly picks out `VE (t - n) s = matIdF t s - E t s`!
      have hsub_lt : t - n < k0 := by omega
      have hadd_eq : n + (t - n) = t := by omega
      unfold matMulF matSub
      have hc : sumR k0 (fun u => UE t u * VE u s) = sumR k0 (fun u => matIdF (t - n) u * VE u s) :=
        sumR_congr (fun u _ => by dsimp only [UE]; rw [ite_f htn])
      rw [hc, show sumR k0 (fun u => matIdF (t - n) u * VE u s) = matMulF k0 matIdF VE (t - n) s from rfl,
          matMulF_id_left k0 VE hsub_lt]
      dsimp only [VE]; rw [hadd_eq]
  -- 4. Factor `A1 A0inv A2 - A2 A0inv A1` through inner dimension `2 * k0 + 2 * q1 = 2 * (q - n)`!
  -- Part A (pure-0 commutator): `A1_0 A0inv A2_0 - A2_0 A0inv A1_0 = L_a * R_a + L_b * R_b` (each `k0` cols)
  let La (i u : Nat) : K := sumR q0 (fun t => P0 i t * (l1 t * (-(UE t u))))
  let Ra (u j : Nat) : K := sumR q0 (fun s => VE u s * (l2 s * Q0 s j))
  let Lb (i u : Nat) : K := sumR q0 (fun t => P0 i t * (l2 t * UE t u))
  let Rb (u j : Nat) : K := sumR q0 (fun s => VE u s * (l1 s * Q0 s j))
  have hpure0 : MatEq n n
      (matSub (matMulF n (matMulF n A1_0 A0inv) A2_0) (matMulF n (matMulF n A2_0 A0inv) A1_0))
      (matAdd (matMulF k0 La Ra) (matMulF k0 Lb Rb)) := by
    intro i j _ _
    have hquad : ∀ (f g : Nat → K),
        matMulF n (matMulF n (fun a b => sumR q0 (fun t => P0 a t * (f t * Q0 t b))) A0inv)
                  (fun a b => sumR q0 (fun s => P0 a s * (g s * Q0 s b))) i j =
        sumR q0 (fun t => sumR q0 (fun s => (P0 i t * f t) * E t s * (g s * Q0 s j))) := by
      intro f g
      have h1 : ∀ a, matMulF n (fun r c => sumR q0 (fun t => P0 r t * (f t * Q0 t c))) A0inv i a =
          sumR q0 (fun t => (P0 i t * f t) * matMulF n Q0 A0inv t a) := by
        intro a
        unfold matMulF
        calc sumR n (fun k => sumR q0 (fun t => P0 i t * (f t * Q0 t k)) * A0inv k a)
            = sumR n (fun k => sumR q0 (fun t => P0 i t * (f t * Q0 t k) * A0inv k a)) :=
              sumR_congr (fun k _ => sumR_mul_right q0 _ _)
          _ = sumR q0 (fun t => sumR n (fun k => P0 i t * (f t * Q0 t k) * A0inv k a)) := sumR_swap n q0 _
          _ = sumR q0 (fun t => (P0 i t * f t) * sumR n (fun k => Q0 t k * A0inv k a)) := by
              apply sumR_congr; intro t _
              rw [sumR_mul_left]; apply sumR_congr; intro k _
              simp only [CommRing.mul_assoc]
      unfold matMulF
      calc sumR n (fun a => matMulF n (fun r c => sumR q0 (fun t => P0 r t * (f t * Q0 t c))) A0inv i a *
                            sumR q0 (fun s => P0 a s * (g s * Q0 s j)))
          = sumR n (fun a => sumR q0 (fun t => (P0 i t * f t) * matMulF n Q0 A0inv t a) *
                             sumR q0 (fun s => P0 a s * (g s * Q0 s j))) :=
            sumR_congr (fun a _ => by rw [h1 a])
        _ = sumR n (fun a => sumR q0 (fun t => (P0 i t * f t) * matMulF n Q0 A0inv t a *
                             sumR q0 (fun s => P0 a s * (g s * Q0 s j)))) :=
            sumR_congr (fun a _ => sumR_mul_right q0 _ _)
        _ = sumR q0 (fun t => sumR n (fun a => (P0 i t * f t) * matMulF n Q0 A0inv t a *
                             sumR q0 (fun s => P0 a s * (g s * Q0 s j)))) := sumR_swap n q0 _
        _ = sumR q0 (fun t => sumR n (fun a => sumR q0 (fun s =>
              (P0 i t * f t) * matMulF n Q0 A0inv t a * (P0 a s * (g s * Q0 s j))))) :=
            sumR_congr (fun t _ => sumR_congr (fun a _ => sumR_mul_left q0 _ _))
        _ = sumR q0 (fun t => sumR q0 (fun s => sumR n (fun a =>
              (P0 i t * f t) * matMulF n Q0 A0inv t a * (P0 a s * (g s * Q0 s j))))) :=
            sumR_congr (fun t _ => sumR_swap n q0 _)
        _ = sumR q0 (fun t => sumR q0 (fun s => (P0 i t * f t) * E t s * (g s * Q0 s j))) := by
            apply sumR_congr; intro t _; apply sumR_congr; intro s _
            dsimp only [E, matMulF]
            rw [sumR_mul_left, sumR_mul_right]
            apply sumR_congr; intro a _
            simp only [CommRing.mul_assoc]
    have hdiag_cancel :
        sumR q0 (fun t => sumR q0 (fun s => (P0 i t * l1 t) * matIdF t s * (l2 s * Q0 s j))) =
        sumR q0 (fun t => sumR q0 (fun s => (P0 i t * l2 t) * matIdF t s * (l1 s * Q0 s j))) := by
      have heval : ∀ (f g : Nat → K),
          sumR q0 (fun t => sumR q0 (fun s => (P0 i t * f t) * matIdF t s * (g s * Q0 s j))) =
          sumR q0 (fun t => P0 i t * (f t * g t) * Q0 t j) := by
        intro f g
        apply sumR_congr; intro t ht
        have hs : sumR q0 (fun s => (P0 i t * f t) * matIdF t s * (g s * Q0 s j)) =
            sumR q0 (fun s => if s = t then P0 i t * (f t * g t) * Q0 t j else 0) := by
          apply sumR_congr; intro s _
          unfold matIdF
          by_cases hst : s = t
          · subst hst; rw [ite_t rfl, ite_t rfl, mul_one]; simp only [CommRing.mul_assoc]
          · have hts : t ≠ s := Ne.symm hst
            rw [ite_f hst, ite_f hts, mul_zero, zero_mul]
        rw [hs, sumR_single q0 t _ ht]
      rw [heval l1 l2, heval l2 l1]
      exact sumR_congr (fun t _ => by rw [CommRing.mul_comm (l1 t) (l2 t)])
    have hfac_eval : ∀ (f g : Nat → K),
        sumR q0 (fun t => sumR q0 (fun s => (P0 i t * f t) * (E t s - matIdF t s) * (g s * Q0 s j))) =
        matMulF k0 (fun a u => sumR q0 (fun t => P0 a t * (f t * (-(UE t u)))))
                   (fun u b => sumR q0 (fun s => VE u s * (g s * Q0 s b))) i j := by
      intro f g
      have hEmI : ∀ t s, t < q0 → s < q0 → E t s - matIdF t s = sumR k0 (fun u => (-(UE t u)) * VE u s) := by
        intro t s ht hs
        have h := hIE_fact t s ht hs
        unfold matSub matMulF at h
        have hneg : E t s - matIdF t s = -(matIdF t s - E t s) := by
          rw [CommRing.sub_eq, CommRing.sub_eq, neg_add_distrib, neg_neg, CommRing.add_comm]
        rw [hneg, h, ← sumR_neg]
        exact sumR_congr (fun u _ => (neg_mul (UE t u) (VE u s)).symm)
      calc sumR q0 (fun t => sumR q0 (fun s => (P0 i t * f t) * (E t s - matIdF t s) * (g s * Q0 s j)))
          = sumR q0 (fun t => sumR q0 (fun s =>
              sumR k0 (fun u => (P0 i t * (f t * (-(UE t u)))) * (VE u s * (g s * Q0 s j))))) := by
            apply sumR_congr; intro t ht; apply sumR_congr; intro s hs
            rw [hEmI t s ht hs, sumR_mul_left, sumR_mul_right]
            apply sumR_congr; intro u _; simp only [CommRing.mul_assoc]
        _ = sumR q0 (fun t => sumR k0 (fun u => sumR q0 (fun s =>
              (P0 i t * (f t * (-(UE t u)))) * (VE u s * (g s * Q0 s j))))) :=
            sumR_congr (fun t _ => sumR_swap q0 k0 _)
        _ = sumR k0 (fun u => sumR q0 (fun t => sumR q0 (fun s =>
              (P0 i t * (f t * (-(UE t u)))) * (VE u s * (g s * Q0 s j))))) := sumR_swap q0 k0 _
        _ = sumR k0 (fun u => sumR q0 (fun t => P0 i t * (f t * (-(UE t u)))) *
                              sumR q0 (fun s => VE u s * (g s * Q0 s j))) := by
            apply sumR_congr; intro u _
            rw [sumR_mul_right]
            apply sumR_congr; intro t _
            rw [sumR_mul_left]
    unfold matSub matAdd
    rw [hquad l1 l2, hquad l2 l1]
    have hdiff :
        sumR q0 (fun t => sumR q0 (fun s => (P0 i t * l1 t) * E t s * (l2 s * Q0 s j))) -
        sumR q0 (fun t => sumR q0 (fun s => (P0 i t * l2 t) * E t s * (l1 s * Q0 s j))) =
        sumR q0 (fun t => sumR q0 (fun s => (P0 i t * l1 t) * (E t s - matIdF t s) * (l2 s * Q0 s j))) -
        sumR q0 (fun t => sumR q0 (fun s => (P0 i t * l2 t) * (E t s - matIdF t s) * (l1 s * Q0 s j))) := by
      have hsub_eq : ∀ (f g : Nat → K),
          sumR q0 (fun t => sumR q0 (fun s => (P0 i t * f t) * (E t s - matIdF t s) * (g s * Q0 s j))) =
          sumR q0 (fun t => sumR q0 (fun s => (P0 i t * f t) * E t s * (g s * Q0 s j))) -
          sumR q0 (fun t => sumR q0 (fun s => (P0 i t * f t) * matIdF t s * (g s * Q0 s j))) := by
        intro f g
        rw [← sumR_sub]
        apply sumR_congr; intro t _; rw [← sumR_sub]
        apply sumR_congr; intro s _
        rw [mul_sub_r, sub_mul_r]
      rw [hsub_eq l1 l2, hsub_eq l2 l1, hdiag_cancel]
      let X := sumR q0 (fun t => sumR q0 (fun s => (P0 i t * l1 t) * E t s * (l2 s * Q0 s j)))
      let Y := sumR q0 (fun t => sumR q0 (fun s => (P0 i t * l2 t) * E t s * (l1 s * Q0 s j)))
      let Z := sumR q0 (fun t => sumR q0 (fun s => (P0 i t * l2 t) * matIdF t s * (l1 s * Q0 s j)))
      change X - Y = (X - Z) - (Y - Z)
      rw [CommRing.sub_eq, CommRing.sub_eq, CommRing.sub_eq, CommRing.sub_eq,
          neg_add_distrib, neg_neg, CommRing.add_assoc X (-Z),
          ← CommRing.add_assoc (-Z) (-Y) Z, CommRing.add_comm (-Z) (-Y),
          CommRing.add_assoc (-Y) (-Z) Z, neg_add, add_zero]
    rw [hdiff, hfac_eval l1 l2, hfac_eval l2 l1]
    have hneg_b : -(matMulF k0 (fun a u => sumR q0 (fun t => P0 a t * (l2 t * (-(UE t u))))) Rb i j) =
        matMulF k0 Lb Rb i j := by
      unfold matMulF
      rw [← sumR_neg]
      apply sumR_congr; intro u _
      rw [← neg_mul, ← sumR_neg]
      congr 1
      apply sumR_congr; intro t _
      rw [mul_neg, mul_neg, neg_neg]
    rw [CommRing.sub_eq, hneg_b]
  -- Part B (cross & pure-1 commutator): `Lc * Rc + Ld * Rd` (each `q1` cols)
  let Lc (i t : Nat) : K := P1 i t
  let Rc (t j : Nat) : K :=
    d1 t * matMulF n (matMulF n Q1 A0inv) A2 t j - d2 t * matMulF n (matMulF n Q1 A0inv) A1 t j
  let Ld (i t : Nat) : K :=
    matMulF n (matMulF n A1_0 A0inv) P1 i t * d2 t - matMulF n (matMulF n A2_0 A0inv) P1 i t * d1 t
  let Rd (t j : Nat) : K := Q1 t j
  have hfull : MatEq n n
      (matSub (matMulF n (matMulF n A1 A0inv) A2) (matMulF n (matMulF n A2 A0inv) A1))
      (matAdd (matAdd (matMulF k0 La Ra) (matMulF k0 Lb Rb))
              (matAdd (matMulF q1 Lc Rc) (matMulF q1 Ld Rd))) := by
    intro i j hi hj
    have hmul_A11 : ∀ (B : Nat → Nat → K) (d : Nat → K),
        matMulF n (matMulF n (fun r c => sumR q1 (fun t => P1 r t * (d t * Q1 t c))) A0inv) B i j =
        sumR q1 (fun t => P1 i t * (d t * matMulF n (matMulF n Q1 A0inv) B t j)) := by
      intro B d
      have h1 : ∀ a, matMulF n (fun r c => sumR q1 (fun t => P1 r t * (d t * Q1 t c))) A0inv i a =
          sumR q1 (fun t => P1 i t * (d t * matMulF n Q1 A0inv t a)) := by
        intro a; unfold matMulF
        calc sumR n (fun k => sumR q1 (fun t => P1 i t * (d t * Q1 t k)) * A0inv k a)
            = sumR n (fun k => sumR q1 (fun t => P1 i t * (d t * Q1 t k) * A0inv k a)) :=
              sumR_congr (fun k _ => sumR_mul_right q1 _ _)
          _ = sumR q1 (fun t => sumR n (fun k => P1 i t * (d t * Q1 t k) * A0inv k a)) := sumR_swap n q1 _
          _ = sumR q1 (fun t => P1 i t * (d t * sumR n (fun k => Q1 t k * A0inv k a))) := by
              apply sumR_congr; intro t _; rw [sumR_mul_left, sumR_mul_left]
              exact sumR_congr (fun k _ => by simp only [CommRing.mul_assoc])
      unfold matMulF
      calc sumR n (fun a => matMulF n (fun r c => sumR q1 (fun t => P1 r t * (d t * Q1 t c))) A0inv i a * B a j)
          = sumR n (fun a => sumR q1 (fun t => P1 i t * (d t * matMulF n Q1 A0inv t a)) * B a j) :=
            sumR_congr (fun a _ => by rw [h1 a])
        _ = sumR n (fun a => sumR q1 (fun t => P1 i t * (d t * matMulF n Q1 A0inv t a) * B a j)) :=
            sumR_congr (fun a _ => sumR_mul_right q1 _ _)
        _ = sumR q1 (fun t => sumR n (fun a => P1 i t * (d t * matMulF n Q1 A0inv t a) * B a j)) := sumR_swap n q1 _
        _ = sumR q1 (fun t => P1 i t * (d t * sumR n (fun a => matMulF n Q1 A0inv t a * B a j))) := by
            apply sumR_congr; intro t _; rw [sumR_mul_left, sumR_mul_left]
            exact sumR_congr (fun a _ => by simp only [CommRing.mul_assoc])
    have hmul_B1 : ∀ (A : Nat → Nat → K) (d : Nat → K),
        matMulF n (matMulF n A A0inv) (fun r c => sumR q1 (fun t => P1 r t * (d t * Q1 t c))) i j =
        sumR q1 (fun t => (matMulF n (matMulF n A A0inv) P1 i t * d t) * Q1 t j) := by
      intro A d; unfold matMulF
      calc sumR n (fun a => matMulF n A A0inv i a * sumR q1 (fun t => P1 a t * (d t * Q1 t j)))
          = sumR n (fun a => sumR q1 (fun t => matMulF n A A0inv i a * (P1 a t * (d t * Q1 t j)))) :=
            sumR_congr (fun a _ => sumR_mul_left q1 _ _)
        _ = sumR q1 (fun t => sumR n (fun a => matMulF n A A0inv i a * (P1 a t * (d t * Q1 t j)))) := sumR_swap n q1 _
        _ = sumR q1 (fun t => (sumR n (fun a => matMulF n A A0inv i a * P1 a t) * d t) * Q1 t j) := by
            apply sumR_congr; intro t _; rw [sumR_mul_right, sumR_mul_right]
            exact sumR_congr (fun a _ => by simp only [CommRing.mul_assoc])
    have hLcRc : matMulF q1 Lc Rc i j =
        matMulF n (matMulF n A1_1 A0inv) A2 i j - matMulF n (matMulF n A2_1 A0inv) A1 i j := by
      rw [hmul_A11 A2 d1, hmul_A11 A1 d2]
      unfold matMulF Lc Rc
      rw [← sumR_sub]
      exact sumR_congr (fun t _ => mul_sub_r ..)
    have hLdRd : matMulF q1 Ld Rd i j =
        matMulF n (matMulF n A1_0 A0inv) A2_1 i j - matMulF n (matMulF n A2_0 A0inv) A1_1 i j := by
      rw [hmul_B1 A1_0 d2, hmul_B1 A2_0 d1]
      unfold matMulF Ld Rd
      rw [← sumR_sub]
      exact sumR_congr (fun t _ => sub_mul_r ..)
    have hT1 : matMulF n (matMulF n A1 A0inv) A2 i j =
        matMulF n (matMulF n A1_0 A0inv) A2_0 i j +
        matMulF n (matMulF n A1_0 A0inv) A2_1 i j +
        matMulF n (matMulF n A1_1 A0inv) A2 i j := by
      have h1 : matMulF n (matMulF n A1 A0inv) A2 i j =
          matMulF n (matAdd (matMulF n A1_0 A0inv) (matMulF n A1_1 A0inv)) A2 i j :=
        matMulF_congr (fun a ha => by
          rw [matMulF_congr (fun b hb => hA1_eq i b hi hb) (fun _ _ => rfl), matMulF_add_left]; rfl) (fun _ _ => rfl)
      rw [h1, matMulF_add_left]
      congr 1
      rw [matMulF_congr (fun _ _ => rfl) (fun b hb => hA2_eq b j hb hj), matMulF_add_right]
    have hT2 : matMulF n (matMulF n A2 A0inv) A1 i j =
        matMulF n (matMulF n A2_0 A0inv) A1_0 i j +
        matMulF n (matMulF n A2_0 A0inv) A1_1 i j +
        matMulF n (matMulF n A2_1 A0inv) A1 i j := by
      have h2 : matMulF n (matMulF n A2 A0inv) A1 i j =
          matMulF n (matAdd (matMulF n A2_0 A0inv) (matMulF n A2_1 A0inv)) A1 i j :=
        matMulF_congr (fun a ha => by
          rw [matMulF_congr (fun b hb => hA2_eq i b hi hb) (fun _ _ => rfl), matMulF_add_left]; rfl) (fun _ _ => rfl)
      rw [h2, matMulF_add_left]
      congr 1
      rw [matMulF_congr (fun _ _ => rfl) (fun b hb => hA1_eq b j hb hj), matMulF_add_right]
    change matMulF n (matMulF n A1 A0inv) A2 i j - matMulF n (matMulF n A2 A0inv) A1 i j =
      matAdd (matMulF k0 La Ra) (matMulF k0 Lb Rb) i j + (matMulF q1 Lc Rc i j + matMulF q1 Ld Rd i j)
    rw [hT1, hT2, ← hpure0 i j hi hj, hLcRc, hLdRd]
    unfold matSub
    -- Pure CommRing rearrangement `(a+b+c) - (d+e+f) = (a-d) + ((c-f) + (b-e))`
    let a := matMulF n (matMulF n A1_0 A0inv) A2_0 i j
    let b := matMulF n (matMulF n A1_0 A0inv) A2_1 i j
    let c := matMulF n (matMulF n A1_1 A0inv) A2 i j
    let d := matMulF n (matMulF n A2_0 A0inv) A1_0 i j
    let e := matMulF n (matMulF n A2_0 A0inv) A1_1 i j
    let f := matMulF n (matMulF n A2_1 A0inv) A1 i j
    change (a + b + c) - (d + e + f) = (a - d) + ((c - f) + (b - e))
    simp only [CommRing.sub_eq, neg_add_distrib]
    -- Both sides equal `a + (-d) + (b + (-e)) + (c + (-f))`
    have hre : ∀ u1 u2 u3 v1 v2 v3 : K,
        (u1 + u2 + u3) + (v1 + v2 + v3) = (u1 + v1) + ((u3 + v3) + (u2 + v2)) := by
      intro u1 u2 u3 v1 v2 v3
      calc (u1 + u2 + u3) + (v1 + v2 + v3)
          = u1 + (u2 + (u3 + (v1 + (v2 + v3)))) := by simp only [CommRing.add_assoc]
        _ = u1 + (v1 + (u2 + (v2 + (u3 + v3)))) := by
            congr 1
            rw [← CommRing.add_assoc u3 v1, CommRing.add_comm u3 v1, CommRing.add_assoc v1 u3,
                ← CommRing.add_assoc u2 v1, CommRing.add_comm u2 v1, CommRing.add_assoc v1 u2]
            congr 1
            rw [← CommRing.add_assoc u3 v2, CommRing.add_comm u3 v2, CommRing.add_assoc v2 u3]
        _ = (u1 + v1) + ((u3 + v3) + (u2 + v2)) := by
            rw [← CommRing.add_assoc u1 v1]
            congr 1
            rw [← CommRing.add_assoc u2 v2, CommRing.add_comm (u2 + v2)]
    exact hre a b c (-d) (-e) (-f)
  -- 5. Concatenate the 4 factor blocks into inner dimension `D := (k0 + k0) + (q1 + q1) = 2 * (q - n)` and apply `matRankFactor_le`!
  let D := (k0 + k0) + (q1 + q1)
  let FL (i t : Nat) : K :=
    if t < k0 then La i t
    else if t < k0 + k0 then Lb i (t - k0)
    else if t < (k0 + k0) + q1 then Lc i (t - (k0 + k0))
    else Ld i (t - ((k0 + k0) + q1))
  let FR (t j : Nat) : K :=
    if t < k0 then Ra t j
    else if t < k0 + k0 then Rb (t - k0) j
    else if t < (k0 + k0) + q1 then Rc (t - (k0 + k0)) j
    else Rd (t - ((k0 + k0) + q1)) j
  have hFLFR : MatEq n n (matMulF D FL FR)
      (matAdd (matAdd (matMulF k0 La Ra) (matMulF k0 Lb Rb))
              (matAdd (matMulF q1 Lc Rc) (matMulF q1 Ld Rd))) := by
    intro i j _ _
    unfold matMulF matAdd
    dsimp only [D]
    rw [sumR_split (k0 + k0) (q1 + q1), sumR_split k0 k0, sumR_split q1 q1]
    congr 1
    · congr 1
      · exact sumR_congr (fun t ht => by dsimp only [FL, FR]; rw [ite_t ht, ite_t ht])
      · apply sumR_congr; intro t ht; dsimp only [FL, FR]
        have h1 : ¬ (k0 + t < k0) := by omega
        have h2 : k0 + t < k0 + k0 := by omega
        have h3 : k0 + t - k0 = t := by omega
        rw [ite_f h1, ite_t h2, ite_f h1, ite_t h2, h3]
    · congr 1
      · apply sumR_congr; intro t ht; dsimp only [FL, FR]
        have h1 : ¬ (k0 + k0 + t < k0) := by omega
        have h2 : ¬ (k0 + k0 + t < k0 + k0) := by omega
        have h3 : k0 + k0 + t < k0 + k0 + q1 := by omega
        have h4 : k0 + k0 + t - (k0 + k0) = t := by omega
        rw [ite_f h1, ite_f h2, ite_t h3, ite_f h1, ite_f h2, ite_t h3, h4]
      · apply sumR_congr; intro t ht; dsimp only [FL, FR]
        have h1 : ¬ (k0 + k0 + (q1 + t) < k0) := by omega
        have h2 : ¬ (k0 + k0 + (q1 + t) < k0 + k0) := by omega
        have h3 : ¬ (k0 + k0 + (q1 + t) < k0 + k0 + q1) := by omega
        have h4 : k0 + k0 + (q1 + t) - (k0 + k0 + q1) = t := by omega
        rw [ite_f h1, ite_f h2, ite_f h3, ite_f h1, ite_f h2, ite_f h3, h4]
  have hnleD : n ≤ D := by
    apply matRankFactor_le D n FL (matMulF n FR Cinv)
    intro i j hi hj
    rw [← matMulF_assoc D n FL FR Cinv,
        matMulF_congr (fun t ht => by rw [hFLFR i t hi ht, ← hfull i t hi ht]) (fun _ _ => rfl)]
    exact hInvC.1 i j hi hj
  exact ⟨by omega, by omega⟩

-- ============================================================================
-- Section 6: Bläser's `5/2 m² - 3m` Lower Bound (`t3m_blaser_five_halves_matmul_bound`)
-- ============================================================================

/-- Left-multiplication Kronecker matrix `L_X = X ⊗ I_m` on `[m^2] × [m^2]`. -/
def leftMulMat {R : Type} [CommRing R] (m : Nat) (X : Nat → Nat → R) (c b : Nat) : R :=
  if c % m = b % m then X (c / m) (b / m) else 0

theorem leftMulMat_eq_tensor_slice {R : Type} [CommRing R] (m : Nat) (X : Nat → Nat → R)
    (c b : Nat) (hc : c < m * m) (hb : b < m * m) :
    leftMulMat m X c b = sumR (m * m) (fun a => X (a / m) (a % m) * intToR (matMulTensor m a b c)) := by
  have hm : 0 < m := by cases m with | zero => simp at hc | succ _ => exact Nat.zero_lt_succ _
  have hcm : c / m < m := Nat.div_lt_of_lt_mul hc
  have hbm : b / m < m := Nat.div_lt_of_lt_mul hb
  by_cases hmod : c % m = b % m
  · let a0 := (c / m) * m + (b / m)
    have ha0_lt : a0 < m * m := by
      calc (c / m) * m + b / m < (c / m) * m + m := Nat.add_lt_add_left hbm _
        _ = (c / m + 1) * m := by rw [Nat.succ_mul]
        _ ≤ m * m := Nat.mul_le_mul_right m hcm
    have ha0_div : a0 / m = c / m := by
      dsimp only [a0]; rw [Nat.mul_comm (c / m) m, Nat.mul_add_div hm, Nat.div_eq_of_lt hbm, Nat.add_zero]
    have ha0_mod : a0 % m = b / m := by
      dsimp only [a0]; rw [Nat.mul_comm (c / m) m, Nat.mul_add_mod, Nat.mod_eq_of_lt hbm]
    unfold leftMulMat; rw [ite_t hmod]
    have hs : sumR (m * m) (fun a => X (a / m) (a % m) * intToR (matMulTensor m a b c)) =
        sumR (m * m) (fun a => if a = a0 then X (c / m) (b / m) else 0) := by
      apply sumR_congr; intro a ha
      by_cases hae : a = a0
      · subst hae
        rw [ite_t rfl, ha0_div, ha0_mod]
        unfold matMulTensor
        simp [ha0_div, ha0_mod, hmod.symm, ha0_lt, hb, hc, intToR_one, mul_one]
      · rw [ite_f hae]
        have hzero : matMulTensor m a b c = 0 := by
          unfold matMulTensor
          dsimp only
          split
          · rename_i hcond
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            have hd : a / m = c / m := hcond.1.1.1.1.1
            have hmd : a % m = b / m := hcond.1.1.1.1.2
            have heq : a = a0 := by
              have hr := Nat.div_add_mod a m
              rw [hd, hmd, Nat.mul_comm m (c / m)] at hr
              exact hr.symm
            exact absurd heq hae
          · rfl
        rw [hzero, intToR_zero, mul_zero]
    rw [hs, sumR_single (m * m) a0 _ ha0_lt]
  · unfold leftMulMat; rw [ite_f hmod]
    symm
    have hz : sumR (m * m) (fun a => X (a / m) (a % m) * intToR (matMulTensor m a b c)) =
        sumR (m * m) (fun _ => (0 : R)) := by
      apply sumR_congr; intro a _
      have h0 : matMulTensor m a b c = 0 := by
        unfold matMulTensor
        dsimp only
        split
        · rename_i hcond
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          exact absurd hcond.1.1.1.2.symm hmod
        · rfl
      rw [h0, intToR_zero, mul_zero]
    rw [hz, sumR_zero_fn]

theorem leftMulMat_mul {R : Type} [CommRing R] (m : Nat) (X Y : Nat → Nat → R) :
    MatEq (m * m) (m * m)
      (matMulF (m * m) (leftMulMat m X) (leftMulMat m Y))
      (leftMulMat m (matMulF m X Y)) := by
  intro c b hc hb
  have hm : 0 < m := by cases m with | zero => simp at hc | succ _ => exact Nat.zero_lt_succ _
  by_cases hmod : c % m = b % m
  · unfold leftMulMat matMulF
    rw [ite_t hmod]
    have hsplit : sumR (m * m) (fun t => (if c % m = t % m then X (c / m) (t / m) else 0) *
                                         (if t % m = b % m then Y (t / m) (b / m) else 0)) =
        sumR m (fun k => sumR m (fun r =>
          (if c % m = (k * m + r) % m then X (c / m) ((k * m + r) / m) else 0) *
          (if (k * m + r) % m = b % m then Y ((k * m + r) / m) (b / m) else 0))) := by
      have hsp : ∀ n : Nat, sumR (n * m) (fun t =>
            (if c % m = t % m then X (c / m) (t / m) else 0) *
            (if t % m = b % m then Y (t / m) (b / m) else 0)) =
          sumR n (fun k => sumR m (fun r =>
            (if c % m = (k * m + r) % m then X (c / m) ((k * m + r) / m) else 0) *
            (if (k * m + r) % m = b % m then Y ((k * m + r) / m) (b / m) else 0))) := by
        intro n; induction n with
        | zero => simp [sumR]
        | succ n' ihn =>
          rw [Nat.succ_mul, sumR_split (n' * m) m, ihn]; rfl
      exact hsp m
    rw [hsplit]
    apply sumR_congr; intro k _
    have hbm : b % m < m := Nat.mod_lt b hm
    have hs : sumR m (fun r =>
        (if c % m = (k * m + r) % m then X (c / m) ((k * m + r) / m) else 0) *
        (if (k * m + r) % m = b % m then Y ((k * m + r) / m) (b / m) else 0)) =
        sumR m (fun r => if r = b % m then X (c / m) k * Y k (b / m) else 0) := by
      apply sumR_congr; intro r hr
      have hmd : (k * m + r) % m = r := by rw [Nat.mul_comm k m, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      have hdv : (k * m + r) / m = k := by rw [Nat.mul_comm k m, Nat.mul_add_div hm, Nat.div_eq_of_lt hr, Nat.add_zero]
      rw [hmd, hdv]
      by_cases hrb : r = b % m
      · subst hrb; rw [ite_t rfl, ite_t hmod, ite_t rfl]
      · rw [ite_f hrb, ite_f hrb, mul_zero]
    rw [hs, sumR_single m (b % m) _ hbm]
  · unfold leftMulMat matMulF
    rw [ite_f hmod]
    have hz : sumR (m * m) (fun t => (if c % m = t % m then X (c / m) (t / m) else 0) *
                                     (if t % m = b % m then Y (t / m) (b / m) else 0)) =
        sumR (m * m) (fun _ => (0 : R)) := by
      apply sumR_congr; intro t _
      by_cases h1 : c % m = t % m
      · have h2 : t % m ≠ b % m := by omega
        rw [ite_f h2, mul_zero]
      · rw [ite_f h1, zero_mul]
    rw [hz, sumR_zero_fn]

theorem leftMulMat_id {R : Type} [CommRing R] (m : Nat) :
    MatEq (m * m) (m * m) (leftMulMat m (matIdF (R := R))) matIdF := by
  intro c b hc hb
  unfold leftMulMat matIdF
  by_cases hcb : c = b
  · subst hcb; simp
  · rw [ite_f hcb]
    by_cases hm : c % m = b % m
    · rw [ite_t hm]
      have hdiv_ne : c / m ≠ b / m := by
        intro hd
        have r1 := Nat.div_add_mod c m
        have r2 := Nat.div_add_mod b m
        rw [hd, hm] at r1; omega
      rw [ite_f hdiv_ne]
    · rw [ite_f hm]

theorem leftMulMat_isMatInv {R : Type} [CommRing R] {m : Nat} {X Xinv : Nat → Nat → R}
    (h : IsMatInv m X Xinv) : IsMatInv (m * m) (leftMulMat m X) (leftMulMat m Xinv) := by
  have hm_pos : ∀ c, c < m * m → c / m < m := fun _ hc => Nat.div_lt_of_lt_mul hc
  constructor
  · intro c b hc hb
    rw [leftMulMat_mul m X Xinv c b hc hb]
    have hcongr : leftMulMat m (matMulF m X Xinv) c b = leftMulMat m matIdF c b := by
      unfold leftMulMat; by_cases hmod : c % m = b % m
      · rw [ite_t hmod, ite_t hmod]; exact h.1 (c / m) (b / m) (hm_pos c hc) (hm_pos b hb)
      · rw [ite_f hmod, ite_f hmod]
    rw [hcongr, leftMulMat_id m c b hc hb]
  · intro c b hc hb
    rw [leftMulMat_mul m Xinv X c b hc hb]
    have hcongr : leftMulMat m (matMulF m Xinv X) c b = leftMulMat m matIdF c b := by
      unfold leftMulMat; by_cases hmod : c % m = b % m
      · rw [ite_t hmod, ite_t hmod]; exact h.2 (c / m) (b / m) (hm_pos c hc) (hm_pos b hb)
      · rw [ite_f hmod, ite_f hmod]
    rw [hcongr, leftMulMat_id m c b hc hb]

private theorem filter_mem_length_le :
    ∀ (L S : List Nat), ListNodup L → (L.filter (fun x => decide (x ∈ S))).length ≤ S.length
  | [], _, _ => Nat.zero_le _
  | x :: xs, S, ⟨hnot, hnd⟩ => by
    simp only [List.filter_cons]
    by_cases hx : x ∈ S
    · simp only [hx, decide_true, ↓reduceIte, List.length_cons]
      -- Remove one occurrence of `x` from `S`
      have herase : ∀ (T : List Nat), x ∈ T → ∃ T' : List Nat, T'.length + 1 = T.length ∧ ∀ y, y ∈ T → y ≠ x → y ∈ T' := by
        intro T
        induction T with
        | nil => intro h; simp at h
        | cons a as iha =>
          intro hm
          cases hm with
          | head => exact ⟨as, by simp, fun y hy hne => by cases hy with | head => exact absurd rfl hne | tail _ h' => exact h'⟩
          | tail _ h' =>
            obtain ⟨T', hlen, hmem⟩ := iha h'
            exact ⟨a :: T', by simp; omega, fun y hy hne => by
              cases hy with
              | head => exact List.mem_cons_self ..
              | tail _ h2 => exact List.mem_cons_of_mem a (hmem y h2 hne)⟩
      obtain ⟨S', hS'len, hS'mem⟩ := herase S hx
      have hsub : (xs.filter (fun y => decide (y ∈ S))).length ≤ (xs.filter (fun y => decide (y ∈ S'))).length := by
        have hfl : ∀ (M : List Nat), (∀ y, y ∈ M → y ≠ x) →
            (M.filter (fun y => decide (y ∈ S))).length ≤ (M.filter (fun y => decide (y ∈ S'))).length := by
          intro M
          induction M with
          | nil => intro _; exact Nat.le_refl 0
          | cons u us ihu =>
            intro hne
            have hle := ihu (fun y hy => hne y (List.mem_cons_of_mem u hy))
            simp only [List.filter_cons]
            by_cases hu : u ∈ S
            · have hu' : u ∈ S' := hS'mem u hu (hne u (List.mem_cons_self ..))
              simp only [hu, hu', decide_true, ↓reduceIte, List.length_cons]; omega
            · by_cases hu' : u ∈ S' <;> simp [hu, hu'] <;> omega
        exact hfl xs hnot
      have ih := filter_mem_length_le xs S' hnd
      omega
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact filter_mem_length_le xs S hnd

/-- **Core Bläser (1999) Rank Lower Bound for `m ≥ 2` over EVERY `SimpleField F` (incl. `F_2`!):**
    `5 * m * m - 6 * m ≤ 2 * r` whenever `rank_F(⟨m, m, m⟩) ≤ r`. -/
theorem blaser_matmul_rank_ge_five_halves (F : Type) [SimpleField F] (m r : Nat) (hm : 2 ≤ m)
    (hr : HasTensorRankAtMost (m * m) (m * m) (m * m) r
            (fun a b c => intToR (R := F) (matMulTensor m a b c))) :
    5 * m * m - 6 * m ≤ 2 * r := by
  have hm_pos : 0 < m := by omega
  let N := m * m
  obtain ⟨U, V, W, hT⟩ := hr
  -- Step 1: Build explicit right-inverse `Rinv` of `U^T` (`N × r`) and apply `col_basis_of_right_inv`!
  let UT (a s : Nat) : F := U s a
  let Rinv (s a' : Nat) : F := V s ((a' % m) * m) * W s ((a' / m) * m)
  have hUR : MatEq N N (matMulF r UT Rinv) matIdF := by
    intro a a' ha ha'
    have h1 : (a' % m) * m < N := by
      have hlt : a' % m < m := Nat.mod_lt a' hm_pos
      calc (a' % m) * m < (a' % m) * m + m := Nat.lt_add_of_pos_right hm_pos
        _ = (a' % m + 1) * m := by rw [Nat.succ_mul]
        _ ≤ m * m := Nat.mul_le_mul_right m hlt
    have h2 : (a' / m) * m < N := by
      have hlt : a' / m < m := Nat.div_lt_of_lt_mul ha'
      calc (a' / m) * m < (a' / m) * m + m := Nat.lt_add_of_pos_right hm_pos
        _ = (a' / m + 1) * m := by rw [Nat.succ_mul]
        _ ≤ m * m := Nat.mul_le_mul_right m hlt
    have hsum : matMulF r UT Rinv a a' =
        sumR r (fun s => U s a * V s ((a' % m) * m) * W s ((a' / m) * m)) := by
      unfold matMulF UT Rinv
      exact sumR_congr (fun s _ => (CommRing.mul_assoc ..).symm)
    rw [hsum, ← hT a ((a' % m) * m) ((a' / m) * m) ha h1 h2]
    unfold matMulTensor matIdF
    dsimp only
    rw [Nat.mul_div_cancel _ hm_pos, Nat.mul_div_cancel _ hm_pos, Nat.mul_mod_left, Nat.mul_mod_left]
    by_cases hae : a = a'
    · subst hae; dsimp only [N] at ha h1 h2; simp only [ha, h1, h2, decide_true, Bool.and_self, ↓reduceIte, intToR_one]
    · rw [ite_f hae]
      have h0 : ¬ (a / m = a' / m ∧ a % m = a' % m) := by
        intro ⟨hd, hmd⟩
        have r1 := Nat.div_add_mod a m
        have r2 := Nat.div_add_mod a' m
        rw [hd, hmd] at r1; omega
      split
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        exact absurd ⟨hcond.1.1.1.1.1, hcond.1.1.1.1.2⟩ h0
      · exact intToR_zero
  obtain ⟨hNr, π, πInv, Binv, hbij, hUTB⟩ := col_basis_of_right_inv N r UT Rinv hUR
  -- `hUTB.1 : (UT ∘ π) * Binv = I_N`  (so `∑_j U (π j) a * Binv j b = δ_{a,b}`, SPANNING!)
  -- `hUTB.2 : Binv * (UT ∘ π) = I_N`  (so `∑_a Binv i a * U (π j) a = δ_{i,j}`, DUALITY!)
  let Bmat (i r c : Nat) : F := Binv i (r * m + c)
  have hrc_bound : ∀ r c, r < m → c < m → r * m + c < N := by
    intro r c hr hc
    calc r * m + c < r * m + m := Nat.add_lt_add_left hc _
      _ = (r + 1) * m := by rw [Nat.succ_mul]
      _ ≤ m * m := Nat.mul_le_mul_right m hr
  have hrc_dm : ∀ r c, c < m → (r * m + c) / m = r ∧ (r * m + c) % m = c := by
    intro r c hc
    exact ⟨by rw [Nat.mul_comm r m, Nat.mul_add_div hm_pos, Nat.div_eq_of_lt hc, Nat.add_zero],
           by rw [Nat.mul_comm r m, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]⟩
  -- Spanning helper over ANY field extension `K` via a ring hom `φ : F → K`:
  have hspan : ∀ {K : Type} [SimpleField K] (φ : RingHom F K) (Y : Nat → Nat → K),
      ∃ α : Nat → K,
        MatEq m m Y (fun r c => sumR N (fun i => α i * φ.toFun (Bmat i r c))) := by
    intro K _ φ Y
    let α (i : Nat) : K := sumR N (fun a => φ.toFun (U (π i) a) * Y (a / m) (a % m))
    refine ⟨α, ?_⟩
    intro r c hr hc
    have hlt := hrc_bound r c hr hc
    obtain ⟨hdv, hmd⟩ := hrc_dm r c hc
    have hinvK := φ.map_isMatInv hUTB
    have hswap : sumR N (fun i => α i * φ.toFun (Bmat i r c)) =
        sumR N (fun a => matMulF N (fun x y => φ.toFun (UT x (π y))) (fun x y => φ.toFun (Binv x y)) a (r * m + c) * Y (a / m) (a % m)) := by
      calc sumR N (fun i => α i * φ.toFun (Bmat i r c))
          = sumR N (fun i => sumR N (fun a => φ.toFun (U (π i) a) * Y (a / m) (a % m) * φ.toFun (Binv i (r * m + c)))) :=
            sumR_congr (fun i _ => sumR_mul_right N _ _)
        _ = sumR N (fun a => sumR N (fun i => φ.toFun (U (π i) a) * Y (a / m) (a % m) * φ.toFun (Binv i (r * m + c)))) :=
            sumR_swap N N _
        _ = sumR N (fun a => sumR N (fun i => φ.toFun (U (π i) a) * φ.toFun (Binv i (r * m + c))) * Y (a / m) (a % m)) := by
            apply sumR_congr; intro a _
            rw [sumR_mul_right]; apply sumR_congr; intro i _
            rw [CommRing.mul_assoc (φ.toFun (U (π i) a)), CommRing.mul_comm (Y (a / m) (a % m)),
                ← CommRing.mul_assoc]
    dsimp only
    rw [hswap]
    have hs : sumR N (fun a => matMulF N (fun x y => φ.toFun (UT x (π y))) (fun x y => φ.toFun (Binv x y)) a (r * m + c) * Y (a / m) (a % m)) =
        sumR N (fun a => if a = r * m + c then Y r c else 0) := by
      apply sumR_congr; intro a ha
      rw [hinvK.1 a (r * m + c) ha hlt]
      unfold matIdF
      by_cases hae : a = r * m + c
      · subst hae; rw [ite_t rfl, ite_t rfl, CommRing.one_mul, hdv, hmd]
      · rw [ite_f hae, ite_f hae, zero_mul]
    rw [hs, sumR_single N (r * m + c) (Y r c) hlt]
  -- Duality helper over ANY field extension `K` via a ring hom `φ : F → K`:
  have hdual : ∀ {K : Type} [SimpleField K] (φ : RingHom F K) (c : Nat → K) (j : Nat), j < N →
      sumR N (fun a => (sumR N (fun i => c i * φ.toFun (Bmat i (a / m) (a % m)))) * φ.toFun (U (π j) a)) = c j := by
    intro K _ φ c j hj
    have hinvK := φ.map_isMatInv hUTB
    have hswap : sumR N (fun a => (sumR N (fun i => c i * φ.toFun (Bmat i (a / m) (a % m)))) * φ.toFun (U (π j) a)) =
        sumR N (fun i => c i * matMulF N (fun x y => φ.toFun (Binv x y)) (fun x y => φ.toFun (UT x (π y))) i j) := by
      calc sumR N (fun a => (sumR N (fun i => c i * φ.toFun (Bmat i (a / m) (a % m)))) * φ.toFun (U (π j) a))
          = sumR N (fun a => sumR N (fun i => c i * φ.toFun (Bmat i (a / m) (a % m)) * φ.toFun (U (π j) a))) :=
            sumR_congr (fun a _ => sumR_mul_right N _ _)
        _ = sumR N (fun i => sumR N (fun a => c i * φ.toFun (Bmat i (a / m) (a % m)) * φ.toFun (U (π j) a))) :=
            sumR_swap N N _
        _ = sumR N (fun i => c i * sumR N (fun a => φ.toFun (Binv i a) * φ.toFun (U (π j) a))) := by
            apply sumR_congr; intro i _; rw [sumR_mul_left]
            apply sumR_congr; intro a _
            have hrec : (a / m) * m + a % m = a := by rw [Nat.mul_comm (a / m) m]; exact Nat.div_add_mod a m
            dsimp only [Bmat]; rw [hrec, CommRing.mul_assoc]
    rw [hswap]
    have hs : sumR N (fun i => c i * matMulF N (fun x y => φ.toFun (Binv x y)) (fun x y => φ.toFun (UT x (π y))) i j) =
        sumR N (fun i => if i = j then c j else 0) := by
      apply sumR_congr; intro i hi
      rw [hinvK.2 i j hi hj]
      unfold matIdF
      by_cases hij : i = j
      · subst hij; rw [ite_t rfl, ite_t rfl, mul_one]
      · rw [ite_f hij, ite_f hij, mul_zero]
    rw [hs, sumR_single N j (c j) hj]
  -- Helper: RingHom composition
  let compHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : RingHom B C) (f : RingHom A B) : RingHom A C :=
    ⟨fun x => g.toFun (f.toFun x),
     by rw [f.map_zero, g.map_zero], by rw [f.map_one, g.map_one],
     fun a b => by rw [f.map_add, g.map_add], fun a => by rw [f.map_neg, g.map_neg],
     fun a b => by rw [f.map_mul, g.map_mul]⟩
  -- Step 2 (Tower Stage 1: `F → K1 = RatFunc F`): Pick `S1` (`|S1| ≤ m`) spanning invertible `Z`!
  let idF : RingHom F F := ⟨id, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  obtain ⟨aId, haId⟩ := hspan idF (matIdF (R := F))
  have hdetId : detM m (fun r c => sumR N (fun i => aId i * Bmat i r c)) ≠ 0 := by
    dsimp only [idF, id] at haId
    rw [← detM_congr m haId, detM_id m]
    exact Ne.symm SimpleField.zero_ne_one
  obtain ⟨S1, z1, hS1_len, hS1_sup, hdetZ⟩ := exists_le_m_subset_det_ne_zero m N Bmat aId hdetId
  let K1 := RatFunc F
  let φ1 : RingHom F K1 := ratConstHom F
  let Z : Nat → Nat → K1 := fun r c => sumR N (fun i => z1 i * φ1.toFun (Bmat i r c))
  obtain ⟨Zinv, hZinv⟩ := isMatInv_of_detM_ne_zero m Z hdetZ
  let Btil (i : Nat) : Nat → Nat → K1 := matMulF m Zinv (fun r c => φ1.toFun (Bmat i r c))
  -- Spanning property of `Btil` over ANY extension `ψ : K1 → K`!
  have hspan_Btil : ∀ {K : Type} [SimpleField K] (ψ : RingHom K1 K) (Y : Nat → Nat → K),
      ∃ α : Nat → K, MatEq m m Y (fun r c => sumR N (fun i => α i * ψ.toFun (Btil i r c))) := by
    intro K _ ψ Y
    let ZK (r c : Nat) : K := ψ.toFun (Z r c)
    let ZinvK (r c : Nat) : K := ψ.toFun (Zinv r c)
    have hZinvK : IsMatInv m ZK ZinvK := ψ.map_isMatInv hZinv
    obtain ⟨α, hα⟩ := hspan (compHom ψ φ1) (matMulF m ZK Y)
    refine ⟨α, ?_⟩
    intro r c hr hc
    have hmul : sumR N (fun i => α i * ψ.toFun (Btil i r c)) =
        matMulF m ZinvK (fun a b => sumR N (fun i => α i * ψ.toFun (φ1.toFun (Bmat i a b)))) r c := by
      unfold matMulF
      calc sumR N (fun i => α i * ψ.toFun (Btil i r c))
          = sumR N (fun i => α i * sumR m (fun k => ZinvK r k * ψ.toFun (φ1.toFun (Bmat i k c)))) :=
            sumR_congr (fun i _ => by dsimp only [Btil]; rw [ψ.map_matMulF]; rfl)
        _ = sumR N (fun i => sumR m (fun k => ZinvK r k * (α i * ψ.toFun (φ1.toFun (Bmat i k c))))) := by
            apply sumR_congr; intro i _; rw [sumR_mul_left]
            apply sumR_congr; intro k _
            rw [← CommRing.mul_assoc, CommRing.mul_comm (α i) (ZinvK r k), CommRing.mul_assoc]
        _ = sumR m (fun k => sumR N (fun i => ZinvK r k * (α i * ψ.toFun (φ1.toFun (Bmat i k c))))) := sumR_swap N m _
        _ = sumR m (fun k => ZinvK r k * sumR N (fun i => α i * ψ.toFun (φ1.toFun (Bmat i k c)))) :=
            sumR_congr (fun k _ => (sumR_mul_left N _ _).symm)
    dsimp only
    rw [hmul, matMulF_congr (fun _ _ => rfl) (fun k hk => (hα k c hk hc).symm),
        ← matMulF_assoc m m ZinvK ZK Y r c,
        matMulF_congr (fun k hk => hZinvK.2 r k hr hk) (fun _ _ => rfl),
        matMulF_id_left m Y hr]
  -- Step 3 (Tower Stage 2: `K1 → K2 = RatFunc K1`): Pick `S2` (`|S2| ≤ m`) with `detM m [Xhat, Y0] ≠ 0`!
  let idK1 : RingHom K1 K1 := ⟨id, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  let X0 : Nat → Nat → K1 := commPairX m
  let Y0 : Nat → Nat → K1 := commPairY m
  obtain ⟨ax, hax⟩ := hspan_Btil idK1 X0
  let M2 (i : Nat) : Nat → Nat → K1 := matComm m (Btil i) Y0
  have hcomm_lin_L : ∀ {K : Type} [SimpleField K] (B_fam : Nat → Nat → Nat → K) (Y : Nat → Nat → K) (c : Nat → K),
      MatEq m m (matComm m (fun r s => sumR N (fun i => c i * B_fam i r s)) Y)
                (fun r s => sumR N (fun i => c i * matComm m (B_fam i) Y r s)) := by
    intro K _ Bfam Y c r s _ _
    unfold matComm matSub matMulF
    have h1 : sumR m (fun k => sumR N (fun i => c i * Bfam i r k) * Y k s) =
        sumR N (fun i => c i * sumR m (fun k => Bfam i r k * Y k s)) := by
      calc sumR m (fun k => sumR N (fun i => c i * Bfam i r k) * Y k s)
          = sumR m (fun k => sumR N (fun i => c i * (Bfam i r k * Y k s))) :=
            sumR_congr (fun k _ => by rw [sumR_mul_right]; exact sumR_congr (fun i _ => CommRing.mul_assoc ..))
        _ = sumR N (fun i => sumR m (fun k => c i * (Bfam i r k * Y k s))) := sumR_swap m N _
        _ = sumR N (fun i => c i * sumR m (fun k => Bfam i r k * Y k s)) :=
            sumR_congr (fun i _ => (sumR_mul_left m _ _).symm)
    have h2 : sumR m (fun k => Y r k * sumR N (fun i => c i * Bfam i k s)) =
        sumR N (fun i => c i * sumR m (fun k => Y r k * Bfam i k s)) := by
      calc sumR m (fun k => Y r k * sumR N (fun i => c i * Bfam i k s))
          = sumR m (fun k => sumR N (fun i => c i * (Y r k * Bfam i k s))) :=
            sumR_congr (fun k _ => by
              rw [sumR_mul_left]; apply sumR_congr; intro i _
              rw [← CommRing.mul_assoc, CommRing.mul_comm (Y r k) (c i), CommRing.mul_assoc])
        _ = sumR N (fun i => sumR m (fun k => c i * (Y r k * Bfam i k s))) := sumR_swap m N _
        _ = sumR N (fun i => c i * sumR m (fun k => Y r k * Bfam i k s)) :=
            sumR_congr (fun i _ => (sumR_mul_left m _ _).symm)
    rw [h1, h2, ← sumR_sub]
    exact sumR_congr (fun i _ => (mul_sub_r ..).symm)
  have hcomm_lin_R : ∀ {K : Type} [SimpleField K] (X : Nat → Nat → K) (B_fam : Nat → Nat → Nat → K) (c : Nat → K),
      MatEq m m (matComm m X (fun r s => sumR N (fun i => c i * B_fam i r s)))
                (fun r s => sumR N (fun i => c i * matComm m X (B_fam i) r s)) := by
    intro K _ X Bfam c r s _ _
    unfold matComm matSub matMulF
    have h1 : sumR m (fun k => X r k * sumR N (fun i => c i * Bfam i k s)) =
        sumR N (fun i => c i * sumR m (fun k => X r k * Bfam i k s)) := by
      calc sumR m (fun k => X r k * sumR N (fun i => c i * Bfam i k s))
          = sumR m (fun k => sumR N (fun i => c i * (X r k * Bfam i k s))) :=
            sumR_congr (fun k _ => by
              rw [sumR_mul_left]; apply sumR_congr; intro i _
              rw [← CommRing.mul_assoc, CommRing.mul_comm (X r k) (c i), CommRing.mul_assoc])
        _ = sumR N (fun i => sumR m (fun k => c i * (X r k * Bfam i k s))) := sumR_swap m N _
        _ = sumR N (fun i => c i * sumR m (fun k => X r k * Bfam i k s)) :=
            sumR_congr (fun i _ => (sumR_mul_left m _ _).symm)
    have h2 : sumR m (fun k => sumR N (fun i => c i * Bfam i r k) * X k s) =
        sumR N (fun i => c i * sumR m (fun k => Bfam i r k * X k s)) := by
      calc sumR m (fun k => sumR N (fun i => c i * Bfam i r k) * X k s)
          = sumR m (fun k => sumR N (fun i => c i * (Bfam i r k * X k s))) :=
            sumR_congr (fun k _ => by rw [sumR_mul_right]; exact sumR_congr (fun i _ => CommRing.mul_assoc ..))
        _ = sumR N (fun i => sumR m (fun k => c i * (Bfam i r k * X k s))) := sumR_swap m N _
        _ = sumR N (fun i => c i * sumR m (fun k => Bfam i r k * X k s)) :=
            sumR_congr (fun i _ => (sumR_mul_left m _ _).symm)
    rw [h1, h2, ← sumR_sub]
    exact sumR_congr (fun i _ => (mul_sub_r ..).symm)
  have hdet2_init : detM m (fun r s => sumR N (fun i => ax i * M2 i r s)) ≠ 0 := by
    dsimp only [idK1, id] at hax
    have heq : MatEq m m (matComm m X0 Y0) (fun r s => sumR N (fun i => ax i * M2 i r s)) := by
      intro r s hr hs
      have hsub : matComm m X0 Y0 r s = matComm m (fun a b => sumR N (fun i => ax i * Btil i a b)) Y0 r s := by
        unfold matComm matSub
        congr 1
        · exact matMulF_congr (fun k hk => hax r k hr hk) (fun _ _ => rfl)
        · exact matMulF_congr (fun _ _ => rfl) (fun k hk => hax k s hk hs)
      rw [hsub]
      exact hcomm_lin_L Btil Y0 ax r s hr hs
    rw [← detM_congr m heq, detM_commPair m hm]
    exact Ne.symm SimpleField.zero_ne_one
  obtain ⟨S2, x2, hS2_len, hS2_sup, hdetXhat⟩ := exists_le_m_subset_det_ne_zero m N M2 ax hdet2_init
  let K2 := RatFunc K1
  let φ2 : RingHom K1 K2 := ratConstHom K1
  let Xhat : Nat → Nat → K2 := fun r s => sumR N (fun i => x2 i * φ2.toFun (Btil i r s))
  let Y0_2 : Nat → Nat → K2 := fun r s => φ2.toFun (Y0 r s)
  -- Step 4 (Tower Stage 3: `K2 → K3 = RatFunc K2`): Pick `S3` (`|S3| ≤ m`) with `detM m [Xhat, Yhat] ≠ 0`!
  obtain ⟨ay, hay⟩ := hspan_Btil φ2 Y0_2
  let M3 (i : Nat) : Nat → Nat → K2 := matComm m Xhat (fun r s => φ2.toFun (Btil i r s))
  have hdet3_init : detM m (fun r s => sumR N (fun i => ay i * M3 i r s)) ≠ 0 := by
    have heq1 : MatEq m m (fun r s => sumR N (fun i => x2 i * φ2.toFun (M2 i r s))) (matComm m Xhat Y0_2) := by
      intro r s hr hs
      symm
      rw [hcomm_lin_L (fun i a b => φ2.toFun (Btil i a b)) Y0_2 x2 r s hr hs]
      apply sumR_congr; intro i _
      congr 1
      dsimp only [M2, matComm, matSub]
      rw [φ2.map_sub, φ2.map_matMulF, φ2.map_matMulF]
    have heq2 : MatEq m m (matComm m Xhat Y0_2) (fun r s => sumR N (fun i => ay i * M3 i r s)) := by
      intro r s hr hs
      have hsub : matComm m Xhat Y0_2 r s = matComm m Xhat (fun a b => sumR N (fun i => ay i * φ2.toFun (Btil i a b))) r s := by
        unfold matComm matSub
        congr 1
        · exact matMulF_congr (fun _ _ => rfl) (fun k hk => hay k s hk hs)
        · exact matMulF_congr (fun k hk => hay r k hr hk) (fun _ _ => rfl)
      rw [hsub]
      exact hcomm_lin_R Xhat (fun i a b => φ2.toFun (Btil i a b)) ay r s hr hs
    rw [← detM_congr m heq2, ← detM_congr m heq1]
    exact hdetXhat
  obtain ⟨S3, y3, hS3_len, hS3_sup, hdetXY⟩ := exists_le_m_subset_det_ne_zero m N M3 ay hdet3_init
  let K3 := RatFunc K2
  let φ3 : RingHom K2 K3 := ratConstHom K2
  let φ23 : RingHom K1 K3 := compHom φ3 φ2
  let φ13 : RingHom F K3 := compHom φ23 φ1
  let X3 : Nat → Nat → K3 := fun r s => φ3.toFun (Xhat r s)
  let Y3 : Nat → Nat → K3 := fun r s => sumR N (fun i => y3 i * φ23.toFun (Btil i r s))
  have hdetComm3 : detM m (matComm m X3 Y3) ≠ 0 := by
    have heq : MatEq m m (fun r s => sumR N (fun i => y3 i * φ3.toFun (M3 i r s))) (matComm m X3 Y3) := by
      intro r s hr hs
      symm
      rw [hcomm_lin_R X3 (fun i a b => φ23.toFun (Btil i a b)) y3 r s hr hs]
      apply sumR_congr; intro i _
      congr 1
      dsimp only [M3, matComm, matSub]
      rw [φ3.map_sub, φ3.map_matMulF, φ3.map_matMulF]
    rw [← detM_congr m heq]; exact hdetXY
  obtain ⟨CommInv, hCommInv⟩ := isMatInv_of_detM_ne_zero m (matComm m X3 Y3) hdetComm3
  -- Step 5: Assemble the 3 matrices `M0, M1, M2mat` in `K3^{m × m}` with supports in `S1, S2, S3`!
  let M0 : Nat → Nat → K3 := fun r s => sumR N (fun i => φ23.toFun (z1 i) * φ13.toFun (Bmat i r s))
  let M1 : Nat → Nat → K3 := fun r s => sumR N (fun i => φ3.toFun (x2 i) * φ13.toFun (Bmat i r s))
  let M2m : Nat → Nat → K3 := fun r s => sumR N (fun i => y3 i * φ13.toFun (Bmat i r s))
  let M0inv : Nat → Nat → K3 := fun r s => φ23.toFun (Zinv r s)
  have hM0_eq_Z : MatEq m m M0 (fun r s => φ23.toFun (Z r s)) := by
    intro r s _ _
    dsimp only [M0, Z]
    rw [φ23.map_sumR]
    exact sumR_congr (fun i _ => (φ23.map_mul (z1 i) (φ1.toFun (Bmat i r s))).symm)
  have hInvM0 : IsMatInv m M0 M0inv := by
    have hZ3 := φ23.map_isMatInv hZinv
    constructor
    · intro i j hi hj
      have h1 : matMulF m M0 M0inv i j = matMulF m (fun r s => φ23.toFun (Z r s)) (fun r s => φ23.toFun (Zinv r s)) i j :=
        matMulF_congr (fun k hk => hM0_eq_Z i k hi hk) (fun _ _ => rfl)
      rw [h1]; exact hZ3.1 i j hi hj
    · intro i j hi hj
      have h2 : matMulF m M0inv M0 i j = matMulF m (fun r s => φ23.toFun (Zinv r s)) (fun r s => φ23.toFun (Z r s)) i j :=
        matMulF_congr (fun _ _ => rfl) (fun k hk => hM0_eq_Z k j hk hj)
      rw [h2]; exact hZ3.2 i j hi hj
  have hM0_Btil : ∀ i, MatEq m m (matMulF m M0 (fun r s => φ23.toFun (Btil i r s))) (fun r s => φ13.toFun (Bmat i r s)) := by
    intro i r s hr hs
    have hZ3 := φ23.map_isMatInv hZinv
    calc matMulF m M0 (fun a b => φ23.toFun (Btil i a b)) r s
        = matMulF m (fun a b => φ23.toFun (Z a b)) (matMulF m M0inv (fun a b => φ13.toFun (Bmat i a b))) r s :=
          matMulF_congr (fun k hk => hM0_eq_Z r k hr hk) (fun k _ => φ23.map_matMulF m Zinv _ k s)
      _ = matMulF m (matMulF m (fun a b => φ23.toFun (Z a b)) M0inv) (fun a b => φ13.toFun (Bmat i a b)) r s :=
          (matMulF_assoc m m _ M0inv _ r s).symm
      _ = matMulF m matIdF (fun a b => φ13.toFun (Bmat i a b)) r s :=
          matMulF_congr (fun k hk => hZ3.1 r k hr hk) (fun _ _ => rfl)
      _ = φ13.toFun (Bmat i r s) := matMulF_id_left m _ hr
  have hM1_eq : MatEq m m M1 (matMulF m M0 X3) := by
    intro r s hr hs
    have hX3 : ∀ a b, X3 a b = sumR N (fun i => φ3.toFun (x2 i) * φ23.toFun (Btil i a b)) := by
      intro a b; dsimp only [X3, Xhat]; rw [φ3.map_sumR]
      exact sumR_congr (fun i _ => φ3.map_mul (x2 i) (φ2.toFun (Btil i a b)))
    unfold matMulF
    calc M1 r s = sumR N (fun i => φ3.toFun (x2 i) * matMulF m M0 (fun a b => φ23.toFun (Btil i a b)) r s) :=
           sumR_congr (fun i _ => by rw [hM0_Btil i r s hr hs])
      _ = sumR N (fun i => sumR m (fun k => M0 r k * (φ3.toFun (x2 i) * φ23.toFun (Btil i k s)))) := by
           apply sumR_congr; intro i _; unfold matMulF; rw [sumR_mul_left]
           apply sumR_congr; intro k _
           rw [← CommRing.mul_assoc, CommRing.mul_comm (φ3.toFun (x2 i)) (M0 r k), CommRing.mul_assoc]
      _ = sumR m (fun k => sumR N (fun i => M0 r k * (φ3.toFun (x2 i) * φ23.toFun (Btil i k s)))) := sumR_swap N m _
      _ = sumR m (fun k => M0 r k * X3 k s) := by
           apply sumR_congr; intro k _; rw [← sumR_mul_left, ← hX3 k s]
  have hM2_eq : MatEq m m M2m (matMulF m M0 Y3) := by
    intro r s hr hs
    unfold matMulF
    calc M2m r s = sumR N (fun i => y3 i * matMulF m M0 (fun a b => φ23.toFun (Btil i a b)) r s) :=
           sumR_congr (fun i _ => by rw [hM0_Btil i r s hr hs])
      _ = sumR N (fun i => sumR m (fun k => M0 r k * (y3 i * φ23.toFun (Btil i k s)))) := by
           apply sumR_congr; intro i _; unfold matMulF; rw [sumR_mul_left]
           apply sumR_congr; intro k _
           rw [← CommRing.mul_assoc, CommRing.mul_comm (y3 i) (M0 r k), CommRing.mul_assoc]
      _ = sumR m (fun k => sumR N (fun i => M0 r k * (y3 i * φ23.toFun (Btil i k s)))) := sumR_swap N m _
      _ = sumR m (fun k => M0 r k * Y3 k s) :=
           sumR_congr (fun k _ => (sumR_mul_left N _ _).symm)
  -- `M1 * M0inv * M2m - M2m * M0inv * M1 = M0 * [X3, Y3]`, hence invertible with inverse `CommInv * M0inv`!
  have hCommM : MatEq m m
      (matSub (matMulF m (matMulF m M1 M0inv) M2m) (matMulF m (matMulF m M2m M0inv) M1))
      (matMulF m M0 (matComm m X3 Y3)) := by
    intro r s hr hs
    have h1 : matMulF m (matMulF m M1 M0inv) M2m r s = matMulF m M0 (matMulF m X3 Y3) r s := by
      have hM1inv : ∀ k, k < m → matMulF m M1 M0inv r k = matMulF m M0 (matMulF m X3 M0inv) r k := by
        intro k _
        rw [matMulF_congr (fun t ht => hM1_eq r t hr ht) (fun _ _ => rfl), matMulF_assoc]
      calc matMulF m (matMulF m M1 M0inv) M2m r s
          = matMulF m (matMulF m M0 (matMulF m X3 M0inv)) (matMulF m M0 Y3) r s :=
            matMulF_congr (fun k hk => hM1inv k hk) (fun k hk => hM2_eq k s hk hs)
        _ = matMulF m M0 (matMulF m (matMulF m X3 M0inv) (matMulF m M0 Y3)) r s := matMulF_assoc m m ..
        _ = matMulF m M0 (matMulF m X3 (matMulF m M0inv (matMulF m M0 Y3))) r s :=
            matMulF_congr (fun _ _ => rfl) (fun k _ => matMulF_assoc m m ..)
        _ = matMulF m M0 (matMulF m X3 Y3) r s := by
            apply matMulF_congr (fun _ _ => rfl); intro k _
            apply matMulF_congr (fun _ _ => rfl); intro t ht
            rw [← matMulF_assoc m m M0inv M0 Y3 t s,
                matMulF_congr (fun u hu => hInvM0.2 t u ht hu) (fun _ _ => rfl),
                matMulF_id_left m Y3 ht]
    have h2 : matMulF m (matMulF m M2m M0inv) M1 r s = matMulF m M0 (matMulF m Y3 X3) r s := by
      have hM2inv : ∀ k, k < m → matMulF m M2m M0inv r k = matMulF m M0 (matMulF m Y3 M0inv) r k := by
        intro k _
        rw [matMulF_congr (fun t ht => hM2_eq r t hr ht) (fun _ _ => rfl), matMulF_assoc]
      calc matMulF m (matMulF m M2m M0inv) M1 r s
          = matMulF m (matMulF m M0 (matMulF m Y3 M0inv)) (matMulF m M0 X3) r s :=
            matMulF_congr (fun k hk => hM2inv k hk) (fun k hk => hM1_eq k s hk hs)
        _ = matMulF m M0 (matMulF m (matMulF m Y3 M0inv) (matMulF m M0 X3)) r s := matMulF_assoc m m ..
        _ = matMulF m M0 (matMulF m Y3 (matMulF m M0inv (matMulF m M0 X3))) r s :=
            matMulF_congr (fun _ _ => rfl) (fun k _ => matMulF_assoc m m ..)
        _ = matMulF m M0 (matMulF m Y3 X3) r s := by
            apply matMulF_congr (fun _ _ => rfl); intro k _
            apply matMulF_congr (fun _ _ => rfl); intro t ht
            rw [← matMulF_assoc m m M0inv M0 X3 t s,
                matMulF_congr (fun u hu => hInvM0.2 t u ht hu) (fun _ _ => rfl),
                matMulF_id_left m X3 ht]
    unfold matSub matComm
    rw [h1, h2, ← matMulF_sub_right]
  -- Step 6: Lift to `N × N` Kronecker left-multiplication slices `A0, A1, A2` and drop all `j < N, j ∉ S`!
  let A0 := leftMulMat m M0
  let A1 := leftMulMat m M1
  let A2 := leftMulMat m M2m
  let A0inv := leftMulMat m M0inv
  have hInvA0 : IsMatInv N A0 A0inv := leftMulMat_isMatInv hInvM0
  let CinvSmall := matMulF m CommInv M0inv
  have hInvBigComm : IsMatInv m (matMulF m M0 (matComm m X3 Y3)) CinvSmall := isMatInv_mul hInvM0 hCommInv
  let Cinv := leftMulMat m CinvSmall
  have hInvA_comm : IsMatInv N
      (matSub (matMulF N (matMulF N A1 A0inv) A2) (matMulF N (matMulF N A2 A0inv) A1)) Cinv := by
    have hBig := leftMulMat_isMatInv hInvBigComm
    have hEqA : MatEq N N
        (matSub (matMulF N (matMulF N A1 A0inv) A2) (matMulF N (matMulF N A2 A0inv) A1))
        (leftMulMat m (matMulF m M0 (matComm m X3 Y3))) := by
      intro c b hc hb
      have h1 : matMulF N (matMulF N A1 A0inv) A2 c b = leftMulMat m (matMulF m (matMulF m M1 M0inv) M2m) c b := by
        rw [matMulF_congr (fun t ht => leftMulMat_mul m M1 M0inv c t hc ht) (fun _ _ => rfl),
            leftMulMat_mul m (matMulF m M1 M0inv) M2m c b hc hb]
      have h2 : matMulF N (matMulF N A2 A0inv) A1 c b = leftMulMat m (matMulF m (matMulF m M2m M0inv) M1) c b := by
        rw [matMulF_congr (fun t ht => leftMulMat_mul m M2m M0inv c t hc ht) (fun _ _ => rfl),
            leftMulMat_mul m (matMulF m M2m M0inv) M1 c b hc hb]
      unfold matSub; rw [h1, h2]
      unfold leftMulMat
      by_cases hmod : c % m = b % m
      · rw [ite_t hmod, ite_t hmod, ite_t hmod]
        exact hCommM (c / m) (b / m) (Nat.div_lt_of_lt_mul hc) (Nat.div_lt_of_lt_mul hb)
      · rw [ite_f hmod, ite_f hmod, ite_f hmod, sub_self]
    exact ⟨fun i j hi hj => by rw [matMulF_congr (fun t ht => hEqA i t hi ht) (fun _ _ => rfl)]; exact hBig.1 i j hi hj,
           fun i j hi hj => by rw [matMulF_congr (fun _ _ => rfl) (fun t ht => hEqA t j ht hj)]; exact hBig.2 i j hi hj⟩
  -- Permuted rank-`r` representation of `leftMulMat m X`:
  have hsum_perm_r : ∀ (f : Nat → K3), sumR r (fun t => f (π t)) = sumR r f := by
    intro f
    have hgen : ∀ (L : List Nat), ListNodup L → (∀ x, x ∈ L → x < r) →
        ∀ (g : Nat → K3), (∀ t, t < r → t ∉ L → g t = 0) →
        sumR r (fun t => g (π t)) = sumR r g := by
      intro L; induction L with
      | nil =>
        intro _ _ g hg
        rw [sumR_congr (fun t ht => hg (π t) (hbij t ht).1 (by simp)), sumR_zero_fn,
            sumR_congr (fun t ht => hg t ht (by simp)), sumR_zero_fn]
      | cons x xs ihL =>
        intro ⟨hnot, hnd⟩ hbd g hg
        let gx : Nat → K3 := fun t => if t = x then g x else 0
        let gr : Nat → K3 := fun t => if t = x then 0 else g t
        have hd : ∀ t, g t = gx t + gr t := fun t => by dsimp only [gx, gr]; by_cases h : t = x <;> simp [h, add_zero, CommRing.zero_add]
        have hL1 : sumR r (fun t => g (π t)) = sumR r (fun t => gx (π t)) + sumR r (fun t => gr (π t)) := by
          rw [← sumR_add]; exact sumR_congr (fun t _ => hd (π t))
        have hR1 : sumR r g = sumR r gx + sumR r gr := by
          rw [← sumR_add]; exact sumR_congr (fun t _ => hd t)
        have hxlt : x < r := hbd x (List.mem_cons_self ..)
        have hgx1 : sumR r (fun t => gx (π t)) = g x := by
          have hc : sumR r (fun t => gx (π t)) = sumR r (fun t => if t = πInv x then g x else 0) := by
            apply sumR_congr; intro t ht; dsimp only [gx]
            by_cases h1 : π t = x
            · rw [ite_t h1, ite_t (by rw [← h1, (hbij t ht).2.2.2])]
            · rw [ite_f h1, ite_f (fun e => h1 (by rw [e, (hbij x hxlt).2.2.1]))]
          rw [hc, sumR_single r (πInv x) (g x) (hbij x hxlt).2.1]
        have hgr := ihL hnd (fun y hy => hbd y (List.mem_cons_of_mem x hy)) gr (fun t ht htn => by
          dsimp only [gr]; by_cases htx : t = x
          · rw [ite_t htx]
          · rw [ite_f htx]; exact hg t ht (fun hm => by cases hm with | head => exact htx rfl | tail _ h' => exact htn h'))
        rw [hL1, hR1, hgx1, sumR_single r x (g x) hxlt, hgr]
    have hndR : ∀ k : Nat, ListNodup (List.range k) := by
      intro k; induction k with
      | zero => trivial
      | succ k' ihk =>
        rw [List.range_succ]
        have happ : ∀ (l : List Nat) (a : Nat), ListNodup l → (∀ y, y ∈ l → y ≠ a) → ListNodup (l ++ [a]) := by
          intro l; induction l with
          | nil => intro _ _ _; simp [ListNodup]
          | cons u us ihu =>
            intro a ⟨h1, h2⟩ h3
            refine ⟨fun y hy => ?_, ihu a h2 (fun y hy => h3 y (List.mem_cons_of_mem u hy))⟩
            cases List.mem_append.mp hy with
            | inl hm => exact h1 y hm
            | inr hm =>
              have hya : y = a := by simpa using hm
              subst hya; exact Ne.symm (h3 u (List.mem_cons_self ..))
        exact happ _ k' ihk (fun y hy => by have := List.mem_range.mp hy; omega)
    exact hgen (List.range r) (hndR r) (fun x hx => List.mem_range.mp hx) f
      (fun t ht hnot => absurd (List.mem_range.mpr ht) hnot)
  -- `S := S1 ++ S2 ++ S3` (`S.length ≤ 3 * m`)
  let S := S1 ++ S2 ++ S3
  have hS_len : S.length ≤ 3 * m := by
    dsimp only [S]; simp only [List.length_append]; omega
  let keepLow := (List.range N).filter (fun j => decide (j ∈ S))
  have hndN : ListNodup (List.range N) := by
    have hndR : ∀ k : Nat, ListNodup (List.range k) := by
      intro k; induction k with
      | zero => trivial
      | succ k' ihk =>
        rw [List.range_succ]
        have happ : ∀ (l : List Nat) (a : Nat), ListNodup l → (∀ y, y ∈ l → y ≠ a) → ListNodup (l ++ [a]) := by
          intro l; induction l with
          | nil => intro _ _ _; simp [ListNodup]
          | cons u us ihu =>
            intro a ⟨h1, h2⟩ h3
            refine ⟨fun y hy => ?_, ihu a h2 (fun y hy => h3 y (List.mem_cons_of_mem u hy))⟩
            cases List.mem_append.mp hy with
            | inl hm => exact h1 y hm
            | inr hm =>
              have hya : y = a := by simpa using hm
              subst hya; exact Ne.symm (h3 u (List.mem_cons_self ..))
        exact happ _ k' ihk (fun y hy => by have := List.mem_range.mp hy; omega)
    exact hndR N
  have hkeepLow_len : keepLow.length ≤ 3 * m :=
    Nat.le_trans (filter_mem_length_le (List.range N) S hndN) hS_len
  let keepList := keepLow ++ (List.range (r - N)).map (fun t => N + t)
  let q := keepList.length
  have hq_le : q ≤ 3 * m + (r - N) := by
    dsimp only [q, keepList]; simp only [List.length_append, List.length_map, List.length_range]; omega
  -- Helper: Any `X = ∑ c_i φ13(B_i)` whose coefficients vanish outside `S` is computed by the `q` kept products!
  let coef (X : Nat → Nat → K3) (t : Nat) : K3 :=
    sumR N (fun a => X (a / m) (a % m) * φ13.toFun (U (π (keepList.getD t 0)) a))
  let P_big (c t : Nat) : K3 := φ13.toFun (W (π (keepList.getD t 0)) c)
  let Q_big (t b : Nat) : K3 := φ13.toFun (V (π (keepList.getD t 0)) b)
  have hslice_keep : ∀ (cvec : Nat → K3), (∀ j, j ∉ S → cvec j = 0) →
      let X := fun a b => sumR N (fun i => cvec i * φ13.toFun (Bmat i a b))
      ∀ c b, c < N → b < N →
        leftMulMat m X c b = sumR q (fun t => coef X t * P_big c t * Q_big t b) := by
    intro cvec hcvec X c b hc hb
    -- Step A: `leftMulMat m X c b = sumR r (fun j => coef_raw X j * W (π j) c * V (π j) b)`
    let rawTerm (j : Nat) : K3 :=
      (sumR N (fun a => X (a / m) (a % m) * φ13.toFun (U (π j) a))) *
      φ13.toFun (W (π j) c) * φ13.toFun (V (π j) b)
    have hfull_r : leftMulMat m X c b = sumR r rawTerm := by
      rw [leftMulMat_eq_tensor_slice m X c b hc hb]
      have hint_eq : ∀ a, a < N → intToR (R := K3) (matMulTensor m a b c) =
          sumR r (fun s => φ13.toFun (U s a) * φ13.toFun (V s b) * φ13.toFun (W s c)) := by
        intro a ha
        have hlift : intToR (R := K3) (matMulTensor m a b c) = φ13.toFun (intToR (R := F) (matMulTensor m a b c)) := by
          unfold matMulTensor; dsimp only; split <;> simp [intToR_one, intToR_zero, φ13.map_one, φ13.map_zero]
        have hTabc : intToR (R := F) (matMulTensor m a b c) = sumR r (fun s => U s a * V s b * W s c) :=
          hT a b c ha hb hc
        rw [hlift, hTabc, φ13.map_sumR]
        exact sumR_congr (fun s _ => by rw [φ13.map_mul, φ13.map_mul])
      calc sumR N (fun a => X (a / m) (a % m) * intToR (R := K3) (matMulTensor m a b c))
          = sumR N (fun a => X (a / m) (a % m) * sumR r (fun s => φ13.toFun (U s a) * φ13.toFun (V s b) * φ13.toFun (W s c))) :=
            sumR_congr (fun a ha => by rw [hint_eq a ha])
        _ = sumR N (fun a => sumR r (fun s => X (a / m) (a % m) * (φ13.toFun (U s a) * φ13.toFun (V s b) * φ13.toFun (W s c)))) :=
            sumR_congr (fun a _ => sumR_mul_left r _ _)
        _ = sumR r (fun s => sumR N (fun a => X (a / m) (a % m) * (φ13.toFun (U s a) * φ13.toFun (V s b) * φ13.toFun (W s c)))) :=
            sumR_swap N r _
        _ = sumR r (fun s => (sumR N (fun a => X (a / m) (a % m) * φ13.toFun (U s a))) * φ13.toFun (W s c) * φ13.toFun (V s b)) := by
            apply sumR_congr; intro s _
            rw [sumR_mul_right, sumR_mul_right]
            apply sumR_congr; intro a _
            rw [CommRing.mul_assoc (X (a / m) (a % m)), CommRing.mul_assoc (φ13.toFun (U s a)),
                CommRing.mul_comm (φ13.toFun (V s b)) (φ13.toFun (W s c)),
                ← CommRing.mul_assoc (φ13.toFun (U s a)), ← CommRing.mul_assoc (X (a / m) (a % m)),
                ← CommRing.mul_assoc]
        _ = sumR r rawTerm := (hsum_perm_r _).symm
    -- Step B: Split `sumR r rawTerm = sumR N rawTerm + sumR (r - N) (rawTerm (N + ·))` and drop `j < N, j ∉ S`!
    rw [hfull_r]
    have hr_split : r = N + (r - N) := by omega
    have hLsp : sumR r rawTerm = sumR N rawTerm + sumR (r - N) (fun t => rawTerm (N + t)) := by
      have h1 : sumR r rawTerm = sumR (N + (r - N)) rawTerm := congrArg (fun k => sumR k rawTerm) hr_split
      rw [h1, sumR_split N (r - N)]
    rw [hLsp]
    have hlow : sumR N rawTerm = sumR keepLow.length (fun t => rawTerm (keepLow.getD t 0)) := by
      have hvan : ∀ j, j < N → j ∉ S → rawTerm j = 0 := by
        intro j hj hjnot
        dsimp only [rawTerm, X]
        rw [hdual φ13 cvec j hj, hcvec j hjnot, zero_mul, zero_mul]
      have hfilt : ∀ (L : List Nat), (∀ j, j ∈ L → j < N) →
          sumList (L.map rawTerm) = sumList ((L.filter (fun j => decide (j ∈ S))).map rawTerm) := by
        intro L
        induction L with
        | nil => intro _; rfl
        | cons x xs ih =>
          intro hbd
          simp only [List.map_cons, sumList, List.filter_cons]
          by_cases hx : x ∈ S
          · simp only [hx, decide_true, ↓reduceIte, List.map_cons, sumList]
            rw [ih (fun y hy => hbd y (List.mem_cons_of_mem x hy))]
          · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
            rw [hvan x (hbd x (List.mem_cons_self ..)) hx, CommRing.zero_add]
            exact ih (fun y hy => hbd y (List.mem_cons_of_mem x hy))
      have hlist_to_sumR : ∀ (L : List Nat), sumList (L.map rawTerm) = sumR L.length (fun t => rawTerm (L.getD t 0)) := by
        intro L
        have hrev : ∀ (M : List Nat), sumList (M.map rawTerm) = sumR M.length (fun t => rawTerm (M.getD t 0)) := by
          intro M; induction M with
          | nil => rfl
          | cons a as iha =>
            simp only [List.map_cons, sumList, List.length_cons]
            have hsp : sumR (1 + as.length) (fun t => rawTerm ((a :: as).getD t 0)) =
                sumR 1 (fun t => rawTerm ((a :: as).getD t 0)) +
                sumR as.length (fun t => rawTerm ((a :: as).getD (1 + t) 0)) := sumR_split 1 as.length _
            have h1 : 1 + as.length = as.length + 1 := Nat.add_comm 1 _
            rw [h1] at hsp; rw [hsp]
            simp only [sumR, CommRing.zero_add, List.getD_cons_zero]
            rw [iha]
            congr 1
            exact sumR_congr (fun t _ => by rw [Nat.add_comm 1 t]; rfl)
        exact hrev L
      rw [← sumList_map_range N rawTerm, hfilt (List.range N) (fun j hj => List.mem_range.mp hj), hlist_to_sumR]
    rw [hlow]
    -- Recombine `sumR keepLow.length + sumR (r - N)` into `sumR q` over `keepList`!
    have hq_eq : q = keepLow.length + (r - N) := by
      dsimp only [q, keepList]; simp only [List.length_append, List.length_map, List.length_range]
    rw [hq_eq, sumR_split keepLow.length (r - N)]
    have hget_app : ∀ (L1 L2 : List Nat) (t : Nat),
        (L1 ++ L2).getD t 0 = if t < L1.length then L1.getD t 0 else L2.getD (t - L1.length) 0 := by
      intro L1 L2 t
      induction L1 generalizing t with
      | nil => simp
      | cons a as ih =>
        cases t with
        | zero => simp
        | succ t' =>
          simp only [List.cons_append, List.getD_cons_succ, List.length_cons, ih t']
          by_cases h1 : t' < as.length
          · rw [ite_t h1, ite_t (Nat.succ_lt_succ h1)]
          · have h2 : ¬ (t' + 1 < as.length + 1) := by omega
            have hsub : t' + 1 - (as.length + 1) = t' - as.length := by omega
            rw [ite_f h1, ite_f h2, hsub]
    congr 1
    · apply sumR_congr; intro t ht
      dsimp only [rawTerm, coef, P_big, Q_big, keepList]
      rw [hget_app, ite_t ht]
    · apply sumR_congr; intro t ht
      dsimp only [rawTerm, coef, P_big, Q_big, keepList]
      have hnot : ¬ (keepLow.length + t < keepLow.length) := by omega
      have hsub : keepLow.length + t - keepLow.length = t := by omega
      rw [hget_app, ite_f hnot, hsub]
      have hget_map : ∀ (k u : Nat), u < k → ((List.range k).map (fun v => N + v)).getD u 0 = N + u := by
        intro k; induction k with
        | zero => intro u hu; omega
        | succ k' ihk =>
          intro u hu
          rw [List.range_succ, List.map_append, List.map_singleton, hget_app]
          simp only [List.length_map, List.length_range]
          by_cases hlt : u < k'
          · rw [ite_t hlt]; exact ihk u hlt
          · have heq : u = k' := by omega
            subst heq
            rw [ite_f hlt, Nat.sub_self]; rfl
      rw [hget_map (r - N) t ht]
  -- Apply `strassen_commutator_bound`!
  have hA0_rep := hslice_keep (fun i => φ23.toFun (z1 i))
    (fun j hj => by rw [hS1_sup j (fun hm => hj (by dsimp only [S]; simp [hm])), φ23.map_zero])
  have hA1_rep := hslice_keep (fun i => φ3.toFun (x2 i))
    (fun j hj => by rw [hS2_sup j (fun hm => hj (by dsimp only [S]; simp [hm])), φ3.map_zero])
  have hA2_rep := hslice_keep y3
    (fun j hj => hS3_sup j (fun hm => hj (by dsimp only [S]; simp [hm])))
  obtain ⟨hNq, hStras⟩ := strassen_commutator_bound N q (coef M0) (coef M1) (coef M2m)
    P_big Q_big A0 A1 A2 A0inv Cinv hA0_rep hA1_rep hA2_rep hInvA0 hInvA_comm
  -- `N ≤ 2 * (q - N)` and `N ≤ q` and `q ≤ 3 * m + (r - N)` and `N ≤ r` ⇒ `5 * m * m - 6 * m ≤ 2 * r`!
  have h5 : 5 * m * m = 5 * N := Nat.mul_assoc 5 m m
  rw [h5]
  omega

/-- **Theorem T3m (Bläser's `5/2 m² - 3m` Matrix Multiplication Lower Bound Over EVERY Field `F`):**
    Over **EVERY `SimpleField F` (including `F_2`!)**:
    1. **Bläser's (1999) `5/2 m² - 3m` Lower Bound (`∀ m ≥ 1, ∀ F`):**
       `5 * m * m - 6 * m ≤ 2 * r` whenever `rank_F(⟨m, m, m⟩) ≤ r`.
    2. **Strict Domination Over `2 m² - 1` (`∀ m ≥ 6`):**
       Strictly surpasses BOTH `T3i`'s `2 m² - m` AND Brockett–Dobkin / Alder–Strassen's `2 m² - 1`
       for every `m ≥ 6` (e.g. `m = 6 → r ≥ 72 > 71`; `m = 10 → r ≥ 220 > 199`).
    3. **Tightened Strassen–Bläser Power-of-2 Sandwich (`∀ k : Nat, ∀ F`):**
       `5 * 4^k - 6 * 2^k ≤ 2 * rank_F(⟨2^k, 2^k, 2^k⟩) ≤ 2 * 7^k`. -/
theorem t3m_blaser_five_halves_matmul_bound :
    (∀ (F : Type) [SimpleField F] (m r : Nat),
      1 ≤ m →
      HasTensorRankAtMost (m * m) (m * m) (m * m) r
        (fun a b c => intToR (R := F) (matMulTensor m a b c)) →
      5 * m * m - 6 * m ≤ 2 * r) ∧
    (∀ (m : Nat), 6 ≤ m → 2 * (2 * m * m - 1) < 5 * m * m - 6 * m) ∧
    (∀ (F : Type) [SimpleField F] (k : Nat),
      HasTensorRankAtMost (2 ^ k * 2 ^ k) (2 ^ k * 2 ^ k) (2 ^ k * 2 ^ k) (7 ^ k)
        (fun a b c => intToR (R := F) (matMulTensor (2 ^ k) a b c)) ∧
      ∀ r : Nat,
        HasTensorRankAtMost (2 ^ k * 2 ^ k) (2 ^ k * 2 ^ k) (2 ^ k * 2 ^ k) r
          (fun a b c => intToR (R := F) (matMulTensor (2 ^ k) a b c)) →
        5 * 4 ^ k - 6 * 2 ^ k ≤ 2 * r) := by
  have hmain : ∀ (F : Type) [SimpleField F] (m r : Nat),
      1 ≤ m →
      HasTensorRankAtMost (m * m) (m * m) (m * m) r
        (fun a b c => intToR (R := F) (matMulTensor m a b c)) →
      5 * m * m - 6 * m ≤ 2 * r := by
    intro F _ m r hm hr
    by_cases hm1 : m = 1
    · subst hm1; omega
    · exact blaser_matmul_rank_ge_five_halves F m r (by omega) hr
  refine ⟨hmain, ?_, ?_⟩
  · intro m hm
    have h6m : 6 * m ≤ m * m := Nat.mul_le_mul_right m hm
    have hm2 : 36 ≤ m * m := Nat.mul_le_mul hm hm
    have hsub : 5 * m * m = 5 * (m * m) := Nat.mul_assoc 5 m m
    have hsub2 : 2 * m * m = 2 * (m * m) := Nat.mul_assoc 2 m m
    rw [hsub, hsub2]
    omega
  · intro F _ k
    refine ⟨strassen_power_upper_bound F k, fun r hr => ?_⟩
    have hpos : 1 ≤ 2 ^ k := Nat.pow_pos (by decide)
    have hbd := hmain F (2 ^ k) r hpos hr
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
end TriadFrontier.BlaserLowerBound
