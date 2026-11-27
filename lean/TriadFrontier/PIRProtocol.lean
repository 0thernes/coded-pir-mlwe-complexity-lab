module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore
public import TriadFrontier.KoszulTensor

/-!
# Universal Zero-Error Decoding and Exact `T`-Collusion Privacy Bijection for Linear MDS-Coded PIR

Zero-Mathlib Lean 4.35.0 formalization over **ANY `SimpleField F`** of the 2-file, `N`-server,
`K`-MDS-coded linear flag-private PIR protocol (instantiated at `(M=2, N=6, K=3, T=3, F=F_101)`
with exact zero-error rate `10/17 = 60/102 > 4/7` in `data/f101_t3_k3_e6_witness.json`):

1. **Exact Zero-Error Decoding (`pir_zero_error_decoding_exact`):**
   Given ANY database `(W_1, W_2)` (`K` stripes in `F^D`, `L = K * D` symbols per file), ANY
   MDS storage coefficients `g_{n,k}`, ANY invertible randomness tuple `(S_1, S_2, R_1, R_2, H_1, H_2, L_1, L_2)`,
   an exact interference-cancellation matrix `Cancel` (`Cancel · M_pure = M_mixed`), and a left inverse
   `DecInv` (`DecInv · M_des = I_{K*D}`), the explicit linear decoder recovers **BOTH** `W_1` (for `θ = 1`)
   and `W_2` (for `θ = 2`) with **ZERO decoding error**.

2. **Exact Information-Theoretic `T`-Collusion Privacy Bijection (`pir_exact_t_privacy_bijection`):**
   For ANY colluding server subset `I` admitting an ambient isomorphism `M_I ∈ GL_D(F)` and per-server
   block automorphisms `α_n ∈ GL_y(F)`, `γ_n ∈ GL_z(F)`, `β_n ∈ F^{z × y}` satisfying
     `P_n M_I = α_n Q_n`   and   `C_n M_I = γ_n D_n + β_n Q_n`   for all `n ∈ I`,
   the explicit randomness map `Ψ_I` is a **two-sided bijection** on valid invertible randomness tuples
   that maps the `θ = 1` query tuple on `I` **entry-for-entry** onto the `θ = 2` query tuple on `I`
   (yielding zero information leakage `I(θ; Q_I) = 0` under uniform randomness over any finite field `F`).
-/

namespace TriadFrontier.PIRProtocol

open TriadFrontier.AlgebraCore
open TriadFrontier.KoszulTensor

@[expose] public section

-- ============================================================================
-- Section 1: Finite Matrix Algebra Helpers over ANY `SimpleField F`
-- ============================================================================

/-- Matrix-vector product `(A v)_i = ∑_{j < n} A i j * v j`. -/
def matVec {R : Type} [CommRing R] (n : Nat) (A : Nat → Nat → R) (v : Nat → R) (i : Nat) : R :=
  sumR n (fun j => A i j * v j)

/-- Pointwise matrix addition and subtraction. -/
def matAdd {R : Type} [CommRing R] (A B : Nat → Nat → R) (i j : Nat) : R := A i j + B i j
def matSub {R : Type} [CommRing R] (A B : Nat → Nat → R) (i j : Nat) : R := A i j - B i j

/-- Matrix equality on `m × n`. -/
def MatEq {R : Type} (m n : Nat) (A B : Nat → Nat → R) : Prop :=
  ∀ i j, i < m → j < n → A i j = B i j

/-- Two-sided matrix inverse witness on `d × d`. -/
def IsMatInv {R : Type} [CommRing R] (d : Nat) (A Ainv : Nat → Nat → R) : Prop :=
  MatEq d d (matMulF d A Ainv) matIdF ∧ MatEq d d (matMulF d Ainv A) matIdF

theorem matMulF_congr {R : Type} [CommRing R] {k : Nat} {A1 A2 B1 B2 : Nat → Nat → R}
    {i j : Nat}
    (hA : ∀ t, t < k → A1 i t = A2 i t)
    (hB : ∀ t, t < k → B1 t j = B2 t j) :
    matMulF k A1 B1 i j = matMulF k A2 B2 i j := by
  apply sumR_congr
  intro t ht
  rw [hA t ht, hB t ht]

theorem matMulF_assoc {R : Type} [CommRing R] (k1 k2 : Nat)
    (A B C : Nat → Nat → R) (i j : Nat) :
    matMulF k2 (matMulF k1 A B) C i j = matMulF k1 A (matMulF k2 B C) i j := by
  unfold matMulF
  induction k1 with
  | zero =>
    simp only [sumR]
    rw [sumR_congr (fun _ _ => zero_mul _), sumR_zero_fn]
  | succ m ih =>
    simp only [sumR]
    rw [← ih, sumR_mul_left, ← sumR_add]
    apply sumR_congr
    intro t _
    rw [right_distrib, CommRing.mul_assoc]

theorem matMulF_id_left {R : Type} [CommRing R] (k : Nat) (A : Nat → Nat → R)
    {i j : Nat} (hi : i < k) :
    matMulF k matIdF A i j = A i j := by
  unfold matMulF
  have h : ∀ n : Nat, sumR n (fun t => matIdF (R := R) i t * A t j) = if i < n then A i j else 0 := by
    intro n
    induction n with
    | zero => simp [sumR]
    | succ m ih =>
      simp only [sumR, ih]
      by_cases him : i = m
      · subst him
        have h1 : ¬ (i < i) := Nat.lt_irrefl i
        have h2 : i < i + 1 := Nat.lt_succ_self i
        simp only [h1, h2, ↓reduceIte, matIdF, CommRing.zero_add, CommRing.one_mul]
      · have hiff : (i < m + 1) ↔ (i < m) := by omega
        have hid : matIdF (R := R) i m = 0 := by simp [matIdF, him]
        rw [hid, zero_mul, add_zero]
        simp only [hiff]
  rw [h k]; simp [hi]

theorem matMulF_id_right {R : Type} [CommRing R] (k : Nat) (A : Nat → Nat → R)
    {i j : Nat} (hj : j < k) :
    matMulF k A matIdF i j = A i j := by
  unfold matMulF
  have h : ∀ n : Nat, sumR n (fun t => A i t * matIdF (R := R) t j) = if j < n then A i j else 0 := by
    intro n
    induction n with
    | zero => simp [sumR]
    | succ m ih =>
      simp only [sumR, ih]
      by_cases hmj : m = j
      · subst hmj
        have h1 : ¬ (m < m) := Nat.lt_irrefl m
        have h2 : m < m + 1 := Nat.lt_succ_self m
        simp only [h1, h2, ↓reduceIte, matIdF, CommRing.zero_add, mul_one]
      · have hiff : (j < m + 1) ↔ (j < m) := by omega
        have hid : matIdF (R := R) m j = 0 := by simp [matIdF, hmj]
        rw [hid, mul_zero, add_zero]
        simp only [hiff]
  rw [h k]; simp [hj]

theorem matMulF_add_left {R : Type} [CommRing R] (k : Nat) (A B C : Nat → Nat → R) (i j : Nat) :
    matMulF k (matAdd A B) C i j = matMulF k A C i j + matMulF k B C i j := by
  unfold matMulF matAdd
  rw [← sumR_add]
  apply sumR_congr; intro t _; exact right_distrib ..

theorem matMulF_add_right {R : Type} [CommRing R] (k : Nat) (A B C : Nat → Nat → R) (i j : Nat) :
    matMulF k A (matAdd B C) i j = matMulF k A B i j + matMulF k A C i j := by
  unfold matMulF matAdd
  rw [← sumR_add]
  apply sumR_congr; intro t _; exact CommRing.left_distrib ..

theorem matMulF_sub_left {R : Type} [CommRing R] (k : Nat) (A B C : Nat → Nat → R) (i j : Nat) :
    matMulF k (matSub A B) C i j = matMulF k A C i j - matMulF k B C i j := by
  unfold matMulF matSub
  rw [CommRing.sub_eq, ← sumR_neg, ← sumR_add]
  apply sumR_congr; intro t _
  rw [CommRing.sub_eq, right_distrib, neg_mul]

theorem isMatInv_mul {R : Type} [CommRing R] {d : Nat} {A Ainv B Binv : Nat → Nat → R}
    (hA : IsMatInv d A Ainv) (hB : IsMatInv d B Binv) :
    IsMatInv d (matMulF d A B) (matMulF d Binv Ainv) := by
  constructor
  · intro i j hi hj
    rw [matMulF_assoc]
    rw [matMulF_congr (fun _ _ => rfl) (fun t ht => by
      rw [← matMulF_assoc d d B Binv Ainv,
          matMulF_congr (fun u hu => hB.1 t u ht hu) (fun _ _ => rfl),
          matMulF_id_left d Ainv ht])]
    exact hA.1 i j hi hj
  · intro i j hi hj
    rw [matMulF_assoc]
    rw [matMulF_congr (fun _ _ => rfl) (fun t ht => by
      rw [← matMulF_assoc d d Ainv A B,
          matMulF_congr (fun u hu => hA.2 t u ht hu) (fun _ _ => rfl),
          matMulF_id_left d B ht])]
    exact hB.2 i j hi hj

theorem matVec_mul {R : Type} [CommRing R] (k1 k2 : Nat)
    (A B : Nat → Nat → R) (v : Nat → R) (i : Nat) :
    matVec k2 (matMulF k1 A B) v i = matVec k1 A (matVec k2 B v) i := by
  unfold matVec matMulF
  induction k1 with
  | zero =>
    simp only [sumR]
    rw [sumR_congr (fun _ _ => zero_mul _), sumR_zero_fn]
  | succ m ih =>
    simp only [sumR]
    rw [← ih, sumR_mul_left, ← sumR_add]
    apply sumR_congr; intro t _; rw [right_distrib, CommRing.mul_assoc]

theorem matVec_add {R : Type} [CommRing R] (k : Nat) (A B : Nat → Nat → R) (v : Nat → R) (i : Nat) :
    matVec k (matAdd A B) v i = matVec k A v i + matVec k B v i := by
  unfold matVec matAdd
  rw [← sumR_add]
  apply sumR_congr; intro t _; exact right_distrib ..

theorem matVec_vec_add {R : Type} [CommRing R] (k : Nat) (A : Nat → Nat → R) (u v : Nat → R) (i : Nat) :
    matVec k A (fun t => u t + v t) i = matVec k A u i + matVec k A v i := by
  unfold matVec
  rw [← sumR_add]
  apply sumR_congr; intro t _; exact CommRing.left_distrib ..

theorem matVec_id {R : Type} [CommRing R] (k : Nat) (v : Nat → R) {i : Nat} (hi : i < k) :
    matVec k matIdF v i = v i := by
  have h := matMulF_id_left k (fun t _ => v t) (j := 0) hi
  exact h

theorem matVec_scale_sum {R : Type} [CommRing R] (D K : Nat)
    (A : Nat → Nat → R) (g : Nat → R) (W : Nat → Nat → R) (i : Nat) :
    matVec D A (fun d => sumR K (fun k => g k * W k d)) i =
    sumR K (fun k => g k * matVec D A (W k) i) := by
  induction K with
  | zero =>
    simp only [sumR, matVec]
    rw [sumR_congr (fun _ _ => mul_zero _), sumR_zero_fn]
  | succ m ih =>
    simp only [sumR]
    rw [matVec_vec_add, ih]
    congr 1
    unfold matVec
    rw [sumR_mul_left]
    apply sumR_congr; intro d _
    rw [← CommRing.mul_assoc, CommRing.mul_comm (A i d) (g m), CommRing.mul_assoc]

-- ============================================================================
-- Section 2: Linear MDS-Coded Flag-Private PIR Scheme & Zero-Error Decoding
-- ============================================================================

/-- Public linear PIR query-block scheme `(P_n, Q_n, C_n, D_n)` and MDS storage weights `g_{n,k}`. -/
structure PIRScheme (F : Type) where
  N : Nat
  K : Nat
  D : Nat
  y : Nat
  z : Nat
  g : Nat → Nat → F
  P : Nat → Nat → Nat → F
  Q : Nat → Nat → Nat → F
  C : Nat → Nat → Nat → F
  Dblk : Nat → Nat → Nat → F

/-- User's invertible randomness tuple `(S_1, S_2, R_1, R_2, H_1, H_2, L_1, L_2)` with explicit inverses. -/
structure PIRRand (F : Type) where
  S1    : Nat → Nat → F
  S1inv : Nat → Nat → F
  S2    : Nat → Nat → F
  S2inv : Nat → Nat → F
  R1    : Nat → Nat → Nat → F
  R1inv : Nat → Nat → Nat → F
  R2    : Nat → Nat → Nat → F
  R2inv : Nat → Nat → Nat → F
  H1    : Nat → Nat → Nat → F
  H1inv : Nat → Nat → Nat → F
  H2    : Nat → Nat → Nat → F
  H2inv : Nat → Nat → Nat → F
  L1    : Nat → Nat → Nat → F
  L2    : Nat → Nat → Nat → F

/-- Invertibility validity predicate on `PIRRand`. -/
def ValidRand {F : Type} [CommRing F] (sc : PIRScheme F) (r : PIRRand F) : Prop :=
  IsMatInv sc.D r.S1 r.S1inv ∧
  IsMatInv sc.D r.S2 r.S2inv ∧
  (∀ n, n < sc.N → IsMatInv sc.y (r.R1 n) (r.R1inv n)) ∧
  (∀ n, n < sc.N → IsMatInv sc.y (r.R2 n) (r.R2inv n)) ∧
  (∀ n, n < sc.N → IsMatInv sc.z (r.H1 n) (r.H1inv n)) ∧
  (∀ n, n < sc.N → IsMatInv sc.z (r.H2 n) (r.H2inv n))

/-- Server `n`'s coded storage vector for file `W : Nat → Nat → F` (`K` stripes in `F^D`):
    `Y_n(W)_d = ∑_{k < K} g_{n,k} W_{k,d}`. -/
def serverStorage {F : Type} [CommRing F] (sc : PIRScheme F) (W : Nat → Nat → F) (n d : Nat) : F :=
  sumR sc.K (fun k => sc.g n k * W k d)

/-- Query blocks sent to server `n` for desired file `θ ∈ {false (File 1), true (File 2)}`:
    Block 1 (`y × D` on File 1), Block 2 (`y × D` on File 2), Block 3 (`z × D` on File 1 & File 2). -/
def qBlk1 {F : Type} [CommRing F] (sc : PIRScheme F) (θ : Bool) (r : PIRRand F) (n : Nat) : Nat → Nat → F :=
  let B := if θ then sc.Q n else sc.P n
  matMulF sc.D (matMulF sc.y (r.R1 n) B) r.S1

def qBlk2 {F : Type} [CommRing F] (sc : PIRScheme F) (θ : Bool) (r : PIRRand F) (n : Nat) : Nat → Nat → F :=
  let B := if θ then sc.P n else sc.Q n
  matMulF sc.D (matMulF sc.y (r.R2 n) B) r.S2

def qBlk3File1 {F : Type} [CommRing F] (sc : PIRScheme F) (θ : Bool) (r : PIRRand F) (n : Nat) : Nat → Nat → F :=
  let C' := if θ then sc.Dblk n else sc.C n
  let P' := if θ then sc.Q n else sc.P n
  matMulF sc.D (matAdd (matMulF sc.z (r.H1 n) C') (matMulF sc.y (r.L1 n) P')) r.S1

def qBlk3File2 {F : Type} [CommRing F] (sc : PIRScheme F) (θ : Bool) (r : PIRRand F) (n : Nat) : Nat → Nat → F :=
  let D' := if θ then sc.C n else sc.Dblk n
  let Q' := if θ then sc.P n else sc.Q n
  matMulF sc.D (matAdd (matMulF sc.z (r.H2 n) D') (matMulF sc.y (r.L2 n) Q')) r.S2

/-- Server `n`'s 3 linear answer blocks (`A1 ∈ F^y`, `A2 ∈ F^y`, `A3 ∈ F^z`). -/
def ansBlk1 {F : Type} [CommRing F] (sc : PIRScheme F) (θ : Bool) (r : PIRRand F)
    (W1 : Nat → Nat → F) (n : Nat) : Nat → F :=
  matVec sc.D (qBlk1 sc θ r n) (serverStorage sc W1 n)

def ansBlk2 {F : Type} [CommRing F] (sc : PIRScheme F) (θ : Bool) (r : PIRRand F)
    (W2 : Nat → Nat → F) (n : Nat) : Nat → F :=
  matVec sc.D (qBlk2 sc θ r n) (serverStorage sc W2 n)

def ansBlk3 {F : Type} [CommRing F] (sc : PIRScheme F) (θ : Bool) (r : PIRRand F)
    (W1 W2 : Nat → Nat → F) (n : Nat) : Nat → F :=
  fun i => matVec sc.D (qBlk3File1 sc θ r n) (serverStorage sc W1 n) i +
           matVec sc.D (qBlk3File2 sc θ r n) (serverStorage sc W2 n) i

/-- Flattened linear equation index for `N` servers of `y` pure interference equations (`row = n*y + i`),
    evaluated against `K` stripes of dimension `D` (`col = k*D + d`). -/
def pureIntMat {F : Type} [CommRing F] (sc : PIRScheme F) (row col : Nat) : F :=
  let n := row / sc.y
  let i := row % sc.y
  let k := col / sc.D
  let d := col % sc.D
  sc.g n k * sc.Q n i d

/-- Flattened mixed interference matrix (`row = n*z + i`, `col = k*D + d`). -/
def mixedIntMat {F : Type} [CommRing F] (sc : PIRScheme F) (row col : Nat) : F :=
  let n := row / sc.z
  let i := row % sc.z
  let k := col / sc.D
  let d := col % sc.D
  sc.g n k * sc.Dblk n i d

/-- Flattened desired decoding matrix (`N * (y + z)` rows × `K * D` cols):
    server `n`, local row `t < y` uses `P_n`, local row `y + t` uses `C_n`. -/
def desiredMat {F : Type} [CommRing F] (sc : PIRScheme F) (row col : Nat) : F :=
  let n := row / (sc.y + sc.z)
  let t := row % (sc.y + sc.z)
  let k := col / sc.D
  let d := col % sc.D
  if t < sc.y then sc.g n k * sc.P n t d
  else sc.g n k * sc.C n (t - sc.y) d

/-- Explicit linear user decoder given interference-cancellation matrix `Cancel : (N*z) × (N*y)`
    and desired left-inverse `DecInv : (K*D) × (N*(y+z))`. -/
def pirDecode {F : Type} [CommRing F] (sc : PIRScheme F)
    (Cancel DecInv : Nat → Nat → F)
    (θ : Bool) (r : PIRRand F)
    (A1 A2 A3 : Nat → Nat → F) (k d : Nat) : F :=
  -- Step 1: unscramble Block 1 (`u_n`) and Block 2 (`v_n`)
  let u : Nat → Nat → F := fun n => matVec sc.y (r.R1inv n) (A1 n)
  let v : Nat → Nat → F := fun n => matVec sc.y (r.R2inv n) (A2 n)
  -- Step 2: flatten pure interference vector (`v` for File 1, `u` for File 2)
  let intVec : Nat → F := fun idx =>
    let n := idx / sc.y
    let i := idx % sc.y
    if θ then u n i else v n i
  -- Step 3: reconstruct exact mixed interference `D_n Y_int` via `Cancel`
  let intMixed : Nat → Nat → F := fun n i =>
    matVec (sc.N * sc.y) Cancel intVec (n * sc.z + i)
  -- Step 4: strip shifts `L_1 u_n + L_2 v_n` and cancelled mixed interference, then invert `H`
  let w : Nat → Nat → F := fun n =>
    let stripped : Nat → F := fun i =>
      A3 n i - matVec sc.y (r.L1 n) (u n) i - matVec sc.y (r.L2 n) (v n) i -
        if θ then matVec sc.z (r.H1 n) (intMixed n) i
        else matVec sc.z (r.H2 n) (intMixed n) i
    if θ then matVec sc.z (r.H2inv n) stripped
    else matVec sc.z (r.H1inv n) stripped
  -- Step 5: stack desired observations (`u_n, w_n` for File 1; `v_n, w_n` for File 2)
  let desVec : Nat → F := fun row =>
    let n := row / (sc.y + sc.z)
    let t := row % (sc.y + sc.z)
    if t < sc.y then (if θ then v n t else u n t)
    else w n (t - sc.y)
  -- Step 6: invert `desiredMat` to recover scrambled stripes `S_θ W_θ`, then multiply by `S_θ^{-1}`!
  let scrambled : Nat → F := fun d' =>
    matVec (sc.N * (sc.y + sc.z)) DecInv desVec (k * sc.D + d')
  if θ then matVec sc.D r.S2inv scrambled d
  else matVec sc.D r.S1inv scrambled d

theorem sumR_prod_reindex {R : Type} [CommRing R] (A B : Nat) (hB : 0 < B) (f : Nat → Nat → R) :
    sumR (A * B) (fun idx => f (idx / B) (idx % B)) =
    sumR A (fun a => sumR B (fun b => f a b)) := by
  induction A with
  | zero => simp [sumR]
  | succ m ih =>
    rw [Nat.succ_mul, sumR_split (m * B) B, ih, sumR]
    congr 1
    apply sumR_congr
    intro b hb
    have hdiv : (m * B + b) / B = m := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hb, Nat.zero_add]
    have hmod : (m * B + b) % B = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    rw [hdiv, hmod]

/-- **Theorem 1 (`pir_zero_error_decoding_exact` over ANY `SimpleField F`):**
    If `Cancel · pureIntMat = mixedIntMat` and `DecInv · desiredMat = I_{K*D}`, then for EVERY
    database `(W1, W2)`, EVERY valid invertible randomness `r`, and BOTH desired files `θ ∈ {false, true}`,
    `pirDecode` recovers the exact desired file (`W1` if `θ = false`, `W2` if `θ = true`) with ZERO error! -/
theorem pir_zero_error_decoding_exact {F : Type} [SimpleField F] (sc : PIRScheme F)
    (hy : 0 < sc.y) (hz : 0 < sc.z) (hD : 0 < sc.D)
    (Cancel DecInv : Nat → Nat → F)
    (hCancel : MatEq (sc.N * sc.z) (sc.K * sc.D) (matMulF (sc.N * sc.y) Cancel (pureIntMat sc)) (mixedIntMat sc))
    (hDec : MatEq (sc.K * sc.D) (sc.K * sc.D) (matMulF (sc.N * (sc.y + sc.z)) DecInv (desiredMat sc)) matIdF)
    (r : PIRRand F) (hr : ValidRand sc r)
    (W1 W2 : Nat → Nat → F) (θ : Bool) :
    ∀ k d, k < sc.K → d < sc.D →
      pirDecode sc Cancel DecInv θ r
        (ansBlk1 sc θ r W1) (ansBlk2 sc θ r W2) (ansBlk3 sc θ r W1 W2) k d =
      (if θ then W2 k d else W1 k d) := by
  intro k d hk hd
  let W1t : Nat → Nat → F := fun k' => matVec sc.D r.S1 (W1 k')
  let W2t : Nat → Nat → F := fun k' => matVec sc.D r.S2 (W2 k')
  -- Clean exact push: `matVec D (M · S) (serverStorage W n) = matVec D M (serverStorage (S · W) n)`
  have hstorage : ∀ (M S : Nat → Nat → F) (W : Nat → Nat → F) (n i : Nat),
      matVec sc.D (matMulF sc.D M S) (serverStorage sc W n) i =
      matVec sc.D M (serverStorage sc (fun k' => matVec sc.D S (W k')) n) i := by
    intro M S W n i
    rw [matVec_mul]
    apply sumR_congr; intro d' _
    congr 1
    exact matVec_scale_sum sc.D sc.K S (sc.g n) W d'
  -- Unscramble Block 1 & Block 2
  have hu_eq : ∀ n i, n < sc.N → i < sc.y →
      matVec sc.y (r.R1inv n) (ansBlk1 sc θ r W1 n) i =
      matVec sc.D (if θ then sc.Q n else sc.P n) (serverStorage sc W1t n) i := by
    intro n i hn hi
    unfold ansBlk1 qBlk1
    dsimp only
    have hst : matVec sc.y (r.R1inv n)
        (matVec sc.D (matMulF sc.D (matMulF sc.y (r.R1 n) (if θ then sc.Q n else sc.P n)) r.S1) (serverStorage sc W1 n)) i =
        matVec sc.y (r.R1inv n)
          (matVec sc.D (matMulF sc.y (r.R1 n) (if θ then sc.Q n else sc.P n)) (serverStorage sc W1t n)) i := by
      apply sumR_congr; intro t _
      exact congrArg _ (hstorage _ _ _ _ _)
    rw [hst, ← matVec_mul]
    have hinv := (hr.2.2.1 n hn).2
    apply sumR_congr; intro d' _
    congr 1
    rw [← matMulF_assoc, matMulF_congr (fun t ht => hinv i t hi ht) (fun _ _ => rfl), matMulF_id_left sc.y _ hi]
  have hv_eq : ∀ n i, n < sc.N → i < sc.y →
      matVec sc.y (r.R2inv n) (ansBlk2 sc θ r W2 n) i =
      matVec sc.D (if θ then sc.P n else sc.Q n) (serverStorage sc W2t n) i := by
    intro n i hn hi
    unfold ansBlk2 qBlk2
    dsimp only
    have hst : matVec sc.y (r.R2inv n)
        (matVec sc.D (matMulF sc.D (matMulF sc.y (r.R2 n) (if θ then sc.P n else sc.Q n)) r.S2) (serverStorage sc W2 n)) i =
        matVec sc.y (r.R2inv n)
          (matVec sc.D (matMulF sc.y (r.R2 n) (if θ then sc.P n else sc.Q n)) (serverStorage sc W2t n)) i := by
      apply sumR_congr; intro t _
      exact congrArg _ (hstorage _ _ _ _ _)
    rw [hst, ← matVec_mul]
    have hinv := (hr.2.2.2.1 n hn).2
    apply sumR_congr; intro d' _
    congr 1
    rw [← matMulF_assoc, matMulF_congr (fun t ht => hinv i t hi ht) (fun _ _ => rfl), matMulF_id_left sc.y _ hi]
  -- Evaluate `intMixed` via `hCancel`: for any scrambled file `Wint`,
  -- `∑_{idx < N*y} Cancel (n*z + i) idx * matVec D (Q (idx/y)) (serverStorage Wint (idx/y)) (idx%y)`
  -- `= matVec D (Dblk n) (serverStorage Wint n) i`!
  have hcancel_vec : ∀ (Wint : Nat → Nat → F) (n i : Nat), n < sc.N → i < sc.z →
      matVec (sc.N * sc.y) Cancel
        (fun idx => matVec sc.D (sc.Q (idx / sc.y)) (serverStorage sc Wint (idx / sc.y)) (idx % sc.y))
        (n * sc.z + i) =
      matVec sc.D (sc.Dblk n) (serverStorage sc Wint n) i := by
    intro Wint n i hn hi
    -- Rewrite `matVec D (Q m) (serverStorage Wint m) j` as `∑_{col < K*D} pureIntMat (m*y+j) col * Wint(col/D, col%D)`
    have hrow_pure : ∀ idx, idx < sc.N * sc.y →
        matVec sc.D (sc.Q (idx / sc.y)) (serverStorage sc Wint (idx / sc.y)) (idx % sc.y) =
        matVec (sc.K * sc.D) (pureIntMat sc) (fun col => Wint (col / sc.D) (col % sc.D)) idx := by
      intro idx _
      unfold serverStorage
      rw [matVec_scale_sum]
      unfold matVec pureIntMat
      dsimp only
      rw [sumR_prod_reindex sc.K sc.D hD (fun k' d' => sc.g (idx / sc.y) k' * sc.Q (idx / sc.y) (idx % sc.y) d' * Wint k' d')]
      apply sumR_congr; intro k' _
      rw [sumR_mul_left]
      apply sumR_congr; intro d' _
      rw [CommRing.mul_assoc]
    have hrow_mixed :
        matVec sc.D (sc.Dblk n) (serverStorage sc Wint n) i =
        matVec (sc.K * sc.D) (mixedIntMat sc) (fun col => Wint (col / sc.D) (col % sc.D)) (n * sc.z + i) := by
      unfold serverStorage
      rw [matVec_scale_sum]
      unfold matVec mixedIntMat
      dsimp only
      have hdiv : (n * sc.z + i) / sc.z = n := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hz, Nat.div_eq_of_lt hi, Nat.zero_add]
      have hmod : (n * sc.z + i) % sc.z = i := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
      simp only [hdiv, hmod]
      rw [sumR_prod_reindex sc.K sc.D hD (fun k' d' => sc.g n k' * sc.Dblk n i d' * Wint k' d')]
      apply sumR_congr; intro k' _
      rw [sumR_mul_left]
      apply sumR_congr; intro d' _
      rw [CommRing.mul_assoc]
    have hnz : n * sc.z + i < sc.N * sc.z := by
      calc n * sc.z + i < n * sc.z + sc.z := Nat.add_lt_add_left hi _
        _ = (n + 1) * sc.z := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ sc.N * sc.z := Nat.mul_le_mul_right sc.z hn
    rw [hrow_mixed]
    have h1 : matVec (sc.N * sc.y) Cancel
        (fun idx => matVec sc.D (sc.Q (idx / sc.y)) (serverStorage sc Wint (idx / sc.y)) (idx % sc.y))
        (n * sc.z + i) =
        matVec (sc.N * sc.y) Cancel
          (matVec (sc.K * sc.D) (pureIntMat sc) (fun col => Wint (col / sc.D) (col % sc.D)))
          (n * sc.z + i) := by
      apply sumR_congr; intro idx hidx
      dsimp only
      rw [hrow_pure idx hidx]
    rw [h1, ← matVec_mul]
    apply sumR_congr; intro col hcol
    rw [hCancel (n * sc.z + i) col hnz hcol]
  -- Evaluate `ansBlk3`
  have hans3 : ∀ n i,
      ansBlk3 sc θ r W1 W2 n i =
      (matVec sc.z (r.H1 n) (matVec sc.D (if θ then sc.Dblk n else sc.C n) (serverStorage sc W1t n)) i +
       matVec sc.y (r.L1 n) (matVec sc.D (if θ then sc.Q n else sc.P n) (serverStorage sc W1t n)) i) +
      (matVec sc.z (r.H2 n) (matVec sc.D (if θ then sc.C n else sc.Dblk n) (serverStorage sc W2t n)) i +
       matVec sc.y (r.L2 n) (matVec sc.D (if θ then sc.P n else sc.Q n) (serverStorage sc W2t n)) i) := by
    intro n i
    unfold ansBlk3 qBlk3File1 qBlk3File2
    rw [hstorage, hstorage, matVec_add, matVec_add, matVec_mul, matVec_mul, matVec_mul, matVec_mul]
  -- Helper arithmetic: `((a + b) + (c + d)) - b - d - c = a` and `((a + b) + (c + d)) - b - d - a = c`
  have hsub_keep1 : ∀ a b c d : F, ((a + b) + (c + d)) - b - d - c = a := by
    intro a b c d
    rw [CommRing.sub_eq, CommRing.sub_eq, CommRing.sub_eq]
    calc (a + b) + (c + d) + -b + -d + -c
        = (a + (b + -b)) + ((c + -c) + (d + -d)) := by
          -- Reorder 7 summands cleanly
          rw [CommRing.add_assoc (a + b) (c + d) (-b),
              CommRing.add_comm (c + d) (-b),
              ← CommRing.add_assoc (a + b) (-b) (c + d),
              CommRing.add_assoc a b (-b),
              CommRing.add_assoc (a + (b + -b)) (c + d) (-d),
              CommRing.add_assoc c d (-d),
              CommRing.add_assoc (a + (b + -b)) (c + (d + -d)) (-c),
              CommRing.add_comm c (d + -d),
              CommRing.add_assoc (d + -d) c (-c),
              CommRing.add_comm (d + -d) (c + -c)]
      _ = (a + 0) + (0 + 0) := by rw [CommRing.add_neg, CommRing.add_neg, CommRing.add_neg]
      _ = a := by rw [add_zero, add_zero, add_zero]
  have hsub_keep2 : ∀ a b c d : F, ((a + b) + (c + d)) - b - d - a = c := by
    intro a b c d
    rw [CommRing.add_comm (a + b) (c + d)]
    have h := hsub_keep1 c d a b
    -- Swap `- b - d` order
    have hsw : ∀ x y z : F, x - y - z = x - z - y := by
      intro x y z
      rw [CommRing.sub_eq, CommRing.sub_eq, CommRing.sub_eq, CommRing.sub_eq,
          CommRing.add_assoc, CommRing.add_comm (-y) (-z), ← CommRing.add_assoc]
    rw [hsw _ b d]
    exact h
  -- Final step: evaluate `pirDecode` by cases on `θ`
  unfold pirDecode
  cases θ with
  | false =>
    -- File 1 (`θ = false`): `desVec` matches `desiredMat · W1t`, then `DecInv` recovers `W1t`, `S1inv` recovers `W1`!
    have hdes_eq : ∀ row, row < sc.N * (sc.y + sc.z) →
        (let u := fun n => matVec sc.y (r.R1inv n) (ansBlk1 sc false r W1 n)
         let v := fun n => matVec sc.y (r.R2inv n) (ansBlk2 sc false r W2 n)
         let intVec := fun idx => v (idx / sc.y) (idx % sc.y)
         let intMixed := fun n i => matVec (sc.N * sc.y) Cancel intVec (n * sc.z + i)
         let w := fun n => matVec sc.z (r.H1inv n) (fun i =>
           ansBlk3 sc false r W1 W2 n i - matVec sc.y (r.L1 n) (u n) i -
           matVec sc.y (r.L2 n) (v n) i - matVec sc.z (r.H2 n) (intMixed n) i)
         let n := row / (sc.y + sc.z)
         let t := row % (sc.y + sc.z)
         if t < sc.y then u n t else w n (t - sc.y)) =
        matVec (sc.K * sc.D) (desiredMat sc) (fun col => W1t (col / sc.D) (col % sc.D)) row := by
      intro row hrow
      have hyz : 0 < sc.y + sc.z := Nat.add_pos_left hy sc.z
      let n := row / (sc.y + sc.z)
      let t := row % (sc.y + sc.z)
      have hn : n < sc.N := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hrow)
      have ht : t < sc.y + sc.z := Nat.mod_lt row hyz
      have hmat_eval : ∀ (M : Nat → Nat → F) (idx : Nat),
          matVec sc.D M (serverStorage sc W1t n) idx =
          sumR (sc.K * sc.D) (fun col => sc.g n (col / sc.D) * M idx (col % sc.D) * W1t (col / sc.D) (col % sc.D)) := by
        intro M idx
        unfold serverStorage
        rw [matVec_scale_sum]
        unfold matVec
        rw [sumR_prod_reindex sc.K sc.D hD (fun k' d' => sc.g n k' * M idx d' * W1t k' d')]
        apply sumR_congr; intro k' _
        rw [sumR_mul_left]
        apply sumR_congr; intro d' _; rw [CommRing.mul_assoc]
      dsimp only
      by_cases hty : row % (sc.y + sc.z) < sc.y
      · simp only [hty, ↓reduceIte]
        rw [hu_eq n t hn hty]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hmat_eval (sc.P n) t]
        unfold matVec desiredMat
        apply sumR_congr; intro col _
        dsimp only
        simp only [hty, ↓reduceIte]
        rfl
      · simp only [hty, ↓reduceIte]
        have htz : t - sc.y < sc.z := by omega
        -- Simplify `stripped` to `matVec sc.z (r.H1 n) (matVec sc.D (sc.C n) (serverStorage sc W1t n))`
        have hstr : ∀ j, j < sc.z →
            ansBlk3 sc false r W1 W2 n j -
            matVec sc.y (r.L1 n) (matVec sc.y (r.R1inv n) (ansBlk1 sc false r W1 n)) j -
            matVec sc.y (r.L2 n) (matVec sc.y (r.R2inv n) (ansBlk2 sc false r W2 n)) j -
            matVec sc.z (r.H2 n)
              (fun i => matVec (sc.N * sc.y) Cancel
                (fun idx => matVec sc.y (r.R2inv (idx / sc.y)) (ansBlk2 sc false r W2 (idx / sc.y)) (idx % sc.y))
                (n * sc.z + i)) j =
            matVec sc.z (r.H1 n) (matVec sc.D (sc.C n) (serverStorage sc W1t n)) j := by
          intro j _
          rw [hans3 n j]
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hL1 : matVec sc.y (r.L1 n) (matVec sc.y (r.R1inv n) (ansBlk1 sc false r W1 n)) j =
              matVec sc.y (r.L1 n) (matVec sc.D (sc.P n) (serverStorage sc W1t n)) j := by
            apply sumR_congr; intro i hi
            rw [hu_eq n i hn hi]; simp
          have hL2 : matVec sc.y (r.L2 n) (matVec sc.y (r.R2inv n) (ansBlk2 sc false r W2 n)) j =
              matVec sc.y (r.L2 n) (matVec sc.D (sc.Q n) (serverStorage sc W2t n)) j := by
            apply sumR_congr; intro i hi
            rw [hv_eq n i hn hi]; simp
          have hH2 : matVec sc.z (r.H2 n)
              (fun i => matVec (sc.N * sc.y) Cancel
                (fun idx => matVec sc.y (r.R2inv (idx / sc.y)) (ansBlk2 sc false r W2 (idx / sc.y)) (idx % sc.y))
                (n * sc.z + i)) j =
              matVec sc.z (r.H2 n) (matVec sc.D (sc.Dblk n) (serverStorage sc W2t n)) j := by
            apply sumR_congr; intro i hi
            congr 1
            dsimp only
            have hint_congr : matVec (sc.N * sc.y) Cancel
                (fun idx => matVec sc.y (r.R2inv (idx / sc.y)) (ansBlk2 sc false r W2 (idx / sc.y)) (idx % sc.y))
                (n * sc.z + i) =
                matVec (sc.N * sc.y) Cancel
                  (fun idx => matVec sc.D (sc.Q (idx / sc.y)) (serverStorage sc W2t (idx / sc.y)) (idx % sc.y))
                  (n * sc.z + i) := by
              apply sumR_congr; intro idx hidx
              dsimp only
              have hn' : idx / sc.y < sc.N := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
              have hi' : idx % sc.y < sc.y := Nat.mod_lt idx hy
              rw [hv_eq (idx / sc.y) (idx % sc.y) hn' hi']; simp
            rw [hint_congr, hcancel_vec W2t n i hn hi]
          rw [hL1, hL2, hH2]
          exact hsub_keep1 ..
        have hw_eq : matVec sc.z (r.H1inv n)
            (fun j => ansBlk3 sc false r W1 W2 n j -
              matVec sc.y (r.L1 n) (matVec sc.y (r.R1inv n) (ansBlk1 sc false r W1 n)) j -
              matVec sc.y (r.L2 n) (matVec sc.y (r.R2inv n) (ansBlk2 sc false r W2 n)) j -
              matVec sc.z (r.H2 n)
                (fun i => matVec (sc.N * sc.y) Cancel
                  (fun idx => matVec sc.y (r.R2inv (idx / sc.y)) (ansBlk2 sc false r W2 (idx / sc.y)) (idx % sc.y))
                  (n * sc.z + i)) j) (t - sc.y) =
            matVec sc.D (sc.C n) (serverStorage sc W1t n) (t - sc.y) := by
          have hc1 : matVec sc.z (r.H1inv n)
              (fun j => ansBlk3 sc false r W1 W2 n j -
                matVec sc.y (r.L1 n) (matVec sc.y (r.R1inv n) (ansBlk1 sc false r W1 n)) j -
                matVec sc.y (r.L2 n) (matVec sc.y (r.R2inv n) (ansBlk2 sc false r W2 n)) j -
                matVec sc.z (r.H2 n)
                  (fun i => matVec (sc.N * sc.y) Cancel
                    (fun idx => matVec sc.y (r.R2inv (idx / sc.y)) (ansBlk2 sc false r W2 (idx / sc.y)) (idx % sc.y))
                    (n * sc.z + i)) j) (t - sc.y) =
              matVec sc.z (r.H1inv n) (matVec sc.z (r.H1 n) (matVec sc.D (sc.C n) (serverStorage sc W1t n))) (t - sc.y) := by
            apply sumR_congr; intro j hj; dsimp only; rw [hstr j hj]
          rw [hc1, ← matVec_mul]
          have hinv := (hr.2.2.2.2.1 n hn).2
          have h2 : matVec sc.z (matMulF sc.z (r.H1inv n) (r.H1 n))
              (matVec sc.D (sc.C n) (serverStorage sc W1t n)) (t - sc.y) =
              matVec sc.z matIdF (matVec sc.D (sc.C n) (serverStorage sc W1t n)) (t - sc.y) := by
            apply sumR_congr; intro j hj; rw [hinv (t - sc.y) j htz hj]
          rw [h2, matVec_id sc.z _ htz]
        rw [hw_eq, hmat_eval (sc.C n) (t - sc.y)]
        unfold matVec desiredMat
        apply sumR_congr; intro col _
        dsimp only
        have hty' : ¬ (row % (sc.y + sc.z) < sc.y) := hty
        simp only [hty', ↓reduceIte]
        rfl
    -- Apply `DecInv` and `S1inv`
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hscr : ∀ d', d' < sc.D →
        matVec (sc.N * (sc.y + sc.z)) DecInv
          (fun row =>
            if row % (sc.y + sc.z) < sc.y then
              matVec sc.y (r.R1inv (row / (sc.y + sc.z))) (ansBlk1 sc false r W1 (row / (sc.y + sc.z))) (row % (sc.y + sc.z))
            else
              matVec sc.z (r.H1inv (row / (sc.y + sc.z)))
                (fun i =>
                  ansBlk3 sc false r W1 W2 (row / (sc.y + sc.z)) i -
                  matVec sc.y (r.L1 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R1inv (row / (sc.y + sc.z))) (ansBlk1 sc false r W1 (row / (sc.y + sc.z)))) i -
                  matVec sc.y (r.L2 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R2inv (row / (sc.y + sc.z))) (ansBlk2 sc false r W2 (row / (sc.y + sc.z)))) i -
                  matVec sc.z (r.H2 (row / (sc.y + sc.z)))
                    (fun j => matVec (sc.N * sc.y) Cancel
                      (fun idx => matVec sc.y (r.R2inv (idx / sc.y)) (ansBlk2 sc false r W2 (idx / sc.y)) (idx % sc.y))
                      (row / (sc.y + sc.z) * sc.z + j)) i)
                (row % (sc.y + sc.z) - sc.y))
          (k * sc.D + d') =
        W1t k d' := by
      intro d' hd'
      have hkd : k * sc.D + d' < sc.K * sc.D := by
        calc k * sc.D + d' < k * sc.D + sc.D := Nat.add_lt_add_left hd' _
          _ = (k + 1) * sc.D := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ sc.K * sc.D := Nat.mul_le_mul_right sc.D hk
      have hc : matVec (sc.N * (sc.y + sc.z)) DecInv
          (fun row =>
            if row % (sc.y + sc.z) < sc.y then
              matVec sc.y (r.R1inv (row / (sc.y + sc.z))) (ansBlk1 sc false r W1 (row / (sc.y + sc.z))) (row % (sc.y + sc.z))
            else
              matVec sc.z (r.H1inv (row / (sc.y + sc.z)))
                (fun i =>
                  ansBlk3 sc false r W1 W2 (row / (sc.y + sc.z)) i -
                  matVec sc.y (r.L1 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R1inv (row / (sc.y + sc.z))) (ansBlk1 sc false r W1 (row / (sc.y + sc.z)))) i -
                  matVec sc.y (r.L2 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R2inv (row / (sc.y + sc.z))) (ansBlk2 sc false r W2 (row / (sc.y + sc.z)))) i -
                  matVec sc.z (r.H2 (row / (sc.y + sc.z)))
                    (fun j => matVec (sc.N * sc.y) Cancel
                      (fun idx => matVec sc.y (r.R2inv (idx / sc.y)) (ansBlk2 sc false r W2 (idx / sc.y)) (idx % sc.y))
                      (row / (sc.y + sc.z) * sc.z + j)) i)
                (row % (sc.y + sc.z) - sc.y))
          (k * sc.D + d') =
          matVec (sc.N * (sc.y + sc.z)) DecInv
            (matVec (sc.K * sc.D) (desiredMat sc) (fun col => W1t (col / sc.D) (col % sc.D)))
            (k * sc.D + d') := by
        apply sumR_congr; intro row hrow
        dsimp only
        exact congrArg (fun x => DecInv (k * sc.D + d') row * x) (hdes_eq row hrow)
      rw [hc, ← matVec_mul]
      have h2 : matVec (sc.K * sc.D) (matMulF (sc.N * (sc.y + sc.z)) DecInv (desiredMat sc))
          (fun col => W1t (col / sc.D) (col % sc.D)) (k * sc.D + d') =
          matVec (sc.K * sc.D) matIdF (fun col => W1t (col / sc.D) (col % sc.D)) (k * sc.D + d') := by
        apply sumR_congr; intro col hcol; rw [hDec (k * sc.D + d') col hkd hcol]
      rw [h2, matVec_id (sc.K * sc.D) _ hkd]
      have hdiv : (k * sc.D + d') / sc.D = k := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hd', Nat.zero_add]
      have hmod : (k * sc.D + d') % sc.D = d' := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd']
      rw [hdiv, hmod]
    have hfin : matVec sc.D r.S1inv (fun d' =>
        matVec (sc.N * (sc.y + sc.z)) DecInv
          (fun row =>
            if row % (sc.y + sc.z) < sc.y then
              matVec sc.y (r.R1inv (row / (sc.y + sc.z))) (ansBlk1 sc false r W1 (row / (sc.y + sc.z))) (row % (sc.y + sc.z))
            else
              matVec sc.z (r.H1inv (row / (sc.y + sc.z)))
                (fun i =>
                  ansBlk3 sc false r W1 W2 (row / (sc.y + sc.z)) i -
                  matVec sc.y (r.L1 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R1inv (row / (sc.y + sc.z))) (ansBlk1 sc false r W1 (row / (sc.y + sc.z)))) i -
                  matVec sc.y (r.L2 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R2inv (row / (sc.y + sc.z))) (ansBlk2 sc false r W2 (row / (sc.y + sc.z)))) i -
                  matVec sc.z (r.H2 (row / (sc.y + sc.z)))
                    (fun j => matVec (sc.N * sc.y) Cancel
                      (fun idx => matVec sc.y (r.R2inv (idx / sc.y)) (ansBlk2 sc false r W2 (idx / sc.y)) (idx % sc.y))
                      (row / (sc.y + sc.z) * sc.z + j)) i)
                (row % (sc.y + sc.z) - sc.y))
          (k * sc.D + d')) d =
        matVec sc.D r.S1inv (W1t k) d := by
      apply sumR_congr; intro d' hd'
      dsimp only
      exact congrArg (fun x => r.S1inv d d' * x) (hscr d' hd')
    rw [hfin]
    dsimp only [W1t]
    rw [← matVec_mul]
    have h2 : matVec sc.D (matMulF sc.D r.S1inv r.S1) (W1 k) d = matVec sc.D matIdF (W1 k) d := by
      apply sumR_congr; intro d' hd'; rw [hr.1.2 d d' hd hd']
    rw [h2, matVec_id sc.D _ hd]
  | true =>
    -- File 2 (`θ = true`): exact symmetric proof recovering `W2 k d`!
    have hdes_eq : ∀ row, row < sc.N * (sc.y + sc.z) →
        (let u := fun n => matVec sc.y (r.R1inv n) (ansBlk1 sc true r W1 n)
         let v := fun n => matVec sc.y (r.R2inv n) (ansBlk2 sc true r W2 n)
         let intVec := fun idx => u (idx / sc.y) (idx % sc.y)
         let intMixed := fun n i => matVec (sc.N * sc.y) Cancel intVec (n * sc.z + i)
         let w := fun n => matVec sc.z (r.H2inv n) (fun i =>
           ansBlk3 sc true r W1 W2 n i - matVec sc.y (r.L1 n) (u n) i -
           matVec sc.y (r.L2 n) (v n) i - matVec sc.z (r.H1 n) (intMixed n) i)
         let n := row / (sc.y + sc.z)
         let t := row % (sc.y + sc.z)
         if t < sc.y then v n t else w n (t - sc.y)) =
        matVec (sc.K * sc.D) (desiredMat sc) (fun col => W2t (col / sc.D) (col % sc.D)) row := by
      intro row hrow
      have hyz : 0 < sc.y + sc.z := Nat.add_pos_left hy sc.z
      let n := row / (sc.y + sc.z)
      let t := row % (sc.y + sc.z)
      have hn : n < sc.N := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hrow)
      have ht : t < sc.y + sc.z := Nat.mod_lt row hyz
      have hmat_eval : ∀ (M : Nat → Nat → F) (idx : Nat),
          matVec sc.D M (serverStorage sc W2t n) idx =
          sumR (sc.K * sc.D) (fun col => sc.g n (col / sc.D) * M idx (col % sc.D) * W2t (col / sc.D) (col % sc.D)) := by
        intro M idx
        unfold serverStorage
        rw [matVec_scale_sum]
        unfold matVec
        rw [sumR_prod_reindex sc.K sc.D hD (fun k' d' => sc.g n k' * M idx d' * W2t k' d')]
        apply sumR_congr; intro k' _
        rw [sumR_mul_left]
        apply sumR_congr; intro d' _; rw [CommRing.mul_assoc]
      dsimp only
      by_cases hty : row % (sc.y + sc.z) < sc.y
      · simp only [hty, ↓reduceIte]
        rw [hv_eq n t hn hty]
        simp only [↓reduceIte]
        rw [hmat_eval (sc.P n) t]
        unfold matVec desiredMat
        apply sumR_congr; intro col _
        dsimp only
        simp only [hty, ↓reduceIte]
        rfl
      · simp only [hty, ↓reduceIte]
        have htz : t - sc.y < sc.z := by omega
        have hstr : ∀ j, j < sc.z →
            ansBlk3 sc true r W1 W2 n j -
            matVec sc.y (r.L1 n) (matVec sc.y (r.R1inv n) (ansBlk1 sc true r W1 n)) j -
            matVec sc.y (r.L2 n) (matVec sc.y (r.R2inv n) (ansBlk2 sc true r W2 n)) j -
            matVec sc.z (r.H1 n)
              (fun i => matVec (sc.N * sc.y) Cancel
                (fun idx => matVec sc.y (r.R1inv (idx / sc.y)) (ansBlk1 sc true r W1 (idx / sc.y)) (idx % sc.y))
                (n * sc.z + i)) j =
            matVec sc.z (r.H2 n) (matVec sc.D (sc.C n) (serverStorage sc W2t n)) j := by
          intro j _
          rw [hans3 n j]
          simp only [↓reduceIte]
          have hL1 : matVec sc.y (r.L1 n) (matVec sc.y (r.R1inv n) (ansBlk1 sc true r W1 n)) j =
              matVec sc.y (r.L1 n) (matVec sc.D (sc.Q n) (serverStorage sc W1t n)) j := by
            apply sumR_congr; intro i hi
            rw [hu_eq n i hn hi]; simp
          have hL2 : matVec sc.y (r.L2 n) (matVec sc.y (r.R2inv n) (ansBlk2 sc true r W2 n)) j =
              matVec sc.y (r.L2 n) (matVec sc.D (sc.P n) (serverStorage sc W2t n)) j := by
            apply sumR_congr; intro i hi
            rw [hv_eq n i hn hi]; simp
          have hH1 : matVec sc.z (r.H1 n)
              (fun i => matVec (sc.N * sc.y) Cancel
                (fun idx => matVec sc.y (r.R1inv (idx / sc.y)) (ansBlk1 sc true r W1 (idx / sc.y)) (idx % sc.y))
                (n * sc.z + i)) j =
              matVec sc.z (r.H1 n) (matVec sc.D (sc.Dblk n) (serverStorage sc W1t n)) j := by
            apply sumR_congr; intro i hi
            congr 1
            dsimp only
            have hint_congr : matVec (sc.N * sc.y) Cancel
                (fun idx => matVec sc.y (r.R1inv (idx / sc.y)) (ansBlk1 sc true r W1 (idx / sc.y)) (idx % sc.y))
                (n * sc.z + i) =
                matVec (sc.N * sc.y) Cancel
                  (fun idx => matVec sc.D (sc.Q (idx / sc.y)) (serverStorage sc W1t (idx / sc.y)) (idx % sc.y))
                  (n * sc.z + i) := by
              apply sumR_congr; intro idx hidx
              dsimp only
              have hn' : idx / sc.y < sc.N := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
              have hi' : idx % sc.y < sc.y := Nat.mod_lt idx hy
              rw [hu_eq (idx / sc.y) (idx % sc.y) hn' hi']; simp
            rw [hint_congr, hcancel_vec W1t n i hn hi]
          rw [hL1, hL2, hH1]
          exact hsub_keep2 ..
        have hw_eq : matVec sc.z (r.H2inv n)
            (fun j => ansBlk3 sc true r W1 W2 n j -
              matVec sc.y (r.L1 n) (matVec sc.y (r.R1inv n) (ansBlk1 sc true r W1 n)) j -
              matVec sc.y (r.L2 n) (matVec sc.y (r.R2inv n) (ansBlk2 sc true r W2 n)) j -
              matVec sc.z (r.H1 n)
                (fun i => matVec (sc.N * sc.y) Cancel
                  (fun idx => matVec sc.y (r.R1inv (idx / sc.y)) (ansBlk1 sc true r W1 (idx / sc.y)) (idx % sc.y))
                  (n * sc.z + i)) j) (t - sc.y) =
            matVec sc.D (sc.C n) (serverStorage sc W2t n) (t - sc.y) := by
          have hc1 : matVec sc.z (r.H2inv n)
              (fun j => ansBlk3 sc true r W1 W2 n j -
                matVec sc.y (r.L1 n) (matVec sc.y (r.R1inv n) (ansBlk1 sc true r W1 n)) j -
                matVec sc.y (r.L2 n) (matVec sc.y (r.R2inv n) (ansBlk2 sc true r W2 n)) j -
                matVec sc.z (r.H1 n)
                  (fun i => matVec (sc.N * sc.y) Cancel
                    (fun idx => matVec sc.y (r.R1inv (idx / sc.y)) (ansBlk1 sc true r W1 (idx / sc.y)) (idx % sc.y))
                    (n * sc.z + i)) j) (t - sc.y) =
              matVec sc.z (r.H2inv n) (matVec sc.z (r.H2 n) (matVec sc.D (sc.C n) (serverStorage sc W2t n))) (t - sc.y) := by
            apply sumR_congr; intro j hj; dsimp only; rw [hstr j hj]
          rw [hc1, ← matVec_mul]
          have hinv := (hr.2.2.2.2.2 n hn).2
          have h2 : matVec sc.z (matMulF sc.z (r.H2inv n) (r.H2 n))
              (matVec sc.D (sc.C n) (serverStorage sc W2t n)) (t - sc.y) =
              matVec sc.z matIdF (matVec sc.D (sc.C n) (serverStorage sc W2t n)) (t - sc.y) := by
            apply sumR_congr; intro j hj; rw [hinv (t - sc.y) j htz hj]
          rw [h2, matVec_id sc.z _ htz]
        rw [hw_eq, hmat_eval (sc.C n) (t - sc.y)]
        unfold matVec desiredMat
        apply sumR_congr; intro col _
        dsimp only
        have hty' : ¬ (row % (sc.y + sc.z) < sc.y) := hty
        simp only [hty', ↓reduceIte]
        rfl
    dsimp only
    simp only [↓reduceIte]
    have hscr : ∀ d', d' < sc.D →
        matVec (sc.N * (sc.y + sc.z)) DecInv
          (fun row =>
            if row % (sc.y + sc.z) < sc.y then
              matVec sc.y (r.R2inv (row / (sc.y + sc.z))) (ansBlk2 sc true r W2 (row / (sc.y + sc.z))) (row % (sc.y + sc.z))
            else
              matVec sc.z (r.H2inv (row / (sc.y + sc.z)))
                (fun i =>
                  ansBlk3 sc true r W1 W2 (row / (sc.y + sc.z)) i -
                  matVec sc.y (r.L1 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R1inv (row / (sc.y + sc.z))) (ansBlk1 sc true r W1 (row / (sc.y + sc.z)))) i -
                  matVec sc.y (r.L2 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R2inv (row / (sc.y + sc.z))) (ansBlk2 sc true r W2 (row / (sc.y + sc.z)))) i -
                  matVec sc.z (r.H1 (row / (sc.y + sc.z)))
                    (fun j => matVec (sc.N * sc.y) Cancel
                      (fun idx => matVec sc.y (r.R1inv (idx / sc.y)) (ansBlk1 sc true r W1 (idx / sc.y)) (idx % sc.y))
                      (row / (sc.y + sc.z) * sc.z + j)) i)
                (row % (sc.y + sc.z) - sc.y))
          (k * sc.D + d') =
        W2t k d' := by
      intro d' hd'
      have hkd : k * sc.D + d' < sc.K * sc.D := by
        calc k * sc.D + d' < k * sc.D + sc.D := Nat.add_lt_add_left hd' _
          _ = (k + 1) * sc.D := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ sc.K * sc.D := Nat.mul_le_mul_right sc.D hk
      have hc : matVec (sc.N * (sc.y + sc.z)) DecInv
          (fun row =>
            if row % (sc.y + sc.z) < sc.y then
              matVec sc.y (r.R2inv (row / (sc.y + sc.z))) (ansBlk2 sc true r W2 (row / (sc.y + sc.z))) (row % (sc.y + sc.z))
            else
              matVec sc.z (r.H2inv (row / (sc.y + sc.z)))
                (fun i =>
                  ansBlk3 sc true r W1 W2 (row / (sc.y + sc.z)) i -
                  matVec sc.y (r.L1 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R1inv (row / (sc.y + sc.z))) (ansBlk1 sc true r W1 (row / (sc.y + sc.z)))) i -
                  matVec sc.y (r.L2 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R2inv (row / (sc.y + sc.z))) (ansBlk2 sc true r W2 (row / (sc.y + sc.z)))) i -
                  matVec sc.z (r.H1 (row / (sc.y + sc.z)))
                    (fun j => matVec (sc.N * sc.y) Cancel
                      (fun idx => matVec sc.y (r.R1inv (idx / sc.y)) (ansBlk1 sc true r W1 (idx / sc.y)) (idx % sc.y))
                      (row / (sc.y + sc.z) * sc.z + j)) i)
                (row % (sc.y + sc.z) - sc.y))
          (k * sc.D + d') =
          matVec (sc.N * (sc.y + sc.z)) DecInv
            (matVec (sc.K * sc.D) (desiredMat sc) (fun col => W2t (col / sc.D) (col % sc.D)))
            (k * sc.D + d') := by
        apply sumR_congr; intro row hrow
        dsimp only
        exact congrArg (fun x => DecInv (k * sc.D + d') row * x) (hdes_eq row hrow)
      rw [hc, ← matVec_mul]
      have h2 : matVec (sc.K * sc.D) (matMulF (sc.N * (sc.y + sc.z)) DecInv (desiredMat sc))
          (fun col => W2t (col / sc.D) (col % sc.D)) (k * sc.D + d') =
          matVec (sc.K * sc.D) matIdF (fun col => W2t (col / sc.D) (col % sc.D)) (k * sc.D + d') := by
        apply sumR_congr; intro col hcol; rw [hDec (k * sc.D + d') col hkd hcol]
      rw [h2, matVec_id (sc.K * sc.D) _ hkd]
      have hdiv : (k * sc.D + d') / sc.D = k := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hd', Nat.zero_add]
      have hmod : (k * sc.D + d') % sc.D = d' := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd']
      rw [hdiv, hmod]
    have hfin : matVec sc.D r.S2inv (fun d' =>
        matVec (sc.N * (sc.y + sc.z)) DecInv
          (fun row =>
            if row % (sc.y + sc.z) < sc.y then
              matVec sc.y (r.R2inv (row / (sc.y + sc.z))) (ansBlk2 sc true r W2 (row / (sc.y + sc.z))) (row % (sc.y + sc.z))
            else
              matVec sc.z (r.H2inv (row / (sc.y + sc.z)))
                (fun i =>
                  ansBlk3 sc true r W1 W2 (row / (sc.y + sc.z)) i -
                  matVec sc.y (r.L1 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R1inv (row / (sc.y + sc.z))) (ansBlk1 sc true r W1 (row / (sc.y + sc.z)))) i -
                  matVec sc.y (r.L2 (row / (sc.y + sc.z)))
                    (matVec sc.y (r.R2inv (row / (sc.y + sc.z))) (ansBlk2 sc true r W2 (row / (sc.y + sc.z)))) i -
                  matVec sc.z (r.H1 (row / (sc.y + sc.z)))
                    (fun j => matVec (sc.N * sc.y) Cancel
                      (fun idx => matVec sc.y (r.R1inv (idx / sc.y)) (ansBlk1 sc true r W1 (idx / sc.y)) (idx % sc.y))
                      (row / (sc.y + sc.z) * sc.z + j)) i)
                (row % (sc.y + sc.z) - sc.y))
          (k * sc.D + d')) d =
        matVec sc.D r.S2inv (W2t k) d := by
      apply sumR_congr; intro d' hd'
      dsimp only
      exact congrArg (fun x => r.S2inv d d' * x) (hscr d' hd')
    rw [hfin]
    dsimp only [W2t]
    rw [← matVec_mul]
    have h2 : matVec sc.D (matMulF sc.D r.S2inv r.S2) (W2 k) d = matVec sc.D matIdF (W2 k) d := by
      apply sumR_congr; intro d' hd'; rw [hr.2.1.2 d d' hd hd']
    rw [h2, matVec_id sc.D _ hd]

-- ============================================================================
-- Section 3: Exact `T`-Collusion Information-Theoretic Privacy Bijection `Ψ_I`
-- ============================================================================

/-- Flag-isomorphism witness for a colluding server subset `inI : Nat → Bool`. -/
structure FlagIsoWitness (F : Type) where
  M    : Nat → Nat → F
  Minv : Nat → Nat → F
  α    : Nat → Nat → Nat → F
  αinv : Nat → Nat → Nat → F
  γ    : Nat → Nat → Nat → F
  γinv : Nat → Nat → Nat → F
  β    : Nat → Nat → Nat → F

/-- Algebraic flag-preservation certificate for subset `inI`:
    `M ∈ GL_D(F)` and for every `n < N` with `inI n = true`,
    `α_n ∈ GL_y(F)`, `γ_n ∈ GL_z(F)`, `P_n M = α_n Q_n`, and `C_n M = γ_n D_n + β_n Q_n`. -/
def ValidFlagIso {F : Type} [CommRing F] (sc : PIRScheme F) (inI : Nat → Bool)
    (w : FlagIsoWitness F) : Prop :=
  IsMatInv sc.D w.M w.Minv ∧
  (∀ n, n < sc.N → inI n = true →
    IsMatInv sc.y (w.α n) (w.αinv n) ∧
    IsMatInv sc.z (w.γ n) (w.γinv n) ∧
    MatEq sc.y sc.D (matMulF sc.D (sc.P n) w.M) (matMulF sc.y (w.α n) (sc.Q n)) ∧
    MatEq sc.z sc.D (matMulF sc.D (sc.C n) w.M)
      (matAdd (matMulF sc.z (w.γ n) (sc.Dblk n)) (matMulF sc.y (w.β n) (sc.Q n))))

/-- Forward privacy bijection `Ψ_I : PIRRand → PIRRand` mapping `θ = false` (File 1) randomness
    to `θ = true` (File 2) randomness with IDENTICAL queries on every server `n ∈ I`. -/
def psiFwd {F : Type} [CommRing F] (sc : PIRScheme F) (inI : Nat → Bool)
    (w : FlagIsoWitness F) (r : PIRRand F) : PIRRand F where
  S1    := matMulF sc.D w.Minv r.S1
  S1inv := matMulF sc.D r.S1inv w.M
  S2    := matMulF sc.D w.M r.S2
  S2inv := matMulF sc.D r.S2inv w.Minv
  R1    := fun n => if inI n then matMulF sc.y (r.R1 n) (w.α n) else r.R1 n
  R1inv := fun n => if inI n then matMulF sc.y (w.αinv n) (r.R1inv n) else r.R1inv n
  R2    := fun n => if inI n then matMulF sc.y (r.R2 n) (w.αinv n) else r.R2 n
  R2inv := fun n => if inI n then matMulF sc.y (w.α n) (r.R2inv n) else r.R2inv n
  H1    := fun n => if inI n then matMulF sc.z (r.H1 n) (w.γ n) else r.H1 n
  H1inv := fun n => if inI n then matMulF sc.z (w.γinv n) (r.H1inv n) else r.H1inv n
  H2    := fun n => if inI n then matMulF sc.z (r.H2 n) (w.γinv n) else r.H2 n
  H2inv := fun n => if inI n then matMulF sc.z (w.γ n) (r.H2inv n) else r.H2inv n
  L1    := fun n => if inI n then
      matAdd (matMulF sc.z (r.H1 n) (w.β n)) (matMulF sc.y (r.L1 n) (w.α n)) else r.L1 n
  L2    := fun n => if inI n then
      matMulF sc.y (matSub (r.L2 n) (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (w.β n))) (w.αinv n)
    else r.L2 n

/-- Inverse privacy bijection `Ψ_I^{-1} : PIRRand → PIRRand`. -/
def psiInv {F : Type} [CommRing F] (sc : PIRScheme F) (inI : Nat → Bool)
    (w : FlagIsoWitness F) (r : PIRRand F) : PIRRand F where
  S1    := matMulF sc.D w.M r.S1
  S1inv := matMulF sc.D r.S1inv w.Minv
  S2    := matMulF sc.D w.Minv r.S2
  S2inv := matMulF sc.D r.S2inv w.M
  R1    := fun n => if inI n then matMulF sc.y (r.R1 n) (w.αinv n) else r.R1 n
  R1inv := fun n => if inI n then matMulF sc.y (w.α n) (r.R1inv n) else r.R1inv n
  R2    := fun n => if inI n then matMulF sc.y (r.R2 n) (w.α n) else r.R2 n
  R2inv := fun n => if inI n then matMulF sc.y (w.αinv n) (r.R2inv n) else r.R2inv n
  H1    := fun n => if inI n then matMulF sc.z (r.H1 n) (w.γinv n) else r.H1 n
  H1inv := fun n => if inI n then matMulF sc.z (w.γ n) (r.H1inv n) else r.H1inv n
  H2    := fun n => if inI n then matMulF sc.z (r.H2 n) (w.γ n) else r.H2 n
  H2inv := fun n => if inI n then matMulF sc.z (w.γinv n) (r.H2inv n) else r.H2inv n
  L1    := fun n => if inI n then
      matMulF sc.y (matSub (r.L1 n) (matMulF sc.z (matMulF sc.z (r.H1 n) (w.γinv n)) (w.β n))) (w.αinv n)
    else r.L1 n
  L2    := fun n => if inI n then
      matAdd (matMulF sc.z (r.H2 n) (w.β n)) (matMulF sc.y (r.L2 n) (w.α n)) else r.L2 n

/-- Equality of two `PIRRand` tuples on all active matrix entries `< D, < y, < z, < N`. -/
def RandEq {F : Type} (sc : PIRScheme F) (r1 r2 : PIRRand F) : Prop :=
  MatEq sc.D sc.D r1.S1 r2.S1 ∧
  MatEq sc.D sc.D r1.S2 r2.S2 ∧
  (∀ n, n < sc.N →
    MatEq sc.y sc.y (r1.R1 n) (r2.R1 n) ∧
    MatEq sc.y sc.y (r1.R2 n) (r2.R2 n) ∧
    MatEq sc.z sc.z (r1.H1 n) (r2.H1 n) ∧
    MatEq sc.z sc.z (r1.H2 n) (r2.H2 n) ∧
    MatEq sc.z sc.y (r1.L1 n) (r2.L1 n) ∧
    MatEq sc.z sc.y (r1.L2 n) (r2.L2 n))

/-- **Theorem 2 (`pir_exact_t_privacy_bijection` over ANY `SimpleField F`):**
    Given a valid flag isomorphism `w` on colluding subset `inI`:
    1. `Ψ_I` preserves `ValidRand` (`ValidRand r → ValidRand (psiFwd r)`), and `Ψ_I^{-1}` preserves `ValidRand`.
    2. `Ψ_I` and `Ψ_I^{-1}` are exact two-sided inverses on `PIRRand` (`RandEq (psiInv (psiFwd r)) r`
       and `RandEq (psiFwd (psiInv r)) r`).
    3. For EVERY server `n ∈ I`, ALL FOUR query matrices sent to server `n` under `(θ = true, Ψ_I(r))`
       are **ENTRY-FOR-ENTRY IDENTICAL** to those under `(θ = false, r)`! -/
theorem pir_exact_t_privacy_bijection {F : Type} [SimpleField F] (sc : PIRScheme F)
    (inI : Nat → Bool) (w : FlagIsoWitness F) (hw : ValidFlagIso sc inI w) :
    (∀ r, ValidRand sc r → ValidRand sc (psiFwd sc inI w r) ∧ ValidRand sc (psiInv sc inI w r)) ∧
    (∀ r, RandEq sc (psiInv sc inI w (psiFwd sc inI w r)) r ∧
          RandEq sc (psiFwd sc inI w (psiInv sc inI w r)) r) ∧
    (∀ r n, n < sc.N → inI n = true →
      MatEq sc.y sc.D (qBlk1 sc true (psiFwd sc inI w r) n) (qBlk1 sc false r n) ∧
      MatEq sc.y sc.D (qBlk2 sc true (psiFwd sc inI w r) n) (qBlk2 sc false r n) ∧
      MatEq sc.z sc.D (qBlk3File1 sc true (psiFwd sc inI w r) n) (qBlk3File1 sc false r n) ∧
      MatEq sc.z sc.D (qBlk3File2 sc true (psiFwd sc inI w r) n) (qBlk3File2 sc false r n)) := by
  have hM_swap : IsMatInv sc.D w.Minv w.M := ⟨hw.1.2, hw.1.1⟩
  -- Helper: right-cancel `A * B * Binv = A` on `m × k`
  have hrc : ∀ {k : Nat} (A B Binv : Nat → Nat → F) (i j : Nat),
      j < k → MatEq k k (matMulF k B Binv) matIdF →
      matMulF k (matMulF k A B) Binv i j = A i j := by
    intro k A B Binv i j hj hBB
    rw [matMulF_assoc, matMulF_congr (fun _ _ => rfl) (fun t ht => hBB t j ht hj),
        matMulF_id_right k A hj]
  -- Helper: left-cancel `Binv * (B * A) = A`
  have hlc : ∀ {k : Nat} (Binv B A : Nat → Nat → F) (i j : Nat),
      i < k → MatEq k k (matMulF k Binv B) matIdF →
      matMulF k Binv (matMulF k B A) i j = A i j := by
    intro k Binv B A i j hi hBB
    rw [← matMulF_assoc, matMulF_congr (fun t ht => hBB i t hi ht) (fun _ _ => rfl),
        matMulF_id_left k A hi]
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: `psiFwd` and `psiInv` preserve `ValidRand`
    intro r hr
    constructor
    · refine ⟨isMatInv_mul hM_swap hr.1, isMatInv_mul hw.1 hr.2.1, ?_, ?_, ?_, ?_⟩
      · intro n hn; dsimp only [psiFwd]; split
        · rename_i hin; exact isMatInv_mul (hr.2.2.1 n hn) (hw.2 n hn hin).1
        · exact hr.2.2.1 n hn
      · intro n hn; dsimp only [psiFwd]; split
        · rename_i hin; have hα := (hw.2 n hn hin).1
          exact isMatInv_mul (hr.2.2.2.1 n hn) ⟨hα.2, hα.1⟩
        · exact hr.2.2.2.1 n hn
      · intro n hn; dsimp only [psiFwd]; split
        · rename_i hin; exact isMatInv_mul (hr.2.2.2.2.1 n hn) (hw.2 n hn hin).2.1
        · exact hr.2.2.2.2.1 n hn
      · intro n hn; dsimp only [psiFwd]; split
        · rename_i hin; have hγ := (hw.2 n hn hin).2.1
          exact isMatInv_mul (hr.2.2.2.2.2 n hn) ⟨hγ.2, hγ.1⟩
        · exact hr.2.2.2.2.2 n hn
    · refine ⟨isMatInv_mul hw.1 hr.1, isMatInv_mul hM_swap hr.2.1, ?_, ?_, ?_, ?_⟩
      · intro n hn; dsimp only [psiInv]; split
        · rename_i hin; have hα := (hw.2 n hn hin).1
          exact isMatInv_mul (hr.2.2.1 n hn) ⟨hα.2, hα.1⟩
        · exact hr.2.2.1 n hn
      · intro n hn; dsimp only [psiInv]; split
        · rename_i hin; exact isMatInv_mul (hr.2.2.2.1 n hn) (hw.2 n hn hin).1
        · exact hr.2.2.2.1 n hn
      · intro n hn; dsimp only [psiInv]; split
        · rename_i hin; have hγ := (hw.2 n hn hin).2.1
          exact isMatInv_mul (hr.2.2.2.2.1 n hn) ⟨hγ.2, hγ.1⟩
        · exact hr.2.2.2.2.1 n hn
      · intro n hn; dsimp only [psiInv]; split
        · rename_i hin; exact isMatInv_mul (hr.2.2.2.2.2 n hn) (hw.2 n hn hin).2.1
        · exact hr.2.2.2.2.2 n hn
  · -- Part 2: Two-sided bijection (`psiInv ∘ psiFwd = id` and `psiFwd ∘ psiInv = id`)
    intro r
    constructor
    · refine ⟨fun i j hi _ => hlc w.M w.Minv r.S1 i j hi hw.1.1,
              fun i j hi _ => hlc w.Minv w.M r.S2 i j hi hw.1.2, ?_⟩
      intro n hn
      by_cases hin : inI n = true
      · have ⟨hα, hγ, _, _⟩ := hw.2 n hn hin
        simp only [psiInv, psiFwd, hin, ↓reduceIte]
        refine ⟨fun i j _ hj => hrc (r.R1 n) (w.α n) (w.αinv n) i j hj hα.1,
                fun i j _ hj => hrc (r.R2 n) (w.αinv n) (w.α n) i j hj hα.2,
                fun i j _ hj => hrc (r.H1 n) (w.γ n) (w.γinv n) i j hj hγ.1,
                fun i j _ hj => hrc (r.H2 n) (w.γinv n) (w.γ n) i j hj hγ.2, ?_, ?_⟩
        · intro i j _ hj
          have hsub_eq : ∀ u, u < sc.y →
              matSub (matAdd (matMulF sc.z (r.H1 n) (w.β n)) (matMulF sc.y (r.L1 n) (w.α n)))
                (matMulF sc.z (matMulF sc.z (matMulF sc.z (r.H1 n) (w.γ n)) (w.γinv n)) (w.β n)) i u =
              matMulF sc.y (r.L1 n) (w.α n) i u := by
            intro u _
            dsimp only [matSub, matAdd]
            have hhc : matMulF sc.z (matMulF sc.z (matMulF sc.z (r.H1 n) (w.γ n)) (w.γinv n)) (w.β n) i u =
                matMulF sc.z (r.H1 n) (w.β n) i u := by
              apply sumR_congr; intro t ht; rw [hrc (r.H1 n) (w.γ n) (w.γinv n) i t ht hγ.1]
            rw [hhc, CommRing.sub_eq, CommRing.add_comm (matMulF sc.z (r.H1 n) (w.β n) i u),
                CommRing.add_assoc, CommRing.add_neg, add_zero]
          rw [matMulF_congr hsub_eq (fun _ _ => rfl)]
          exact hrc (r.L1 n) (w.α n) (w.αinv n) i j hj hα.1
        · intro i j _ hj
          dsimp only [matAdd]
          rw [hrc (matSub (r.L2 n) (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (w.β n)))
                  (w.αinv n) (w.α n) i j hj hα.2]
          dsimp only [matSub]
          rw [CommRing.sub_eq, CommRing.add_comm (r.L2 n i j), ← CommRing.add_assoc,
              CommRing.add_neg, CommRing.zero_add]
      · simp only [psiInv, psiFwd, hin, Bool.false_eq_true, ↓reduceIte]
        exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
               fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    · refine ⟨fun i j hi _ => hlc w.Minv w.M r.S1 i j hi hw.1.2,
              fun i j hi _ => hlc w.M w.Minv r.S2 i j hi hw.1.1, ?_⟩
      intro n hn
      by_cases hin : inI n = true
      · have ⟨hα, hγ, _, _⟩ := hw.2 n hn hin
        simp only [psiFwd, psiInv, hin, ↓reduceIte]
        refine ⟨fun i j _ hj => hrc (r.R1 n) (w.αinv n) (w.α n) i j hj hα.2,
                fun i j _ hj => hrc (r.R2 n) (w.α n) (w.αinv n) i j hj hα.1,
                fun i j _ hj => hrc (r.H1 n) (w.γinv n) (w.γ n) i j hj hγ.2,
                fun i j _ hj => hrc (r.H2 n) (w.γ n) (w.γinv n) i j hj hγ.1, ?_, ?_⟩
        · intro i j _ hj
          dsimp only [matAdd]
          rw [hrc (matSub (r.L1 n) (matMulF sc.z (matMulF sc.z (r.H1 n) (w.γinv n)) (w.β n)))
                  (w.αinv n) (w.α n) i j hj hα.2]
          dsimp only [matSub]
          rw [CommRing.sub_eq, CommRing.add_comm (r.L1 n i j), ← CommRing.add_assoc,
              CommRing.add_neg, CommRing.zero_add]
        · intro i j _ hj
          have hsub_eq : ∀ u, u < sc.y →
              matSub (matAdd (matMulF sc.z (r.H2 n) (w.β n)) (matMulF sc.y (r.L2 n) (w.α n)))
                (matMulF sc.z (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γ n)) (w.γinv n)) (w.β n)) i u =
              matMulF sc.y (r.L2 n) (w.α n) i u := by
            intro u _
            dsimp only [matSub, matAdd]
            have hhc : matMulF sc.z (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γ n)) (w.γinv n)) (w.β n) i u =
                matMulF sc.z (r.H2 n) (w.β n) i u := by
              apply sumR_congr; intro t ht; rw [hrc (r.H2 n) (w.γ n) (w.γinv n) i t ht hγ.1]
            rw [hhc, CommRing.sub_eq, CommRing.add_comm (matMulF sc.z (r.H2 n) (w.β n) i u),
                CommRing.add_assoc, CommRing.add_neg, add_zero]
          rw [matMulF_congr hsub_eq (fun _ _ => rfl)]
          exact hrc (r.L2 n) (w.α n) (w.αinv n) i j hj hα.1
      · simp only [psiFwd, psiInv, hin, Bool.false_eq_true, ↓reduceIte]
        exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
               fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  · -- Part 3: Entry-for-entry query identity on EVERY colluding server `n ∈ I`!
    intro r n hn hin
    have ⟨hα, hγ, hPM, hCM⟩ := hw.2 n hn hin
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Block 1: `(R1 α) Q (M^{-1} S1) = R1 P S1`
      intro i j _ _
      unfold qBlk1
      simp only [psiFwd, hin, ↓reduceIte, Bool.false_eq_true]
      rw [← matMulF_assoc]
      have h1 : ∀ u, u < sc.D →
          matMulF sc.y (matMulF sc.y (r.R1 n) (w.α n)) (sc.Q n) i u =
          matMulF sc.D (matMulF sc.y (r.R1 n) (sc.P n)) w.M i u := by
        intro u hu
        rw [matMulF_assoc sc.y sc.y (r.R1 n) (w.α n) (sc.Q n),
            matMulF_congr (fun _ _ => rfl) (fun v hv => (hPM v u hv hu).symm), ← matMulF_assoc]
      have h2 : ∀ t, t < sc.D →
          matMulF sc.D (matMulF sc.y (matMulF sc.y (r.R1 n) (w.α n)) (sc.Q n)) w.Minv i t =
          matMulF sc.y (r.R1 n) (sc.P n) i t := by
        intro t ht
        rw [matMulF_congr h1 (fun _ _ => rfl)]
        exact hrc (matMulF sc.y (r.R1 n) (sc.P n)) w.M w.Minv i t ht hw.1.1
      exact matMulF_congr h2 (fun _ _ => rfl)
    · -- Block 2: `(R2 α^{-1}) P (M S2) = R2 Q S2`
      intro i j _ _
      unfold qBlk2
      simp only [psiFwd, hin, ↓reduceIte, Bool.false_eq_true]
      rw [← matMulF_assoc]
      have h1 : ∀ t, t < sc.D →
          matMulF sc.D (matMulF sc.y (matMulF sc.y (r.R2 n) (w.αinv n)) (sc.P n)) w.M i t =
          matMulF sc.y (r.R2 n) (sc.Q n) i t := by
        intro t ht
        rw [matMulF_assoc sc.y sc.D (matMulF sc.y (r.R2 n) (w.αinv n)) (sc.P n) w.M,
            matMulF_congr (fun _ _ => rfl) (fun u hu => hPM u t hu ht), ← matMulF_assoc]
        apply sumR_congr; intro u hu
        congr 1
        exact hrc (r.R2 n) (w.αinv n) (w.α n) i u hu hα.2
      exact matMulF_congr h1 (fun _ _ => rfl)
    · -- Block 3 File 1: `((H1 γ) D + (H1 β + L1 α) Q) (M^{-1} S1) = (H1 C + L1 P) S1`
      intro i j _ _
      unfold qBlk3File1
      simp only [psiFwd, hin, ↓reduceIte, Bool.false_eq_true]
      rw [← matMulF_assoc]
      have h1 : ∀ u, u < sc.D →
          matAdd (matMulF sc.z (matMulF sc.z (r.H1 n) (w.γ n)) (sc.Dblk n))
            (matMulF sc.y (matAdd (matMulF sc.z (r.H1 n) (w.β n)) (matMulF sc.y (r.L1 n) (w.α n))) (sc.Q n)) i u =
          matMulF sc.D (matAdd (matMulF sc.z (r.H1 n) (sc.C n)) (matMulF sc.y (r.L1 n) (sc.P n))) w.M i u := by
        intro u hu
        dsimp only [matAdd]
        rw [matMulF_add_left, matMulF_assoc sc.z sc.z (r.H1 n) (w.γ n) (sc.Dblk n),
            matMulF_assoc sc.z sc.y (r.H1 n) (w.β n) (sc.Q n),
            matMulF_assoc sc.y sc.y (r.L1 n) (w.α n) (sc.Q n),
            ← CommRing.add_assoc, ← matMulF_add_right]
        have hC : matMulF sc.z (r.H1 n)
            (matAdd (matMulF sc.z (w.γ n) (sc.Dblk n)) (matMulF sc.y (w.β n) (sc.Q n))) i u =
            matMulF sc.D (matMulF sc.z (r.H1 n) (sc.C n)) w.M i u := by
          rw [matMulF_congr (fun _ _ => rfl) (fun v hv => (hCM v u hv hu).symm), ← matMulF_assoc]
        have hP : matMulF sc.y (r.L1 n) (matMulF sc.y (w.α n) (sc.Q n)) i u =
            matMulF sc.D (matMulF sc.y (r.L1 n) (sc.P n)) w.M i u := by
          rw [matMulF_congr (fun _ _ => rfl) (fun v hv => (hPM v u hv hu).symm), ← matMulF_assoc]
        rw [hC, hP, ← matMulF_add_left]
      have h2 : ∀ t, t < sc.D →
          matMulF sc.D
            (matAdd (matMulF sc.z (matMulF sc.z (r.H1 n) (w.γ n)) (sc.Dblk n))
              (matMulF sc.y (matAdd (matMulF sc.z (r.H1 n) (w.β n)) (matMulF sc.y (r.L1 n) (w.α n))) (sc.Q n)))
            w.Minv i t =
          matAdd (matMulF sc.z (r.H1 n) (sc.C n)) (matMulF sc.y (r.L1 n) (sc.P n)) i t := by
        intro t ht
        rw [matMulF_congr h1 (fun _ _ => rfl)]
        exact hrc (matAdd (matMulF sc.z (r.H1 n) (sc.C n)) (matMulF sc.y (r.L1 n) (sc.P n))) w.M w.Minv i t ht hw.1.1
      exact matMulF_congr h2 (fun _ _ => rfl)
    · -- Block 3 File 2: `((H2 γ^{-1}) C + (L2 - H2 γ^{-1} β) α^{-1} P) (M S2) = (H2 D + L2 Q) S2`
      intro i j _ _
      unfold qBlk3File2
      simp only [psiFwd, hin, ↓reduceIte, Bool.false_eq_true]
      rw [← matMulF_assoc]
      have h1 : ∀ t, t < sc.D →
          matMulF sc.D
            (matAdd (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (sc.C n))
              (matMulF sc.y
                (matMulF sc.y (matSub (r.L2 n) (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (w.β n))) (w.αinv n))
                (sc.P n))) w.M i t =
          matAdd (matMulF sc.z (r.H2 n) (sc.Dblk n)) (matMulF sc.y (r.L2 n) (sc.Q n)) i t := by
        intro t ht
        rw [matMulF_add_left, matMulF_assoc sc.z sc.D _ (sc.C n) w.M,
            matMulF_assoc sc.y sc.D _ (sc.P n) w.M]
        have hCpart : matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (matMulF sc.D (sc.C n) w.M) i t =
            matMulF sc.z (r.H2 n) (sc.Dblk n) i t +
            matMulF sc.y (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (w.β n)) (sc.Q n) i t := by
          rw [matMulF_congr (fun _ _ => rfl) (fun u hu => hCM u t hu ht), matMulF_add_right,
              ← matMulF_assoc sc.z sc.z _ (w.γ n) (sc.Dblk n),
              ← matMulF_assoc sc.z sc.y _ (w.β n) (sc.Q n)]
          congr 1
          apply sumR_congr; intro u hu
          congr 1
          exact hrc (r.H2 n) (w.γinv n) (w.γ n) i u hu hγ.2
        have hPpart : matMulF sc.y
            (matMulF sc.y (matSub (r.L2 n) (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (w.β n))) (w.αinv n))
            (matMulF sc.D (sc.P n) w.M) i t =
            matMulF sc.y (r.L2 n) (sc.Q n) i t -
            matMulF sc.y (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (w.β n)) (sc.Q n) i t := by
          rw [matMulF_congr (fun _ _ => rfl) (fun u hu => hPM u t hu ht), ← matMulF_assoc]
          have hsub_cancel : ∀ u, u < sc.y →
              matMulF sc.y (matMulF sc.y (matSub (r.L2 n)
                (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (w.β n))) (w.αinv n)) (w.α n) i u =
              matSub (r.L2 n) (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (w.β n)) i u :=
            fun u hu => hrc _ (w.αinv n) (w.α n) i u hu hα.2
          rw [matMulF_congr hsub_cancel (fun _ _ => rfl), matMulF_sub_left]
        rw [hCpart, hPpart]
        dsimp only [matAdd]
        rw [CommRing.sub_eq, CommRing.add_assoc,
            CommRing.add_comm (matMulF sc.y (matMulF sc.z (matMulF sc.z (r.H2 n) (w.γinv n)) (w.β n)) (sc.Q n) i t),
            CommRing.add_assoc (matMulF sc.y (r.L2 n) (sc.Q n) i t),
            neg_add, add_zero]
      exact matMulF_congr h1 (fun _ _ => rfl)

end
end TriadFrontier.PIRProtocol
