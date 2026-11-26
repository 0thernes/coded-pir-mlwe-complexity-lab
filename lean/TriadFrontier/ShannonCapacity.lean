module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore
public import TriadFrontier.KoszulTensor

/-!
# Zero-Error Shannon Capacity of Graphs (`CS-CMP-012` ↔ `CS-053` ↔ `CS-004`, Theorem `T3j`)

Zero-Mathlib, zero-real-number, first-principles Lean 4.35.0 formalization bridging
zero-error information theory with matrix/tensor rank:
1. **Field-Universal Haemers (1979) Rank Bound (`haemers_strong_pow_rank_bound`):**
   Over **EVERY `SimpleField F` (including `F_2`)**, if `M ∈ F^{n × n}` fits graph `G`
   (`M i i ≠ 0` and `M i j = 0` on non-edges) and factors through inner dimension `r`, then
   EVERY independent set `S` in the `t`-th strong product `G^{⊠ t}` satisfies **`|S| ≤ r ^ t`**.
2. **Exact Lovász (1979) Pentagon Theorem `Θ(C_5) = √5` in Exact `Z[√5]` Sum-of-Squares Arithmetic:**
   - **Upper bound (`lovasz_c5_strong_pow_upper`):** Exact 2-term `Z[√5]` SOS factorization of
     `40(2√5 I_5 - 2 B_{C_5})` and exact 5-term `Z[√5]` SOS factorization of
     `40(2√5 I_5 + 2 B_{C_5})`, lifted by Kronecker tensor-product PSD closure to prove
     **`k * k ≤ 5 ^ t`** for EVERY `t ≥ 1` and EVERY independent set of size `k` in `C_5^{⊠ t}`!
   - **Lower bound (`c5_even_pow_indep_ge`):** Explicit 5-element independent set in `C_5^{⊠ 2}`
     lifted to **`α(C_5^{⊠ 2m}) ≥ 5 ^ m`** for EVERY `m ≥ 1`!
3. **Exact `C_7` Minimum Haemers Rank = 4 Over EVERY Field (`c7_exact_min_haemers_rank_four`):**
   Explicit 10-element independent set in `C_7^{⊠ 2}` lifts to `α(C_7^{⊠ 2m}) ≥ 10 ^ m`,
   ruling out any rank-`≤ 3` fitting matrix (`10 > 3^2 = 9`) over ANY field `F`, while an explicit
   4-clique cover achieves rank 4 over EVERY field `F` (leaving `Θ(C_7) ∈ [√10, ϑ(C_7)]` OPEN!).
-/

namespace TriadFrontier.ShannonCapacity

open TriadFrontier.AlgebraCore
open TriadFrontier.KoszulTensor

@[expose] public section

-- ============================================================================
-- Section 1: Graphs, Strong Products `G^{⊠ t}`, & Field-Universal Haemers Bound
-- ============================================================================

/-- Extract base-`n` digit `d` of `x : Nat`. -/
def digit (n x d : Nat) : Nat := (x / n ^ d) % n

/-- Product of `t` ring elements `f 0 * f 1 * ... * f (t-1)`. -/
def prodR {R : Type} [CommRing R] : Nat → (Nat → R) → R
  | 0, _ => 1
  | k + 1, f => prodR k f * f k

theorem prodR_congr {R : Type} [CommRing R] {t : Nat} {f g : Nat → R}
    (h : ∀ d, d < t → f d = g d) : prodR t f = prodR t g := by
  induction t with
  | zero => rfl
  | succ k ih =>
    simp only [prodR]
    rw [ih (fun d hd => h d (Nat.lt_succ_of_lt hd)), h k (Nat.lt_succ_self k)]

theorem prodR_zero_of_exists {R : Type} [CommRing R] :
    ∀ (t : Nat) (f : Nat → R), (∃ d, d < t ∧ f d = 0) → prodR t f = 0
  | 0, _, ⟨_, h, _⟩ => by omega
  | k + 1, f, ⟨d, hd, hz⟩ => by
    simp only [prodR]
    cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hd) with
    | inl heq => subst heq; rw [hz, mul_zero]
    | inr hlt => rw [prodR_zero_of_exists k f ⟨d, hlt, hz⟩, zero_mul]

theorem prodR_ne_zero {F : Type} [SimpleField F] :
    ∀ (t : Nat) (f : Nat → F), (∀ d, d < t → f d ≠ 0) → prodR t f ≠ 0
  | 0, _, _ => Ne.symm SimpleField.zero_ne_one
  | k + 1, f, h => by
    simp only [prodR]
    have h1 := prodR_ne_zero k f (fun d hd => h d (Nat.lt_succ_of_lt hd))
    have h2 := h k (Nat.lt_succ_self k)
    intro hz
    have hinv := congrArg (fun z => z * SimpleField.inv (f k)) hz
    rw [zero_mul, CommRing.mul_assoc, SimpleField.mul_inv_cancel (f k) h2, mul_one] at hinv
    exact h1 hinv

/-- Recursive coordinate check for strong-product adjacency `G^{⊠ t}`. -/
def strongPowAdjGo (n : Nat) (adj : Nat → Nat → Bool) (x y : Nat) : Nat → Bool
  | 0 => true
  | d + 1 =>
    let xd := digit n x d; let yd := digit n y d
    (xd == yd || adj xd yd) && strongPowAdjGo n adj x y d

/-- Strong-product adjacency on `G^{⊠ t}` (vertices encoded in `[0, n^t)`):
    two distinct vertices `x ≠ y` are adjacent iff in every coordinate `d < t`,
    either `digit n x d = digit n y d` or `adj (digit n x d) (digit n y d) = true`. -/
def strongPowAdj (n : Nat) (adj : Nat → Nat → Bool) (t x y : Nat) : Bool :=
  if x == y then false else strongPowAdjGo n adj x y t

/-- An independent set of size `k` in graph `(N, adj)` given by an injective map `f : [k] → [N]`. -/
def IsIndepSet (N : Nat) (adj : Nat → Nat → Bool) (k : Nat) (f : Nat → Nat) : Prop :=
  (∀ i, i < k → f i < N) ∧
  (∀ i j, i < k → j < k → i ≠ j → f i ≠ f j) ∧
  (∀ i j, i < k → j < k → i ≠ j → adj (f i) (f j) = false)

/-- Matrix `M` fits `(n, adj)` over `F`: nonzero diagonal, zero on non-edges. -/
def FitsGraph {F : Type} [SimpleField F] (n : Nat) (adj : Nat → Nat → Bool)
    (M : Nat → Nat → F) : Prop :=
  (∀ i, i < n → M i i ≠ 0) ∧
  (∀ i j, i < n → j < n → i ≠ j → adj i j = false → M i j = 0)

theorem sumR_mul_factor {R : Type} [CommRing R] (A B : Nat) (f g : Nat → R) :
    sumR (A * B) (fun s => f (s / B) * g (s % B)) = sumR A f * sumR B g := by
  induction A with
  | zero => simp [sumR, zero_mul]
  | succ a ih =>
    have hsplit : (a + 1) * B = a * B + B := Nat.succ_mul a B
    rw [hsplit]
    have hadd : ∀ (base len : Nat) (h : Nat → R),
        sumR (base + len) h = sumR base h + sumR len (fun j => h (base + j)) := by
      intro base len h
      induction len with
      | zero => simp [sumR, add_zero]
      | succ l ihl =>
        rw [Nat.add_succ, sumR, ihl, sumR, CommRing.add_assoc]
    rw [hadd (a * B) B, ih, sumR, right_distrib]
    congr 1
    cases B with
    | zero => simp [sumR, mul_zero]
    | succ b' =>
      have hB : 0 < b' + 1 := Nat.zero_lt_succ b'
      rw [sumR_mul_left]
      apply sumR_congr
      intro j hj
      have hd : (a * (b' + 1) + j) / (b' + 1) = a := by
        rw [Nat.mul_comm a (b' + 1), Nat.mul_add_div hB, Nat.div_eq_of_lt hj, Nat.add_zero]
      have hm : (a * (b' + 1) + j) % (b' + 1) = j := by
        rw [Nat.mul_comm a (b' + 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      rw [hd, hm]

/-- Kronecker-power factorization: `(U · V)^{⊗ t} = U^{⊗ t} · V^{⊗ t}` through inner dim `r^t`! -/
theorem kronecker_pow_factor {R : Type} [CommRing R] (n r : Nat)
    (U V M : Nat → Nat → R)
    (hUV : ∀ i j, i < n → j < n → sumR r (fun s => U i s * V s j) = M i j) :
    ∀ (t x y : Nat), x < n ^ t → y < n ^ t →
      sumR (r ^ t) (fun s =>
        prodR t (fun d => U (digit n x d) (digit r s d)) *
        prodR t (fun d => V (digit r s d) (digit n y d))) =
      prodR t (fun d => M (digit n x d) (digit n y d))
  | 0, _, _, _, _ => by simp [sumR, prodR, CommRing.zero_add, mul_one]
  | t + 1, x, y, hx, hy => by
    have hn : 0 < n := by
      cases n with
      | zero => simp [Nat.zero_pow (Nat.zero_lt_succ t)] at hx
      | succ n' => exact Nat.zero_lt_succ n'
    -- Split `s < r^(t+1) = r^t * r` as `s / r` (wait: `r^(t+1) = r^t * r`!)
    -- Actually `digit r s t = s / r^t % r` and for `d < t`, `digit r s d = digit r (s % r^t) d`!
    -- So split `r^(t+1) = r * r^t` via `s_hi = s / r^t < r` and `s_lo = s % r^t < r^t`!
    have hpow_comm : r ^ (t + 1) = r * r ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow_comm]
    cases r with
    | zero =>
      simp only [Nat.zero_mul, sumR]
      have hx0 : digit n x t < n := Nat.mod_lt _ hn
      have hy0 : digit n y t < n := Nat.mod_lt _ hn
      have hM0 : M (digit n x t) (digit n y t) = 0 := by
        rw [← hUV _ _ hx0 hy0]; rfl
      simp [prodR, hM0, mul_zero]
    | succ r' =>
      let R' := r' + 1
      have hRpos : 0 < R' := Nat.zero_lt_succ r'
      have hRtpos : 0 < R' ^ t := Nat.pow_pos hRpos
      have hsplit : sumR (R' * R' ^ t) (fun s =>
          prodR (t + 1) (fun d => U (digit n x d) (digit R' s d)) *
          prodR (t + 1) (fun d => V (digit R' s d) (digit n y d))) =
          sumR (R' * R' ^ t) (fun s =>
            (U (digit n x t) (s / R' ^ t) * V (s / R' ^ t) (digit n y t)) *
            (prodR t (fun d => U (digit n x d) (digit R' (s % R' ^ t) d)) *
             prodR t (fun d => V (digit R' (s % R' ^ t) d) (digit n y d)))) := by
        apply sumR_congr
        intro s hs
        have htop : digit R' s t = s / R' ^ t := by
          unfold digit
          have hdiv : s / R' ^ t < R' := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hs)
          exact Nat.mod_eq_of_lt hdiv
        have hlow : ∀ d, d < t → digit R' s d = digit R' (s % R' ^ t) d := by
          intro d hd
          unfold digit
          have hdvd : R' ^ (d + 1) ∣ R' ^ t := Nat.pow_dvd_pow R' hd
          obtain ⟨q, hq⟩ := hdvd
          have hdecomp := Nat.div_add_mod s (R' ^ t)
          have hpowd : R' ^ t = R' ^ d * (R' * q) := by
            rw [hq, Nat.pow_succ, Nat.mul_assoc]
          have hdiv_eq : s / R' ^ d = (R' * q) * (s / R' ^ t) + (s % R' ^ t) / R' ^ d := by
            have hpdpos : 0 < R' ^ d := Nat.pow_pos hRpos
            have hs_eq : s = R' ^ d * ((R' * q) * (s / R' ^ t)) + s % R' ^ t := by
              calc s = R' ^ t * (s / R' ^ t) + s % R' ^ t := hdecomp.symm
                _ = R' ^ d * ((R' * q) * (s / R' ^ t)) + s % R' ^ t := by rw [hpowd, Nat.mul_assoc]
            calc s / R' ^ d
                = (R' ^ d * ((R' * q) * (s / R' ^ t)) + s % R' ^ t) / R' ^ d := congrArg (· / R' ^ d) hs_eq
              _ = (R' * q) * (s / R' ^ t) + (s % R' ^ t) / R' ^ d := Nat.mul_add_div hpdpos _ _
          rw [hdiv_eq, Nat.mul_assoc, Nat.mul_add_mod]
        simp only [prodR, htop]
        have hl1 := prodR_congr (fun d hd => by rw [hlow d hd]) (f := fun d => U (digit n x d) (digit R' s d))
        have hl2 := prodR_congr (fun d hd => by rw [hlow d hd]) (f := fun d => V (digit R' s d) (digit n y d))
        rw [hl1, hl2]
        let A := prodR t (fun d => U (digit n x d) (digit R' (s % R' ^ t) d))
        let B := prodR t (fun d => V (digit R' (s % R' ^ t) d) (digit n y d))
        let u := U (digit n x t) (s / R' ^ t)
        let v := V (s / R' ^ t) (digit n y t)
        change (A * u) * (B * v) = (u * v) * (A * B)
        calc (A * u) * (B * v)
            = A * (u * (B * v)) := CommRing.mul_assoc A u (B * v)
          _ = A * ((u * v) * B) := by
              rw [← CommRing.mul_assoc u B v, CommRing.mul_comm u B,
                  CommRing.mul_assoc B u v, CommRing.mul_comm B (u * v)]
          _ = (u * v) * (A * B) := by
              rw [← CommRing.mul_assoc A (u * v) B, CommRing.mul_comm A (u * v),
                  CommRing.mul_assoc (u * v) A B]
      rw [hsplit]
      have hfac := sumR_mul_factor R' (R' ^ t)
        (fun i => U (digit n x t) i * V i (digit n y t))
        (fun j => prodR t (fun d => U (digit n x d) (digit R' j d)) *
                  prodR t (fun d => V (digit R' j d) (digit n y d)))
      rw [hfac]
      have hxt : digit n x t < n := Nat.mod_lt _ hn
      have hyt : digit n y t < n := Nat.mod_lt _ hn
      rw [hUV _ _ hxt hyt]
      -- Apply IH on `x % n^t` and `y % n^t`!
      have hx' : x % n ^ t < n ^ t := Nat.mod_lt x (Nat.pow_pos hn)
      have hy' : y % n ^ t < n ^ t := Nat.mod_lt y (Nat.pow_pos hn)
      have hdig_x : ∀ d, d < t → digit n x d = digit n (x % n ^ t) d := by
        intro d hd
        unfold digit
        obtain ⟨q, hq⟩ := Nat.pow_dvd_pow n hd
        have hdecomp := Nat.div_add_mod x (n ^ t)
        have hpowd : n ^ t = n ^ d * (n * q) := by rw [hq, Nat.pow_succ, Nat.mul_assoc]
        have hs_eq : x = n ^ d * ((n * q) * (x / n ^ t)) + x % n ^ t := by
          calc x = n ^ t * (x / n ^ t) + x % n ^ t := hdecomp.symm
            _ = n ^ d * ((n * q) * (x / n ^ t)) + x % n ^ t := by rw [hpowd, Nat.mul_assoc]
        have hdiv : x / n ^ d = (n * q) * (x / n ^ t) + (x % n ^ t) / n ^ d := by
          calc x / n ^ d = (n ^ d * ((n * q) * (x / n ^ t)) + x % n ^ t) / n ^ d := congrArg (· / n ^ d) hs_eq
            _ = (n * q) * (x / n ^ t) + (x % n ^ t) / n ^ d := Nat.mul_add_div (Nat.pow_pos hn) _ _
        rw [hdiv, Nat.mul_assoc, Nat.mul_add_mod]
      have hdig_y : ∀ d, d < t → digit n y d = digit n (y % n ^ t) d := by
        intro d hd
        unfold digit
        obtain ⟨q, hq⟩ := Nat.pow_dvd_pow n hd
        have hdecomp := Nat.div_add_mod y (n ^ t)
        have hpowd : n ^ t = n ^ d * (n * q) := by rw [hq, Nat.pow_succ, Nat.mul_assoc]
        have hs_eq : y = n ^ d * ((n * q) * (y / n ^ t)) + y % n ^ t := by
          calc y = n ^ t * (y / n ^ t) + y % n ^ t := hdecomp.symm
            _ = n ^ d * ((n * q) * (y / n ^ t)) + y % n ^ t := by rw [hpowd, Nat.mul_assoc]
        have hdiv : y / n ^ d = (n * q) * (y / n ^ t) + (y % n ^ t) / n ^ d := by
          calc y / n ^ d = (n ^ d * ((n * q) * (y / n ^ t)) + y % n ^ t) / n ^ d := congrArg (· / n ^ d) hs_eq
            _ = (n * q) * (y / n ^ t) + (y % n ^ t) / n ^ d := Nat.mul_add_div (Nat.pow_pos hn) _ _
        rw [hdiv, Nat.mul_assoc, Nat.mul_add_mod]
      have hih := kronecker_pow_factor n R' U V M hUV t (x % n ^ t) (y % n ^ t) hx' hy'
      have hcong : sumR (R' ^ t) (fun s =>
          prodR t (fun d => U (digit n x d) (digit R' s d)) *
          prodR t (fun d => V (digit R' s d) (digit n y d))) =
          sumR (R' ^ t) (fun s =>
          prodR t (fun d => U (digit n (x % n ^ t) d) (digit R' s d)) *
          prodR t (fun d => V (digit R' s d) (digit n (y % n ^ t) d))) := by
        apply sumR_congr; intro s _
        have hx1 := prodR_congr (f := fun d => U (digit n x d) (digit R' s d)) (fun d hd => by rw [hdig_x d hd])
        have hy1 := prodR_congr (f := fun d => V (digit R' s d) (digit n y d)) (fun d hd => by rw [hdig_y d hd])
        rw [hx1, hy1]
      rw [hcong, hih]
      simp only [prodR]
      have hxy := prodR_congr (f := fun d => M (digit n x d) (digit n y d)) (fun d hd => by rw [hdig_x d hd, hdig_y d hd])
      rw [hxy, CommRing.mul_comm]

theorem strongPowAdj_false_exists_nonedge (n : Nat) (adj : Nat → Nat → Bool)
    (t x y : Nat) (hne : x ≠ y) (hfalse : strongPowAdj n adj t x y = false) :
    ∃ d, d < t ∧ digit n x d ≠ digit n y d ∧ adj (digit n x d) (digit n y d) = false := by
  unfold strongPowAdj at hfalse
  have hbeq : (x == y) = false := beq_false_of_ne hne
  simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hfalse
  have hgo : ∀ m, strongPowAdjGo n adj x y m = false →
      ∃ d, d < m ∧ digit n x d ≠ digit n y d ∧ adj (digit n x d) (digit n y d) = false := by
    intro m
    induction m with
    | zero => intro h; simp [strongPowAdjGo] at h
    | succ m' ih =>
      intro h
      simp only [strongPowAdjGo] at h
      cases h1 : (digit n x m' == digit n y m' || adj (digit n x m') (digit n y m'))
      · have hne' : digit n x m' ≠ digit n y m' := by
          intro heq; simp [heq] at h1
        have hadj : adj (digit n x m') (digit n y m') = false := by
          cases h2 : adj (digit n x m') (digit n y m')
          · rfl
          · simp [h2] at h1
        exact ⟨m', Nat.lt_succ_self m', hne', hadj⟩
      · rw [h1, Bool.true_and] at h
        obtain ⟨d, hd, hne', hadj⟩ := ih h
        exact ⟨d, Nat.lt_succ_of_lt hd, hne', hadj⟩
  exact hgo t hfalse

/-- **Field-Universal Haemers (1979) Rank Bound:**
    Over **EVERY `SimpleField F`**, any rank-`r` fitting matrix `M = U · V` for `(n, adj)`
    bounds every independent set `S` in `G^{⊠ t}` by **`|S| ≤ r ^ t`**! -/
theorem haemers_strong_pow_rank_bound {F : Type} [SimpleField F]
    (n r t k : Nat) (adj : Nat → Nat → Bool)
    (U V M : Nat → Nat → F) (f : Nat → Nat)
    (hUV : ∀ i j, i < n → j < n → sumR r (fun s => U i s * V s j) = M i j)
    (hFit : FitsGraph n adj M)
    (hInd : IsIndepSet (n ^ t) (strongPowAdj n adj t) k f) :
    k ≤ r ^ t := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k' =>
    cases n with
    | zero =>
      cases t with
      | zero =>
        -- `n = 0, t = 0`: `0^0 = 1`, so `k' + 1 ≤ 1` (`f 0 < 1` and `f` injective!) and `r^0 = 1`!
        have hk0 : k' = 0 := by
          by_cases h0 : k' = 0
          · exact h0
          · have h1 := hInd.1 0 (Nat.zero_lt_succ k')
            have h2 := hInd.1 1 (by omega)
            have hne := hInd.2.1 0 1 (Nat.zero_lt_succ k') (by omega) (by decide)
            simp at h1 h2; omega
        subst hk0; simp
      | succ t' =>
        have hf0 := hInd.1 0 (Nat.zero_lt_succ k')
        simp [Nat.zero_pow (Nat.zero_lt_succ t')] at hf0
    | succ n' =>
    have hn : 0 < n' + 1 := Nat.zero_lt_succ n'
    let diagVal (i : Nat) : F := prodR t (fun d => M (digit (n' + 1) (f i) d) (digit (n' + 1) (f i) d))
    have hdiag_ne : ∀ i, i < k' + 1 → diagVal i ≠ 0 := fun i _ =>
      prodR_ne_zero t _ (fun d _ => hFit.1 (digit (n' + 1) (f i) d) (Nat.mod_lt _ hn))
    let P : Nat → Nat → F := fun i s =>
      SimpleField.inv (diagVal i) * prodR t (fun d => U (digit (n' + 1) (f i) d) (digit r s d))
    let Q : Nat → Nat → F := fun s j =>
      prodR t (fun d => V (digit r s d) (digit (n' + 1) (f j) d))
    apply matRankFactor_le (r ^ t) (k' + 1) P Q
    intro i j hi hj
    unfold matMulF
    have hpull : sumR (r ^ t) (fun s => P i s * Q s j) =
        SimpleField.inv (diagVal i) *
        sumR (r ^ t) (fun s =>
          prodR t (fun d => U (digit (n' + 1) (f i) d) (digit r s d)) *
          prodR t (fun d => V (digit r s d) (digit (n' + 1) (f j) d))) := by
      rw [sumR_mul_left]
      apply sumR_congr; intro s _; dsimp only [P, Q]; rw [CommRing.mul_assoc]
    rw [hpull, kronecker_pow_factor (n' + 1) r U V M hUV t (f i) (f j) (hInd.1 i hi) (hInd.1 j hj)]
    unfold matIdF
    by_cases heq : i = j
    · subst heq
      simp only [↓reduceIte]
      rw [CommRing.mul_comm, SimpleField.mul_inv_cancel (diagVal i) (hdiag_ne i hi)]
    · simp only [heq, ↓reduceIte]
      have hne_f := hInd.2.1 i j hi hj heq
      have hfalse := hInd.2.2 i j hi hj heq
      obtain ⟨d, hd, hne_d, hadj_d⟩ := strongPowAdj_false_exists_nonedge (n' + 1) adj t (f i) (f j) hne_f hfalse
      have hMz : M (digit (n' + 1) (f i) d) (digit (n' + 1) (f j) d) = 0 :=
        hFit.2 _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) hne_d hadj_d
      rw [prodR_zero_of_exists t _ ⟨d, hd, hMz⟩, mul_zero]

-- ============================================================================
-- Section 2: Exact `Z[√5]` Ring & Sum-of-Squares Proof of Lovász `Θ(C_5) = √5`
-- ============================================================================

/-- Exact quadratic integer ring `Z[√5]`, representing `a + b√5`. -/
structure ZSqrt5 where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace ZSqrt5

def zero : ZSqrt5 := ⟨0, 0⟩
def one : ZSqrt5 := ⟨1, 0⟩
def sqrt5 : ZSqrt5 := ⟨0, 1⟩
def ofInt (n : Int) : ZSqrt5 := ⟨n, 0⟩
def add (x y : ZSqrt5) : ZSqrt5 := ⟨x.a + y.a, x.b + y.b⟩
def neg (x : ZSqrt5) : ZSqrt5 := ⟨-x.a, -x.b⟩
def sub (x y : ZSqrt5) : ZSqrt5 := ⟨x.a - y.a, x.b - y.b⟩
def mul (x y : ZSqrt5) : ZSqrt5 := ⟨x.a * y.a + 5 * x.b * y.b, x.a * y.b + x.b * y.a⟩

theorem neg_add_ring {R : Type} [CommRing R] (a b : R) : -(a + b) = -a + -b := by
  have hsum : (a + b) + (-a + -b) = 0 := by
    rw [CommRing.add_assoc a b (-a + -b), ← CommRing.add_assoc b (-a) (-b),
        CommRing.add_comm b (-a), CommRing.add_assoc (-a) b (-b),
        CommRing.add_neg, add_zero, CommRing.add_neg]
  exact (neg_eq_of_add_eq_zero hsum).symm

theorem mul_sub_ring {R : Type} [CommRing R] (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [CommRing.sub_eq, CommRing.left_distrib, mul_neg, ← CommRing.sub_eq]

instance : CommRing ZSqrt5 where
  zero := zero
  one := one
  add := add
  neg := neg
  sub := sub
  mul := mul
  add_comm x y := by
    cases x with | mk xa xb => cases y with | mk ya yb =>
    change ZSqrt5.mk (xa + ya) (xb + yb) = ZSqrt5.mk (ya + xa) (yb + xb)
    rw [Int.add_comm xa ya, Int.add_comm xb yb]
  add_assoc x y z := by
    cases x with | mk xa xb => cases y with | mk ya yb => cases z with | mk za zb =>
    change ZSqrt5.mk ((xa + ya) + za) ((xb + yb) + zb) = ZSqrt5.mk (xa + (ya + za)) (xb + (yb + zb))
    rw [Int.add_assoc xa ya za, Int.add_assoc xb yb zb]
  zero_add x := by
    cases x with | mk xa xb =>
    change ZSqrt5.mk (0 + xa) (0 + xb) = ZSqrt5.mk xa xb
    rw [Int.zero_add xa, Int.zero_add xb]
  add_neg x := by
    cases x with | mk xa xb =>
    change ZSqrt5.mk (xa + -xa) (xb + -xb) = ZSqrt5.mk 0 0
    rw [Int.add_right_neg xa, Int.add_right_neg xb]
  sub_eq x y := by
    cases x with | mk xa xb => cases y with | mk ya yb =>
    change ZSqrt5.mk (xa - ya) (xb - yb) = ZSqrt5.mk (xa + -ya) (xb + -yb)
    congr 1 <;> omega
  mul_comm x y := by
    cases x with | mk xa xb => cases y with | mk ya yb =>
    change ZSqrt5.mk (xa * ya + 5 * xb * yb) (xa * yb + xb * ya) =
           ZSqrt5.mk (ya * xa + 5 * yb * xb) (ya * xb + yb * xa)
    congr 1
    · rw [Int.mul_comm xa ya, Int.mul_assoc 5 xb yb, Int.mul_comm xb yb, ← Int.mul_assoc 5 yb xb]
    · rw [Int.mul_comm xa yb, Int.mul_comm xb ya, Int.add_comm]
  mul_assoc x y z := by
    cases x with | mk xa xb => cases y with | mk ya yb => cases z with | mk za zb =>
    change ZSqrt5.mk
        ((xa * ya + 5 * xb * yb) * za + 5 * (xa * yb + xb * ya) * zb)
        ((xa * ya + 5 * xb * yb) * zb + (xa * yb + xb * ya) * za) =
      ZSqrt5.mk
        (xa * (ya * za + 5 * yb * zb) + 5 * xb * (ya * zb + yb * za))
        (xa * (ya * zb + yb * za) + xb * (ya * za + 5 * yb * zb))
    congr 1
    · rw [Int.add_mul (xa * ya) (5 * xb * yb) za, Int.mul_add 5 (xa * yb) (xb * ya),
          Int.add_mul (5 * (xa * yb)) (5 * (xb * ya)) zb,
          Int.mul_add xa (ya * za) (5 * yb * zb), Int.mul_add (5 * xb) (ya * zb) (yb * za)]
      simp only [Int.mul_assoc]
      have h1 : xa * (5 * (yb * zb)) = 5 * (xa * (yb * zb)) := by rw [← Int.mul_assoc, Int.mul_comm xa 5, Int.mul_assoc]
      have h2 : 5 * (xb * (ya * zb)) = 5 * (ya * (xb * zb)) := by
        rw [← Int.mul_assoc xb ya zb, Int.mul_comm xb ya, Int.mul_assoc]
      rw [h1]; omega
    · rw [Int.add_mul, Int.add_mul, Int.mul_add, Int.mul_add]
      simp only [Int.mul_assoc]
      have h1 : xb * (5 * (yb * zb)) = 5 * (xb * (yb * zb)) := by rw [← Int.mul_assoc, Int.mul_comm xb 5, Int.mul_assoc]
      rw [h1]; omega
  one_mul x := by
    cases x with | mk xa xb =>
    change ZSqrt5.mk (1 * xa + 5 * 0 * xb) (1 * xb + 0 * xa) = ZSqrt5.mk xa xb
    simp
  left_distrib x y z := by
    cases x with | mk xa xb => cases y with | mk ya yb => cases z with | mk za zb =>
    change ZSqrt5.mk (xa * (ya + za) + 5 * xb * (yb + zb)) (xa * (yb + zb) + xb * (ya + za)) =
           ZSqrt5.mk ((xa * ya + 5 * xb * yb) + (xa * za + 5 * xb * zb))
                     ((xa * yb + xb * ya) + (xa * zb + xb * za))
    congr 1
    · rw [Int.mul_add, Int.mul_add]; omega
    · rw [Int.mul_add, Int.mul_add]; omega

/-- Exact decidable nonnegativity predicate for `a + b√5 ≥ 0` in `Z[√5]`! -/
def nonneg (x : ZSqrt5) : Prop :=
  (0 ≤ x.a ∧ 0 ≤ x.b) ∨
  (0 ≤ x.a ∧ x.b < 0 ∧ 5 * x.b * x.b ≤ x.a * x.a) ∨
  (x.a < 0 ∧ 0 ≤ x.b ∧ x.a * x.a ≤ 5 * x.b * x.b)

theorem nonneg_zero : nonneg (0 : ZSqrt5) := Or.inl ⟨Int.le_refl 0, Int.le_refl 0⟩

theorem nonneg_ofNat (n : Nat) : nonneg (ofInt n) := Or.inl ⟨Int.natCast_nonneg n, Int.le_refl 0⟩

theorem sq_nonneg_int (z : Int) : 0 ≤ z * z := by
  by_cases hz : 0 ≤ z
  · exact Int.mul_nonneg hz hz
  · have hneg : 0 ≤ -z := by omega
    have heq : (-z) * (-z) = z * z := Int.neg_mul_neg z z
    rw [← heq]; exact Int.mul_nonneg hneg hneg

theorem nonneg_sq (x : ZSqrt5) : nonneg (x * x) := by
  cases x with | mk a b =>
  change nonneg ⟨a * a + 5 * b * b, a * b + b * a⟩
  dsimp only [nonneg]
  have ha2 : 0 ≤ a * a := sq_nonneg_int a
  have hb2 : 0 ≤ b * b := sq_nonneg_int b
  have h5b2 : 0 ≤ 5 * b * b := by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) hb2
  have ha_nn : 0 ≤ a * a + 5 * b * b := by omega
  by_cases hsign : 0 ≤ a * b + b * a
  · exact Or.inl ⟨ha_nn, hsign⟩
  · right; left
    refine ⟨ha_nn, by omega, ?_⟩
    have hdiff : (a * a + 5 * b * b) * (a * a + 5 * b * b) -
        5 * (a * b + b * a) * (a * b + b * a) =
        (a * a - 5 * b * b) * (a * a - 5 * b * b) := by
      have hba : b * a = a * b := Int.mul_comm b a
      rw [hba]
      have h1 : (a * a + 5 * b * b) * (a * a + 5 * b * b) =
          (a * a) * (a * a) + 2 * ((a * a) * (5 * b * b)) + (5 * b * b) * (5 * b * b) := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm (5 * b * b) (a * a), Int.two_mul]; omega
      have h2 : (a * a - 5 * b * b) * (a * a - 5 * b * b) =
          (a * a) * (a * a) - 2 * ((a * a) * (5 * b * b)) + (5 * b * b) * (5 * b * b) := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm (5 * b * b) (a * a), Int.two_mul]; omega
      have h3 : 5 * (a * b + a * b) * (a * b + a * b) = 4 * ((a * a) * (5 * b * b)) := by
        rw [Int.mul_add 5 (a * b) (a * b), Int.add_mul (5 * (a * b)) (5 * (a * b)) (a * b + a * b),
            Int.mul_add (5 * (a * b)) (a * b) (a * b)]
        have heq : 5 * (a * b) * (a * b) = (a * a) * (5 * b * b) := by
          simp only [Int.mul_assoc]
          have c1 : b * (a * b) = a * (b * b) := by rw [← Int.mul_assoc, Int.mul_comm b a, Int.mul_assoc]
          rw [c1]
          rw [← Int.mul_assoc 5 a, Int.mul_comm 5 a, Int.mul_assoc a 5,
              ← Int.mul_assoc 5 a, Int.mul_comm 5 a, Int.mul_assoc a 5]
        rw [heq]; omega
      rw [h1, h2, h3]; omega
    have hsq := sq_nonneg_int (a * a - 5 * b * b)
    omega

/-- Helper: `x, y ≥ 0` and `x^2 ≤ y^2` implies `x ≤ y`, and `0 ≤ x ≤ y` implies `x^2 ≤ y^2`. -/
theorem int_le_of_sq_le {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x * x ≤ y * y) : x ≤ y := by
  by_cases hle : x ≤ y
  · exact hle
  · have hlt : y < x := by omega
    have h1 : y * y ≤ y * x := Int.mul_le_mul_of_nonneg_left (by omega) hy
    have h2 : y * x < x * x := Int.mul_lt_mul_of_pos_right hlt (by omega)
    omega

theorem int_sq_le_of_le {x y : Int} (hx : 0 ≤ x) (h : x ≤ y) : x * x ≤ y * y := by
  have h1 : x * x ≤ x * y := Int.mul_le_mul_of_nonneg_left h hx
  have h2 : x * y ≤ y * y := Int.mul_le_mul_of_nonneg_right h (by omega)
  omega

/-- Key Cauchy-like helper: if `0 ≤ u, v, w, z`, `5 * v^2 ≤ u^2`, and `w^2 ≤ 5 * z^2`,
    then `5 * (v * w)^2 ≤ (u * z)^2` and `v * w ≤ u * z` (wait: `u*z` vs `v*w`!). -/
theorem mul_sq_bound_5 {u v w z : Int} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (h1 : 5 * v * v ≤ u * u) (h2 : w * w ≤ 5 * z * z) :
    v * w ≤ u * z := by
  have h5 : 5 * ((v * w) * (v * w)) ≤ 5 * ((u * z) * (u * z)) := by
    have hL : 5 * ((v * w) * (v * w)) = (5 * v * v) * (w * w) := by
      simp only [Int.mul_assoc]
      have c1 : w * (v * w) = v * (w * w) := by rw [← Int.mul_assoc, Int.mul_comm w v, Int.mul_assoc]
      rw [c1]
    have hR : 5 * ((u * z) * (u * z)) = (u * u) * (5 * z * z) := by
      simp only [Int.mul_assoc]
      have c1 : z * (u * z) = u * (z * z) := by rw [← Int.mul_assoc, Int.mul_comm z u, Int.mul_assoc]
      rw [c1, ← Int.mul_assoc 5 u, Int.mul_comm 5 u, Int.mul_assoc u 5,
          ← Int.mul_assoc 5 u, Int.mul_comm 5 u, Int.mul_assoc u 5]
    rw [hL, hR]
    have hvw : 0 ≤ w * w := sq_nonneg_int w
    have huu : 0 ≤ u * u := sq_nonneg_int u
    have s1 := Int.mul_le_mul_of_nonneg_right h1 hvw
    have s2 := Int.mul_le_mul_of_nonneg_left h2 huu
    omega
  have hsq : (v * w) * (v * w) ≤ (u * z) * (u * z) := by omega
  exact int_le_of_sq_le (Int.mul_nonneg hv hw) (Int.mul_nonneg hu hz) hsq

/-- Helper: if `0 ≤ u, v, w, z`, `5 * v^2 ≤ u^2`, `5 * z^2 ≤ w^2`, then `5*(v+z)^2 ≤ (u+w)^2`. -/
theorem add_sq_bound_5_pos {u v w z : Int} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (h1 : 5 * v * v ≤ u * u) (h2 : 5 * z * z ≤ w * w) :
    5 * (v + z) * (v + z) ≤ (u + w) * (u + w) := by
  -- Need `5 * (v^2 + 2vz + z^2) ≤ u^2 + 2uw + w^2`; suffices `5*v*z ≤ u*w`, from `(5vz)^2 = (5v^2)(5z^2) ≤ u^2 w^2`!
  have hcross_sq : (5 * v * z) * (5 * v * z) ≤ (u * w) * (u * w) := by
    have hL : (5 * v * z) * (5 * v * z) = (5 * v * v) * (5 * z * z) := by
      simp only [Int.mul_assoc]
      have c1 : z * (5 * (v * z)) = v * (5 * (z * z)) := by
        rw [← Int.mul_assoc z 5, Int.mul_comm z 5, Int.mul_assoc 5 z,
            ← Int.mul_assoc z v z, Int.mul_comm z v, Int.mul_assoc v z z,
            ← Int.mul_assoc 5 v, Int.mul_comm 5 v, Int.mul_assoc v 5]
      rw [c1]
    have hR : (u * w) * (u * w) = (u * u) * (w * w) := by
      simp only [Int.mul_assoc]
      have c1 : w * (u * w) = u * (w * w) := by rw [← Int.mul_assoc, Int.mul_comm w u, Int.mul_assoc]
      rw [c1]
    rw [hL, hR]
    have h5z : 0 ≤ 5 * z * z := by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (sq_nonneg_int z)
    have s1 := Int.mul_le_mul_of_nonneg_right h1 h5z
    have s2 := Int.mul_le_mul_of_nonneg_left h2 (sq_nonneg_int u)
    omega
  have hcross : 5 * v * z ≤ u * w :=
    int_le_of_sq_le (Int.mul_nonneg (Int.mul_nonneg (by omega) hv) hz) (Int.mul_nonneg hu hw) hcross_sq
  have hL : 5 * (v + z) * (v + z) = 5 * v * v + 2 * (5 * v * z) + 5 * z * z := by
    rw [Int.mul_add 5 v z, Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_assoc 5 v z,
        Int.mul_assoc 5 z v, Int.mul_comm z v, Int.two_mul]; omega
  have hR : (u + w) * (u + w) = u * u + 2 * (u * w) + w * w := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm w u, Int.two_mul]; omega
  rw [hL, hR]; omega

/-- Helper: if `0 ≤ u, v, w, z`, `u^2 ≤ 5 * v^2`, `w^2 ≤ 5 * z^2`, then `(u+w)^2 ≤ 5*(v+z)^2`. -/
theorem add_sq_bound_5_neg {u v w z : Int} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (h1 : u * u ≤ 5 * v * v) (h2 : w * w ≤ 5 * z * z) :
    (u + w) * (u + w) ≤ 5 * (v + z) * (v + z) := by
  have hcross_sq : (u * w) * (u * w) ≤ (5 * v * z) * (5 * v * z) := by
    have hL : (u * w) * (u * w) = (u * u) * (w * w) := by
      simp only [Int.mul_assoc]
      have c1 : w * (u * w) = u * (w * w) := by rw [← Int.mul_assoc, Int.mul_comm w u, Int.mul_assoc]
      rw [c1]
    have hR : (5 * v * z) * (5 * v * z) = (5 * v * v) * (5 * z * z) := by
      simp only [Int.mul_assoc]
      have c1 : z * (5 * (v * z)) = v * (5 * (z * z)) := by
        rw [← Int.mul_assoc z 5, Int.mul_comm z 5, Int.mul_assoc 5 z,
            ← Int.mul_assoc z v z, Int.mul_comm z v, Int.mul_assoc v z z,
            ← Int.mul_assoc 5 v, Int.mul_comm 5 v, Int.mul_assoc v 5]
      rw [c1]
    rw [hL, hR]
    have h5v : 0 ≤ 5 * v * v := by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (sq_nonneg_int v)
    have s1 := Int.mul_le_mul_of_nonneg_right h1 (sq_nonneg_int w)
    have s2 := Int.mul_le_mul_of_nonneg_left h2 h5v
    omega
  have hcross : u * w ≤ 5 * v * z :=
    int_le_of_sq_le (Int.mul_nonneg hu hw) (Int.mul_nonneg (Int.mul_nonneg (by omega) hv) hz) hcross_sq
  have hL : (u + w) * (u + w) = u * u + 2 * (u * w) + w * w := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm w u, Int.two_mul]; omega
  have hR : 5 * (v + z) * (v + z) = 5 * v * v + 2 * (5 * v * z) + 5 * z * z := by
    rw [Int.mul_add 5 v z, Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_assoc 5 v z,
        Int.mul_assoc 5 z v, Int.mul_comm z v, Int.two_mul]; omega
  rw [hL, hR]; omega

/-- `nonneg` is closed under addition in `Z[√5]`. -/
theorem nonneg_add {x y : ZSqrt5} (hx : nonneg x) (hy : nonneg y) : nonneg (x + y) := by
  cases x with | mk xa xb =>
  cases y with | mk ya yb =>
  change nonneg ⟨xa + ya, xb + yb⟩
  -- Helper for mixed sign: `u ≥ 0, v ≥ 0` with `5 v^2 ≤ u^2` vs `w ≥ 0, z ≥ 0` with `w^2 ≤ 5 z^2`
  have hmix : ∀ (u v w z : Int), 0 ≤ u → 0 ≤ v → 0 ≤ w → 0 ≤ z →
      5 * v * v ≤ u * u → w * w ≤ 5 * z * z → nonneg ⟨u - w, z - v⟩ := by
    intro u v w z hu hv hw hz h1 h2
    dsimp only [nonneg]
    by_cases ha : 0 ≤ u - w
    · by_cases hb : 0 ≤ z - v
      · exact Or.inl ⟨ha, hb⟩
      · right; left; refine ⟨ha, by omega, ?_⟩
        -- Need `5*(v-z)^2 ≤ (u-w)^2`, i.e., `u - w ≥ 0, v - z > 0`.
        -- Since `5 v^2 ≤ u^2` and `w^2 ≤ 5 z^2`: `u*w ≤ ...` wait: `(u-w)^2 - 5(v-z)^2 = (u^2 - 5v^2) + (5z^2 - w^2) + 2(5vz - uw)`!
        -- Wait: `5vz ≥ uw`? No, `v > z` and `u ≥ w`, so we need `u - w` vs `v - z`!
        -- Actually use `add_sq_bound_5_pos`? No: `5*(v-z)^2 ≤ (u-w)^2 ↔ u ≥ w + ...`:
        -- `u^2 ≥ 5v^2` and `5z^2 ≥ w^2`, so `u*z ≥ v*w` (by `mul_sq_bound_5`)!
        -- Still easier: `(u*z - v*w)` doesn't directly sign `5vz - uw`. Check:
        -- `5v^2 ≤ u^2` & `w^2 ≤ 5z^2` & `z < v` & `w ≤ u`:
        -- Multiply `u` and `w`: `(u - w)^2 - 5(v - z)^2 = u^2 + w^2 - 2uw - 5v^2 - 5z^2 + 10vz`.
        -- Wait: take `v = 3, z = 1` (`5v^2 = 45, 5z^2 = 5`), `u = 7` (`u^2 = 49 ≥ 45`), `w = 2` (`w^2 = 4 ≤ 5`):
        -- `u - w = 5`, `v - z = 2`, `5*(2)^2 = 20 ≤ 25 = 5^2`!
        -- Why? Because `u ≥ √5 v` and `w ≤ √5 z`, so `u - w ≥ √5 (v - z) > 0`!
        -- Prove `5*(v-z)^2 ≤ (u-w)^2` via `u ≥ √5 v ≥ √5 z ≥ w`!
        -- Specifically, `w^2 ≤ 5 z^2` and `5 v^2 ≤ u^2`, so:
        -- `5 z^2 + 5 (v - z)^2` ... even simpler: `w + √5(v-z) ≤ √5 z + √5(v-z) = √5 v ≤ u`,
        -- which purely in Int is: `(u - w)^2 ≥ 5(v - z)^2` iff `u ≥ w + ...`, proved by:
        -- Let `t := v - z > 0`. Notice `w^2 ≤ 5 z^2` and `5 (z + t)^2 = 5 v^2 ≤ u^2`!
        -- We want `5 t^2 ≤ (u - w)^2`. By `add_sq_bound_5_neg`? Look:
        -- Wait: `(w + ...)` — just use `5*(z+t)^2 ≤ u^2` and `w^2 ≤ 5*z^2`!
        -- `(u - w)^2 - 5 t^2 = (u^2 - 5(z+t)^2) + (5z^2 - w^2) + 2*(5*z*t + w*(w - u))` — no!
        -- Use `w * (z + t)` vs `u * z`:
        -- Better: prove `w^2 + 2 w (u - w) + (u - w)^2 = u^2 ≥ 5 z^2 + 10 z t + 5 t^2`!
        -- Wait: `w^2 ≤ 5 z^2`, so `2 w (u - w) + (u - w)^2 ≥ 10 z t + 5 t^2`!
        -- Suppose for contradiction `(u - w)^2 < 5 t^2` (with `u - w ≥ 0, t > 0`)!
        -- Then `w^2 ≤ 5 z^2` AND `(u - w)^2 ≤ 5 t^2` — APPLY `add_sq_bound_5_neg` to `(w, z)` and `(u - w, t)`!!
        -- Wait: `add_sq_bound_5_neg` gives `(w + (u - w))^2 ≤ 5 * (z + t)^2`, i.e., **`u^2 ≤ 5 v^2`**!
        -- And with STRICT `<` on `(u - w)^2 < 5 t^2` (since `t > 0`, `z ≥ 0`), we get **`u^2 < 5 v^2`**, CONTRADICTING `5 v^2 ≤ u^2`!!
        -- OH!! GENIUS 4-LINE PROOF BY CONTRADICTION!!
        by_cases hok : 5 * (z - v) * (z - v) ≤ (u - w) * (u - w)
        · exact hok
        · exfalso
          have ht : 0 < v - z := by omega
          have hlt : (u - w) * (u - w) < 5 * (v - z) * (v - z) := by
            have heq : (z - v) * (z - v) = (v - z) * (v - z) := by
              have : z - v = -(v - z) := by omega
              rw [this, Int.neg_mul_neg]
            rw [Int.mul_assoc, heq, ← Int.mul_assoc] at hok; omega
          have hcross_sq : (w * (u - w)) * (w * (u - w)) ≤ (5 * z * (v - z)) * (5 * z * (v - z)) := by
            have hL : (w * (u - w)) * (w * (u - w)) = (w * w) * ((u - w) * (u - w)) := by
              simp only [Int.mul_assoc]
              have c1 : (u - w) * (w * (u - w)) = w * ((u - w) * (u - w)) := by
                rw [← Int.mul_assoc, Int.mul_comm (u - w) w, Int.mul_assoc]
              rw [c1]
            have hR : (5 * z * (v - z)) * (5 * z * (v - z)) = (5 * z * z) * (5 * (v - z) * (v - z)) := by
              simp only [Int.mul_assoc]
              have c1 : (v - z) * (5 * (z * (v - z))) = z * (5 * ((v - z) * (v - z))) := by
                rw [← Int.mul_assoc (v - z) 5, Int.mul_comm (v - z) 5, Int.mul_assoc 5 (v - z),
                    ← Int.mul_assoc (v - z) z (v - z), Int.mul_comm (v - z) z, Int.mul_assoc z (v - z),
                    ← Int.mul_assoc 5 z, Int.mul_comm 5 z, Int.mul_assoc z 5]
              rw [c1]
            rw [hL, hR]
            have h5z : 0 ≤ 5 * z * z := by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (sq_nonneg_int z)
            have s1 := Int.mul_le_mul_of_nonneg_right h2 (sq_nonneg_int (u - w))
            have s2 := Int.mul_le_mul_of_nonneg_left (by omega : (u - w) * (u - w) ≤ 5 * (v - z) * (v - z)) h5z
            omega
          have hcross : w * (u - w) ≤ 5 * z * (v - z) :=
            int_le_of_sq_le (Int.mul_nonneg hw ha) (Int.mul_nonneg (Int.mul_nonneg (by omega) hz) (by omega)) hcross_sq
          have hu_eq : u * u = w * w + 2 * (w * (u - w)) + (u - w) * (u - w) := by
            have hu1 : u = w + (u - w) := by omega
            calc u * u = (w + (u - w)) * (w + (u - w)) := by rw [← hu1]
              _ = w * w + 2 * (w * (u - w)) + (u - w) * (u - w) := by
                rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm (u - w) w, Int.two_mul]; omega
          have hv_eq : 5 * v * v = 5 * z * z + 2 * (5 * z * (v - z)) + 5 * (v - z) * (v - z) := by
            have hv1 : v = z + (v - z) := by omega
            calc 5 * v * v = 5 * (z + (v - z)) * (z + (v - z)) := by rw [← hv1]
              _ = 5 * z * z + 2 * (5 * z * (v - z)) + 5 * (v - z) * (v - z) := by
                rw [Int.mul_add 5 z (v - z), Int.add_mul, Int.mul_add, Int.mul_add,
                    Int.mul_assoc 5 z (v - z), Int.mul_assoc 5 (v - z) z, Int.mul_comm (v - z) z, Int.two_mul]; omega
          omega
    · by_cases hb : 0 ≤ z - v
      · right; right; refine ⟨by omega, hb, ?_⟩
        by_cases hok : (u - w) * (u - w) ≤ 5 * (z - v) * (z - v)
        · exact hok
        · exfalso
          have ht : 0 < w - u := by omega
          have hlt : 5 * (z - v) * (z - v) < (w - u) * (w - u) := by
            have heq : (u - w) * (u - w) = (w - u) * (w - u) := by
              have : u - w = -(w - u) := by omega
              rw [this, Int.neg_mul_neg]
            rw [heq] at hok; omega
          have hcross_sq : (5 * v * (z - v)) * (5 * v * (z - v)) ≤ (u * (w - u)) * (u * (w - u)) := by
            have hL : (5 * v * (z - v)) * (5 * v * (z - v)) = (5 * v * v) * (5 * (z - v) * (z - v)) := by
              simp only [Int.mul_assoc]
              have c1 : (z - v) * (5 * (v * (z - v))) = v * (5 * ((z - v) * (z - v))) := by
                rw [← Int.mul_assoc (z - v) 5, Int.mul_comm (z - v) 5, Int.mul_assoc 5 (z - v),
                    ← Int.mul_assoc (z - v) v (z - v), Int.mul_comm (z - v) v, Int.mul_assoc v (z - v),
                    ← Int.mul_assoc 5 v, Int.mul_comm 5 v, Int.mul_assoc v 5]
              rw [c1]
            have hR : (u * (w - u)) * (u * (w - u)) = (u * u) * ((w - u) * (w - u)) := by
              simp only [Int.mul_assoc]
              have c1 : (w - u) * (u * (w - u)) = u * ((w - u) * (w - u)) := by
                rw [← Int.mul_assoc, Int.mul_comm (w - u) u, Int.mul_assoc]
              rw [c1]
            rw [hL, hR]
            have h5zv : 0 ≤ 5 * (z - v) * (z - v) := by
              rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (sq_nonneg_int (z - v))
            have s1 := Int.mul_le_mul_of_nonneg_right h1 h5zv
            have s2 := Int.mul_le_mul_of_nonneg_left (by omega : 5 * (z - v) * (z - v) ≤ (w - u) * (w - u)) (sq_nonneg_int u)
            omega
          have hcross : 5 * v * (z - v) ≤ u * (w - u) :=
            int_le_of_sq_le (Int.mul_nonneg (Int.mul_nonneg (by omega) hv) hb) (Int.mul_nonneg hu (by omega)) hcross_sq
          have hw_eq : w * w = u * u + 2 * (u * (w - u)) + (w - u) * (w - u) := by
            have hw1 : w = u + (w - u) := by omega
            calc w * w = (u + (w - u)) * (u + (w - u)) := by rw [← hw1]
              _ = u * u + 2 * (u * (w - u)) + (w - u) * (w - u) := by
                rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm (w - u) u, Int.two_mul]; omega
          have hz_eq : 5 * z * z = 5 * v * v + 2 * (5 * v * (z - v)) + 5 * (z - v) * (z - v) := by
            have hz1 : z = v + (z - v) := by omega
            calc 5 * z * z = 5 * (v + (z - v)) * (v + (z - v)) := by rw [← hz1]
              _ = 5 * v * v + 2 * (5 * v * (z - v)) + 5 * (z - v) * (z - v) := by
                rw [Int.mul_add 5 v (z - v), Int.add_mul, Int.mul_add, Int.mul_add,
                    Int.mul_assoc 5 v (z - v), Int.mul_assoc 5 (z - v) v, Int.mul_comm (z - v) v, Int.two_mul]; omega
          omega
      · -- Impossible: `u < w` and `z < v` contradicts `5 v^2 ≤ u^2 < w^2 ≤ 5 z^2 < 5 v^2`!
        exfalso
        have h1' : u * u < w * w := by
          have s1 := Int.mul_le_mul_of_nonneg_left (by omega : u ≤ w) hu
          have s2 := Int.mul_lt_mul_of_pos_right (by omega : u < w) (by omega : 0 < w)
          omega
        have h2' : 5 * z * z < 5 * v * v := by
          have s1 := Int.mul_le_mul_of_nonneg_left (by omega : z ≤ v) hz
          have s2 := Int.mul_lt_mul_of_pos_right (by omega : z < v) (by omega : 0 < v)
          have s3 : z * z < v * v := by omega
          have s4 := Int.mul_lt_mul_of_pos_left s3 (by decide : (0 : Int) < 5)
          rw [Int.mul_assoc, Int.mul_assoc]; exact s4
        omega
  -- Dispatch all 3 × 3 = 9 sign cases!
  dsimp only [nonneg] at hx hy
  rcases hx with ⟨hxa, hxb⟩ | ⟨hxa, hxb, hxs⟩ | ⟨hxa, hxb, hxs⟩ <;>
  rcases hy with ⟨hya, hyb⟩ | ⟨hya, hyb, hys⟩ | ⟨hya, hyb, hys⟩
  · dsimp only [nonneg]; exact Or.inl ⟨by omega, by omega⟩
  · have h := hmix (xa + ya) (-yb) 0 xb (by omega) (by omega) (Int.le_refl 0) hxb
      (by
        have h1 : 5 * (-yb) * (-yb) = 5 * yb * yb := by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]
        have h2 : ya * ya ≤ (xa + ya) * (xa + ya) := int_sq_le_of_le hya (by omega)
        omega)
      (by
        have : 0 ≤ 5 * xb * xb := by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (sq_nonneg_int xb)
        omega)
    have hEq : (⟨xa + ya - 0, xb - -yb⟩ : ZSqrt5) = ⟨xa + ya, xb + yb⟩ := by congr 1 <;> omega
    rw [← hEq]; exact h
  · have h := hmix xa 0 (-ya) (xb + yb) hxa (Int.le_refl 0) (by omega) (by omega)
      (by simp; exact sq_nonneg_int xa)
      (by
        have h1 : (-ya) * (-ya) = ya * ya := Int.neg_mul_neg ya ya
        have h2 : yb * yb ≤ (xb + yb) * (xb + yb) := int_sq_le_of_le hyb (by omega)
        have h5 := Int.mul_le_mul_of_nonneg_left h2 (by decide : (0 : Int) ≤ 5)
        rw [← Int.mul_assoc, ← Int.mul_assoc] at h5; omega)
    have hEq : (⟨xa - -ya, xb + yb - 0⟩ : ZSqrt5) = ⟨xa + ya, xb + yb⟩ := by congr 1 <;> omega
    rw [← hEq]; exact h
  · have h := hmix (xa + ya) (-xb) 0 yb (by omega) (by omega) (Int.le_refl 0) hyb
      (by
        have h1 : 5 * (-xb) * (-xb) = 5 * xb * xb := by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]
        have h2 : xa * xa ≤ (xa + ya) * (xa + ya) := int_sq_le_of_le hxa (by omega)
        omega)
      (by
        have : 0 ≤ 5 * yb * yb := by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (sq_nonneg_int yb)
        omega)
    have hEq : (⟨xa + ya - 0, yb - -xb⟩ : ZSqrt5) = ⟨xa + ya, xb + yb⟩ := by congr 1 <;> omega
    rw [← hEq]; exact h
  · dsimp only [nonneg]; right; left; refine ⟨by omega, by omega, ?_⟩
    have h := add_sq_bound_5_pos hxa (by omega : 0 ≤ -xb) hya (by omega : 0 ≤ -yb)
      (by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]; exact hxs)
      (by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]; exact hys)
    have hneg : (-xb + -yb) * (-xb + -yb) = (xb + yb) * (xb + yb) := by
      have : -xb + -yb = -(xb + yb) := by omega
      rw [this, Int.neg_mul_neg]
    rw [Int.mul_assoc, hneg, ← Int.mul_assoc] at h
    exact h
  · have h := hmix xa (-xb) (-ya) yb hxa (by omega) (by omega) hyb
      (by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]; exact hxs)
      (by rw [Int.neg_mul_neg]; exact hys)
    have hEq : (⟨xa - -ya, yb - -xb⟩ : ZSqrt5) = ⟨xa + ya, xb + yb⟩ := by congr 1 <;> omega
    rw [← hEq]; exact h
  · have h := hmix ya 0 (-xa) (xb + yb) hya (Int.le_refl 0) (by omega) (by omega)
      (by simp; exact sq_nonneg_int ya)
      (by
        have h1 : (-xa) * (-xa) = xa * xa := Int.neg_mul_neg xa xa
        have h2 : xb * xb ≤ (xb + yb) * (xb + yb) := int_sq_le_of_le hxb (by omega)
        have h5 := Int.mul_le_mul_of_nonneg_left h2 (by decide : (0 : Int) ≤ 5)
        rw [← Int.mul_assoc, ← Int.mul_assoc] at h5; omega)
    have hEq : (⟨ya - -xa, xb + yb - 0⟩ : ZSqrt5) = ⟨xa + ya, xb + yb⟩ := by congr 1 <;> omega
    rw [← hEq]; exact h
  · have h := hmix ya (-yb) (-xa) xb hya (by omega) (by omega) hxb
      (by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]; exact hys)
      (by rw [Int.neg_mul_neg]; exact hxs)
    have hEq : (⟨ya - -xa, xb - -yb⟩ : ZSqrt5) = ⟨xa + ya, xb + yb⟩ := by congr 1 <;> omega
    rw [← hEq]; exact h
  · dsimp only [nonneg]; right; right; refine ⟨by omega, by omega, ?_⟩
    have h := add_sq_bound_5_neg (by omega : 0 ≤ -xa) hxb (by omega : 0 ≤ -ya) hyb
      (by rw [Int.neg_mul_neg]; exact hxs) (by rw [Int.neg_mul_neg]; exact hys)
    have hneg : (-xa + -ya) * (-xa + -ya) = (xa + ya) * (xa + ya) := by
      have : -xa + -ya = -(xa + ya) := by omega
      rw [this, Int.neg_mul_neg]
    rw [hneg] at h; exact h

/-- Exact norm-sign partition of `nonneg`: either `a ≥ 0, 5b^2 ≤ a^2` or `b ≥ 0, a^2 ≤ 5b^2`. -/
theorem nonneg_cases {x : ZSqrt5} (hx : nonneg x) :
    (0 ≤ x.a ∧ 5 * x.b * x.b ≤ x.a * x.a) ∨
    (0 ≤ x.b ∧ x.a * x.a ≤ 5 * x.b * x.b) := by
  rcases hx with ⟨ha, hb⟩ | ⟨ha, _, h⟩ | ⟨_, hb, h⟩
  · by_cases h5 : 5 * x.b * x.b ≤ x.a * x.a
    · exact Or.inl ⟨ha, h5⟩
    · exact Or.inr ⟨hb, by omega⟩
  · exact Or.inl ⟨ha, h⟩
  · exact Or.inr ⟨hb, h⟩

theorem nonneg_of_pos_norm {a b : Int} (ha : 0 ≤ a) (h : 5 * b * b ≤ a * a) :
    nonneg ⟨a, b⟩ := by
  dsimp only [nonneg]
  by_cases hb : 0 ≤ b
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr (Or.inl ⟨ha, by omega, h⟩)

theorem nonneg_of_neg_norm {a b : Int} (hb : 0 ≤ b) (h : a * a ≤ 5 * b * b) :
    nonneg ⟨a, b⟩ := by
  dsimp only [nonneg]
  by_cases ha : 0 ≤ a
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr (Or.inr ⟨by omega, hb, h⟩)

theorem int_le_of_sq_le_any {u v : Int} (hv : 0 ≤ v) (h : u * u ≤ v * v) : u ≤ v := by
  by_cases hu : 0 ≤ u
  · exact int_le_of_sq_le hu hv h
  · omega

theorem int_neg_le_of_sq_le_any {u v : Int} (hv : 0 ≤ v) (h : u * u ≤ v * v) : -u ≤ v := by
  apply int_le_of_sq_le_any hv
  rw [Int.neg_mul_neg]; exact h

/-- `nonneg` is closed under multiplication in `Z[√5]` (clean 2×2 norm-sign proof!). -/
theorem nonneg_mul {x y : ZSqrt5} (hx : nonneg x) (hy : nonneg y) : nonneg (x * y) := by
  have hnorm : ∀ (xa xb ya yb : Int),
      (xa * ya + 5 * xb * yb) * (xa * ya + 5 * xb * yb) -
      5 * (xa * yb + xb * ya) * (xa * yb + xb * ya) =
      (xa * xa - 5 * xb * xb) * (ya * ya - 5 * yb * yb) := by
    intro xa xb ya yb
    have t1 : (xa * ya + 5 * xb * yb) * (xa * ya + 5 * xb * yb) =
        (xa * xa) * (ya * ya) + 2 * (5 * xa * xb * ya * yb) + (5 * xb * xb) * (5 * yb * yb) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.two_mul]
      have e1 : (xa * ya) * (xa * ya) = (xa * xa) * (ya * ya) := by
        simp only [Int.mul_assoc]; rw [← Int.mul_assoc ya xa ya, Int.mul_comm ya xa, Int.mul_assoc]
      have e2 : (5 * xb * yb) * (5 * xb * yb) = (5 * xb * xb) * (5 * yb * yb) := by
        simp only [Int.mul_assoc]
        have c1 : yb * (5 * (xb * yb)) = xb * (5 * (yb * yb)) := by
          rw [← Int.mul_assoc yb 5, Int.mul_comm yb 5, Int.mul_assoc 5 yb,
              ← Int.mul_assoc yb xb yb, Int.mul_comm yb xb, Int.mul_assoc xb yb yb,
              ← Int.mul_assoc 5 xb, Int.mul_comm 5 xb, Int.mul_assoc xb 5]
        rw [c1]
      have e3 : (xa * ya) * (5 * xb * yb) = 5 * xa * xb * ya * yb := by
        simp only [Int.mul_assoc]
        rw [← Int.mul_assoc ya 5, Int.mul_comm ya 5, Int.mul_assoc 5 ya,
            ← Int.mul_assoc xa 5, Int.mul_comm xa 5, Int.mul_assoc 5 xa,
            ← Int.mul_assoc ya xb yb, Int.mul_comm ya xb, Int.mul_assoc xb ya yb]
      have e4 : (5 * xb * yb) * (xa * ya) = (xa * ya) * (5 * xb * yb) := Int.mul_comm _ _
      rw [e1, e2, e4, e3]; omega
    have t2 : 5 * (xa * yb + xb * ya) * (xa * yb + xb * ya) =
        (xa * xa) * (5 * yb * yb) + 2 * (5 * xa * xb * ya * yb) + (5 * xb * xb) * (ya * ya) := by
      rw [Int.mul_add 5 (xa * yb) (xb * ya), Int.add_mul, Int.mul_add, Int.mul_add, Int.two_mul]
      have e1 : 5 * (xa * yb) * (xa * yb) = (xa * xa) * (5 * yb * yb) := by
        simp only [Int.mul_assoc]
        rw [← Int.mul_assoc yb xa yb, Int.mul_comm yb xa, Int.mul_assoc xa yb yb,
            ← Int.mul_assoc 5 xa, Int.mul_comm 5 xa, Int.mul_assoc xa 5,
            ← Int.mul_assoc 5 xa, Int.mul_comm 5 xa, Int.mul_assoc xa 5]
      have e2 : 5 * (xb * ya) * (xb * ya) = (5 * xb * xb) * (ya * ya) := by
        simp only [Int.mul_assoc]
        rw [← Int.mul_assoc ya xb ya, Int.mul_comm ya xb, Int.mul_assoc xb ya ya]
      have e3 : 5 * (xa * yb) * (xb * ya) = 5 * xa * xb * ya * yb := by
        simp only [Int.mul_assoc]
        rw [← Int.mul_assoc yb xb ya, Int.mul_comm yb xb, Int.mul_assoc xb yb ya, Int.mul_comm yb ya]
      have e4 : 5 * (xb * ya) * (xa * yb) = 5 * xa * xb * ya * yb := by
        calc 5 * (xb * ya) * (xa * yb)
            = 5 * ((xb * ya) * (xa * yb)) := Int.mul_assoc ..
          _ = 5 * ((xa * yb) * (xb * ya)) := by rw [Int.mul_comm (xb * ya) (xa * yb)]
          _ = 5 * (xa * yb) * (xb * ya) := (Int.mul_assoc ..).symm
          _ = 5 * xa * xb * ya * yb := e3
      rw [e1, e2, e3, e4]; omega
    have t3 : (xa * xa - 5 * xb * xb) * (ya * ya - 5 * yb * yb) =
        (xa * xa) * (ya * ya) - (xa * xa) * (5 * yb * yb) - (5 * xb * xb) * (ya * ya) +
        (5 * xb * xb) * (5 * yb * yb) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
    rw [t1, t2, t3]; omega
  have hPN : ∀ (xa xb ya yb : Int),
      0 ≤ xa → 5 * xb * xb ≤ xa * xa →
      0 ≤ yb → ya * ya ≤ 5 * yb * yb →
      nonneg ⟨xa * ya + 5 * xb * yb, xa * yb + xb * ya⟩ := by
    intro xa xb ya yb hxa hx5 hyb hy5
    have hn := hnorm xa xb ya yb
    have hprod_le : (xa * xa - 5 * xb * xb) * (ya * ya - 5 * yb * yb) ≤ 0 := by
      have hp := Int.mul_nonneg (by omega : 0 ≤ xa * xa - 5 * xb * xb) (by omega : 0 ≤ -(ya * ya - 5 * yb * yb))
      rw [Int.mul_neg] at hp; omega
    have hsq5 : 5 * ((xb * ya) * (xb * ya)) ≤ 5 * ((xa * yb) * (xa * yb)) := by
      have hL : 5 * ((xb * ya) * (xb * ya)) = (5 * xb * xb) * (ya * ya) := by
        simp only [Int.mul_assoc]; rw [← Int.mul_assoc ya xb ya, Int.mul_comm ya xb, Int.mul_assoc]
      have hR : 5 * ((xa * yb) * (xa * yb)) = (xa * xa) * (5 * yb * yb) := by
        simp only [Int.mul_assoc]
        rw [← Int.mul_assoc yb xa yb, Int.mul_comm yb xa, Int.mul_assoc xa yb yb,
            ← Int.mul_assoc 5 xa, Int.mul_comm 5 xa, Int.mul_assoc xa 5,
            ← Int.mul_assoc 5 xa, Int.mul_comm 5 xa, Int.mul_assoc xa 5]
      rw [hL, hR]
      have s1 := Int.mul_le_mul_of_nonneg_right hx5 (sq_nonneg_int ya)
      have s2 := Int.mul_le_mul_of_nonneg_left hy5 (sq_nonneg_int xa)
      omega
    have hb_nn : 0 ≤ xa * yb + xb * ya := by
      have hle := int_neg_le_of_sq_le_any (Int.mul_nonneg hxa hyb) (by omega : (xb * ya) * (xb * ya) ≤ (xa * yb) * (xa * yb))
      omega
    exact nonneg_of_neg_norm hb_nn (by omega)
  cases x with | mk xa xb =>
  cases y with | mk ya yb =>
  change nonneg ⟨xa * ya + 5 * xb * yb, xa * yb + xb * ya⟩
  rcases nonneg_cases hx with ⟨hxa, hx5⟩ | ⟨hxb, hx5⟩ <;>
  rcases nonneg_cases hy with ⟨hya, hy5⟩ | ⟨hyb, hy5⟩
  · -- (P, P)
    dsimp only at hxa hx5 hya hy5
    have hn := hnorm xa xb ya yb
    have hprod_ge := Int.mul_nonneg (by omega : 0 ≤ xa * xa - 5 * xb * xb) (by omega : 0 ≤ ya * ya - 5 * yb * yb)
    have hsq : (5 * xb * yb) * (5 * xb * yb) ≤ (xa * ya) * (xa * ya) := by
      have hL : (5 * xb * yb) * (5 * xb * yb) = (5 * xb * xb) * (5 * yb * yb) := by
        simp only [Int.mul_assoc]
        have c1 : yb * (5 * (xb * yb)) = xb * (5 * (yb * yb)) := by
          rw [← Int.mul_assoc yb 5, Int.mul_comm yb 5, Int.mul_assoc 5 yb,
              ← Int.mul_assoc yb xb yb, Int.mul_comm yb xb, Int.mul_assoc xb yb yb,
              ← Int.mul_assoc 5 xb, Int.mul_comm 5 xb, Int.mul_assoc xb 5]
        rw [c1]
      have hR : (xa * ya) * (xa * ya) = (xa * xa) * (ya * ya) := by
        simp only [Int.mul_assoc]; rw [← Int.mul_assoc ya xa ya, Int.mul_comm ya xa, Int.mul_assoc]
      rw [hL, hR]
      have h5y : 0 ≤ 5 * yb * yb := by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (sq_nonneg_int yb)
      have s1 := Int.mul_le_mul_of_nonneg_right hx5 h5y
      have s2 := Int.mul_le_mul_of_nonneg_left hy5 (sq_nonneg_int xa)
      omega
    have ha_nn : 0 ≤ xa * ya + 5 * xb * yb := by
      have hle := int_neg_le_of_sq_le_any (Int.mul_nonneg hxa hya) hsq
      omega
    exact nonneg_of_pos_norm ha_nn (by omega)
  · -- (P, N)
    dsimp only at hxa hx5 hyb hy5
    exact hPN xa xb ya yb hxa hx5 hyb hy5
  · -- (N, P) via commutativity
    dsimp only at hxb hx5 hya hy5
    have hsym := hPN ya yb xa xb hya hy5 hxb hx5
    have hEq : (⟨ya * xa + 5 * yb * xb, ya * xb + yb * xa⟩ : ZSqrt5) =
        ⟨xa * ya + 5 * xb * yb, xa * yb + xb * ya⟩ := by
      congr 1
      · rw [Int.mul_comm ya xa, Int.mul_assoc 5 yb xb, Int.mul_comm yb xb, ← Int.mul_assoc 5 xb yb]
      · rw [Int.mul_comm ya xb, Int.mul_comm yb xa, Int.add_comm]
    rw [← hEq]; exact hsym
  · -- (N, N)
    dsimp only at hxb hx5 hyb hy5
    have hn := hnorm xa xb ya yb
    have hprod_ge : 0 ≤ (xa * xa - 5 * xb * xb) * (ya * ya - 5 * yb * yb) := by
      have hp := Int.mul_nonneg (by omega : 0 ≤ -(xa * xa - 5 * xb * xb)) (by omega : 0 ≤ -(ya * ya - 5 * yb * yb))
      rw [Int.neg_mul_neg] at hp; exact hp
    have hsq : (xa * ya) * (xa * ya) ≤ (5 * xb * yb) * (5 * xb * yb) := by
      have hL : (xa * ya) * (xa * ya) = (xa * xa) * (ya * ya) := by
        simp only [Int.mul_assoc]; rw [← Int.mul_assoc ya xa ya, Int.mul_comm ya xa, Int.mul_assoc]
      have hR : (5 * xb * yb) * (5 * xb * yb) = (5 * xb * xb) * (5 * yb * yb) := by
        simp only [Int.mul_assoc]
        have c1 : yb * (5 * (xb * yb)) = xb * (5 * (yb * yb)) := by
          rw [← Int.mul_assoc yb 5, Int.mul_comm yb 5, Int.mul_assoc 5 yb,
              ← Int.mul_assoc yb xb yb, Int.mul_comm yb xb, Int.mul_assoc xb yb yb,
              ← Int.mul_assoc 5 xb, Int.mul_comm 5 xb, Int.mul_assoc xb 5]
        rw [c1]
      rw [hL, hR]
      have h5x : 0 ≤ 5 * xb * xb := by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (sq_nonneg_int xb)
      have s1 := Int.mul_le_mul_of_nonneg_right hx5 (sq_nonneg_int ya)
      have s2 := Int.mul_le_mul_of_nonneg_left hy5 h5x
      omega
    have ha_nn : 0 ≤ xa * ya + 5 * xb * yb := by
      have hle := int_neg_le_of_sq_le_any (Int.mul_nonneg (Int.mul_nonneg (by omega) hxb) hyb) hsq
      omega
    exact nonneg_of_pos_norm ha_nn (by omega)

theorem nonneg_of_pos_int_mul {c : Int} {z : ZSqrt5} (hc : 0 < c)
    (h : nonneg (ofInt c * z)) : nonneg z := by
  cases z with | mk a b =>
  change nonneg ⟨c * a + 5 * 0 * b, c * b + 0 * a⟩ at h
  simp only [Int.mul_zero, Int.zero_mul, Int.add_zero] at h
  have hc2 : 0 < c * c := Int.mul_pos hc hc
  have hsq_cancel : ∀ u v : Int, c * c * u ≤ c * c * v → u ≤ v := by
    intro u v huv
    by_cases hok : u ≤ v
    · exact hok
    · have hneg : v - u < 0 := by omega
      have hmul := Int.mul_neg_of_pos_of_neg hc2 hneg
      rw [Int.mul_sub] at hmul; omega
  have h5cb : 5 * (c * b) * (c * b) = c * c * (5 * b * b) := by
    simp only [Int.mul_assoc]
    rw [← Int.mul_assoc b c b, Int.mul_comm b c, Int.mul_assoc c b b,
        ← Int.mul_assoc 5 c, Int.mul_comm 5 c, Int.mul_assoc c 5,
        ← Int.mul_assoc 5 c, Int.mul_comm 5 c, Int.mul_assoc c 5]
  have hca2 : (c * a) * (c * a) = c * c * (a * a) := by
    simp only [Int.mul_assoc]; rw [← Int.mul_assoc a c a, Int.mul_comm a c, Int.mul_assoc]
  have hsign_ge : ∀ u : Int, 0 ≤ c * u → 0 ≤ u := by
    intro u hu
    by_cases hok : 0 ≤ u
    · exact hok
    · have := Int.mul_neg_of_pos_of_neg hc (by omega : u < 0); omega
  have hsign_lt : ∀ u : Int, c * u < 0 → u < 0 := by
    intro u hu
    by_cases hok : u < 0
    · exact hok
    · have := Int.mul_nonneg (by omega : 0 ≤ c) (by omega : 0 ≤ u); omega
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hs⟩ | ⟨ha, hb, hs⟩
  · exact Or.inl ⟨hsign_ge a ha, hsign_ge b hb⟩
  · rw [h5cb, hca2] at hs
    exact Or.inr (Or.inl ⟨hsign_ge a ha, hsign_lt b hb, hsq_cancel _ _ hs⟩)
  · rw [h5cb, hca2] at hs
    exact Or.inr (Or.inr ⟨hsign_lt a ha, hsign_ge b hb, hsq_cancel _ _ hs⟩)

theorem sumR_nonneg (N : Nat) (f : Nat → ZSqrt5) (hf : ∀ i, i < N → nonneg (f i)) :
    nonneg (sumR N f) := by
  induction N with
  | zero => exact nonneg_zero
  | succ m ih =>
    simp only [sumR]
    exact nonneg_add (ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))) (hf m (Nat.lt_succ_self m))

theorem prodR_nonneg (t : Nat) (f : Nat → ZSqrt5) (hf : ∀ d, d < t → nonneg (f d)) :
    nonneg (prodR t f) := by
  induction t with
  | zero => exact nonneg_ofNat 1
  | succ m ih =>
    simp only [prodR]
    exact nonneg_mul (ih (fun d hd => hf d (Nat.lt_succ_of_lt hd))) (hf m (Nat.lt_succ_self m))

theorem ofInt_mul (x y : Int) : ofInt x * ofInt y = ofInt (x * y) := by
  change (⟨x * y + 5 * 0 * 0, x * 0 + 0 * y⟩ : ZSqrt5) = ⟨x * y, 0⟩
  simp

theorem ofInt_add (x y : Int) : ofInt x + ofInt y = ofInt (x + y) := by
  change (⟨x + y, 0 + 0⟩ : ZSqrt5) = ⟨x + y, 0⟩
  simp

theorem ofInt_sub (x y : Int) : ofInt x - ofInt y = ofInt (x - y) := by
  change (⟨x - y, 0 - 0⟩ : ZSqrt5) = ⟨x - y, 0⟩
  simp

theorem ofInt_pow (c : Int) : ∀ t : Nat, rPow (ofInt c) t = ofInt (c ^ t)
  | 0 => by simp [rPow, ofInt]; rfl
  | t + 1 => by
    rw [rPow_succ, ofInt_pow c t, ofInt_mul, Int.pow_succ]

theorem sqrt5_pow_even : ∀ q : Nat, rPow sqrt5 (2 * q) = ofInt (5 ^ q)
  | 0 => rfl
  | q + 1 => by
    have heq : 2 * (q + 1) = 2 * q + 2 := by omega
    rw [heq, rPow_succ, rPow_succ, sqrt5_pow_even q]
    change (⟨(5 : Int) ^ q * 0 + 5 * 0 * 1, (5 : Int) ^ q * 1 + 0 * 0⟩ : ZSqrt5) * ⟨0, 1⟩ = ⟨(5 : Int) ^ (q + 1), 0⟩
    simp only [Int.mul_zero, Int.add_zero, Int.mul_one]
    change (⟨0 * 0 + 5 * (5 : Int) ^ q * 1, 0 * 1 + (5 : Int) ^ q * 0⟩ : ZSqrt5) = ⟨(5 : Int) ^ (q + 1), 0⟩
    simp only [Int.mul_zero, Int.add_zero, Int.mul_one, Int.zero_add]
    congr 1; rw [Int.pow_succ, Int.mul_comm]

theorem sqrt5_pow_odd (q : Nat) : rPow sqrt5 (2 * q + 1) = ⟨0, 5 ^ q⟩ := by
  rw [rPow_succ, sqrt5_pow_even q]
  change (⟨(5 : Int) ^ q * 0 + 5 * 0 * 1, (5 : Int) ^ q * 1 + 0 * 0⟩ : ZSqrt5) = ⟨0, (5 : Int) ^ q⟩
  simp

theorem nat_sq_le_pow5_of_nonneg (t k : Nat)
    (h : nonneg (rPow sqrt5 t - ofInt k)) : k * k ≤ 5 ^ t := by
  have hdiv := Nat.div_add_mod t 2
  cases hmod : t % 2 with
  | zero =>
    have ht : t = 2 * (t / 2) := by omega
    rw [ht, sqrt5_pow_even] at h
    rw [ht]
    change nonneg ⟨(5 : Int) ^ (t / 2) - (k : Int), 0 - 0⟩ at h
    have hle : (k : Int) ≤ (5 : Int) ^ (t / 2) := by
      rcases h with ⟨ha, _⟩ | ⟨ha, _, _⟩ | ⟨ha, _, hs⟩
      · dsimp only at ha; omega
      · dsimp only at ha; omega
      · dsimp only at ha hs
        simp only [Int.sub_self, Int.mul_zero] at hs
        have hneg : 0 < (k : Int) - (5 : Int) ^ (t / 2) := by omega
        have hpos := Int.mul_pos hneg hneg
        have heq : ((5 : Int) ^ (t / 2) - (k : Int)) * ((5 : Int) ^ (t / 2) - (k : Int)) =
            ((k : Int) - (5 : Int) ^ (t / 2)) * ((k : Int) - (5 : Int) ^ (t / 2)) := by
          have : (5 : Int) ^ (t / 2) - (k : Int) = -((k : Int) - (5 : Int) ^ (t / 2)) := by omega
          rw [this, Int.neg_mul_neg]
        omega
    have hk_nat : k ≤ 5 ^ (t / 2) := by
      have : ((5 ^ (t / 2) : Nat) : Int) = (5 : Int) ^ (t / 2) := by
        induction (t / 2) with
        | zero => rfl
        | succ m ih => rw [Nat.pow_succ, Int.natCast_mul, ih, Int.pow_succ]; rfl
      omega
    have hmul := Nat.mul_le_mul hk_nat hk_nat
    have hpow : 5 ^ (t / 2) * 5 ^ (t / 2) = 5 ^ (2 * (t / 2)) := by
      rw [← Nat.pow_add, Nat.two_mul]
    omega
  | succ r =>
    have hr0 : r = 0 := by have := Nat.mod_lt t (by decide : 0 < 2); omega
    subst hr0
    have ht : t = 2 * (t / 2) + 1 := by omega
    rw [ht, sqrt5_pow_odd] at h
    rw [ht]
    change nonneg ⟨0 - (k : Int), (5 : Int) ^ (t / 2) - 0⟩ at h
    simp only [Int.zero_sub, Int.sub_zero] at h
    have hpow_cast : ∀ m : Nat, ((5 ^ m : Nat) : Int) = (5 : Int) ^ m := by
      intro m; induction m with
      | zero => rfl
      | succ m' ih => rw [Nat.pow_succ, Int.natCast_mul, ih, Int.pow_succ]; rfl
    have hsq_int : (k : Int) * (k : Int) ≤ 5 * ((5 : Int) ^ (t / 2)) * ((5 : Int) ^ (t / 2)) := by
      rcases h with ⟨ha, _⟩ | ⟨ha, _, _⟩ | ⟨_, _, hs⟩
      · dsimp only at ha
        have hk0 : (k : Int) = 0 := by omega
        rw [hk0, Int.zero_mul]
        rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (sq_nonneg_int _)
      · dsimp only at ha
        have hk0 : (k : Int) = 0 := by omega
        rw [hk0, Int.zero_mul]
        rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (sq_nonneg_int _)
      · dsimp only at hs
        rw [Int.neg_mul_neg] at hs; exact hs
    have hR : 5 * ((5 : Int) ^ (t / 2)) * ((5 : Int) ^ (t / 2)) = ((5 ^ (2 * (t / 2) + 1) : Nat) : Int) := by
      rw [hpow_cast (2 * (t / 2) + 1), Int.pow_succ, Nat.two_mul, Int.pow_add, Int.mul_comm _ 5, Int.mul_assoc]
    have hL : (k : Int) * (k : Int) = ((k * k : Nat) : Int) := (Int.natCast_mul k k).symm
    rw [hL, hR] at hsq_int
    omega

end ZSqrt5

-- ============================================================================
-- Section 3: Exact 3-Term `Z[√5]` SOS Proof of Lovász `Θ(C_5) = √5`
-- ============================================================================

/-- Adjacency of the 5-cycle `C_5` on `{0, 1, 2, 3, 4}`. -/
def c5Adj (i j : Nat) : Bool :=
  let d1 := (i + 5 - j % 5) % 5
  let d2 := (j + 5 - i % 5) % 5
  (d1 == 1) || (d2 == 1)

/-- Exact `6 × 6` Lovász umbrella Gram matrix `80 * M_6` in `Z[√5]`:
    index `0` is handle `5^{1/4} c`; indices `1..5` are umbrella vectors `u_0..u_4` of `C_5`. -/
def lovaszM6 (i j : Nat) : ZSqrt5 :=
  if i == 0 && j == 0 then ⟨0, 80⟩
  else if i == 0 || j == 0 then ⟨80, 0⟩
  else if i == j then ⟨80, 0⟩
  else if c5Adj (i - 1) (j - 1) then ⟨-40, 40⟩
  else ⟨0, 0⟩

/-- Positive `Z[√5]` weights `w_0 = 16√5`, `w_1 = 5 - √5`, `w_2 = 10` for the exact 3-term SOS. -/
def lovaszW : Nat → ZSqrt5
  | 0 => ⟨0, 16⟩
  | 1 => ⟨5, -1⟩
  | _ => ⟨10, 0⟩

/-- Exact 3-column SOS factor `Z(i, r)` (`i < 6`, `r < 3`) satisfying
    `∑_{r < 3} lovaszW r * lovaszZ i r * lovaszZ j r = lovaszM6 i j` identically! -/
def lovaszZ (i r : Nat) : ZSqrt5 :=
  match r with
  | 0 => if i == 0 then ⟨0, 1⟩ else ⟨1, 0⟩
  | 1 =>
    match i with
    | 1 => ⟨4, 0⟩
    | 2 => ⟨-1, 1⟩
    | 3 => ⟨-1, -1⟩
    | 4 => ⟨-1, -1⟩
    | 5 => ⟨-1, 1⟩
    | _ => ⟨0, 0⟩
  | _ =>
    match i with
    | 2 => ⟨2, 0⟩
    | 3 => ⟨-1, 1⟩
    | 4 => ⟨1, -1⟩
    | 5 => ⟨-2, 0⟩
    | _ => ⟨0, 0⟩

theorem lovaszW_nonneg (r : Nat) : ZSqrt5.nonneg (lovaszW r) := by
  match r with
  | 0 => change (0 ≤ (0 : Int) ∧ 0 ≤ (16 : Int)) ∨ _; exact Or.inl ⟨by decide, by decide⟩
  | 1 => change _ ∨ (0 ≤ (5 : Int) ∧ (-1 : Int) < 0 ∧ 5 * (-1) * (-1) ≤ 5 * 5) ∨ _; exact Or.inr (Or.inl ⟨by decide, by decide, by decide⟩)
  | _ + 2 => change (0 ≤ (10 : Int) ∧ 0 ≤ (0 : Int)) ∨ _; exact Or.inl ⟨by decide, by decide⟩

theorem lovaszM6_sos_exact (i j : Nat) (hi : i < 6) (hj : j < 6) :
    sumR 3 (fun r => lovaszW r * lovaszZ i r * lovaszZ j r) = lovaszM6 i j := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Embed a vertex `x < 5^t` of `C_5^{⊠ t}` into `[6^t)` by shifting every base-5 digit by `+1`. -/
def embed5to6 : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, x => (digit 5 x t + 1) * 6 ^ t + embed5to6 t x

theorem embed5to6_lt : ∀ t x : Nat, embed5to6 t x < 6 ^ t
  | 0, _ => by simp [embed5to6]
  | t + 1, x => by
    simp only [embed5to6]
    have hdig : digit 5 x t < 5 := Nat.mod_lt _ (by decide)
    have hrec := embed5to6_lt t x
    have h6 : 6 ^ (t + 1) = 6 * 6 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : (digit 5 x t + 1) * 6 ^ t + embed5to6 t x < (digit 5 x t + 1) * 6 ^ t + 6 ^ t :=
      Nat.add_lt_add_left hrec _
    have h2 : (digit 5 x t + 1) * 6 ^ t + 6 ^ t = (digit 5 x t + 2) * 6 ^ t := by
      calc (digit 5 x t + 1) * 6 ^ t + 6 ^ t
          = (digit 5 x t + 1) * 6 ^ t + 1 * 6 ^ t := by rw [Nat.one_mul]
        _ = ((digit 5 x t + 1) + 1) * 6 ^ t := (Nat.add_mul ..).symm
        _ = (digit 5 x t + 2) * 6 ^ t := rfl
    have h3 : (digit 5 x t + 2) * 6 ^ t ≤ 6 * 6 ^ t := Nat.mul_le_mul_right _ (by omega)
    omega

theorem digit_embed5to6 : ∀ (t x d : Nat), d < t → digit 6 (embed5to6 t x) d = digit 5 x d + 1
  | 0, _, _, hd => by omega
  | t + 1, x, d, hd => by
    simp only [embed5to6]
    have hrec := embed5to6_lt t x
    have hdig : digit 5 x t + 1 < 6 := by
      unfold digit
      have := Nat.mod_lt (x / 5 ^ t) (by decide : 0 < 5); omega
    cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hd) with
    | inl heq =>
      rw [heq]
      have hpos : 0 < 6 ^ t := Nat.pow_pos (by decide)
      calc (((digit 5 x t + 1) * 6 ^ t + embed5to6 t x) / 6 ^ t) % 6
          = ((6 ^ t * (digit 5 x t + 1) + embed5to6 t x) / 6 ^ t) % 6 := by
            rw [Nat.mul_comm (digit 5 x t + 1) (6 ^ t)]
        _ = ((digit 5 x t + 1) + embed5to6 t x / 6 ^ t) % 6 := by rw [Nat.mul_add_div hpos]
        _ = (digit 5 x t + 1) % 6 := by rw [Nat.div_eq_of_lt hrec, Nat.add_zero]
        _ = digit 5 x t + 1 := Nat.mod_eq_of_lt hdig
    | inr hlt =>
      obtain ⟨q, hq⟩ := Nat.pow_dvd_pow 6 hlt
      have hpow : 6 ^ t = 6 ^ d * (6 * q) := by rw [hq, Nat.pow_succ, Nat.mul_assoc]
      have hpos : 0 < 6 ^ d := Nat.pow_pos (by decide)
      have hrew : (digit 5 x t + 1) * 6 ^ t + embed5to6 t x =
          6 ^ d * (6 * (q * (digit 5 x t + 1))) + embed5to6 t x := by
        rw [hpow]
        have h1 : (digit 5 x t + 1) * (6 ^ d * (6 * q)) = 6 ^ d * (6 * (q * (digit 5 x t + 1))) := by
          rw [Nat.mul_comm (digit 5 x t + 1), Nat.mul_assoc, Nat.mul_assoc]
        rw [h1]
      change (((digit 5 x t + 1) * 6 ^ t + embed5to6 t x) / 6 ^ d) % 6 = digit 5 x d + 1
      rw [hrew, Nat.mul_add_div hpos, Nat.mul_add_mod]
      exact digit_embed5to6 t x d hlt

theorem digit_zero (n d : Nat) : digit n 0 d = 0 := by
  unfold digit; simp

/-- **Lovász (1979) Pentagon Upper Bound (`k^2 ≤ 5^t` for ALL `t` and ALL independent sets `S ⊆ C_5^{⊠ t}`):**
    Proved completely algebraically in exact `Z[√5]` arithmetic with ZERO Mathlib and ZERO reals! -/
theorem lovasz_c5_strong_pow_upper (t k : Nat) (f : Nat → Nat)
    (hInd : IsIndepSet (5 ^ t) (strongPowAdj 5 c5Adj t) k f) :
    k * k ≤ 5 ^ t := by
  -- Define Kronecker-lifted SOS weights `W s` and factors `Z x s` (`s < 3^t`, `x < 6^t`)
  let W : Nat → ZSqrt5 := fun s => prodR t (fun d => lovaszW (digit 3 s d))
  let Z : Nat → Nat → ZSqrt5 := fun x s => prodR t (fun d => lovaszZ (digit 6 x d) (digit 3 s d))
  let M : Nat → Nat → ZSqrt5 := fun x y => prodR t (fun d => lovaszM6 (digit 6 x d) (digit 6 y d))
  have hFactor : ∀ x y, x < 6 ^ t → y < 6 ^ t →
      sumR (3 ^ t) (fun s => W s * (Z x s * Z y s)) = M x y := by
    intro x y hx hy
    let U : Nat → Nat → ZSqrt5 := fun i r => lovaszW r * lovaszZ i r
    have hUV : ∀ i j, i < 6 → j < 6 → sumR 3 (fun r => U i r * lovaszZ j r) = lovaszM6 i j :=
      fun i j hi hj => lovaszM6_sos_exact i j hi hj
    have hkr := kronecker_pow_factor 6 3 U (fun r j => lovaszZ j r) lovaszM6 hUV t x y hx hy
    change sumR (3 ^ t) (fun s => W s * (Z x s * Z y s)) = prodR t (fun d => lovaszM6 (digit 6 x d) (digit 6 y d))
    rw [← hkr]
    apply sumR_congr
    intro s _
    have hprod_mul : ∀ m (a b : Nat → ZSqrt5),
        prodR m (fun d => a d * b d) = prodR m a * prodR m b := by
      intro m a b
      induction m with
      | zero => simp [prodR, CommRing.one_mul]
      | succ m' ih =>
        simp only [prodR, ih]
        rw [CommRing.mul_assoc (prodR m' a) (prodR m' b),
            ← CommRing.mul_assoc (prodR m' b) (a m') (b m'),
            CommRing.mul_comm (prodR m' b) (a m'),
            CommRing.mul_assoc (a m') (prodR m' b) (b m'),
            ← CommRing.mul_assoc (prodR m' a) (a m')]
    dsimp only [W, Z, U]
    rw [hprod_mul t (fun d => lovaszW (digit 3 s d)) (fun d => lovaszZ (digit 6 x d) (digit 3 s d)),
        CommRing.mul_assoc]
  -- Evaluate the exact nonnegative SOS form: `∑_{s < 3^t} W s * (Z 0 s - ∑_{i < k} Z (emb (f i)) s)^2 ≥ 0`!
  let emb (i : Nat) : Nat := embed5to6 t (f i)
  have hSOS_nn : ZSqrt5.nonneg
      (sumR (3 ^ t) (fun s => W s * ((Z 0 s - sumR k (fun i => Z (emb i) s)) *
                                     (Z 0 s - sumR k (fun i => Z (emb i) s))))) := by
    apply ZSqrt5.sumR_nonneg
    intro s _
    exact ZSqrt5.nonneg_mul (ZSqrt5.prodR_nonneg t _ (fun d _ => lovaszW_nonneg _)) (ZSqrt5.nonneg_sq _)
  -- Expand the SOS quadratic form into `M 0 0 - 2 * ∑ M 0 (emb i) + ∑_{i,j} M (emb i) (emb j)`!
  have hExpand :
      sumR (3 ^ t) (fun s => W s * ((Z 0 s - sumR k (fun i => Z (emb i) s)) *
                                    (Z 0 s - sumR k (fun i => Z (emb i) s)))) =
      M 0 0 - (sumR k (fun i => M 0 (emb i)) + sumR k (fun i => M 0 (emb i))) +
      sumR k (fun i => sumR k (fun j => M (emb i) (emb j))) := by
    have hsum_sub : ∀ (N : Nat) (a b : Nat → ZSqrt5),
        sumR N (fun s => a s - b s) = sumR N a - sumR N b := by
      intro N a b
      induction N with
      | zero => simp [sumR, CommRing.sub_eq, CommRing.zero_add]; exact neg_zero
      | succ m ih =>
        simp only [sumR, ih]
        rw [CommRing.sub_eq, CommRing.sub_eq, CommRing.sub_eq, ZSqrt5.neg_add_ring,
            CommRing.add_assoc, ← CommRing.add_assoc (-(sumR m b)) (a m) (-(b m)),
            CommRing.add_comm (-(sumR m b)) (a m),
            CommRing.add_assoc (a m) (-(sumR m b)) (-(b m)), ← CommRing.add_assoc]
    have hsum_swap : ∀ (A B : Nat) (h : Nat → Nat → ZSqrt5),
        sumR A (fun i => sumR B (fun j => h i j)) = sumR B (fun j => sumR A (fun i => h i j)) := by
      intro A B h
      induction A with
      | zero => simp [sumR, sumR_zero_fn]
      | succ m ih => simp only [sumR, ih, ← sumR_add]
    have hterm : ∀ s, W s * ((Z 0 s - sumR k (fun i => Z (emb i) s)) *
                             (Z 0 s - sumR k (fun i => Z (emb i) s))) =
        W s * (Z 0 s * Z 0 s) -
        (sumR k (fun i => W s * (Z 0 s * Z (emb i) s)) + sumR k (fun i => W s * (Z 0 s * Z (emb i) s))) +
        sumR k (fun i => sumR k (fun j => W s * (Z (emb i) s * Z (emb j) s))) := by
      intro s
      let u := Z 0 s
      let S := sumR k (fun i => Z (emb i) s)
      have hsq : (u - S) * (u - S) = u * u - (u * S + u * S) + S * S := by
        calc (u - S) * (u - S)
            = (u + -S) * (u + -S) := by rw [CommRing.sub_eq]
          _ = (u * u + -(u * S)) + (-(u * S) + S * S) := by
              rw [CommRing.left_distrib, right_distrib, right_distrib,
                  mul_neg, neg_mul, neg_mul, mul_neg, neg_neg, CommRing.mul_comm S u]
          _ = (u * u + (-(u * S) + -(u * S))) + S * S := by
              rw [CommRing.add_assoc (u * u) (-(u * S)) (-(u * S) + S * S),
                  ← CommRing.add_assoc (-(u * S)) (-(u * S)) (S * S),
                  ← CommRing.add_assoc (u * u) (-(u * S) + -(u * S)) (S * S)]
          _ = u * u - (u * S + u * S) + S * S := by
              rw [CommRing.sub_eq (u * u) (u * S + u * S), ZSqrt5.neg_add_ring]
      rw [hsq, CommRing.left_distrib, ZSqrt5.mul_sub_ring, CommRing.left_distrib]
      congr 1
      · congr 1
        have huS : W s * (u * S) = sumR k (fun i => W s * (u * Z (emb i) s)) := by
          dsimp only [S]
          rw [sumR_mul_left, sumR_mul_left]
        rw [huS]
      · have hSS : W s * (S * S) = sumR k (fun i => sumR k (fun j => W s * (Z (emb i) s * Z (emb j) s))) := by
          dsimp only [S]
          have h1 : S * S = sumR k (fun i => Z (emb i) s * sumR k (fun j => Z (emb j) s)) := by
            rw [CommRing.mul_comm, sumR_mul_left]
            exact sumR_congr (fun i _ => CommRing.mul_comm _ _)
          rw [h1, sumR_mul_left]
          apply sumR_congr; intro i _
          rw [sumR_mul_left, sumR_mul_left]
        exact hSS
    rw [sumR_congr (fun s _ => hterm s), sumR_add, hsum_sub, sumR_add]
    have h0lt : (0 : Nat) < 6 ^ t := Nat.pow_pos (by decide)
    have hM00 : sumR (3 ^ t) (fun s => W s * (Z 0 s * Z 0 s)) = M 0 0 := hFactor 0 0 h0lt h0lt
    have hM0i : sumR (3 ^ t) (fun s => sumR k (fun i => W s * (Z 0 s * Z (emb i) s))) =
        sumR k (fun i => M 0 (emb i)) := by
      rw [hsum_swap]
      apply sumR_congr; intro i _
      exact hFactor 0 (emb i) h0lt (embed5to6_lt t (f i))
    have hMij : sumR (3 ^ t) (fun s => sumR k (fun i => sumR k (fun j => W s * (Z (emb i) s * Z (emb j) s)))) =
        sumR k (fun i => sumR k (fun j => M (emb i) (emb j))) := by
      rw [hsum_swap]
      apply sumR_congr; intro i _
      rw [hsum_swap]
      apply sumR_congr; intro j _
      exact hFactor (emb i) (emb j) (embed5to6_lt t (f i)) (embed5to6_lt t (f j))
    rw [hM00, hM0i, hMij]
  -- Evaluate the exact entries of `M` on `0` and `emb (f i)`!
  have hM00_val : M 0 0 = ZSqrt5.ofInt ((80 : Int) ^ t) * rPow ZSqrt5.sqrt5 t := by
    dsimp only [M]
    have hstep : prodR t (fun d => lovaszM6 (digit 6 0 d) (digit 6 0 d)) =
        prodR t (fun _ => ZSqrt5.ofInt 80 * ZSqrt5.sqrt5) := by
      apply prodR_congr; intro d _; rw [digit_zero]; decide
    rw [hstep]
    have hconst : ∀ m (c : ZSqrt5), prodR m (fun _ => c) = rPow c m := by
      intro m c; induction m with | zero => rfl | succ m' ih => simp only [prodR, rPow_succ, ih]
    have hmul_pow : ∀ m (a b : ZSqrt5), rPow (a * b) m = rPow a m * rPow b m := by
      intro m a b
      induction m with
      | zero => simp [rPow, CommRing.one_mul]
      | succ m' ih =>
        rw [rPow_succ, rPow_succ, rPow_succ, ih]
        rw [CommRing.mul_assoc (rPow a m') (rPow b m'),
            ← CommRing.mul_assoc (rPow b m') a b, CommRing.mul_comm (rPow b m') a,
            CommRing.mul_assoc a (rPow b m') b, ← CommRing.mul_assoc (rPow a m') a]
    rw [hconst, hmul_pow, ZSqrt5.ofInt_pow]
  have hM0i_val : ∀ i, M 0 (emb i) = ZSqrt5.ofInt ((80 : Int) ^ t) := by
    intro i; dsimp only [M, emb]
    have hstep : prodR t (fun d => lovaszM6 (digit 6 0 d) (digit 6 (embed5to6 t (f i)) d)) =
        prodR t (fun _ => ZSqrt5.ofInt 80) := by
      apply prodR_congr; intro d hd
      rw [digit_zero, digit_embed5to6 t (f i) d hd]
      have hne : digit 5 (f i) d + 1 ≠ 0 := Nat.succ_ne_zero _
      unfold lovaszM6
      simp [ZSqrt5.ofInt]
    rw [hstep]
    have hconst : ∀ m (c : ZSqrt5), prodR m (fun _ => c) = rPow c m := by
      intro m c; induction m with | zero => rfl | succ m' ih => simp only [prodR, rPow_succ, ih]
    rw [hconst, ZSqrt5.ofInt_pow]
  have hMii_val : ∀ i, M (emb i) (emb i) = ZSqrt5.ofInt ((80 : Int) ^ t) := by
    intro i; dsimp only [M, emb]
    have hstep : prodR t (fun d => lovaszM6 (digit 6 (embed5to6 t (f i)) d) (digit 6 (embed5to6 t (f i)) d)) =
        prodR t (fun _ => ZSqrt5.ofInt 80) := by
      apply prodR_congr; intro d hd
      rw [digit_embed5to6 t (f i) d hd]
      unfold lovaszM6
      simp [ZSqrt5.ofInt]
    rw [hstep]
    have hconst : ∀ m (c : ZSqrt5), prodR m (fun _ => c) = rPow c m := by
      intro m c; induction m with | zero => rfl | succ m' ih => simp only [prodR, rPow_succ, ih]
    rw [hconst, ZSqrt5.ofInt_pow]
  have hMij_zero : ∀ i j, i < k → j < k → i ≠ j → M (emb i) (emb j) = 0 := by
    intro i j hi hj hne
    have hne_f := hInd.2.1 i j hi hj hne
    have hfalse := hInd.2.2 i j hi hj hne
    obtain ⟨d, hd, hne_d, hadj_d⟩ := strongPowAdj_false_exists_nonedge 5 c5Adj t (f i) (f j) hne_f hfalse
    apply prodR_zero_of_exists t _
    refine ⟨d, hd, ?_⟩
    dsimp only [emb]
    rw [digit_embed5to6 t (f i) d hd, digit_embed5to6 t (f j) d hd]
    unfold lovaszM6
    have hbeq : (digit 5 (f i) d + 1 == digit 5 (f j) d + 1) = false :=
      beq_false_of_ne (by omega)
    simp [hbeq, hadj_d]; rfl
  -- Sum over `i < k` and `j < k`!
  have hsum_const : ∀ m (c : Int), sumR m (fun _ => ZSqrt5.ofInt c) = ZSqrt5.ofInt ((m : Int) * c) := by
    intro m c
    induction m with
    | zero => simp [sumR]; rfl
    | succ m' ih =>
      simp only [sumR, ih, ZSqrt5.ofInt_add]
      congr 1
      have : ((m' + 1 : Nat) : Int) = (m' : Int) + 1 := by omega
      rw [this, Int.add_mul, Int.one_mul]
  have hsum_0i : sumR k (fun i => M 0 (emb i)) = ZSqrt5.ofInt ((k : Int) * (80 : Int) ^ t) := by
    rw [sumR_congr (fun i _ => hM0i_val i), hsum_const]
  have hsum_ij : sumR k (fun i => sumR k (fun j => M (emb i) (emb j))) =
      ZSqrt5.ofInt ((k : Int) * (80 : Int) ^ t) := by
    have hrow : ∀ i, i < k → sumR k (fun j => M (emb i) (emb j)) = ZSqrt5.ofInt ((80 : Int) ^ t) := by
      intro i hi
      have hsingle : ∀ m (a : Nat → ZSqrt5) (idx : Nat), idx < m →
          (∀ j, j < m → j ≠ idx → a j = 0) → sumR m a = a idx := by
        intro m a idx hidx hz
        induction m with
        | zero => omega
        | succ m' ih =>
          simp only [sumR]
          cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hidx) with
          | inl heq =>
            rw [heq]
            have h0 : sumR m' a = 0 := by
              rw [sumR_congr (fun j hj => hz j (Nat.lt_succ_of_lt hj) (by omega)), sumR_zero_fn]
            rw [h0, CommRing.zero_add]
          | inr hlt =>
            rw [hz m' (Nat.lt_succ_self m') (by omega), add_zero]
            exact ih hlt (fun j hj hne => hz j (Nat.lt_succ_of_lt hj) hne)
      rw [hsingle k (fun j => M (emb i) (emb j)) i hi (fun j hj hne => hMij_zero i j hi hj hne.symm)]
      exact hMii_val i
    rw [sumR_congr hrow, hsum_const]
  rw [hExpand, hM00_val, hsum_0i, hsum_ij] at hSOS_nn
  -- Simplify `80^t * √5^t - (k*80^t + k*80^t) + k*80^t = 80^t * (√5^t - k)`!
  have hSimp : ZSqrt5.ofInt ((80 : Int) ^ t) * rPow ZSqrt5.sqrt5 t -
      (ZSqrt5.ofInt ((k : Int) * (80 : Int) ^ t) + ZSqrt5.ofInt ((k : Int) * (80 : Int) ^ t)) +
      ZSqrt5.ofInt ((k : Int) * (80 : Int) ^ t) =
      ZSqrt5.ofInt ((80 : Int) ^ t) * (rPow ZSqrt5.sqrt5 t - ZSqrt5.ofInt k) := by
    rw [ZSqrt5.mul_sub_ring, ZSqrt5.ofInt_mul, Int.mul_comm ((80 : Int) ^ t) (k : Int)]
    let A := ZSqrt5.ofInt ((80 : Int) ^ t) * rPow ZSqrt5.sqrt5 t
    let B := ZSqrt5.ofInt ((k : Int) * (80 : Int) ^ t)
    change A - (B + B) + B = A - B
    rw [CommRing.sub_eq, CommRing.sub_eq, ZSqrt5.neg_add_ring,
        CommRing.add_assoc A (-B + -B) B, CommRing.add_assoc (-B) (-B) B, neg_add, add_zero]
  rw [hSimp] at hSOS_nn
  have h80pos : ∀ m : Nat, (0 : Int) < (80 : Int) ^ m := by
    intro m
    induction m with
    | zero => decide
    | succ m' ih => rw [Int.pow_succ]; exact Int.mul_pos ih (by decide)
  exact ZSqrt5.nat_sq_le_pow5_of_nonneg t k (ZSqrt5.nonneg_of_pos_int_mul (h80pos t) hSOS_nn)

-- ============================================================================
-- Section 4: Even-Power Independent-Set Lifting, `C_5` Tightness, & `C_7` Min-Rank = 4
-- ============================================================================

theorem strongPowAdj_false_of_exists_nonedge (n : Nat) (adj : Nat → Nat → Bool)
    (t x y d : Nat) (hd : d < t)
    (hne : digit n x d ≠ digit n y d) (hadj : adj (digit n x d) (digit n y d) = false) :
    strongPowAdj n adj t x y = false := by
  unfold strongPowAdj
  cases hxy : (x == y)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hgo : ∀ m, d < m → strongPowAdjGo n adj x y m = false := by
      intro m hm
      induction m with
      | zero => omega
      | succ m' ih =>
        simp only [strongPowAdjGo]
        cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hm) with
        | inl heq =>
          rw [← heq]
          have hbeq : (digit n x d == digit n y d) = false := beq_false_of_ne hne
          simp [hbeq, hadj]
        | inr hlt =>
          rw [ih hlt, Bool.and_false]
    exact hgo t hd
  · rfl

/-- Lift an independent set `f : [k] → [n^2)` in `G^{⊠ 2}` to `k^m` independent vertices in `G^{⊠ 2m}`! -/
def liftIndep2 (n k : Nat) (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, x => f (x / k ^ m) * n ^ (2 * m) + liftIndep2 n k f m (x % k ^ m)

theorem liftIndep2_lt (n k : Nat) (f : Nat → Nat) (hf : ∀ i, i < k → f i < n ^ 2)
    (hk : 0 < k) : ∀ m x, x < k ^ m → liftIndep2 n k f m x < n ^ (2 * m)
  | 0, _, _ => by simp [liftIndep2]
  | m + 1, x, hx => by
    simp only [liftIndep2]
    have hq : x / k ^ m < k := Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ] at hx; exact hx)
    have hr : x % k ^ m < k ^ m := Nat.mod_lt x (Nat.pow_pos hk)
    have hfq : f (x / k ^ m) < n ^ 2 := hf _ hq
    have hrec := liftIndep2_lt n k f hf hk m (x % k ^ m) hr
    have hpow : n ^ (2 * (m + 1)) = n ^ 2 * n ^ (2 * m) := by
      have : 2 * (m + 1) = 2 + 2 * m := by omega
      rw [this, Nat.pow_add]
    calc f (x / k ^ m) * n ^ (2 * m) + liftIndep2 n k f m (x % k ^ m)
        < f (x / k ^ m) * n ^ (2 * m) + n ^ (2 * m) := Nat.add_lt_add_left hrec _
      _ = (f (x / k ^ m) + 1) * n ^ (2 * m) := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ n ^ 2 * n ^ (2 * m) := Nat.mul_le_mul_right _ hfq
      _ = n ^ (2 * (m + 1)) := hpow.symm

theorem digit_liftIndep2_lo (n k : Nat) (f : Nat → Nat)
    (hn : 0 < n) (m x d : Nat) (hd : d < 2 * m) :
    digit n (liftIndep2 n k f (m + 1) x) d = digit n (liftIndep2 n k f m (x % k ^ m)) d := by
  simp only [liftIndep2]
  unfold digit
  obtain ⟨q, hq⟩ := Nat.pow_dvd_pow n hd
  have hpow : n ^ (2 * m) = n ^ d * (n * q) := by rw [hq, Nat.pow_succ, Nat.mul_assoc]
  have hrew : f (x / k ^ m) * n ^ (2 * m) + liftIndep2 n k f m (x % k ^ m) =
      n ^ d * (n * (q * f (x / k ^ m))) + liftIndep2 n k f m (x % k ^ m) := by
    rw [hpow]
    have h1 : f (x / k ^ m) * (n ^ d * (n * q)) = n ^ d * (n * (q * f (x / k ^ m))) := by
      rw [Nat.mul_comm (f (x / k ^ m)), Nat.mul_assoc, Nat.mul_assoc]
    rw [h1]
  rw [hrew, Nat.mul_add_div (Nat.pow_pos hn), Nat.mul_add_mod]

theorem digit_liftIndep2_hi (n k : Nat) (f : Nat → Nat) (hf : ∀ i, i < k → f i < n ^ 2)
    (hn : 0 < n) (hk : 0 < k) (m x b : Nat) :
    digit n (liftIndep2 n k f (m + 1) x) (2 * m + b) = digit n (f (x / k ^ m)) b := by
  simp only [liftIndep2]
  unfold digit
  have hr : x % k ^ m < k ^ m := Nat.mod_lt x (Nat.pow_pos hk)
  have hrec := liftIndep2_lt n k f hf hk m (x % k ^ m) hr
  have hdiv : (f (x / k ^ m) * n ^ (2 * m) + liftIndep2 n k f m (x % k ^ m)) / n ^ (2 * m + b) =
      f (x / k ^ m) / n ^ b := by
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul,
        Nat.mul_comm (f (x / k ^ m)) (n ^ (2 * m)),
        Nat.mul_add_div (Nat.pow_pos hn), Nat.div_eq_of_lt hrec, Nat.add_zero]
  rw [hdiv]

/-- General even-power lifting: `α(G^{⊠ 2}) ≥ k → ∀ m, α(G^{⊠ 2m}) ≥ k^m`! -/
theorem indep_lift_even_pow (n k : Nat) (adj : Nat → Nat → Bool) (f : Nat → Nat)
    (hn : 0 < n) (hk : 0 < k)
    (hInd : IsIndepSet (n ^ 2) (strongPowAdj n adj 2) k f) :
    ∀ m : Nat, IsIndepSet (n ^ (2 * m)) (strongPowAdj n adj (2 * m)) (k ^ m) (liftIndep2 n k f m) := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun i _ => by simp [liftIndep2],
            fun i j hi hj hne => by simp at hi hj; omega,
            fun i j hi hj hne => by simp at hi hj; omega⟩
  | succ m' ih =>
    have hlt := liftIndep2_lt n k f hInd.1 hk (m' + 1)
    have hnonedge : ∀ i j, i < k ^ (m' + 1) → j < k ^ (m' + 1) → i ≠ j →
        ∃ d, d < 2 * (m' + 1) ∧
          digit n (liftIndep2 n k f (m' + 1) i) d ≠ digit n (liftIndep2 n k f (m' + 1) j) d ∧
          adj (digit n (liftIndep2 n k f (m' + 1) i) d) (digit n (liftIndep2 n k f (m' + 1) j) d) = false := by
      intro i j hi hj hne
      by_cases hq : i / k ^ m' = j / k ^ m'
      · have hr_ne : i % k ^ m' ≠ j % k ^ m' := by
          intro hmod
          have e1 := Nat.div_add_mod i (k ^ m')
          have e2 := Nat.div_add_mod j (k ^ m')
          rw [hq, hmod] at e1
          exact hne (by omega)
        have hri : i % k ^ m' < k ^ m' := Nat.mod_lt i (Nat.pow_pos hk)
        have hrj : j % k ^ m' < k ^ m' := Nat.mod_lt j (Nat.pow_pos hk)
        have hne_rec := ih.2.1 _ _ hri hrj hr_ne
        have hfalse_rec := ih.2.2 _ _ hri hrj hr_ne
        obtain ⟨d, hd, hne_d, hadj_d⟩ := strongPowAdj_false_exists_nonedge n adj (2 * m') _ _ hne_rec hfalse_rec
        refine ⟨d, by omega, ?_, ?_⟩
        · rw [digit_liftIndep2_lo n k f hn m' i d hd,
              digit_liftIndep2_lo n k f hn m' j d hd]
          exact hne_d
        · rw [digit_liftIndep2_lo n k f hn m' i d hd,
              digit_liftIndep2_lo n k f hn m' j d hd]
          exact hadj_d
      · have hqi : i / k ^ m' < k := Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ] at hi; exact hi)
        have hqj : j / k ^ m' < k := Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ] at hj; exact hj)
        have hne_f := hInd.2.1 _ _ hqi hqj hq
        have hfalse_f := hInd.2.2 _ _ hqi hqj hq
        obtain ⟨b, hb, hne_b, hadj_b⟩ := strongPowAdj_false_exists_nonedge n adj 2 _ _ hne_f hfalse_f
        refine ⟨2 * m' + b, by omega, ?_, ?_⟩
        · rw [digit_liftIndep2_hi n k f hInd.1 hn hk m' i b,
              digit_liftIndep2_hi n k f hInd.1 hn hk m' j b]
          exact hne_b
        · rw [digit_liftIndep2_hi n k f hInd.1 hn hk m' i b,
              digit_liftIndep2_hi n k f hInd.1 hn hk m' j b]
          exact hadj_b
    refine ⟨hlt, ?_, ?_⟩
    · intro i j hi hj hne heq
      obtain ⟨d, _, hne_d, _⟩ := hnonedge i j hi hj hne
      rw [heq] at hne_d; exact hne_d rfl
    · intro i j hi hj hne
      obtain ⟨d, hd, hne_d, hadj_d⟩ := hnonedge i j hi hj hne
      exact strongPowAdj_false_of_exists_nonedge n adj (2 * (m' + 1)) _ _ d hd hne_d hadj_d

/-- Explicit 5-element independent set in `C_5^{⊠ 2}` (`{(0,0),(1,2),(2,4),(3,1),(4,3)}`). -/
def c5Indep2 : Nat → Nat
  | 0 => 0
  | 1 => 7
  | 2 => 14
  | 3 => 16
  | _ => 23

theorem c5Indep2_valid : IsIndepSet (5 ^ 2) (strongPowAdj 5 c5Adj 2) 5 c5Indep2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi; have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro i j hi hj hne
    have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    have h2 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases h1 with rfl | rfl | rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | decide
  · intro i j hi hj hne
    have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    have h2 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases h1 with rfl | rfl | rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | decide

/-- Adjacency of the 7-cycle `C_7` on `{0, 1, 2, 3, 4, 5, 6}` (`CS-CMP-012` open frontier!). -/
def c7Adj (i j : Nat) : Bool :=
  let d1 := (i + 7 - j % 7) % 7
  let d2 := (j + 7 - i % 7) % 7
  (d1 == 1) || (d2 == 1)

/-- Explicit 10-element independent set in `C_7^{⊠ 2}` (`α(C_7^{⊠ 2}) ≥ 10 > 3^2 = 9`). -/
def c7Indep2 : Nat → Nat
  | 0 => 0   -- (0, 0)
  | 1 => 2   -- (0, 2)
  | 2 => 11  -- (1, 4)
  | 3 => 14  -- (2, 0)
  | 4 => 16  -- (2, 2)
  | 5 => 25  -- (3, 4)
  | 6 => 29  -- (4, 1)
  | 7 => 34  -- (4, 6)
  | 8 => 38  -- (5, 3)
  | _ => 47  -- (6, 5)

def checkC7Indep2 : Bool :=
  (List.range 10).all fun i =>
    c7Indep2 i < 49 &&
    (List.range 10).all fun j =>
      if i == j then true
      else c7Indep2 i != c7Indep2 j && !strongPowAdj 7 c7Adj 2 (c7Indep2 i) (c7Indep2 j)

theorem checkC7Indep2_ok : checkC7Indep2 = true := by decide

theorem c7Indep2_valid : IsIndepSet (7 ^ 2) (strongPowAdj 7 c7Adj 2) 10 c7Indep2 := by
  have hall := checkC7Indep2_ok
  have hget : ∀ i, i < 10 →
      c7Indep2 i < 49 ∧
      ∀ j, j < 10 → i ≠ j →
        c7Indep2 i ≠ c7Indep2 j ∧ strongPowAdj 7 c7Adj 2 (c7Indep2 i) (c7Indep2 j) = false := by
    intro i hi
    have hmem : i ∈ List.range 10 := List.mem_range.mpr hi
    have h1 := List.all_eq_true.mp hall i hmem
    have ⟨hlt, hrest⟩ := Bool.and_eq_true_iff.mp h1
    refine ⟨of_decide_eq_true hlt, fun j hj hne => ?_⟩
    have h2 := List.all_eq_true.mp hrest j (List.mem_range.mpr hj)
    have hbeq : (i == j) = false := beq_false_of_ne hne
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h2
    have ⟨hnev, hadj⟩ := Bool.and_eq_true_iff.mp h2
    refine ⟨?_, ?_⟩
    · intro heq; simp [heq] at hnev
    · cases h : strongPowAdj 7 c7Adj 2 (c7Indep2 i) (c7Indep2 j)
      · rfl
      · simp [h] at hadj
  exact ⟨fun i hi => (hget i hi).1,
         fun i j hi hj hne => ((hget i hi).2 j hj hne).1,
         fun i j hi hj hne => ((hget i hi).2 j hj hne).2⟩

/-- Explicit 4-clique partition of `C_7` (`{0,1}, {2,3}, {4,5}, {6}`), achieving Haemers rank 4 over EVERY field! -/
def c7Clique (i : Nat) : Nat := i / 2

/-- **Theorem T3j (Zero-Error Shannon Capacity: Field-Universal Haemers Bound, Exact Lovász `Θ(C_5) = √5`, & Exact `C_7` Min-Rank `= 4`):**
    1. **Field-Universal Haemers (1979) Rank Bound:** Over **EVERY `SimpleField F` (incl. `F_2`)**,
       any rank-`r` fitting matrix for `(n, adj)` satisfies **`|S| ≤ r ^ t`** for every independent set
       `S ⊆ G^{⊠ t}` and every `t : Nat`.
    2. **Exact Lovász (1979) Pentagon Capacity `Θ(C_5) = √5`:**
       - Upper bound: for EVERY `t : Nat` and EVERY independent set `S ⊆ C_5^{⊠ t}` of size `k`,
         **`k * k ≤ 5 ^ t`** (exact 3-term `Z[√5]` SOS proof, ZERO Mathlib, ZERO reals!).
       - Matching lower bound: for EVERY `m : Nat`, `C_5^{⊠ 2m}` contains an explicit independent set
         of size **`5 ^ m`** (so `α(C_5^{⊠ 2m}) = 5^m` exactly!).
    3. **Exact `C_7` Frontier (`CS-CMP-012`):**
       - Lower bound: for EVERY `m : Nat`, `C_7^{⊠ 2m}` contains an explicit independent set of size
         **`10 ^ m`** (`Θ(C_7) ≥ √10 ≈ 3.16228`, while exact `Θ(C_7) ∈ [√10, ϑ(C_7) ≈ 3.31767]` remains OPEN!).
       - Exact minimum Haemers rank = 4 over EVERY `SimpleField F`: NO fitting matrix of rank `r ≤ 3`
         exists over ANY field (`10 > 3^2`), while an explicit 4-clique cover gives rank 4 over EVERY field! -/
theorem t3j_shannon_capacity_lovasz_c5_and_haemers :
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
        FitsGraph 7 c7Adj M) := by
  refine ⟨fun _ _ n r t k adj U V M f hUV hFit hInd =>
            haemers_strong_pow_rank_bound n r t k adj U V M f hUV hFit hInd,
          lovasz_c5_strong_pow_upper,
          fun m => ⟨liftIndep2 5 5 c5Indep2 m, indep_lift_even_pow 5 5 c5Adj c5Indep2 (by decide) (by decide) c5Indep2_valid m⟩,
          fun m => ⟨liftIndep2 7 10 c7Indep2 m, indep_lift_even_pow 7 10 c7Adj c7Indep2 (by decide) (by decide) c7Indep2_valid m⟩,
          ?_, ?_⟩
  · intro F _ r U V M hUV hFit
    have hle := haemers_strong_pow_rank_bound 7 r 2 10 c7Adj U V M c7Indep2 hUV hFit c7Indep2_valid
    by_cases h4 : 4 ≤ r
    · exact h4
    · have hsmall : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
      rcases hsmall with rfl | rfl | rfl | rfl <;> omega
  · intro F _
    let U : Nat → Nat → F := fun i s => if c7Clique i = s then 1 else 0
    let V : Nat → Nat → F := fun s j => if c7Clique j = s then 1 else 0
    let M : Nat → Nat → F := fun i j => if c7Clique i = c7Clique j then 1 else 0
    refine ⟨U, V, M, ?_, ?_⟩
    · intro i j hi hj
      dsimp only [U, V, M]
      have hci : c7Clique i < 4 := by unfold c7Clique; omega
      have hterm : ∀ s, (if c7Clique i = s then (1 : F) else 0) * (if c7Clique j = s then 1 else 0) =
          if s = c7Clique i then (if c7Clique i = c7Clique j then 1 else 0) else 0 := by
        intro s
        by_cases h1 : c7Clique i = s
        · subst h1
          simp only [↓reduceIte, CommRing.one_mul]
          by_cases h2 : c7Clique j = c7Clique i
          · simp only [h2, ↓reduceIte]
          · have h2' : c7Clique i ≠ c7Clique j := fun h => h2 h.symm
            simp only [h2, h2', ↓reduceIte]
        · have h1' : s ≠ c7Clique i := fun h => h1 h.symm
          simp only [h1, h1', ↓reduceIte, zero_mul]
      rw [sumR_congr (fun s _ => hterm s)]
      have hsingle : ∀ m (idx : Nat) (val : F), idx < m →
          sumR m (fun s => if s = idx then val else 0) = val := by
        intro m idx val hidx
        induction m with
        | zero => omega
        | succ m' ih =>
          simp only [sumR]
          cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hidx) with
          | inl heq =>
            rw [heq]
            have h0 : sumR m' (fun s => if s = m' then val else 0) = sumR m' (fun _ => 0) :=
              sumR_congr (fun s hs => by
                have hne : s ≠ m' := by omega
                split
                · contradiction
                · rfl)
            rw [h0, sumR_zero_fn, CommRing.zero_add]; simp only [↓reduceIte]
          | inr hlt =>
            have hne : m' ≠ idx := by omega
            simp only [hne, ↓reduceIte, add_zero]
            exact ih hlt
      exact hsingle 4 (c7Clique i) _ hci
    · refine ⟨fun i _ => by dsimp only [M]; simp only [↓reduceIte]; exact Ne.symm SimpleField.zero_ne_one, ?_⟩
      intro i j hi hj hne hadj
      dsimp only [M]
      have hne_c : c7Clique i ≠ c7Clique j := by
        intro heq
        unfold c7Clique at heq
        have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
        have h2 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
        rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hne | omega | (simp [c7Adj] at hadj)
      simp only [hne_c, ↓reduceIte]

end
end TriadFrontier.ShannonCapacity
