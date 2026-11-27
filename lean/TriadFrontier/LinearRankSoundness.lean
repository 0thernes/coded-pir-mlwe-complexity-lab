module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.AlgebraCore
public import TriadFrontier.KoszulTensor
public import TriadFrontier.PIRLinearCerts

/-!
# Linear-Algebraic Soundness of `gf2RankSparse` and `matRankModP` (`ERRATA L02` Closure)

Zero-Mathlib Lean 4.35.0 soundness proofs establishing that the computational Gaussian-elimination
rank procedures used in `T1i` (`matRankModP` over `F_2` and `F_3`) and `T1j` (`gf2RankSparse`
over `F_2^d`) compute the **true vector-space span dimension** `HasSpanDim`:
1. `HasSpanDim_unique`: Over ANY `SimpleField F`, span dimension `HasSpanDim F d rows k` is
   uniquely determined (`k₁ = k₂`), proved via `KoszulTensor.matRankFactor_le`.
2. `gf2RankSparse_sound`: For EVERY `d : Nat` and EVERY sparse row list `rows`,
   `HasSpanDim (Fin 2) d (rows.map (sparseVec d)) (gf2RankSparse d rows)`.
3. `matRankModP_sound_f2` & `matRankModP_sound_f3`: For EVERY `d : Nat` and EVERY dense row list
   `rows` of uniform length `d`, `matRankModP 2 rows` and `matRankModP 3 rows` compute exact
   `HasSpanDim` over `SimpleField (Fin 2)` and `SimpleField (Fin 3)` respectively.
4. Direct corollaries linking `T1i` (`linRay4Spec`) and `T1j` (`ret6F2Arrangement`) directly to
   `HasSpanDim` over `F_2` and `F_3`.
-/

namespace TriadFrontier.LinearRankSoundness

open TriadFrontier.AlgebraCore
open TriadFrontier.KoszulTensor
open TriadFrontier.PIRLinearCerts

@[expose] public section

-- ============================================================================
-- Section 1: Abstract Linear Span, Independence, and Steinitz Uniqueness
-- ============================================================================

/-- Transparent list indexing helper (zero `List.getD` module opacity). -/
def vecAt {α : Type} (defv : α) : List α → Nat → α
  | [], _ => defv
  | x :: _, 0 => x
  | _ :: xs, k + 1 => vecAt defv xs k

/-- Linear combination of a list of vectors in `F^d`, matching list structure directly. -/
def linCombList {F : Type} [SimpleField F] : List (Nat → F) → (Nat → F) → Nat → F
  | [], _, _ => 0
  | r :: rs, cs, j => cs 0 * r j + linCombList rs (fun i => cs (i + 1)) j

theorem linCombList_eq_sumR {F : Type} [SimpleField F] :
    ∀ (rows : List (Nat → F)) (cs : Nat → F) (j : Nat),
      linCombList rows cs j = sumR rows.length (fun i => cs i * vecAt (fun _ => 0) rows i j)
  | [], _, _ => rfl
  | r :: rs, cs, j => by
    simp only [linCombList, List.length_cons]
    rw [Nat.add_comm rs.length 1, sumR_split 1 rs.length]
    have h0 : sumR 1 (fun i => cs i * vecAt (fun _ => 0) (r :: rs) i j) = cs 0 * r j := by
      simp [sumR, vecAt, CommRing.zero_add]
    have hrest : sumR rs.length (fun i => cs (1 + i) * vecAt (fun _ => 0) (r :: rs) (1 + i) j) =
        sumR rs.length (fun i => cs (i + 1) * vecAt (fun _ => 0) rs i j) := by
      apply sumR_congr
      intro i _
      have h1 : 1 + i = i + 1 := Nat.add_comm 1 i
      rw [h1]; rfl
    rw [h0, hrest, linCombList_eq_sumR rs (fun i => cs (i + 1)) j]

theorem linCombList_congr {F : Type} [SimpleField F] :
    ∀ (rows : List (Nat → F)) (cs1 cs2 : Nat → F) (j : Nat),
      (∀ i, i < rows.length → cs1 i = cs2 i) →
      linCombList rows cs1 j = linCombList rows cs2 j
  | [], _, _, _, _ => rfl
  | _ :: rs, cs1, cs2, j, h => by
    simp only [linCombList]
    rw [h 0 (Nat.zero_lt_succ _),
        linCombList_congr rs (fun i => cs1 (i + 1)) (fun i => cs2 (i + 1)) j
          (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

theorem linCombList_zero {F : Type} [SimpleField F] :
    ∀ (rows : List (Nat → F)) (j : Nat),
      linCombList rows (fun _ => (0 : F)) j = 0
  | [], _ => rfl
  | _ :: rs, j => by
    simp only [linCombList, zero_mul, CommRing.zero_add]
    exact linCombList_zero rs j

theorem linCombList_add {F : Type} [SimpleField F] :
    ∀ (rows : List (Nat → F)) (cs1 cs2 : Nat → F) (j : Nat),
      linCombList rows (fun i => cs1 i + cs2 i) j =
      linCombList rows cs1 j + linCombList rows cs2 j
  | [], _, _, _ => by simp [linCombList, add_zero]
  | r :: rs, cs1, cs2, j => by
    simp only [linCombList, right_distrib, linCombList_add rs]
    rw [CommRing.add_assoc, ← CommRing.add_assoc (cs2 0 * r j),
        CommRing.add_comm (cs2 0 * r j) (linCombList rs (fun i => cs1 (i + 1)) j),
        CommRing.add_assoc (linCombList rs (fun i => cs1 (i + 1)) j), ← CommRing.add_assoc]

theorem linCombList_scale {F : Type} [SimpleField F] :
    ∀ (rows : List (Nat → F)) (a : F) (cs : Nat → F) (j : Nat),
      linCombList rows (fun i => a * cs i) j = a * linCombList rows cs j
  | [], _, _, _ => by simp [linCombList, mul_zero]
  | r :: rs, a, cs, j => by
    simp only [linCombList, CommRing.left_distrib, CommRing.mul_assoc, linCombList_scale rs]

theorem linCombList_neg {F : Type} [SimpleField F] (rows : List (Nat → F)) (cs : Nat → F) (j : Nat) :
    linCombList rows (fun i => -(cs i)) j = -(linCombList rows cs j) := by
  have h1 : ∀ i, -(cs i) = (-(1 : F)) * cs i := by
    intro i; rw [neg_mul, CommRing.one_mul]
  rw [linCombList_congr rows (fun i => -(cs i)) (fun i => (-(1 : F)) * cs i) j (fun i _ => h1 i),
      linCombList_scale, neg_mul, CommRing.one_mul]

/-- Vector `v : Nat → F` agrees on coordinates `< d` with an `F`-linear combination of `rows`. -/
def InSpan {F : Type} [SimpleField F] (d : Nat) (rows : List (Nat → F)) (v : Nat → F) : Prop :=
  ∃ cs : Nat → F, ∀ j, j < d → v j = linCombList rows cs j

/-- `basis ⊆ F^d` is `F`-linearly independent on coordinates `< d`. -/
def LinIndep {F : Type} [SimpleField F] (d : Nat) (basis : List (Nat → F)) : Prop :=
  ∀ cs : Nat → F,
    (∀ j, j < d → linCombList basis cs j = 0) →
    ∀ i, i < basis.length → cs i = 0

/-- Exact `F`-vector-space span dimension: `rows` spans a `k`-dimensional subspace of `F^d`. -/
def HasSpanDim {F : Type} [SimpleField F] (d : Nat) (rows : List (Nat → F)) (k : Nat) : Prop :=
  ∃ basis : List (Nat → F),
    basis.length = k ∧
    LinIndep d basis ∧
    (∀ b ∈ basis, InSpan d rows b) ∧
    (∀ r ∈ rows, InSpan d basis r)

theorem inSpan_zero {F : Type} [SimpleField F] (d : Nat) (rows : List (Nat → F)) :
    InSpan d rows (fun _ => 0) :=
  ⟨fun _ => 0, fun j _ => (linCombList_zero rows j).symm⟩

theorem inSpan_add {F : Type} [SimpleField F] {d : Nat} {rows : List (Nat → F)} {u v : Nat → F}
    (hu : InSpan d rows u) (hv : InSpan d rows v) :
    InSpan d rows (fun j => u j + v j) := by
  obtain ⟨c1, h1⟩ := hu
  obtain ⟨c2, h2⟩ := hv
  refine ⟨fun i => c1 i + c2 i, fun j hj => ?_⟩
  dsimp only
  rw [h1 j hj, h2 j hj, linCombList_add]

theorem inSpan_scale {F : Type} [SimpleField F] {d : Nat} {rows : List (Nat → F)} {u : Nat → F}
    (a : F) (hu : InSpan d rows u) :
    InSpan d rows (fun j => a * u j) := by
  obtain ⟨c, h⟩ := hu
  refine ⟨fun i => a * c i, fun j hj => ?_⟩
  dsimp only
  rw [h j hj, linCombList_scale]

theorem inSpan_sub {F : Type} [SimpleField F] {d : Nat} {rows : List (Nat → F)} {u v : Nat → F}
    (hu : InSpan d rows u) (hv : InSpan d rows v) :
    InSpan d rows (fun j => u j - v j) := by
  obtain ⟨c1, h1⟩ := hu
  obtain ⟨c2, h2⟩ := hv
  refine ⟨fun i => c1 i - c2 i, fun j hj => ?_⟩
  dsimp only
  rw [h1 j hj, h2 j hj]
  have hsub : ∀ i, c1 i - c2 i = c1 i + (-(c2 i)) := fun i => CommRing.sub_eq (c1 i) (c2 i)
  rw [linCombList_congr rows (fun i => c1 i - c2 i) (fun i => c1 i + -(c2 i)) j (fun i _ => hsub i),
      linCombList_add, linCombList_neg, ← CommRing.sub_eq]

theorem inSpan_congr {F : Type} [SimpleField F] {d : Nat} {rows : List (Nat → F)} {u v : Nat → F}
    (heq : ∀ j, j < d → u j = v j) (hu : InSpan d rows u) :
    InSpan d rows v := by
  obtain ⟨c, h⟩ := hu
  exact ⟨c, fun j hj => by rw [← heq j hj, h j hj]⟩

theorem inSpan_mem {F : Type} [SimpleField F] (d : Nat) :
    ∀ {rows : List (Nat → F)} {r : Nat → F}, r ∈ rows → InSpan d rows r
  | [], _, h => by cases h
  | x :: xs, r, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | hmem
    · refine ⟨fun i => if i = 0 then 1 else 0, fun j _ => ?_⟩
      simp only [linCombList, ↓reduceIte, CommRing.one_mul]
      have hz : linCombList xs (fun i => if i + 1 = 0 then (1 : F) else 0) j = 0 := by
        rw [linCombList_congr xs _ (fun _ => 0) j (fun _ _ => by simp), linCombList_zero]
      rw [hz, add_zero]
    · obtain ⟨cs, hcs⟩ := inSpan_mem d hmem
      refine ⟨fun i => match i with | 0 => 0 | k + 1 => cs k, fun j hj => ?_⟩
      simp only [linCombList, zero_mul, CommRing.zero_add]
      exact hcs j hj

theorem inSpan_cons_of_inSpan {F : Type} [SimpleField F] {d : Nat} {rows : List (Nat → F)}
    {v : Nat → F} (x : Nat → F) (hv : InSpan d rows v) :
    InSpan d (x :: rows) v := by
  obtain ⟨cs, hcs⟩ := hv
  refine ⟨fun i => match i with | 0 => 0 | k + 1 => cs k, fun j hj => ?_⟩
  simp only [linCombList, zero_mul, CommRing.zero_add]
  exact hcs j hj

theorem inSpan_trans {F : Type} [SimpleField F] {d : Nat} :
    ∀ {A B : List (Nat → F)} {v : Nat → F},
      InSpan d A v → (∀ a ∈ A, InSpan d B a) → InSpan d B v
  | [], B, v, ⟨_, hv⟩, _ => by
    refine ⟨fun _ => 0, fun j hj => ?_⟩
    rw [hv j hj, linCombList, linCombList_zero]
  | a :: as, B, v, ⟨cs, hv⟩, hAB => by
    have ha : InSpan d B a := hAB a (by simp)
    have htail : InSpan d as (fun j => linCombList as (fun i => cs (i + 1)) j) :=
      ⟨fun i => cs (i + 1), fun _ _ => rfl⟩
    have hrest : InSpan d B (fun j => linCombList as (fun i => cs (i + 1)) j) :=
      inSpan_trans htail (fun x hx => hAB x (by simp [hx]))
    have hcomb := inSpan_add (inSpan_scale (cs 0) ha) hrest
    exact inSpan_congr (fun j hj => (hv j hj).symm) hcomb

theorem vecAt_mem {α : Type} (defv : α) :
    ∀ (xs : List α) (i : Nat), i < xs.length → vecAt defv xs i ∈ xs
  | [], _, hi => by simp at hi
  | x :: _, 0, _ => by simp [vecAt]
  | _ :: xs, k + 1, hi => by
    simp only [List.length_cons] at hi
    exact List.mem_cons_of_mem _ (vecAt_mem defv xs k (Nat.lt_of_succ_lt_succ hi))

/-- Helper: If `B1` is linearly independent in `F^d` and `B1 ⊆ Span(B2)` and `B2 ⊆ Span(B1)`,
    then `B1.length ≤ B2.length` (proved directly from `KoszulTensor.matRankFactor_le`). -/
theorem linIndep_length_le_of_mutual_span {F : Type} [SimpleField F] (d : Nat)
    (B1 B2 : List (Nat → F))
    (hInd : LinIndep d B1)
    (h12 : ∀ b ∈ B1, InSpan d B2 b)
    (h21 : ∀ b ∈ B2, InSpan d B1 b) :
    B1.length ≤ B2.length := by
  have hexP : ∀ i, ∃ cs : Nat → F, i < B1.length →
      ∀ j, j < d → vecAt (fun _ => 0) B1 i j =
        sumR B2.length (fun t => cs t * vecAt (fun _ => 0) B2 t j) := by
    intro i
    by_cases hi : i < B1.length
    · obtain ⟨cs, hcs⟩ := h12 _ (vecAt_mem (fun _ => 0) B1 i hi)
      refine ⟨cs, fun _ j hj => ?_⟩
      rw [hcs j hj, linCombList_eq_sumR]
    · exact ⟨fun _ => 0, fun h => absurd h hi⟩
  have hexQ : ∀ t, ∃ cs : Nat → F, t < B2.length →
      ∀ j, j < d → vecAt (fun _ => 0) B2 t j =
        sumR B1.length (fun s => cs s * vecAt (fun _ => 0) B1 s j) := by
    intro t
    by_cases ht : t < B2.length
    · obtain ⟨cs, hcs⟩ := h21 _ (vecAt_mem (fun _ => 0) B2 t ht)
      refine ⟨cs, fun _ j hj => ?_⟩
      rw [hcs j hj, linCombList_eq_sumR]
    · exact ⟨fun _ => 0, fun h => absurd h ht⟩
  let P : Nat → Nat → F := fun i t => Classical.choose (hexP i) t
  let Q : Nat → Nat → F := fun t s => Classical.choose (hexQ t) s
  have hP : ∀ i, i < B1.length → ∀ j, j < d →
      vecAt (fun _ => 0) B1 i j = sumR B2.length (fun t => P i t * vecAt (fun _ => 0) B2 t j) :=
    fun i hi => Classical.choose_spec (hexP i) hi
  have hQ : ∀ t, t < B2.length → ∀ j, j < d →
      vecAt (fun _ => 0) B2 t j = sumR B1.length (fun s => Q t s * vecAt (fun _ => 0) B1 s j) :=
    fun t ht => Classical.choose_spec (hexQ t) ht
  apply matRankFactor_le B2.length B1.length P Q
  intro i s hi hs
  let diff : Nat → F := fun u => matMulF B2.length P Q i u - matIdF i u
  have hzero : ∀ j, j < d → linCombList B1 diff j = 0 := by
    intro j hj
    rw [linCombList_eq_sumR]
    -- Expand `∑_u (matMulF P Q i u - δ_{i,u}) B1_u(j)`
    have hsplit : sumR B1.length (fun u => diff u * vecAt (fun _ => 0) B1 u j) =
        sumR B1.length (fun u => matMulF B2.length P Q i u * vecAt (fun _ => 0) B1 u j) +
        -(sumR B1.length (fun u => matIdF (R := F) i u * vecAt (fun _ => 0) B1 u j)) := by
      rw [← sumR_neg, ← sumR_add]
      apply sumR_congr
      intro u _
      dsimp only [diff]
      rw [CommRing.sub_eq, right_distrib, neg_mul]
    rw [hsplit]
    -- Swap double sum `∑_u (∑_t P i t * Q t u) * B1_u(j) = ∑_t P i t * (∑_u Q t u * B1_u(j))`
    have hswap : ∀ m : Nat,
        sumR B1.length (fun u => sumR m (fun t => P i t * Q t u) * vecAt (fun _ => 0) B1 u j) =
        sumR m (fun t => P i t * sumR B1.length (fun u => Q t u * vecAt (fun _ => 0) B1 u j)) := by
      intro m
      induction m with
      | zero =>
        simp only [sumR]
        rw [sumR_congr (fun _ _ => zero_mul _), sumR_zero_fn]
      | succ k ih =>
        simp only [sumR]
        rw [← ih, sumR_mul_left, ← sumR_add]
        apply sumR_congr
        intro u _
        rw [right_distrib, CommRing.mul_assoc]
    have h1 : sumR B1.length (fun u => matMulF B2.length P Q i u * vecAt (fun _ => 0) B1 u j) =
        vecAt (fun _ => 0) B1 i j := by
      unfold matMulF
      rw [hswap B2.length, hP i hi j hj]
      apply sumR_congr
      intro t ht
      rw [hQ t ht j hj]
    have h2 : ∀ n : Nat,
        sumR n (fun u => matIdF (R := F) i u * vecAt (fun _ => 0) B1 u j) =
        if i < n then vecAt (fun _ => 0) B1 i j else 0 := by
      intro n
      induction n with
      | zero => simp [sumR]
      | succ k ih =>
        simp only [sumR, ih]
        by_cases hik : i = k
        · subst hik
          have hlt1 : ¬ (i < i) := Nat.lt_irrefl i
          have hlt2 : i < i + 1 := Nat.lt_succ_self i
          simp only [hlt1, hlt2, ↓reduceIte, matIdF, CommRing.zero_add, CommRing.one_mul]
        · have hiff : (i < k + 1) ↔ (i < k) := by omega
          have hid : matIdF (R := F) i k = 0 := by simp [matIdF, hik]
          rw [hid, zero_mul, add_zero]
          simp only [hiff]
    rw [h1, h2 B1.length]
    simp only [hi, ↓reduceIte, CommRing.add_neg]
  have hds := hInd diff hzero s hs
  exact eq_of_sub_eq_zero hds

/-- **Steinitz Span-Dimension Uniqueness (over ANY `SimpleField F`):**
    If a row list in `F^d` has span dimension `k₁` and span dimension `k₂`, then `k₁ = k₂`. -/
theorem HasSpanDim_unique {F : Type} [SimpleField F] {d : Nat} {rows : List (Nat → F)}
    {k1 k2 : Nat} (h1 : HasSpanDim d rows k1) (h2 : HasSpanDim d rows k2) : k1 = k2 := by
  obtain ⟨B1, hlen1, hind1, hsub1, hsp1⟩ := h1
  obtain ⟨B2, hlen2, hind2, hsub2, hsp2⟩ := h2
  have h12 : ∀ b ∈ B1, InSpan d B2 b := fun b hb => inSpan_trans (hsub1 b hb) hsp2
  have h21 : ∀ b ∈ B2, InSpan d B1 b := fun b hb => inSpan_trans (hsub2 b hb) hsp1
  have hle1 := linIndep_length_le_of_mutual_span d B1 B2 hind1 h12 h21
  have hle2 := linIndep_length_le_of_mutual_span d B2 B1 hind2 h21 h12
  omega

-- ============================================================================
-- Section 2: Soundness of `gf2RankSparse` over `SimpleField (Fin 2)` (`T1j`)
-- ============================================================================

/-- Interpret a sparse list of bit indices as a vector in `F_2^d`. -/
def sparseVec (d : Nat) : List Nat → Nat → Fin 2
  | [], _ => 0
  | b :: bs, j => (if b < d ∧ b = j then (1 : Fin 2) else 0) + sparseVec d bs j

theorem fin2_add_self : ∀ a : Fin 2, a + a = 0 := by decide

theorem fin2_eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  rcases a with ⟨v, hv⟩
  have h : v = 0 ∨ v = 1 := by omega
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Strict increasing sortedness predicate on `List Nat`. -/
def SortedLt : List Nat → Prop
  | [] => True
  | x :: xs => (∀ y ∈ xs, x < y) ∧ SortedLt xs

theorem toggleBit_mem_lt {d b : Nat} (hb : b < d) :
    ∀ {xs : List Nat}, (∀ x ∈ xs, x < d) → ∀ y ∈ toggleBit b xs, y < d
  | [], _, y, hy => by
    simp only [toggleBit, List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [hy]; exact hb
  | x :: xs, hxs, y, hy => by
    unfold toggleBit at hy
    by_cases hlt : b < x
    · simp only [hlt, ↓reduceIte, List.mem_cons] at hy
      rcases hy with rfl | rfl | hrest
      · exact hb
      · exact hxs _ List.mem_cons_self
      · exact hxs y (by simp [hrest])
    · simp only [hlt, ↓reduceIte] at hy
      by_cases heq : (b == x) = true
      · simp only [heq, ↓reduceIte] at hy
        exact hxs y (by simp [hy])
      · simp only [heq, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hy
        rcases hy with rfl | hrest
        · exact hxs _ List.mem_cons_self
        · exact toggleBit_mem_lt hb (fun z hz => hxs z (by simp [hz])) y hrest

theorem toggleBit_mem_gt {k b : Nat} (hkb : k < b) :
    ∀ {xs : List Nat}, (∀ x ∈ xs, k < x) → ∀ y ∈ toggleBit b xs, k < y
  | [], _, y, hy => by
    simp only [toggleBit, List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [hy]; exact hkb
  | x :: xs, hxs, y, hy => by
    unfold toggleBit at hy
    by_cases hlt : b < x
    · simp only [hlt, ↓reduceIte, List.mem_cons] at hy
      rcases hy with rfl | rfl | hrest
      · exact hkb
      · exact hxs _ List.mem_cons_self
      · exact hxs y (by simp [hrest])
    · simp only [hlt, ↓reduceIte] at hy
      by_cases heq : (b == x) = true
      · simp only [heq, ↓reduceIte] at hy
        exact hxs y (by simp [hy])
      · simp only [heq, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hy
        rcases hy with rfl | hrest
        · exact hxs _ List.mem_cons_self
        · exact toggleBit_mem_gt hkb (fun z hz => hxs z (by simp [hz])) y hrest

theorem toggleBit_sorted (b : Nat) :
    ∀ {xs : List Nat}, SortedLt xs → SortedLt (toggleBit b xs)
  | [], _ => ⟨(fun _ h => by cases h), trivial⟩
  | x :: xs, ⟨hx, hxs⟩ => by
    unfold toggleBit
    by_cases hlt : b < x
    · simp only [hlt, ↓reduceIte]
      refine ⟨fun y hy => ?_, hx, hxs⟩
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hmem
      · exact hlt
      · exact Nat.lt_trans hlt (hx y hmem)
    · simp only [hlt, ↓reduceIte]
      by_cases heq : (b == x) = true
      · simp only [heq, ↓reduceIte]; exact hxs
      · simp only [heq, Bool.false_eq_true, ↓reduceIte]
        have hxb : x < b := by
          have hne : b ≠ x := fun h => heq (beq_iff_eq.mpr h)
          omega
        exact ⟨toggleBit_mem_gt hxb hx, toggleBit_sorted b hxs⟩

theorem sparseVec_toggleBit (d b : Nat) :
    ∀ (xs : List Nat) (j : Nat),
      sparseVec d (toggleBit b xs) j =
      (if b < d ∧ b = j then (1 : Fin 2) else 0) + sparseVec d xs j
  | [], j => rfl
  | x :: xs, j => by
    unfold toggleBit
    by_cases hlt : b < x
    · simp only [hlt, ↓reduceIte, sparseVec]
    · simp only [hlt, ↓reduceIte]
      by_cases heq : (b == x) = true
      · have hbx : b = x := beq_iff_eq.mp heq
        subst hbx
        simp only [heq, ↓reduceIte, sparseVec]
        rw [← CommRing.add_assoc, fin2_add_self, CommRing.zero_add]
      · simp only [heq, Bool.false_eq_true, ↓reduceIte, sparseVec]
        rw [sparseVec_toggleBit d b xs j]
        rw [← CommRing.add_assoc, CommRing.add_comm (if x < d ∧ x = j then (1 : Fin 2) else 0),
            CommRing.add_assoc]

theorem toSparseF2Go_spec (d : Nat) :
    ∀ (bits acc : List Nat),
      SortedLt acc →
      (∀ x ∈ acc, x < d) →
      SortedLt (toSparseF2Go d bits acc) ∧
      (∀ x ∈ toSparseF2Go d bits acc, x < d) ∧
      (∀ j, sparseVec d (toSparseF2Go d bits acc) j = sparseVec d bits j + sparseVec d acc j)
  | [], acc, hs, hlt => by
    refine ⟨hs, hlt, fun j => by simp [toSparseF2Go, sparseVec, CommRing.zero_add]⟩
  | b :: bs, acc, hs, hlt => by
    simp only [toSparseF2Go]
    by_cases hb : b < d
    · simp only [hb, ↓reduceIte]
      have ⟨hs', hlt', hvec⟩ :=
        toSparseF2Go_spec d bs (toggleBit b acc) (toggleBit_sorted b hs) (toggleBit_mem_lt hb hlt)
      refine ⟨hs', hlt', fun j => ?_⟩
      rw [hvec j, sparseVec_toggleBit d b acc j]
      simp only [sparseVec]
      rw [← CommRing.add_assoc, CommRing.add_comm (sparseVec d bs j), CommRing.add_assoc]
    · simp only [hb, ↓reduceIte]
      have ⟨hs', hlt', hvec⟩ := toSparseF2Go_spec d bs acc hs hlt
      refine ⟨hs', hlt', fun j => ?_⟩
      rw [hvec j]
      simp only [sparseVec]
      have hnot : ¬ (b < d ∧ b = j) := fun h => hb h.1
      simp only [hnot, ↓reduceIte, CommRing.zero_add]

theorem toSparseF2_spec (d : Nat) (bits : List Nat) :
    SortedLt (toSparseF2 d bits) ∧
    (∀ x ∈ toSparseF2 d bits, x < d) ∧
    (∀ j, sparseVec d (toSparseF2 d bits) j = sparseVec d bits j) := by
  have ⟨hs, hlt, hv⟩ := toSparseF2Go_spec d bits [] trivial (fun _ h => by cases h)
  exact ⟨hs, hlt, fun j => by unfold toSparseF2; rw [hv j, sparseVec, add_zero]⟩

theorem xorSparse_spec (d : Nat) :
    ∀ (b a : List Nat),
      SortedLt a →
      (∀ x ∈ a, x < d) →
      (∀ x ∈ b, x < d) →
      SortedLt (xorSparse a b) ∧
      (∀ x ∈ xorSparse a b, x < d) ∧
      (∀ j, sparseVec d (xorSparse a b) j = sparseVec d a j + sparseVec d b j)
  | [], a, hs, ha, _ => by
    exact ⟨hs, ha, fun j => by simp [xorSparse, sparseVec, add_zero]⟩
  | x :: xs, a, hs, ha, hb => by
    have hx : x < d := hb x (by simp)
    have hxs : ∀ y ∈ xs, y < d := fun y hy => hb y (by simp [hy])
    have ⟨hs', hlt', hv⟩ :=
      xorSparse_spec d xs (toggleBit x a) (toggleBit_sorted x hs) (toggleBit_mem_lt hx ha) hxs
    refine ⟨hs', hlt', fun j => ?_⟩
    simp only [xorSparse]
    rw [hv j, sparseVec_toggleBit d x a j]
    simp only [sparseVec]
    rw [CommRing.add_comm (if x < d ∧ x = j then (1 : Fin 2) else 0) (sparseVec d a j),
        CommRing.add_assoc]

theorem sparseVec_eq_zero_of_lt_all (d j : Nat) :
    ∀ {xs : List Nat}, (∀ x ∈ xs, j < x) → sparseVec d xs j = 0
  | [], _ => rfl
  | x :: xs, h => by
    simp only [sparseVec]
    have hne : ¬ (x < d ∧ x = j) := by
      have hjx := h x (by simp)
      omega
    simp only [hne, ↓reduceIte, CommRing.zero_add]
    exact sparseVec_eq_zero_of_lt_all d j (fun y hy => h y (by simp [hy]))

theorem sparseVec_head_one {d p : Nat} {rest : List Nat}
    (hs : SortedLt (p :: rest)) (hp : p < d) :
    sparseVec d (p :: rest) p = 1 := by
  simp only [sparseVec, hp, true_and, ↓reduceIte]
  rw [sparseVec_eq_zero_of_lt_all d p hs.1, add_zero]

theorem sparseVec_head_zero_below {d p j : Nat} {rest : List Nat}
    (hs : SortedLt (p :: rest)) (hj : j < p) :
    sparseVec d (p :: rest) j = 0 := by
  apply sparseVec_eq_zero_of_lt_all d j
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hmem
  · exact hj
  · exact Nat.lt_trans hj (hs.1 y hmem)

theorem xorSparse_same_head_lt {d p q : Nat} {rest brest qrest : List Nat}
    (hs1 : SortedLt (p :: rest)) (hlt1 : ∀ x ∈ p :: rest, x < d)
    (hs2 : SortedLt (p :: brest)) (hlt2 : ∀ x ∈ p :: brest, x < d)
    (hxor : xorSparse (p :: rest) (p :: brest) = q :: qrest) :
    p < q := by
  have ⟨hs3, hlt3, hvec⟩ := xorSparse_spec d (p :: brest) (p :: rest) hs1 hlt1 hlt2
  rw [hxor] at hs3 hlt3 hvec
  have hq_lt : q < d := hlt3 q (by simp)
  have hq1 : sparseVec d (q :: qrest) q = 1 := sparseVec_head_one hs3 hq_lt
  by_cases hle : q ≤ p
  · cases Nat.eq_or_lt_of_le hle with
    | inl heq =>
      subst heq
      have h0 : sparseVec d (q :: qrest) q = 0 := by
        rw [hvec q, sparseVec_head_one hs1 hq_lt, sparseVec_head_one hs2 hq_lt, fin2_add_self]
      rw [h0] at hq1
      exact absurd hq1 SimpleField.zero_ne_one
    | inr hlt =>
      have h0 : sparseVec d (q :: qrest) q = 0 := by
        rw [hvec q, sparseVec_head_zero_below hs1 hlt, sparseVec_head_zero_below hs2 hlt, add_zero]
      rw [h0] at hq1
      exact absurd hq1 SimpleField.zero_ne_one
  · omega

-- ============================================================================
-- Section 2b: PivotTrie Lookup/Insert Correctness
-- ============================================================================

def TrieDepth : Nat → PivotTrie → Prop
  | _, PivotTrie.empty => True
  | 0, PivotTrie.leaf _ => True
  | _ + 1, PivotTrie.leaf _ => False
  | 0, PivotTrie.node _ _ => False
  | d + 1, PivotTrie.node l r => TrieDepth d l ∧ TrieDepth d r

theorem trieDepth_empty (d : Nat) : TrieDepth d PivotTrie.empty := by
  cases d <;> trivial

theorem trieDepth_insert :
    ∀ (depth key bits : Nat) (row : List Nat) (t : PivotTrie),
      TrieDepth depth t → TrieDepth depth (trieInsert depth key bits row t)
  | 0, _, _, _, PivotTrie.empty, _ => trivial
  | 0, _, _, _, PivotTrie.leaf _, _ => trivial
  | 0, _, _, _, PivotTrie.node _ _, h => h
  | d + 1, key, bits, row, PivotTrie.empty, _ => by
    unfold trieInsert
    split
    · exact ⟨trieDepth_insert d key (bits / 2) row PivotTrie.empty (trieDepth_empty d), trieDepth_empty d⟩
    · exact ⟨trieDepth_empty d, trieDepth_insert d key (bits / 2) row PivotTrie.empty (trieDepth_empty d)⟩
  | _ + 1, _, _, _, PivotTrie.leaf _, h => False.elim h
  | d + 1, key, bits, row, PivotTrie.node l r, ⟨hl, hr⟩ => by
    unfold trieInsert
    split
    · exact ⟨trieDepth_insert d key (bits / 2) row l hl, hr⟩
    · exact ⟨hl, trieDepth_insert d key (bits / 2) row r hr⟩

theorem trieLookup_insert_same :
    ∀ (depth key bits : Nat) (row : List Nat) (t : PivotTrie),
      TrieDepth depth t →
      trieLookup depth key bits (trieInsert depth key bits row t) = some row
  | 0, key, _, row, PivotTrie.empty, _ => by simp [trieInsert, trieLookup, bucketLookup]
  | 0, key, _, row, PivotTrie.leaf _, _ => by simp [trieInsert, trieLookup, bucketLookup]
  | 0, _, _, _, PivotTrie.node _ _, h => False.elim h
  | d + 1, key, bits, row, PivotTrie.empty, _ => by
    unfold trieInsert
    by_cases he : (bits % 2 == 0) = true
    · simp only [he, ↓reduceIte, trieLookup]
      exact trieLookup_insert_same d key (bits / 2) row PivotTrie.empty (trieDepth_empty d)
    · simp only [he, Bool.false_eq_true, ↓reduceIte, trieLookup]
      exact trieLookup_insert_same d key (bits / 2) row PivotTrie.empty (trieDepth_empty d)
  | _ + 1, _, _, _, PivotTrie.leaf _, h => False.elim h
  | d + 1, key, bits, row, PivotTrie.node l r, ⟨hl, hr⟩ => by
    unfold trieInsert
    by_cases he : (bits % 2 == 0) = true
    · simp only [he, ↓reduceIte, trieLookup]
      exact trieLookup_insert_same d key (bits / 2) row l hl
    · simp only [he, Bool.false_eq_true, ↓reduceIte, trieLookup]
      exact trieLookup_insert_same d key (bits / 2) row r hr

theorem trieLookup_insert_ne :
    ∀ (depth p pBits q qBits : Nat) (row : List Nat) (t : PivotTrie),
      TrieDepth depth t → p ≠ q →
      trieLookup depth p pBits (trieInsert depth q qBits row t) = trieLookup depth p pBits t
  | 0, p, _, q, _, row, PivotTrie.empty, _, hne => by
    have hbf : (q == p) = false := beq_false_of_ne (Ne.symm hne)
    simp [trieInsert, trieLookup, bucketLookup, hbf]
  | 0, p, _, q, _, row, PivotTrie.leaf b, _, hne => by
    have hbf : (q == p) = false := beq_false_of_ne (Ne.symm hne)
    simp [trieInsert, trieLookup, bucketLookup, hbf]
  | 0, _, _, _, _, _, PivotTrie.node _ _, h, _ => False.elim h
  | d + 1, p, pBits, q, qBits, row, PivotTrie.empty, _, hne => by
    unfold trieInsert
    by_cases hq : (qBits % 2 == 0) = true
    · simp only [hq, ↓reduceIte, trieLookup]
      by_cases hp : (pBits % 2 == 0) = true
      · simp only [hp, ↓reduceIte]
        simpa [trieLookup] using trieLookup_insert_ne d p (pBits / 2) q (qBits / 2) row PivotTrie.empty (trieDepth_empty d) hne
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    · simp only [hq, Bool.false_eq_true, ↓reduceIte, trieLookup]
      by_cases hp : (pBits % 2 == 0) = true
      · simp only [hp, ↓reduceIte]
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
        simpa [trieLookup] using trieLookup_insert_ne d p (pBits / 2) q (qBits / 2) row PivotTrie.empty (trieDepth_empty d) hne
  | _ + 1, _, _, _, _, _, PivotTrie.leaf _, h, _ => False.elim h
  | d + 1, p, pBits, q, qBits, row, PivotTrie.node l r, ⟨hl, hr⟩, hne => by
    unfold trieInsert
    by_cases hq : (qBits % 2 == 0) = true
    · simp only [hq, ↓reduceIte, trieLookup]
      by_cases hp : (pBits % 2 == 0) = true
      · simp only [hp, ↓reduceIte]
        exact trieLookup_insert_ne d p (pBits / 2) q (qBits / 2) row l hl hne
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    · simp only [hq, Bool.false_eq_true, ↓reduceIte, trieLookup]
      by_cases hp : (pBits % 2 == 0) = true
      · simp only [hp, ↓reduceIte]
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
        exact trieLookup_insert_ne d p (pBits / 2) q (qBits / 2) row r hr hne

-- ============================================================================
-- Section 2c: Triangular Linear Independence and `gf2RankSparse_sound`
-- ============================================================================

/-- Basis invariant for sparse F_2 pivot rows paired with their leading bit indices. -/
def SparsePivotInv (d : Nat) (origin : List (Nat → Fin 2))
    (t : PivotTrie) (basis : List (Nat × List Nat)) : Prop :=
  TrieDepth 6 t ∧
  PairwiseNeq (basis.map Prod.fst) ∧
  (∀ p brow, trieLookup 6 p p t = some brow → (p, brow) ∈ basis) ∧
  (∀ pb ∈ basis, trieLookup 6 pb.1 pb.1 t = some pb.2) ∧
  (∀ pb ∈ basis, SortedLt pb.2 ∧ (∀ x ∈ pb.2, x < d) ∧
    (∃ rt, pb.2 = pb.1 :: rt) ∧ InSpan d origin (sparseVec d pb.2))

theorem exists_min_nonzero_pivot :
    ∀ (basis : List (Nat × List Nat)) (cs : Nat → Fin 2),
      (∃ i, i < basis.length ∧ cs i ≠ 0) →
      ∃ im, im < basis.length ∧ cs im ≠ 0 ∧
        ∀ i, i < basis.length → cs i ≠ 0 → (vecAt (0, []) basis im).1 ≤ (vecAt (0, []) basis i).1
  | [], _, ⟨_, hi, _⟩ => by simp at hi
  | (p, row) :: rest, cs, hex => by
    by_cases htail : ∃ k, k < rest.length ∧ cs (k + 1) ≠ 0
    · obtain ⟨km, hkm, hnz, hmin⟩ := exists_min_nonzero_pivot rest (fun k => cs (k + 1)) htail
      by_cases h0 : cs 0 ≠ 0
      · by_cases hle : p ≤ (vecAt (0, []) rest km).1
        · refine ⟨0, Nat.zero_lt_succ _, h0, fun i hi hci => ?_⟩
          cases i with
          | zero => exact Nat.le_refl _
          | succ k => exact Nat.le_trans hle (hmin k (Nat.lt_of_succ_lt_succ hi) hci)
        · refine ⟨km + 1, Nat.succ_lt_succ hkm, hnz, fun i hi hci => ?_⟩
          cases i with
          | zero => dsimp only [vecAt]; omega
          | succ k => exact hmin k (Nat.lt_of_succ_lt_succ hi) hci
      · refine ⟨km + 1, Nat.succ_lt_succ hkm, hnz, fun i hi hci => ?_⟩
        cases i with
        | zero => exact absurd hci h0
        | succ k => exact hmin k (Nat.lt_of_succ_lt_succ hi) hci
    · obtain ⟨i0, hi0, hci0⟩ := hex
      cases i0 with
      | zero =>
        refine ⟨0, Nat.zero_lt_succ _, hci0, fun i hi hci => ?_⟩
        cases i with
        | zero => exact Nat.le_refl _
        | succ k => exact absurd ⟨k, Nat.lt_of_succ_lt_succ hi, hci⟩ htail
      | succ k => exact absurd ⟨k, Nat.lt_of_succ_lt_succ hi0, hci0⟩ htail

theorem pairwiseNeq_vecAt {α : Type} (defv : α) :
    ∀ {xs : List α}, PairwiseNeq xs →
      ∀ i j, i < xs.length → j < xs.length → i ≠ j → vecAt defv xs i ≠ vecAt defv xs j
  | [], _, _, _, hi, _, _ => by simp at hi
  | x :: xs, ⟨hhead, htail⟩, i, j, hi, hj, hij => by
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j' =>
        dsimp only [vecAt]
        exact hhead _ (vecAt_mem defv xs j' (Nat.lt_of_succ_lt_succ hj))
    | succ i' =>
      cases j with
      | zero =>
        dsimp only [vecAt]
        exact Ne.symm (hhead _ (vecAt_mem defv xs i' (Nat.lt_of_succ_lt_succ hi)))
      | succ j' =>
        dsimp only [vecAt]
        exact pairwiseNeq_vecAt defv htail i' j'
          (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) (fun h => hij (congrArg Nat.succ h))

theorem vecAt_map {α β : Type} (da : α) (db : β) (f : α → β) :
    ∀ (xs : List α) (i : Nat), i < xs.length → vecAt db (xs.map f) i = f (vecAt da xs i)
  | [], _, hi => by simp at hi
  | _ :: _, 0, _ => rfl
  | _ :: xs, k + 1, hi => vecAt_map da db f xs k (Nat.lt_of_succ_lt_succ hi)

theorem sparsePivot_linIndep {d : Nat} {origin : List (Nat → Fin 2)}
    {t : PivotTrie} {basis : List (Nat × List Nat)}
    (hinv : SparsePivotInv d origin t basis) :
    LinIndep d (basis.map (fun pb => sparseVec d pb.2)) := by
  intro cs hzero i hi
  by_cases hne : cs i = 0
  · exact hne
  · rw [List.length_map] at hi
    obtain ⟨im, him, hcm, hmin⟩ := exists_min_nonzero_pivot basis cs ⟨i, hi, hne⟩
    let pmin := (vecAt (0, []) basis im).1
    have hmem_m := vecAt_mem (0, []) basis im him
    have ⟨hsm, hltm, ⟨rtm, hrowm⟩, _⟩ := hinv.2.2.2.2 _ hmem_m
    have hpmin_lt : pmin < d := hltm pmin (by rw [hrowm]; exact List.mem_cons_self)
    have hsum0 := hzero pmin hpmin_lt
    rw [linCombList_eq_sumR, List.length_map] at hsum0
    -- Every term `k ≠ im` is 0, and term `im` is 1!
    have hterm : ∀ k, k < basis.length →
        cs k * vecAt (fun _ => 0) (basis.map (fun pb => sparseVec d pb.2)) k pmin =
        if k = im then (1 : Fin 2) else 0 := by
      intro k hk
      rw [vecAt_map (0, []) (fun _ => 0) (fun pb => sparseVec d pb.2) basis k hk]
      by_cases hkim : k = im
      · subst hkim
        simp only [↓reduceIte]
        have hcm1 : cs k = 1 := by
          rcases fin2_eq_zero_or_one (cs k) with h0 | h1
          · exact absurd h0 hcm
          · exact h1
        rw [hcm1, CommRing.one_mul, hrowm]
        exact sparseVec_head_one (by rwa [← hrowm]) hpmin_lt
      · simp only [hkim, ↓reduceIte]
        by_cases hck : cs k = 0
        · rw [hck, zero_mul]
        · have hle := hmin k hk hck
          have hneq : pmin ≠ (vecAt (0, []) basis k).1 := by
            have hpw := pairwiseNeq_vecAt 0 hinv.2.1 im k
              (by simpa using him) (by simpa using hk) (Ne.symm hkim)
            rw [vecAt_map (0, []) 0 Prod.fst basis im him,
                vecAt_map (0, []) 0 Prod.fst basis k hk] at hpw
            exact hpw
          have hlt_pk : pmin < (vecAt (0, []) basis k).1 := by omega
          have ⟨hsk, _, ⟨rtk, hrowk⟩, _⟩ := hinv.2.2.2.2 _ (vecAt_mem (0, []) basis k hk)
          rw [hrowk, sparseVec_head_zero_below (by rwa [← hrowk]) hlt_pk, mul_zero]
    have hsum_single : ∀ n : Nat,
        sumR n (fun k => if k = im then (1 : Fin 2) else 0) = if im < n then 1 else 0 := by
      intro n
      induction n with
      | zero => simp [sumR]
      | succ m ih =>
        simp only [sumR, ih]
        by_cases hmeq : m = im
        · subst hmeq
          have h1 : ¬ (m < m) := Nat.lt_irrefl m
          have h2 : m < m + 1 := Nat.lt_succ_self m
          simp only [h1, h2, ↓reduceIte, CommRing.zero_add]
        · have hiff : (im < m + 1) ↔ (im < m) := by omega
          simp only [hmeq, ↓reduceIte, add_zero, hiff]
    rw [sumR_congr hterm, hsum_single basis.length] at hsum0
    simp only [him, ↓reduceIte] at hsum0
    exact absurd hsum0.symm SimpleField.zero_ne_one

theorem reduceSparse_spec {d : Nat} {origin : List (Nat → Fin 2)}
    {t : PivotTrie} {basis : List (Nat × List Nat)}
    (hinv : SparsePivotInv d origin t basis) :
    ∀ (fuel : Nat) (v : List Nat),
      SortedLt v →
      (∀ x ∈ v, x < d) →
      (v = [] ∨ ∃ p rt, v = p :: rt ∧ d - p ≤ fuel) →
      let res := reduceSparse fuel t v
      SortedLt res ∧
      (∀ x ∈ res, x < d) ∧
      (res = [] ∨ ∃ r rt, res = r :: rt ∧ trieLookup 6 r r t = none) ∧
      InSpan d (basis.map (fun pb => sparseVec d pb.2))
        (fun j => sparseVec d v j + sparseVec d res j)
  | 0, [], _, _, _ => by
    refine ⟨trivial, (fun _ h => by cases h), Or.inl rfl, ?_⟩
    exact inSpan_congr (fun j _ => by simp [reduceSparse, sparseVec, add_zero]) (inSpan_zero d _)
  | 0, p :: rt, _, hlt, hfuel => by
    rcases hfuel with hnil | ⟨p', _, heq, hle⟩
    · cases hnil
    · injection heq with hp _
      subst hp
      have hpd : p < d := hlt p (by simp)
      omega
  | fuel' + 1, [], _, _, _ => by
    refine ⟨trivial, (fun _ h => by cases h), Or.inl rfl, ?_⟩
    exact inSpan_congr (fun j _ => by simp [reduceSparse, sparseVec, add_zero]) (inSpan_zero d _)
  | fuel' + 1, p :: rt, hs, hlt, hfuel => by
    dsimp only [reduceSparse]
    cases hlu : trieLookup 6 p p t with
    | none =>
      refine ⟨hs, hlt, Or.inr ⟨p, rt, rfl, hlu⟩, ?_⟩
      exact inSpan_congr (fun j _ => (fin2_add_self _).symm) (inSpan_zero d _)
    | some brow =>
      have hmem : (p, brow) ∈ basis := hinv.2.2.1 p brow hlu
      have ⟨hsb, hltb, ⟨brest, hbrow⟩, _⟩ := hinv.2.2.2.2 (p, brow) hmem
      let v' := xorSparse (p :: rt) brow
      have ⟨hs', hlt', hvec'⟩ := xorSparse_spec d brow (p :: rt) hs hlt hltb
      have hfuel' : v' = [] ∨ ∃ q qrt, v' = q :: qrt ∧ d - q ≤ fuel' := by
        cases hv' : v' with
        | nil => exact Or.inl rfl
        | cons q qrt =>
          right
          have hlt_pq : p < q := xorSparse_same_head_lt hs hlt (by rwa [← hbrow]) (by rwa [← hbrow])
            (by rw [← hbrow]; exact hv')
          rcases hfuel with hnil | ⟨p', _, heq, hle⟩
          · cases hnil
          · injection heq with hp _; subst hp
            exact ⟨q, qrt, rfl, by omega⟩
      have ⟨hsr, hltr, hfresh, hsp'⟩ := reduceSparse_spec hinv fuel' v' hs' hlt' hfuel'
      refine ⟨hsr, hltr, hfresh, ?_⟩
      have hbrow_in : InSpan d (basis.map (fun pb => sparseVec d pb.2)) (sparseVec d brow) :=
        inSpan_mem d (List.mem_map_of_mem hmem)
      have hsum := inSpan_add hsp' hbrow_in
      refine inSpan_congr (fun j _ => ?_) hsum
      dsimp only
      rw [hvec' j]
      calc sparseVec d (p :: rt) j + sparseVec d brow j + sparseVec d (reduceSparse fuel' t v') j +
            sparseVec d brow j
          = sparseVec d (p :: rt) j + sparseVec d (reduceSparse fuel' t v') j +
            (sparseVec d brow j + sparseVec d brow j) := by
              rw [CommRing.add_assoc (sparseVec d (p :: rt) j),
                  CommRing.add_comm (sparseVec d brow j) (sparseVec d (reduceSparse fuel' t v') j),
                  ← CommRing.add_assoc (sparseVec d (p :: rt) j),
                  CommRing.add_assoc]
        _ = sparseVec d (p :: rt) j + sparseVec d (reduceSparse fuel' t v') j := by
              rw [fin2_add_self, add_zero]

theorem gf2RankSparseGo_sound (d : Nat) (origin : List (Nat → Fin 2)) :
    ∀ (rem : List (List Nat)) (t : PivotTrie) (basis : List (Nat × List Nat)),
      SparsePivotInv d origin t basis →
      (∀ r ∈ rem, InSpan d origin (sparseVec d r)) →
      ∃ basis' : List (Nat × List Nat),
        basis'.length = gf2RankSparseGo d rem t basis.length ∧
        LinIndep d (basis'.map (fun pb => sparseVec d pb.2)) ∧
        (∀ pb ∈ basis', InSpan d origin (sparseVec d pb.2)) ∧
        (∀ pb ∈ basis, InSpan d (basis'.map (fun pb => sparseVec d pb.2)) (sparseVec d pb.2)) ∧
        (∀ r ∈ rem, InSpan d (basis'.map (fun pb => sparseVec d pb.2)) (sparseVec d r))
  | [], t, basis, hinv, _ => by
    refine ⟨basis, rfl, sparsePivot_linIndep hinv,
            fun pb hpb => (hinv.2.2.2.2 pb hpb).2.2.2,
            fun pb hpb => inSpan_mem d (List.mem_map_of_mem hpb),
            fun _ h => by cases h⟩
  | row :: rest, t, basis, hinv, hrem => by
    have hrow_in : InSpan d origin (sparseVec d row) := hrem row (by simp)
    have hrest_in : ∀ r ∈ rest, InSpan d origin (sparseVec d r) := fun r hr => hrem r (by simp [hr])
    let v := toSparseF2 d row
    have ⟨hsv, hltv, hvecv⟩ := toSparseF2_spec d row
    have hfuelv : v = [] ∨ ∃ p rt, v = p :: rt ∧ d - p ≤ d := by
      cases hv : v with
      | nil => exact Or.inl rfl
      | cons p rt => exact Or.inr ⟨p, rt, rfl, Nat.sub_le d p⟩
    have ⟨hsr, hltr, hfresh, hdiff⟩ := reduceSparse_spec hinv d v hsv hltv hfuelv
    simp only [gf2RankSparseGo]
    cases hred : reduceSparse d t v with
    | nil =>
      rw [hred] at hdiff
      have hrow_sp : InSpan d (basis.map (fun pb => sparseVec d pb.2)) (sparseVec d row) :=
        inSpan_congr (fun j _ => by rw [sparseVec, add_zero, hvecv j]) hdiff
      obtain ⟨basis', hlen', hind', hsub', hkeep', hrem'⟩ :=
        gf2RankSparseGo_sound d origin rest t basis hinv hrest_in
      refine ⟨basis', hlen', hind', hsub', hkeep', fun r hr => ?_⟩
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hmem
      · exact inSpan_trans hrow_sp (fun b hb => by
          obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hb
          exact hkeep' pb hpb)
      · exact hrem' r hmem
    | cons p pt =>
      rw [hred] at hsr hltr hfresh hdiff
      have hlu_none : trieLookup 6 p p t = none := by
        rcases hfresh with hnil | ⟨r, _, heq, hlu⟩
        · cases hnil
        · injection heq with hr _; subst hr; exact hlu
      -- Show `p` is fresh (not among `basis.map Prod.fst`)
      have hp_not_mem : ∀ q ∈ basis.map Prod.fst, p ≠ q := by
        intro q hq heq
        subst heq
        obtain ⟨pb, hpb, hfst⟩ := List.mem_map.mp hq
        have hsome := hinv.2.2.2.1 pb hpb
        rw [hfst] at hsome
        rw [hlu_none] at hsome
        cases hsome
      -- Show `sparseVec d (p :: pt) ∈ InSpan d origin`
      have hdiff_orig : InSpan d origin (fun j => sparseVec d v j + sparseVec d (p :: pt) j) :=
        inSpan_trans hdiff (fun b hb => by
          obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hb
          exact (hinv.2.2.2.2 pb hpb).2.2.2)
      have hv_orig : InSpan d origin (sparseVec d v) :=
        inSpan_congr (fun j _ => (hvecv j).symm) hrow_in
      have hp_orig : InSpan d origin (sparseVec d (p :: pt)) := by
        have hadd := inSpan_add hv_orig hdiff_orig
        refine inSpan_congr (fun j _ => ?_) hadd
        change sparseVec d v j + (sparseVec d v j + sparseVec d (p :: pt) j) = sparseVec d (p :: pt) j
        rw [← CommRing.add_assoc, fin2_add_self, CommRing.zero_add]
      -- Build new invariant on `(p, p :: pt) :: basis` and `t' = trieInsert 6 p p (p :: pt) t`
      let t' := trieInsert 6 p p (p :: pt) t
      let basis1 := (p, p :: pt) :: basis
      have hinv1 : SparsePivotInv d origin t' basis1 := by
        refine ⟨trieDepth_insert 6 p p (p :: pt) t hinv.1, ⟨hp_not_mem, hinv.2.1⟩, ?_, ?_, ?_⟩
        · intro q brow hlu
          by_cases hqp : q = p
          · subst hqp
            rw [trieLookup_insert_same 6 q q (q :: pt) t hinv.1] at hlu
            injection hlu with heq; subst heq
            exact List.mem_cons_self
          · rw [trieLookup_insert_ne 6 q q p p (p :: pt) t hinv.1 hqp] at hlu
            exact List.mem_cons_of_mem _ (hinv.2.2.1 q brow hlu)
        · intro pb hpb
          simp only [basis1, List.mem_cons] at hpb
          rcases hpb with rfl | hmem
          · exact trieLookup_insert_same 6 p p (p :: pt) t hinv.1
          · have hne : pb.1 ≠ p := Ne.symm (hp_not_mem pb.1 (List.mem_map_of_mem hmem))
            rw [trieLookup_insert_ne 6 pb.1 pb.1 p p (p :: pt) t hinv.1 hne]
            exact hinv.2.2.2.1 pb hmem
        · intro pb hpb
          simp only [basis1, List.mem_cons] at hpb
          rcases hpb with rfl | hmem
          · exact ⟨hsr, hltr, ⟨pt, rfl⟩, hp_orig⟩
          · exact hinv.2.2.2.2 pb hmem
      have hlen1 : basis1.length = basis.length + 1 := rfl
      obtain ⟨basis', hlen', hind', hsub', hkeep', hrem'⟩ :=
        gf2RankSparseGo_sound d origin rest t' basis1 hinv1 hrest_in
      rw [hlen1] at hlen'
      refine ⟨basis', hlen', hind', hsub',
              fun pb hpb => hkeep' pb (List.mem_cons_of_mem _ hpb),
              fun r hr => ?_⟩
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hmem
      · -- `sparseVec d r = sparseVec d (p :: pt) + (v + (p :: pt))` ∈ Span(basis1) ⊆ Span(basis')
        have hrow_b1 : InSpan d (basis1.map (fun pb => sparseVec d pb.2)) (sparseVec d r) := by
          have hp_in : InSpan d (basis1.map (fun pb => sparseVec d pb.2)) (sparseVec d (p :: pt)) :=
            inSpan_mem d (by simp [basis1])
          have hdiff_b1 : InSpan d (basis1.map (fun pb => sparseVec d pb.2))
              (fun j => sparseVec d v j + sparseVec d (p :: pt) j) :=
            inSpan_cons_of_inSpan (sparseVec d (p :: pt)) hdiff
          have hadd := inSpan_add hdiff_b1 hp_in
          refine inSpan_congr (fun j _ => ?_) hadd
          change (sparseVec d v j + sparseVec d (p :: pt) j) + sparseVec d (p :: pt) j = sparseVec d r j
          rw [CommRing.add_assoc, fin2_add_self, add_zero, hvecv j]
        exact inSpan_trans hrow_b1 (fun b hb => by
          obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hb
          exact hkeep' pb hpb)
      · exact hrem' r hmem

/-- **Theorem (`gf2RankSparse_sound` — Closes `L02` for `T1j`):**
    For EVERY ambient dimension `d : Nat` and EVERY sparse row list `rows : List (List Nat)`,
    `gf2RankSparse d rows` equals the EXACT `F_2`-vector-space span dimension `HasSpanDim` of
    `rows.map (sparseVec d)` in `F_2^d`. -/
theorem gf2RankSparse_sound (d : Nat) (rows : List (List Nat)) :
    HasSpanDim (F := Fin 2) d (rows.map (sparseVec d)) (gf2RankSparse d rows) := by
  have hinv0 : SparsePivotInv d (rows.map (sparseVec d)) PivotTrie.empty [] :=
    ⟨trieDepth_empty 6, trivial, (fun _ _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩
  obtain ⟨basis', hlen', hind', hsub', _, hrem'⟩ :=
    gf2RankSparseGo_sound d (rows.map (sparseVec d)) rows PivotTrie.empty [] hinv0
      (fun r hr => inSpan_mem d (List.mem_map_of_mem hr))
  refine ⟨basis'.map (fun pb => sparseVec d pb.2), by rw [List.length_map]; exact hlen', hind', ?_, ?_⟩
  · intro b hb
    obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hb
    exact hsub' pb hpb
  · intro r hr
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hr
    exact hrem' row hrow

-- ============================================================================
-- Section 3: Soundness of `matRankModP` for `p = 2` and `p = 3` (`T1i`)
-- ============================================================================

/-- Interpret a dense `List Nat` row as a vector in `(Fin p)^d`. -/
def denseVec2 (row : List Nat) (j : Nat) : Fin 2 :=
  ⟨row.getD j 0 % 2, Nat.mod_lt _ (by decide)⟩

def denseVec3 (row : List Nat) (j : Nat) : Fin 3 :=
  ⟨row.getD j 0 % 3, Nat.mod_lt _ (by decide)⟩

theorem fin2_self_inv : ∀ x : Fin 2, x ≠ 0 → x * x = 1 := by decide

theorem fin3_self_inv : ∀ x : Fin 3, x ≠ 0 → x * x = 1 := by decide

theorem matRankModP_go_shift (p : Nat) :
    ∀ (fuel col rk : Nat) (A : List (List Nat)),
      matRankModP.go p col fuel A rk = rk + matRankModP.go p col fuel A 0
  | 0, _, _, _ => by simp [matRankModP.go]
  | fuel' + 1, col, rk, A => by
    unfold matRankModP.go
    cases A.find? (fun r => r.getD col 0 % p != 0) with
    | none => exact matRankModP_go_shift p fuel' (col + 1) rk A
    | some piv =>
      dsimp only
      rw [matRankModP_go_shift p fuel' (col + 1) (rk + 1),
          matRankModP_go_shift p fuel' (col + 1) 1]
      omega

theorem getD_map_lt {α β : Type} (da : α) (db : β) (f : α → β) :
    ∀ (xs : List α) (j : Nat), j < xs.length → (xs.map f).getD j db = f (xs.getD j da)
  | [], _, hj => by simp at hj
  | _ :: _, 0, _ => rfl
  | _ :: xs, k + 1, hj => getD_map_lt da db f xs k (Nat.lt_of_succ_lt_succ hj)

theorem getD_zip_lt {α β : Type} (da : α) (db : β) :
    ∀ (xs : List α) (ys : List β) (j : Nat),
      j < xs.length → j < ys.length →
      (xs.zip ys).getD j (da, db) = (xs.getD j da, ys.getD j db)
  | [], _, _, hx, _ => by simp at hx
  | _, [], _, _, hy => by simp at hy
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: xs, _ :: ys, k + 1, hx, hy =>
      getD_zip_lt da db xs ys k (Nat.lt_of_succ_lt_succ hx) (Nat.lt_of_succ_lt_succ hy)

theorem mem_erase_or_eq {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (xs : List α) (a x : α), x ∈ xs → x = a ∨ x ∈ xs.erase a
  | [], _, _, h => by cases h
  | y :: ys, a, x, h => by
    simp only [List.erase_cons]
    by_cases hya : y == a
    · simp only [hya, ↓reduceIte]
      have hyeq : y = a := beq_iff_eq.mp hya
      simp only [List.mem_cons] at h
      rcases h with rfl | hmem
      · exact Or.inl hyeq
      · exact Or.inr hmem
    · simp only [hya, Bool.false_eq_true, ↓reduceIte]
      simp only [List.mem_cons] at h
      rcases h with rfl | hmem
      · exact Or.inr List.mem_cons_self
      · rcases mem_erase_or_eq ys a x hmem with rfl | hrest
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem _ hrest)

theorem mem_of_mem_erase {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs : List α} {a x : α}, x ∈ xs.erase a → x ∈ xs
  | [], _, _, h => by cases h
  | y :: ys, a, x, h => by
    simp only [List.erase_cons] at h
    by_cases hya : y == a
    · simp only [hya, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ h
    · simp only [hya, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | hrest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_erase hrest)

theorem find_some_mem_and_pred {α : Type} (P : α → Bool) :
    ∀ {xs : List α} {a : α}, xs.find? P = some a → a ∈ xs ∧ P a = true
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    simp only [List.find?] at h
    cases hpx : P x with
    | true =>
      rw [hpx] at h
      injection h with hxa; subst hxa
      exact ⟨List.mem_cons_self, hpx⟩
    | false =>
      rw [hpx] at h
      have ⟨hm, hp⟩ := find_some_mem_and_pred P h
      exact ⟨List.mem_cons_of_mem _ hm, hp⟩

theorem find_none_false {α : Type} (P : α → Bool) :
    ∀ {xs : List α}, xs.find? P = none → ∀ x ∈ xs, P x = false
  | [], _, _, h => by cases h
  | x :: xs, h, y, hy => by
    simp only [List.find?] at h
    cases hpx : P x with
    | true =>
      rw [hpx] at h; cases h
    | false =>
      rw [hpx] at h
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hmem
      · exact hpx
      · exact find_none_false P h y hmem

theorem inSpan_vanish_below {F : Type} [SimpleField F] {d col : Nat}
    {rows : List (Nat → F)} {v : Nat → F}
    (hvan : ∀ r ∈ rows, ∀ j, j < col → r j = 0)
    (hv : InSpan d rows v) :
    ∀ j, j < d → j < col → v j = 0 := by
  obtain ⟨cs, hcs⟩ := hv
  intro j hjd hjc
  rw [hcs j hjd]
  clear hcs hjd
  induction rows generalizing cs with
  | nil => rfl
  | cons r rs ih =>
    simp only [linCombList]
    rw [hvan r (by simp) j hjc, mul_zero, CommRing.zero_add]
    exact ih (fun x hx => hvan x (by simp [hx])) (fun i => cs (i + 1))

/-- Generic Gaussian elimination step lemma over ANY `SimpleField F` with a mod-`p` embedding
    `ofMod : Nat → F` for `p ∈ {2, 3}` (where every nonzero residue is self-inverse!).
    Parameterized over abstract `F` to avoid any `Fin.instMul` vs `SimpleField.toMul` diamond. -/
theorem matRankModP_go_sound_aux (p : Nat) (hp : 0 < p) (F : Type) [SimpleField F]
    (ofMod : Nat → F)
    (hmod : ∀ a, ofMod (a % p) = ofMod a)
    (hzero : ofMod 0 = 0)
    (hone : ofMod 1 = 1)
    (hadd : ∀ a b, ofMod (a + b) = ofMod a + ofMod b)
    (hmul : ∀ a b, ofMod (a * b) = ofMod a * ofMod b)
    (hsub : ∀ a b, b < p → ofMod (a + p * p - b) = ofMod a - ofMod b)
    (hself : ∀ a, a % p ≠ 0 → ofMod a * ofMod a = 1)
    (hzero_iff : ∀ a, ofMod a = 0 ↔ a % p = 0)
    (d : Nat) :
    ∀ (fuel col : Nat) (A : List (List Nat)),
      col + fuel = d →
      (∀ r ∈ A, r.length = d) →
      (∀ r ∈ A, ∀ j, j < col → r.getD j 0 % p = 0) →
      let toV : List Nat → Nat → F := fun r j => ofMod (r.getD j 0)
      HasSpanDim (F := F) d (A.map toV) (matRankModP.go p col fuel A 0)
  | 0, col, A, hcd, _, hvan => by
    intro toV
    refine ⟨[], rfl, (fun _ _ _ hi => by simp at hi), (fun _ h => by cases h), ?_⟩
    intro v hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    refine ⟨fun _ => 0, fun j hj => ?_⟩
    dsimp only [toV]
    rw [linCombList, (hzero_iff (r.getD j 0)).mpr (hvan r hr j (by omega))]
  | fuel' + 1, col, A, hcd, hlen, hvan => by
    intro toV
    unfold matRankModP.go
    cases hfind : A.find? (fun r => r.getD col 0 % p != 0) with
    | none =>
      have hvan' : ∀ r ∈ A, ∀ j, j < col + 1 → r.getD j 0 % p = 0 := by
        intro r hr j hj
        cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with
        | inl heq =>
          subst heq
          have hf := find_none_false (fun (r : List Nat) => r.getD j 0 % p != 0) hfind r hr
          simpa using hf
        | inr hlt => exact hvan r hr j hlt
      exact matRankModP_go_sound_aux p hp F ofMod hmod hzero hone hadd hmul hsub hself hzero_iff d
        fuel' (col + 1) A (by omega) hlen hvan'
    | some piv =>
      have ⟨hpiv_mem, hpiv_nz_b⟩ := find_some_mem_and_pred (fun (r : List Nat) => r.getD col 0 % p != 0) hfind
      have hpiv_nz_nat : piv.getD col 0 % p ≠ 0 := by simpa using hpiv_nz_b
      let pv : Nat := piv.getD col 0 % p
      let pvF : F := ofMod pv
      have hpv_sq : pvF * pvF = 1 := by
        dsimp only [pvF, pv]
        rw [hmod]
        exact hself (piv.getD col 0) hpiv_nz_nat
      let pivNorm : List Nat := piv.map (fun x => (x * pv) % p)
      let rest : List (List Nat) := A.erase piv
      let elimRow : List Nat → List Nat := fun r =>
        let f := r.getD col 0 % p
        if f == 0 then r
        else (r.zip pivNorm).map (fun ab => (ab.1 + p * p - (f * ab.2) % p) % p)
      let elim : List (List Nat) := rest.map elimRow
      have hpiv_len : piv.length = d := hlen piv hpiv_mem
      have hpivNorm_len : pivNorm.length = d := by simp [pivNorm, hpiv_len]
      -- Coordinate formula for `pivNorm`
      have hpivNorm_vec : ∀ j, j < d → toV pivNorm j = pvF * toV piv j := by
        intro j hj
        dsimp only [toV, pivNorm, pvF]
        rw [getD_map_lt 0 0 (fun x => (x * pv) % p) piv j (by omega), hmod, hmul, CommRing.mul_comm]
      -- `pivNorm` vanishes on `< col` and equals `1` at `col`
      have hpivNorm_van : ∀ j, j < col → pivNorm.getD j 0 % p = 0 := by
        intro j hj
        dsimp only [pivNorm]
        rw [getD_map_lt 0 0 (fun x => (x * pv) % p) piv j (by omega), Nat.mod_mod,
            Nat.mul_mod, hvan piv hpiv_mem j hj, Nat.zero_mul, Nat.zero_mod]
      have hpivNorm_col : toV pivNorm col = 1 := by
        rw [hpivNorm_vec col (by omega)]
        dsimp only [toV, pvF, pv]
        rw [hmod]
        exact hself (piv.getD col 0) hpiv_nz_nat
      -- Coordinate formula for `elimRow r`
      have helim_vec : ∀ r ∈ rest, ∀ j, j < d →
          toV (elimRow r) j = toV r j - ofMod (r.getD col 0) * toV pivNorm j := by
        intro r hr j hj
        have hr_len : r.length = d := hlen r (mem_of_mem_erase hr)
        dsimp only [elimRow]
        by_cases hf : (r.getD col 0 % p == 0) = true
        · have hf0 : r.getD col 0 % p = 0 := beq_iff_eq.mp hf
          simp only [hf, ↓reduceIte]
          rw [(hzero_iff (r.getD col 0)).mpr hf0, zero_mul, CommRing.sub_eq, neg_zero, add_zero]
        · simp only [hf, Bool.false_eq_true, ↓reduceIte]
          dsimp only [toV]
          rw [getD_map_lt (0, 0) 0 (fun ab => (ab.1 + p * p - (r.getD col 0 % p * ab.2) % p) % p)
                (r.zip pivNorm) j (by simp [hr_len, hpivNorm_len]; omega),
              getD_zip_lt 0 0 r pivNorm j (by omega) (by omega),
              hmod, hsub _ _ (Nat.mod_lt _ hp), hmod, hmul, hmod]
      -- Length & vanishing invariants for `elim`
      have helim_len : ∀ r' ∈ elim, r'.length = d := by
        intro r' hr'
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
        have hr_len : r.length = d := hlen r (mem_of_mem_erase hr)
        dsimp only [elimRow]
        split
        · exact hr_len
        · simp [hr_len, hpivNorm_len]
      have helim_van : ∀ r' ∈ elim, ∀ j, j < col + 1 → r'.getD j 0 % p = 0 := by
        intro r' hr' j hj
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
        apply (hzero_iff _).mp
        change toV (elimRow r) j = 0
        rw [helim_vec r hr j (by omega)]
        cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with
        | inl heq =>
          subst heq
          rw [hpivNorm_col, mul_one]
          exact sub_self _
        | inr hlt =>
          have hr0 : toV r j = 0 := (hzero_iff _).mpr (hvan r (mem_of_mem_erase hr) j hlt)
          have hp0 : toV pivNorm j = 0 := (hzero_iff _).mpr (hpivNorm_van j hlt)
          rw [hr0, hp0, mul_zero, sub_self]
      -- Inductive hypothesis on `elim`
      have ⟨Btail, hBlen, hBind, hBsub, hBspan⟩ :=
        matRankModP_go_sound_aux p hp F ofMod hmod hzero hone hadd hmul hsub hself hzero_iff d
          fuel' (col + 1) elim (by omega) helim_len helim_van
      -- Assemble new basis `toV pivNorm :: Btail`!
      dsimp only
      rw [matRankModP_go_shift p fuel' (col + 1) 1 elim]
      refine ⟨toV pivNorm :: Btail, by simp [hBlen, Nat.add_comm], ?_, ?_, ?_⟩
      · -- Linear independence of `toV pivNorm :: Btail`
        intro cs hcs0 i hi
        have hBtail_van : ∀ b ∈ Btail, b col = 0 := by
          intro b hb
          apply inSpan_vanish_below (d := d) (col := col + 1)
            (rows := elim.map toV)
            (fun v hv j hj => by
              obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hv
              exact (hzero_iff _).mpr (helim_van r' hr' j hj))
            (hBsub b hb) col (by omega) (Nat.lt_succ_self col)
        have hc0 : cs 0 = 0 := by
          have hcol0 := hcs0 col (by omega)
          simp only [linCombList, hpivNorm_col, mul_one] at hcol0
          have htail0 : linCombList Btail (fun k => cs (k + 1)) col = 0 := by
            clear hcol0 hcs0 hi hBlen hBind hBsub hBspan
            generalize (fun k => cs (k + 1)) = cs'
            induction Btail generalizing cs' with
            | nil => rfl
            | cons b bs ih =>
              simp only [linCombList, hBtail_van b (by simp), mul_zero, CommRing.zero_add]
              exact ih (fun x hx => hBtail_van x (by simp [hx])) (fun k => cs' (k + 1))
          rw [htail0, add_zero] at hcol0
          exact hcol0
        cases i with
        | zero => exact hc0
        | succ k =>
          have htail_zero : ∀ j, j < d → linCombList Btail (fun m => cs (m + 1)) j = 0 := by
            intro j hj
            have h0 := hcs0 j hj
            simp only [linCombList, hc0, zero_mul, CommRing.zero_add] at h0
            exact h0
          exact hBind (fun m => cs (m + 1)) htail_zero k (Nat.lt_of_succ_lt_succ hi)
      · -- Every basis vector lies in `InSpan d (A.map toV)`
        have hpivNorm_in_A : InSpan d (A.map toV) (toV pivNorm) :=
          inSpan_congr (fun j hj => (hpivNorm_vec j hj).symm)
            (inSpan_scale pvF (inSpan_mem d (List.mem_map_of_mem hpiv_mem)))
        have helim_in_A : ∀ v ∈ elim.map toV, InSpan d (A.map toV) v := by
          intro v hv
          obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hv
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
          have hr_in : InSpan d (A.map toV) (toV r) :=
            inSpan_mem d (List.mem_map_of_mem (mem_of_mem_erase hr))
          exact inSpan_congr (fun j hj => (helim_vec r hr j hj).symm)
            (inSpan_sub hr_in (inSpan_scale (ofMod (r.getD col 0)) hpivNorm_in_A))
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hmem
        · exact hpivNorm_in_A
        · exact inSpan_trans (hBsub b hmem) helim_in_A
      · -- Every row of `A` lies in `InSpan d (toV pivNorm :: Btail)`
        intro v hv
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
        rcases mem_erase_or_eq A piv r hr with rfl | hrest
        · -- `toV r = pvF * toV pivNorm` (since `r = piv`)
          have hpiv_rec : ∀ j, j < d → pvF * toV pivNorm j = toV r j := by
            intro j hj
            rw [hpivNorm_vec j hj, ← CommRing.mul_assoc, hpv_sq, CommRing.one_mul]
          exact inSpan_congr hpiv_rec (inSpan_scale pvF (inSpan_mem d List.mem_cons_self))
        · -- `toV r = toV (elimRow r) + f * toV pivNorm`
          have hel_in : InSpan d (toV pivNorm :: Btail) (toV (elimRow r)) :=
            inSpan_cons_of_inSpan (toV pivNorm)
              (hBspan (toV (elimRow r)) (List.mem_map_of_mem (List.mem_map_of_mem hrest)))
          have hp_in : InSpan d (toV pivNorm :: Btail)
              (fun j => ofMod (r.getD col 0) * toV pivNorm j) :=
            inSpan_scale (ofMod (r.getD col 0)) (inSpan_mem d List.mem_cons_self)
          have hadd := inSpan_add hel_in hp_in
          refine inSpan_congr (fun j hj => ?_) hadd
          change toV (elimRow r) j + ofMod (r.getD col 0) * toV pivNorm j = toV r j
          rw [helim_vec r hrest j hj, CommRing.sub_eq, CommRing.add_assoc, neg_add, add_zero]

/-- Helper embedding `Nat → Fin 2` matching `SimpleField (Fin 2)`. -/
def ofMod2 (n : Nat) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by decide)⟩

/-- Helper embedding `Nat → Fin 3` matching `SimpleField (Fin 3)`. -/
def ofMod3 (n : Nat) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩

/-- **Theorem (`matRankModP_sound_f2` — Closes `L02` for `F_2` in `T1i`):**
    For EVERY uniform-width row list `rows` of width `d`, `matRankModP 2 rows` equals the EXACT
    `F_2`-vector-space span dimension `HasSpanDim` of `rows.map denseVec2` in `F_2^d`. -/
theorem matRankModP_sound_f2 (d : Nat) (rows : List (List Nat))
    (hlen : ∀ r ∈ rows, r.length = d) :
    HasSpanDim (F := Fin 2) d (rows.map denseVec2) (matRankModP 2 rows) := by
  cases rows with
  | nil =>
    exact ⟨[], rfl, (fun _ _ _ hi => by simp at hi), (fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons r0 rs =>
    have hr0 : r0.length = d := hlen r0 List.mem_cons_self
    unfold matRankModP
    dsimp only
    rw [hr0]
    have hmod2 : ∀ a, ofMod2 (a % 2) = ofMod2 a := fun a => Fin.ext (Nat.mod_mod a 2)
    have hz2 : ∀ a, ofMod2 a = 0 ↔ a % 2 = 0 := fun a =>
      ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    refine matRankModP_go_sound_aux 2 (by decide) (Fin 2) ofMod2 hmod2 rfl rfl ?_ ?_ ?_ ?_ hz2
      d d 0 (r0 :: rs) (Nat.zero_add d) hlen (fun _ _ _ hj => absurd hj (Nat.not_lt_zero _))
    · intro a b; apply Fin.ext; exact Nat.add_mod a b 2
    · intro a b; apply Fin.ext; exact Nat.mul_mod a b 2
    · intro a b hb
      apply Fin.ext
      change (a + 2 * 2 - b) % 2 = (a % 2 + 2 - b % 2) % 2
      have hbm : b % 2 = b := Nat.mod_eq_of_lt hb
      rw [hbm]
      have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb' : b = 0 ∨ b = 1 := by omega
      rcases ha with ha0 | ha1 <;> rcases hb' with rfl | rfl <;> omega
    · intro a ha
      have ha1 : a % 2 = 1 := by omega
      apply Fin.ext; change (a % 2 * (a % 2)) % 2 = 1; rw [ha1]

/-- **Theorem (`matRankModP_sound_f3` — Closes `L02` for `F_3` in `T1i`):**
    For EVERY uniform-width row list `rows` of width `d`, `matRankModP 3 rows` equals the EXACT
    `F_3`-vector-space span dimension `HasSpanDim` of `rows.map denseVec3` in `F_3^d`. -/
theorem matRankModP_sound_f3 (d : Nat) (rows : List (List Nat))
    (hlen : ∀ r ∈ rows, r.length = d) :
    HasSpanDim (F := Fin 3) d (rows.map denseVec3) (matRankModP 3 rows) := by
  cases rows with
  | nil =>
    exact ⟨[], rfl, (fun _ _ _ hi => by simp at hi), (fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons r0 rs =>
    have hr0 : r0.length = d := hlen r0 List.mem_cons_self
    unfold matRankModP
    dsimp only
    rw [hr0]
    have hmod3 : ∀ a, ofMod3 (a % 3) = ofMod3 a := fun a => Fin.ext (Nat.mod_mod a 3)
    have hz3 : ∀ a, ofMod3 a = 0 ↔ a % 3 = 0 := fun a =>
      ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    refine matRankModP_go_sound_aux 3 (by decide) (Fin 3) ofMod3 hmod3 rfl rfl ?_ ?_ ?_ ?_ hz3
      d d 0 (r0 :: rs) (Nat.zero_add d) hlen (fun _ _ _ hj => absurd hj (Nat.not_lt_zero _))
    · intro a b; apply Fin.ext; exact Nat.add_mod a b 3
    · intro a b; apply Fin.ext; exact Nat.mul_mod a b 3
    · intro a b hb
      apply Fin.ext
      change (a + 3 * 3 - b) % 3 = (a % 3 + 3 - b % 3) % 3
      have hbm : b % 3 = b := Nat.mod_eq_of_lt hb
      rw [hbm]
      have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
      have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases ha with ha0 | ha1 | ha2 <;> rcases hb' with rfl | rfl | rfl <;> omega
    · intro a ha
      have ha12 : a % 3 = 1 ∨ a % 3 = 2 := by omega
      apply Fin.ext; change (a % 3 * (a % 3)) % 3 = 1
      rcases ha12 with h1 | h2
      · rw [h1]
      · rw [h2]

-- ============================================================================
-- Section 4: Direct Corollary Linking `T1j` (`hUncondRet6`) to True `HasSpanDim`
-- ============================================================================

/-- Exact union of sparse generator rows of `ret6F2Arrangement` selected by subset mask `m ∈ 1..63`. -/
def ret6SubsetRows (mask : Nat) : List (List Nat) :=
  let s0 := if (mask % 2) == 1 then getSub6 ret6F2Arrangement 0 else []
  let s1 := if ((mask / 2) % 2) == 1 then getSub6 ret6F2Arrangement 1 else []
  let s2 := if ((mask / 4) % 2) == 1 then getSub6 ret6F2Arrangement 2 else []
  let s3 := if ((mask / 8) % 2) == 1 then getSub6 ret6F2Arrangement 3 else []
  let s4 := if ((mask / 16) % 2) == 1 then getSub6 ret6F2Arrangement 4 else []
  let s5 := if ((mask / 32) % 2) == 1 then getSub6 ret6F2Arrangement 5 else []
  s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5

/-- **Direct `T1j` Linear-Algebraic Soundness Corollary:**
    For EVERY non-empty subset `m ∈ {1..63}` of `{W1, W2, A1, A2, A3, A4}`, the true `F_2`-vector-space
    span dimension of `ret6SubsetRows m` in `F_2^64` is literally `hUncondRet6 m / 4` (with `hUncondRet6 m`
    exact multiple of `4`)! -/
theorem t1j_ret6_true_f2_span_dim :
    ∀ m : Nat, 1 ≤ m → m ≤ 63 →
      HasSpanDim (F := Fin 2) 64 ((ret6SubsetRows m).map (sparseVec 64)) (hUncondRet6 m / 4) ∧
      4 * (hUncondRet6 m / 4) = hUncondRet6 m := by
  intro m hm1 hm63
  have heq := h_uncond_ret6_eq_4_times_f2_64 m hm1 hm63
  have hdiv : hUncondRet6 m / 4 = subspaceRank6F2 64 ret6F2Arrangement m := by omega
  refine ⟨?_, by omega⟩
  rw [hdiv]
  exact gf2RankSparse_sound 64 (ret6SubsetRows m)

end
end TriadFrontier.LinearRankSoundness
