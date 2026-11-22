/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.LocalEntropy

/-!
# The Feng–Huang variational principle, Lower half: weighted Bowen content

Auxiliary material for `FengHuangLower.lean` (D.-J. Feng and W. Huang, *Variational principles
for topological entropies of subsets*, J. Funct. Anal. 263 (2012), §3).

* `fhLowerWeightedContent T s ε N g`: the weighted Bowen content `W^s_{N,ε}(g)` of a function
  `g : X → [0, ∞]` (Feng–Huang (3.1), base `2`): the infimum of `∑ c(n, x) 2^{-s n}` over weights
  `c : ℕ × X → [0, ∞]` carried by orders `n ≥ N` with `g ≤ ∑ c(n, x) 1_{B_n(x, ε)}`. Weights on
  `ℕ × X` (an unordered `ENNReal` sum) encode countable families with repetitions.
* Its basic properties: monotone, subadditive, positively homogeneous, `W 0 = 0`, finite on
  constants (compact `X`), at most `2^{-s n}` on one Bowen ball of order `n ≥ N`.
* `fhLower_lowerContent_le_weightedContent`: the comparison
  `lowerContent T 0 .centered Z (s + δ) (2ε) N ≤ W^s_{N,ε}(1_Z)` when `∑_{k} 2^{-δ (k + N)} < 1`.
  The proof replaces Feng–Huang's Vitali covering argument: at a fixed order `n` all balls have
  the same radius, so a maximal `(n, 2ε)`-separated subset of the set where the order-`n` part of
  the weighted sum exceeds `2^{-δ n}` covers it and has at most `2^{δ n} ∑_x c(n, x)` points.

With the zero potential the centered ball weight is `1` (`fhLower_pressureBallWeight_zero`), so
the library's `lowerContent T 0 .centered Z s r N` is Feng–Huang's `M^s_{N, r}(Z)` in base `2`
with open Bowen balls and countable covers by balls of orders `≥ max 1 N`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X]

/-! ### The Bowen content at the zero potential -/

/-- With the zero potential the centered ball weight is `1`: the library's lower content at
the zero potential is the unweighted Bowen content `M^s_{N, r}` of Feng–Huang (base `2`). -/
theorem fhLower_pressureBallWeight_zero (T : X → X) (n : ℕ) (y : X) (r : ℝ) :
    pressureBallWeight T (fun _ ↦ 0) .centered n y r = 1 := by
  simp [pressureBallWeight, birkhoffSum]

/-- A countable family of Bowen balls of orders `≥ max 1 N` covering `Z` bounds the lower content
at the zero potential by its cost `∑ 2^{-s nᵢ}`. -/
theorem fhLower_lowerContent_le_of_countable {ι : Type*} [Countable ι] (T : X → X) (Z : Set X)
    (s r : ℝ) (N : ℕ) (x : ι → X) (n : ι → ℕ) (hn : ∀ i, max 1 N ≤ n i)
    (hZ : Z ⊆ ⋃ i, bowenBall T (n i) (x i) r) :
    lowerContent T (fun _ ↦ 0) .centered Z s r N ≤ ∑' i, (2 : ℝ≥0∞) ^ (-s * (n i : ℝ)) := by
  obtain ⟨f, hf⟩ := exists_injective_nat ι
  let e : ι ≃ range f := Equiv.ofInjective f hf
  let C : BowenCoverFamily X := ⟨range f, fun j ↦ x (e.symm j), fun j ↦ n (e.symm j)⟩
  have hC : IsBowenCover T Z r N C := by
    refine ⟨fun j ↦ hn _, fun z hz ↦ ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hZ hz)
    exact mem_iUnion.2 ⟨e i, by simpa [C] using hi⟩
  unfold lowerContent
  refine (iInf₂_le C hC).trans_eq ?_
  simp only [bowenCoverCost, fhLower_pressureBallWeight_zero, mul_one, C]
  exact e.symm.tsum_eq (fun i ↦ (2 : ℝ≥0∞) ^ (-s * (n i : ℝ)))

/-- Raising the order cutoff can only increase the lower content. -/
theorem fhLower_lowerContent_mono_cutoff (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (Z : Set X) (s r : ℝ) {N M : ℕ} (h : N ≤ M) :
    lowerContent T φ w Z s r N ≤ lowerContent T φ w Z s r M := by
  unfold lowerContent
  exact iInf_mono fun C ↦ iInf_mono' fun hC ↦
    ⟨⟨fun j ↦ (max_le_max le_rfl h).trans (hC.1 j), hC.2⟩, le_rfl⟩

/-! ### Weighted Bowen content -/

/-- A weight `c` on (order, center) pairs is a weighted cover of `g` at radius `ε` and cutoff `N`:
it vanishes below order `N` and `g ≤ ∑ c(n, x) 1_{B_n(x, ε)}`. -/
def FhLowerWeightedCover (T : X → X) (ε : ℝ) (N : ℕ) (g : X → ℝ≥0∞) (c : ℕ × X → ℝ≥0∞) :
    Prop :=
  (∀ q : ℕ × X, q.1 < N → c q = 0) ∧
    ∀ z, g z ≤ ∑' q : ℕ × X, c q * (bowenBall T q.1 q.2 ε).indicator 1 z

/-- The cost `∑ c(n, x) 2^{-s n}` of a weight on (order, center) pairs. -/
noncomputable def fhLowerWeightedCost (s : ℝ) (c : ℕ × X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' q : ℕ × X, c q * (2 : ℝ≥0∞) ^ (-s * (q.1 : ℝ))

/-- The weighted Bowen content `W^s_{N,ε}(g)` of Feng–Huang (3.1), base `2`: the infimum of the
costs of weighted covers of `g`. -/
noncomputable def fhLowerWeightedContent (T : X → X) (s ε : ℝ) (N : ℕ) (g : X → ℝ≥0∞) :
    ℝ≥0∞ :=
  ⨅ (c : ℕ × X → ℝ≥0∞) (_ : FhLowerWeightedCover T ε N g c), fhLowerWeightedCost s c

/-- The weighted content is at most the cost of any weighted cover. -/
theorem fhLower_weightedContent_le_cost {T : X → X} {s ε : ℝ} {N : ℕ} {g : X → ℝ≥0∞}
    {c : ℕ × X → ℝ≥0∞} (hc : FhLowerWeightedCover T ε N g c) :
    fhLowerWeightedContent T s ε N g ≤ fhLowerWeightedCost s c :=
  iInf₂_le c hc

omit [MetricSpace X] in
/-- Sums over (order, center) pairs split as iterated sums. -/
theorem fhLower_tsum_prod (f : ℕ × X → ℝ≥0∞) : ∑' q, f q = ∑' n, ∑' x, f (n, x) :=
  ENNReal.tsum_prod (f := fun n x ↦ f (n, x))

/-- The weighted content is monotone in the function. -/
theorem fhLower_weightedContent_mono (T : X → X) (s ε : ℝ) (N : ℕ) {g₁ g₂ : X → ℝ≥0∞}
    (h : g₁ ≤ g₂) :
    fhLowerWeightedContent T s ε N g₁ ≤ fhLowerWeightedContent T s ε N g₂ :=
  le_iInf₂ fun c hc ↦ iInf₂_le c ⟨hc.1, fun z ↦ (h z).trans (hc.2 z)⟩

/-- The weighted content is subadditive. -/
theorem fhLower_weightedContent_add_le (T : X → X) (s ε : ℝ) (N : ℕ) (g₁ g₂ : X → ℝ≥0∞) :
    fhLowerWeightedContent T s ε N (g₁ + g₂) ≤
      fhLowerWeightedContent T s ε N g₁ + fhLowerWeightedContent T s ε N g₂ := by
  unfold fhLowerWeightedContent
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun c₂ ↦ le_iInf fun h₂ ↦ le_iInf fun c₁ ↦ le_iInf fun h₁ ↦ ?_
  have hc : FhLowerWeightedCover T ε N (g₁ + g₂) (c₁ + c₂) := by
    refine ⟨fun q hq ↦ by simp [h₁.1 q hq, h₂.1 q hq], fun z ↦ ?_⟩
    simp only [Pi.add_apply, add_mul]
    rw [ENNReal.tsum_add]
    exact add_le_add (h₁.2 z) (h₂.2 z)
  refine (iInf₂_le (c₁ + c₂) hc).trans_eq ?_
  simp only [fhLowerWeightedCost, Pi.add_apply, add_mul]
  exact ENNReal.tsum_add

/-- Scaling a function by a finite constant scales the weighted content at most by it. -/
theorem fhLower_weightedContent_mul_le (T : X → X) (s ε : ℝ) (N : ℕ) (g : X → ℝ≥0∞)
    {a : ℝ≥0∞} (ha0 : a ≠ 0) (haT : a ≠ ⊤) :
    fhLowerWeightedContent T s ε N (fun z ↦ a * g z) ≤ a * fhLowerWeightedContent T s ε N g := by
  unfold fhLowerWeightedContent
  simp only [ENNReal.mul_iInf_of_ne ha0 haT]
  refine le_iInf fun c ↦ le_iInf fun hc ↦ ?_
  have hc' : FhLowerWeightedCover T ε N (fun z ↦ a * g z) (fun q ↦ a * c q) := by
    refine ⟨fun q hq ↦ by simp [hc.1 q hq], fun z ↦ ?_⟩
    simp only [mul_assoc]
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul_right (hc.2 z) a
  refine (iInf₂_le _ hc').trans_eq ?_
  simp only [fhLowerWeightedCost, mul_assoc]
  exact ENNReal.tsum_mul_left

/-- The weighted content is positively homogeneous. -/
theorem fhLower_weightedContent_mul (T : X → X) (s ε : ℝ) (N : ℕ) (g : X → ℝ≥0∞)
    {a : ℝ≥0∞} (ha0 : a ≠ 0) (haT : a ≠ ⊤) :
    fhLowerWeightedContent T s ε N (fun z ↦ a * g z) = a * fhLowerWeightedContent T s ε N g := by
  refine le_antisymm (fhLower_weightedContent_mul_le T s ε N g ha0 haT) ?_
  have h := fhLower_weightedContent_mul_le T s ε N (fun z ↦ a * g z)
    (ENNReal.inv_ne_zero.2 haT) (ENNReal.inv_ne_top.2 ha0)
  simp only [← mul_assoc, ENNReal.inv_mul_cancel ha0 haT, one_mul] at h
  calc a * fhLowerWeightedContent T s ε N g
      ≤ a * (a⁻¹ * fhLowerWeightedContent T s ε N fun z ↦ a * g z) := mul_le_mul_right h a
    _ = _ := by rw [← mul_assoc, ENNReal.mul_inv_cancel ha0 haT, one_mul]

/-- The weighted content of the zero function vanishes. -/
theorem fhLower_weightedContent_zero (T : X → X) (s ε : ℝ) (N : ℕ) :
    fhLowerWeightedContent T s ε N (fun _ ↦ 0) = 0 := by
  refine le_antisymm ((fhLower_weightedContent_le_cost (c := fun _ ↦ 0) ?_).trans_eq ?_) bot_le
  · exact ⟨fun _ _ ↦ rfl, fun _ ↦ zero_le⟩
  · simp [fhLowerWeightedCost]

/-- The weighted content of the indicator of one Bowen ball of order `n ≥ N` is at most
`2^{-s n}`. -/
theorem fhLower_weightedContent_bowenBall_le (T : X → X) (s ε : ℝ) {N n : ℕ} (hn : N ≤ n)
    (x : X) :
    fhLowerWeightedContent T s ε N ((bowenBall T n x ε).indicator 1) ≤
      (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) := by
  classical
  let c : ℕ × X → ℝ≥0∞ := fun q ↦ if q = (n, x) then 1 else 0
  have hc : FhLowerWeightedCover T ε N ((bowenBall T n x ε).indicator 1) c := by
    refine ⟨fun q hq ↦ ?_, fun z ↦ ?_⟩
    · have : q ≠ (n, x) := fun h ↦ by rw [h] at hq; exact absurd hn (not_le.2 hq)
      simp [c, this]
    · refine le_trans ?_ (ENNReal.le_tsum (n, x))
      simp [c]
  refine (fhLower_weightedContent_le_cost hc).trans_eq ?_
  rw [fhLowerWeightedCost, tsum_eq_single (n, x) (fun q hq ↦ by simp [c, hq])]
  simp [c]

/-- On a compact space, the weighted content of a finite constant is finite. -/
theorem fhLower_weightedContent_const_lt_top [CompactSpace X] {T : X → X} (hT : Continuous T)
    (s : ℝ) {ε : ℝ} (hε : 0 < ε) (N : ℕ) {b : ℝ≥0∞} (hb : b ≠ ⊤) :
    fhLowerWeightedContent T s ε N (fun _ ↦ b) < ⊤ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ bowenBall T N x ε)
    (fun x ↦ bowen_ball_dense_open T hT N x ε)
    (fun x _ ↦ mem_iUnion.2 ⟨x, self_mem_bowenBall T N x ε hε⟩)
  let S : Finset (ℕ × X) := ({N} : Finset ℕ) ×ˢ t
  let c : ℕ × X → ℝ≥0∞ := fun q ↦ if q ∈ S then b else 0
  have hc : FhLowerWeightedCover T ε N (fun _ ↦ b) c := by
    refine ⟨fun q hq ↦ ?_, fun z ↦ ?_⟩
    · have : q ∉ S := by
        simp only [S, Finset.mem_product, Finset.mem_singleton, not_and]
        intro h
        omega
      simp [c, this]
    · obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (ht (mem_univ z))
      refine le_trans ?_ (ENNReal.le_tsum (N, x))
      have hS : (N, x) ∈ S := by simp [S, hx]
      simp [c, hS, hzx]
  refine (fhLower_weightedContent_le_cost hc).trans_lt ?_
  rw [fhLowerWeightedCost, tsum_eq_sum (s := S) (fun q hq ↦ by simp [c, hq])]
  refine ENNReal.sum_lt_top.2 fun q _ ↦ ?_
  refine ENNReal.mul_lt_top ?_ ?_
  · exact (show c q ≤ b by simp only [c]; split_ifs; simp).trans_lt hb.lt_top
  · exact (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)).lt_top

/-! ### Weighted content dominates the Bowen content -/

/-- Inside a set where the order-`n` part of a weighted sum exceeds a positive threshold there is
a `(n, 2ε)`-separated subset whose `(n, 2ε)`-balls cover it. -/
private theorem fhLower_exists_separated (T : X → X) (n : ℕ) {ε : ℝ} (hε : 0 < ε) (Y : Set X) :
    ∃ E : Set X, E ⊆ Y ∧ (∀ y ∈ E, ∀ y' ∈ E, y ≠ y' → y' ∉ bowenBall T n y (2 * ε)) ∧
      Y ⊆ ⋃ y ∈ E, bowenBall T n y (2 * ε) := by
  let P : Set (Set X) :=
    {E | E ⊆ Y ∧ ∀ y ∈ E, ∀ y' ∈ E, y ≠ y' → y' ∉ bowenBall T n y (2 * ε)}
  obtain ⟨m, hm⟩ := zorn_subset P fun ch hch hc ↦ by
    refine ⟨⋃₀ ch, ⟨sUnion_subset fun E hE ↦ (hch hE).1, ?_⟩, fun E hE ↦ subset_sUnion_of_mem hE⟩
    rintro y ⟨A, hA, hy⟩ y' ⟨A', hA', hy'⟩ hne
    rcases hc.total hA hA' with h | h
    · exact (hch hA').2 y (h hy) y' hy' hne
    · exact (hch hA).2 y hy y' (h hy') hne
  refine ⟨m, hm.1.1, hm.1.2, fun z hz ↦ ?_⟩
  by_contra hzm
  have hz2 : ∀ y ∈ m, z ∉ bowenBall T n y (2 * ε) := fun y hy h ↦
    hzm (mem_iUnion₂.2 ⟨y, hy, h⟩)
  have hzn : z ∉ m := fun h ↦ hz2 z h (self_mem_bowenBall T n z _ (by positivity))
  have hins : insert z m ∈ P := by
    refine ⟨insert_subset hz hm.1.1, ?_⟩
    rintro y (rfl | hy) y' (rfl | hy') hne
    · exact absurd rfl hne
    · exact fun h ↦ hz2 y' hy' (mem_bowenBall_symm h)
    · exact hz2 y hy
    · exact hm.1.2 y hy y' hy' hne
  exact hzn (hm.2 hins (subset_insert z m) (mem_insert z m))

/-- **Weighted content dominates the Bowen content** (replaces Feng–Huang, Proposition 3.2):
if `∑_k 2^{-δ (k + N)} < 1`, then `M^{s+δ}_{N, 2ε}(Z) ≤ W^s_{N, ε}(1_Z)`. -/
theorem fhLower_lowerContent_le_weightedContent (T : X → X) (Z : Set X) {s δ ε : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hε : 0 < ε)
    (hsum : ∑' k : ℕ, (2 : ℝ≥0∞) ^ (-δ * ((k + N : ℕ) : ℝ)) < 1) :
    lowerContent T (fun _ ↦ 0) .centered Z (s + δ) (2 * ε) N ≤
      fhLowerWeightedContent T s ε N (Z.indicator 1) := by
  classical
  refine le_iInf₂ fun c hc ↦ ?_
  by_cases hS : fhLowerWeightedCost s c = ⊤
  · rw [hS]
    exact le_top
  -- thresholds, order-`n` parts of the weighted sum, and the sets where they are large
  set t : ℕ → ℝ≥0∞ := fun n ↦ (2 : ℝ≥0∞) ^ (-δ * (n : ℝ)) with ht_def
  set F : ℕ → X → ℝ≥0∞ := fun n z ↦ ∑' x, c (n, x) * (bowenBall T n x ε).indicator 1 z
    with hF_def
  set Y : ℕ → Set X := fun n ↦ {z | z ∈ Z ∧ t n < F n z} with hY_def
  have ht0 : ∀ n, t n ≠ 0 := fun n ↦ (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have htT : ∀ n, t n ≠ ⊤ := fun n ↦ ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  have hw0 : ∀ n : ℕ, (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) ≠ 0 :=
    fun n ↦ (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have hcost : fhLowerWeightedCost s c = ∑' n, (∑' x, c (n, x)) * (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) := by
    rw [fhLowerWeightedCost, fhLower_tsum_prod]
    simp only [ENNReal.tsum_mul_right]
  have hfib : ∀ n, ∑' x, c (n, x) ≠ ⊤ := by
    intro n h
    apply hS
    rw [hcost]
    refine top_le_iff.1 (le_trans ?_ (ENNReal.le_tsum n))
    rw [h, ENNReal.top_mul (hw0 n)]
  -- separated sets
  choose E hEY hEsep hEcov using fun n ↦ fhLower_exists_separated T n hε (Y n)
  have hcount : ∀ n (G : Finset X), (G : Set X) ⊆ E n →
      (G.card : ℝ≥0∞) * t n ≤ ∑' x, c (n, x) := by
    intro n G hG
    calc (G.card : ℝ≥0∞) * t n = ∑ y ∈ G, t n := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ G, F n y := Finset.sum_le_sum fun y hy ↦ (hEY n (hG hy)).2.le
      _ = ∑' x, ∑ y ∈ G, c (n, x) * (bowenBall T n x ε).indicator 1 y :=
          (Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable).symm
      _ ≤ ∑' x, c (n, x) := by
          refine ENNReal.tsum_le_tsum fun x ↦ ?_
          rw [← Finset.mul_sum]
          refine mul_le_of_le_one_right' ?_
          rw [← Finset.sum_filter_add_sum_filter_not G (· ∈ bowenBall T n x ε)]
          have h2 : ∑ y ∈ G with y ∉ bowenBall T n x ε,
              (bowenBall T n x ε).indicator (1 : X → ℝ≥0∞) y = 0 :=
            Finset.sum_eq_zero fun y hy ↦ indicator_of_notMem (Finset.mem_filter.1 hy).2 _
          have h1 : ∑ y ∈ G with y ∈ bowenBall T n x ε,
              (bowenBall T n x ε).indicator (1 : X → ℝ≥0∞) y =
              ((G.filter (· ∈ bowenBall T n x ε)).card : ℝ≥0∞) := by
            rw [Finset.card_eq_sum_ones, Nat.cast_sum]
            exact Finset.sum_congr rfl fun y hy ↦ by
              simp [indicator_of_mem (Finset.mem_filter.1 hy).2]
          rw [h1, h2, add_zero, Nat.cast_le_one, Finset.card_le_one]
          intro a ha b hb
          by_contra hab
          rw [Finset.mem_filter] at ha hb
          refine hEsep n a (hG ha.1) b (hG hb.1) hab ?_
          have := bowenBall_subset_bowenBall_add (mem_bowenBall_symm ha.2) hb.2
          rwa [← two_mul] at this
  have hfin : ∀ n, (E n).Finite := by
    intro n
    by_contra hinf
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top (hfib n) (ht0 n))
    obtain ⟨G, hG, hGc⟩ := Set.Infinite.exists_subset_card_eq hinf m
    have := hcount n G hG
    rw [hGc, ← ENNReal.le_div_iff_mul_le (Or.inl (ht0 n)) (Or.inl (htT n))] at this
    exact absurd hm (not_lt.2 this)
  -- every point of `Y n` has order at least `N`
  have hYN : ∀ n, (Y n).Nonempty → N ≤ n := by
    rintro n ⟨z, -, hz⟩
    by_contra hn
    have : F n z = 0 := ENNReal.tsum_eq_zero.2 fun x ↦ by
      rw [hc.1 (n, x) (not_le.1 hn), zero_mul]
    rw [this] at hz
    exact absurd hz (not_lt.2 zero_le)
  -- the cover
  let D : Set (ℕ × X) := {q | q.2 ∈ E q.1}
  have hD : D.Countable := by
    refine (countable_iUnion fun n ↦ ((hfin n).image (Prod.mk n)).countable).mono ?_
    intro q hq
    exact mem_iUnion.2 ⟨q.1, q.2, hq, rfl⟩
  have : Countable D := hD.to_subtype
  refine (fhLower_lowerContent_le_of_countable T Z (s + δ) (2 * ε) N (fun q : D ↦ q.1.2)
    (fun q : D ↦ q.1.1) (fun q ↦ ?_) (fun z hz ↦ ?_)).trans ?_
  · rw [max_eq_right hN]
    exact hYN _ ⟨_, hEY _ q.2⟩
  · -- some order-`n` part is large at `z`
    obtain ⟨n, hn⟩ : ∃ n, t n < F n z := by
      by_contra hno
      push Not at hno
      have h1 : (1 : ℝ≥0∞) ≤ ∑' n, F n z := by
        have := hc.2 z
        rw [indicator_of_mem hz, fhLower_tsum_prod] at this
        exact this
      have hzero : ∀ n, n ∉ range (fun k : ℕ ↦ k + N) → F n z = 0 := by
        intro n hn
        have hnN : n < N := by
          by_contra h
          exact hn ⟨n - N, by simp only; omega⟩
        exact ENNReal.tsum_eq_zero.2 fun x ↦ by rw [hc.1 (n, x) hnN, zero_mul]
      have h2 : ∑' n, F n z = ∑' k, F (k + N) z :=
        ((add_left_injective N).tsum_eq (f := fun n ↦ F n z) fun n hn ↦
          by_contra fun h ↦ hn (hzero n h)).symm
      have h3 : ∑' k, F (k + N) z ≤ ∑' k : ℕ, (2 : ℝ≥0∞) ^ (-δ * ((k + N : ℕ) : ℝ)) :=
        ENNReal.tsum_le_tsum fun k ↦ hno (k + N)
      exact absurd (h1.trans (h2.trans_le h3)) (not_le.2 hsum)
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (hEcov n ⟨hz, hn⟩)
    exact mem_iUnion.2 ⟨⟨(n, y), hy⟩, hzy⟩
  · -- the cost
    rw [hcost, tsum_subtype D (fun q ↦ (2 : ℝ≥0∞) ^ (-(s + δ) * (q.1 : ℝ))), fhLower_tsum_prod]
    refine ENNReal.tsum_le_tsum fun n ↦ ?_
    have hsplit : (2 : ℝ≥0∞) ^ (-(s + δ) * (n : ℝ)) = (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) * t n := by
      rw [ht_def, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      ring_nf
    have hind : ∀ x, D.indicator (fun q ↦ (2 : ℝ≥0∞) ^ (-(s + δ) * (q.1 : ℝ))) (n, x) =
        (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) * (E n).indicator (fun _ ↦ t n) x := by
      intro x
      by_cases hx : x ∈ E n
      · rw [indicator_of_mem (show (n, x) ∈ D from hx), indicator_of_mem hx, hsplit]
      · rw [indicator_of_notMem (show (n, x) ∉ D from hx), indicator_of_notMem hx, mul_zero]
    simp only [hind, ENNReal.tsum_mul_left]
    rw [mul_comm]
    refine mul_le_mul_left ?_ _
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun G ↦ ?_
    rw [← Finset.sum_filter_add_sum_filter_not G (· ∈ E n)]
    have h2 : ∑ y ∈ G with y ∉ E n, (E n).indicator (fun _ ↦ t n) y = 0 :=
      Finset.sum_eq_zero fun y hy ↦ indicator_of_notMem (Finset.mem_filter.1 hy).2 _
    have h1 : ∑ y ∈ G with y ∈ E n, (E n).indicator (fun _ ↦ t n) y =
        ((G.filter (· ∈ E n)).card : ℝ≥0∞) * t n := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl fun y hy ↦ indicator_of_mem (Finset.mem_filter.1 hy).2 _
    rw [h1, h2, add_zero]
    exact hcount n _ fun y hy ↦ (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2

end Kolmogorov.PointToSet
