/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.InformationRate
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# The Feng–Huang variational principle, Upper half

D.-J. Feng and W. Huang, *Variational principles for topological entropies of subsets*,
J. Funct. Anal. 263 (2012) (arXiv:1012.1103): for a continuous map `T` of a compact metric space
and a nonempty compact `K`, the upper half `upperEntropy P T K ≤ sup_{μ(K)=1} h̄_μ(T)`.

Here `upperEntropy` is defined as the modified upper capacity entropy
(`entropy_eq_zeroPotentialPressure_of_nonempty_upper`); it equals Feng–Huang's packing entropy
by `pressureEquivalence_upper` (see `VariationalPacking.lean`), but the proof works with
capacity. Fix `0 ≤ t` below the entropy, a dyadic radius `r = 4ε` with
`t < modifiedUpperPressure K r`, all at zero potential.

* **Separated sets** (`fhUpper_exists_separated`). If the upper capacity of `Y` exceeds `t`, then
  at arbitrarily large orders `n` there are finite `(n, r)`-separated subsets of `Y` with more
  than `2^{n t}` points. No compactness is needed: a separated set of maximal cardinality covers
  `Y` by Bowen balls.
* **Thin sets and the kernel** (`FhUpperThin`, `fhUpper_kernel`). A set is thin if it is covered
  by countably many sets of upper capacity `≤ t`. Removing from `K` the open sets meeting it in a
  thin set (countably many suffice, by second countability) leaves a nonempty `K'` none of whose
  nonempty relatively open pieces is thin (`fhUpper_exists_kernel`).
* **The Cantor tree** (`fhUpper_tree`). Nodes are lists of points; the root is a point of `K'` of
  order `0`. The children of a node `x` of order `m` at level `q` form a finite
  `(n, 4ε)`-separated set of more than `2^{n t}` points of `K'` in `B_m(x, ε 2^{-q}/4)`, `n > m`,
  and the mass of `x` is split equally among them, so a node of order `n` has mass `≤ 2^{-n t}`.
  Distinct nodes of level `q` are `(2 + 2^{-q}) ε`-apart at the smaller order, the closed cells
  `B̄_m(x, ε 2^{-q}/2)` are nested, and a cell meets no `3ε/2`-ball about another node of its
  level. Hence the discrete measures `ν_k` of the levels `k ≥ q` give mass at most `2^{-n t}` to
  the `3ε/2`-ball about a node of level `q` and order `n`, and live on the union of the cells.
* **The limit** (`fhUpper_limit`). A cluster point `μ` of the `ν_k` in the compact space of
  probability measures (Prokhorov, portmanteau) has `μ(K) = 1`, and almost every point lies, for
  every `q`, in a cell of level `q`; so `μ(B_n(z, ε)) ≤ 2^{-n t}` for infinitely many `n` and the
  upper local entropy at scale `ε` is at least `t` almost everywhere.

Compared with Feng–Huang Part 2 (and the coordinator's plan) the masses are split equally, so no
second exponent `s < t` and no mass calibration are needed: the upper local entropy only needs
the bound along the orders of the tree. Blueprint node `meas:variational`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

section Capacity

variable {X : Type*} [MetricSpace X]

/-! ### Separated sets of large cardinality -/

/-- Two points of a finite set at Bowen order `n` are `r`-separated: neither lies in the open
Bowen ball of radius `r` about the other. -/
def FhUpperSeparated (T : X → X) (n : ℕ) (r : ℝ) (E : Finset X) : Prop :=
  ∀ y ∈ E, ∀ y' ∈ E, y ≠ y' → y' ∉ bowenBall T n y r

/-- The zero-potential partition sum is at most the cardinality of a finite set of centers whose
Bowen balls cover the set. -/
theorem fhUpper_partitionSum_le_card (T : X → X) {Y : Set X} (n : ℕ) (r : ℝ) (E : Finset X)
    (hE : Y ⊆ ⋃ y ∈ (E : Set X), bowenBall T n y r) :
    partitionSum T (fun _ => 0) .centered Y n r ≤ E.card := by
  refine (iInf₂_le (E : Set X) ⟨E.countable_toSet, hE⟩).trans_eq ?_
  simp [partitionCoverCost, pressureBallWeight, birkhoffSum]

/-- If the upper capacity of `Y` at radius `r > 0` exceeds `t`, then for every `N` there are an
order `n ≥ N` and a finite `(n, r)`-separated subset of `Y` with more than `2^{n t}` points.
No compactness is needed: otherwise a separated subset of maximal cardinality covers `Y` by
Bowen balls and bounds the partition sums. -/
theorem fhUpper_exists_separated (T : X → X) {Y : Set X} {r t : ℝ} (hr : 0 < r)
    (h : (t : EReal) < upperCapacity T (fun _ => 0) .centered Y r) (N : ℕ) :
    ∃ n ≥ N, ∃ E : Finset X, ↑E ⊆ Y ∧ FhUpperSeparated T n r E ∧
      (2 : ℝ) ^ ((n : ℝ) * t) < E.card := by
  classical
  have hfreq := frequently_lt_of_lt_limsup (by isBoundedDefault) h
  obtain ⟨n, hn, hlt⟩ := frequently_atTop.1 hfreq (max N 1)
  refine ⟨n, le_of_max_le_left hn, ?_⟩
  by_contra hcon
  push Not at hcon
  let S : Set ℕ := {k | ∃ E : Finset X, ↑E ⊆ Y ∧ FhUpperSeparated T n r E ∧ E.card = k}
  have hbdd : BddAbove S := by
    refine ⟨⌊(2 : ℝ) ^ ((n : ℝ) * t)⌋₊, ?_⟩
    rintro k ⟨E, hEY, hEs, rfl⟩
    exact Nat.le_floor (hcon E hEY hEs)
  have hS0 : (0 : ℕ) ∈ S := ⟨∅, by simp, by simp [FhUpperSeparated], rfl⟩
  obtain ⟨E, hEY, hEs, hEc⟩ := Nat.sSup_mem ⟨0, hS0⟩ hbdd
  have hcov : Y ⊆ ⋃ y ∈ (E : Set X), bowenBall T n y r := by
    intro z hz
    by_contra hzE
    simp only [mem_iUnion, Finset.mem_coe, not_exists] at hzE
    have hzn : z ∉ E := fun hzE' ↦ hzE z hzE' (self_mem_bowenBall T n z r hr)
    have hins : E.card + 1 ∈ S := by
      refine ⟨insert z E, ?_, ?_, ?_⟩
      · rw [Finset.coe_insert]
        exact insert_subset hz hEY
      · intro y hy y' hy' hne
        rw [Finset.mem_insert] at hy hy'
        rcases hy with rfl | hy <;> rcases hy' with rfl | hy'
        · exact absurd rfl hne
        · exact fun hmem ↦ hzE y' hy' (mem_bowenBall_symm hmem)
        · exact hzE y hy
        · exact hEs y hy y' hy' hne
      · rw [Finset.card_insert_of_notMem hzn]
    have := le_csSup hbdd hins
    omega
  have hcard := hcon E hEY hEs
  have hle : partitionSum T (fun _ => 0) .centered Y n r ≤ (2 : ℝ≥0∞) ^ ((n : ℝ) * t) := by
    refine (fhUpper_partitionSum_le_card T n r E hcov).trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2,
      ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact ENNReal.ofReal_le_ofReal hcard
  have hrate := pressureRate_le_of_le_rpow
    (q := fun n ↦ partitionSum T (fun _ => 0) .centered Y n r) (le_of_max_le_right hn) hle
  have hn0 : (n : ℝ) ≠ 0 := by
    have := le_of_max_le_right hn
    positivity
  rw [mul_div_cancel_left₀ t hn0] at hrate
  exact absurd hlt (not_lt.2 hrate)

/-! ### Thin sets and the kernel -/

/-- A set is thin (at radius `r`, threshold `t`) if it is covered by countably many sets of
zero-potential upper capacity at most `t`. -/
def FhUpperThin (T : X → X) (r t : ℝ) (Y : Set X) : Prop :=
  ∃ 𝒴 : Set (Set X), 𝒴.Countable ∧ Y ⊆ ⋃₀ 𝒴 ∧
    ∀ Z ∈ 𝒴, upperCapacity T (fun _ => 0) .centered Z r ≤ t

/-- Subsets of thin sets are thin. -/
theorem FhUpperThin.mono {T : X → X} {r t : ℝ} {Y Y' : Set X} (h : FhUpperThin T r t Y')
    (hY : Y ⊆ Y') : FhUpperThin T r t Y := by
  obtain ⟨𝒴, hc, hcov, hcap⟩ := h
  exact ⟨𝒴, hc, hY.trans hcov, hcap⟩

/-- The empty set is thin. -/
theorem fhUpperThin_empty (T : X → X) (r t : ℝ) : FhUpperThin T r t ∅ :=
  ⟨∅, countable_empty, empty_subset _, fun _ h ↦ absurd h (notMem_empty _)⟩

/-- The union of two thin sets is thin. -/
theorem FhUpperThin.union {T : X → X} {r t : ℝ} {Y Y' : Set X} (h : FhUpperThin T r t Y)
    (h' : FhUpperThin T r t Y') : FhUpperThin T r t (Y ∪ Y') := by
  obtain ⟨𝒴, hc, hcov, hcap⟩ := h
  obtain ⟨𝒴', hc', hcov', hcap'⟩ := h'
  refine ⟨𝒴 ∪ 𝒴', hc.union hc', ?_, fun Z hZ ↦ hZ.elim (hcap Z) (hcap' Z)⟩
  rw [sUnion_union]
  exact union_subset_union hcov hcov'

/-- A countable union of thin sets is thin. -/
theorem fhUpperThin_sUnion {T : X → X} {r t : ℝ} {𝒮 : Set (Set X)} (h𝒮 : 𝒮.Countable)
    (h : ∀ Y ∈ 𝒮, FhUpperThin T r t Y) : FhUpperThin T r t (⋃₀ 𝒮) := by
  choose! f hfc hfcov hfcap using h
  refine ⟨⋃ Y ∈ 𝒮, f Y, h𝒮.biUnion hfc, ?_, ?_⟩
  · intro z hz
    obtain ⟨Y, hY, hzY⟩ := mem_sUnion.1 hz
    obtain ⟨Z, hZ, hzZ⟩ := mem_sUnion.1 (hfcov Y hY hzY)
    exact mem_sUnion.2 ⟨Z, mem_biUnion hY hZ, hzZ⟩
  · intro Z hZ
    obtain ⟨Y, hY, hZY⟩ := mem_iUnion₂.1 hZ
    exact hfcap Y hY Z hZY

/-- The zero-potential upper capacity of the empty set is `⊥`. -/
theorem fhUpper_upperCapacity_empty (T : X → X) (r : ℝ) :
    upperCapacity T (fun _ => 0) .centered (∅ : Set X) r = ⊥ := by
  have h0 : (fun n ↦ partitionSum T (fun _ => 0) .centered (∅ : Set X) n r) = fun _ ↦ 0 := by
    funext n
    exact le_antisymm ((fhUpper_partitionSum_le_card T n r ∅ (empty_subset _)).trans_eq
      (by simp)) bot_le
  have h1 : pressureRate (fun _ ↦ (0 : ℝ≥0∞)) = fun _ ↦ ⊥ := funext pressureRate_zero
  unfold upperCapacity
  rw [h0, h1, limsup_const]

/-- A set whose modified upper capacity exceeds `t` is not thin. -/
theorem fhUpper_not_thin_of_lt {T : X → X} {r t : ℝ} {Y : Set X}
    (h : (t : EReal) < modifiedUpperPressure T (fun _ => 0) .centered Y r) :
    ¬ FhUpperThin T r t Y := by
  rintro ⟨𝒴, hc, hcov, hcap⟩
  refine absurd h (not_lt.2 ?_)
  rcases 𝒴.eq_empty_or_nonempty with rfl | hne
  · refine (iInf₂_le (fun _ ↦ (∅ : Set X)) ?_).trans ?_
    · simpa using hcov
    · simp [fhUpper_upperCapacity_empty]
  · obtain ⟨g, rfl⟩ := hc.exists_eq_range hne
    refine (iInf₂_le g ?_).trans (iSup_le fun k ↦ hcap _ (mem_range_self k))
    simpa [sUnion_range] using hcov

/-- A set that is not thin has upper capacity larger than `t`. -/
theorem fhUpper_lt_upperCapacity_of_not_thin {T : X → X} {r t : ℝ} {Y : Set X}
    (h : ¬ FhUpperThin T r t Y) : (t : EReal) < upperCapacity T (fun _ => 0) .centered Y r := by
  by_contra hle
  exact h ⟨{Y}, countable_singleton Y, by simp, fun Z hZ ↦ by
    rw [mem_singleton_iff.1 hZ]; exact not_lt.1 hle⟩

/-- **The localized kernel.** In a second-countable space, a set `K` that is not thin contains a
nonempty kernel `K'` all of whose nonempty relatively open pieces `K' ∩ G` are not thin. The
kernel is `K` minus the union of the open sets meeting `K` in a thin set. -/
theorem fhUpper_kernel [SecondCountableTopology X] {T : X → X} {r t : ℝ} {K : Set X}
    (hK : ¬ FhUpperThin T r t K) :
    ∃ K' ⊆ K, K'.Nonempty ∧
      ∀ G : Set X, IsOpen G → (G ∩ K').Nonempty → ¬ FhUpperThin T r t (K' ∩ G) := by
  let 𝒢 : Set (Set X) := {G | IsOpen G ∧ FhUpperThin T r t (K ∩ G)}
  obtain ⟨𝒯, h𝒯c, h𝒯, h𝒯eq⟩ := TopologicalSpace.isOpen_sUnion_countable 𝒢 fun G hG ↦ hG.1
  have hH : FhUpperThin T r t (K ∩ ⋃₀ 𝒢) := by
    refine (fhUpperThin_sUnion (h𝒯c.image (K ∩ ·)) ?_).mono ?_
    · rintro _ ⟨G, hG, rfl⟩
      exact (h𝒯 hG).2
    · rintro z ⟨hzK, hz⟩
      rw [← h𝒯eq] at hz
      obtain ⟨G, hG, hzG⟩ := mem_sUnion.1 hz
      exact mem_sUnion.2 ⟨K ∩ G, mem_image_of_mem _ hG, hzK, hzG⟩
  have hsplit : ∀ G : Set X, K ∩ G ⊆ ((K \ ⋃₀ 𝒢) ∩ G) ∪ (K ∩ ⋃₀ 𝒢) := by
    rintro G z ⟨hzK, hzG⟩
    by_cases hz : z ∈ ⋃₀ 𝒢
    · exact Or.inr ⟨hzK, hz⟩
    · exact Or.inl ⟨⟨hzK, hz⟩, hzG⟩
  have hnot : ¬ FhUpperThin T r t (K \ ⋃₀ 𝒢) := fun hthin ↦
    hK ((hthin.union hH).mono (by simp))
  refine ⟨K \ ⋃₀ 𝒢, sdiff_subset, ?_, ?_⟩
  · rw [nonempty_iff_ne_empty]
    rintro he
    exact hnot (he ▸ fhUpperThin_empty T r t)
  · rintro G hG ⟨z, hzG, hzK, hzH⟩ hthin
    exact hzH (mem_sUnion.2 ⟨G, ⟨hG, (hthin.union hH).mono (hsplit G)⟩, hzG⟩)

/-- **Step of the tree.** If the modified upper capacity of `K` at radius `r > 0` exceeds `t`,
there is a nonempty `K' ⊆ K` such that every Bowen ball about a point of `K'` contains, at
arbitrarily large orders `n`, finite `(n, r)`-separated subsets of `K'` with more than `2^{n t}`
points. -/
theorem fhUpper_exists_kernel [SecondCountableTopology X] {T : X → X} (hT : Continuous T)
    {K : Set X} {r t : ℝ} (hr : 0 < r)
    (ht : (t : EReal) < modifiedUpperPressure T (fun _ => 0) .centered K r) :
    ∃ K' ⊆ K, K'.Nonempty ∧ ∀ x ∈ K', ∀ m : ℕ, ∀ ρ > 0, ∀ N : ℕ, ∃ n ≥ N, ∃ E : Finset X,
      ↑E ⊆ K' ∩ bowenBall T m x ρ ∧ FhUpperSeparated T n r E ∧
        (2 : ℝ) ^ ((n : ℝ) * t) < E.card := by
  obtain ⟨K', hK'K, hne, hK'⟩ := fhUpper_kernel (fhUpper_not_thin_of_lt ht)
  refine ⟨K', hK'K, hne, fun x hx m ρ hρ N ↦ ?_⟩
  have hG := hK' _ (bowen_ball_dense_open T hT m x ρ)
    ⟨x, self_mem_bowenBall T m x ρ hρ, hx⟩
  exact fhUpper_exists_separated T hr (fhUpper_lt_upperCapacity_of_not_thin hG) N

end Capacity

section Tree

variable {X : Type*}

/-- `ε 2^{-(q+1)} = ε 2^{-q} / 2`. -/
theorem fhUpper_pow_succ (ε : ℝ) (q : ℕ) : ε * (2 : ℝ)⁻¹ ^ (q + 1) = ε * 2⁻¹ ^ q / 2 := by
  rw [pow_succ]
  ring

/-- Closed Bowen balls are monotone in the radius. -/
theorem fhUpper_closedBowenBall_mono [MetricSpace X] {T : X → X} {n : ℕ} {x : X} {ρ ρ' : ℝ}
    (h : ρ ≤ ρ') : closedBowenBall T n x ρ ⊆ closedBowenBall T n x ρ' :=
  fun _ hz k hk ↦ (hz k hk).trans h

/-- The center belongs to its closed Bowen ball of nonnegative radius. -/
theorem fhUpper_self_mem_closedBowenBall [MetricSpace X] {T : X → X} {n : ℕ} {x : X} {ρ : ℝ}
    (h : 0 ≤ ρ) : x ∈ closedBowenBall T n x ρ :=
  fun k _ ↦ by rw [dist_self]; exact h

/-- A cell lies in the open Bowen ball of radius `3ε/2` about its node. -/
theorem fhUpper_cell_subset [MetricSpace X] {T : X → X} {ε : ℝ} (hε : 0 < ε) (q n : ℕ) (x : X) :
    closedBowenBall T n x (ε * 2⁻¹ ^ q / 2) ⊆ bowenBall T n x (3 * ε / 2) := by
  refine closedBowenBall_subset_bowenBall T n x ?_
  have : (2 : ℝ)⁻¹ ^ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

/-! ### The Cantor tree -/

section Nodes

variable (x₀ : X) (ch : X → ℕ → ℕ → ℕ × Finset X)

/-- The point of a node of the tree; nodes are lists of points, the head being the newest. The
root `[]` sits at `x₀`. -/
def fhUpperPt : List X → X
  | [] => x₀
  | y :: _ => y

/-- The order of a node: `0` at the root, and the order chosen by `ch` for the children of the
parent otherwise. -/
def fhUpperOrd : List X → ℕ
  | [] => 0
  | _ :: l => (ch (fhUpperPt x₀ l) (fhUpperOrd l) l.length).1

/-- The children points of a node, chosen by `ch` from its point, order and level. -/
def fhUpperChildren (l : List X) : Finset X :=
  (ch (fhUpperPt x₀ l) (fhUpperOrd x₀ ch l) l.length).2

/-- The mass of a node: the mass of the parent split equally among its children. -/
noncomputable def fhUpperMass : List X → ℝ≥0∞
  | [] => 1
  | _ :: l => fhUpperMass l / (fhUpperChildren x₀ ch l).card

variable [DecidableEq X]

/-- The nodes of level `q`: lists of length `q` obtained by successively choosing children. -/
def fhUpperLevel : ℕ → Finset (List X)
  | 0 => {[]}
  | q + 1 => (fhUpperLevel q).biUnion fun l ↦ (fhUpperChildren x₀ ch l).image (· :: l)

/-- The discrete measure of level `k`: each node carries its mass at its point. -/
noncomputable def fhUpperMeasure [MeasurableSpace X] (k : ℕ) : Measure X :=
  ∑ l ∈ fhUpperLevel x₀ ch k, fhUpperMass x₀ ch l • Measure.dirac (fhUpperPt x₀ l)

/-- The choice function `ch` is good: from a point `x ∈ K'` of order `m` at level `q`, it
chooses a larger order `n` and a finite `(n, 4ε)`-separated set of more than `2^{n t}` points of
`K'` in the Bowen ball `B_m(x, ε 2^{-q}/4)`. -/
def FhUpperGoodChoice [MetricSpace X] (T : X → X) (K' : Set X) (ε t : ℝ) : Prop :=
  ∀ x m q, x ∈ K' → m < (ch x m q).1 ∧ ↑(ch x m q).2 ⊆ K' ∩ bowenBall T m x (ε * 2⁻¹ ^ q / 4) ∧
    FhUpperSeparated T (ch x m q).1 (4 * ε) (ch x m q).2 ∧
      (2 : ℝ) ^ (((ch x m q).1 : ℝ) * t) < (ch x m q).2.card

variable {x₀ ch}

/-- Membership in level zero. -/
theorem fhUpper_mem_level_zero {l : List X} : l ∈ fhUpperLevel x₀ ch 0 ↔ l = [] :=
  Finset.mem_singleton

/-- Membership in a successor level. -/
theorem fhUpper_mem_level_succ {q : ℕ} {u : List X} :
    u ∈ fhUpperLevel x₀ ch (q + 1) ↔
      ∃ l ∈ fhUpperLevel x₀ ch q, ∃ y ∈ fhUpperChildren x₀ ch l, u = y :: l := by
  simp only [fhUpperLevel, Finset.mem_biUnion, Finset.mem_image]
  exact exists_congr fun l ↦ and_congr_right fun _ ↦ exists_congr fun y ↦
    and_congr_right fun _ ↦ eq_comm

/-- Nodes of level `q` have length `q`. -/
theorem fhUpper_length {q : ℕ} {l : List X} (hl : l ∈ fhUpperLevel x₀ ch q) : l.length = q := by
  induction q generalizing l with
  | zero => rw [fhUpper_mem_level_zero.1 hl]; rfl
  | succ q ih =>
    obtain ⟨a, ha, y, -, rfl⟩ := fhUpper_mem_level_succ.1 hl
    simp [ih ha]

variable [MetricSpace X] {T : X → X} {K' : Set X} {ε t : ℝ}

section Good

omit [MetricSpace X] in
/-- The measure of level `k` of a set `S` is the total mass of the nodes with point in `S`. -/
theorem fhUpper_measure_apply [MeasurableSpace X] [MeasurableSingletonClass X] (k : ℕ)
    (S : Set X) : fhUpperMeasure x₀ ch k S =
      ∑ l ∈ fhUpperLevel x₀ ch k, fhUpperMass x₀ ch l * S.indicator 1 (fhUpperPt x₀ l) := by
  simp [fhUpperMeasure, Measure.finsetSum_apply, Measure.dirac_apply]

variable (hx₀ : x₀ ∈ K') (hch : FhUpperGoodChoice ch T K' ε t)
include hx₀ hch

/-- The points of the tree lie in `K'`. -/
theorem fhUpper_pt_mem {q : ℕ} {l : List X} (hl : l ∈ fhUpperLevel x₀ ch q) :
    fhUpperPt x₀ l ∈ K' := by
  induction q generalizing l with
  | zero => rw [fhUpper_mem_level_zero.1 hl]; exact hx₀
  | succ q ih =>
    obtain ⟨a, ha, y, hy, rfl⟩ := fhUpper_mem_level_succ.1 hl
    exact ((hch _ _ _ (ih ha)).2.1 hy).1

/-- The properties of the children of a node of level `q`. -/
theorem fhUpper_child {q : ℕ} {l : List X} (hl : l ∈ fhUpperLevel x₀ ch q) :
    fhUpperOrd x₀ ch l < (ch (fhUpperPt x₀ l) (fhUpperOrd x₀ ch l) l.length).1 ∧
      (∀ y ∈ fhUpperChildren x₀ ch l,
        fhUpperOrd x₀ ch (y :: l) = (ch (fhUpperPt x₀ l) (fhUpperOrd x₀ ch l) l.length).1 ∧
        y ∈ bowenBall T (fhUpperOrd x₀ ch l) (fhUpperPt x₀ l) (ε * 2⁻¹ ^ q / 4)) ∧
      FhUpperSeparated T (ch (fhUpperPt x₀ l) (fhUpperOrd x₀ ch l) l.length).1 (4 * ε)
        (fhUpperChildren x₀ ch l) ∧
      (2 : ℝ) ^ (((ch (fhUpperPt x₀ l) (fhUpperOrd x₀ ch l) l.length).1 : ℝ) * t) <
        (fhUpperChildren x₀ ch l).card := by
  obtain rfl := fhUpper_length hl
  obtain ⟨h1, h2, h3, h4⟩ :=
    hch (fhUpperPt x₀ l) (fhUpperOrd x₀ ch l) l.length (fhUpper_pt_mem hx₀ hch hl)
  exact ⟨h1, fun y hy ↦ ⟨rfl, (h2 hy).2⟩, h3, h4⟩

/-- Orders at level `q` are at least `q`. -/
theorem fhUpper_le_ord {q : ℕ} {l : List X} (hl : l ∈ fhUpperLevel x₀ ch q) :
    q ≤ fhUpperOrd x₀ ch l := by
  induction q generalizing l with
  | zero => exact Nat.zero_le _
  | succ q ih =>
    obtain ⟨a, ha, y, hy, rfl⟩ := fhUpper_mem_level_succ.1 hl
    have h := fhUpper_child hx₀ hch ha
    rw [(h.2.1 y hy).1]
    exact (ih ha).trans_lt h.1

/-- The children sets are nonempty: their cardinality is positive. -/
theorem fhUpper_card_pos {q : ℕ} {l : List X} (hl : l ∈ fhUpperLevel x₀ ch q) :
    0 < (fhUpperChildren x₀ ch l).card := by
  have h := (fhUpper_child hx₀ hch hl).2.2.2
  exact_mod_cast (Real.rpow_pos_of_pos two_pos _).trans h

/-- Masses are at most `1` and at most `2^{-m t}` at a node of order `m`. -/
theorem fhUpper_mass_le {q : ℕ} {l : List X} (hl : l ∈ fhUpperLevel x₀ ch q) :
    fhUpperMass x₀ ch l ≤ 1 ∧
      fhUpperMass x₀ ch l ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((fhUpperOrd x₀ ch l : ℝ) * t))) := by
  induction q generalizing l with
  | zero =>
    rw [fhUpper_mem_level_zero.1 hl]
    simp [fhUpperMass, fhUpperOrd]
  | succ q ih =>
    obtain ⟨a, ha, y, hy, rfl⟩ := fhUpper_mem_level_succ.1 hl
    have h := fhUpper_child hx₀ hch ha
    have hc := fhUpper_card_pos hx₀ hch ha
    set c := (fhUpperChildren x₀ ch a).card
    have hmass : fhUpperMass x₀ ch (y :: a) ≤ (c : ℝ≥0∞)⁻¹ := by
      change fhUpperMass x₀ ch a / c ≤ _
      rw [div_eq_mul_inv]
      exact (mul_le_mul_left (ih ha).1 _).trans_eq (one_mul _)
    refine ⟨hmass.trans (ENNReal.inv_le_one.2 (by exact_mod_cast hc)), hmass.trans ?_⟩
    rw [(h.2.1 y hy).1, Real.rpow_neg zero_le_two]
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hcR]
    exact ENNReal.ofReal_le_ofReal (inv_anti₀ (Real.rpow_pos_of_pos two_pos _) h.2.2.2.le)

/-- **Nesting.** The cell of a child, of radius `ε 2^{-q-1}/2`, lies in the cell of its parent,
of radius `ε 2^{-q}/2`. -/
theorem fhUpper_nest {q : ℕ} {l : List X} (hl : l ∈ fhUpperLevel x₀ ch q) {y : X}
    (hy : y ∈ fhUpperChildren x₀ ch l) :
    closedBowenBall T (fhUpperOrd x₀ ch (y :: l)) y (ε * 2⁻¹ ^ (q + 1) / 2) ⊆
      closedBowenBall T (fhUpperOrd x₀ ch l) (fhUpperPt x₀ l) (ε * 2⁻¹ ^ q / 2) := by
  have h := fhUpper_child hx₀ hch hl
  intro z hz k hk
  have d1 := mem_bowenBall_iff.1 (h.2.1 y hy).2 k hk
  have d2 := hz k (by rw [(h.2.1 y hy).1]; exact hk.trans h.1)
  have := dist_triangle (T^[k] (fhUpperPt x₀ l)) (T^[k] y) (T^[k] z)
  rw [fhUpper_pow_succ] at d2
  linarith

/-- **Descendants.** For `q ≤ k`, the cell of a node of level `k` lies in the cell of some node
of level `q` (its ancestor). -/
theorem fhUpper_descend {q k : ℕ} (hqk : q ≤ k) {u : List X} (hu : u ∈ fhUpperLevel x₀ ch k) :
    ∃ l ∈ fhUpperLevel x₀ ch q,
      closedBowenBall T (fhUpperOrd x₀ ch u) (fhUpperPt x₀ u) (ε * 2⁻¹ ^ k / 2) ⊆
        closedBowenBall T (fhUpperOrd x₀ ch l) (fhUpperPt x₀ l) (ε * 2⁻¹ ^ q / 2) := by
  induction k, hqk using Nat.le_induction generalizing u with
  | base => exact ⟨u, hu, subset_rfl⟩
  | succ k hqk ih =>
    obtain ⟨a, ha, y, hy, rfl⟩ := fhUpper_mem_level_succ.1 hu
    obtain ⟨l, hl, hsub⟩ := ih ha
    exact ⟨l, hl, (fhUpper_nest hx₀ hch ha hy).trans hsub⟩

section Eps

variable (hε : 0 < ε)
include hε

/-- **Separation.** Distinct nodes `l ≠ l'` of level `q` are `(2 + 2^{-q}) ε`-apart at the
smaller of their two orders. -/
theorem fhUpper_sep {q : ℕ} {l l' : List X} (hl : l ∈ fhUpperLevel x₀ ch q)
    (hl' : l' ∈ fhUpperLevel x₀ ch q) (hne : l ≠ l') :
    fhUpperPt x₀ l' ∉ bowenBall T (min (fhUpperOrd x₀ ch l) (fhUpperOrd x₀ ch l'))
      (fhUpperPt x₀ l) (2 * ε + ε * 2⁻¹ ^ q) := by
  induction q generalizing l l' with
  | zero =>
    exact absurd ((fhUpper_mem_level_zero.1 hl).trans (fhUpper_mem_level_zero.1 hl').symm) hne
  | succ q ih =>
    obtain ⟨a, ha, y, hy, rfl⟩ := fhUpper_mem_level_succ.1 hl
    obtain ⟨a', ha', y', hy', rfl⟩ := fhUpper_mem_level_succ.1 hl'
    have h := fhUpper_child hx₀ hch ha
    have h' := fhUpper_child hx₀ hch ha'
    change y' ∉ bowenBall T (min (fhUpperOrd x₀ ch (y :: a)) (fhUpperOrd x₀ ch (y' :: a'))) y _
    rw [(h.2.1 y hy).1, (h'.2.1 y' hy').1]
    by_cases haa : a = a'
    · subst haa
      have hyy : y ≠ y' := fun e ↦ hne (by rw [e])
      rw [min_self]
      refine fun hmem ↦ h.2.2.1 y hy y' hy' hyy (bowenBall_subset_of_le T _ y ?_ hmem)
      have : (2 : ℝ)⁻¹ ^ (q + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    · intro hmem
      apply ih ha ha' haa
      rw [mem_bowenBall_iff] at hmem ⊢
      intro k hk
      have hk1 : k < fhUpperOrd x₀ ch a := lt_of_lt_of_le hk (min_le_left _ _)
      have hk2 : k < fhUpperOrd x₀ ch a' := lt_of_lt_of_le hk (min_le_right _ _)
      have d1 := mem_bowenBall_iff.1 (h.2.1 y hy).2 k hk1
      have d2 := mem_bowenBall_iff.1 (h'.2.1 y' hy').2 k hk2
      have d3 := hmem k (lt_min (hk1.trans h.1) (hk2.trans h'.1))
      have := dist_triangle4 (T^[k] (fhUpperPt x₀ a)) (T^[k] y) (T^[k] y')
        (T^[k] (fhUpperPt x₀ a'))
      rw [dist_comm (T^[k] y') _] at this
      rw [fhUpper_pow_succ] at d3
      linarith

/-- **Disjointness.** The cell of a node `l'` of level `q` does not meet the open Bowen ball of
radius `3ε/2` about another node `l` of the same level. -/
theorem fhUpper_disjoint {q : ℕ} {l l' : List X} (hl : l ∈ fhUpperLevel x₀ ch q)
    (hl' : l' ∈ fhUpperLevel x₀ ch q) (hne : l ≠ l') {z : X}
    (hz : z ∈ closedBowenBall T (fhUpperOrd x₀ ch l') (fhUpperPt x₀ l') (ε * 2⁻¹ ^ q / 2)) :
    z ∉ bowenBall T (fhUpperOrd x₀ ch l) (fhUpperPt x₀ l) (3 * ε / 2) := by
  intro hmem
  apply fhUpper_sep hx₀ hch hε hl hl' hne
  rw [mem_bowenBall_iff] at hmem ⊢
  intro k hk
  have d1 := hmem k (lt_of_lt_of_le hk (min_le_left _ _))
  have d2 := hz k (lt_of_lt_of_le hk (min_le_right _ _))
  have := dist_triangle (T^[k] (fhUpperPt x₀ l)) (T^[k] z) (T^[k] (fhUpperPt x₀ l'))
  rw [dist_comm (T^[k] z)] at this
  have : 0 ≤ ε * (2 : ℝ)⁻¹ ^ q := by positivity
  linarith

end Eps

section Measure

variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- If no node of level `k` is separated from its children by `S`, the measures of levels `k`
and `k + 1` agree on `S`: the mass of a node is split equally among its children. -/
theorem fhUpper_measure_succ {k : ℕ} {S : Set X}
    (hS : ∀ u ∈ fhUpperLevel x₀ ch k, ∀ y ∈ fhUpperChildren x₀ ch u,
      (y ∈ S ↔ fhUpperPt x₀ u ∈ S)) :
    fhUpperMeasure x₀ ch (k + 1) S = fhUpperMeasure x₀ ch k S := by
  rw [fhUpper_measure_apply, fhUpper_measure_apply, fhUpperLevel, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun u hu ↦ ?_
    rw [Finset.sum_image fun y _ y' _ e ↦ (List.cons.inj e).1]
    have hc := fhUpper_card_pos hx₀ hch hu
    have hcard : ((fhUpperChildren x₀ ch u).card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
    calc ∑ y ∈ fhUpperChildren x₀ ch u,
          fhUpperMass x₀ ch (y :: u) * S.indicator 1 (fhUpperPt x₀ (y :: u))
        = ∑ y ∈ fhUpperChildren x₀ ch u, fhUpperMass x₀ ch u /
            (fhUpperChildren x₀ ch u).card * S.indicator 1 (fhUpperPt x₀ u) := by
          refine Finset.sum_congr rfl fun y hy ↦ ?_
          have hiff := hS u hu y hy
          change fhUpperMass x₀ ch u / _ * S.indicator 1 y = _
          by_cases h : fhUpperPt x₀ u ∈ S
          · simp [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.2 h)]
          · simp [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hiff.1 h)]
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
            ENNReal.mul_div_cancel hcard (ENNReal.natCast_ne_top _)]
  · intro a _ a' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y', -, e⟩ := Finset.mem_image.1 hu'
    exact hne (List.cons.inj e).2.symm

/-- The measures of all levels are probability measures. -/
theorem fhUpper_measure_univ (k : ℕ) : fhUpperMeasure x₀ ch k univ = 1 := by
  induction k with
  | zero =>
    rw [fhUpper_measure_apply]
    simp [fhUpperLevel, fhUpperMass]
  | succ k ih => rw [fhUpper_measure_succ hx₀ hch fun _ _ _ _ ↦ by simp, ih]

/-- The measures of all levels live on `K'`. -/
theorem fhUpper_measure_compl (k : ℕ) : fhUpperMeasure x₀ ch k K'ᶜ = 0 := by
  rw [fhUpper_measure_apply]
  refine Finset.sum_eq_zero fun l hl ↦ ?_
  have h : fhUpperPt x₀ l ∉ K'ᶜ := fun h ↦ h (fhUpper_pt_mem hx₀ hch hl)
  rw [Set.indicator_of_notMem h, mul_zero]

section Eps

variable (hε : 0 < ε)
include hε

/-- For `q ≤ k`, the measure of level `k` lives on the union of the closed Bowen balls of radius
`ε/2` about the nodes of level `q`. -/
theorem fhUpper_measure_cover {q k : ℕ} (hqk : q ≤ k) :
    fhUpperMeasure x₀ ch k (⋃ c ∈ (fhUpperLevel x₀ ch q).image
      (fun l ↦ (fhUpperPt x₀ l, fhUpperOrd x₀ ch l)), closedBowenBall T c.2 c.1 (ε / 2))ᶜ = 0 := by
  rw [fhUpper_measure_apply]
  refine Finset.sum_eq_zero fun u hu ↦ ?_
  obtain ⟨l, hl, hsub⟩ := fhUpper_descend hx₀ hch hqk hu
  have hrad : ε * (2 : ℝ)⁻¹ ^ q / 2 ≤ ε / 2 := by
    have : (2 : ℝ)⁻¹ ^ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hmem : fhUpperPt x₀ u ∈ ⋃ c ∈ (fhUpperLevel x₀ ch q).image
      (fun l ↦ (fhUpperPt x₀ l, fhUpperOrd x₀ ch l)), closedBowenBall T c.2 c.1 (ε / 2) := by
    refine mem_iUnion₂.2 ⟨(fhUpperPt x₀ l, fhUpperOrd x₀ ch l), Finset.mem_image_of_mem _ hl, ?_⟩
    exact fhUpper_closedBowenBall_mono hrad
      (hsub (fhUpper_self_mem_closedBowenBall (by positivity)))
  rw [Set.indicator_of_notMem (not_not_intro hmem), mul_zero]

/-- For `q ≤ k` and a node `l` of level `q`, the measure of level `k` of the open Bowen ball of
radius `3ε/2` about `l` is at most the mass of `l`. -/
theorem fhUpper_measure_ball {q k : ℕ} (hqk : q ≤ k) {l : List X}
    (hl : l ∈ fhUpperLevel x₀ ch q) :
    fhUpperMeasure x₀ ch k (bowenBall T (fhUpperOrd x₀ ch l) (fhUpperPt x₀ l) (3 * ε / 2)) ≤
      fhUpperMass x₀ ch l := by
  induction k, hqk using Nat.le_induction with
  | base =>
    rw [fhUpper_measure_apply, Finset.sum_eq_single l]
    · by_cases h : fhUpperPt x₀ l ∈ bowenBall T (fhUpperOrd x₀ ch l) (fhUpperPt x₀ l) (3 * ε / 2)
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    · intro l' hl' hne
      rw [Set.indicator_of_notMem (fhUpper_disjoint hx₀ hch hε hl hl' (Ne.symm hne)
        (fhUpper_self_mem_closedBowenBall (by positivity))), mul_zero]
    · exact fun h ↦ absurd hl h
  | succ k hqk ih =>
    rw [fhUpper_measure_succ hx₀ hch ?_]
    · exact ih
    intro u hu y hy
    obtain ⟨l'', hl'', hsub⟩ := fhUpper_descend hx₀ hch hqk hu
    have hpc : fhUpperPt x₀ u ∈ closedBowenBall T (fhUpperOrd x₀ ch u) (fhUpperPt x₀ u)
        (ε * 2⁻¹ ^ k / 2) := fhUpper_self_mem_closedBowenBall (by positivity)
    have hyc := fhUpper_nest hx₀ hch hu hy (fhUpper_self_mem_closedBowenBall (by positivity))
    by_cases he : l'' = l
    · subst he
      exact iff_of_true (fhUpper_cell_subset hε _ _ _ (hsub hyc))
        (fhUpper_cell_subset hε _ _ _ (hsub hpc))
    · exact iff_of_false (fhUpper_disjoint hx₀ hch hε hl hl'' (Ne.symm he) (hsub hyc))
        (fhUpper_disjoint hx₀ hch hε hl hl'' (Ne.symm he) (hsub hpc))

end Eps

end Measure

end Good

end Nodes

/-- **The Cantor tree and its measures.** Let `K'` be nonempty and suppose every Bowen ball about
a point of `K'` contains, at arbitrarily large orders `n`, finite `(n, 4ε)`-separated subsets of
`K'` with more than `2^{n t}` points. Then there are probability measures `ν k` on `K'` and finite
sets `C q` of centers with orders `≥ q` such that, for `q ≤ k`, `ν k` lives on the closed Bowen
balls of radius `ε/2` about `C q` and gives mass at most `2^{-n t}` to the open Bowen ball of
radius `3ε/2` about each center of order `n` in `C q`. -/
theorem fhUpper_tree [MeasurableSpace X] [MeasurableSingletonClass X] [MetricSpace X]
    {T : X → X} {K' : Set X} (hne : K'.Nonempty) {ε t : ℝ} (hε : 0 < ε)
    (hstep : ∀ x ∈ K', ∀ m : ℕ, ∀ ρ > 0, ∀ N : ℕ, ∃ n ≥ N, ∃ E : Finset X,
      ↑E ⊆ K' ∩ bowenBall T m x ρ ∧ FhUpperSeparated T n (4 * ε) E ∧
        (2 : ℝ) ^ ((n : ℝ) * t) < E.card) :
    ∃ (ν : ℕ → Measure X) (C : ℕ → Finset (X × ℕ)), (∀ k, IsProbabilityMeasure (ν k)) ∧
      (∀ k, ν k K'ᶜ = 0) ∧ (∀ q, ∀ c ∈ C q, q ≤ c.2) ∧
      (∀ q k, q ≤ k → ν k (⋃ c ∈ C q, closedBowenBall T c.2 c.1 (ε / 2))ᶜ = 0) ∧
      ∀ q k, q ≤ k → ∀ c ∈ C q,
        ν k (bowenBall T c.2 c.1 (3 * ε / 2)) ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((c.2 : ℝ) * t))) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  have hex : ∀ (x : X) (m q : ℕ), ∃ p : ℕ × Finset X, x ∈ K' → m < p.1 ∧
      ↑p.2 ⊆ K' ∩ bowenBall T m x (ε * 2⁻¹ ^ q / 4) ∧ FhUpperSeparated T p.1 (4 * ε) p.2 ∧
        (2 : ℝ) ^ ((p.1 : ℝ) * t) < p.2.card := by
    intro x m q
    by_cases hx : x ∈ K'
    · obtain ⟨n, hn, E, h1, h2, h3⟩ := hstep x hx m (ε * 2⁻¹ ^ q / 4) (by positivity) (m + 1)
      exact ⟨(n, E), fun _ ↦ ⟨hn, h1, h2, h3⟩⟩
    · exact ⟨(0, ∅), fun h ↦ absurd h hx⟩
  choose ch hch using hex
  have hgood : FhUpperGoodChoice ch T K' ε t := fun x m q hx ↦ hch x m q hx
  refine ⟨fhUpperMeasure x₀ ch, fun q ↦ (fhUpperLevel x₀ ch q).image
    fun l ↦ (fhUpperPt x₀ l, fhUpperOrd x₀ ch l), fun k ↦ ⟨fhUpper_measure_univ hx₀ hgood k⟩,
    fhUpper_measure_compl hx₀ hgood, ?_, fun q k hqk ↦ fhUpper_measure_cover hx₀ hgood hε hqk, ?_⟩
  · intro q c hc
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hc
    exact fhUpper_le_ord hx₀ hgood hl
  · intro q k hqk c hc
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hc
    exact (fhUpper_measure_ball hx₀ hgood hε hqk hl).trans (fhUpper_mass_le hx₀ hgood hl).2

end Tree

section Limit

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The limit measure.** A cluster point `μ` of probability measures `ν k` as produced by
`fhUpper_tree` (on a closed set `K`) is a probability measure with `μ K = 1` whose upper local
entropy at scale `ε` is at least `t` almost everywhere: almost every point lies, for each `q`, in
a closed Bowen ball of radius `ε/2` about a center of order `n ≥ q` whose `3ε/2`-ball has
`μ`-measure at most `2^{-n t}` (portmanteau). -/
theorem fhUpper_limit [CompactSpace X] {T : X → X} {K : Set X} (hK : IsClosed K) {ε t : ℝ}
    (hT : Continuous T) (ν : ℕ → Measure X) (hprob : ∀ k, IsProbabilityMeasure (ν k))
    (hK1 : ∀ k, ν k Kᶜ = 0) (C : ℕ → Finset (X × ℕ)) (hCq : ∀ q, ∀ c ∈ C q, q ≤ c.2)
    (hcover : ∀ q k, q ≤ k → ν k (⋃ c ∈ C q, closedBowenBall T c.2 c.1 (ε / 2))ᶜ = 0)
    (hmass : ∀ q k, q ≤ k → ∀ c ∈ C q,
      ν k (bowenBall T c.2 c.1 (3 * ε / 2)) ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((c.2 : ℝ) * t)))) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ μ K = 1 ∧
      ∀ᵐ z ∂μ, ENNReal.ofReal t ≤ (localEntropyAt μ T z ε).2 := by
  let u : ℕ → ProbabilityMeasure X := fun k ↦ ⟨ν k, hprob k⟩
  obtain ⟨μ, hμ⟩ := exists_clusterPt_of_compactSpace (map u atTop)
  let L : Filter ℕ := atTop ⊓ comap u (𝓝 μ)
  have hL : L.NeBot := by
    rw [← Filter.map_neBot_iff u, Filter.push_pull, inf_comm]
    exact hμ
  have hlim : Tendsto u L (𝓝 μ) := tendsto_iff_comap.2 inf_le_right
  have hev : ∀ {P : ℕ → Prop}, (∀ᶠ k in atTop, P k) → ∀ᶠ k in L, P k :=
    fun h ↦ h.filter_mono inf_le_left
  -- closed sets of eventually full measure have full limit measure
  have hclosed : ∀ F : Set X, IsClosed F → (∀ᶠ k in atTop, ν k Fᶜ = 0) →
      (μ : Measure X) Fᶜ = 0 := by
    intro F hF h
    have h1 := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
    have h2 : (1 : ℝ≥0∞) ≤ L.limsup fun k ↦ (u k : Measure X) F := by
      refine le_limsup_of_frequently_le (hev (h.mono fun k hk ↦ ?_)).frequently
      have := hprob k
      exact ((prob_compl_eq_zero_iff hF.measurableSet).1 hk).ge
    exact (prob_compl_eq_zero_iff hF.measurableSet).2 (le_antisymm prob_le_one (h2.trans h1))
  refine ⟨μ, inferInstance, ?_, ?_⟩
  · exact (prob_compl_eq_zero_iff hK.measurableSet).1
      (hclosed K hK (Eventually.of_forall hK1))
  -- the mass bound for the limit
  have hball : ∀ q, ∀ c ∈ C q, (μ : Measure X) (bowenBall T c.2 c.1 (3 * ε / 2)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-((c.2 : ℝ) * t))) := by
    intro q c hc
    refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
      (bowen_ball_dense_open T hT _ _ _)).trans ?_
    refine liminf_le_of_frequently_le (hev ?_).frequently
    exact (eventually_ge_atTop q).mono fun k hk ↦ hmass q k hk c hc
  -- almost every point lies in every cover
  have hae : ∀ᵐ z ∂(μ : Measure X), ∀ q, z ∈ ⋃ c ∈ C q, closedBowenBall T c.2 c.1 (ε / 2) := by
    refine ae_all_iff.2 fun q ↦ mem_ae_iff.2 ?_
    refine hclosed _ ?_ ((eventually_ge_atTop q).mono fun k hk ↦ hcover q k hk)
    exact isClosed_biUnion_finset fun c _ ↦ isClosed_closedBowenBall hT _ _ _
  filter_upwards [hae] with z hz
  refine le_limsup_of_frequently_le (frequently_atTop.2 fun a ↦ ?_)
  obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.1 (hz (max a 1))
  have hn : max a 1 ≤ c.2 := hCq _ c hc
  refine ⟨c.2, le_of_max_le_left hn, ?_⟩
  have hsub : bowenBall T c.2 z ε ⊆ bowenBall T c.2 c.1 (3 * ε / 2) := by
    intro w hw
    rw [mem_bowenBall_iff] at hw ⊢
    intro k hk
    have := dist_triangle (T^[k] c.1) (T^[k] z) (T^[k] w)
    have := hzc k hk
    have := hw k hk
    linarith
  have hinfo := le_infoBits_of_le_rpow ((measure_mono hsub).trans (hball _ c hc))
  have hn0 : (c.2 : ℝ≥0∞) ≠ 0 := by
    have : 1 ≤ c.2 := le_of_max_le_right hn
    exact_mod_cast (by omega : c.2 ≠ 0)
  unfold localEntropyRate
  rw [ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top _))]
  refine le_trans (le_of_eq ?_) hinfo
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul' (Nat.cast_nonneg _), mul_comm]

/-- The Feng–Huang variational principle, Upper half (the statement of the leaf in
`Variational.lean`). Blueprint node `meas:variational`. -/
theorem upperEntropy_le_iSup_measureEntropy' [CompactSpace X] (P : Presentation X) {T : X → X}
    (hT : Continuous T) {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) :
    upperEntropy P T K ≤
      ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : μ K = 1), (measureEntropy μ T).2 := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  have hctop : c ≠ ⊤ := ne_top_of_lt hc
  set t := c.toReal with ht
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hct : c = ENNReal.ofReal t := (ENNReal.ofReal_toReal hctop).symm
  have hlt : (t : EReal) < upperPressure T (fun _ => 0) 0 K := by
    rw [← entropy_eq_zeroPotentialPressure_of_nonempty_upper P T hT K hne]
    have h := EReal.coe_ennreal_lt_coe_ennreal_iff.2 hc
    rwa [hct, EReal.coe_ennreal_ofReal, max_eq_left ht0] at h
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (t : EReal) <
      modifiedUpperPressure T (fun _ => 0) .centered K (dyadicRadius p) := by
    simp only [upperPressure, lt_iSup_iff] at hlt
    obtain ⟨p, _, hp⟩ := hlt
    exact ⟨p, hp⟩
  set ε := dyadicRadius (p + 2) with hεdef
  have hε : 0 < ε := by rw [hεdef, dyadicRadius]; positivity
  have hr : dyadicRadius p = 4 * ε := by
    rw [hεdef, dyadicRadius, dyadicRadius, pow_add]
    ring
  rw [hr] at hp
  obtain ⟨K', hK'K, hK'ne, hstep⟩ := fhUpper_exists_kernel hT (by positivity) hp
  obtain ⟨ν, C, hprob, hK', hCq, hcover, hmass⟩ := fhUpper_tree hK'ne hε hstep
  obtain ⟨μ, hμ, hμK, hae⟩ := fhUpper_limit hK.isClosed hT ν hprob
    (fun k ↦ measure_mono_null (compl_subset_compl.2 hK'K) (hK' k)) C hCq hcover hmass
  refine le_iSup_of_le μ (le_iSup_of_le hμ (le_iSup_of_le hμK ?_))
  calc c = ∫⁻ _, ENNReal.ofReal t ∂μ := by rw [lintegral_const, measure_univ, mul_one, hct]
    _ ≤ (measureEntropy μ T).2 := by
      refine lintegral_mono_ae (hae.mono fun z hz ↦ hz.trans ?_)
      exact le_iSup (fun q ↦ (localEntropyAt μ T z (dyadicRadius q)).2) (p + 2)

end Limit

end Kolmogorov.PointToSet
