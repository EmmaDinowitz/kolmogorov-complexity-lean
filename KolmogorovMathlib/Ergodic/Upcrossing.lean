/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Ergodic.MaximalInequality

/-!
# An upcrossing inequality for Birkhoff averages (Bishop–V'yugin)

For a real sequence `y`, `UpcrossesAtLeast a b y k L` says that the Cesàro averages
`(1/j) ∑_{i<j} y i` dip below `a` and then rise above `b`, `k` times, at times
`1 ≤ u₁ < v₁ < u₂ < ⋯ < u_k < v_k ≤ L`.

* `measureReal_upcrossesAtLeast_le` (Bishop's inequality, in V'yugin's potential-function form,
  V'yugin, *Ergodic theorems for algorithmically random points*, arXiv:2202.13465, §4.2): for a
  measure-preserving `T` of a probability space and a bounded measurable `f`,
  `μ{x | ∃ L, (f ∘ T^i x)_i upcrosses [a, b] at least k times by L} ≤ ∫ (f - a)⁺ / ((b - a) k)`.
  No ergodicity. Proof: the potential `Λ_L y` (maximal gain of an admissible buy-low/sell-high
  strategy on the prefix sums) satisfies `(b - a) N + Λ_L y ≤ Λ_L (y ∘ succ) + (y 0 - a)⁺` when `y`
  crosses `N` times; integrate along the orbit (invariance) and use Markov's inequality.
* `exists_tendsto_of_forall_not_upcrossesAtLeast`: a bounded sequence whose averages cross every
  rational interval only boundedly often has convergent averages (`tendsto_of_no_upcrossings`).

## Implementation notes

With the prefix sums `P_c(j) = ∑_{i<j} (y i - c)`, an admissible strategy for the window `L` is a
finset `d` of pairs `s < t ≤ L` whose intervals `[s, t]` overlap at most at endpoints; its gain is
`∑_{(s,t) ∈ d} (P_b(t) - P_a(s))`, and the potential `Λ_L y` is the maximal gain (a `Finset.sup'`
over the finitely many admissible finsets). Finsets instead of ordered lists make finiteness free.

* Extension lemma: if the averages cross `N` times, a strategy with fewer than `N` pairs can be
  strictly improved: either some crossing `(u, v)` fits between the pairs (insert it), or by
  pigeonhole two crossings `i < i'` meet the same pair `(s, t)` (split it into `(s, v_i)` and
  `(u_{i'}, t)`). Hence every maximizer has at least `N` pairs.
* Shift identity: moving a strategy one step to the left loses `b - a` per pair and gains at
  most `(y 0 - a)⁺` (only one pair can start at time `0`).
* The measure part needs no measurability of the crossing sets: Markov's inequality is applied to
  the integrable function `(f - a)⁺ + Λ_L ∘ T - Λ_L`, and the union over `L` is handled by
  `Monotone.measure_iUnion` (continuity from below for arbitrary monotone sets).

Blueprint node `erg:upcrossing`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Kolmogorov.Ergodic

/-- The Cesàro average `(1/j) ∑_{i<j} y i`. Blueprint node `erg:upcrossing`. -/
def cesaroAvg (y : ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.range j, y i) / j

/-- The averages of `y` upcross `[a, b]` at least `k` times by time `L`: there are
`1 ≤ u₀ < v₀ < u₁ < ⋯ < u_{k-1} < v_{k-1} ≤ L` with average `< a` at the `u`'s and `> b` at the
`v`'s. Blueprint node `erg:upcrossing`. -/
def UpcrossesAtLeast (a b : ℝ) (y : ℕ → ℝ) (k L : ℕ) : Prop :=
  ∃ u v : ℕ → ℕ, ∀ i < k, 1 ≤ u i ∧ u i < v i ∧ v i ≤ L ∧ (i + 1 < k → v i < u (i + 1)) ∧
    cesaroAvg y (u i) < a ∧ b < cesaroAvg y (v i)

/-! ### Prefix sums -/

/-- The prefix sum `∑_{i<j} (y i - c)`. -/
private def upPrefix (c : ℝ) (y : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, (y i - c)

/-- Shift identity for prefix sums. -/
private lemma upPrefix_succ (c : ℝ) (y : ℕ → ℝ) (j : ℕ) :
    upPrefix c y (j + 1) = (y 0 - c) + upPrefix c (fun i ↦ y (i + 1)) j := by
  simp only [upPrefix]
  rw [Finset.sum_range_succ']
  ring

/-- An average below `a` is a negative prefix sum for the level `a`. -/
private lemma upPrefix_neg_of_cesaroAvg_lt {y : ℕ → ℝ} {a : ℝ} {u : ℕ} (hu : 1 ≤ u)
    (h : cesaroAvg y u < a) : upPrefix a y u < 0 := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  rw [cesaroAvg, div_lt_iff₀ hu'] at h
  simp only [upPrefix, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

/-- An average above `b` is a positive prefix sum for the level `b`. -/
private lemma upPrefix_pos_of_lt_cesaroAvg {y : ℕ → ℝ} {b : ℝ} {v : ℕ} (hv : 1 ≤ v)
    (h : b < cesaroAvg y v) : 0 < upPrefix b y v := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  rw [cesaroAvg, lt_div_iff₀ hv'] at h
  simp only [upPrefix, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

/-- The value of one buy/sell pair `(s, t)`, rewritten for the shifted sequence. -/
private lemma upPrefix_pair (a b : ℝ) (y : ℕ → ℝ) {s t : ℕ} (hst : s < t) :
    upPrefix b y t - upPrefix a y s =
      (upPrefix b (fun i ↦ y (i + 1)) (t - 1) - upPrefix a (fun i ↦ y (i + 1)) (s - 1)) +
        (if s = 0 then y 0 - a else 0) - (b - a) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rcases s with _ | s
  · rw [upPrefix_succ]
    simp only [Nat.add_sub_cancel, Nat.zero_sub, ↓reduceIte, upPrefix, Finset.range_zero,
      Finset.sum_empty]
    ring
  · simp only [upPrefix_succ, Nat.add_sub_cancel, Nat.add_one_ne_zero, ↓reduceIte]
    ring

/-! ### Admissible strategies and the potential -/

/-- An admissible strategy for the window `L`: disjoint buy/sell pairs `s < t ≤ L`. -/
private def UpAdm (L : ℕ) (d : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ d, p.1 < p.2 ∧ p.2 ≤ L) ∧ ∀ p ∈ d, ∀ q ∈ d, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1

/-- The gain `∑_{(s,t) ∈ d} (P_b(t) - P_a(s))` of a strategy. -/
private def upGain (a b : ℝ) (y : ℕ → ℝ) (d : Finset (ℕ × ℕ)) : ℝ :=
  ∑ p ∈ d, (upPrefix b y p.2 - upPrefix a y p.1)

open Classical in
/-- The (finite) set of admissible strategies for the window `L`. -/
private def upCands (L : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (Finset.range (L + 1) ×ˢ Finset.range (L + 1)).powerset.filter (UpAdm L)

/-- Membership in `upCands`. -/
private lemma mem_upCands {L : ℕ} {d : Finset (ℕ × ℕ)} : d ∈ upCands L ↔ UpAdm L d := by
  simp only [upCands, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun p hp ↦ ?_, h⟩⟩
  have := h.1 p hp
  simp only [Finset.mem_product, Finset.mem_range]
  omega

/-- The empty strategy is admissible. -/
private lemma empty_mem_upCands (L : ℕ) : ∅ ∈ upCands L :=
  mem_upCands.2 ⟨by simp, by simp⟩

/-- There is an admissible strategy. -/
private lemma upCands_nonempty (L : ℕ) : (upCands L).Nonempty :=
  ⟨∅, empty_mem_upCands L⟩

/-- The potential: the maximal gain of an admissible strategy. -/
private def upPot (a b : ℝ) (L : ℕ) (y : ℕ → ℝ) : ℝ :=
  (upCands L).sup' (upCands_nonempty L) (upGain a b y)

/-- Every admissible gain is at most the potential. -/
private lemma upGain_le_upPot {a b : ℝ} {L : ℕ} {y : ℕ → ℝ} {d : Finset (ℕ × ℕ)}
    (hd : UpAdm L d) : upGain a b y d ≤ upPot a b L y :=
  Finset.le_sup' (upGain a b y) (mem_upCands.2 hd)

/-- The potential is attained. -/
private lemma exists_upPot_eq (a b : ℝ) (L : ℕ) (y : ℕ → ℝ) :
    ∃ d, UpAdm L d ∧ upGain a b y d = upPot a b L y := by
  obtain ⟨d, hd, h⟩ := Finset.exists_mem_eq_sup' (upCands_nonempty L) (upGain a b y)
  exact ⟨d, mem_upCands.1 hd, h.symm⟩

/-! ### The extension lemma -/

/-- Splitting a pair `(s, t)` around `s < v' < u' < t` into `(s, v')` and `(u', t)`. -/
private lemma upGain_split {a b : ℝ} {y : ℕ → ℝ} {L : ℕ} {d : Finset (ℕ × ℕ)} (hd : UpAdm L d)
    {s t : ℕ} (hp : (s, t) ∈ d) {v' u' : ℕ} (h1 : s < v') (h2 : v' < u') (h3 : u' < t) :
    ∃ d', UpAdm L d' ∧
      upGain a b y d' = upGain a b y d + (upPrefix b y v' - upPrefix a y u') := by
  have key : ∀ q ∈ d.erase (s, t), q.2 ≤ s ∨ t ≤ q.1 := fun q hq ↦ by
    obtain ⟨hne, hmd⟩ := Finset.mem_erase.1 hq
    simpa using hd.2 _ hmd _ hp hne
  have hq1 : ∀ q ∈ d.erase (s, t), q.1 < q.2 ∧ q.2 ≤ L :=
    fun q hq ↦ hd.1 q (Finset.mem_of_mem_erase hq)
  have hst := hd.1 _ hp
  simp only at hst
  have hA : (u', t) ∉ d.erase (s, t) := by
    intro hm
    rcases key _ hm with h | h <;> simp only at h <;> omega
  have hB : (s, v') ∉ insert (u', t) (d.erase (s, t)) := by
    rw [Finset.mem_insert]
    rintro (h | hm)
    · simp only [Prod.mk.injEq] at h
      omega
    · rcases key _ hm with h | h <;> simp only at h <;> omega
  refine ⟨insert (s, v') (insert (u', t) (d.erase (s, t))), ⟨?_, ?_⟩, ?_⟩
  · intro q hq
    rw [Finset.mem_insert, Finset.mem_insert] at hq
    rcases hq with rfl | rfl | hq
    · simp only
      omega
    · simp only
      omega
    · exact hq1 q hq
  · intro q hq r hr hqr
    rw [Finset.mem_insert, Finset.mem_insert] at hq hr
    rcases hq with rfl | rfl | hq <;> rcases hr with rfl | rfl | hr
    · exact absurd rfl hqr
    · simp only
      omega
    · have := key r hr
      simp only
      omega
    · simp only
      omega
    · exact absurd rfl hqr
    · have := key r hr
      simp only
      omega
    · have := key q hq
      have := hq1 q hq
      simp only
      omega
    · have := key q hq
      have := hq1 q hq
      simp only
      omega
    · exact hd.2 q (Finset.mem_of_mem_erase hq) r (Finset.mem_of_mem_erase hr) hqr
  · rw [upGain, upGain, Finset.sum_insert hB, Finset.sum_insert hA, Finset.sum_erase_eq_sub hp]
    ring

/-- Consecutive crossing links compose: `v i < u j` for `i < j`. -/
private lemma upcross_chain {k : ℕ} {u v : ℕ → ℕ}
    (h : ∀ i < k, u i < v i ∧ (i + 1 < k → v i < u (i + 1))) {i j : ℕ} (hij : i < j)
    (hj : j < k) : v i < u j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
    · have h1 := ih h' (by omega)
      have h2 := (h j (by omega)).1
      have h3 := (h j (by omega)).2 hj
      omega
    · exact (h i (by omega)).2 hj

/-- Extension lemma (V'yugin, Lemma 1): if the averages cross `N` times, every admissible strategy
with fewer than `N` pairs can be strictly improved. -/
private lemma upGain_extend {a b : ℝ} {y : ℕ → ℝ} {N L : ℕ} (hN : UpcrossesAtLeast a b y N L)
    {d : Finset (ℕ × ℕ)} (hd : UpAdm L d) (hdN : d.card < N) :
    ∃ d', UpAdm L d' ∧ upGain a b y d < upGain a b y d' := by
  obtain ⟨u, v, huv⟩ := hN
  have hlt : ∀ i < N, upPrefix a y (u i) < 0 := fun i hi ↦
    upPrefix_neg_of_cesaroAvg_lt (huv i hi).1 (huv i hi).2.2.2.2.1
  have hgt : ∀ i < N, 0 < upPrefix b y (v i) := fun i hi ↦
    upPrefix_pos_of_lt_cesaroAvg (by have := huv i hi; omega) (huv i hi).2.2.2.2.2
  have hchain : ∀ i j, i < j → j < N → v i < u j := fun i j hij hj ↦
    upcross_chain (fun i hi ↦ ⟨(huv i hi).2.1, (huv i hi).2.2.2.1⟩) hij hj
  by_cases hfit : ∃ i < N, ∀ p ∈ d, v i ≤ p.1 ∨ p.2 ≤ u i
  · obtain ⟨i, hi, hfi⟩ := hfit
    have hui := huv i hi
    have hnot : (u i, v i) ∉ d := by
      intro hm
      have := hfi _ hm
      simp only at this
      omega
    refine ⟨insert (u i, v i) d, ⟨?_, ?_⟩, ?_⟩
    · intro p hp
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact ⟨hui.2.1, hui.2.2.1⟩
      · exact hd.1 p hp
    · intro p hp q hq hpq
      rw [Finset.mem_insert] at hp hq
      rcases hp with rfl | hp <;> rcases hq with rfl | hq
      · exact absurd rfl hpq
      · exact hfi q hq
      · exact (hfi p hp).symm
      · exact hd.2 p hp q hq hpq
    · rw [upGain, upGain, Finset.sum_insert hnot]
      have := hlt i hi
      have := hgt i hi
      linarith
  · push Not at hfit
    choose! g hgd hg using hfit
    obtain ⟨i, hi, i', hi', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range N) (t := d) (by simpa using hdN)
      (fun i hi ↦ hgd i (Finset.mem_range.1 hi))
    rw [Finset.mem_range] at hi hi'
    -- the pair `p` shared by two crossings `j < j'`
    have main : ∀ j j', j < j' → j' < N → g j = g j' →
        ∃ d', UpAdm L d' ∧ upGain a b y d < upGain a b y d' := by
      intro j j' hjj hj' hgj
      have hj : j < N := by omega
      obtain ⟨d', hd', hgain⟩ := upGain_split (a := a) (b := b) (y := y) hd
        (s := (g j).1) (t := (g j).2) (by simpa using hgd j hj) (hg j hj).1 (hchain j j' hjj hj')
        (by rw [hgj]; exact (hg j' hj').2)
      refine ⟨d', hd', ?_⟩
      have := hlt j' hj'
      have := hgt j hj
      linarith
    rcases lt_or_gt_of_ne hne with h | h
    · exact main i i' h hi' heq
    · exact main i' i h hi heq.symm

/-! ### The shift inequality -/

/-- Shifting a strategy by one step (V'yugin's identity): the gain drops by `b - a` per pair,
up to the term `(y 0 - a)⁺` of a pair bought at time `0`. -/
private lemma upGain_le_shift (a b : ℝ) (y : ℕ → ℝ) {L : ℕ} {d : Finset (ℕ × ℕ)}
    (hd : UpAdm L d) :
    upGain a b y d ≤ upPot a b L (fun i ↦ y (i + 1)) + max (y 0 - a) 0 - (b - a) * d.card := by
  classical
  set y' : ℕ → ℝ := fun i ↦ y (i + 1)
  set φ : ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.1 - 1, p.2 - 1)
  set G : ℕ × ℕ → ℝ := fun q ↦ upPrefix b y' q.2 - upPrefix a y' q.1
  have hinj : ∀ p ∈ d, ∀ q ∈ d, φ p = φ q → p = q := by
    intro p hp q hq hpq
    by_contra hne
    have h1 := hd.1 p hp
    have h2 := hd.1 q hq
    simp only [φ, Prod.mk.injEq] at hpq
    rcases hd.2 p hp q hq hne with h | h <;> omega
  set d' := (d.image φ).erase (0, 0)
  have hd' : UpAdm L d' := by
    constructor
    · intro q hq
      obtain ⟨hq0, hq⟩ := Finset.mem_erase.1 hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      have := hd.1 p hp
      simp only [φ, ne_eq, Prod.mk.injEq] at hq0 ⊢
      omega
    · intro q hq r hr hqr
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hq)
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hr)
      have hne : p ≠ p' := fun h ↦ hqr (by rw [h])
      simp only [φ]
      rcases hd.2 p hp p' hp' hne with h | h <;> omega
  have hG0 : G (0, 0) = 0 := by simp [G, upPrefix]
  have hsum : ∑ p ∈ d, G (φ p) = upGain a b y' d' := by
    rw [upGain, Finset.sum_erase _ hG0, Finset.sum_image hinj]
  have hcard : (d.filter (fun p ↦ p.1 = 0)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun p hp q hq ↦ ?_
    by_contra hne
    rw [Finset.mem_filter] at hp hq
    have h1 := hd.1 p hp.1
    have h2 := hd.1 q hq.1
    rcases hd.2 p hp.1 q hq.1 hne with h | h <;> omega
  have hite : ∑ p ∈ d, (if p.1 = 0 then y 0 - a else 0) ≤ max (y 0 - a) 0 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, add_zero]
    rcases (by omega : (d.filter (fun p ↦ p.1 = 0)).card = 0 ∨
      (d.filter (fun p ↦ p.1 = 0)).card = 1) with h | h <;> rw [h] <;> simp
  have hexp : upGain a b y d =
      ∑ p ∈ d, G (φ p) + ∑ p ∈ d, (if p.1 = 0 then y 0 - a else 0) - (b - a) * d.card := by
    rw [upGain, ← Finset.sum_add_distrib, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    exact upPrefix_pair a b y (hd.1 p hp).1
  have := upGain_le_upPot (a := a) (b := b) (y := y') hd'
  rw [hexp, hsum]
  linarith

/-- V'yugin's pointwise potential inequality (12): if the averages of `y` cross `[a, b]` `N` times
by time `L`, then `(b - a) N + Λ_L y ≤ Λ_L (y ∘ succ) + (y 0 - a)⁺`. -/
private lemma upPot_le_shift {a b : ℝ} (hab : a ≤ b) {y : ℕ → ℝ} {N L : ℕ}
    (hN : UpcrossesAtLeast a b y N L) :
    (b - a) * N + upPot a b L y ≤ upPot a b L (fun i ↦ y (i + 1)) + max (y 0 - a) 0 := by
  obtain ⟨q, hq, hqe⟩ := exists_upPot_eq a b L y
  have hcard : N ≤ q.card := by
    by_contra h
    push Not at h
    obtain ⟨d', hd', hlt⟩ := upGain_extend hN hq h
    have := upGain_le_upPot (a := a) (b := b) (y := y) hd'
    linarith
  have h1 := upGain_le_shift a b y hq
  have h2 : (b - a) * N ≤ (b - a) * q.card :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by linarith)
  linarith

/-- Zero crossings always happen. -/
private lemma upcrossesAtLeast_zero (a b : ℝ) (y : ℕ → ℝ) (L : ℕ) : UpcrossesAtLeast a b y 0 L :=
  ⟨id, id, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩

/-- Crossing more often is harder: monotonicity in the window. -/
private lemma UpcrossesAtLeast.mono_window {a b : ℝ} {y : ℕ → ℝ} {k L L' : ℕ}
    (h : UpcrossesAtLeast a b y k L) (hL : L ≤ L') : UpcrossesAtLeast a b y k L' := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u, v, fun i hi ↦ ⟨(huv i hi).1, (huv i hi).2.1, (huv i hi).2.2.1.trans hL,
    (huv i hi).2.2.2⟩⟩

/-! ### Bishop's inequality -/

variable {X : Type*} [MeasurableSpace X]

/-- The potential along an orbit is integrable. -/
private lemma integrable_upPot {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Measurable T) {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (a b : ℝ) (L : ℕ) : Integrable (fun x ↦ upPot a b L (fun i ↦ f (T^[i] x))) μ := by
  have hfi : ∀ i, Integrable (fun x ↦ f (T^[i] x)) μ := fun i ↦
    Integrable.of_bound (hf.comp (hT.iterate i)).aestronglyMeasurable C
      (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hC _)
  have hP : ∀ c j, Integrable (fun x ↦ upPrefix c (fun i ↦ f (T^[i] x)) j) μ := fun c j ↦ by
    simp only [upPrefix]
    exact integrable_finsetSum _ fun i _ ↦ (hfi i).sub (integrable_const c)
  have hG : ∀ d, Integrable (fun x ↦ upGain a b (fun i ↦ f (T^[i] x)) d) μ := fun d ↦ by
    simp only [upGain]
    exact integrable_finsetSum _ fun p _ ↦ (hP b p.2).sub (hP a p.1)
  have heq : (fun x ↦ upPot a b L (fun i ↦ f (T^[i] x))) =
      (upCands L).sup' (upCands_nonempty L)
        (fun d x ↦ upGain a b (fun i ↦ f (T^[i] x)) d) := by
    ext x
    rw [Finset.sup'_apply]
    rfl
  rw [heq]
  exact Finset.sup'_induction (p := fun g : X → ℝ ↦ Integrable g μ) _ _
    (fun g₁ h₁ g₂ h₂ ↦ h₁.sup h₂) (fun d _ ↦ hG d)

/-- Bishop's upcrossing inequality for Birkhoff averages of a bounded measurable function under a
measure-preserving map (no ergodicity). Blueprint node `erg:upcrossing`. -/
theorem measureReal_upcrossesAtLeast_le {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) {a b : ℝ} (hab : a < b) {k : ℕ} (hk : 1 ≤ k) :
    μ.real {x | ∃ L, UpcrossesAtLeast a b (fun i ↦ f (T^[i] x)) k L} ≤
      (∫ x, max (f x - a) 0 ∂μ) / ((b - a) * k) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : 0 < (b - a) * k := mul_pos hba hk'
  set I := ∫ x, max (f x - a) 0 ∂μ with hIdef
  have hI : 0 ≤ I := integral_nonneg fun x ↦ le_max_right _ _
  have hfa : Integrable (fun x ↦ max (f x - a) 0) μ := by
    refine Integrable.of_bound ((hf.sub_const a).max measurable_const).aestronglyMeasurable
      (C + |a|) (ae_of_all _ fun x ↦ ?_)
    have h1 := hC x
    have h2 := abs_le.1 h1
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := le_max_right (f x - a) 0
      linarith [abs_nonneg a, abs_nonneg (f x)]
    · rw [max_le_iff]
      constructor
      · linarith [neg_abs_le a]
      · linarith [abs_nonneg a, abs_nonneg (f x)]
  have hL : ∀ L, μ {x | UpcrossesAtLeast a b (fun i ↦ f (T^[i] x)) k L} ≤
      ENNReal.ofReal (I / ((b - a) * k)) := by
    intro L
    set h : X → ℝ := fun x ↦ upPot a b L (fun i ↦ f (T^[i] x)) with hhdef
    have hh : Integrable h μ := integrable_upPot hT.measurable hf hC a b L
    have hhT : Integrable (h ∘ T) μ := hT.integrable_comp_of_integrable hh
    have hint : ∫ x, h (T x) ∂μ = ∫ x, h x ∂μ := by
      rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hh.1), hT.map_eq]
    have hshift : ∀ x, h (T x) = upPot a b L (fun i ↦ (fun i ↦ f (T^[i] x)) (i + 1)) := by
      intro x
      simp only [h, Function.iterate_succ_apply]
    set g : X → ℝ := fun x ↦ max (f x - a) 0 + h (T x) - h x with hgdef
    have hgi : Integrable g μ := (hfa.add hhT).sub hh
    have hg0 : ∀ x, 0 ≤ g x := by
      intro x
      have := upPot_le_shift hab.le (upcrossesAtLeast_zero a b (fun i ↦ f (T^[i] x)) L)
      simp only [g, hshift x, h]
      simp only [Function.iterate_zero, id_eq, CharP.cast_eq_zero, mul_zero, zero_add] at this
      linarith
    have hgk : ∀ x, UpcrossesAtLeast a b (fun i ↦ f (T^[i] x)) k L → (b - a) * k ≤ g x := by
      intro x hx
      have := upPot_le_shift hab.le hx
      simp only [g, hshift x, h]
      simp only [Function.iterate_zero, id_eq] at this
      linarith
    have hgint : ∫ x, g x ∂μ = I := by
      have e1 : ∫ x, (max (f x - a) 0 + h (T x) - h x) ∂μ =
          ∫ x, (max (f x - a) 0 + h (T x)) ∂μ - ∫ x, h x ∂μ := integral_sub (hfa.add hhT) hh
      have e2 : ∫ x, (max (f x - a) 0 + h (T x)) ∂μ =
          ∫ x, max (f x - a) 0 ∂μ + ∫ x, h (T x) ∂μ := integral_add hfa hhT
      simp only [g]
      rw [e1, e2, hint]
      ring
    have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hg0) hgi ((b - a) * k)
    rw [hgint] at hmarkov
    calc μ {x | UpcrossesAtLeast a b (fun i ↦ f (T^[i] x)) k L}
        ≤ μ {x | (b - a) * k ≤ g x} := measure_mono fun x hx ↦ hgk x hx
      _ = ENNReal.ofReal (μ.real {x | (b - a) * k ≤ g x}) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (I / ((b - a) * k)) := by
          gcongr
          rw [le_div_iff₀ hden]
          linarith
  have hmono : Monotone fun L ↦ {x | UpcrossesAtLeast a b (fun i ↦ f (T^[i] x)) k L} :=
    fun L L' hLL' x hx ↦ UpcrossesAtLeast.mono_window hx hLL'
  have hU : μ {x | ∃ L, UpcrossesAtLeast a b (fun i ↦ f (T^[i] x)) k L} ≤
      ENNReal.ofReal (I / ((b - a) * k)) := by
    rw [Set.ofPred_exists, hmono.measure_iUnion]
    exact iSup_le hL
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hI hden.le) hU

/-! ### Convergence of averages -/

/-- Appending one more crossing after time `L`. -/
private lemma UpcrossesAtLeast.succ {a b : ℝ} {y : ℕ → ℝ} {k L : ℕ}
    (h : UpcrossesAtLeast a b y k L) {n m : ℕ} (hLn : L < n) (hnm : n < m)
    (hn : cesaroAvg y n < a) (hm : b < cesaroAvg y m) : UpcrossesAtLeast a b y (k + 1) m := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨fun i ↦ if i < k then u i else n, fun i ↦ if i < k then v i else m, fun i hi ↦ ?_⟩
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hik | rfl
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := huv i hik
    simp only [hik, ↓reduceIte]
    refine ⟨h1, h2, by omega, fun hi1 ↦ ?_, h5, h6⟩
    by_cases hi1k : i + 1 < k
    · simp only [hi1k, ↓reduceIte]
      exact h4 hi1k
    · simp only [hi1k, ↓reduceIte]
      omega
  · simp only [lt_irrefl, ↓reduceIte]
    exact ⟨by omega, hnm, le_rfl, fun h ↦ by simp at h, hn, hm⟩

/-- If the averages are frequently below `a` and frequently above `b`, they cross `[a, b]`
arbitrarily often. -/
private lemma exists_upcrossesAtLeast_of_frequently {a b : ℝ} {y : ℕ → ℝ}
    (ha : ∃ᶠ n in atTop, cesaroAvg y n < a) (hb : ∃ᶠ n in atTop, b < cesaroAvg y n) (k : ℕ) :
    ∃ L, UpcrossesAtLeast a b y k L := by
  induction k with
  | zero => exact ⟨0, upcrossesAtLeast_zero a b y 0⟩
  | succ k ih =>
    obtain ⟨L, hL⟩ := ih
    obtain ⟨n, hn, hna⟩ := Filter.frequently_atTop.1 ha (L + 1)
    obtain ⟨m, hm, hmb⟩ := Filter.frequently_atTop.1 hb (n + 1)
    exact ⟨m, hL.succ (by omega) (by omega) hna hmb⟩

/-- A bounded sequence whose averages upcross every rational interval only boundedly often has
convergent averages. Blueprint node `erg:upcrossing`. -/
theorem exists_tendsto_of_forall_not_upcrossesAtLeast {y : ℕ → ℝ} {C : ℝ}
    (hC : ∀ i, |y i| ≤ C)
    (h : ∀ a b : ℚ, a < b → ∃ k, ∀ L, ¬ UpcrossesAtLeast a b y k L) :
    ∃ l, Tendsto (cesaroAvg y) atTop (𝓝 l) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hbd : ∀ j, |cesaroAvg y j| ≤ C := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [cesaroAvg, hC0]
    · have hj' : (0 : ℝ) < j := by exact_mod_cast hj
      rw [cesaroAvg, abs_div, abs_of_pos hj', div_le_iff₀ hj']
      calc |∑ i ∈ Finset.range j, y i| ≤ ∑ i ∈ Finset.range j, |y i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ Finset.range j, C := Finset.sum_le_sum fun i _ ↦ hC i
        _ = C * j := by simp [mul_comm]
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_
    (isBoundedUnder_of ⟨C, fun n ↦ (le_abs_self _).trans (hbd n)⟩)
    (isBoundedUnder_of ⟨-C, fun n ↦ neg_le_of_abs_le (hbd n)⟩)
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab ⟨ha, hb⟩
  obtain ⟨k, hk⟩ := h a b (by exact_mod_cast hab)
  obtain ⟨L, hL⟩ := exists_upcrossesAtLeast_of_frequently ha hb k
  exact hk L hL

end Kolmogorov.Ergodic
