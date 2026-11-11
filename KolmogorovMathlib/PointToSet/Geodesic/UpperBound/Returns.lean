/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.GeometricData

/-!
# Controlled returns, positive rates and stopping times (geodesic blueprint, Chapter I, part 1)

The nodes `geo:controlled-returns`, `geo:positive-rates`, `geo:stopping-times` and
`geo:return-adjustment` of `geodesic_upper_bound_blueprint.md`: the two pointwise hypotheses of
the upper bound (`ControlledReturns`, `PositiveRates`), the eventual linear lower bound on the
Birkhoff sums of `u^±` that positive rates provide, the stopping times `n(p)` at which
`S_n u(x) - ρ n` first reaches `p`, and the adjustment of a stopping time to a regular return.
The Birkhoff-sum bookkeeping lemmas `exists_linear_of_lowerBirkhoffAverage_pos`,
`birkhoffSum_bounds_of_le` and `stopping_time_aux` are shared with the limit arguments of
`UpperBound/PrecisionChain.lean` and `UpperBound/Mixed.lean`.

Conventions: integer return times (decision D6); `u^± ≥ 0` (G2) is load-bearing in
`return_adjustment`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

namespace GeodesicReconstructionData

variable (G : GeodesicReconstructionData X)

/-! ### `geo:controlled-returns` and `geo:positive-rates` -/

/-- Controlled regular returns with integer times: for every `c > 1` there are compact regular
sets `Pp, Pm` and a threshold `K` such that every `n > K` admits integer times
`T⁺, T⁻ ∈ [n, c n]` with `φ T⁺ x ∈ Pp` and `φ (-T⁻) x ∈ Pm`. No convergence of averages is
assumed. Blueprint node `geo:controlled-returns` (decision D6). -/
def ControlledReturns (x : X) : Prop :=
  ∀ c : ℝ, 1 < c → ∃ Pp Pm : Set X, IsCompact Pp ∧ Pp ⊆ G.Reg ∧ IsCompact Pm ∧ Pm ⊆ G.Reg ∧
    ∃ K : ℕ, ∀ n : ℕ, K < n →
      (∃ T : ℕ, n ≤ T ∧ (T : ℝ) ≤ c * n ∧ G.φ (T : ℝ) x ∈ Pp) ∧
      (∃ T : ℕ, n ≤ T ∧ (T : ℝ) ≤ c * n ∧ G.φ (-(T : ℝ)) x ∈ Pm)

/-- The set `𝓡` of points with controlled regular returns. -/
def controlledReturnsSet : Set X := {x | G.ControlledReturns x}

/-- Points with controlled returns are regular (invariance of `Reg`).
Blueprint node `geo:controlled-returns`. -/
theorem ControlledReturns.mem_Reg {x : X} (hx : G.ControlledReturns x) : x ∈ G.Reg := by
  obtain ⟨Pp, Pm, -, hPp, -, -, K, hK⟩ := hx 2 (by norm_num)
  obtain ⟨⟨T, -, -, hT⟩, -⟩ := hK (K + 1) (Nat.lt_succ_self K)
  rw [← G.Reg_invariant (-(T : ℝ))]
  refine ⟨_, hPp hT, ?_⟩
  rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]

/-- The real-time definition of the drafts implies the integer-time one after enlarging the
endpoint sets to `φ [-1, 0] P^±`, which stay compact and regular.
Blueprint node `geo:controlled-returns` (decision D6). -/
theorem controlledReturns_of_real {x : X}
    (h : ∀ c : ℝ, 1 < c → ∃ Pp Pm : Set X, IsCompact Pp ∧ Pp ⊆ G.Reg ∧ IsCompact Pm ∧
      Pm ⊆ G.Reg ∧ ∃ K : ℝ, ∀ t : ℝ, K < t →
        (∃ s : ℝ, t ≤ s ∧ s ≤ c * t ∧ G.φ s x ∈ Pp) ∧
        (∃ s : ℝ, t ≤ s ∧ s ≤ c * t ∧ G.φ (-s) x ∈ Pm)) :
    G.ControlledReturns x := by
  intro c hc
  set c' : ℝ := (1 + c) / 2 with hc'
  have hc'1 : 1 < c' := by rw [hc']; linarith
  obtain ⟨Pp, Pm, hPp, hPpR, hPm, hPmR, K, hK⟩ := h c' hc'1
  let F : ℝ × X → X := fun q ↦ G.φ q.1 q.2
  have hF : Continuous F := G.φ.continuous continuous_fst continuous_snd
  have himage : ∀ P : Set X, IsCompact P → P ⊆ G.Reg →
      IsCompact (F '' (Icc (-1) 1 ×ˢ P)) ∧ F '' (Icc (-1) 1 ×ˢ P) ⊆ G.Reg := by
    intro P hP hPR
    refine ⟨(isCompact_Icc.prod hP).image hF, ?_⟩
    rintro _ ⟨⟨s, y⟩, ⟨-, hy⟩, rfl⟩
    rw [← G.Reg_invariant s]
    exact ⟨y, hPR hy, rfl⟩
  obtain ⟨hPp', hPpR'⟩ := himage Pp hPp hPpR
  obtain ⟨hPm', hPmR'⟩ := himage Pm hPm hPmR
  refine ⟨_, _, hPp', hPpR', hPm', hPmR', max ⌈K⌉₊ ⌈2 / (c - 1)⌉₊, fun n hn ↦ ?_⟩
  have hnK : K < n := by
    have h1 : ⌈K⌉₊ < n := lt_of_le_of_lt (le_max_left _ _) hn
    calc K ≤ ⌈K⌉₊ := Nat.le_ceil K
      _ < n := by exact_mod_cast h1
  have hn2 : 2 / (c - 1) ≤ n := by
    have h1 : ⌈2 / (c - 1)⌉₊ ≤ n := (le_max_right _ _).trans hn.le
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hcn : c' * n + 1 ≤ c * n := by
    have hc1 : 0 < c - 1 := by linarith
    rw [div_le_iff₀ hc1] at hn2
    rw [hc']; nlinarith
  obtain ⟨⟨s, hns, hsc, hs⟩, ⟨s', hns', hsc', hs'⟩⟩ := hK n hnK
  have key : ∀ s : ℝ, (n : ℝ) ≤ s → s ≤ c' * n →
      ∃ T : ℕ, n ≤ T ∧ (T : ℝ) ≤ c * n ∧ (T : ℝ) - s ∈ Icc (-1 : ℝ) 1 := by
    intro s hns hsc
    have hs0 : 0 ≤ s := (Nat.cast_nonneg n).trans hns
    refine ⟨⌈s⌉₊, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hns.trans (Nat.le_ceil s)
    · linarith [Nat.ceil_lt_add_one hs0]
    · linarith [Nat.le_ceil s]
    · linarith [Nat.ceil_lt_add_one hs0]
  constructor
  · obtain ⟨T, hT1, hT2, hT3⟩ := key s hns hsc
    refine ⟨T, hT1, hT2, ⟨((T : ℝ) - s, G.φ s x), ⟨hT3, hs⟩, ?_⟩⟩
    change G.φ ((T : ℝ) - s) (G.φ s x) = G.φ (T : ℝ) x
    rw [← Flow.map_add, sub_add_cancel]
  · obtain ⟨T, hT1, hT2, hT3⟩ := key s' hns' hsc'
    refine ⟨T, hT1, hT2, ⟨(-((T : ℝ) - s'), G.φ (-s') x), ⟨?_, hs'⟩, ?_⟩⟩
    · constructor <;> linarith [hT3.1, hT3.2]
    · change G.φ (-((T : ℝ) - s')) (G.φ (-s') x) = G.φ (-(T : ℝ)) x
      rw [← Flow.map_add]; congr 1; ring

/-- Positive lower forward unstable and backward stable rates.
Blueprint node `geo:positive-rates`. -/
def PositiveRates (x : X) : Prop :=
  0 < lowerBirkhoffAverage G.f G.uPlus x ∧ 0 < lowerBirkhoffAverage G.finv G.uMinus x


omit [MetricSpace X] [CompactSpace X] in
/-- A positive lower Birkhoff average gives an eventual linear lower bound on the Birkhoff
sums (any positive real below the `liminf`). -/
lemma exists_linear_of_lowerBirkhoffAverage_pos {T : X → X} {u : X → ℝ} {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → c * n ≤ birkhoffSum T u n x := by
  obtain ⟨b, hb0, hb⟩ := exists_between hx
  have hbt : b ≠ ⊤ := ne_top_of_lt hb
  have hbb : b ≠ ⊥ := ne_bot_of_gt hb0
  have hcb : ((b.toReal : ℝ) : EReal) = b := EReal.coe_toReal hbt hbb
  have hc0 : 0 < b.toReal := by
    have := hb0
    rw [← hcb] at this
    exact_mod_cast this
  have hev : ∀ᶠ n : ℕ in atTop, b < ((birkhoffSum T u n x / n : ℝ) : EReal) :=
    eventually_lt_of_lt_liminf hb
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨b.toReal, hc0, N + 1, fun n hn ↦ ?_⟩
  have h := hN n (by omega)
  rw [← hcb, EReal.coe_lt_coe_iff] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [lt_div_iff₀ hn0] at h
  exact h.le

/-- Positive rates give a common eventual linear lower bound `S_n u^±(x) ≥ λ̲ n` for `n ≥ N₀`.
Blueprint node `geo:positive-rates`. -/
theorem PositiveRates.exists_linear {x : X} (hx : G.PositiveRates x) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      lam * n ≤ birkhoffSum G.f G.uPlus n x ∧ lam * n ≤ birkhoffSum G.finv G.uMinus n x := by
  obtain ⟨c₁, hc₁, N₁, hN₁⟩ := exists_linear_of_lowerBirkhoffAverage_pos hx.1
  obtain ⟨c₂, hc₂, N₂, hN₂⟩ := exists_linear_of_lowerBirkhoffAverage_pos hx.2
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max N₁ N₂, fun n hn ↦ ⟨?_, ?_⟩⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg (α := ℝ) n)).trans
      (hN₁ n (le_of_max_le_left hn))
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg (α := ℝ) n)).trans
      (hN₂ n (le_of_max_le_right hn))

/-- The common bound `Λ' = Λ / log 2` of both unit potentials. -/
noncomputable def Λ' : ℝ := G.Λ / Real.log 2


omit [MetricSpace X] [CompactSpace X] in
/-- Birkhoff sums of a function with values in `[0, M]` are monotone in the duration and grow
at most linearly with slope `M`. -/
lemma birkhoffSum_bounds_of_le {T : X → X} {u : X → ℝ} {M : ℝ} (hu0 : ∀ y, 0 ≤ u y)
    (huM : ∀ y, u y ≤ M) (x : X) {n m : ℕ} (hnm : n ≤ m) :
    birkhoffSum T u n x ≤ birkhoffSum T u m x ∧
      birkhoffSum T u m x ≤ birkhoffSum T u n x + M * (m - n : ℕ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [birkhoffSum_add_right_apply, Nat.add_sub_cancel_left]
  constructor
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hu0 _)
  · refine add_le_add le_rfl ?_
    have := Finset.sum_le_card_nsmul (Finset.range k) (fun i ↦ u (T^[i] (T^[n] x))) M
      fun i _ ↦ huM _
    simpa [Finset.card_range, nsmul_eq_mul, birkhoffSum, mul_comm] using this

/-- Birkhoff sums of the unit potentials grow at most linearly with slope `Λ'`, and are
monotone in the duration (nonnegativity, G2). Blueprint node `geo:return-adjustment`. -/
theorem birkhoff_uPlus_bounds (x : X) (n m : ℕ) (hnm : n ≤ m) :
    birkhoffSum G.f G.uPlus n x ≤ birkhoffSum G.f G.uPlus m x ∧
      birkhoffSum G.f G.uPlus m x ≤ birkhoffSum G.f G.uPlus n x + G.Λ' * (m - n : ℕ) := by
  obtain ⟨-, h0, hM⟩ := G.uPlus_props
  exact birkhoffSum_bounds_of_le h0 hM x hnm

/-- Backward counterpart. Blueprint node `geo:return-adjustment`. -/
theorem birkhoff_uMinus_bounds (x : X) (n m : ℕ) (hnm : n ≤ m) :
    birkhoffSum G.finv G.uMinus n x ≤ birkhoffSum G.finv G.uMinus m x ∧
      birkhoffSum G.finv G.uMinus m x ≤ birkhoffSum G.finv G.uMinus n x + G.Λ' * (m - n : ℕ) := by
  obtain ⟨-, h0, hM⟩ := G.uMinus_props
  exact birkhoffSum_bounds_of_le h0 hM x hnm

/-! ### `geo:stopping-times` -/

omit [MetricSpace X] [CompactSpace X] in
/-- The stopping-time construction for one potential `u` with values in `[0, M]`: given an
eventual linear lower bound `lam₀ n ≤ S_n u x` for `n ≥ N₀` and a slope `lam ≤ lam₀` with
`lam (N₀ + 1) ≤ 2`, the least `n` with `S_n u x - ρ n ≥ p` tends to infinity, is at most
`2p/lam + 1`, and satisfies the two-sided bound by minimality. -/
lemma stopping_time_aux {T : X → X} {u : X → ℝ} {M : ℝ} (hu0 : ∀ y, 0 ≤ u y)
    (huM : ∀ y, u y ≤ M) (x : X) {lam₀ lam : ℝ} {N₀ : ℕ}
    (hlin : ∀ n : ℕ, N₀ ≤ n → lam₀ * n ≤ birkhoffSum T u n x)
    (hlam : 0 < lam) (hlam_le : lam ≤ lam₀) (hlam_le' : lam * (N₀ + 1) ≤ 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρlam : ρ < lam / 2) :
    ∃ np : ℕ → ℕ, Tendsto np atTop atTop ∧
      (∀ p : ℕ, (np p : ℝ) ≤ 2 * p / lam + 1) ∧
      (∀ p : ℕ, (p : ℝ) + ρ * np p ≤ birkhoffSum T u (np p) x ∧
        birkhoffSum T u (np p) x ≤ p + ρ * np p + M + ρ) := by
  classical
  have hΛ0 : 0 ≤ M := (hu0 x).trans (huM x)
  -- existence of a stopping time
  have hex : ∀ p : ℕ, ∃ n : ℕ, (p : ℝ) ≤ birkhoffSum T u n x - ρ * n := by
    intro p
    refine ⟨max N₀ ⌈2 * (p : ℝ) / lam⌉₊, ?_⟩
    have hnN : N₀ ≤ max N₀ ⌈2 * (p : ℝ) / lam⌉₊ := le_max_left _ _
    have hn2 : 2 * (p : ℝ) / lam ≤ ((max N₀ ⌈2 * (p : ℝ) / lam⌉₊ : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))
    generalize max N₀ ⌈2 * (p : ℝ) / lam⌉₊ = n at hnN hn2 ⊢
    have h1 := hlin n hnN
    have h2 : lam * n ≤ lam₀ * n := mul_le_mul_of_nonneg_right hlam_le (Nat.cast_nonneg n)
    have h3 : ρ * n ≤ lam / 2 * n := mul_le_mul_of_nonneg_right hρlam.le (Nat.cast_nonneg n)
    rw [div_le_iff₀ hlam] at hn2
    linarith
  obtain ⟨np, hnp⟩ : ∃ np : ℕ → ℕ, ∀ p : ℕ,
      ((p : ℝ) ≤ birkhoffSum T u (np p) x - ρ * np p) ∧
      (∀ m, m < np p → ¬ ((p : ℝ) ≤ birkhoffSum T u m x - ρ * m)) ∧
      (∀ m, (p : ℝ) ≤ birkhoffSum T u m x - ρ * m → np p ≤ m) :=
    ⟨fun p ↦ Nat.find (hex p), fun p ↦ ⟨Nat.find_spec (hex p),
      fun m hm ↦ Nat.find_min (hex p) hm, fun m hm ↦ Nat.find_min' (hex p) hm⟩⟩
  have hS_le : ∀ n : ℕ, birkhoffSum T u n x ≤ M * n := by
    intro n
    have := (birkhoffSum_bounds_of_le (T := T) hu0 huM x (Nat.zero_le n)).2
    simpa using this
  refine ⟨np, ?_, fun p ↦ ?_, fun p ↦ ⟨?_, ?_⟩⟩
  · -- `np → ∞`
    have hge : ∀ p : ℕ, (p : ℝ) / (M + 1) ≤ np p := by
      intro p
      rw [div_le_iff₀ (by linarith)]
      have h1 := (hnp p).1
      have h2 := hS_le (np p)
      have h3 : 0 ≤ ρ * np p := mul_nonneg hρ.le (Nat.cast_nonneg _)
      nlinarith [(Nat.cast_nonneg (np p) : (0 : ℝ) ≤ np p)]
    have ht : Tendsto (fun p : ℕ ↦ (p : ℝ) / (M + 1)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by linarith)
    exact tendsto_natCast_atTop_iff.1 (tendsto_atTop_mono hge ht)
  · -- the upper bound on `np p`
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      have h0 : np 0 = 0 := by
        apply Nat.le_zero.1
        apply (hnp 0).2.2 0
        simp
      simp [h0]
    · set w := ⌈2 * (p : ℝ) / lam⌉₊ with hw
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
      have hwN : N₀ ≤ w := by
        have h1 : (N₀ : ℝ) + 1 ≤ 2 * p / lam := by
          rw [le_div_iff₀ hlam]
          nlinarith
        have : (N₀ : ℝ) < w := by linarith [Nat.le_ceil (2 * (p : ℝ) / lam)]
        exact_mod_cast this.le
      have hwQ : (p : ℝ) ≤ birkhoffSum T u w x - ρ * w := by
        have h1 := hlin w hwN
        have h2 : lam * w ≤ lam₀ * w := mul_le_mul_of_nonneg_right hlam_le (Nat.cast_nonneg w)
        have h3 : ρ * w ≤ lam / 2 * w := mul_le_mul_of_nonneg_right hρlam.le (Nat.cast_nonneg w)
        have h4 : 2 * (p : ℝ) / lam ≤ w := Nat.le_ceil _
        rw [div_le_iff₀ hlam] at h4
        linarith
      have hle : (np p : ℝ) ≤ w := by exact_mod_cast (hnp p).2.2 w hwQ
      have hw1 : (w : ℝ) < 2 * p / lam + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
  · linarith [(hnp p).1]
  · rcases Nat.eq_zero_or_pos (np p) with h0 | h0
    · rw [h0]
      simp only [birkhoffSum_zero, Pi.zero_apply, Nat.cast_zero, mul_zero, add_zero]
      linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    · obtain ⟨k, hk⟩ : ∃ k, np p = k + 1 := ⟨np p - 1, by omega⟩
      have hfail := not_le.1 ((hnp p).2.1 k (by omega))
      have hstep := (birkhoffSum_bounds_of_le (T := T) hu0 huM x (show k ≤ k + 1 by omega)).2
      simp only [add_tsub_cancel_left, Nat.cast_one, mul_one] at hstep
      rw [hk]
      push_cast
      linarith

/-- Expansion stopping times: for `0 < ρ < λ̲/2` and every precision `p` there are least
`n⁺(p), n⁻(p) ≥ N₀` with `S_n u^±(x) - ρ n ≥ p`; they tend to infinity, are at most
`2p/λ̲ + N₀ + 1`, and by minimality `S_{n⁺(p)} u⁺(x) ≤ p + ρ n⁺(p) + Λ' + ρ` (and `≥ p + ρ n⁺(p)`).
Blueprint node `geo:stopping-times`. -/
theorem exists_stopping_times {x : X} (hx : G.PositiveRates x) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ N₀ : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ < lam / 2 →
      ∃ np nm : ℕ → ℕ,
        Tendsto np atTop atTop ∧ Tendsto nm atTop atTop ∧
        (∀ p : ℕ, N₀ ≤ np p ∧ (np p : ℝ) ≤ 2 * p / lam + N₀ + 1) ∧
        (∀ p : ℕ, N₀ ≤ nm p ∧ (nm p : ℝ) ≤ 2 * p / lam + N₀ + 1) ∧
        (∀ p : ℕ, (p : ℝ) + ρ * np p ≤ birkhoffSum G.f G.uPlus (np p) x ∧
          birkhoffSum G.f G.uPlus (np p) x ≤ p + ρ * np p + G.Λ' + ρ) ∧
        (∀ p : ℕ, (p : ℝ) + ρ * nm p ≤ birkhoffSum G.finv G.uMinus (nm p) x ∧
          birkhoffSum G.finv G.uMinus (nm p) x ≤ p + ρ * nm p + G.Λ' + ρ) := by
  obtain ⟨lam₀, hlam₀, N₀, hN₀⟩ := hx.exists_linear
  obtain ⟨-, hu0, huM⟩ := G.uPlus_props
  obtain ⟨-, hv0, hvM⟩ := G.uMinus_props
  replace huM : ∀ y, G.uPlus y ≤ G.Λ' := huM
  replace hvM : ∀ y, G.uMinus y ≤ G.Λ' := hvM
  set lam : ℝ := min lam₀ (2 / (N₀ + 1)) with hlam_def
  have hlam : 0 < lam := lt_min hlam₀ (by positivity)
  have hlam_le : lam ≤ lam₀ := min_le_left _ _
  have hlam_le' : lam * (N₀ + 1) ≤ 2 := by
    have := min_le_right lam₀ (2 / ((N₀ : ℝ) + 1))
    rwa [le_div_iff₀ (by positivity)] at this
  refine ⟨lam, hlam, 0, fun ρ hρ hρlam ↦ ?_⟩
  obtain ⟨np, hnp1, hnp2, hnp3⟩ := stopping_time_aux hu0 huM x (fun n hn ↦ (hN₀ n hn).1) hlam
    hlam_le hlam_le' hρ hρlam
  obtain ⟨nm, hnm1, hnm2, hnm3⟩ := stopping_time_aux hv0 hvM x (fun n hn ↦ (hN₀ n hn).2) hlam
    hlam_le hlam_le' hρ hρlam
  refine ⟨np, nm, hnp1, hnm1, fun p ↦ ⟨Nat.zero_le _, ?_⟩, fun p ↦ ⟨Nat.zero_le _, ?_⟩, hnp3,
    hnm3⟩
  · simpa using hnp2 p
  · simpa using hnm2 p

/-! ### `geo:return-adjustment` -/

/-- Regular endpoints with controlled loss. Fix `c > 1` with its return data `Pp, Pm, K` and
`0 < ρ < λ̲/2`. There are return times `Tp p ∈ [n⁺(p), c n⁺(p)]`, `Tm p ∈ [n⁻(p), c n⁻(p)]`
with regular endpoints such that, with `θ = 2ρ(c-1)/λ̲`, `θ' = 2(ρ + Λ'(c-1))/λ̲`,
`κ₀ = ρ(c-1)(N₀+1)`, `κ₁ = (ρ + Λ'(c-1))(N₀+1) + Λ' + ρ`:
1. `min (S_{Tp} u⁺(x) - ρ Tp, S_{Tm} u⁻(x) - ρ Tm) ≥ (1-θ) p - κ₀`
   (this is where `u^± ≥ 0` is used: `S_T u ≥ S_n u` for `T ≥ n`);
2. `S_{Tp} u⁺(x) ≤ (1+θ') p + κ₁` and likewise backward;
3. `Tp p, Tm p ≤ c (2p/λ̲ + N₀ + 1)` and both tend to infinity.
Blueprint node `geo:return-adjustment`. -/
theorem return_adjustment {x : X} (hx : G.ControlledReturns x) (hpos : G.PositiveRates x) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ N₀ : ℕ, ∀ c : ℝ, 1 < c →
      ∃ Pp Pm : Set X, IsCompact Pp ∧ Pp ⊆ G.Reg ∧ IsCompact Pm ∧ Pm ⊆ G.Reg ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < lam / 2 →
        ∃ Tp Tm : ℕ → ℕ, ∃ p₀ : ℕ,
          Tendsto Tp atTop atTop ∧ Tendsto Tm atTop atTop ∧
          (∀ p : ℕ, (Tp p : ℝ) ≤ c * (2 * p / lam + N₀ + 1) ∧
            (Tm p : ℝ) ≤ c * (2 * p / lam + N₀ + 1)) ∧
          ∀ p : ℕ, p₀ ≤ p →
            G.φ (Tp p : ℝ) x ∈ Pp ∧ G.φ (-(Tm p : ℝ)) x ∈ Pm ∧
            (1 - 2 * ρ * (c - 1) / lam) * p - ρ * (c - 1) * (N₀ + 1) ≤
              min (birkhoffSum G.f G.uPlus (Tp p) x - ρ * Tp p)
                (birkhoffSum G.finv G.uMinus (Tm p) x - ρ * Tm p) ∧
            birkhoffSum G.f G.uPlus (Tp p) x ≤
              (1 + 2 * (ρ + G.Λ' * (c - 1)) / lam) * p +
                ((ρ + G.Λ' * (c - 1)) * (N₀ + 1) + G.Λ' + ρ) ∧
            birkhoffSum G.finv G.uMinus (Tm p) x ≤
              (1 + 2 * (ρ + G.Λ' * (c - 1)) / lam) * p +
                ((ρ + G.Λ' * (c - 1)) * (N₀ + 1) + G.Λ' + ρ) := by
  obtain ⟨lam, hlam, N₀, hst⟩ := G.exists_stopping_times hpos
  obtain ⟨-, hu0, huM⟩ := G.uPlus_props
  obtain ⟨-, hv0, hvM⟩ := G.uMinus_props
  replace huM : ∀ y, G.uPlus y ≤ G.Λ' := huM
  replace hvM : ∀ y, G.uMinus y ≤ G.Λ' := hvM
  have hΛ0 : 0 ≤ G.Λ' := (hu0 x).trans (huM x)
  refine ⟨lam, hlam, N₀, fun c hc ↦ ?_⟩
  obtain ⟨Pp, Pm, hPp, hPpR, hPm, hPmR, K, hK⟩ := hx c hc
  refine ⟨Pp, Pm, hPp, hPpR, hPm, hPmR, fun ρ hρ hρlam ↦ ?_⟩
  obtain ⟨np, nm, hnp, hnm, hnpb, hnmb, hnpS, hnmS⟩ := hst ρ hρ hρlam
  -- choice of the return times (junk value `n p` below the threshold)
  have hchoose : ∀ (n : ℕ → ℕ) (σ : ℝ → ℝ) (P : Set X),
      (∀ m, K < m → ∃ T : ℕ, m ≤ T ∧ (T : ℝ) ≤ c * m ∧ G.φ (σ T) x ∈ P) →
      ∃ Tf : ℕ → ℕ, ∀ p, n p ≤ Tf p ∧ (Tf p : ℝ) ≤ c * n p ∧
        (K < n p → G.φ (σ (Tf p)) x ∈ P) := by
    intro n σ P h
    have : ∀ p, ∃ T : ℕ, n p ≤ T ∧ (T : ℝ) ≤ c * n p ∧ (K < n p → G.φ (σ T) x ∈ P) := by
      intro p
      by_cases hp : K < n p
      · obtain ⟨T, h1, h2, h3⟩ := h (n p) hp
        exact ⟨T, h1, h2, fun _ ↦ h3⟩
      · exact ⟨n p, le_rfl, le_mul_of_one_le_left (Nat.cast_nonneg _) hc.le,
          fun h' ↦ (hp h').elim⟩
    choose Tf hTf using this
    exact ⟨Tf, hTf⟩
  obtain ⟨Tp, hTp⟩ := hchoose np (fun t ↦ t) Pp fun m hm ↦ (hK m hm).1
  obtain ⟨Tm, hTm⟩ := hchoose nm (fun t ↦ -t) Pm fun m hm ↦ (hK m hm).2
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.1 (hnp.eventually_gt_atTop K)
  obtain ⟨p₂, hp₂⟩ := eventually_atTop.1 (hnm.eventually_gt_atTop K)
  refine ⟨Tp, Tm, max p₁ p₂, tendsto_atTop_mono (fun p ↦ (hTp p).1) hnp,
    tendsto_atTop_mono (fun p ↦ (hTm p).1) hnm, fun p ↦ ⟨?_, ?_⟩, fun p hp ↦ ?_⟩
  · exact (hTp p).2.1.trans (mul_le_mul_of_nonneg_left (hnpb p).2 (by linarith))
  · exact (hTm p).2.1.trans (mul_le_mul_of_nonneg_left (hnmb p).2 (by linarith))
  · have hKp : K < np p := hp₁ p (le_of_max_le_left hp)
    have hKm : K < nm p := hp₂ p (le_of_max_le_right hp)
    obtain ⟨hn1, hn2, hn3⟩ := hTp p
    obtain ⟨hm1, hm2, hm3⟩ := hTm p
    obtain ⟨hS1, hS2⟩ := hnpS p
    obtain ⟨hR1, hR2⟩ := hnmS p
    obtain ⟨hb1, hb2⟩ := birkhoffSum_bounds_of_le (T := G.f) hu0 huM x hn1
    obtain ⟨hc1, hc2⟩ := birkhoffSum_bounds_of_le (T := G.finv) hv0 hvM x hm1
    have hnpb' := (hnpb p).2
    have hnmb' := (hnmb p).2
    have hc1' : 0 ≤ c - 1 := by linarith
    rw [Nat.cast_sub hn1] at hb2
    rw [Nat.cast_sub hm1] at hc2
    have hρc : 0 ≤ ρ * (c - 1) := mul_nonneg hρ.le hc1'
    have hΛc : 0 ≤ ρ + G.Λ' * (c - 1) := add_nonneg hρ.le (mul_nonneg hΛ0 hc1')
    have e1 : ρ * ((Tp p : ℝ) - np p) ≤ ρ * ((c - 1) * np p) :=
      mul_le_mul_of_nonneg_left (by linarith) hρ.le
    have e2 : ρ * ((Tm p : ℝ) - nm p) ≤ ρ * ((c - 1) * nm p) :=
      mul_le_mul_of_nonneg_left (by linarith) hρ.le
    have e3 : ρ * (c - 1) * np p ≤ ρ * (c - 1) * (2 * p / lam + N₀ + 1) :=
      mul_le_mul_of_nonneg_left hnpb' hρc
    have e4 : ρ * (c - 1) * nm p ≤ ρ * (c - 1) * (2 * p / lam + N₀ + 1) :=
      mul_le_mul_of_nonneg_left hnmb' hρc
    have e5 : G.Λ' * ((Tp p : ℝ) - np p) ≤ G.Λ' * ((c - 1) * np p) :=
      mul_le_mul_of_nonneg_left (by linarith) hΛ0
    have e6 : G.Λ' * ((Tm p : ℝ) - nm p) ≤ G.Λ' * ((c - 1) * nm p) :=
      mul_le_mul_of_nonneg_left (by linarith) hΛ0
    have e7 : (ρ + G.Λ' * (c - 1)) * np p ≤ (ρ + G.Λ' * (c - 1)) * (2 * p / lam + N₀ + 1) :=
      mul_le_mul_of_nonneg_left hnpb' hΛc
    have e8 : (ρ + G.Λ' * (c - 1)) * nm p ≤ (ρ + G.Λ' * (c - 1)) * (2 * p / lam + N₀ + 1) :=
      mul_le_mul_of_nonneg_left hnmb' hΛc
    have eq1 : (1 - 2 * ρ * (c - 1) / lam) * p - ρ * (c - 1) * (N₀ + 1) =
        p - ρ * (c - 1) * (2 * p / lam + N₀ + 1) := by ring
    have eq2 : (1 + 2 * (ρ + G.Λ' * (c - 1)) / lam) * p +
        ((ρ + G.Λ' * (c - 1)) * (N₀ + 1) + G.Λ' + ρ) =
        p + (ρ + G.Λ' * (c - 1)) * (2 * p / lam + N₀ + 1) + G.Λ' + ρ := by ring
    refine ⟨hn3 hKp, hm3 hKm, le_min ?_ ?_, ?_, ?_⟩
    · rw [eq1]; linarith
    · rw [eq1]; linarith
    · rw [eq2]; linarith
    · rw [eq2]; linarith

end GeodesicReconstructionData

end Kolmogorov.PointToSet
