/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import Mathlib.Dynamics.Flow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import KolmogorovMathlib.PointToSet.Dynamics.PointwiseQuantities
import KolmogorovMathlib.PointToSet.BSDimension.Defs
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.PointToSet.Dynamics.BirkhoffComputability
import KolmogorovMathlib.Oracle.Closure

/-!
# Flow-to-map interface (geodesic blueprint, Chapter A)

The nodes `geo:flow-data`, `geo:bowen-flow-compare`, `geo:unit-potentials`,
`geo:orbit-complexity` and `geo:bs-denominator-swap` of `geodesic_upper_bound_blueprint.md`;
the node `geo:orbit-extension` is in `FlowInterface/OrbitExtension.lean`.

The point-to-set library is discrete-time: Bowen balls `bowenBall T n x ε` observe the
iterates `T^[k] x` for `k < n` and `birkhoffSum T u n x = ∑_{k<n} u (T^[k] x)`. A continuous
flow `φ : Flow ℝ X` enters only through its time-one map `f := φ 1` and its inverse
`φ (-1)`, with unit-time integrated potentials in bits (base `2`, matching `dyadicRadius`
and `Real.logb 2` everywhere in the library). Nothing in this file mentions geodesic flows:
the inputs are a flow with a Lipschitz bound on `|s| ≤ 1` and continuous rate functions.

Conventions: `L` is the Lipschitz constant of `φ s` for `|s| ≤ 1`, `V` the speed bound
`dist (φ s y) y ≤ V |s|`; both are fields of `FlowData` (blueprint D1, D2, D7).

Signatures follow the API of `PointToSet/Dynamics/BowenBalls.lean`, `PointwiseQuantities.lean`
and `ComputableMetric/Presentation.lean`.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-! ### `geo:flow-data`: standing analytic data -/

/-- A continuous flow on a compact metric space together with a Lipschitz constant and a
speed bound valid for times `|s| ≤ 1`. The time-one map and its inverse are the discrete
dynamics seen by the point-to-set library. Blueprint node `geo:flow-data`. -/
structure FlowData (X : Type*) [MetricSpace X] [CompactSpace X] where
  /-- The flow. -/
  φ : Flow ℝ X
  /-- Lipschitz constant of `φ s` for `|s| ≤ 1`. -/
  L : ℝ
  /-- The Lipschitz constant is at least one, so it can be used as a multiplier freely. -/
  one_le_L : 1 ≤ L
  /-- Uniform Lipschitz bound on unit time intervals. -/
  lipschitz_unit : ∀ s : ℝ, |s| ≤ 1 → ∀ x y : X, dist (φ s x) (φ s y) ≤ L * dist x y
  /-- Speed bound of the flow, used only to restore the flow coordinate. -/
  V : ℝ
  /-- The speed bound is nonnegative. -/
  V_nonneg : 0 ≤ V
  /-- Points move at most at speed `V` on unit time intervals. -/
  speed_unit : ∀ s : ℝ, |s| ≤ 1 → ∀ y : X, dist (φ s y) y ≤ V * |s|

section flowData

variable [CompactSpace X]

namespace FlowData

variable (D : FlowData X)

/-- The time-one map. Blueprint node `geo:flow-data`. -/
def f : X → X := D.φ 1

/-- The time-minus-one map, inverse to `f`. Blueprint node `geo:flow-data`. -/
def finv : X → X := D.φ (-1)

/-- Iterates of the time-one map are integer times of the flow.
Blueprint node `geo:flow-data`. -/
theorem iterate_f (n : ℕ) : D.f^[n] = D.φ (n : ℝ) := by
  induction n with
  | zero => simp [Flow.map_zero]
  | succ k ih =>
    funext x
    rw [Function.iterate_succ_apply', ih, Nat.cast_succ, add_comm, Flow.map_add]
    rfl

/-- Iterates of the inverse time-one map are negative integer times of the flow.
Blueprint node `geo:flow-data`. -/
theorem iterate_finv (n : ℕ) : D.finv^[n] = D.φ (-(n : ℝ)) := by
  induction n with
  | zero => simp [Flow.map_zero]
  | succ k ih =>
    funext x
    rw [Function.iterate_succ_apply', ih, Nat.cast_succ, neg_add, add_comm, Flow.map_add]
    rfl

/-- `f` and `finv` are mutually inverse. -/
theorem finv_f (x : X) : D.finv (D.f x) = x := by
  change D.φ (-1) (D.φ 1 x) = x
  rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]

/-- `f` and `finv` are mutually inverse. -/
theorem f_finv (x : X) : D.f (D.finv x) = x := by
  change D.φ 1 (D.φ (-1) x) = x
  rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]

/-- The time-one map is continuous. -/
theorem continuous_f : Continuous D.f := by
  exact D.φ.continuous_toFun 1

/-- The inverse time-one map is continuous. -/
theorem continuous_finv : Continuous D.finv := by
  exact D.φ.continuous_toFun (-1)

/-- The time-one map is Lipschitz with constant `L`. -/
theorem dist_f_le (x y : X) : dist (D.f x) (D.f y) ≤ D.L * dist x y := by
  exact D.lipschitz_unit 1 (by simp) x y

/-- The inverse time-one map is Lipschitz with constant `L`. -/
theorem dist_finv_le (x y : X) : dist (D.finv x) (D.finv y) ≤ D.L * dist x y := by
  exact D.lipschitz_unit (-1) (by simp) x y

/-! ### `geo:bowen-flow-compare`: discrete Bowen balls control continuous orbits -/

/-- A point of the discrete Bowen ball of order `n + 1` shadows the continuous forward
orbit on `[0, n]` within `L ε`. Blueprint node `geo:bowen-flow-compare`. -/
theorem dist_flow_lt_of_mem_bowenBall {x y : X} {n : ℕ} {ε : ℝ}
    (hy : y ∈ bowenBall D.f (n + 1) x ε) {t : ℝ} (ht0 : 0 ≤ t) (htn : t ≤ n) :
    dist (D.φ t x) (D.φ t y) < D.L * ε := by
  set k : ℕ := ⌊t⌋₊ with hk
  have hkn : k < n + 1 := Nat.lt_succ_of_le (Nat.floor_le_of_le htn)
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht0
  have htk : t < k + 1 := Nat.lt_floor_add_one t
  have hs : |t - k| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hclose : dist (D.φ (k : ℝ) x) (D.φ (k : ℝ) y) < ε := by
    rw [← D.iterate_f]
    exact (mem_bowenBall_iff.1 hy) k hkn
  have ht : t = (t - k) + k := by ring
  calc dist (D.φ t x) (D.φ t y) = dist (D.φ (t - k) (D.φ k x)) (D.φ (t - k) (D.φ k y)) := by
        rw [ht, Flow.map_add, Flow.map_add]; ring_nf
    _ ≤ D.L * dist (D.φ (k : ℝ) x) (D.φ (k : ℝ) y) := D.lipschitz_unit _ hs _ _
    _ < D.L * ε := mul_lt_mul_of_pos_left hclose (by linarith [D.one_le_L])

/-- Backward version: a point of the discrete `finv`-Bowen ball of order `n + 1` shadows
the continuous orbit on `[-n, 0]` within `L ε`. Blueprint node `geo:bowen-flow-compare`. -/
theorem dist_flow_lt_of_mem_bowenBall_finv {x y : X} {n : ℕ} {ε : ℝ}
    (hy : y ∈ bowenBall D.finv (n + 1) x ε) {t : ℝ} (htn : -(n : ℝ) ≤ t) (ht0 : t ≤ 0) :
    dist (D.φ t x) (D.φ t y) < D.L * ε := by
  set k : ℕ := ⌊-t⌋₊ with hk
  have hkn : k < n + 1 := Nat.lt_succ_of_le (Nat.floor_le_of_le (by linarith))
  have hkt : (k : ℝ) ≤ -t := Nat.floor_le (by linarith)
  have htk : -t < k + 1 := Nat.lt_floor_add_one (-t)
  have hs : |-(-t - k)| ≤ 1 := by rw [abs_neg, abs_le]; constructor <;> linarith
  have hclose : dist (D.φ (-(k : ℝ)) x) (D.φ (-(k : ℝ)) y) < ε := by
    rw [← D.iterate_finv]
    exact (mem_bowenBall_iff.1 hy) k hkn
  have ht : t = -(-t - k) + -(k : ℝ) := by ring
  calc dist (D.φ t x) (D.φ t y)
      = dist (D.φ (-(-t - k)) (D.φ (-(k : ℝ)) x)) (D.φ (-(-t - k)) (D.φ (-(k : ℝ)) y)) := by
        rw [ht, Flow.map_add, Flow.map_add]; ring_nf
    _ ≤ D.L * dist (D.φ (-(k : ℝ)) x) (D.φ (-(k : ℝ)) y) := D.lipschitz_unit _ hs _ _
    _ < D.L * ε := mul_lt_mul_of_pos_left hclose (by linarith [D.one_le_L])

/-- Conversely, continuous `ε`-shadowing on `[0, n]` lies in the discrete Bowen ball of
order `n + 1`. Blueprint node `geo:bowen-flow-compare`. -/
theorem mem_bowenBall_of_dist_flow_lt {x y : X} {n : ℕ} {ε : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ n → dist (D.φ t x) (D.φ t y) < ε) :
    y ∈ bowenBall D.f (n + 1) x ε := by
  rw [mem_bowenBall_iff]
  intro k hk
  rw [D.iterate_f]
  exact h k (Nat.cast_nonneg k) (by exact_mod_cast Nat.lt_succ_iff.mp hk)

/-- Backward converse. Blueprint node `geo:bowen-flow-compare`. -/
theorem mem_bowenBall_finv_of_dist_flow_lt {x y : X} {n : ℕ} {ε : ℝ}
    (h : ∀ t : ℝ, -(n : ℝ) ≤ t → t ≤ 0 → dist (D.φ t x) (D.φ t y) < ε) :
    y ∈ bowenBall D.finv (n + 1) x ε := by
  rw [mem_bowenBall_iff]
  intro k hk
  rw [D.iterate_finv]
  exact h (-(k : ℝ)) (neg_le_neg (by exact_mod_cast Nat.lt_succ_iff.mp hk)) (by simp)

/-! ### `geo:unit-potentials`: unit-time integrated rates in bits -/

/-- The forward unit-time integrated rate, in bits:
`u⁺ x = (log 2)⁻¹ ∫₀¹ lam (φ τ x) dτ`. Blueprint node `geo:unit-potentials`. -/
noncomputable def unitPotential (lam : X → ℝ) (x : X) : ℝ :=
  (Real.log 2)⁻¹ * ∫ τ in (0 : ℝ)..1, lam (D.φ τ x)

/-- The backward unit-time integrated rate, in bits:
`u⁻ x = (log 2)⁻¹ ∫₀¹ lam (φ (-τ) x) dτ`. Blueprint node `geo:unit-potentials`. -/
noncomputable def unitPotentialBackward (lam : X → ℝ) (x : X) : ℝ :=
  (Real.log 2)⁻¹ * ∫ τ in (0 : ℝ)..1, lam (D.φ (-τ) x)

/-- The continuous-time accumulated rate `S(t, x) = ∫₀ᵗ lam (φ τ x) dτ` (natural units).
Blueprint node `geo:unit-potentials`. -/
noncomputable def accumulatedRate (lam : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  ∫ τ in (0 : ℝ)..t, lam (D.φ τ x)

/-- The backward continuous-time accumulated rate `∫₀ᵗ lam (φ (-τ) x) dτ`.
Blueprint node `geo:unit-potentials`. -/
noncomputable def accumulatedRateBackward (lam : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  ∫ τ in (0 : ℝ)..t, lam (D.φ (-τ) x)

section rates

variable {lam : X → ℝ} (hlam : Continuous lam) {Λ : ℝ} (hlam0 : ∀ x, 0 ≤ lam x)
  (hlamΛ : ∀ x, lam x ≤ Λ)

include hlam in
/-- The unit potential of a continuous rate is continuous.
Blueprint node `geo:unit-potentials` (i). -/
theorem continuous_unitPotential : Continuous (D.unitPotential lam) := by
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x τ ↦ lam (D.φ τ x)) (hlam.comp (D.φ.continuous continuous_snd continuous_fst)) 0 1

include hlam in
/-- The unit potential of a continuous rate is uniformly continuous (compactness).
Blueprint node `geo:unit-potentials` (i). -/
theorem uniformContinuous_unitPotential : UniformContinuous (D.unitPotential lam) := by
  exact CompactSpace.uniformContinuous_of_continuous (D.continuous_unitPotential hlam)

include hlam in
/-- The backward unit potential of a continuous rate is continuous.
Blueprint node `geo:unit-potentials` (i). -/
theorem continuous_unitPotentialBackward : Continuous (D.unitPotentialBackward lam) := by
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x τ ↦ lam (D.φ (-τ) x))
    (hlam.comp (D.φ.continuous continuous_snd.neg continuous_fst)) 0 1

include hlam in
/-- The backward unit potential of a continuous rate is uniformly continuous.
Blueprint node `geo:unit-potentials` (i). -/
theorem uniformContinuous_unitPotentialBackward :
    UniformContinuous (D.unitPotentialBackward lam) := by
  exact CompactSpace.uniformContinuous_of_continuous (D.continuous_unitPotentialBackward hlam)

include hlam0 in
/-- Nonnegative rates give nonnegative unit potentials. This is the nonnegativity used in
`geo:return-adjustment`. Blueprint node `geo:unit-potentials` (i). -/
theorem unitPotential_nonneg (x : X) : 0 ≤ D.unitPotential lam x := by
  exact mul_nonneg (inv_nonneg.mpr (Real.log_nonneg one_le_two))
    (intervalIntegral.integral_nonneg zero_le_one fun τ _ ↦ hlam0 _)

include hlam hlamΛ in
/-- Bounded rates give unit potentials bounded by `Λ / log 2`.
Blueprint node `geo:unit-potentials` (i). -/
theorem unitPotential_le (x : X) : D.unitPotential lam x ≤ Λ / Real.log 2 := by
  unfold unitPotential
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.log_nonneg one_le_two))
  have hint : IntervalIntegrable (fun τ ↦ lam (D.φ τ x)) MeasureTheory.volume 0 1 :=
    (hlam.comp (D.φ.continuous continuous_id continuous_const)).intervalIntegrable 0 1
  calc ∫ τ in (0 : ℝ)..1, lam (D.φ τ x) ≤ ∫ τ in (0 : ℝ)..1, Λ :=
        intervalIntegral.integral_mono_on zero_le_one hint intervalIntegrable_const
          (fun τ _ ↦ hlamΛ _)
    _ = Λ := by simp

include hlam0 in
/-- Backward nonnegativity. Blueprint node `geo:unit-potentials` (i). -/
theorem unitPotentialBackward_nonneg (x : X) : 0 ≤ D.unitPotentialBackward lam x := by
  exact mul_nonneg (inv_nonneg.mpr (Real.log_nonneg one_le_two))
    (intervalIntegral.integral_nonneg zero_le_one fun τ _ ↦ hlam0 _)

include hlam hlamΛ in
/-- Backward upper bound. Blueprint node `geo:unit-potentials` (i). -/
theorem unitPotentialBackward_le (x : X) : D.unitPotentialBackward lam x ≤ Λ / Real.log 2 := by
  unfold unitPotentialBackward
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.log_nonneg one_le_two))
  have hint : IntervalIntegrable (fun τ ↦ lam (D.φ (-τ) x)) MeasureTheory.volume 0 1 :=
    (hlam.comp (D.φ.continuous continuous_neg continuous_const)).intervalIntegrable 0 1
  calc ∫ τ in (0 : ℝ)..1, lam (D.φ (-τ) x) ≤ ∫ τ in (0 : ℝ)..1, Λ :=
        intervalIntegral.integral_mono_on zero_le_one hint intervalIntegrable_const
          (fun τ _ ↦ hlamΛ _)
    _ = Λ := by simp

include hlam in
/-- Birkhoff sums of the unit potential along the time-one map are the accumulated rate
over `[0, n]`, in bits: `S_n u⁺(x) = (log 2)⁻¹ ∫₀ⁿ lam (φ τ x) dτ`.
Blueprint node `geo:unit-potentials` (ii). -/
theorem birkhoffSum_unitPotential (n : ℕ) (x : X) :
    birkhoffSum D.f (D.unitPotential lam) n x =
      (Real.log 2)⁻¹ * D.accumulatedRate lam (n : ℝ) x := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun τ ↦ lam (D.φ τ x)) MeasureTheory.volume a b :=
    fun a b ↦ (hlam.comp (D.φ.continuous continuous_id continuous_const)).intervalIntegrable a b
  induction n with
  | zero => simp [accumulatedRate]
  | succ k ih =>
    rw [birkhoffSum_succ_apply, ih, D.iterate_f]
    unfold unitPotential accumulatedRate
    rw [← mul_add]
    congr 1
    have h1 : (fun τ ↦ lam (D.φ τ (D.φ (k : ℝ) x))) = fun τ ↦ lam (D.φ (τ + k) x) := by
      funext τ; rw [Flow.map_add]
    rw [h1, intervalIntegral.integral_comp_add_right (fun τ ↦ lam (D.φ τ x)) (k : ℝ), zero_add,
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _), Nat.cast_succ,
      add_comm (1 : ℝ) (k : ℝ)]

include hlam in
/-- Backward Birkhoff sums along `finv` are the backward accumulated rate over `[0, n]`.
Blueprint node `geo:unit-potentials` (ii). -/
theorem birkhoffSum_unitPotentialBackward (n : ℕ) (x : X) :
    birkhoffSum D.finv (D.unitPotentialBackward lam) n x =
      (Real.log 2)⁻¹ * D.accumulatedRateBackward lam (n : ℝ) x := by
  have hint : ∀ a b : ℝ,
      IntervalIntegrable (fun τ ↦ lam (D.φ (-τ) x)) MeasureTheory.volume a b :=
    fun a b ↦ (hlam.comp (D.φ.continuous continuous_neg continuous_const)).intervalIntegrable a b
  induction n with
  | zero => simp [accumulatedRateBackward]
  | succ k ih =>
    rw [birkhoffSum_succ_apply, ih, D.iterate_finv]
    unfold unitPotentialBackward accumulatedRateBackward
    rw [← mul_add]
    congr 1
    have h1 : (fun τ ↦ lam (D.φ (-τ) (D.φ (-(k : ℝ)) x))) = fun τ ↦ lam (D.φ (-(τ + k)) x) := by
      funext τ; rw [← Flow.map_add, neg_add]
    rw [h1, intervalIntegral.integral_comp_add_right (fun τ ↦ lam (D.φ (-τ) x)) (k : ℝ), zero_add,
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _), Nat.cast_succ,
      add_comm (1 : ℝ) (k : ℝ)]

include hlam in
/-- Natural exponential scales of the drafts equal dyadic scales of the library:
`exp (-(S(n,x) - ρ n)) = 2 ^ (-(S_n u⁺(x) - ρ' n))` with `ρ' = ρ / log 2`.
Blueprint node `geo:unit-potentials`, decision D2. -/
theorem exp_neg_accumulatedRate_eq_two_zpow (n : ℕ) (x : X) (ρ : ℝ) :
    Real.exp (-(D.accumulatedRate lam (n : ℝ) x - ρ * (n : ℝ))) =
      (2 : ℝ) ^ (-(birkhoffSum D.f (D.unitPotential lam) n x - (ρ / Real.log 2) * (n : ℝ))) := by
  rw [D.birkhoffSum_unitPotential hlam, Real.rpow_def_of_pos two_pos]
  congr 1
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp

include hlam hlam0 hlamΛ in
/-- Continuous and integer-time accumulated rates differ by at most `Λ` on `[n, n + 1]`.
Blueprint node `geo:unit-potentials` (iii). -/
theorem abs_accumulatedRate_sub_le (x : X) {t : ℝ} {n : ℕ} (hn : (n : ℝ) ≤ t)
    (ht : t ≤ (n : ℝ) + 1) :
    |D.accumulatedRate lam t x - D.accumulatedRate lam (n : ℝ) x| ≤ Λ := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun τ ↦ lam (D.φ τ x)) MeasureTheory.volume a b :=
    fun a b ↦ (hlam.comp (D.φ.continuous continuous_id continuous_const)).intervalIntegrable a b
  have hΛ : 0 ≤ Λ := (hlam0 x).trans (hlamΛ x)
  unfold accumulatedRate
  rw [intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (n : ℝ)) (b := t)
    (f := fun τ ↦ lam (D.φ τ x)) (C := Λ) fun τ _ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hlam0 _)]; exact hlamΛ _
  rw [Real.norm_eq_abs] at hb
  refine hb.trans ?_
  rw [abs_of_nonneg (by linarith)]
  nlinarith

include hlam hlam0 hlamΛ in
/-- Positivity of the lower Birkhoff average of the unit potential is equivalent to an
eventual linear lower bound on the continuous accumulated rate.
Blueprint node `geo:unit-potentials` (iii) and `geo:positive-rates`. -/
theorem lowerBirkhoffAverage_unitPotential_pos_iff (x : X) :
    0 < lowerBirkhoffAverage D.f (D.unitPotential lam) x ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop, c * t ≤ D.accumulatedRate lam t x := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hΛ : 0 ≤ Λ := (hlam0 x).trans (hlamΛ x)
  constructor
  · intro hx
    obtain ⟨r, hr, hrx⟩ := EReal.exists_between_coe_real hx
    have hrpos : 0 < r := EReal.coe_pos.mp hr
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hrx)
    have hapos : 0 < r * Real.log 2 := mul_pos hrpos hlog
    refine ⟨r * Real.log 2 / 2, half_pos hapos, ?_⟩
    rw [eventually_atTop]
    refine ⟨max ((N₀ : ℝ) + 1) (2 * (r * Real.log 2 + Λ) / (r * Real.log 2)), fun t ht ↦ ?_⟩
    have ht1 : (N₀ : ℝ) + 1 ≤ t := (le_max_left _ _).trans ht
    have ht2 : 2 * (r * Real.log 2 + Λ) ≤ t * (r * Real.log 2) :=
      (div_le_iff₀ hapos).mp ((le_max_right _ _).trans ht)
    have ht0 : 0 ≤ t := by linarith [Nat.cast_nonneg (α := ℝ) N₀]
    have hnt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
    have htn : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have hN₀n : N₀ + 1 ≤ ⌊t⌋₊ := Nat.le_floor (by push_cast; exact ht1)
    have hnpos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (show 0 < ⌊t⌋₊ by omega)
    have hS := (abs_le.mp (D.abs_accumulatedRate_sub_le hlam hlam0 hlamΛ x hnt htn.le)).1
    have hbs := EReal.coe_lt_coe_iff.mp (hN₀ ⌊t⌋₊ (by omega))
    rw [D.birkhoffSum_unitPotential hlam, lt_div_iff₀ hnpos] at hbs
    have hSn : r * Real.log 2 * ⌊t⌋₊ < D.accumulatedRate lam (⌊t⌋₊ : ℝ) x := by
      have h1 := mul_lt_mul_of_pos_left hbs hlog
      have h2 : Real.log 2 * ((Real.log 2)⁻¹ * D.accumulatedRate lam (⌊t⌋₊ : ℝ) x) =
          D.accumulatedRate lam (⌊t⌋₊ : ℝ) x := by field_simp
      linarith
    have hat : r * Real.log 2 * (t - 1) < r * Real.log 2 * ⌊t⌋₊ :=
      mul_lt_mul_of_pos_left (by linarith) hapos
    linarith
  · rintro ⟨c, hc, hct⟩
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hct
    have hpos : (0 : EReal) < ((c / Real.log 2 : ℝ) : EReal) :=
      EReal.coe_pos.mpr (div_pos hc hlog)
    refine lt_of_lt_of_le hpos (le_liminf_of_le (by isBoundedDefault) ?_)
    rw [eventually_atTop]
    refine ⟨max ⌈T₀⌉₊ 1, fun n hn ↦ ?_⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
    have hnT : T₀ ≤ n := (Nat.le_ceil T₀).trans (by exact_mod_cast (le_max_left _ _).trans hn)
    rw [EReal.coe_le_coe_iff, D.birkhoffSum_unitPotential hlam, le_div_iff₀ (by linarith)]
    calc c / Real.log 2 * n = (Real.log 2)⁻¹ * (c * n) := by ring
      _ ≤ (Real.log 2)⁻¹ * D.accumulatedRate lam n x :=
          mul_le_mul_of_nonneg_left (hT₀ n hnT) (inv_nonneg.mpr hlog.le)

/-- Positivity of the lower Birkhoff average yields the eventual linear lower bound on
integer-time Birkhoff sums used throughout Chapter I.
Blueprint node `geo:positive-rates`. -/
theorem exists_linear_lower_bound_of_pos (x : X)
    (hx : 0 < lowerBirkhoffAverage D.f (D.unitPotential lam) x) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) ≤ birkhoffSum D.f (D.unitPotential lam) n x := by
  obtain ⟨r, hr, hrx⟩ := EReal.exists_between_coe_real hx
  have hrpos : 0 < r := EReal.coe_pos.mp hr
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hrx)
  refine ⟨r, hrpos, max N₀ 1, fun n hn ↦ ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (le_max_right N₀ 1).trans hn
  have h := EReal.coe_lt_coe_iff.mp (hN₀ n ((le_max_left N₀ 1).trans hn))
  exact ((lt_div_iff₀ hnpos).mp h).le

end rates

end FlowData

end flowData

/-! ### `geo:orbit-complexity`: finite orbit complexity -/

/- The finite orbit complexity `K^A_n(x, T, ε)` is already defined by the library:
`orbitComplexityNat P T A x n ε : ℕ∞` (an `ENat` infimum of `oracleNatComplexity A i` over
ideal `i` with `P.ι i ∈ bowenBall T n x ε`) and its natural shadow `orbitComplexityNat`
(`PointToSet/Pressure/Defs.lean`, blueprint node `pressure:entropy-definitions`). This
section only records the properties that Chapter I needs, for the natural shadow.
Blueprint node `geo:orbit-complexity`. -/

section orbitComplexityNat

variable (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X)

/-- Positive-radius Bowen balls contain an ideal point, so the orbit complexity is attained.
Blueprint node `geo:orbit-complexity`. -/
theorem orbitComplexityNat_attained (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ i, P.ι i ∈ bowenBall T n x ε ∧ oracleNatComplexity A i = orbitComplexityNat P T A x n ε := by
  let S : Set ℕ := {i | P.ι i ∈ bowenBall T n x ε}
  have hS : S.Nonempty := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact ⟨0, by simp [S, hn, bowen_ball_dense_zero]⟩
    · exact bowen_ball_dense P T hT x n hn ε hε
  have hmem := Function.argminOn_mem (oracleNatComplexity A) S hS
  refine ⟨Function.argminOn (oracleNatComplexity A) S hS, hmem, ?_⟩
  have h : orbitComplexity P T A x n ε =
      (oracleNatComplexity A (Function.argminOn (oracleNatComplexity A) S hS) : ℕ∞) := by
    refine le_antisymm (iInf₂_le _ hmem) (le_iInf₂ fun j hj ↦ ?_)
    exact_mod_cast Function.argminOn_le (oracleNatComplexity A) S hj
  rw [orbitComplexityNat, h, ENat.toNat_natCast]

/-- The orbit complexity is a lower bound for the complexity of every ideal point in the
Bowen ball. Blueprint node `geo:orbit-complexity`. -/
theorem orbitComplexityNat_le {n : ℕ} {ε : ℝ} {i : ℕ} (hi : P.ι i ∈ bowenBall T n x ε) :
    orbitComplexityNat P T A x n ε ≤ oracleNatComplexity A i := by
  exact ENat.toNat_le_of_le_natCast (iInf₂_le i hi)

/-- Observing more times can only increase the orbit complexity.
Blueprint node `geo:orbit-complexity`. -/
theorem orbitComplexityNat_mono_order (hT : Continuous T) {ε : ℝ} (hε : 0 < ε) :
    Monotone fun n ↦ orbitComplexityNat P T A x n ε := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  obtain ⟨i, hi, hiK⟩ := orbitComplexityNat_attained P T A x hT (n + 1) hε
  rw [← hiK]
  exact orbitComplexityNat_le P T A x (bowen_ball_dense_succ T n x ε hi)

/-- Shrinking the radius can only increase the orbit complexity.
Blueprint node `geo:orbit-complexity`. -/
theorem orbitComplexityNat_anti_radius (hT : Continuous T) (n : ℕ) {ε₁ ε₂ : ℝ} (h0 : 0 < ε₁)
    (h : ε₁ ≤ ε₂) :
    orbitComplexityNat P T A x n ε₂ ≤ orbitComplexityNat P T A x n ε₁ := by
  obtain ⟨i, hi, hiK⟩ := orbitComplexityNat_attained P T A x hT n h0
  rw [← hiK]
  exact orbitComplexityNat_le P T A x (bowenBall_subset_of_le T n x h hi)

/-- Shifting the order by one does not change lower or upper time limits of normalized
orbit complexities (analogue of `pointwiseDimensionEqBS_order_shift`).
Blueprint node `geo:orbit-complexity`, blueprint check 2. -/
theorem orbitComplexityNat_timeLimit_order_shift (ε : ℝ) (g : ℕ → ℝ≥0∞) (σ : LimitSide) :
    σ.timeLimit (fun n ↦ (orbitComplexityNat P T A x (n + 1) ε : ℝ≥0∞) / g (n + 1)) =
      σ.timeLimit (fun n ↦ (orbitComplexityNat P T A x n ε : ℝ≥0∞) / g n) := by
  cases σ
  · exact liminf_nat_add (fun n ↦ (orbitComplexityNat P T A x n ε : ℝ≥0∞) / g n) 1
  · exact limsup_nat_add (fun n ↦ (orbitComplexityNat P T A x n ε : ℝ≥0∞) / g n) 1

/-- Oracle monotonicity: a stronger oracle lowers orbit complexity by a uniform constant.
Blueprint node `geo:orbit-complexity`. -/
theorem orbitComplexityNat_mono_oracle (hT : Continuous T) {B : Set ℕ}
    (hAB : charOracle A ≤ᵀ charOracle B) :
    ∃ c : ℕ, ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      orbitComplexityNat P T B x n ε ≤ orbitComplexityNat P T A x n ε + c := by
  obtain ⟨c, hc⟩ := oracle_monotonicity A B hAB
  refine ⟨c, fun n ε hε ↦ ?_⟩
  obtain ⟨i, hi, hiK⟩ := orbitComplexityNat_attained P T A x hT n hε
  rw [← hiK]
  exact (orbitComplexityNat_le P T B x hi).trans (hc _)

/-- The finite-scale BS cost is bounded by the orbit complexity divided by the Birkhoff sum
of the realizing ideal point. Blueprint node `geo:orbit-complexity`. -/
theorem finiteScaleBSCost_le_orbitComplexityNat (hT : Continuous T) (u : X → ℝ) {n : ℕ}
    (hn : n ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ i, P.ι i ∈ bowenBall T n x ε → 0 < birkhoffSum T u n (P.ι i)) :
    ∃ i, P.ι i ∈ bowenBall T n x ε ∧
      oracleNatComplexity A i = orbitComplexityNat P T A x n ε ∧
      finiteScaleBSCost P T u A x n ε ≤
        (orbitComplexityNat P T A x n ε : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i)) := by
  obtain ⟨i, hi, hiK⟩ := orbitComplexityNat_attained P T A x hT n hε
  refine ⟨i, hi, hiK, ?_⟩
  rw [← hiK]
  exact finiteScaleBSCost_le_div P T u A hn hi (hpos i hi)

end orbitComplexityNat

/-! ### `geo:bs-denominator-swap`: center versus ideal-point denominators -/

/-- The normalized orbit complexity with the Birkhoff denominator evaluated at the center
`x` rather than at the realizing ideal point. Blueprint node `geo:bs-denominator-swap`. -/
noncomputable def centeredBSCost (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ)
    (x : X) (n : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  (orbitComplexityNat P T A x n ε : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n x)

section denominatorSwap

variable (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (A : Set ℕ) (x : X)
  (hx : 0 < lowerBirkhoffAverage T u x)

include hT hu hx in
/-- On the positive-average locus, for every sufficiently small dyadic radius, the centered
cost and the library's finite-scale BS cost have time limits within a multiplicative factor
`1 + η p`, with `η p → 0` (`η p = 2 ω_p / λ̲` in the blueprint).
Blueprint node `geo:bs-denominator-swap`. -/
theorem centeredBSCost_timeLimit_le (σ : LimitSide) :
    ∃ p₀ : ℕ, ∃ η : ℕ → ℝ≥0∞, Tendsto η atTop (𝓝 0) ∧ ∀ p : ℕ, p₀ ≤ p →
      σ.timeLimit (fun n ↦ centeredBSCost P T u A x n (dyadicRadius p)) ≤
        (1 + η p) * σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) := by
  obtain ⟨r, hr, hrx⟩ := EReal.exists_between_coe_real hx
  have hrpos : 0 < r := EReal.coe_pos.mp hr
  obtain ⟨ω, hωpos, hωzero, pω, hω⟩ := small_scale_oscillation u hu
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.mp (hωzero.eventually (gt_mem_nhds (half_pos hrpos)))
  have hρpos : 0 < r / 2 := half_pos hrpos
  refine ⟨max pω p₁, fun p ↦ ENNReal.ofReal (ω p / (r / 2)), ?_, fun p hp ↦ ?_⟩
  · have := ENNReal.tendsto_ofReal (hωzero.div_const (r / 2))
    simpa using this
  have hωp : 0 ≤ ω p / (r / 2) := div_nonneg (hωpos p).le hρpos.le
  have hηp : (1 : ℝ≥0∞) + ENNReal.ofReal (ω p / (r / 2)) = ENNReal.ofReal (1 + ω p / (r / 2)) := by
    rw [ENNReal.ofReal_add zero_le_one hωp, ENNReal.ofReal_one]
  have hfin : (1 : ℝ≥0∞) + ENNReal.ofReal (ω p / (r / 2)) ≠ ⊤ := by
    rw [hηp]; exact ENNReal.ofReal_ne_top
  have hTL : σ.timeLimit (fun n ↦ (1 + ENNReal.ofReal (ω p / (r / 2))) *
      finiteScaleBSCost P T u A x n (dyadicRadius p)) =
      (1 + ENNReal.ofReal (ω p / (r / 2))) *
        σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) := by
    cases σ
    · exact ENNReal.liminf_const_mul_of_ne_top hfin
    · exact ENNReal.limsup_const_mul_of_ne_top hfin
  rw [← hTL]
  apply LimitSide.timeLimit_mono
  filter_upwards [eventually_lt_of_lt_liminf hrx, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hbase : r * n < birkhoffSum T u n x :=
    (lt_div_iff₀ hnpos).mp (EReal.coe_lt_coe_iff.mp hn)
  have hsmall : ω p < r / 2 := hp₁ p (le_of_max_le_right hp)
  have hosc : ∀ y ∈ bowenBall T n x (dyadicRadius p),
      |birkhoffSum T u n y - birkhoffSum T u n x| ≤ n * ω p := fun y hy ↦
    small_scale_oscillation_birkhoff T u p (ω p) (hω p (le_of_max_le_left hp)) n x y hy
  have hlow : ∀ y ∈ bowenBall T n x (dyadicRadius p), r / 2 * n ≤ birkhoffSum T u n y := by
    intro y hy
    have := (abs_le.mp (hosc y hy)).1
    nlinarith
  have hup : ∀ y ∈ bowenBall T n x (dyadicRadius p),
      birkhoffSum T u n y ≤ birkhoffSum T u n x + n * ω p := by
    intro y hy
    have := (abs_le.mp (hosc y hy)).2
    linarith
  obtain ⟨i, hi, hieq⟩ := finite_scale_min_attained_ratio P T hT u A x n hn1 (dyadicRadius p)
    (dyadicRadius_pos p) (r / 2 * n) (birkhoffSum T u n x + n * ω p) (by positivity)
    (fun j hj ↦ ⟨hlow _ hj, hup _ hj⟩)
  rw [hieq]
  have hbx : 0 < birkhoffSum T u n x := lt_trans (by positivity) hbase
  have hbi : 0 < birkhoffSum T u n (P.ι i) := lt_of_lt_of_le (by positivity) (hlow _ hi)
  have hK : (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) ≤ oracleNatComplexity A i := by
    exact_mod_cast orbitComplexityNat_le P T A x hi
  have hbi_le : birkhoffSum T u n (P.ι i) ≤ (1 + ω p / (r / 2)) * birkhoffSum T u n x := by
    have h1 := hup _ hi
    have h2 : (n : ℝ) * ω p ≤ birkhoffSum T u n x / (r / 2) * ω p := by
      refine mul_le_mul_of_nonneg_right ?_ (hωpos p).le
      rw [le_div_iff₀ hρpos]
      linarith [hlow x (self_mem_bowenBall T n x _ (dyadicRadius_pos p))]
    have h3 : birkhoffSum T u n x / (r / 2) * ω p = ω p / (r / 2) * birkhoffSum T u n x := by
      ring
    linarith
  unfold centeredBSCost
  rw [hηp, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hbx,
    ← ENNReal.ofReal_div_of_pos hbi, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hne : (1 + ω p / (r / 2)) ≠ 0 := by positivity
  calc (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) / birkhoffSum T u n x
      ≤ (oracleNatComplexity A i : ℝ) / birkhoffSum T u n x :=
        div_le_div_of_nonneg_right hK hbx.le
    _ = (1 + ω p / (r / 2)) *
        ((oracleNatComplexity A i : ℝ) / ((1 + ω p / (r / 2)) * birkhoffSum T u n x)) := by
        rw [← mul_div_assoc, mul_div_mul_left _ _ hne]
    _ ≤ (1 + ω p / (r / 2)) * ((oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hbi hbi_le) (by positivity)

include hT hu hx in
/-- The reverse comparison, with the same kind of factor; together with
`centeredBSCost_timeLimit_le` it shows the two scale suprema agree.
Blueprint node `geo:bs-denominator-swap`. -/
theorem finiteScaleBSCost_timeLimit_le_centered (σ : LimitSide) :
    ∃ p₀ : ℕ, ∃ η : ℕ → ℝ≥0∞, Tendsto η atTop (𝓝 0) ∧ ∀ p : ℕ, p₀ ≤ p →
      σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) ≤
        (1 + η p) * σ.timeLimit (fun n ↦ centeredBSCost P T u A x n (dyadicRadius p)) := by
  obtain ⟨r, hr, hrx⟩ := EReal.exists_between_coe_real hx
  have hrpos : 0 < r := EReal.coe_pos.mp hr
  obtain ⟨ω, hωpos, hωzero, pω, hω⟩ := small_scale_oscillation u hu
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.mp (hωzero.eventually (gt_mem_nhds (half_pos hrpos)))
  have hρpos : 0 < r / 2 := half_pos hrpos
  refine ⟨max pω p₁, fun p ↦ ENNReal.ofReal (ω p / (r / 2)), ?_, fun p hp ↦ ?_⟩
  · have := ENNReal.tendsto_ofReal (hωzero.div_const (r / 2))
    simpa using this
  have hωp : 0 ≤ ω p / (r / 2) := div_nonneg (hωpos p).le hρpos.le
  have hηp : (1 : ℝ≥0∞) + ENNReal.ofReal (ω p / (r / 2)) = ENNReal.ofReal (1 + ω p / (r / 2)) := by
    rw [ENNReal.ofReal_add zero_le_one hωp, ENNReal.ofReal_one]
  have hfin : (1 : ℝ≥0∞) + ENNReal.ofReal (ω p / (r / 2)) ≠ ⊤ := by
    rw [hηp]; exact ENNReal.ofReal_ne_top
  have hTL : σ.timeLimit (fun n ↦ (1 + ENNReal.ofReal (ω p / (r / 2))) *
      centeredBSCost P T u A x n (dyadicRadius p)) =
      (1 + ENNReal.ofReal (ω p / (r / 2))) *
        σ.timeLimit (fun n ↦ centeredBSCost P T u A x n (dyadicRadius p)) := by
    cases σ
    · exact ENNReal.liminf_const_mul_of_ne_top hfin
    · exact ENNReal.limsup_const_mul_of_ne_top hfin
  rw [← hTL]
  apply LimitSide.timeLimit_mono
  filter_upwards [eventually_lt_of_lt_liminf hrx, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hbase : r * n < birkhoffSum T u n x :=
    (lt_div_iff₀ hnpos).mp (EReal.coe_lt_coe_iff.mp hn)
  have hsmall : ω p < r / 2 := hp₁ p (le_of_max_le_right hp)
  have hosc : ∀ y ∈ bowenBall T n x (dyadicRadius p),
      |birkhoffSum T u n y - birkhoffSum T u n x| ≤ n * ω p := fun y hy ↦
    small_scale_oscillation_birkhoff T u p (ω p) (hω p (le_of_max_le_left hp)) n x y hy
  have hlow : ∀ y ∈ bowenBall T n x (dyadicRadius p), r / 2 * n ≤ birkhoffSum T u n y := by
    intro y hy
    have := (abs_le.mp (hosc y hy)).1
    nlinarith
  obtain ⟨i, hi, hiK⟩ := orbitComplexityNat_attained P T A x hT n (dyadicRadius_pos p)
  have hbx : 0 < birkhoffSum T u n x := lt_trans (by positivity) hbase
  have hbi : 0 < birkhoffSum T u n (P.ι i) := lt_of_lt_of_le (by positivity) (hlow _ hi)
  refine (finiteScaleBSCost_le_div P T u A (by omega) hi hbi).trans ?_
  have hbx_le : birkhoffSum T u n x ≤ (1 + ω p / (r / 2)) * birkhoffSum T u n (P.ι i) := by
    have h1 := (abs_le.mp (hosc _ hi)).1
    have h2 : (n : ℝ) * ω p ≤ birkhoffSum T u n (P.ι i) / (r / 2) * ω p := by
      refine mul_le_mul_of_nonneg_right ?_ (hωpos p).le
      rw [le_div_iff₀ hρpos]
      linarith [hlow _ hi]
    have h3 : birkhoffSum T u n (P.ι i) / (r / 2) * ω p =
        ω p / (r / 2) * birkhoffSum T u n (P.ι i) := by
      ring
    linarith
  unfold centeredBSCost
  rw [hiK, hηp, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hbx,
    ← ENNReal.ofReal_div_of_pos hbi, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hne : (1 + ω p / (r / 2)) ≠ 0 := by positivity
  calc (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) / birkhoffSum T u n (P.ι i)
      = (1 + ω p / (r / 2)) * ((orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) /
          ((1 + ω p / (r / 2)) * birkhoffSum T u n (P.ι i))) := by
        rw [← mul_div_assoc, mul_div_mul_left _ _ hne]
    _ ≤ (1 + ω p / (r / 2)) *
        ((orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) / birkhoffSum T u n x) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hbx hbx_le) (by positivity)

include hT in
/-- The centered cost's time limit is nondecreasing in the dyadic precision index.
Blueprint node `geo:bs-denominator-swap`. -/
theorem centeredBSCost_timeLimit_mono (σ : LimitSide) :
    Monotone fun p : ℕ ↦ σ.timeLimit (fun n ↦ centeredBSCost P T u A x n (dyadicRadius p)) := by
  intro p q hpq
  apply LimitSide.timeLimit_mono
  refine Eventually.of_forall fun n ↦ ?_
  unfold centeredBSCost
  refine ENNReal.div_le_div ?_ le_rfl
  exact_mod_cast orbitComplexityNat_anti_radius P T A x hT n (dyadicRadius_pos q)
    (dyadicRadius_antitone hpq)

include hT hu hx in
/-- The scale supremum of centered costs is the pointwise BS dimension. This is the bridge
between the drafts' `K^A_n(x,T,ε) / S_n u(x)` and `pointwiseBSDimension`.
Blueprint node `geo:bs-denominator-swap`. -/
theorem iSup_centeredBSCost_timeLimit_eq (σ : LimitSide) :
    (⨆ p : ℕ, σ.timeLimit (fun n ↦ centeredBSCost P T u A x n (dyadicRadius p))) =
      σ.choose (pointwiseBSDimension P T u A x) := by
  have key : ∀ F G : ℕ → ℝ≥0∞, Monotone F →
      (∃ p₀ : ℕ, ∃ η : ℕ → ℝ≥0∞, Tendsto η atTop (𝓝 0) ∧ ∀ p, p₀ ≤ p → F p ≤ (1 + η p) * G p) →
      (⨆ p, F p) ≤ ⨆ p, G p := by
    rintro F G hF ⟨p₀, η, hη, h⟩
    refine iSup_le fun p ↦ ?_
    have ht : Tendsto (fun q ↦ (1 + η q) * ⨆ p, G p) atTop (𝓝 ((1 + 0) * ⨆ p, G p)) :=
      ENNReal.Tendsto.mul_const (tendsto_const_nhds.add hη) (Or.inl (by simp))
    rw [add_zero, one_mul] at ht
    refine ge_of_tendsto ht (eventually_atTop.2 ⟨max p p₀, fun q hq ↦ ?_⟩)
    exact (hF (le_of_max_le_left hq)).trans ((h q (le_of_max_le_right hq)).trans
      (mul_le_mul_right (le_iSup G q) _))
  have hchoose : σ.choose (pointwiseBSDimension P T u A x) =
      ⨆ p, σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) := by
    cases σ <;> rfl
  rw [hchoose]
  apply le_antisymm
  · exact key _ _ (centeredBSCost_timeLimit_mono P T hT u A x σ)
      (centeredBSCost_timeLimit_le P T hT u hu A x hx σ)
  · refine key _ _ ?_ (finiteScaleBSCost_timeLimit_le_centered P T hT u hu A x hx σ)
    intro p q hpq
    apply LimitSide.timeLimit_mono
    exact Eventually.of_forall fun n ↦
      pointwiseBSDimension_antitone_radius P T u A x n (dyadicRadius_antitone hpq)

include hT hu hx in
/-- The inequality actually used in Chapter I: every fixed-radius time limit of the centered
cost is at most `(1 + η p)` times the pointwise BS dimension.
Blueprint node `geo:bs-denominator-swap`. -/
theorem centeredBSCost_timeLimit_le_pointwiseBSDimension (σ : LimitSide) :
    ∃ p₀ : ℕ, ∃ η : ℕ → ℝ≥0∞, Tendsto η atTop (𝓝 0) ∧ ∀ p : ℕ, p₀ ≤ p →
      σ.timeLimit (fun n ↦ centeredBSCost P T u A x n (dyadicRadius p)) ≤
        (1 + η p) * σ.choose (pointwiseBSDimension P T u A x) := by
  obtain ⟨p₀, η, hη, h⟩ := centeredBSCost_timeLimit_le P T hT u hu A x hx σ
  refine ⟨p₀, η, hη, fun p hp ↦ (h p hp).trans (mul_le_mul_right ?_ _)⟩
  have hchoose : σ.choose (pointwiseBSDimension P T u A x) =
      ⨆ p, σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) := by
    cases σ <;> rfl
  rw [hchoose]
  exact le_iSup (fun p ↦ σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p))) p

end denominatorSwap

end Kolmogorov.PointToSet
