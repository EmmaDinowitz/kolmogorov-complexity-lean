/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.Surface.JacobiSolutions

/-!
# The unstable and stable rates and the singular set

Part 1 of `/home/user/geometry_formalization_blueprint.md`, second half (nodes
`surf:riccati-solutions` (limits), `surf:rates-continuous`, `surf:singular-set`,
`surf:transversality-rates`). Decisions in force: C1 (surfaces, scalar equation), C7 (rates as
Riccati limits), C3 (minimal regularity: only a continuous flow and a continuous potential).

## Main definitions

* `CurvatureFlow.lamU v`: the unstable rate, the decreasing limit of `logDerivFrom v (-T) 0` as
  `T → ∞`; `CurvatureFlow.lamS v`: the stable rate, minus the increasing limit of
  `logDerivTo v T 0`. Both are nonnegative and bounded by `Λ = √(sup (-K))`.
* `CurvatureFlow.Sing`: the singular set `{v | lamU v = 0 ∧ lamS v = 0}`; `Reg` its complement.

## Main results

* The rates satisfy the Riccati equation along orbits; the unstable rate is the logarithmic
  derivative of the unique (up to scale) Jacobi solution bounded in backward time
  (`exists_unstable_jacobiSolution`, `eq_lamU_of_riccati_nonneg`).
* The rates are continuous (`continuous_lamU`, `continuous_lamS`): uniform limits, by the
  Wronskian bound `0 ≤ logDerivFrom v (-T) 0 - lamU v ≤ 1 / T`.
* `Sing` is closed and invariant; `v ∈ Sing` iff `K` vanishes along the whole orbit of `v`;
  `lamU v = 0` iff `K` vanishes along the backward orbit; `0 < lamU v + lamS v` iff `v ∈ Reg`.

Density of the regular set is not provable in this generality (blueprint node `surf:reg-dense`,
Part 4).

## References

* P. Eberlein, *When is a geodesic flow of Anosov type? I*, J. Differential Geom. 8 (1973), §2.
* W. Ballmann, *Lectures on spaces of nonpositive curvature*, Chapter IV.
* G. Knieper, *Hyperbolic dynamics and Riemannian geometry*, Handbook of Dynamical Systems 1A, §2.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]

namespace CurvatureFlow

variable (C : CurvatureFlow X)

/-! ### The rates `lamU` and `lamS` -/

/-- The unstable rate `u^u(v) = lim_{T → ∞} logDerivFrom v (-T) 0`, as the infimum of the
nonincreasing family. -/
noncomputable def lamU (v : X) : ℝ := ⨅ T : Ioi (0 : ℝ), C.logDerivFrom v (-(T : ℝ)) 0

/-- The stable rate `λ^s(v) = -u^s(v) = -lim_{T → ∞} logDerivTo v T 0`. -/
noncomputable def lamS (v : X) : ℝ := ⨅ T : Ioi (0 : ℝ), -C.logDerivTo v (T : ℝ) 0

/-- The stable rate of `C` is the unstable rate of the reversed flow. -/
theorem lamS_eq_reverse_lamU (v : X) : C.lamS v = C.reverse.lamU v := by
  simp only [lamS, lamU, C.logDerivTo_eq_reverse, neg_neg, neg_zero]

/-- The family `logDerivFrom v (-T) 0`, `T > 0`, is bounded below by `0`. -/
private theorem aux2_bddBelow (v : X) :
    BddBelow (range fun T : Ioi (0 : ℝ) ↦ C.logDerivFrom v (-(T : ℝ)) 0) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨T, rfl⟩
  exact (C.logDerivFrom_pos v (neg_lt_zero.2 T.2)).le

/-- `logDerivFrom v (-T) 0` converges to the unstable rate `lamU v` as `T → ∞`. -/
theorem tendsto_logDerivFrom_lamU (v : X) :
    Tendsto (fun T : ℝ ↦ C.logDerivFrom v (-T) 0) atTop (𝓝 (C.lamU v)) := by
  have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  rw [tendsto_order]
  refine ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with T hT
    exact ha.trans_le (ciInf_le (C.aux2_bddBelow v) ⟨T, hT⟩)
  · obtain ⟨T₀, hT₀⟩ := exists_lt_of_ciInf_lt
      (f := fun T : Ioi (0 : ℝ) ↦ C.logDerivFrom v (-(T : ℝ)) 0) ha
    filter_upwards [eventually_ge_atTop (T₀ : ℝ)] with T hT
    exact (C.logDerivFrom_mono_pole v (neg_le_neg hT) (neg_lt_zero.2 T₀.2)).trans_lt hT₀

/-- `-logDerivTo v T 0` converges to the stable rate `lamS v` as `T → ∞`. -/
theorem tendsto_logDerivTo_lamS (v : X) :
    Tendsto (fun T : ℝ ↦ -C.logDerivTo v T 0) atTop (𝓝 (C.lamS v)) := by
  have h := C.reverse.tendsto_logDerivFrom_lamU v
  rw [← C.lamS_eq_reverse_lamU] at h
  refine h.congr fun T ↦ ?_
  rw [C.logDerivTo_eq_reverse, neg_neg, neg_zero]

/-- The unstable rate is at most `logDerivFrom v (-T) 0` for every `T > 0`. -/
theorem lamU_le_logDerivFrom (v : X) {T : ℝ} (hT : 0 < T) :
    C.lamU v ≤ C.logDerivFrom v (-T) 0 :=
  ciInf_le (C.aux2_bddBelow v) ⟨T, hT⟩

/-- The unstable rate is nonnegative. -/
theorem lamU_nonneg (v : X) : 0 ≤ C.lamU v := by
  have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  exact le_ciInf fun T ↦ (C.logDerivFrom_pos v (neg_lt_zero.2 T.2)).le

/-- The stable rate is nonnegative. -/
theorem lamS_nonneg (v : X) : 0 ≤ C.lamS v := by
  rw [C.lamS_eq_reverse_lamU]
  exact C.reverse.lamU_nonneg v

/-- The unstable rate is at most `Λ = √(sup (-K))`. -/
theorem lamU_le (v : X) : C.lamU v ≤ C.Λ := by
  have h : Tendsto (fun T : ℝ ↦ 1 / T + C.Λ) atTop (𝓝 (0 + C.Λ)) :=
    (tendsto_const_nhds.div_atTop tendsto_id).add_const _
  rw [zero_add] at h
  refine le_of_tendsto_of_tendsto (C.tendsto_logDerivFrom_lamU v) h ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  simpa using C.logDerivFrom_le v (neg_lt_zero.2 hT)

/-- The stable rate is at most `Λ = √(sup (-K))`. -/
theorem lamS_le (v : X) : C.lamS v ≤ C.Λ := by
  rw [C.lamS_eq_reverse_lamU]
  exact C.reverse.lamU_le v

/-- Rescaling a Jacobi solution gives a Jacobi solution. -/
private theorem aux2_smul {v : X} {y y' : ℝ → ℝ} (h : C.IsJacobiSolution v y y') (k : ℝ) :
    C.IsJacobiSolution v (fun t ↦ k * y t) (fun t ↦ k * y' t) := by
  simpa using h.add_smul h k 0

/-- The zero function is a Jacobi solution. -/
private theorem aux2_zero (v : X) : C.IsJacobiSolution v (fun _ ↦ 0) (fun _ ↦ 0) :=
  ⟨fun _ ↦ hasDerivAt_const _ _, fun t ↦ by simpa using hasDerivAt_const t (0 : ℝ)⟩

/-- A Jacobi solution with a double zero vanishes identically. -/
private theorem aux2_eq_zero {v : X} {y y' : ℝ → ℝ} (h : C.IsJacobiSolution v y y') {t₀ : ℝ}
    (h0 : y t₀ = 0) (h0' : y' t₀ = 0) (t : ℝ) : y t = 0 :=
  congrFun (h.unique (C.aux2_zero v) h0 h0').1 t

/-- A nonnegative Jacobi solution that does not vanish identically is positive: a zero would be
a minimum, hence a double zero. -/
private theorem aux2_pos_of_nonneg {v : X} {y y' : ℝ → ℝ} (h : C.IsJacobiSolution v y y')
    (hnn : ∀ t, 0 ≤ y t) {s : ℝ} (hs : y s ≠ 0) (t : ℝ) : 0 < y t := by
  refine (hnn t).lt_of_ne fun ht ↦ hs ?_
  have hmin : IsLocalMin y t := Filter.Eventually.of_forall fun x ↦ by rw [← ht]; exact hnn x
  exact C.aux2_eq_zero h ht.symm (hmin.hasDerivAt_eq_zero (h.hasDerivAt t)) s

/-- `logDerivFrom v (-S) t → lamU (φ t v)` as `S → ∞` (shift of `tendsto_logDerivFrom_lamU`). -/
private theorem aux2_tendsto_shift (v : X) (t : ℝ) :
    Tendsto (fun S : ℝ ↦ C.logDerivFrom v (-S) t) atTop (𝓝 (C.lamU (C.φ t v))) := by
  have h := (C.tendsto_logDerivFrom_lamU (C.φ t v)).comp
    (tendsto_atTop_add_const_right _ t tendsto_id)
  refine h.congr fun S ↦ ?_
  change C.logDerivFrom (C.φ t v) (-(S + t)) 0 = _
  rw [C.logDerivFrom_flow]
  congr 1 <;> ring

/-- The unstable Jacobi solution: `y'' + K y = 0`, `y 0 = 1`, `y' 0 = lamU v`; it is positive and
bounded on `(-∞, 0]` and `lamU (φ t v) = y' t / y t` for all `t`. It is the limit of the
normalized solutions `jacobiFrom v (-S)` written in the basis of solutions with data `(1, 0)` and
`(0, 1)` at time `0`. -/
theorem exists_unstable_jacobiSolution (v : X) :
    ∃ y y' : ℝ → ℝ, C.IsJacobiSolution v y y' ∧ y 0 = 1 ∧ y' 0 = C.lamU v ∧
      (∀ t, 0 < y t) ∧ (∀ t ≤ 0, y t ≤ 1) ∧ ∀ t, C.lamU (C.φ t v) = y' t / y t := by
  obtain ⟨a, a', ha, ha0, ha0'⟩ := C.exists_isJacobiSolution v 0 1 0
  obtain ⟨b, b', hb, hb0, hb0'⟩ := C.exists_isJacobiSolution v 0 0 1
  have hrep : ∀ S, 0 < S → ∀ t,
      C.jacobiFrom v (-S) t =
        C.jacobiFrom v (-S) 0 * (a t + C.logDerivFrom v (-S) 0 * b t) ∧
      C.jacobiFrom' v (-S) t =
        C.jacobiFrom v (-S) 0 * (a' t + C.logDerivFrom v (-S) 0 * b' t) := by
    intro S hS t
    have hJ0 : C.jacobiFrom v (-S) 0 ≠ 0 := (C.jacobiFrom_pos v (neg_lt_zero.2 hS)).ne'
    have hc := ha.add_smul hb (C.jacobiFrom v (-S) 0)
      (C.jacobiFrom v (-S) 0 * C.logDerivFrom v (-S) 0)
    have e1 : C.jacobiFrom v (-S) 0 * a 0 +
        C.jacobiFrom v (-S) 0 * C.logDerivFrom v (-S) 0 * b 0 = C.jacobiFrom v (-S) 0 := by
      rw [ha0, hb0]; ring
    have e2 : C.jacobiFrom v (-S) 0 * a' 0 +
        C.jacobiFrom v (-S) 0 * C.logDerivFrom v (-S) 0 * b' 0 = C.jacobiFrom' v (-S) 0 := by
      rw [ha0', hb0', logDerivFrom]; field_simp; ring
    have hu := hc.unique (C.isJacobiSolution_jacobiFrom v (-S)) (s := 0) e1 e2
    constructor
    · rw [← congrFun hu.1 t]; ring
    · rw [← congrFun hu.2 t]; ring
  set L := C.lamU v with hL
  have hy : C.IsJacobiSolution v (fun t ↦ a t + L * b t) (fun t ↦ a' t + L * b' t) := by
    simpa using ha.add_smul hb 1 L
  have hc : Tendsto (fun S : ℝ ↦ C.logDerivFrom v (-S) 0) atTop (𝓝 L) :=
    C.tendsto_logDerivFrom_lamU v
  have hden : ∀ t, Tendsto (fun S ↦ a t + C.logDerivFrom v (-S) 0 * b t) atTop
      (𝓝 (a t + L * b t)) := fun t ↦ tendsto_const_nhds.add (hc.mul_const _)
  have hnum : ∀ t, Tendsto (fun S ↦ a' t + C.logDerivFrom v (-S) 0 * b' t) atTop
      (𝓝 (a' t + L * b' t)) := fun t ↦ tendsto_const_nhds.add (hc.mul_const _)
  have hposS : ∀ t S, 0 < S → -S < t → 0 < a t + C.logDerivFrom v (-S) 0 * b t := by
    intro t S hS ht
    have h1 := C.jacobiFrom_pos v ht
    have h0 := C.jacobiFrom_pos v (neg_lt_zero.2 hS)
    rw [(hrep S hS t).1] at h1
    exact pos_of_mul_pos_right h1 h0.le
  have hev : ∀ t, ∀ᶠ S : ℝ in atTop, 0 < S ∧ -S < t := fun t ↦
    ((eventually_gt_atTop 0).and (eventually_gt_atTop (-t))).mono
      fun S h ↦ ⟨h.1, by linarith [h.2]⟩
  have hnn : ∀ t, 0 ≤ a t + L * b t := fun t ↦
    ge_of_tendsto (hden t) ((hev t).mono fun S h ↦ (hposS t S h.1 h.2).le)
  have hy0 : a 0 + L * b 0 = 1 := by rw [ha0, hb0]; ring
  have hpos : ∀ t, 0 < a t + L * b t :=
    C.aux2_pos_of_nonneg hy hnn (s := 0) (by rw [hy0]; exact one_ne_zero)
  have hlam : ∀ t, C.lamU (C.φ t v) = (a' t + L * b' t) / (a t + L * b t) := by
    intro t
    refine tendsto_nhds_unique (C.aux2_tendsto_shift v t) ?_
    refine ((hnum t).div (hden t) (hpos t).ne').congr' ?_
    filter_upwards [hev t] with S hS
    have h0 := C.jacobiFrom_pos v (neg_lt_zero.2 hS.1)
    rw [show C.logDerivFrom v (-S) t = C.jacobiFrom' v (-S) t / C.jacobiFrom v (-S) t from rfl,
      (hrep S hS.1 t).1, (hrep S hS.1 t).2, mul_div_mul_left _ _ h0.ne']
    rfl
  have hderiv_nn : ∀ t, 0 ≤ a' t + L * b' t := fun t ↦ by
    have e := (div_mul_cancel₀ (a' t + L * b' t) (hpos t).ne').symm
    rw [← hlam t] at e
    rw [e]
    exact mul_nonneg (C.lamU_nonneg _) (hpos t).le
  have hmono : Monotone (fun t ↦ a t + L * b t) :=
    monotone_of_hasDerivAt_nonneg hy.hasDerivAt hderiv_nn
  refine ⟨_, _, hy, hy0, ?_, hpos, fun t ht ↦ (hmono ht).trans hy0.le, hlam⟩
  rw [ha0', hb0']; ring

/-- The unstable rate solves the Riccati equation along the orbit. -/
theorem hasDerivAt_lamU_flow (v : X) (t : ℝ) :
    HasDerivAt (fun τ ↦ C.lamU (C.φ τ v)) (-(C.lamU (C.φ t v)) ^ 2 - C.orbitK v t) t := by
  obtain ⟨y, y', hy, -, -, hpos, -, hlam⟩ := C.exists_unstable_jacobiSolution v
  have hfun : (fun τ ↦ C.lamU (C.φ τ v)) = fun τ ↦ y' τ / y τ := funext hlam
  rw [hfun, hlam]
  convert (hy.hasDerivAt' t).div (hy.hasDerivAt t) (hpos t).ne' using 1
  have := (hpos t).ne'
  field_simp
  ring

/-- The reversed flow runs the original flow backwards. -/
private theorem aux2_reverse_φ (s : ℝ) (x : X) : C.reverse.φ s x = C.φ (-s) x := rfl

/-- The stable rate solves the Riccati equation with the opposite sign along the orbit
(`u^s = -λ^s`). -/
theorem hasDerivAt_lamS_flow (v : X) (t : ℝ) :
    HasDerivAt (fun τ ↦ -C.lamS (C.φ τ v)) (-(C.lamS (C.φ t v)) ^ 2 - C.orbitK v t) t := by
  have h := ((C.reverse.hasDerivAt_lamU_flow v (-t)).comp t (hasDerivAt_neg t)).neg
  have e : ∀ τ, C.reverse.lamU (C.reverse.φ (-τ) v) = C.lamS (C.φ τ v) := fun τ ↦ by
    rw [C.lamS_eq_reverse_lamU, aux2_reverse_φ, neg_neg]
  convert h using 1
  · funext τ
    simp only [Pi.neg_apply, Function.comp_apply]
    rw [e]
  · rw [e, C.reverse_orbitK, neg_neg]
    ring

/-- `jacobiTo v s t ≥ s - t` before the zero, since its derivative is at most `-1` there. -/
private theorem aux2_jacobiTo_ge (v : X) {s t : ℝ} (h : t ≤ s) : s - t ≤ C.jacobiTo v s t := by
  have hJ := C.isJacobiSolution_jacobiTo v s
  have hd : ∀ τ, HasDerivAt (fun τ ↦ C.jacobiTo v s τ + τ) (C.jacobiTo' v s τ + 1) τ :=
    fun τ ↦ (hJ.hasDerivAt τ).add (hasDerivAt_id' τ)
  have hanti : AntitoneOn (fun τ ↦ C.jacobiTo v s τ + τ) (Iic s) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic s)
      (fun τ _ ↦ (hd τ).continuousAt.continuousWithinAt) (fun τ _ ↦ (hd τ).hasDerivWithinAt) ?_
    intro τ hτ
    rw [interior_Iic] at hτ
    linarith [C.jacobiTo'_le_neg_one v hτ]
  have := hanti h (Set.mem_Iic.2 le_rfl) h
  simp only [C.jacobiTo_self] at this
  linarith

/-- Uniqueness: a positive Jacobi solution bounded in backward time is a multiple of the unstable
one, so its logarithmic derivative at `0` is `lamU v`. -/
theorem IsJacobiSolution.deriv_div_eq_lamU_of_bounded {C : CurvatureFlow X} {v : X} {y y' : ℝ → ℝ}
    (h : C.IsJacobiSolution v y y') (hpos : ∀ t ≤ 0, 0 < y t) (hbdd : ∃ M, ∀ t ≤ 0, y t ≤ M) :
    y' 0 / y 0 = C.lamU v := by
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨w, w', hw, hw0, hw0', hwpos, hw1, -⟩ := C.exists_unstable_jacobiSolution v
  have hy0 := hpos 0 le_rfl
  have hM0 : 0 < M := hy0.trans_le (hM 0 le_rfl)
  by_contra hne
  have hD : y' 0 - C.lamU v * y 0 ≠ 0 := by
    intro h0; apply hne; rw [div_eq_iff hy0.ne']; linarith
  set α := y 0 / (y' 0 - C.lamU v * y 0) with hα
  set β := -1 / (y' 0 - C.lamU v * y 0) with hβ
  have hcomb := hw.add_smul h α β
  have e1 : α * w 0 + β * y 0 = C.jacobiTo v 0 0 := by
    rw [hw0, C.jacobiTo_self, hα, hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hD]
    ring
  have e2 : α * w' 0 + β * y' 0 = C.jacobiTo' v 0 0 := by
    rw [hw0', C.jacobiTo'_self, hα, hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hD]
    ring
  have hu := (hcomb.unique (C.isJacobiSolution_jacobiTo v 0) (s := 0) e1 e2).1
  set B := |α| + |β| * M with hB
  have hB0 : 0 ≤ B := add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hM0.le)
  have hτ : -(B + 1) ≤ 0 := by linarith
  have hge := C.aux2_jacobiTo_ge v hτ
  rw [← hu] at hge
  have h1 : α * w (-(B + 1)) ≤ |α| :=
    calc α * w (-(B + 1)) ≤ |α| * w (-(B + 1)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (hwpos _).le
      _ ≤ |α| * 1 := mul_le_mul_of_nonneg_left (hw1 _ hτ) (abs_nonneg _)
      _ = |α| := mul_one _
  have h2 : β * y (-(B + 1)) ≤ |β| * M :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (hpos _ hτ).le).trans
      (mul_le_mul_of_nonneg_left (hM _ hτ) (abs_nonneg _))
  simp only at hge
  linarith

/-- Uniqueness in Riccati form: a Riccati solution on `(-∞, 0]` that stays nonnegative there is
the unstable one. -/
theorem eq_lamU_of_riccati_nonneg {v : X} {u : ℝ → ℝ}
    (hu : ∀ t ≤ 0, HasDerivWithinAt u (-(u t) ^ 2 - C.orbitK v t) (Iic 0) t)
    (hnn : ∀ t ≤ 0, 0 ≤ u t) : u 0 = C.lamU v := by
  obtain ⟨Y, Y', hY, hY0, hY0'⟩ := C.exists_isJacobiSolution v 0 1 (u 0)
  have hYc : Continuous Y :=
    continuous_iff_continuousAt.2 fun t ↦ (hY.hasDerivAt t).continuousAt
  have hY'c : Continuous Y' :=
    continuous_iff_continuousAt.2 fun t ↦ (hY.hasDerivAt' t).continuousAt
  have huc : ContinuousOn u (Iic 0) := fun t ht ↦ (hu t ht).continuousWithinAt
  have hu' : ∀ t < 0, HasDerivAt u (-(u t) ^ 2 - C.orbitK v t) t := fun t ht ↦
    (hu t ht.le).hasDerivAt (Iic_mem_nhds ht)
  -- `g = Y' - u Y` solves `g' = -u g` with `g 0 = 0`, hence vanishes (Grönwall).
  have hg : ∀ t ≤ 0, Y' t = u t * Y t := by
    intro t ht
    have hucI : ContinuousOn u (Icc t 0) := huc.mono Icc_subset_Iic_self
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hucI
    have hkc : ContinuousOn (fun s ↦ (Y' s - u s * Y s) * (Y' s - u s * Y s) *
        Real.exp (2 * B * s)) (Icc t 0) := by
      have h1 : ContinuousOn (fun s ↦ Y' s - u s * Y s) (Icc t 0) :=
        hY'c.continuousOn.sub (hucI.mul hYc.continuousOn)
      exact (h1.mul h1).mul (by fun_prop)
    have hmono : MonotoneOn (fun s ↦ (Y' s - u s * Y s) * (Y' s - u s * Y s) *
        Real.exp (2 * B * s)) (Icc t 0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t 0) hkc
        (f' := fun s ↦ 2 * ((Y' s - u s * Y s) * (Y' s - u s * Y s)) *
          Real.exp (2 * B * s) * (B - u s)) ?_ ?_
      · intro s hs
        rw [interior_Icc] at hs
        have hg' := (hY.hasDerivAt' s).sub ((hu' s hs.2).mul (hY.hasDerivAt s))
        have hd := (hg'.mul hg').mul (((hasDerivAt_id' s).const_mul (2 * B)).exp)
        convert hd.hasDerivWithinAt using 1
        simp only [Pi.sub_apply, Pi.mul_apply]
        ring
      · intro s hs
        rw [interior_Icc] at hs
        have hb := hB s (Ioo_subset_Icc_self hs)
        have hus : u s ≤ B := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
        exact mul_nonneg (mul_nonneg (mul_nonneg two_pos.le (mul_self_nonneg _))
          (Real.exp_pos _).le) (sub_nonneg.2 hus)
    have hk := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    simp only [hY0, hY0', mul_one, sub_self, mul_zero, zero_mul] at hk
    have hsq : (Y' t - u t * Y t) * (Y' t - u t * Y t) ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have := mul_pos hcon (Real.exp_pos (2 * B * t))
      linarith
    have := mul_self_eq_zero.1 (le_antisymm hsq (mul_self_nonneg _))
    linarith
  have hYne : ∀ t ≤ 0, Y t ≠ 0 := by
    intro t ht h0
    have h0' : Y' t = 0 := by rw [hg t ht, h0, mul_zero]
    have := C.aux2_eq_zero hY h0 h0' 0
    rw [hY0] at this
    exact one_ne_zero this
  have hYpos : ∀ t ≤ 0, 0 < Y t := by
    intro t ht
    by_contra hneg
    push Not at hneg
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc ht hYc.continuousOn
      (show (0 : ℝ) ∈ Icc (Y t) (Y 0) from ⟨hneg, by rw [hY0]; exact zero_le_one⟩)
    exact hYne c hc.2 hc0
  have hmonoY : MonotoneOn Y (Iic 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic 0) hYc.continuousOn
      (fun x _ ↦ (hY.hasDerivAt x).hasDerivWithinAt) ?_
    intro x hx
    rw [interior_Iic] at hx
    rw [hg x hx.le]
    exact mul_nonneg (hnn x hx.le) (hYpos x hx.le).le
  have hY1 : ∀ t ≤ 0, Y t ≤ 1 := fun t ht ↦ (hmonoY ht (Set.mem_Iic.2 le_rfl) ht).trans hY0.le
  have := hY.deriv_div_eq_lamU_of_bounded hYpos ⟨1, hY1⟩
  rwa [hY0, hY0', div_one] at this

/-! ### `surf:rates-continuous` -/

/-- `jacobiFrom v s t ≥ t - s` after the zero, since its derivative is at least `1` there. -/
private theorem aux2_jacobiFrom_ge (v : X) {s t : ℝ} (h : s ≤ t) :
    t - s ≤ C.jacobiFrom v s t := by
  have hJ := C.isJacobiSolution_jacobiFrom v s
  have hd : ∀ τ, HasDerivAt (fun τ ↦ C.jacobiFrom v s τ - τ) (C.jacobiFrom' v s τ - 1) τ :=
    fun τ ↦ (hJ.hasDerivAt τ).sub (hasDerivAt_id' τ)
  have hmono : MonotoneOn (fun τ ↦ C.jacobiFrom v s τ - τ) (Ici s) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici s)
      (fun τ _ ↦ (hd τ).continuousAt.continuousWithinAt) (fun τ _ ↦ (hd τ).hasDerivWithinAt) ?_
    intro τ hτ
    rw [interior_Ici] at hτ
    linarith [C.one_le_jacobiFrom' v hτ]
  have := hmono (Set.mem_Ici.2 le_rfl) h h
  simp only [C.jacobiFrom_self] at this
  linarith

/-- Uniform rate of convergence: `logDerivFrom v (-T) 0 - lamU v ≤ 1 / T`. With `w` the unstable
solution and `J = jacobiFrom v (-T)`, the Wronskian gives `J'(0) - lamU v · J(0) = w(-T) ≤ 1`,
and `J(0) ≥ T`. -/
private theorem aux2_logDerivFrom_sub_lamU_le (v : X) {T : ℝ} (hT : 0 < T) :
    C.logDerivFrom v (-T) 0 - C.lamU v ≤ 1 / T := by
  obtain ⟨w, w', hw, hw0, hw0', hwpos, hw1, -⟩ := C.exists_unstable_jacobiSolution v
  have hJ := C.isJacobiSolution_jacobiFrom v (-T)
  have hW := hw.wronskian_eq hJ (-T) 0
  rw [hw0, hw0', C.jacobiFrom_self, C.jacobiFrom'_self] at hW
  have hJ0 : T ≤ C.jacobiFrom v (-T) 0 := by
    simpa using C.aux2_jacobiFrom_ge v (s := -T) (t := 0) (by linarith)
  have hJpos : 0 < C.jacobiFrom v (-T) 0 := hT.trans_le hJ0
  have key : C.logDerivFrom v (-T) 0 - C.lamU v = w (-T) / C.jacobiFrom v (-T) 0 := by
    rw [eq_div_iff hJpos.ne', logDerivFrom, sub_mul, div_mul_cancel₀ _ hJpos.ne']
    linarith
  rw [key]
  calc w (-T) / C.jacobiFrom v (-T) 0 ≤ 1 / C.jacobiFrom v (-T) 0 :=
        div_le_div_of_nonneg_right (hw1 _ (by linarith)) hJpos.le
    _ ≤ 1 / T := one_div_le_one_div_of_le hT hJ0

/-- The rates are continuous (Dini: a monotone limit of continuous functions on a compact space
with a continuous limit converges uniformly; the limit is continuous because the family is
equicontinuous by the Riccati bound). -/
theorem continuous_lamU : Continuous C.lamU := by
  refine TendstoUniformly.continuous (F := fun T v ↦ C.logDerivFrom v (-T) 0) (p := atTop) ?_
    ((eventually_gt_atTop 0).frequently.mono fun T hT ↦
      C.continuous_logDerivFrom (neg_lt_zero.2 hT))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [eventually_gt_atTop (1 / ε)] with T hT v
  have hT0 : 0 < T := (one_div_pos.2 hε).trans hT
  have h1 := C.aux2_logDerivFrom_sub_lamU_le v hT0
  have h2 := C.lamU_le_logDerivFrom v hT0
  have h3 : 1 / T < ε := by
    rw [div_lt_iff₀ hT0]
    have := (div_lt_iff₀ hε).1 hT
    linarith
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- The stable rate is continuous. -/
theorem continuous_lamS : Continuous C.lamS := by
  have : C.lamS = C.reverse.lamU := funext C.lamS_eq_reverse_lamU
  rw [this]
  exact C.reverse.continuous_lamU

/-- The unstable rate is uniformly continuous on the compact space `X`. -/
theorem uniformContinuous_lamU : UniformContinuous C.lamU :=
  CompactSpace.uniformContinuous_of_continuous C.continuous_lamU

/-- The stable rate is uniformly continuous on the compact space `X`. -/
theorem uniformContinuous_lamS : UniformContinuous C.lamS :=
  CompactSpace.uniformContinuous_of_continuous C.continuous_lamS

/-! ### `surf:singular-set` -/

/-- The singular set: both rates vanish. -/
def Sing : Set X := {v | C.lamU v = 0 ∧ C.lamS v = 0}

/-- The regular set. -/
def Reg : Set X := C.Singᶜ

/-- Both rates vanish at `v` exactly when `v` lies in the singular set. -/
theorem lam_eq_zero_iff (v : X) : (C.lamU v = 0 ∧ C.lamS v = 0) ↔ v ∈ C.Sing := Iff.rfl

/-- The unstable rate vanishes exactly when the potential vanishes along the backward orbit. -/
theorem lamU_eq_zero_iff (v : X) : C.lamU v = 0 ↔ ∀ t ≤ 0, C.orbitK v t = 0 := by
  constructor
  · intro h0 t ht
    obtain ⟨w, w', hw, -, hw0', hwpos, -, hlam⟩ := C.exists_unstable_jacobiSolution v
    have hw'nn : ∀ s, 0 ≤ w' s := fun s ↦ by
      have e := (div_mul_cancel₀ (w' s) (hwpos s).ne').symm
      rw [← hlam s] at e
      rw [e]
      exact mul_nonneg (C.lamU_nonneg _) (hwpos s).le
    have hmono := hw.deriv_monotoneOn_of_nonneg (I := univ) ordConnected_univ
      fun s _ ↦ (hwpos s).le
    have hwt : w' t = 0 :=
      le_antisymm ((hmono (mem_univ t) (mem_univ 0) ht).trans (hw0'.trans h0).le) (hw'nn t)
    have hmin : IsLocalMin w' t :=
      Filter.Eventually.of_forall fun x ↦ by rw [hwt]; exact hw'nn x
    have := hmin.hasDerivAt_eq_zero (hw.hasDerivAt' t)
    rcases mul_eq_zero.1 this with h | h
    · exact neg_eq_zero.1 h
    · exact absurd h (hwpos t).ne'
  · intro h
    refine (C.eq_lamU_of_riccati_nonneg (u := fun _ ↦ (0 : ℝ)) (fun t ht ↦ ?_)
      fun _ _ ↦ le_rfl).symm
    rw [h t ht]
    simpa using hasDerivWithinAt_const t (Iic (0 : ℝ)) (0 : ℝ)

/-- The stable rate vanishes exactly when the potential vanishes along the forward orbit. -/
theorem lamS_eq_zero_iff (v : X) : C.lamS v = 0 ↔ ∀ t, 0 ≤ t → C.orbitK v t = 0 := by
  rw [C.lamS_eq_reverse_lamU, C.reverse.lamU_eq_zero_iff]
  constructor
  · intro h t ht
    have := h (-t) (by linarith)
    rwa [C.reverse_orbitK, neg_neg] at this
  · intro h t ht
    rw [C.reverse_orbitK]
    exact h _ (by linarith)

/-- `v` is singular exactly when the potential vanishes along the whole orbit of `v`. -/
theorem mem_Sing_iff (v : X) : v ∈ C.Sing ↔ ∀ t, C.orbitK v t = 0 := by
  change (C.lamU v = 0 ∧ C.lamS v = 0) ↔ _
  rw [C.lamU_eq_zero_iff, C.lamS_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩ t
    rcases le_total t 0 with ht | ht
    exacts [h1 t ht, h2 t ht]
  · intro h
    exact ⟨fun t _ ↦ h t, fun t _ ↦ h t⟩

/-- The singular set is closed. -/
theorem isClosed_Sing : IsClosed C.Sing :=
  (isClosed_eq C.continuous_lamU continuous_const).inter
    (isClosed_eq C.continuous_lamS continuous_const)

/-- The regular set is open. -/
theorem isOpen_Reg : IsOpen C.Reg :=
  C.isClosed_Sing.isOpen_compl

/-- Membership in `Sing` is invariant under the flow. -/
private theorem aux2_flow_mem_Sing_iff (s : ℝ) (x : X) : C.φ s x ∈ C.Sing ↔ x ∈ C.Sing := by
  have hmem : ∀ s x, x ∈ C.Sing → C.φ s x ∈ C.Sing := fun s x hx ↦ by
    rw [mem_Sing_iff] at hx ⊢
    intro r
    rw [C.orbitK_flow]
    exact hx _
  refine ⟨fun h ↦ ?_, hmem s x⟩
  have := hmem (-s) _ h
  rwa [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at this

/-- `φ t` is onto: `x = φ t (φ (-t) x)`. -/
private theorem aux2_flow_neg (t : ℝ) (x : X) : C.φ t (C.φ (-t) x) = x := by
  rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]

/-- The singular set is invariant: its image under each time-`t` map of the flow is itself. -/
theorem Sing_invariant (t : ℝ) : C.φ t '' C.Sing = C.Sing := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (C.aux2_flow_mem_Sing_iff t y).2 hy
  · intro hx
    exact ⟨C.φ (-t) x, (C.aux2_flow_mem_Sing_iff (-t) x).2 hx, C.aux2_flow_neg t x⟩

/-- The regular set is invariant: its image under each time-`t` map of the flow is itself. -/
theorem Reg_invariant (t : ℝ) : C.φ t '' C.Reg = C.Reg := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact fun h ↦ hy ((C.aux2_flow_mem_Sing_iff t y).1 h)
  · intro hx
    exact ⟨C.φ (-t) x, fun h ↦ hx ((C.aux2_flow_mem_Sing_iff (-t) x).1 h),
      C.aux2_flow_neg t x⟩

/-- The singular set is everything exactly when the potential vanishes identically ("rank one"
means `Sing ≠ univ`). -/
theorem Sing_eq_univ_iff : C.Sing = univ ↔ ∀ x, C.K x = 0 := by
  constructor
  · intro h x
    have := (C.mem_Sing_iff x).1 (h ▸ mem_univ x) 0
    simpa [orbitK, Flow.map_zero_apply] using this
  · intro h
    exact eq_univ_of_forall fun x ↦ (C.mem_Sing_iff x).2 fun t ↦ h _

/-- If the potential is negative somewhere then the regular set is nonempty. -/
theorem Reg_nonempty_of_exists_neg (h : ∃ x, C.K x < 0) : C.Reg.Nonempty := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x, fun hs ↦ ?_⟩
  have := (C.mem_Sing_iff x).1 hs 0
  simp only [orbitK, Flow.map_zero_apply] at this
  linarith

/-! ### `surf:transversality-rates` -/

/-- At a regular point the two rates are not both zero; since both are nonnegative this is the
transversality `u^u > u^s` of the stable and unstable directions. -/
theorem lamU_add_lamS_pos_iff (v : X) : 0 < C.lamU v + C.lamS v ↔ v ∈ C.Reg := by
  have h1 := C.lamU_nonneg v
  have h2 := C.lamS_nonneg v
  change _ ↔ ¬(C.lamU v = 0 ∧ C.lamS v = 0)
  constructor
  · rintro h ⟨a, b⟩
    linarith
  · intro h
    by_contra h'
    exact h ⟨by linarith, by linarith⟩

/-- At a regular point at least one of the two rates is positive. -/
theorem lamU_pos_or_lamS_pos_of_mem_Reg {v : X} (hv : v ∈ C.Reg) :
    0 < C.lamU v ∨ 0 < C.lamS v := by
  have h := (C.lamU_add_lamS_pos_iff v).2 hv
  by_contra h'
  push Not at h'
  linarith

end CurvatureFlow

end Kolmogorov.PointToSet
