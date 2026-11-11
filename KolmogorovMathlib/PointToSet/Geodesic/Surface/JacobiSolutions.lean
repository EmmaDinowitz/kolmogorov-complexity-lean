/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.FlowInterface
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Scalar Jacobi solutions along a continuous flow

Part 1 of `/home/user/geometry_formalization_blueprint.md`, first half (node
`surf:riccati-solutions`): the standing data `CurvatureFlow` (a `FlowData` with a continuous
nonpositive potential `K`), the scalar Jacobi equation `y'' + K (φ t v) y = 0` along orbits, its
normalized solutions `jacobiFrom`/`jacobiTo` vanishing at a prescribed time, and their logarithmic
derivatives `logDerivFrom`/`logDerivTo`, the Riccati solutions with a pole. The rates obtained as
limits of these, and the singular set, are in `Surface/Riccati.lean`.

## Main results

* Existence and uniqueness of Jacobi solutions with prescribed data (Picard–Lindelöf and
  Grönwall), linearity, constant Wronskian, naturality under the flow and under time reversal.
* Positivity and convexity after a simple zero (`IsJacobiSolution.pos_of_zero_at`).
* The Riccati equation for the logarithmic derivatives, their signs, Sturm comparison in the pole
  (`logDerivFrom_mono_pole`, `logDerivTo_mono_pole`), the comparison bound
  `logDerivFrom v s t ≤ 1 / (t - s) + Λ`, and continuity in the base point.

## References

* P. Eberlein, *When is a geodesic flow of Anosov type? I*, J. Differential Geom. 8 (1973), §2.
* W. Ballmann, *Lectures on spaces of nonpositive curvature*, Chapter IV.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-! ### `surf:riccati-solutions`: standing data -/

/-- A continuous flow on a compact metric space together with a continuous nonpositive potential
`K`, the "curvature along the orbit". Blueprint node `surf:riccati-solutions`. -/
structure CurvatureFlow (X : Type*) [MetricSpace X] [CompactSpace X] extends FlowData X where
  /-- The potential (the Gaussian curvature at the base point, for a surface). -/
  K : X → ℝ
  /-- The potential is continuous. -/
  continuous_K : Continuous K
  /-- The potential is nonpositive (nonpositive curvature). -/
  K_nonpos : ∀ x, K x ≤ 0

namespace CurvatureFlow

variable (C : CurvatureFlow X)

/-- The potential along the orbit of `v`. -/
def orbitK (v : X) (t : ℝ) : ℝ := C.K (C.φ t v)

/-- The potential along the orbit of `v` is continuous in time. -/
theorem continuous_orbitK (v : X) : Continuous (C.orbitK v) :=
  C.continuous_K.comp (C.φ.continuous continuous_id continuous_const)

/-- The potential along orbits is jointly continuous in the base point and the time. -/
theorem continuous_orbitK_uncurry : Continuous fun p : X × ℝ ↦ C.orbitK p.1 p.2 :=
  C.continuous_K.comp (C.φ.continuous continuous_snd continuous_fst)

/-- The potential along every orbit is nonpositive. -/
theorem orbitK_nonpos (v : X) (t : ℝ) : C.orbitK v t ≤ 0 :=
  C.K_nonpos _

/-- The potential along the orbit of `φ s v` at time `t` is the potential along the orbit of
`v` at time `t + s`. -/
theorem orbitK_flow (v : X) (s t : ℝ) : C.orbitK (C.φ s v) t = C.orbitK v (t + s) := by
  rw [orbitK, orbitK, Flow.map_add]

/-- The time-reversed data: the same potential along the reversed flow. Stable quantities of
`C` are unstable quantities of `C.reverse`. -/
def reverse : CurvatureFlow X where
  φ := C.φ.reverse
  L := C.L
  one_le_L := C.one_le_L
  lipschitz_unit := fun s hs x y ↦ by
    simpa [Flow.reverse_apply] using C.lipschitz_unit (-s) (by rwa [abs_neg]) x y
  V := C.V
  V_nonneg := C.V_nonneg
  speed_unit := fun s hs y ↦ by
    simpa [Flow.reverse_apply, abs_neg] using C.speed_unit (-s) (by rwa [abs_neg]) y
  K := C.K
  continuous_K := C.continuous_K
  K_nonpos := C.K_nonpos

/-- The potential along an orbit of the reversed flow is the original one read backwards in time. -/
theorem reverse_orbitK (v : X) (t : ℝ) : C.reverse.orbitK v t = C.orbitK v (-t) :=
  rfl

/-- The supremum of `-K`, a nonnegative bound on the potential. -/
noncomputable def Kbound : ℝ := sSup (range fun x ↦ -C.K x)

/-- The bound `sup (-K)` on the potential is nonnegative. -/
theorem Kbound_nonneg : 0 ≤ C.Kbound := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · simp [Kbound, Set.range_eq_empty, Real.sSup_empty]
  · exact (neg_nonneg.2 (C.K_nonpos x)).trans
      (le_csSup (isCompact_range C.continuous_K.neg).bddAbove ⟨x, rfl⟩)

/-- Every value of `-K` is at most `Kbound`. -/
theorem neg_K_le_Kbound (x : X) : -C.K x ≤ C.Kbound :=
  le_csSup (isCompact_range C.continuous_K.neg).bddAbove ⟨x, rfl⟩

/-- The common bound `Λ = √(sup (-K))` of the rates. -/
noncomputable def Λ : ℝ := Real.sqrt C.Kbound

/-- The rate bound `Λ` is nonnegative. -/
theorem Λ_nonneg : 0 ≤ C.Λ := Real.sqrt_nonneg _

/-! ### Jacobi solutions along an orbit -/

/-- `y` solves `y'' + K (φ t v) y = 0` on `ℝ`, with `y'` its derivative. -/
structure IsJacobiSolution (v : X) (y y' : ℝ → ℝ) : Prop where
  /-- `y'` is the derivative of `y`. -/
  hasDerivAt : ∀ t, HasDerivAt y (y' t) t
  /-- The Jacobi equation. -/
  hasDerivAt' : ∀ t, HasDerivAt y' (-C.orbitK v t * y t) t

/-- The first-order system `(y, y') ↦ (y', q t * y)` of the scalar equation `y'' = q t * y`. -/
private def aux1_linField (q : ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.2, q t * p.1)

/-- The Lipschitz constant `max 1 M` of the first-order system, as a real number. -/
private lemma aux1_one_le_max (M : ℝ) : (0 : ℝ) ≤ max 1 M :=
  zero_le_one.trans (le_max_left _ _)

/-- The first-order system is Lipschitz in the state, uniformly in time. -/
private lemma aux1_lipschitzWith_linField {q : ℝ → ℝ} {M : ℝ} (hM : ∀ t, |q t| ≤ M) (t : ℝ) :
    LipschitzWith (Real.toNNReal (max 1 M)) (aux1_linField q t) := by
  refine LipschitzWith.of_dist_le_mul fun p p' ↦ ?_
  rw [Real.coe_toNNReal _ (aux1_one_le_max M)]
  simp only [aux1_linField, Prod.dist_eq, Real.dist_eq]
  have h0 : 0 ≤ max |p.1 - p'.1| |p.2 - p'.2| := (abs_nonneg _).trans (le_max_left _ _)
  refine max_le ?_ ?_
  · exact (le_max_right _ _).trans (le_mul_of_one_le_left h0 (le_max_left _ _))
  · rw [← mul_sub, abs_mul]
    exact mul_le_mul ((hM t).trans (le_max_right _ _)) (le_max_left _ _) (abs_nonneg _)
      (aux1_one_le_max M)

/-- Linear growth of the first-order system. -/
private lemma aux1_norm_linField_le {q : ℝ → ℝ} {M : ℝ} (hM : ∀ t, |q t| ≤ M) (t : ℝ)
    (p : ℝ × ℝ) : ‖aux1_linField q t p‖ ≤ max 1 M * ‖p‖ := by
  have := (aux1_lipschitzWith_linField hM t).dist_le_mul p 0
  rw [Real.coe_toNNReal _ (aux1_one_le_max M)] at this
  have h0 : aux1_linField q t 0 = 0 := by simp [aux1_linField]
  rwa [h0, dist_zero_right, dist_zero_right] at this

/-- Uniqueness for the scalar linear equation `y'' = q t * y` with bounded `q` (Grönwall). -/
private lemma aux1_linear_unique {q : ℝ → ℝ} {M : ℝ} (hM : ∀ t, |q t| ≤ M)
    {y₁ y₁' y₂ y₂' : ℝ → ℝ} (h₁ : ∀ t, HasDerivAt y₁ (y₁' t) t)
    (h₁' : ∀ t, HasDerivAt y₁' (q t * y₁ t) t) (h₂ : ∀ t, HasDerivAt y₂ (y₂' t) t)
    (h₂' : ∀ t, HasDerivAt y₂' (q t * y₂ t) t) {s : ℝ} (hy : y₁ s = y₂ s)
    (hy' : y₁' s = y₂' s) : y₁ = y₂ ∧ y₁' = y₂' := by
  have := ODE_solution_unique_univ (v := aux1_linField q) (s := fun _ ↦ univ) (t₀ := s)
    (fun t ↦ (aux1_lipschitzWith_linField hM t).lipschitzOnWith)
    (fun t ↦ ⟨(h₁ t).prodMk (h₁' t), trivial⟩) (fun t ↦ ⟨(h₂ t).prodMk (h₂' t), trivial⟩)
    (Prod.ext hy hy')
  exact ⟨funext fun t ↦ congrArg Prod.fst (congrFun this t),
    funext fun t ↦ congrArg Prod.snd (congrFun this t)⟩

/-- Clamping to `[-R, R]`. -/
private def aux1_clamp (R x : ℝ) : ℝ := max (-R) (min R x)

private lemma aux1_lipschitzWith_clamp (R : ℝ) : LipschitzWith 1 (aux1_clamp R) :=
  (LipschitzWith.id.const_min R).const_max (-R)

/-- Clamping is bounded by `R` and does not increase absolute values. -/
private lemma aux1_abs_clamp_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    |aux1_clamp R x| ≤ R ∧ |aux1_clamp R x| ≤ |x| := by
  refine ⟨abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩, ?_⟩
  have h0 : aux1_clamp R 0 = 0 := by simp [aux1_clamp, hR]
  have := (aux1_lipschitzWith_clamp R).dist_le_mul x 0
  simpa [h0, Real.dist_eq] using this

/-- Clamping does nothing inside `[-R, R]`. -/
private lemma aux1_clamp_eq {R x : ℝ} (hx : |x| ≤ R) : aux1_clamp R x = x := by
  unfold aux1_clamp
  rw [abs_le] at hx
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Local (on `[s - n, s + n]`) existence for `y'' = q t * y`: Picard–Lindelöf for the system
with the state clamped to a box, then a Grönwall bound showing that the clamp is inactive. -/
private lemma aux1_linear_exists_Icc {q : ℝ → ℝ} (hq : Continuous q) {M : ℝ}
    (hM : ∀ t, |q t| ≤ M) (s : ℝ) (x₀ : ℝ × ℝ) (n : ℕ) :
    ∃ α : ℝ → ℝ × ℝ, α s = x₀ ∧ ∀ t ∈ Icc (s - n) (s + n),
      HasDerivWithinAt α (aux1_linField q t (α t)) (Icc (s - n) (s + n)) t := by
  set K' : ℝ := max 1 M with hK'
  have hK'0 : 0 ≤ K' := aux1_one_le_max M
  set R : ℝ := ‖x₀‖ * Real.exp (K' * n) with hR
  have hR0 : 0 ≤ R := by positivity
  set c : ℝ × ℝ → ℝ × ℝ := fun p ↦ (aux1_clamp R p.1, aux1_clamp R p.2) with hc
  set g : ℝ → ℝ × ℝ → ℝ × ℝ := fun t p ↦ aux1_linField q t (c p) with hg
  have hclip : LipschitzWith 1 c := by
    simpa using ((aux1_lipschitzWith_clamp R).comp LipschitzWith.prod_fst).prodMk
      ((aux1_lipschitzWith_clamp R).comp LipschitzWith.prod_snd)
  have hglip (t : ℝ) : LipschitzWith (Real.toNNReal K') (g t) := by
    have := (aux1_lipschitzWith_linField hM t).comp hclip
    rw [mul_one] at this
    exact this
  have hcnorm (p : ℝ × ℝ) : ‖c p‖ ≤ ‖p‖ ∧ ‖c p‖ ≤ R := by
    simp only [hc, Prod.norm_def, Real.norm_eq_abs]
    exact ⟨max_le_max (aux1_abs_clamp_le hR0 _).2 (aux1_abs_clamp_le hR0 _).2,
      max_le (aux1_abs_clamp_le hR0 _).1 (aux1_abs_clamp_le hR0 _).1⟩
  have hgnorm (t : ℝ) (p : ℝ × ℝ) : ‖g t p‖ ≤ K' * ‖p‖ :=
    (aux1_norm_linField_le hM t (c p)).trans (mul_le_mul_of_nonneg_left (hcnorm p).1 hK'0)
  have hgbound (t : ℝ) (p : ℝ × ℝ) : ‖g t p‖ ≤ K' * R :=
    (aux1_norm_linField_le hM t (c p)).trans (mul_le_mul_of_nonneg_left (hcnorm p).2 hK'0)
  have hsmem : s ∈ Icc (s - n) (s + n) := ⟨by linarith [n.cast_nonneg (α := ℝ)],
    by linarith [n.cast_nonneg (α := ℝ)]⟩
  have hPL : IsPicardLindelof g (tmin := s - n) (tmax := s + n) ⟨s, hsmem⟩ x₀
      (Real.toNNReal (K' * R) * n) 0 (Real.toNNReal (K' * R)) (Real.toNNReal K') := by
    refine ⟨fun t _ ↦ (hglip t).lipschitzOnWith, fun x _ ↦ ?_, fun t _ x _ ↦ ?_, ?_⟩
    · exact (continuous_const.prodMk (hq.mul continuous_const)).continuousOn
    · rw [Real.coe_toNNReal _ (by positivity)]; exact hgbound t x
    · simp
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hαc : ContinuousOn α (Icc (s - n) (s + n)) := fun t ht ↦ (hα t ht).continuousWithinAt
  -- forward Grönwall bound
  have hfwd : ∀ t ∈ Icc s (s + n), ‖α t‖ ≤ R := by
    intro t ht
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := α) (f' := fun t ↦ g t (α t))
      (δ := ‖x₀‖) (K := K') (ε := 0) (a := s) (b := s + n)
      (hαc.mono (Icc_subset_Icc_left (by linarith [n.cast_nonneg (α := ℝ)])))
      (fun x hx ↦ (hα x ⟨by linarith [hx.1, n.cast_nonneg (α := ℝ)], hx.2.le⟩)
        |>.mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨by linarith [hx.1, n.cast_nonneg (α := ℝ)], hx.2⟩))
      (by simp [hα0]) (fun x _ ↦ by simpa using hgnorm x (α x)) t ht
    rw [gronwallBound_ε0] at this
    refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) hK'0
  -- backward Grönwall bound, via `t ↦ α (-t)`
  have hbwd : ∀ t ∈ Icc (s - n) s, ‖α t‖ ≤ R := by
    intro t ht
    have hmaps : MapsTo (fun x : ℝ ↦ -x) (Icc (-s - n) (-s + n)) (Icc (s - n) (s + n)) :=
      fun x hx ↦ ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun x ↦ α (-x))
      (f' := fun x ↦ (-1 : ℝ) • g (-x) (α (-x)))
      (δ := ‖x₀‖) (K := K') (ε := 0) (a := -s) (b := -s + n)
      (hαc.comp continuousOn_neg (fun x hx ↦ ⟨by linarith [hx.2], by
        linarith [hx.1, n.cast_nonneg (α := ℝ)]⟩))
      (fun x hx ↦ by
        have hx' : x ∈ Icc (-s - n) (-s + n) :=
          ⟨by linarith [hx.1, n.cast_nonneg (α := ℝ)], hx.2.le⟩
        exact ((hα (-x) (hmaps hx')).scomp x (hasDerivAt_neg x).hasDerivWithinAt
          hmaps).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨by linarith [hx.1, n.cast_nonneg (α := ℝ)], hx.2⟩))
      (by simp [hα0]) (fun x _ ↦ by simpa using hgnorm (-x) (α (-x))) (-t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [gronwallBound_ε0, neg_neg] at this
    refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left (by linarith [ht.1]) hK'0
  refine ⟨α, hα0, fun t ht ↦ ?_⟩
  have hb : ‖α t‖ ≤ R := by
    rcases le_total t s with h | h
    · exact hbwd t ⟨ht.1, h⟩
    · exact hfwd t ⟨h, ht.2⟩
  have hct : c (α t) = α t := by
    have h1 : |(α t).1| ≤ R := (le_max_left _ _).trans (by simpa [Prod.norm_def] using hb)
    have h2 : |(α t).2| ≤ R := (le_max_right _ _).trans (by simpa [Prod.norm_def] using hb)
    simp [hc, aux1_clamp_eq h1, aux1_clamp_eq h2]
  have := hα t ht
  simp only [hg, hct] at this
  exact this

/-- Global existence for `y'' = q t * y` with continuous bounded `q`: the solutions on the
intervals `[s - n, s + n]` agree on overlaps (uniqueness), and are glued together. -/
private lemma aux1_linear_exists {q : ℝ → ℝ} (hq : Continuous q) {M : ℝ}
    (hM : ∀ t, |q t| ≤ M) (s a b : ℝ) :
    ∃ y y' : ℝ → ℝ, (∀ t, HasDerivAt y (y' t) t) ∧ (∀ t, HasDerivAt y' (q t * y t) t) ∧
      y s = a ∧ y' s = b := by
  choose α hα0 hα using fun n : ℕ ↦ aux1_linear_exists_Icc hq hM s (a, b) n
  have hint {n : ℕ} {t : ℝ} (ht : t ∈ Ioo (s - n) (s + n)) :
      HasDerivAt (α n) (aux1_linField q t (α n t)) t :=
    (hα n t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hagree : ∀ m n : ℕ, 1 ≤ m → m ≤ n → EqOn (α m) (α n) (Icc (s - m) (s + m)) := by
    intro m n hm hmn
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hsub : Ioo (s - m) (s + m) ⊆ Ioo (s - n) (s + n) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    refine ODE_solution_unique_of_mem_Icc (v := aux1_linField q) (s := fun _ ↦ univ)
      (fun t _ ↦ (aux1_lipschitzWith_linField hM t).lipschitzOnWith)
      (t₀ := s) ⟨by linarith, by linarith⟩
      (fun t ht ↦ (hα m t ht).continuousWithinAt) (fun t ht ↦ hint ht) (fun _ _ ↦ trivial)
      (fun t ht ↦ ((hα n t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousWithinAt).mono
        (Icc_subset_Icc (by linarith) (by linarith)))
      (fun t ht ↦ hint (hsub ht)) (fun _ _ ↦ trivial) ?_
    rw [hα0, hα0]
  set N : ℝ → ℕ := fun t ↦ ⌈|t - s|⌉₊ + 1 with hN
  set Y : ℝ → ℝ × ℝ := fun t ↦ α (N t) t with hY
  have hYd (t : ℝ) : HasDerivAt Y (aux1_linField q t (Y t)) t := by
    set n : ℕ := ⌈|t - s|⌉₊ + 2 with hn
    have hceil : |t - s| ≤ ⌈|t - s|⌉₊ := Nat.le_ceil _
    have hev : Y =ᶠ[𝓝 t] α n := by
      filter_upwards [Ioo_mem_nhds (show t - 1 < t by linarith) (show t < t + 1 by linarith)]
        with t' ht'
      have h1 : |t' - s| ≤ |t - s| + 1 := by
        have := abs_sub_abs_le_abs_sub (t' - s) (t - s)
        have h2 : |t' - s - (t - s)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [ht'.1, ht'.2]
        linarith
      have hc : ⌈|t' - s|⌉₊ ≤ ⌈|t - s|⌉₊ + 1 := by
        rw [Nat.ceil_le]; push_cast; linarith
      have hc' : |t' - s| ≤ ⌈|t' - s|⌉₊ := Nat.le_ceil _
      refine hagree (N t') n (by simp [hN]) (by simp only [hN, hn]; omega) ?_
      have := abs_le.1 hc'
      simp only [hN]; push_cast
      constructor <;> linarith [this.1, this.2]
    have hmem : t ∈ Ioo (s - n) (s + n) := by
      have := abs_le.1 hceil
      simp only [hn]; push_cast
      constructor <;> linarith [this.1, this.2]
    have := (hint hmem).congr_of_eventuallyEq hev
    rw [hev.eq_of_nhds]
    exact this
  refine ⟨fun t ↦ (Y t).1, fun t ↦ (Y t).2, fun t ↦ ?_, fun t ↦ ?_, ?_, ?_⟩
  · exact hasFDerivAt_fst.comp_hasDerivAt t (hYd t)
  · exact hasFDerivAt_snd.comp_hasDerivAt t (hYd t)
  · simp [hY, hα0]
  · simp [hY, hα0]

/-- The potential along an orbit is bounded by `Kbound`. -/
private lemma aux1_abs_neg_orbitK_le (C : CurvatureFlow X) (v : X) (t : ℝ) :
    |-C.orbitK v t| ≤ C.Kbound := by
  rw [abs_neg, abs_of_nonpos (C.orbitK_nonpos v t)]
  exact C.neg_K_le_Kbound _

/-- Existence of Jacobi solutions with prescribed value and derivative at any time (a linear
equation with continuous coefficients has global solutions). -/
theorem exists_isJacobiSolution (v : X) (s a b : ℝ) :
    ∃ y y' : ℝ → ℝ, C.IsJacobiSolution v y y' ∧ y s = a ∧ y' s = b := by
  obtain ⟨y, y', h, h', hs, hs'⟩ := aux1_linear_exists (q := fun t ↦ -C.orbitK v t)
    (C.continuous_orbitK v).neg (aux1_abs_neg_orbitK_le C v) s a b
  exact ⟨y, y', ⟨h, h'⟩, hs, hs'⟩

section solutions

variable {C}

/-- Uniqueness of Jacobi solutions with the same data at one time (Grönwall). -/
theorem IsJacobiSolution.unique {v : X} {y₁ y₁' y₂ y₂' : ℝ → ℝ}
    (h₁ : C.IsJacobiSolution v y₁ y₁') (h₂ : C.IsJacobiSolution v y₂ y₂') {s : ℝ}
    (hy : y₁ s = y₂ s) (hy' : y₁' s = y₂' s) : y₁ = y₂ ∧ y₁' = y₂' :=
  aux1_linear_unique (q := fun t ↦ -C.orbitK v t) (aux1_abs_neg_orbitK_le C v) h₁.hasDerivAt
    h₁.hasDerivAt' h₂.hasDerivAt h₂.hasDerivAt' hy hy'

/-- The solution space is linear. -/
theorem IsJacobiSolution.add_smul {v : X} {y₁ y₁' y₂ y₂' : ℝ → ℝ}
    (h₁ : C.IsJacobiSolution v y₁ y₁') (h₂ : C.IsJacobiSolution v y₂ y₂') (a b : ℝ) :
    C.IsJacobiSolution v (fun t ↦ a * y₁ t + b * y₂ t) (fun t ↦ a * y₁' t + b * y₂' t) := by
  refine ⟨fun t ↦ ((h₁.hasDerivAt t).const_mul a).add ((h₂.hasDerivAt t).const_mul b),
    fun t ↦ ?_⟩
  convert ((h₁.hasDerivAt' t).const_mul a).add ((h₂.hasDerivAt' t).const_mul b) using 1
  ring

/-- The Wronskian of two Jacobi solutions is constant. -/
theorem IsJacobiSolution.wronskian_eq {v : X} {y₁ y₁' y₂ y₂' : ℝ → ℝ}
    (h₁ : C.IsJacobiSolution v y₁ y₁') (h₂ : C.IsJacobiSolution v y₂ y₂') (s t : ℝ) :
    y₁ t * y₂' t - y₁' t * y₂ t = y₁ s * y₂' s - y₁' s * y₂ s := by
  have hW (τ : ℝ) : HasDerivAt (fun τ ↦ y₁ τ * y₂' τ - y₁' τ * y₂ τ) 0 τ := by
    convert ((h₁.hasDerivAt τ).mul (h₂.hasDerivAt' τ)).sub
      ((h₁.hasDerivAt' τ).mul (h₂.hasDerivAt τ)) using 1
    ring
  exact is_const_of_deriv_eq_zero (fun τ ↦ (hW τ).differentiableAt) (fun τ ↦ (hW τ).deriv) t s

/-- Solutions shift along the flow: a solution along `v` read from time `s` is a solution along
`φ s v`. -/
theorem IsJacobiSolution.comp_add {v : X} {y y' : ℝ → ℝ} (h : C.IsJacobiSolution v y y')
    (s : ℝ) : C.IsJacobiSolution (C.φ s v) (fun t ↦ y (t + s)) (fun t ↦ y' (t + s)) := by
  refine ⟨fun t ↦ (h.hasDerivAt (t + s)).comp_add_const t s, fun t ↦ ?_⟩
  rw [C.orbitK_flow]
  exact (h.hasDerivAt' (t + s)).comp_add_const t s

/-- Time reversal of a solution, for two potentials that are reverses of each other along `v`. -/
private lemma aux1_isJacobiSolution_neg {C₁ C₂ : CurvatureFlow X} {v : X}
    (hK : ∀ t, C₂.orbitK v t = C₁.orbitK v (-t)) {y y' : ℝ → ℝ}
    (h : C₁.IsJacobiSolution v y y') :
    C₂.IsJacobiSolution v (fun t ↦ y (-t)) (fun t ↦ -y' (-t)) := by
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · have := (h.hasDerivAt (-t)).comp t (hasDerivAt_neg t)
    rw [mul_neg_one] at this
    exact this
  · have := ((h.hasDerivAt' (-t)).comp t (hasDerivAt_neg t)).neg
    rw [hK]
    convert this using 1
    · funext τ; simp
    · ring

/-- Time reversal of a solution. -/
theorem IsJacobiSolution.reverse {v : X} {y y' : ℝ → ℝ} (h : C.IsJacobiSolution v y y') :
    C.reverse.IsJacobiSolution v (fun t ↦ y (-t)) (fun t ↦ -y' (-t)) :=
  aux1_isJacobiSolution_neg (fun t ↦ C.reverse_orbitK v t) h

/-- A function with a nonnegative derivative on the interior of a convex set is monotone there. -/
private lemma aux1_monotoneOn_of_hasDerivAt {f f' : ℝ → ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (hf : ∀ x, HasDerivAt f (f' x) x) (h : ∀ x ∈ interior D, 0 ≤ f' x) : MonotoneOn f D :=
  monotoneOn_of_hasDerivWithinAt_nonneg hD (fun x _ ↦ (hf x).continuousAt.continuousWithinAt)
    (fun x _ ↦ (hf x).hasDerivWithinAt) h

/-- `y'` is nondecreasing on an order-connected set where `y ≥ 0` (since `y'' = -K y ≥ 0`
there). -/
theorem IsJacobiSolution.deriv_monotoneOn_of_nonneg {v : X} {y y' : ℝ → ℝ}
    (h : C.IsJacobiSolution v y y') {I : Set ℝ} (hI : I.OrdConnected) (hy : ∀ t ∈ I, 0 ≤ y t) :
    MonotoneOn y' I :=
  aux1_monotoneOn_of_hasDerivAt hI.convex h.hasDerivAt' fun x hx ↦
    mul_nonneg (neg_nonneg.2 (C.orbitK_nonpos v x)) (hy x (interior_subset hx))

/-- Convexity after a simple zero: a solution with `y s = 0`, `y' s = 1` is positive with
derivative at least `1` after `s` (`K ≤ 0` makes `y` convex while positive). -/
theorem IsJacobiSolution.pos_of_zero_at {v : X} {y y' : ℝ → ℝ} (h : C.IsJacobiSolution v y y')
    {s : ℝ} (hs : y s = 0) (hs' : y' s = 1) {t : ℝ} (ht : s < t) : 0 < y t ∧ 1 ≤ y' t := by
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun τ ↦ (h.hasDerivAt τ).continuousAt
  have hy'c : Continuous y' :=
    continuous_iff_continuousAt.2 fun τ ↦ (h.hasDerivAt' τ).continuousAt
  set P : Set ℝ := {r | 0 ≤ y r ∧ 1 ≤ y' r} with hP
  have hPc : IsClosed P :=
    (isClosed_le continuous_const hyc).inter (isClosed_le continuous_const hy'c)
  have hsub : Icc s t ⊆ P := by
    refine (hPc.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin ⟨hs.ge, hs'.ge⟩ ?_
    rintro r ⟨⟨hr0, hr1⟩, -⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      ((hy'c.continuousAt (x := r)).eventually (lt_mem_nhds (show (0 : ℝ) < y' r by linarith)))
    have hD : Ico r (r + ε) ⊆ Metric.ball r ε := fun x hx ↦ by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have hmono : MonotoneOn y (Ico r (r + ε)) :=
      aux1_monotoneOn_of_hasDerivAt (convex_Ico _ _) h.hasDerivAt fun x hx ↦
        (hball (hD (interior_subset hx))).le
    have hnn : ∀ x ∈ Ico r (r + ε), 0 ≤ y x := fun x hx ↦
      hr0.trans (hmono ⟨le_rfl, by linarith⟩ hx hx.1)
    have hmono' := h.deriv_monotoneOn_of_nonneg ordConnected_Ico hnn
    refine mem_of_superset (Ico_mem_nhdsGT (show r < r + ε by linarith)) fun x hx ↦ ?_
    exact ⟨hnn x hx, hr1.trans (hmono' ⟨le_rfl, by linarith⟩ hx hx.1)⟩
  have hg : MonotoneOn (fun τ ↦ y τ - (τ - s)) (Icc s t) :=
    aux1_monotoneOn_of_hasDerivAt (f' := fun τ ↦ y' τ - 1) (convex_Icc _ _)
      (fun τ ↦ (h.hasDerivAt τ).sub ((hasDerivAt_id τ).sub_const s)) fun x hx ↦
        sub_nonneg.2 (hsub (interior_subset hx)).2
  have := hg ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht.le
  refine ⟨?_, (hsub ⟨ht.le, le_rfl⟩).2⟩
  simp only [hs, sub_self] at this
  linarith

end solutions

/-! ### The normalized solutions `jacobiFrom` and `jacobiTo` -/

/-- The Jacobi solution along `v` with `y s = 0`, `y' s = 1`. -/
noncomputable def jacobiFrom (v : X) (s : ℝ) : ℝ → ℝ :=
  Classical.choose (C.exists_isJacobiSolution v s 0 1)

/-- The derivative of `jacobiFrom`. -/
noncomputable def jacobiFrom' (v : X) (s : ℝ) : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec (C.exists_isJacobiSolution v s 0 1))

/-- `jacobiFrom v s` solves the Jacobi equation along `v`, with derivative `jacobiFrom' v s`. -/
theorem isJacobiSolution_jacobiFrom (v : X) (s : ℝ) :
    C.IsJacobiSolution v (C.jacobiFrom v s) (C.jacobiFrom' v s) :=
  (Classical.choose_spec (Classical.choose_spec (C.exists_isJacobiSolution v s 0 1))).1

/-- `jacobiFrom v s` vanishes at time `s`. -/
theorem jacobiFrom_self (v : X) (s : ℝ) : C.jacobiFrom v s s = 0 :=
  (Classical.choose_spec (Classical.choose_spec (C.exists_isJacobiSolution v s 0 1))).2.1

/-- The derivative of `jacobiFrom v s` equals `1` at time `s`. -/
theorem jacobiFrom'_self (v : X) (s : ℝ) : C.jacobiFrom' v s s = 1 :=
  (Classical.choose_spec (Classical.choose_spec (C.exists_isJacobiSolution v s 0 1))).2.2

/-- `jacobiFrom v s` is positive at every time after `s`. -/
theorem jacobiFrom_pos (v : X) {s t : ℝ} (h : s < t) : 0 < C.jacobiFrom v s t :=
  ((C.isJacobiSolution_jacobiFrom v s).pos_of_zero_at (C.jacobiFrom_self v s)
    (C.jacobiFrom'_self v s) h).1

/-- The derivative of `jacobiFrom v s` is at least `1` at every time after `s`. -/
theorem one_le_jacobiFrom' (v : X) {s t : ℝ} (h : s < t) : 1 ≤ C.jacobiFrom' v s t :=
  ((C.isJacobiSolution_jacobiFrom v s).pos_of_zero_at (C.jacobiFrom_self v s)
    (C.jacobiFrom'_self v s) h).2

/-- `jacobiFrom v s` is at least `t - s` after its zero. -/
private lemma aux1_sub_le_jacobiFrom (v : X) {s t : ℝ} (h : s ≤ t) :
    t - s ≤ C.jacobiFrom v s t := by
  have hg : MonotoneOn (fun τ ↦ C.jacobiFrom v s τ - (τ - s)) (Ici s) :=
    aux1_monotoneOn_of_hasDerivAt (f' := fun τ ↦ C.jacobiFrom' v s τ - 1) (convex_Ici _)
      (fun τ ↦ ((C.isJacobiSolution_jacobiFrom v s).hasDerivAt τ).sub
        ((hasDerivAt_id τ).sub_const s)) fun x hx ↦ by
        rw [interior_Ici] at hx
        exact sub_nonneg.2 (C.one_le_jacobiFrom' v hx)
  have := hg (mem_Ici.2 le_rfl) h h
  simp only [C.jacobiFrom_self, sub_self] at this
  linarith

/-- `jacobiFrom v s` is nondecreasing after its zero. -/
private lemma aux1_jacobiFrom_monotoneOn (v : X) (s : ℝ) :
    MonotoneOn (C.jacobiFrom v s) (Ici s) :=
  aux1_monotoneOn_of_hasDerivAt (convex_Ici _) (C.isJacobiSolution_jacobiFrom v s).hasDerivAt
    fun x hx ↦ by
      rw [interior_Ici] at hx
      exact zero_le_one.trans (C.one_le_jacobiFrom' v hx)

/-- `jacobiFrom` and its derivative are natural under the flow. -/
private lemma aux1_jacobiFrom_flow (v : X) (r s : ℝ) :
    C.jacobiFrom (C.φ r v) s = (fun t ↦ C.jacobiFrom v (s + r) (t + r)) ∧
      C.jacobiFrom' (C.φ r v) s = fun t ↦ C.jacobiFrom' v (s + r) (t + r) :=
  (C.isJacobiSolution_jacobiFrom (C.φ r v) s).unique
    ((C.isJacobiSolution_jacobiFrom v (s + r)).comp_add r) (s := s)
    (by simp [jacobiFrom_self]) (by simp [jacobiFrom'_self])

/-- `jacobiFrom` is natural under the flow. -/
theorem jacobiFrom_flow (v : X) (r s t : ℝ) :
    C.jacobiFrom (C.φ r v) s t = C.jacobiFrom v (s + r) (t + r) := by
  rw [(C.aux1_jacobiFrom_flow v r s).1]

/-- The Jacobi solution along `v` with `y s = 0`, `y' s = -1`, positive before `s`. -/
noncomputable def jacobiTo (v : X) (s : ℝ) : ℝ → ℝ :=
  Classical.choose (C.exists_isJacobiSolution v s 0 (-1))

/-- The derivative of `jacobiTo`. -/
noncomputable def jacobiTo' (v : X) (s : ℝ) : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec (C.exists_isJacobiSolution v s 0 (-1)))

/-- `jacobiTo v s` solves the Jacobi equation along `v`, with derivative `jacobiTo' v s`. -/
theorem isJacobiSolution_jacobiTo (v : X) (s : ℝ) :
    C.IsJacobiSolution v (C.jacobiTo v s) (C.jacobiTo' v s) :=
  (Classical.choose_spec (Classical.choose_spec (C.exists_isJacobiSolution v s 0 (-1)))).1

/-- `jacobiTo v s` vanishes at time `s`. -/
theorem jacobiTo_self (v : X) (s : ℝ) : C.jacobiTo v s s = 0 :=
  (Classical.choose_spec (Classical.choose_spec (C.exists_isJacobiSolution v s 0 (-1)))).2.1

/-- The derivative of `jacobiTo v s` equals `-1` at time `s`. -/
theorem jacobiTo'_self (v : X) (s : ℝ) : C.jacobiTo' v s s = -1 :=
  (Classical.choose_spec (Classical.choose_spec (C.exists_isJacobiSolution v s 0 (-1)))).2.2

/-- `jacobiTo` and its derivative in terms of `jacobiFrom` for the reversed flow. -/
private lemma aux1_jacobiTo_eq (v : X) (s : ℝ) :
    C.jacobiTo v s = (fun t ↦ C.reverse.jacobiFrom v (-s) (-t)) ∧
      C.jacobiTo' v s = fun t ↦ -C.reverse.jacobiFrom' v (-s) (-t) :=
  (C.isJacobiSolution_jacobiTo v s).unique
    (aux1_isJacobiSolution_neg (C₁ := C.reverse) (C₂ := C)
      (fun t ↦ by rw [C.reverse_orbitK, neg_neg])
      (C.reverse.isJacobiSolution_jacobiFrom v (-s))) (s := s)
    (by simp [jacobiTo_self, jacobiFrom_self]) (by simp [jacobiTo'_self, jacobiFrom'_self])

/-- `jacobiTo` for `C` is `jacobiFrom` for the reversed flow, read backwards. -/
theorem jacobiTo_eq_reverse_jacobiFrom (v : X) (s t : ℝ) :
    C.jacobiTo v s t = C.reverse.jacobiFrom v (-s) (-t) := by
  rw [(C.aux1_jacobiTo_eq v s).1]

/-- `jacobiTo v s` is positive at every time before `s`. -/
theorem jacobiTo_pos (v : X) {s t : ℝ} (h : t < s) : 0 < C.jacobiTo v s t := by
  rw [C.jacobiTo_eq_reverse_jacobiFrom]
  exact C.reverse.jacobiFrom_pos v (neg_lt_neg h)

/-- The derivative of `jacobiTo v s` is at most `-1` at every time before `s`. -/
theorem jacobiTo'_le_neg_one (v : X) {s t : ℝ} (h : t < s) : C.jacobiTo' v s t ≤ -1 := by
  rw [(C.aux1_jacobiTo_eq v s).2]
  exact neg_le_neg (C.reverse.one_le_jacobiFrom' v (neg_lt_neg h))

/-! ### Riccati solutions with a pole -/

/-- The logarithmic derivative `y'/y` of `jacobiFrom v s`, a solution of the Riccati equation
`u' = -u² - K` on `(s, ∞)` with a pole at `s`. -/
noncomputable def logDerivFrom (v : X) (s t : ℝ) : ℝ := C.jacobiFrom' v s t / C.jacobiFrom v s t

/-- The logarithmic derivative `y'/y` of `jacobiTo v s`, a Riccati solution on `(-∞, s)`. -/
noncomputable def logDerivTo (v : X) (s t : ℝ) : ℝ := C.jacobiTo' v s t / C.jacobiTo v s t

/-- The Riccati solution `logDerivFrom v s` is positive after its pole `s`. -/
theorem logDerivFrom_pos (v : X) {s t : ℝ} (h : s < t) : 0 < C.logDerivFrom v s t :=
  div_pos (zero_lt_one.trans_le (C.one_le_jacobiFrom' v h)) (C.jacobiFrom_pos v h)

/-- The Riccati solution `logDerivTo v s` is negative before its pole `s`. -/
theorem logDerivTo_neg (v : X) {s t : ℝ} (h : t < s) : C.logDerivTo v s t < 0 :=
  div_neg_of_neg_of_pos ((C.jacobiTo'_le_neg_one v h).trans_lt (by norm_num))
    (C.jacobiTo_pos v h)

/-- The Riccati equation for the logarithmic derivative of a Jacobi solution where it is
nonzero. -/
private lemma aux1_hasDerivAt_div {v : X} {y y' : ℝ → ℝ} (h : C.IsJacobiSolution v y y')
    {t : ℝ} (ht : y t ≠ 0) :
    HasDerivAt (fun τ ↦ y' τ / y τ) (-(y' t / y t) ^ 2 - C.orbitK v t) t := by
  convert (h.hasDerivAt' t).div (h.hasDerivAt t) ht using 1
  field_simp
  ring

/-- The Riccati equation for `logDerivFrom` after the pole. -/
theorem hasDerivAt_logDerivFrom (v : X) {s t : ℝ} (h : s < t) :
    HasDerivAt (C.logDerivFrom v s) (-(C.logDerivFrom v s t) ^ 2 - C.orbitK v t) t :=
  C.aux1_hasDerivAt_div (C.isJacobiSolution_jacobiFrom v s) (C.jacobiFrom_pos v h).ne'

/-- The Riccati equation for `logDerivTo` before the pole. -/
theorem hasDerivAt_logDerivTo (v : X) {s t : ℝ} (h : t < s) :
    HasDerivAt (C.logDerivTo v s) (-(C.logDerivTo v s t) ^ 2 - C.orbitK v t) t :=
  C.aux1_hasDerivAt_div (C.isJacobiSolution_jacobiTo v s) (C.jacobiTo_pos v h).ne'

/-- `logDerivFrom` is natural under the flow: along `φ r v` it is the solution along `v` with
pole and time shifted by `r`. -/
theorem logDerivFrom_flow (v : X) (r s t : ℝ) :
    C.logDerivFrom (C.φ r v) s t = C.logDerivFrom v (s + r) (t + r) := by
  rw [logDerivFrom, logDerivFrom, (C.aux1_jacobiFrom_flow v r s).1,
    (C.aux1_jacobiFrom_flow v r s).2]

/-- `logDerivTo` for `C` is minus `logDerivFrom` for the reversed flow, with pole and time
negated. -/
theorem logDerivTo_eq_reverse (v : X) (s t : ℝ) :
    C.logDerivTo v s t = -C.reverse.logDerivFrom v (-s) (-t) := by
  rw [logDerivTo, logDerivFrom, (C.aux1_jacobiTo_eq v s).1, (C.aux1_jacobiTo_eq v s).2, neg_div]

/-- The difference of two Riccati solutions with poles `s₁ ≤ s₂`, through the Wronskian of
`jacobiFrom v s₁` and `jacobiFrom v s₂` (evaluated at `s₂`). -/
private lemma aux1_logDerivFrom_sub_eq (v : X) {s₁ s₂ t : ℝ} (h₁ : s₁ ≤ s₂) (h₂ : s₂ < t) :
    C.logDerivFrom v s₂ t - C.logDerivFrom v s₁ t =
      C.jacobiFrom v s₁ s₂ / (C.jacobiFrom v s₁ t * C.jacobiFrom v s₂ t) := by
  have hW := (C.isJacobiSolution_jacobiFrom v s₁).wronskian_eq
    (C.isJacobiSolution_jacobiFrom v s₂) t s₂
  rw [C.jacobiFrom_self, C.jacobiFrom'_self] at hW
  have hp₁ := C.jacobiFrom_pos v (h₁.trans_lt h₂)
  have hp₂ := C.jacobiFrom_pos v h₂
  rw [logDerivFrom, logDerivFrom, div_sub_div _ _ hp₂.ne' hp₁.ne',
    mul_comm (C.jacobiFrom v s₂ t) (C.jacobiFrom v s₁ t)]
  congr 1
  linear_combination -hW

/-- Sturm comparison: an earlier pole gives a smaller Riccati solution. This is the monotonicity
of `u_T(0)` in `T` of the blueprint. -/
theorem logDerivFrom_mono_pole (v : X) {s₁ s₂ t : ℝ} (h₁ : s₁ ≤ s₂) (h₂ : s₂ < t) :
    C.logDerivFrom v s₁ t ≤ C.logDerivFrom v s₂ t := by
  have h := C.aux1_logDerivFrom_sub_eq v h₁ h₂
  have hn : 0 ≤ C.jacobiFrom v s₁ s₂ := (sub_nonneg.2 h₁).trans (C.aux1_sub_le_jacobiFrom v h₁)
  have hp₁ := C.jacobiFrom_pos v (h₁.trans_lt h₂)
  have hp₂ := C.jacobiFrom_pos v h₂
  have : 0 ≤ C.logDerivFrom v s₂ t - C.logDerivFrom v s₁ t := by rw [h]; positivity
  linarith

/-- The Cauchy estimate behind the convergence of `logDerivFrom v (-T) 0`: moving the pole from
`s₂` back to `s₁` changes the Riccati solution at `t` by at most `1 / (t - s₂)`. -/
private lemma aux1_logDerivFrom_sub_le (v : X) {s₁ s₂ t : ℝ} (h₁ : s₁ ≤ s₂) (h₂ : s₂ < t) :
    C.logDerivFrom v s₂ t - C.logDerivFrom v s₁ t ≤ 1 / (t - s₂) := by
  rw [C.aux1_logDerivFrom_sub_eq v h₁ h₂]
  have hp₁ := C.jacobiFrom_pos v (h₁.trans_lt h₂)
  have hp₂ := C.jacobiFrom_pos v h₂
  have hle : C.jacobiFrom v s₁ s₂ ≤ C.jacobiFrom v s₁ t :=
    C.aux1_jacobiFrom_monotoneOn v s₁ (mem_Ici.2 h₁) (mem_Ici.2 (h₁.trans h₂.le)) h₂.le
  have hlow := C.aux1_sub_le_jacobiFrom v h₂.le
  have hts : 0 < t - s₂ := sub_pos.2 h₂
  rw [div_le_div_iff₀ (by positivity) hts, one_mul]
  calc C.jacobiFrom v s₁ s₂ * (t - s₂) ≤ C.jacobiFrom v s₁ t * C.jacobiFrom v s₂ t :=
    mul_le_mul hle hlow hts.le hp₁.le

/-- Sturm comparison for `logDerivTo`: a later pole gives a larger value (for `K = 0`,
`logDerivTo v s t = -1 / (s - t)` increases with `s`). By time reversal from
`logDerivFrom_mono_pole`. -/
theorem logDerivTo_mono_pole (v : X) {s₁ s₂ t : ℝ} (h₁ : t < s₁) (h₂ : s₁ ≤ s₂) :
    C.logDerivTo v s₁ t ≤ C.logDerivTo v s₂ t := by
  rw [C.logDerivTo_eq_reverse, C.logDerivTo_eq_reverse, neg_le_neg_iff]
  exact C.reverse.logDerivFrom_mono_pole v (neg_le_neg h₂) (neg_lt_neg h₁)

/-- Comparison with constant curvature `-Λ²`: `u ≤ Λ coth (Λ (t - s)) ≤ 1 / (t - s) + Λ`. -/
theorem logDerivFrom_le (v : X) {s t : ℝ} (h : s < t) :
    C.logDerivFrom v s t ≤ 1 / (t - s) + C.Λ := by
  -- Wronskian of `y = jacobiFrom v s` with `z r = (r - s) exp (Λ (r - s))`, `z'' ≥ Λ² z`.
  set Λ := C.Λ with hΛdef
  have hΛ : 0 ≤ Λ := C.Λ_nonneg
  have hΛ2 : Λ ^ 2 = C.Kbound := Real.sq_sqrt C.Kbound_nonneg
  have hy := C.isJacobiSolution_jacobiFrom v s
  set y := C.jacobiFrom v s
  set y' := C.jacobiFrom' v s
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ, E = fun r ↦ Real.exp (Λ * (r - s)) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ → ℝ, z = fun r ↦ (r - s) * E r := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : ℝ → ℝ, z' = fun r ↦ E r * (1 + Λ * (r - s)) := ⟨_, rfl⟩
  obtain ⟨z'', hz''⟩ : ∃ z'' : ℝ → ℝ, z'' = fun r ↦ E r * (2 * Λ + Λ ^ 2 * (r - s)) :=
    ⟨_, rfl⟩
  have hEd (r : ℝ) : HasDerivAt E (E r * Λ) r := by
    subst hE
    exact ((((hasDerivAt_id r).sub_const s).const_mul Λ).exp).congr_deriv (by simp)
  have hzd (r : ℝ) : HasDerivAt z (z' r) r := by
    subst hz hz'
    exact (((hasDerivAt_id r).sub_const s).mul (hEd r)).congr_deriv (by simp only [id_eq]; ring)
  have hz'd (r : ℝ) : HasDerivAt z' (z'' r) r := by
    subst hz' hz''
    exact ((hEd r).mul ((((hasDerivAt_id r).sub_const s).const_mul Λ).const_add 1)).congr_deriv
      (by simp only [id_eq]; ring)
  obtain ⟨W, hW⟩ : ∃ W : ℝ → ℝ, W = fun r ↦ y' r * z r - y r * z' r := ⟨_, rfl⟩
  have hWd (r : ℝ) : HasDerivAt W (-C.orbitK v r * y r * z r - y r * z'' r) r := by
    subst hW
    exact (((hy.hasDerivAt' r).mul (hzd r)).sub ((hy.hasDerivAt r).mul (hz'd r))).congr_deriv
      (by ring)
  have hanti : AntitoneOn W (Ici s) := by
    have := aux1_monotoneOn_of_hasDerivAt (f := fun r ↦ -W r) (convex_Ici s)
      (fun r ↦ (hWd r).neg) fun r hr ↦ by
        rw [interior_Ici] at hr
        have hyr : 0 ≤ y r := (C.jacobiFrom_pos v hr).le
        have hEr : 0 < E r := by rw [hE]; exact Real.exp_pos _
        have hzr : 0 ≤ z r := by rw [hz]; exact mul_nonneg (sub_nonneg.2 (le_of_lt hr)) hEr.le
        have hK : -C.orbitK v r ≤ Λ ^ 2 := by
          rw [hΛ2, ← abs_of_nonneg (neg_nonneg.2 (C.orbitK_nonpos v r))]
          exact aux1_abs_neg_orbitK_le C v r
        have h1 : -C.orbitK v r * z r ≤ Λ ^ 2 * z r := mul_le_mul_of_nonneg_right hK hzr
        have h2 : -C.orbitK v r * z r - z'' r ≤ 0 := by
          simp only [hz, hz''] at h1 ⊢
          nlinarith [mul_nonneg hEr.le hΛ]
        have : -C.orbitK v r * y r * z r - y r * z'' r =
            y r * (-C.orbitK v r * z r - z'' r) := by ring
        rw [this]
        exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos hyr h2)
    exact fun a ha b hb hab ↦ neg_le_neg_iff.1 (this ha hb hab)
  have hWs : W s = 0 := by simp [hW, hz, y, C.jacobiFrom_self]
  have hWt : W t ≤ 0 := hWs ▸ hanti (mem_Ici.2 le_rfl) (mem_Ici.2 h.le) h.le
  have hyt : 0 < y t := C.jacobiFrom_pos v h
  have hτ : 0 < t - s := sub_pos.2 h
  have hEt : 0 < E t := by rw [hE]; exact Real.exp_pos _
  simp only [hW, hz, hz'] at hWt
  have key : y' t * (t - s) ≤ y t * (1 + Λ * (t - s)) := by nlinarith
  rw [logDerivFrom, div_le_iff₀ hyt]
  have : (1 / (t - s) + Λ) * y t = y t * (1 + Λ * (t - s)) / (t - s) := by
    field_simp
  rw [this, le_div_iff₀ hτ]
  exact key

/-- Comparison bound before the pole: `-logDerivTo v s t ≤ 1 / (s - t) + Λ` for `t < s`. -/
theorem neg_logDerivTo_le (v : X) {s t : ℝ} (h : t < s) :
    -C.logDerivTo v s t ≤ 1 / (s - t) + C.Λ := by
  rw [C.logDerivTo_eq_reverse, neg_neg]
  have := C.reverse.logDerivFrom_le v (neg_lt_neg h)
  rwa [show -t - -s = s - t by ring] at this

/-- Continuity in the base point (continuous dependence of the solution on the potential). -/
theorem continuous_logDerivFrom {s t : ℝ} (h : s < t) :
    Continuous fun v ↦ C.logDerivFrom v s t := by
  -- Grönwall comparison of the solutions for `w` and `w₀` on `[s, t]`, the solution for `w`
  -- being an approximate solution of the equation for `w₀` (uniform closeness of the potentials
  -- on `[s, t]` by compactness), with an a priori bound on the solutions.
  set K' : ℝ := max 1 C.Kbound with hK'
  have hK'0 : 0 ≤ K' := aux1_one_le_max _
  set B : ℝ := Real.exp (K' * (t - s)) with hBdef
  have hB : 0 < B := Real.exp_pos _
  obtain ⟨Y, hY⟩ : ∃ Y : X → ℝ → ℝ × ℝ,
      Y = fun w τ ↦ (C.jacobiFrom w s τ, C.jacobiFrom' w s τ) := ⟨_, rfl⟩
  have hYd (w : X) (τ : ℝ) :
      HasDerivAt (Y w) (aux1_linField (fun r ↦ -C.orbitK w r) τ (Y w τ)) τ := by
    subst hY
    exact ((C.isJacobiSolution_jacobiFrom w s).hasDerivAt τ).prodMk
      ((C.isJacobiSolution_jacobiFrom w s).hasDerivAt' τ)
  have hYc (w : X) : Continuous (Y w) :=
    continuous_iff_continuousAt.2 fun τ ↦ (hYd w τ).continuousAt
  have hYs (w : X) : Y w s = (0, 1) := by simp [hY, jacobiFrom_self, jacobiFrom'_self]
  have hYb (w : X) : ∀ τ ∈ Icc s t, ‖Y w τ‖ ≤ B := by
    intro τ hτ
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := Y w) (δ := 1) (K := K')
      (ε := 0) (a := s) (b := t) (hYc w).continuousOn (fun x _ ↦ (hYd w x).hasDerivWithinAt)
      (by simp [hYs]) (fun x _ ↦ by
        simpa using aux1_norm_linField_le (aux1_abs_neg_orbitK_le C w) x (Y w x)) τ hτ
    rw [gronwallBound_ε0, one_mul] at this
    exact this.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hτ.2]) hK'0))
  have hYt : Continuous fun w ↦ Y w t := by
    refine continuous_iff_continuousAt.2 fun w₀ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    obtain ⟨η, hη, hηε⟩ : ∃ η > 0, ∀ e, |e| < η → gronwallBound 0 K' e (t - s) < ε := by
      have hc := (gronwallBound_continuous_ε 0 K' (t - s)).continuousAt (x := 0)
      rw [Metric.continuousAt_iff] at hc
      obtain ⟨η, hη, H⟩ := hc ε hε
      refine ⟨η, hη, fun e he ↦ ?_⟩
      have := H (x := e) (by rwa [Real.dist_eq, sub_zero])
      rw [gronwallBound_ε0_δ0, Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans_lt this
    have hU := Continuous.tendstoUniformly (fun (w : X) (τ : Icc s t) ↦ C.orbitK w τ)
      (C.continuous_orbitK_uncurry.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) w₀
    rw [Metric.tendstoUniformly_iff] at hU
    filter_upwards [hU (η / (2 * B)) (by positivity)] with w hw
    have hdist := dist_le_of_approx_trajectories_ODE
      (v := aux1_linField (fun r ↦ -C.orbitK w₀ r)) (K := Real.toNNReal K') (f := Y w)
      (g := Y w₀) (f' := fun τ ↦ aux1_linField (fun r ↦ -C.orbitK w r) τ (Y w τ))
      (g' := fun τ ↦ aux1_linField (fun r ↦ -C.orbitK w₀ r) τ (Y w₀ τ))
      (εf := η / 2) (εg := 0) (δ := 0) (a := s) (b := t)
      (aux1_lipschitzWith_linField (aux1_abs_neg_orbitK_le C w₀))
      (hYc w).continuousOn (fun x _ ↦ (hYd w x).hasDerivWithinAt) ?_
      (hYc w₀).continuousOn (fun x _ ↦ (hYd w₀ x).hasDerivWithinAt) (fun _ _ ↦ by simp)
      (by simp [hYs]) t ⟨h.le, le_rfl⟩
    · rw [Real.coe_toNNReal _ hK'0, add_zero] at hdist
      exact hdist.trans_lt (hηε _ (by rw [abs_of_pos (by positivity)]; linarith))
    · intro τ hτ
      have h1 := hw ⟨τ, Ico_subset_Icc_self hτ⟩
      have h2 : |(Y w τ).1| ≤ B := (le_max_left _ _).trans
        (by simpa [Prod.norm_def] using hYb w τ (Ico_subset_Icc_self hτ))
      rw [Real.dist_eq] at h1
      simp only [aux1_linField, Prod.dist_eq, dist_self, Real.dist_eq]
      rw [max_eq_right (abs_nonneg _), ← sub_mul, abs_mul]
      calc |-C.orbitK w τ - -C.orbitK w₀ τ| * |(Y w τ).1| ≤ (η / (2 * B)) * B := by
            refine mul_le_mul ?_ h2 (abs_nonneg _) (by positivity)
            rw [show -C.orbitK w τ - -C.orbitK w₀ τ = C.orbitK w₀ τ - C.orbitK w τ by ring]
            exact h1.le
        _ = η / 2 := by field_simp
  have hfst : Continuous fun w ↦ C.jacobiFrom w s t := by
    subst hY; exact continuous_fst.comp hYt
  have hsnd : Continuous fun w ↦ C.jacobiFrom' w s t := by
    subst hY; exact continuous_snd.comp hYt
  exact continuous_iff_continuousAt.2 fun w ↦
    hsnd.continuousAt.div hfst.continuousAt (C.jacobiFrom_pos w h).ne'

/-- For fixed times `t < s`, `logDerivTo v s t` depends continuously on the base point `v`. -/
theorem continuous_logDerivTo {s t : ℝ} (h : t < s) :
    Continuous fun v ↦ C.logDerivTo v s t := by
  simp_rw [C.logDerivTo_eq_reverse]
  exact (C.reverse.continuous_logDerivFrom (neg_lt_neg h)).neg

end CurvatureFlow

end Kolmogorov.PointToSet
