/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Pressure.Upper.PointToSetPrinciple
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Local entropies of a Borel measure along Bowen balls

For a Borel measure `μ` on a metric space and a map `T`, the lower and upper Brin–Katok local
entropies at a point `x` are

`h̲_μ(T, x, ε) = liminf_n -(1/n) log₂ μ(B_n(x, T, ε))`, `h̲_μ(T, x) = lim_{ε → 0} h̲_μ(T, x, ε)`,

and likewise with `limsup` (E. Dinowitz, *Entropy of non-invariant measures and orbit complexity
of random points*, §2.3). The measure is not assumed invariant. Values are taken in `ℝ≥0∞`;
the information `-log₂ q` of a mass `q` is `infoBits q`, truncated at `0` for `q > 1`, so that
the definitions are total for arbitrary measures. Scales are the dyadic radii of the library
(`dyadicRadius`), as for `orbitComplexities`.

* `infoBits`: the information `-log₂ q ∈ [0, ∞]` of a mass `q`.
* `closedBowenBall`: the closed Bowen ball `B̄_n(x, T, ε)`.
* `localEntropyRate`, `localEntropyAt`, `localEntropy`: the finite-time rate, the pair of lower
  and upper local entropies at a fixed scale, and the pair of local entropies.
* `orbitComplexityAt`: the pair of lower and upper orbit complexity rates at a fixed scale.
* `measureEntropy`: the Feng–Huang lower and upper entropies of the measure, the integrals of
  the local entropies.
* `entropyLaw`: the joint law of the lower and upper local entropies (Definition 6.1).

Blueprint nodes `meas:info`, `meas:local-entropy`, `meas:entropy-law`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X]

/-! ### Information of a mass -/

/-- The information `-log₂ q` of a mass `q`, valued in `[0, ∞]`: infinite at `q = 0` and
truncated at `0` for `q ≥ 1`. Blueprint node `meas:info`. -/
noncomputable def infoBits (q : ℝ≥0∞) : ℝ≥0∞ :=
  if q = 0 then ⊤ else ENNReal.ofReal (-Real.logb 2 q.toReal)

/-- The information of the zero mass is infinite. -/
@[simp]
theorem infoBits_zero : infoBits 0 = ⊤ := by
  simp [infoBits]

/-- The information of the infinite mass is `0`. -/
@[simp]
theorem infoBits_top : infoBits ⊤ = 0 := by
  simp [infoBits]

/-- The information of a positive finite mass is `-log₂` of its real value. -/
theorem infoBits_of_ne {q : ℝ≥0∞} (hq0 : q ≠ 0) :
    infoBits q = ENNReal.ofReal (-Real.logb 2 q.toReal) := by
  simp [infoBits, hq0]

/-- The information of a positive real mass `r` is `-log₂ r`. -/
theorem infoBits_ofReal {r : ℝ} (hr : 0 < r) :
    infoBits (ENNReal.ofReal r) = ENNReal.ofReal (-Real.logb 2 r) := by
  rw [infoBits_of_ne (by simpa using hr), ENNReal.toReal_ofReal hr.le]

/-- The information of a positive mass is finite. -/
theorem infoBits_lt_top {q : ℝ≥0∞} (hq : q ≠ 0) : infoBits q < ⊤ := by
  simp [infoBits, hq]

/-- The information is infinite exactly at the zero mass. -/
theorem infoBits_eq_top_iff {q : ℝ≥0∞} : infoBits q = ⊤ ↔ q = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ infoBits_zero⟩
  by_contra hq
  exact (infoBits_lt_top hq).ne h

/-- Larger masses carry less information. Blueprint node `meas:info`. -/
theorem infoBits_antitone : Antitone infoBits := by
  intro a b hab
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  rcases eq_or_ne b ⊤ with rfl | hbt
  · simp
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hbt hab
  rw [infoBits_of_ne ha0, infoBits_of_ne (pos_iff_ne_zero.1 ((pos_iff_ne_zero.2 ha0).trans_le hab))]
  exact ENNReal.ofReal_le_ofReal <| neg_le_neg <| Real.logb_le_logb_of_le one_lt_two
    (ENNReal.toReal_pos ha0 hat) (ENNReal.toReal_mono hbt hab)

/-- A mass whose information is below `k` bits exceeds `2^{-k}`. -/
theorem two_inv_pow_lt_of_infoBits_lt {q : ℝ≥0∞} {k : ℕ} (h : infoBits q < k) :
    (2 : ℝ≥0∞)⁻¹ ^ k < q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp at h
  rcases eq_or_ne q ⊤ with rfl | hqt
  · exact ENNReal.pow_lt_top (by simp)
  have hpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  rw [infoBits_of_ne hq0, ← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff'] at h
  have h2 : (2 : ℝ) ^ (-(k : ℝ)) < q.toReal :=
    (Real.lt_logb_iff_rpow_lt one_lt_two hpos).1 (by linarith [h.1])
  rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, ← inv_pow] at h2
  rw [← ENNReal.ofReal_toReal hqt, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_inv_of_pos two_pos,
    ← ENNReal.ofReal_pow (by norm_num)]
  exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 h2

/-- A mass of at least `2^{-s}` has information at most `s`. -/
theorem infoBits_le_of_rpow_le {q : ℝ≥0∞} {s : ℝ} (hs : 0 ≤ s)
    (h : ENNReal.ofReal ((2 : ℝ) ^ (-s)) ≤ q) : infoBits q ≤ ENNReal.ofReal s := by
  have h2pos : 0 < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos two_pos _
  have hq0 : q ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 h2pos) h).ne'
  rcases eq_or_ne q ⊤ with rfl | hqt
  · simp
  have hpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  rw [← ENNReal.ofReal_toReal hqt, ENNReal.ofReal_le_ofReal_iff hpos.le] at h
  rw [infoBits_of_ne hq0, ENNReal.ofReal_le_ofReal_iff hs]
  have := (Real.le_logb_iff_rpow_le one_lt_two hpos).2 h
  linarith

/-- A mass of at most `2^{-s}` has information at least `s`. -/
theorem le_infoBits_of_le_rpow {q : ℝ≥0∞} {s : ℝ}
    (h : q ≤ ENNReal.ofReal ((2 : ℝ) ^ (-s))) : ENNReal.ofReal s ≤ infoBits q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  have hqt : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  rw [← ENNReal.ofReal_toReal hqt, ENNReal.ofReal_le_ofReal_iff (Real.rpow_pos_of_pos two_pos _).le]
    at h
  rw [infoBits_of_ne hq0]
  refine ENNReal.ofReal_le_ofReal ?_
  have := (Real.logb_le_iff_le_rpow one_lt_two hpos).2 h
  linarith

/-- Multiplying a mass by a factor `c ≥ 1` lowers its information by at most `log₂ c`. -/
theorem infoBits_le_infoBits_mul_add {c : ℝ} (hc : 1 ≤ c) (q : ℝ≥0∞) :
    infoBits q ≤ infoBits (ENNReal.ofReal c * q) + ENNReal.ofReal (Real.logb 2 c) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rcases eq_or_ne q ⊤ with rfl | hqt
  · simp
  have hpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  have hc0 : 0 < c := one_pos.trans_le hc
  have hcq : ENNReal.ofReal c * q = ENNReal.ofReal (c * q.toReal) := by
    rw [ENNReal.ofReal_mul hc0.le, ENNReal.ofReal_toReal hqt]
  rw [infoBits_of_ne hq0, hcq, infoBits_ofReal (mul_pos hc0 hpos), Real.logb_mul hc0.ne' hpos.ne']
  calc ENNReal.ofReal (-Real.logb 2 q.toReal)
      = ENNReal.ofReal (-(Real.logb 2 c + Real.logb 2 q.toReal) + Real.logb 2 c) := by
        congr 1; ring
    _ ≤ _ := ENNReal.ofReal_add_le

/-! ### Closed Bowen balls -/

/-- The closed Bowen ball `B̄_n(x, T, ε)`: the points whose first `n` iterates stay within
distance `ε` of those of `x`. Blueprint node `meas:local-entropy`. -/
def closedBowenBall (T : X → X) (n : ℕ) (x : X) (ε : ℝ) : Set X :=
  {y | ∀ k < n, dist (T^[k] x) (T^[k] y) ≤ ε}

/-- Membership in a closed Bowen ball. -/
theorem mem_closedBowenBall_iff {T : X → X} {n : ℕ} {x y : X} {ε : ℝ} :
    y ∈ closedBowenBall T n x ε ↔ ∀ k < n, dist (T^[k] x) (T^[k] y) ≤ ε :=
  Iff.rfl

/-- The open Bowen ball is contained in the closed one. -/
theorem bowenBall_subset_closedBowenBall (T : X → X) (n : ℕ) (x : X) (ε : ℝ) :
    bowenBall T n x ε ⊆ closedBowenBall T n x ε :=
  fun _ hy k hk ↦ (mem_bowenBall_iff.1 hy k hk).le

/-- The closed Bowen ball is contained in every open Bowen ball of larger radius. -/
theorem closedBowenBall_subset_bowenBall (T : X → X) (n : ℕ) (x : X) {ε ε' : ℝ}
    (h : ε < ε') : closedBowenBall T n x ε ⊆ bowenBall T n x ε' :=
  fun _ hy ↦ mem_bowenBall_iff.2 fun k hk ↦ (hy k hk).trans_lt h

/-- Closed Bowen balls of a continuous map are closed. -/
theorem isClosed_closedBowenBall {T : X → X} (hT : Continuous T) (n : ℕ) (x : X) (ε : ℝ) :
    IsClosed (closedBowenBall T n x ε) := by
  have : closedBowenBall T n x ε = ⋂ k, ⋂ (_ : k < n), {y | dist (T^[k] x) (T^[k] y) ≤ ε} := by
    ext y
    simp [closedBowenBall]
  rw [this]
  exact isClosed_iInter fun k ↦ isClosed_iInter fun _ ↦
    isClosed_le (continuous_const.dist (hT.iterate k)) continuous_const

/-- Triangle inequality for Bowen balls: a Bowen ball about a point of another Bowen ball is
contained in the Bowen ball of the sum of the radii. -/
theorem bowenBall_subset_bowenBall_add {T : X → X} {n : ℕ} {x y : X} {ε δ : ℝ}
    (hy : y ∈ bowenBall T n x ε) : bowenBall T n y δ ⊆ bowenBall T n x (ε + δ) :=
  fun _ hz ↦ mem_bowenBall_iff.2 fun k hk ↦ (dist_triangle _ (T^[k] y) _).trans_lt
    (add_lt_add (mem_bowenBall_iff.1 hy k hk) (mem_bowenBall_iff.1 hz k hk))

/-- If `x` lies in the Bowen ball of radius `ε` about `z`, then the closed Bowen ball of
radius `ε` about `z` lies in the Bowen ball of radius `2ε` about `x`. -/
theorem closedBowenBall_subset_bowenBall_two_mul {T : X → X} {n : ℕ} {x z : X} {ε : ℝ}
    (hx : z ∈ bowenBall T n x ε) : closedBowenBall T n z ε ⊆ bowenBall T n x (2 * ε) :=
  fun _ hy ↦ mem_bowenBall_iff.2 fun k hk ↦ (dist_triangle _ (T^[k] z) _).trans_lt <| by
    rw [two_mul]
    exact add_lt_add_of_lt_of_le (mem_bowenBall_iff.1 hx k hk) (hy k hk)

/-! ### Local entropies -/

variable [MeasurableSpace X]

/-- The finite-time local entropy rate `-(1/n) log₂ μ(B_n(x, T, ε))`.
Blueprint node `meas:local-entropy`. -/
noncomputable def localEntropyRate (μ : Measure X) (T : X → X) (x : X) (n : ℕ) (ε : ℝ) :
    ℝ≥0∞ :=
  infoBits (μ (bowenBall T n x ε)) / n

/-- The lower and upper local entropies `h̲_μ(T, x, ε)`, `h̄_μ(T, x, ε)` at the scale `ε`.
Blueprint node `meas:local-entropy`. -/
noncomputable def localEntropyAt (μ : Measure X) (T : X → X) (x : X) (ε : ℝ) :
    ℝ≥0∞ × ℝ≥0∞ :=
  (liminf (fun n ↦ localEntropyRate μ T x n ε) atTop,
    limsup (fun n ↦ localEntropyRate μ T x n ε) atTop)

/-- The lower and upper Brin–Katok local entropies `h̲_μ(T, x)`, `h̄_μ(T, x)`, as suprema over
the dyadic scales. Blueprint node `meas:local-entropy`. -/
noncomputable def localEntropy (μ : Measure X) (T : X → X) (x : X) : ℝ≥0∞ × ℝ≥0∞ :=
  (⨆ p : ℕ, (localEntropyAt μ T x (dyadicRadius p)).1,
    ⨆ p : ℕ, (localEntropyAt μ T x (dyadicRadius p)).2)

/-- The lower and upper orbit complexity rates `K̲^A(x, T, ε)`, `K̄^A(x, T, ε)` at the scale
`ε`. Blueprint node `meas:local-entropy`. -/
noncomputable def orbitComplexityAt (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X)
    (ε : ℝ) : ℝ≥0∞ × ℝ≥0∞ :=
  (liminf (fun n ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n ε) atTop,
    limsup (fun n ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n ε) atTop)

omit [MeasurableSpace X] in
/-- The orbit complexities are the suprema over the dyadic scales of the rates at a fixed
scale. -/
theorem orbitComplexities_eq_iSup_orbitComplexityAt (P : Presentation X) (T : X → X)
    (A : Set ℕ) (x : X) :
    orbitComplexities P T A x =
      (⨆ p : ℕ, (orbitComplexityAt P T A x (dyadicRadius p)).1,
        ⨆ p : ℕ, (orbitComplexityAt P T A x (dyadicRadius p)).2) :=
  rfl

omit [MeasurableSpace X] in
/-- The orbit complexity rates at a fixed scale are antitone in the scale. -/
theorem orbitComplexityAt_antitone (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X)
    {ε ε' : ℝ} (h : ε ≤ ε') :
    (orbitComplexityAt P T A x ε').1 ≤ (orbitComplexityAt P T A x ε).1 ∧
      (orbitComplexityAt P T A x ε').2 ≤ (orbitComplexityAt P T A x ε).2 :=
  ⟨liminf_le_liminf (Eventually.of_forall fun n ↦
      pointwiseBSDimension_antitone_radius P T _ A x n h),
    limsup_le_limsup (Eventually.of_forall fun n ↦
      pointwiseBSDimension_antitone_radius P T _ A x n h)⟩

omit [MeasurableSpace X] in
/-- The orbit complexity rate at any positive scale is at most the orbit complexity. -/
theorem orbitComplexityAt_le_orbitComplexities (P : Presentation X) (T : X → X) (A : Set ℕ)
    (x : X) {ε : ℝ} (hε : 0 < ε) :
    (orbitComplexityAt P T A x ε).1 ≤ (orbitComplexities P T A x).1 ∧
      (orbitComplexityAt P T A x ε).2 ≤ (orbitComplexities P T A x).2 := by
  obtain ⟨p, hp⟩ := exists_dyadicRadius_lt hε
  have h := orbitComplexityAt_antitone P T A x hp.le
  rw [orbitComplexities_eq_iSup_orbitComplexityAt]
  exact ⟨h.1.trans (le_iSup (fun p ↦ (orbitComplexityAt P T A x (dyadicRadius p)).1) p),
    h.2.trans (le_iSup (fun p ↦ (orbitComplexityAt P T A x (dyadicRadius p)).2) p)⟩

/-- The finite-time local entropy rate is antitone in the scale. -/
theorem localEntropyRate_antitone (μ : Measure X) (T : X → X) (x : X) (n : ℕ) :
    Antitone (localEntropyRate μ T x n) := fun _ _ h ↦
  ENNReal.div_le_div_right (infoBits_antitone (measure_mono (bowenBall_subset_of_le T n x h))) _

/-- The local entropies at a fixed scale are antitone in the scale: they do not decrease as
`ε ↓ 0`. Blueprint node `meas:local-entropy`. -/
theorem localEntropyAt_antitone (μ : Measure X) (T : X → X) (x : X) {ε ε' : ℝ} (h : ε ≤ ε') :
    (localEntropyAt μ T x ε').1 ≤ (localEntropyAt μ T x ε).1 ∧
      (localEntropyAt μ T x ε').2 ≤ (localEntropyAt μ T x ε).2 :=
  ⟨liminf_le_liminf (Eventually.of_forall fun n ↦ localEntropyRate_antitone μ T x n h),
    limsup_le_limsup (Eventually.of_forall fun n ↦ localEntropyRate_antitone μ T x n h)⟩

/-- The lower local entropy at a fixed scale is at most the upper one. -/
theorem localEntropyAt_fst_le_snd (μ : Measure X) (T : X → X) (x : X) (ε : ℝ) :
    (localEntropyAt μ T x ε).1 ≤ (localEntropyAt μ T x ε).2 :=
  liminf_le_limsup

/-- The lower local entropy is at most the upper one. -/
theorem localEntropy_fst_le_snd (μ : Measure X) (T : X → X) (x : X) :
    (localEntropy μ T x).1 ≤ (localEntropy μ T x).2 :=
  iSup_mono fun _ ↦ localEntropyAt_fst_le_snd μ T x _

/-- The local entropy at any positive scale is at most the local entropy. -/
theorem localEntropyAt_le_localEntropy (μ : Measure X) (T : X → X) (x : X) {ε : ℝ}
    (hε : 0 < ε) :
    (localEntropyAt μ T x ε).1 ≤ (localEntropy μ T x).1 ∧
      (localEntropyAt μ T x ε).2 ≤ (localEntropy μ T x).2 := by
  obtain ⟨p, hp⟩ := exists_dyadicRadius_lt hε
  have h := localEntropyAt_antitone μ T x hp.le
  exact ⟨h.1.trans (le_iSup (fun p ↦ (localEntropyAt μ T x (dyadicRadius p)).1) p),
    h.2.trans (le_iSup (fun p ↦ (localEntropyAt μ T x (dyadicRadius p)).2) p)⟩

/-- A bound on the local entropies at all positive rational scales bounds the local
entropies. -/
theorem localEntropy_le_of_forall_rat (μ : Measure X) (T : X → X) (x : X) (s : ℝ≥0∞ × ℝ≥0∞)
    (h : ∀ ε : ℚ, 0 < ε → (localEntropyAt μ T x ε).1 ≤ s.1 ∧ (localEntropyAt μ T x ε).2 ≤ s.2) :
    (localEntropy μ T x).1 ≤ s.1 ∧ (localEntropy μ T x).2 ≤ s.2 := by
  have key : ∀ p : ℕ, (localEntropyAt μ T x (dyadicRadius p)).1 ≤ s.1 ∧
      (localEntropyAt μ T x (dyadicRadius p)).2 ≤ s.2 := fun p ↦ by
    have hcast : (((2 : ℚ)⁻¹ ^ p : ℚ) : ℝ) = dyadicRadius p := by simp [dyadicRadius]
    have := h ((2 : ℚ)⁻¹ ^ p) (by positivity)
    rwa [hcast] at this
  exact ⟨iSup_le fun p ↦ (key p).1, iSup_le fun p ↦ (key p).2⟩

/-- Multiplying a mass by a positive finite factor `c` changes its information by at most
`|log₂ c|`. -/
theorem infoBits_mul_le {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (q : ℝ≥0∞) :
    infoBits (c * q) ≤ infoBits q + ENNReal.ofReal |Real.logb 2 c.toReal| := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rcases eq_or_ne q ⊤ with rfl | hqt
  · simp [ENNReal.mul_top hc0]
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
  have hpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  rw [infoBits_of_ne (mul_ne_zero hc0 hq0), infoBits_of_ne hq0, ENNReal.toReal_mul,
    Real.logb_mul hcpos.ne' hpos.ne']
  calc ENNReal.ofReal (-(Real.logb 2 c.toReal + Real.logb 2 q.toReal))
      = ENNReal.ofReal (-Real.logb 2 q.toReal + -Real.logb 2 c.toReal) := by congr 1; ring
    _ ≤ ENNReal.ofReal (-Real.logb 2 q.toReal) + ENNReal.ofReal (-Real.logb 2 c.toReal) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := by gcongr; exact neg_le_abs _

/-- If `a n ≤ b n + d n` eventually, with `d n → 0`, then `liminf a ≤ liminf b` in `ℝ≥0∞`. -/
theorem liminf_le_liminf_of_le_add_tendsto_zero {a b d : ℕ → ℝ≥0∞}
    (h : ∀ᶠ n in atTop, a n ≤ b n + d n) (hd : Tendsto d atTop (𝓝 0)) :
    liminf a atTop ≤ liminf b atTop :=
  (liminf_le_liminf h).trans_eq (ENNReal.liminf_add_of_right_tendsto_zero hd b)

/-- If `a n ≤ b n + d n` eventually, with `d n → 0`, then `limsup a ≤ limsup b` in `ℝ≥0∞`. -/
theorem limsup_le_limsup_of_le_add_tendsto_zero {a b d : ℕ → ℝ≥0∞}
    (h : ∀ᶠ n in atTop, a n ≤ b n + d n) (hd : Tendsto d atTop (𝓝 0)) :
    limsup a atTop ≤ limsup b atTop :=
  (limsup_le_limsup h).trans_eq (ENNReal.limsup_add_of_right_tendsto_zero hd b)

/-- Rescaling a measure by a positive finite constant does not change its local entropies at
a fixed scale: the information changes by a bounded amount.
Blueprint node `meas:local-entropy`. -/
theorem localEntropyAt_smul (μ : Measure X) (T : X → X) (x : X) (ε : ℝ) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ⊤) : localEntropyAt (c • μ) T x ε = localEntropyAt μ T x ε := by
  set C := ENNReal.ofReal |Real.logb 2 c.toReal|
  have hC : Tendsto (fun n : ℕ ↦ C / n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.ofReal_ne_top (r := |Real.logb 2 c.toReal|)))
    simpa [div_eq_mul_inv] using this
  have hinv : |Real.logb 2 c⁻¹.toReal| = |Real.logb 2 c.toReal| := by
    rw [ENNReal.toReal_inv, Real.logb_inv, abs_neg]
  have h1 : ∀ n : ℕ, localEntropyRate (c • μ) T x n ε ≤ localEntropyRate μ T x n ε + C / n :=
    fun n ↦ by
      simp only [localEntropyRate, Measure.smul_apply, smul_eq_mul, ← ENNReal.add_div]
      exact ENNReal.div_le_div_right (infoBits_mul_le hc0 hc _) _
  have h2 : ∀ n : ℕ, localEntropyRate μ T x n ε ≤ localEntropyRate (c • μ) T x n ε + C / n :=
    fun n ↦ by
      simp only [localEntropyRate, Measure.smul_apply, smul_eq_mul, ← ENNReal.add_div]
      refine ENNReal.div_le_div_right ?_ _
      have := infoBits_mul_le (ENNReal.inv_ne_zero.2 hc) (ENNReal.inv_ne_top.2 hc0)
        (c * μ (bowenBall T n x ε))
      rwa [ENNReal.inv_mul_cancel_left hc0 hc, hinv] at this
  ext
  · exact le_antisymm (liminf_le_liminf_of_le_add_tendsto_zero (.of_forall h1) hC)
      (liminf_le_liminf_of_le_add_tendsto_zero (.of_forall h2) hC)
  · exact le_antisymm (limsup_le_limsup_of_le_add_tendsto_zero (.of_forall h1) hC)
      (limsup_le_limsup_of_le_add_tendsto_zero (.of_forall h2) hC)

/-- Rescaling a measure by a positive finite constant does not change its local entropies. -/
theorem localEntropy_smul (μ : Measure X) (T : X → X) (x : X) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ⊤) : localEntropy (c • μ) T x = localEntropy μ T x := by
  simp only [localEntropy, localEntropyAt_smul μ T x _ hc0 hc]

/-! ### Measurability -/

section measurability

variable [BorelSpace X]

/-- The mass of a Bowen ball is a lower semicontinuous, hence Borel, function of its centre.
Blueprint node `meas:local-entropy`. -/
theorem measurable_measure_bowenBall (μ : Measure X) {T : X → X} (hT : Continuous T) (n : ℕ)
    (ε : ℝ) : Measurable fun x ↦ μ (bowenBall T n x ε) := by
  refine LowerSemicontinuous.measurable (lowerSemicontinuous_iff_isOpen_preimage.2 fun c ↦ ?_)
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  change c < μ (bowenBall T n x ε) at hx
  set s : ℕ → Set X := fun m ↦ bowenBall T n x (ε - 1 / ((m : ℝ) + 1)) with hs
  have hmono : Monotone s := fun m m' hmm' ↦ bowenBall_subset_of_le T n x <| by
    gcongr
  have hU : (⋃ m, s m) = bowenBall T n x ε := by
    ext y
    simp only [hs, mem_iUnion, mem_bowenBall_iff]
    refine ⟨fun ⟨m, hm⟩ k hk ↦ (hm k hk).trans_le (sub_le_self _ (by positivity)), fun hy ↦ ?_⟩
    have hlim : Tendsto (fun m : ℕ ↦ ε - 1 / ((m : ℝ) + 1)) atTop (𝓝 ε) := by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hev : ∀ᶠ m : ℕ in atTop, ∀ k ∈ Iio n, dist (T^[k] x) (T^[k] y) < ε - 1 / ((m : ℝ) + 1) :=
      (eventually_all_finite (finite_Iio n)).2 fun k hk ↦ hlim.eventually (lt_mem_nhds (hy k hk))
    obtain ⟨m, hm⟩ := hev.exists
    exact ⟨m, fun k hk ↦ hm k hk⟩
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hU] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (lt_mem_nhds hx)).exists
  have hδ : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  refine Filter.mem_of_superset ((bowen_ball_dense_open T hT n x _).mem_nhds
    (self_mem_bowenBall T n x _ hδ)) fun x' hx' ↦ ?_
  change c < μ (bowenBall T n x' ε)
  refine hm.trans_le (measure_mono ?_)
  have := bowenBall_subset_bowenBall_add (ε := 1 / ((m : ℝ) + 1)) (δ := ε - 1 / ((m : ℝ) + 1))
    (mem_bowenBall_symm hx')
  rwa [add_sub_cancel] at this

/-- The finite-time local entropy rate is a Borel function of the point. -/
theorem measurable_localEntropyRate (μ : Measure X) {T : X → X} (hT : Continuous T) (n : ℕ)
    (ε : ℝ) : Measurable fun x ↦ localEntropyRate μ T x n ε :=
  (infoBits_antitone.measurable.comp (measurable_measure_bowenBall μ hT n ε)).div_const _

/-- The local entropies at a fixed scale are Borel functions of the point. -/
theorem measurable_localEntropyAt (μ : Measure X) {T : X → X} (hT : Continuous T) (ε : ℝ) :
    Measurable fun x ↦ localEntropyAt μ T x ε :=
  (Measurable.liminf fun n ↦ measurable_localEntropyRate μ hT n ε).prodMk
    (Measurable.limsup fun n ↦ measurable_localEntropyRate μ hT n ε)

/-- The pair of local entropies `Φ_μ` is a Borel map. Blueprint node `meas:entropy-law`. -/
theorem measurable_localEntropy (μ : Measure X) {T : X → X} (hT : Continuous T) :
    Measurable fun x ↦ localEntropy μ T x :=
  (Measurable.iSup fun p ↦ (measurable_localEntropyAt μ hT (dyadicRadius p)).fst).prodMk
    (Measurable.iSup fun p ↦ (measurable_localEntropyAt μ hT (dyadicRadius p)).snd)

end measurability

/-! ### Feng–Huang entropies and the entropy law -/

/-- The Feng–Huang lower and upper entropies `h̲_μ(T)`, `h̄_μ(T)` of a measure: the integrals
of its local entropies. Blueprint node `meas:entropy-law`. -/
noncomputable def measureEntropy (μ : Measure X) (T : X → X) : ℝ≥0∞ × ℝ≥0∞ :=
  (∫⁻ x, (localEntropy μ T x).1 ∂μ, ∫⁻ x, (localEntropy μ T x).2 ∂μ)

/-- The entropy law `Λ_μ` of a measure: the joint law of its lower and upper local entropies
(Definition 6.1). Blueprint node `meas:entropy-law`. -/
noncomputable def entropyLaw (μ : Measure X) (T : X → X) : Measure (ℝ≥0∞ × ℝ≥0∞) :=
  Measure.map (localEntropy μ T) μ

end Kolmogorov.PointToSet
