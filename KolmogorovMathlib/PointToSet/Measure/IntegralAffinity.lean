/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Decomposition
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# When integral affinity holds (Theorem 7.5)

For an integral decomposition `μ = ∫ μ_ω dQ(ω)` given by a kernel `κ`, with `M = Q ⊗ κ`,
integral affinity `Λ_μ = ∫ Λ_{μ_ω} dQ(ω)` is equivalent to `Φ_{μ_ω}(x) = Φ_μ(x)` for
`M`-almost every `(ω, x)` (`kernelEntropyLaw_eq_iff`). This file gives the sufficient
conditions of Theorem 7.5 of E. Dinowitz, *Entropy of non-invariant measures and orbit
complexity of random points*, in that almost-everywhere form.

* `ae_compProd_localEntropy_eq_of_absolutelyContinuous` (Theorem 7.5(a)): the components are
  absolutely continuous with respect to `μ`; `compProd_absolutelyContinuous_prod_iff`: this
  is equivalent to `M ≪ Q ⊗ μ`.
* `ae_compProd_localEntropy_eq_of_ergodicDecomposition` (Theorem 7.5(b)): `X` compact, `μ`
  invariant of finite entropy and `κ` its ergodic decomposition. This rests on the Brin–Katok
  theorem and on Jacobs' theorem, which are not available; it is a tracked `sorry`.
* `ae_compProd_localEntropy_eq_of_ratio` (Theorem 7.5(c)): for every `ε` there is `ε'` with
  `limsup_n (1/n) log (μ_ω(B_n(x, T, ε')) / μ(B_n(x, T, ε))) ≤ 0` almost everywhere. The
  pointwise step is `localEntropyAt_le_of_ratio`.

Part (a) and its equivalent form are proved from `ae_localEntropy_eq_of_absolutelyContinuous`
and Mathlib's `Measure.absolutelyContinuous_compProd_right_iff` (which rests on the Lebesgue
decomposition of kernels); part (c) combines the ratio bound with `ae_compProd_localEntropy_le`.

Blueprint node `meas:integral-affinity`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {Ω : Type*} [MeasurableSpace Ω]

/-- Theorem 7.5(a): if `μ_ω ≪ μ` for `Q`-almost every `ω`, then `Φ_{μ_ω}(x) = Φ_μ(x)` for
`M`-almost every `(ω, x)`, so integral affinity holds. Blueprint node `meas:integral-affinity`. -/
theorem ae_compProd_localEntropy_eq_of_absolutelyContinuous {T : X → X} (hT : Continuous T)
    (Q : Measure Ω) [IsFiniteMeasure Q] (κ : Kernel Ω X) [IsFiniteKernel κ]
    (h : ∀ᵐ ω ∂Q, κ ω ≪ Q.bind κ) :
    ∀ᵐ p ∂(Q ⊗ₘ κ), localEntropy (κ p.1) T p.2 = localEntropy (Q.bind κ) T p.2 := by
  have hK := measurable_localEntropy_kernel hT κ
  have hμ : Measurable fun p : Ω × X ↦ localEntropy (Q.bind κ) T p.2 :=
    (measurable_localEntropy (Q.bind κ) hT).comp measurable_snd
  refine Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hK hμ) ?_
  filter_upwards [h] with ω hω
  exact ae_localEntropy_eq_of_absolutelyContinuous hT hω

/-- Theorem 7.5(a), equivalent form of the hypothesis: `μ_ω ≪ μ` for `Q`-almost every `ω` if
and only if `M ≪ Q ⊗ μ`. Blueprint node `meas:integral-affinity`. -/
theorem compProd_absolutelyContinuous_prod_iff (Q : Measure Ω) [IsFiniteMeasure Q]
    (κ : Kernel Ω X) [IsFiniteKernel κ] :
    (Q ⊗ₘ κ) ≪ Q.prod (Q.bind κ) ↔ ∀ᵐ ω ∂Q, κ ω ≪ Q.bind κ := by
  rw [← Measure.compProd_const, Measure.absolutelyContinuous_compProd_right_iff]
  simp only [Kernel.const_apply]

omit [BorelSpace X] [SecondCountableTopology X] in
/-- If `ν(B_n(x, ε')) ≤ 2^{δ n} μ(B_n(x, ε))` eventually, for every `δ > 0`, then the local
entropies of `μ` at the scale `ε` are at most those of `ν` at the scale `ε'`. -/
theorem localEntropyAt_le_of_ratio {μ ν : Measure X} {T : X → X} {x : X} {ε ε' : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ν (bowenBall T n x ε') ≤ ENNReal.ofReal ((2 : ℝ) ^ (δ * n)) * μ (bowenBall T n x ε)) :
    (localEntropyAt μ T x ε).1 ≤ (localEntropyAt ν T x ε').1 ∧
      (localEntropyAt μ T x ε).2 ≤ (localEntropyAt ν T x ε').2 := by
  have hrate : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      localEntropyRate μ T x n ε ≤ localEntropyRate ν T x n ε' + ENNReal.ofReal δ := by
    intro δ hδ
    filter_upwards [h δ hδ, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn1)
    have hc : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := Real.one_le_rpow one_le_two (by positivity)
    have hinfo : infoBits (μ (bowenBall T n x ε)) ≤
        infoBits (ν (bowenBall T n x ε')) + ENNReal.ofReal δ * n := by
      refine (infoBits_le_infoBits_mul_add hc _).trans (add_le_add (infoBits_antitone hn) ?_)
      rw [Real.logb_rpow two_pos (by norm_num), ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_natCast]
    unfold localEntropyRate
    calc infoBits (μ (bowenBall T n x ε)) / n
        ≤ (infoBits (ν (bowenBall T n x ε')) + ENNReal.ofReal δ * n) / n :=
          ENNReal.div_le_div_right hinfo _
      _ = _ := by
          rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n)]
  constructor
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    calc (localEntropyAt μ T x ε).1
        ≤ liminf (fun n ↦ localEntropyRate ν T x n ε' + ENNReal.ofReal δ) atTop :=
          liminf_le_liminf (hrate δ (by exact_mod_cast hδ))
      _ = _ := by
          rw [ENNReal.ofReal_coe_nnreal, liminf_add_const _ _ _ (by isBoundedDefault)
            (by isBoundedDefault)]
          rfl
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    calc (localEntropyAt μ T x ε).2
        ≤ limsup (fun n ↦ localEntropyRate ν T x n ε' + ENNReal.ofReal δ) atTop :=
          limsup_le_limsup (hrate δ (by exact_mod_cast hδ))
      _ = _ := by
          rw [ENNReal.ofReal_coe_nnreal, limsup_add_const _ _ _ (by isBoundedDefault)
            (by isBoundedDefault)]
          rfl

/-- Theorem 7.5(c): suppose that for every `ε > 0` there is `ε' > 0` such that, for
`M`-almost every `(ω, x)`, `μ_ω(B_n(x, T, ε')) ≤ 2^{δ n} μ(B_n(x, T, ε))` eventually, for every
`δ > 0` (that is, `limsup_n (1/n) log₂ (μ_ω(B_n(x, T, ε')) / μ(B_n(x, T, ε))) ≤ 0`). Then
`Φ_{μ_ω}(x) = Φ_μ(x)` for `M`-almost every `(ω, x)`. Blueprint node `meas:integral-affinity`. -/
theorem ae_compProd_localEntropy_eq_of_ratio {T : X → X} (hT : Continuous T)
    (Q : Measure Ω) [IsFiniteMeasure Q] (κ : Kernel Ω X) [IsFiniteKernel κ]
    (h : ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧ ∀ᵐ p ∂(Q ⊗ₘ κ), ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, κ p.1 (bowenBall T n p.2 ε') ≤
        ENNReal.ofReal ((2 : ℝ) ^ (δ * n)) * (Q.bind κ) (bowenBall T n p.2 ε)) :
    ∀ᵐ p ∂(Q ⊗ₘ κ), localEntropy (κ p.1) T p.2 = localEntropy (Q.bind κ) T p.2 := by
  choose ε' hε' hae using fun p : ℕ ↦ h (dyadicRadius p) (dyadicRadius_pos p)
  filter_upwards [ae_all_iff.2 hae, ae_compProd_localEntropy_le hT Q κ] with q hq hle
  have key : ∀ p : ℕ, (localEntropyAt (Q.bind κ) T q.2 (dyadicRadius p)).1 ≤
      (localEntropy (κ q.1) T q.2).1 ∧ (localEntropyAt (Q.bind κ) T q.2 (dyadicRadius p)).2 ≤
      (localEntropy (κ q.1) T q.2).2 := fun p ↦ by
    have h1 := localEntropyAt_le_of_ratio (hq p)
    have h2 := localEntropyAt_le_localEntropy (κ q.1) T q.2 (hε' p)
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  exact Prod.ext (le_antisymm hle.1 (iSup_le fun p ↦ (key p).1))
    (le_antisymm hle.2 (iSup_le fun p ↦ (key p).2))

/-- Theorem 7.5(b): let `X` be compact, `μ = ∫ μ_ω dQ(ω)` a `T`-invariant probability measure
with `h̄_μ(T) < ∞` and `μ_ω` ergodic for `Q`-almost every `ω`. Then for `M`-almost every
`(ω, x)` the lower and upper local entropies of `μ` at `x` both equal the entropy of the
component `μ_ω` (the common value of its Feng–Huang entropies), and so do those of `μ_ω`; in
particular integral affinity holds and `Λ_μ` is carried by the diagonal.

This rests on the Brin–Katok theorem and on Jacobs' theorem on the entropy of an ergodic
decomposition; neither is available in Mathlib or in this library.
Blueprint node `meas:integral-affinity`. -/
theorem ae_compProd_localEntropy_eq_of_ergodicDecomposition [CompactSpace X] {T : X → X}
    (hT : Continuous T) (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X)
    [IsMarkovKernel κ] (hinv : MeasurePreserving T (Q.bind κ) (Q.bind κ))
    (herg : ∀ᵐ ω ∂Q, Ergodic T (κ ω)) (hfin : (measureEntropy (Q.bind κ) T).2 ≠ ⊤) :
    ∀ᵐ p ∂(Q ⊗ₘ κ),
      localEntropy (Q.bind κ) T p.2 =
          ((measureEntropy (κ p.1) T).1, (measureEntropy (κ p.1) T).1) ∧
        localEntropy (κ p.1) T p.2 = localEntropy (Q.bind κ) T p.2 := by
  -- TODO(sorry): external input — the Brin–Katok theorem and Jacobs' theorem
  sorry

end Kolmogorov.PointToSet
