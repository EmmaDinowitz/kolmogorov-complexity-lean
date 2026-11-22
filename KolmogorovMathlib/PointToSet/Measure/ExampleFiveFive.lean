/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ExampleFiveFiveUpper
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ExampleFiveFiveLower

/-!
# Example 5.5: Martin-Löf randomness is not enough in Theorem 4.3(b), (c)

The two constructions of Example 5.5 (proved in `Ergodic/ExampleFiveFiveUpper.lean` and
`Ergodic/ExampleFiveFiveLower.lean`, on the computable presentation `cantorPresentation` of
`Ergodic/CantorPresentation.lean`) and their consequences: Example 5.5 (1), (2) in the vocabulary
of Theorem 4.3, and the fact that the oracle cannot be fixed in Theorem 4.3(b), (c). All
statements are on Cantor space `ℕ → Bool` with the metric `cantorMetricSpace` and its standard
computable presentation `cantorPresentation`, as in the paper. The measure-theoretic input is in
`RandomNonAtom.lean`. Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-! ### Example 5.5 -/

section example55

attribute [local instance] cantorMetricSpace

/-- Example 5.5(1), core construction. Let `Ω` be a left-c.e. `λ`-random real with computable
approximations `Ω_t ↑ Ω`, `S_n = {Ω_t↾n : t > n}`, `(σ_i)` a computable enumeration of `⋃ S_n`,
`E_i = [σ_i]`, `N_1 = |σ_1|`, `N_{i+1} ≥ (i+1) max(N_i, |σ_{i+1}|)`, `J_i = [N_i, N_{i+1})`, and
`f(y)↾J_i = y↾J_i` if `y ∈ E_i`, `0^{|J_i|}` otherwise. Then `μ = λ ∘ f⁻¹` is computable, carried
by the countable set of eventually-`0` sequences, and `z = f(Ω)` is `μ`-random with
`h̄_μ(σ, z) = 1`.

Formalisation: Cantor space carries its standard computable presentation `cantorPresentation`;
"computable" is `IsMeasureAdmissible cantorPresentation shiftMap μ ∅`, "random" is
`randomPoints cantorPresentation ∅ μ`. Divergences from the paper: the conclusion is stated with
the upper *local entropy* at `z` (the paper then passes to `K̄(z, σ)` by Theorem 3.3, which is
done in `exampleFiveFive_upper`). Proved in `Ergodic/ExampleFiveFiveUpper.lean`; there `E_i` is
indexed by the stage of the approximation of `Ω` and each copied block starts with a marker bit
`1`. Blueprint node `meas:examples`. -/
theorem exists_countable_atomic_random_upperLocalEntropy_eq_one :
    ∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      IsMeasureAdmissible cantorPresentation shiftMap μ ∅ ∧
      (∃ S : Set (ℕ → Bool), S.Countable ∧ μ Sᶜ = 0) ∧
      ∃ z ∈ randomPoints cantorPresentation ∅ μ, (localEntropy μ shiftMap z).2 = 1 :=
  exists_countable_atomic_random_upperLocalEntropy_eq_one'

/-- Example 5.5(2), core construction. With the notation of
`exists_countable_atomic_random_upperLocalEntropy_eq_one`, let `f'(y)↾J_i = 0^{|J_i|}` if
`y ∈ E_i` and `y↾J_i` otherwise. Then `μ' = λ ∘ f'⁻¹` is computable, `Φ_{μ'} = (1, 1)`
`μ'`-almost everywhere, and `z' = f'(Ω)` is `μ'`-random with `h̲_{μ'}(σ, z') = 0`, since
`μ'[z'↾N_{i+1}] ≥ 2^{-N_i}` for the infinitely many `i` with `Ω ∈ E_i`.

Formalisation as for Example 5.5(1) (standard presentation `cantorPresentation`). Divergences
from the paper: the conclusion is stated with the lower local entropy at `z'`. Proved in
`Ergodic/ExampleFiveFiveLower.lean`; the almost-everywhere bound is
`-log₂ μ'[f'(y)↾n] ≥ n - k - O(1)` for `n` in the `k`-th block (`k = o(n)`), rather than
`n - O(log n)`. Blueprint node `meas:examples`. -/
theorem exists_random_lowerLocalEntropy_eq_zero :
    ∃ μ' : Measure (ℕ → Bool), IsProbabilityMeasure μ' ∧
      IsMeasureAdmissible cantorPresentation shiftMap μ' ∅ ∧
      (∀ᵐ x ∂μ', localEntropy μ' shiftMap x = (1, 1)) ∧
      ∃ z' ∈ randomPoints cantorPresentation ∅ μ', (localEntropy μ' shiftMap z').1 = 0 :=
  exists_random_lowerLocalEntropy_eq_zero'

/-- Example 5.5(1): on Cantor space with its standard presentation `cantorPresentation` there
is a probability measure `μ` computable from the empty oracle, carried by a countable set,
with `Φ_μ = (0, 0)` almost everywhere (so `ess sup h̄_μ = 0`), and a `μ`-random point `z` which
is not an atom and has upper orbit complexity `K̄(z, σ) = 1`; hence
`ess sup h̄_μ < sup_{x ∈ R^μ} K̄(x, σ)`.

The paper's "computable" and "random" are `IsMeasureAdmissible cantorPresentation shiftMap μ ∅`
and `randomPoints cantorPresentation ∅ μ`.
Proved from `exists_countable_atomic_random_upperLocalEntropy_eq_one`.
Blueprint node `meas:examples`. -/
theorem exampleFiveFive_upper :
    ∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      IsMeasureAdmissible cantorPresentation shiftMap μ ∅ ∧
      (∃ S : Set (ℕ → Bool), S.Countable ∧ μ Sᶜ = 0) ∧
      (∀ᵐ x ∂μ, localEntropy μ shiftMap x = (0, 0)) ∧
      essSup (fun x ↦ (localEntropy μ shiftMap x).2) μ = 0 ∧
      (∃ z ∈ randomPoints cantorPresentation ∅ μ, μ {z} = 0 ∧
        (orbitComplexities cantorPresentation shiftMap ∅ z).2 = 1) ∧
      essSup (fun x ↦ (localEntropy μ shiftMap x).2) μ <
        ⨆ x ∈ randomPoints cantorPresentation ∅ μ,
          (orbitComplexities cantorPresentation shiftMap ∅ x).2 := by
  set P := cantorPresentation
  obtain ⟨μ, hμ, hA, ⟨S, hS, hSμ⟩, z, hz, hz1⟩ :=
    exists_countable_atomic_random_upperLocalEntropy_eq_one
  have hae := ae_localEntropy_eq_zero_of_countable μ shiftMap hS hSμ
  have hess := (essBounds_eq_zero_of_countable μ shiftMap hS hSμ).2.1
  have hK : (orbitComplexities P shiftMap ∅ z).2 = 1 := by
    rw [orbitComplexities_eq_localEntropy P shiftMap continuous_shiftMap_cantor ∅ μ hA hz]
    exact hz1
  have hatom : μ {z} = 0 := by
    by_contra h
    rw [localEntropy_eq_zero_of_measure_singleton_ne_zero μ shiftMap h] at hz1
    exact zero_ne_one hz1
  refine ⟨μ, hμ, hA, ⟨S, hS, hSμ⟩, hae, hess, ⟨z, hz, hatom, hK⟩, ?_⟩
  rw [hess]
  exact zero_lt_one.trans_le
    (hK ▸ le_iSup₂ (f := fun x _ ↦ (orbitComplexities P shiftMap ∅ x).2) z hz)

/-- Example 5.5(2): on Cantor space with its standard presentation `cantorPresentation` there
is a probability measure `μ'` computable from the empty oracle with `Φ_{μ'} = (1, 1)` almost
everywhere, so `ess inf h̲_{μ'} = 1`, and a `μ'`-random point `z'` of lower orbit complexity
`K̲(z', σ) = 0`; hence `inf_{x ∈ R^{μ'}} K̲(x, σ) < ess inf h̲_{μ'}`.

Formalisation as for `exampleFiveFive_upper`. Proved from
`exists_random_lowerLocalEntropy_eq_zero`. Blueprint node `meas:examples`. -/
theorem exampleFiveFive_lower :
    ∃ μ' : Measure (ℕ → Bool), IsProbabilityMeasure μ' ∧
      IsMeasureAdmissible cantorPresentation shiftMap μ' ∅ ∧
      (∀ᵐ x ∂μ', localEntropy μ' shiftMap x = (1, 1)) ∧
      essInf (fun x ↦ (localEntropy μ' shiftMap x).1) μ' = 1 ∧
      (∃ z' ∈ randomPoints cantorPresentation ∅ μ',
        (orbitComplexities cantorPresentation shiftMap ∅ z').1 = 0) ∧
      ⨅ x ∈ randomPoints cantorPresentation ∅ μ',
          (orbitComplexities cantorPresentation shiftMap ∅ x).1 <
        essInf (fun x ↦ (localEntropy μ' shiftMap x).1) μ' := by
  set P := cantorPresentation
  obtain ⟨μ', hμ, hA, hae, z', hz, hz0⟩ := exists_random_lowerLocalEntropy_eq_zero
  have hess : essInf (fun x ↦ (localEntropy μ' shiftMap x).1) μ' = 1 := by
    rw [essInf_congr_ae (g := fun _ ↦ (1 : ℝ≥0∞)) (hae.mono fun x hx ↦ by simp [hx]),
      essInf_const' 1]
  have hK : (orbitComplexities P shiftMap ∅ z').1 = 0 := by
    rw [orbitComplexities_eq_localEntropy P shiftMap continuous_shiftMap_cantor ∅ μ' hA hz]
    exact hz0
  refine ⟨μ', hμ, hA, hae, hess, ⟨z', hz, hK⟩, ?_⟩
  rw [hess]
  exact (hK ▸ iInf₂_le (f := fun x _ ↦ (orbitComplexities P shiftMap ∅ x).1) z' hz).trans_lt
    zero_lt_one

/-! ### The oracle cannot be fixed in Theorem 4.3(b), (c) -/

/-- Consequence of Example 5.5(1) for Theorem 4.3(b): for a fixed admissible oracle `A` the
supremum of the upper orbit complexity over the `A`-random points can exceed `ess sup h̄_μ`
(compare `essSup_upperLocalEntropy_le_iSup_randomPoints`, which gives `≤` for every admissible
`A`), already on Cantor space with its standard presentation `cantorPresentation`.
Blueprint node `meas:examples`. -/
theorem exists_iSup_randomPoints_gt_essSup :
    ∃ (μ : Measure (ℕ → Bool)) (A : Set ℕ),
      IsProbabilityMeasure μ ∧ IsMeasureAdmissible cantorPresentation shiftMap μ A ∧
      essSup (fun x ↦ (localEntropy μ shiftMap x).2) μ <
        ⨆ x ∈ randomPoints cantorPresentation A μ,
          (orbitComplexities cantorPresentation shiftMap A x).2 := by
  obtain ⟨μ, hμ, hA, -, -, -, -, hlt⟩ := exampleFiveFive_upper
  exact ⟨μ, ∅, hμ, hA, hlt⟩

/-- The optimisation over oracles cannot be dropped in Theorem 4.3(b): it is not true that
`ess sup h̄_μ = sup_{x ∈ R_A} K̄^A(x, σ)` for every admissible oracle `A`, already on Cantor space
with the shift. Blueprint node `meas:examples`. -/
theorem not_forall_iSup_randomPoints_eq_essSup :
    ¬ ∀ (P : Presentation (ℕ → Bool)) (μ : Measure (ℕ → Bool)) (A : Set ℕ),
      IsProbabilityMeasure μ → IsMeasureAdmissible P shiftMap μ A →
        ⨆ x ∈ randomPoints P A μ, (orbitComplexities P shiftMap A x).2 =
          essSup (fun x ↦ (localEntropy μ shiftMap x).2) μ := by
  intro h
  obtain ⟨μ, A, hμ, hA, hlt⟩ := exists_iSup_randomPoints_gt_essSup
  exact hlt.ne' (h cantorPresentation μ A hμ hA)

/-- Consequence of Example 5.5(2) for Theorem 4.3(c): for a fixed admissible oracle `A` the
infimum of the lower orbit complexity over the `A`-random points can be below `ess inf h̲_μ`
(compare `iInf_randomPoints_orbitComplexities_le_essInf`), already on Cantor space with its
standard presentation `cantorPresentation`. Blueprint node `meas:examples`. -/
theorem exists_iInf_randomPoints_lt_essInf :
    ∃ (μ : Measure (ℕ → Bool)) (A : Set ℕ),
      IsProbabilityMeasure μ ∧ IsMeasureAdmissible cantorPresentation shiftMap μ A ∧
      ⨅ x ∈ randomPoints cantorPresentation A μ,
          (orbitComplexities cantorPresentation shiftMap A x).1 <
        essInf (fun x ↦ (localEntropy μ shiftMap x).1) μ := by
  obtain ⟨μ, hμ, hA, -, -, -, hlt⟩ := exampleFiveFive_lower
  exact ⟨μ, ∅, hμ, hA, hlt⟩

/-- The optimisation over oracles cannot be dropped in Theorem 4.3(c) for the lower
complexity: it is not true that `ess inf h̲_μ = inf_{x ∈ R_A} K̲^A(x, σ)` for every admissible
oracle `A`. Blueprint node `meas:examples`. -/
theorem not_forall_iInf_randomPoints_eq_essInf :
    ¬ ∀ (P : Presentation (ℕ → Bool)) (μ : Measure (ℕ → Bool)) (A : Set ℕ),
      IsProbabilityMeasure μ → IsMeasureAdmissible P shiftMap μ A →
        ⨅ x ∈ randomPoints P A μ, (orbitComplexities P shiftMap A x).1 =
          essInf (fun x ↦ (localEntropy μ shiftMap x).1) μ := by
  intro h
  obtain ⟨μ, A, hμ, hA, hlt⟩ := exists_iInf_randomPoints_lt_essInf
  exact hlt.ne (h cantorPresentation μ A hμ hA)

end example55

end Kolmogorov.PointToSet
