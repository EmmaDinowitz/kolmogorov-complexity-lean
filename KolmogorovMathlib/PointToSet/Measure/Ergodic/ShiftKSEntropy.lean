/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Ergodic.FinePartitions
import KolmogorovMathlib.PointToSet.Measure.Ergodic.VyuginGenericity
import KolmogorovMathlib.PointToSet.Measure.Ergodic.Proposition710

/-!
# The entropy of a shift is its Kolmogorov–Sinai entropy

On a one-sided shift `ℕ → α` over a finite alphabet with a first-difference metric
`d(x, y) = β ^ firstDiff x y` (`0 < β < 1`), the entropy used in Proposition 7.10 of
*Entropy of non-invariant measures and orbit complexity of random points*,
`shiftEntropy ν = inf_{k ≥ 1} H_ν(ξ^k) / k` (`ShiftGeneric.lean`, cylinders of length `k`), is the
Kolmogorov–Sinai entropy `Ergodic.ksEntropy ν shiftMap` of the companion note *Orbit complexity
of Martin-Löf random points equals entropy*, for every shift-invariant probability measure `ν`.

* `shiftKS_symbolPartition`: the partition `ξ = {[a] : a ∈ α}` by the first symbol;
  `shiftKS_refinement_eq_wordCylinder`: its refinement `ξ^n = ⋁_{j<n} σ^{-j} ξ` is the partition
  into the cylinders of length `n`, so `shiftKS_shiftEntropy_eq_entropyRate`:
  `shiftEntropy ν = h_ν(σ, ξ)`.
* `shiftKS_shiftEntropy_eq_ksEntropy`: `shiftEntropy ν = h_ν(σ)`. Proof: `h_ν(σ, ξ) ≤ h_ν(σ)` by
  definition. Conversely the partitions `ξ^k` have cells of diameter `≤ β^k → 0`, so
  `h_ν(σ, ξ^k) → h_ν(σ)` (Walters 8.3, `Ergodic.tendsto_entropyRate_ksEntropy`; the space is
  compact by `vyuginGen_compactSpace`), and `h_ν(σ, ξ^k) ≤ h_ν(σ, ξ)`: the partition `ξ^{n+k}`
  refines `(ξ^k)^n`, whence `H_ν((ξ^k)^n) ≤ H_ν(ξ^{n+k}) ≤ H_ν(ξ^n) + H_ν(ξ^k)`; divide by `n`
  and let `n → ∞`.
* Proposition 7.10 in Kolmogorov–Sinai form: `shiftKS_upperOrbitComplexity_le_ksEntropy`
  (7.10(i)) and `shiftKS_orbitComplexities_eq_ksEntropy` (7.10(ii)), from
  `upperOrbitComplexity_le_shiftEntropy` and `orbitComplexities_eq_shiftEntropy`.

Blueprint node `erg:prop710`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-! ### The partition by the first symbol -/

section shift

variable {α : Type*} [Fintype α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] {β : ℝ}

omit [Fintype α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] in
/-- The iterates of the shift: `(σ^j x)_i = x_{i + j}`. -/
private lemma shiftKS_iterate_apply (x : ℕ → α) (j i : ℕ) : (shiftMap^[j] x) i = x (i + j) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih]
    rfl

/-- The partition `ξ` of the shift by the first symbol: `ξ_a = [a] = {y | y 0 = a}`.
Blueprint node `erg:prop710`. -/
def shiftKS_symbolPartition (a : α) : Set (ℕ → α) :=
  {y | y 0 = a}

omit [Fintype α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] in
/-- The cells of `ξ^n = ⋁_{j<n} σ^{-j} ξ` are the cylinders of length `n`:
`⋂_{j<n} σ^{-j} [w_j] = [w]`. Blueprint node `erg:prop710`. -/
theorem shiftKS_refinement_eq_wordCylinder (n : ℕ) (w : Fin n → α) :
    Ergodic.refinement shiftMap shiftKS_symbolPartition n w = wordCylinder w := by
  ext y
  simp [Ergodic.refinement, wordCylinder, shiftKS_symbolPartition, shiftKS_iterate_apply]

omit [MetricSpace (ℕ → α)] in
/-- `H_ν(ξ^n)` is the block entropy of length `n`. Blueprint node `erg:prop710`. -/
theorem shiftKS_blockEntropy_eq_refinementEntropy [DecidableEq α] (ν : Measure (ℕ → α))
    (n : ℕ) :
    blockEntropy ν n = Ergodic.refinementEntropy ν shiftMap shiftKS_symbolPartition n := by
  simp only [blockEntropy, Ergodic.refinementEntropy, Ergodic.partitionEntropy,
    Ergodic.entropyTerm, shiftKS_refinement_eq_wordCylinder]

omit [MetricSpace (ℕ → α)] in
/-- `shiftEntropy ν = h_ν(σ, ξ)`: the entropy of the shift used in Proposition 7.10 is the
entropy rate of the partition by the first symbol (for every measure `ν`).
Blueprint node `erg:prop710`. -/
theorem shiftKS_shiftEntropy_eq_entropyRate [DecidableEq α] (ν : Measure (ℕ → α)) :
    shiftEntropy ν = Ergodic.entropyRate ν shiftMap shiftKS_symbolPartition := by
  simp only [shiftEntropy, Ergodic.entropyRate, shiftKS_blockEntropy_eq_refinementEntropy]

omit [Fintype α] in
/-- For a first-difference metric the partition by the first symbol is a finite measurable
partition. Blueprint node `erg:prop710`. -/
theorem shiftKS_isMeasurablePartition [BorelSpace (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) :
    Ergodic.IsMeasurablePartition (shiftKS_symbolPartition (α := α)) := by
  refine ⟨fun a ↦ ?_, fun a b hab ↦ ?_, ?_⟩
  · have := (vyuginGen_isClopen_setOf_apply_mem hβ hβ₁ hd 0 {a}).isOpen.measurableSet
    simpa [shiftKS_symbolPartition] using this
  · refine Set.disjoint_left.2 fun y ha hb ↦ hab ?_
    simp only [shiftKS_symbolPartition, mem_ofPred_eq] at ha hb
    rw [← ha, ← hb]
  · exact Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y 0, rfl⟩

omit [Fintype α] [MeasurableSpace (ℕ → α)] in
/-- For a first-difference metric a cylinder of length `k` has diameter at most `β^k`. -/
private lemma shiftKS_diam_wordCylinder_le (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {k : ℕ}
    (w : Fin k → α) : Metric.diam (wordCylinder w) ≤ β ^ k := by
  refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy ↦ ?_
  by_cases hxy : x = y
  · rw [hxy, dist_self]
    positivity
  rw [hd x y hxy]
  refine pow_le_pow_of_le_one hβ.le hβ₁.le ?_
  refine le_of_not_gt fun hlt ↦ ?_
  simp only [wordCylinder, mem_ofPred_eq] at hx hy
  exact PiNat.apply_firstDiff_ne hxy ((hx ⟨_, hlt⟩).trans (hy ⟨_, hlt⟩).symm)

omit [Fintype α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] in
/-- `ξ^{n+k}` refines `(ξ^k)^n`. -/
private lemma shiftKS_refines (n k : ℕ) :
    Ergodic.Refines (Ergodic.refinement shiftMap (shiftKS_symbolPartition (α := α)) (n + k))
      (Ergodic.refinement shiftMap
        (Ergodic.refinement shiftMap (shiftKS_symbolPartition (α := α)) k) n) := by
  intro v
  refine ⟨fun j i ↦ v ⟨i + j, by omega⟩, fun y hy ↦ ?_⟩
  have hfun : Ergodic.refinement shiftMap (shiftKS_symbolPartition (α := α)) k =
      fun w ↦ wordCylinder w := funext (shiftKS_refinement_eq_wordCylinder k)
  rw [shiftKS_refinement_eq_wordCylinder] at hy
  rw [hfun]
  simp only [Ergodic.refinement, wordCylinder, mem_iInter, mem_preimage, mem_ofPred_eq,
    shiftKS_iterate_apply] at hy ⊢
  exact fun j i ↦ hy ⟨_, _⟩

omit [MetricSpace (ℕ → α)] in
/-- `h_ν(σ, ξ^k) ≤ h_ν(σ, ξ)` for a shift-invariant probability measure. -/
private lemma shiftKS_entropyRate_refinement_le [DecidableEq α] {ν : Measure (ℕ → α)}
    [IsProbabilityMeasure ν] (hν : MeasurePreserving shiftMap ν ν)
    (hξ : Ergodic.IsMeasurablePartition (shiftKS_symbolPartition (α := α))) (k : ℕ) :
    Ergodic.entropyRate ν shiftMap (Ergodic.refinement shiftMap shiftKS_symbolPartition k) ≤
      Ergodic.entropyRate ν shiftMap shiftKS_symbolPartition := by
  set c := Ergodic.refinementEntropy ν shiftMap shiftKS_symbolPartition k
  have hlim : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal (Ergodic.refinementEntropy ν shiftMap shiftKS_symbolPartition n / n) +
        ENNReal.ofReal (c / n)) atTop
      (𝓝 (Ergodic.entropyRate ν shiftMap shiftKS_symbolPartition + 0)) := by
    refine (Ergodic.tendsto_refinementEntropy_div hν hξ).add ?_
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat c)
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  refine (iInf₂_le n hn : Ergodic.entropyRate ν shiftMap _ ≤ _).trans
    ((ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le)
  rw [← add_div]
  gcongr
  calc Ergodic.refinementEntropy ν shiftMap
        (Ergodic.refinement shiftMap shiftKS_symbolPartition k) n
      ≤ Ergodic.refinementEntropy ν shiftMap shiftKS_symbolPartition (n + k) :=
        Ergodic.partitionEntropy_le_of_refines ν
          ((hξ.refinement hν.measurable k).refinement hν.measurable n)
          (hξ.refinement hν.measurable (n + k)) (shiftKS_refines n k)
    _ ≤ _ := Ergodic.refinementEntropy_add_le hν hξ n k

/-- The entropy `shiftEntropy ν = inf_{k ≥ 1} H_ν(ξ^k) / k` of Proposition 7.10 is the
Kolmogorov–Sinai entropy `h_ν(σ)` of the shift, for every shift-invariant probability measure
`ν` on `ℕ → α` (finite alphabet, first-difference metric). Blueprint node `erg:prop710`. -/
theorem shiftKS_shiftEntropy_eq_ksEntropy [BorelSpace (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν] (hν : MeasurePreserving shiftMap ν ν) :
    shiftEntropy ν = Ergodic.ksEntropy ν shiftMap := by
  classical
  have := vyuginGen_compactSpace hβ hβ₁ hd
  have hξ := shiftKS_isMeasurablePartition hβ hβ₁ hd
  rw [shiftKS_shiftEntropy_eq_entropyRate]
  refine le_antisymm (Ergodic.entropyRate_le_ksEntropy ν shiftMap hξ) ?_
  have hlim := Ergodic.tendsto_entropyRate_ksEntropy hν
    (p := fun k ↦ Fintype.card (Fin k → α))
    (P := fun k ↦ Ergodic.refinement shiftMap shiftKS_symbolPartition k ∘
      (Fintype.equivFin (Fin k → α)).symm)
    (fun k ↦ (hξ.refinement hν.measurable k).comp_equiv _) (r := fun k ↦ β ^ k)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ₁) (fun k i ↦ by
      simp only [Function.comp_apply, shiftKS_refinement_eq_wordCylinder]
      exact shiftKS_diam_wordCylinder_le hβ hβ₁ hd _)
  refine le_of_tendsto' hlim fun k ↦ ?_
  rw [Ergodic.entropyRate_comp_equiv]
  exact shiftKS_entropyRate_refinement_le hν hξ k

/-! ### Proposition 7.10 with the Kolmogorov–Sinai entropy -/

omit [Fintype α] in
/-- Proposition 7.10(i) in Kolmogorov–Sinai form: at a generic point `x` of a shift-invariant
probability measure `ν`, `K̄^A(x, σ) ≤ h_ν(σ)` (`Ergodic.ksEntropy`). Hypotheses as in
`upperOrbitComplexity_le_shiftEntropy`, with `Finite α` for `Fintype α`. Blueprint node
`erg:prop710`. -/
theorem shiftKS_upperOrbitComplexity_le_ksEntropy [Finite α] [Primcodable α]
    [BorelSpace (ℕ → α)]
    (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν] (hν : MeasurePreserving shiftMap ν ν)
    {x : ℕ → α} (hx : IsGenericPoint ν x) :
    (orbitComplexities P shiftMap A x).2 ≤ Ergodic.ksEntropy ν shiftMap := by
  have := Fintype.ofFinite α
  rw [← shiftKS_shiftEntropy_eq_ksEntropy hβ hβ₁ hd ν hν]
  exact upperOrbitComplexity_le_shiftEntropy hβ hβ₁ hd P A hP ν hν hx

omit [Fintype α] in
/-- Proposition 7.10(ii) in Kolmogorov–Sinai form: if `ν` is ergodic and `x` is `ν`-random
relative to an oracle `B` admissible for `ν`, then `K̲^A(x, σ) = K̄^A(x, σ) = h_ν(σ)`
(`Ergodic.ksEntropy`) for every `A ≤_T B`. Hypotheses as in `orbitComplexities_eq_shiftEntropy`,
with `Finite α` for `Fintype α`.
Blueprint node `erg:prop710`. -/
theorem shiftKS_orbitComplexities_eq_ksEntropy [Finite α] [Primcodable α]
    [BorelSpace (ℕ → α)]
    (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (ν : Measure (ℕ → α)) [IsProbabilityMeasure ν]
    (hν : Ergodic shiftMap ν) {B : Set ℕ} (hB : IsMeasureAdmissible P shiftMap ν B)
    {x : ℕ → α} (hx : x ∈ randomPoints P B ν) {A : Set ℕ}
    (hAB : charOracle A ≤ᵀ charOracle B)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    orbitComplexities P shiftMap A x =
      (Ergodic.ksEntropy ν shiftMap, Ergodic.ksEntropy ν shiftMap) := by
  have := Fintype.ofFinite α
  rw [← shiftKS_shiftEntropy_eq_ksEntropy hβ hβ₁ hd ν hν.toMeasurePreserving]
  exact orbitComplexities_eq_shiftEntropy hβ hβ₁ hd P ν hν hB hx hAB hP

end shift

end Kolmogorov.PointToSet
