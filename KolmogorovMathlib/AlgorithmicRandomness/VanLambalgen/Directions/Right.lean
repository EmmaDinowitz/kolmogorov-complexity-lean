/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Pullback
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.OracleUniform.UsePrinciple
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.OracleUniform.Trim

/-!
# van Lambalgen: a random pair has a second coordinate random relative to the first

`IsMartinLofRandomIn.right_of_cantorJoin` (blueprint node `vl:snd`): if `x ⊕ y` is random for
`joinMeasure μ ν` relative to `A`, `μ` is finite and `ν` is computable relative to `A`, then `y`
is random for `ν` relative to `A ⊕ x`. A test `U` relative to `A ⊕ x` is, by the use principle
(`exists_isOracleUniformIn_uniformFamily_eq`), the value at `x` of a family `T^z` oracle-uniform
relative to `A`. Trimming it uniformly in the oracle (`trimUniform`) at the trimming level
`n + c`, where `2^c` bounds `μ(univ)`, gives a family `T̃^z` with `ν(T̃^z) ≤ 2^{-(n+c)}` for every
oracle `z`, which agrees with `U_{n+c+2}` at `x` because `ν(U_{n+c+2}) ≤ 2^{-(n+c+2)}`. The joint
sets `W_n = {z ⊕ y' | y' ∈ T̃^z}` are effectively open relative to `A`, and by Fubini
(`joinMeasure_jointSet`) their measure is `∫⁻ z, ν(T̃^z) ∂μ ≤ 2^{-(n+c)} μ(univ) ≤ 2^{-n}`; they
all contain `x ⊕ y`, contradicting the randomness of `x ⊕ y`.

Used by `AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal
open PointToSet (oracleJoin)

variable {A : Set ℕ} {μ ν : Measure CantorSeq} {x y : CantorSeq}

/-- If the interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A`, then `y` is
random for `ν` relative to `A ⊕ x`. Blueprint node `vl:snd`. -/
theorem IsMartinLofRandomIn.right_of_cantorJoin [IsFiniteMeasure μ]
    (hν : IsComputableCantorMeasureIn A ν)
    (h : IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y)) :
    IsMartinLofRandomIn (oracleJoin A (seqOracle x)) ν y := by
  have := hν.isFiniteMeasure
  intro U hU hyU
  obtain ⟨g, hg, hgx⟩ := exists_isOracleUniformIn_uniformFamily_eq hU.1
  obtain ⟨a, ha, hacc⟩ := hν
  obtain ⟨c, hc⟩ : ∃ c : ℕ, μ Set.univ ≤ ((2 ^ c : ℕ) : ℝ≥0∞) := by
    obtain ⟨c, hc⟩ := ENNReal.exists_nat_gt (measure_ne_top μ Set.univ)
    exact ⟨c, hc.le.trans (by exact_mod_cast Nat.lt_two_pow_self.le)⟩
  have hr : Computable fun n : ℕ => Nat.pair (n + c + 2) (n + c) :=
    (Primrec₂.natPair.comp (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id
      (Primrec.const c)) (Primrec.const 2)) (Primrec.nat_add.comp Primrec.id
        (Primrec.const c))).to_comp
  have hg' := (isOracleUniformIn_trimUniform ha hg).reindex hr
  have hWo := hg'.isUniformlyEffectiveOpenIn_jointSet
  refine h _ ⟨hWo, fun n => ?_⟩ (Set.mem_iInter.2 fun n => ?_)
  · rw [joinMeasure_jointSet (hWo.measurableSet n)]
    have hle : ∀ z, ν (uniformFamily (trimUniform a g) z (Nat.pair (n + c + 2) (n + c))) ≤
        (2 : ℝ≥0∞)⁻¹ ^ (n + c) := fun z => by
      rw [← dyadicValue_one_eq_inv_two_pow']
      exact measure_uniformFamily_trimUniform_le hacc g z _ _
    calc ∫⁻ z, ν (uniformFamily (trimUniform a g) z (Nat.pair (n + c + 2) (n + c))) ∂μ
        ≤ ∫⁻ _, (2 : ℝ≥0∞)⁻¹ ^ (n + c) ∂μ := lintegral_mono hle
      _ = (2 : ℝ≥0∞)⁻¹ ^ (n + c) * μ Set.univ := lintegral_const _
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + c) * 2 ^ c := by
          gcongr
          exact hc.trans (by norm_num)
      _ = dyadicValue 1 n := by
          rw [pow_add, mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
            one_pow, mul_one, dyadicValue_one_eq_inv_two_pow']
  · change cantorJoin x y ∈ jointSet fun z =>
      uniformFamily (trimUniform a g) z (Nat.pair (n + c + 2) (n + c))
    rw [cantorJoin_mem_jointSet, uniformFamily_trimUniform_of_not_mem, hgx]
    · exact Set.mem_iInter.1 hyU _
    · intro hmem
      have hlt := lt_measure_of_mem_discardSet hacc hmem
      rw [hgx] at hlt
      have hU' := hU.2 (n + c + 2)
      rw [dyadicValue_one_eq_inv_two_pow'] at hU'
      exact absurd hU' (not_le.2 hlt)

end Kolmogorov
