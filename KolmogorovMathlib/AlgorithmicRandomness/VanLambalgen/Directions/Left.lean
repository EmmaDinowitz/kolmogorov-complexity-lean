/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Pullback
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs

/-!
# van Lambalgen: a random pair has a random first coordinate

`IsMartinLofRandomIn.left_of_cantorJoin` (blueprint node `vl:fst`): if `x ⊕ y` is random for
`joinMeasure μ ν` relative to `A` and `ν` is finite, then `x` is random for `μ` relative to `A`.
A test `U` for `x` gives the test `{x' ⊕ y' | x' ∈ U_{n+c}}` for pairs, where `2^c` bounds
`ν(univ)`: its measure is `μ(U_{n+c}) ν(univ)` by `Measure.prod_prod`. No hypothesis on `μ`.

Used by `AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal
open PointToSet (oracleJoin)

variable {A : Set ℕ} {μ ν : Measure CantorSeq} {x y : CantorSeq}

/-- If the interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A`, then `x` is
random for `μ` relative to `A`. Blueprint node `vl:fst`. -/
theorem IsMartinLofRandomIn.left_of_cantorJoin [IsFiniteMeasure ν]
    (h : IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y)) :
    IsMartinLofRandomIn A μ x := by
  intro U hU hx
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ν Set.univ ≤ ((2 ^ c : ℕ) : ℝ≥0∞) := by
    obtain ⟨c, hc⟩ := ENNReal.exists_nat_gt (measure_ne_top ν Set.univ)
    exact ⟨c, hc.le.trans (by exact_mod_cast Nat.lt_two_pow_self.le)⟩
  have hUc : IsUniformlyEffectiveOpenIn A fun n => U (n + c) := by
    obtain ⟨f, hf, hfU⟩ := hU.1
    exact ⟨fun n i => f (n + c) i,
      hf.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const c)).to_comp.computableIn
        ComputableIn.snd,
      fun n => hfU (n + c)⟩
  have hjoin : Measurable fun p : CantorSeq × CantorSeq => cantorJoin p.1 p.2 := by
    refine Measurable.of_eval fun n => ?_
    by_cases h : n % 2 = 0
    · simp only [cantorJoin, h, ↓reduceIte]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [cantorJoin, h, ↓reduceIte]
      exact (measurable_pi_apply _).comp measurable_snd
  have heven : Measurable fun z : CantorSeq => z ∘ (2 * ·) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  have hleft : ∀ x' y' : CantorSeq, cantorJoin x' y' ∘ (2 * ·) = x' := fun x' y' =>
    funext fun j => by simp [cantorJoin]
  refine h (fun n => (fun z : CantorSeq => z ∘ (2 * ·)) ⁻¹' U (n + c))
    ⟨hUc.preimage_precomp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id), fun n => ?_⟩ ?_
  · have hpre : (fun p : CantorSeq × CantorSeq => cantorJoin p.1 p.2) ⁻¹'
        ((fun z : CantorSeq => z ∘ (2 * ·)) ⁻¹' U (n + c)) = U (n + c) ×ˢ Set.univ := by
      ext ⟨x', y'⟩
      simp [hleft]
    rw [joinMeasure, Measure.map_apply hjoin (heven (hUc.measurableSet n)), hpre,
      Measure.prod_prod]
    calc μ (U (n + c)) * ν Set.univ ≤ dyadicValue 1 (n + c) * ((2 ^ c : ℕ) : ℝ≥0∞) :=
          mul_le_mul' (hU.2 (n + c)) hc
      _ = dyadicValue 1 n := by
          rw [mul_comm, ← dyadicValue_natCast_mul_left, dyadicValue_two_pow_mul_add]
  · simp only [Set.mem_iInter, Set.mem_preimage, hleft]
    exact fun n => Set.mem_iInter.1 hx (n + c)

end Kolmogorov
