/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Computable

/-!
# Martin-Löf randomness on a presented metric space, relative to an oracle

A `μ`-test relative to `A` is a uniformly `A`-c.e. open sequence `(U_m)` with
`μ(U_m) ≤ 2^{-m}` (`IsMeasureTestIn`). A point is `μ`-random relative to `A` when it lies in
`⋂_m U_m` for no such test; `randomPoints P A μ` is the set `R_A = R_A^μ` of these points
(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*, §2.2).

* `measure_compl_randomPoints`: `μ(R_A) = 1`, in the form that the complement is `μ`-null
  (there are countably many tests, since there are countably many `A`-r.e. predicates:
  `countable_setOf_isREIn`).
* `randomPoints_anti_oracle`: `R_B ⊆ R_A` when `B ≥_T A`.
* `exists_mem_randomPoints_of_measure_pos`: a set of positive outer measure contains a random
  point.

Blueprint node `meas:random`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- A `μ`-test relative to `A`: a uniformly `A`-c.e. open sequence of sets with
`μ(U_m) ≤ 2^{-m}`. Blueprint node `meas:random`. -/
def IsMeasureTestIn (P : Presentation X) (A : Set ℕ) (μ : Measure X) (U : ℕ → Set X) : Prop :=
  IsCeOpenFamilyIn P A U ∧ ∀ m, μ (U m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m

/-- The set `R_A^μ` of points that are `μ`-random relative to `A`: those lying in the
intersection of no `μ`-test relative to `A`. Blueprint node `meas:random`. -/
def randomPoints (P : Presentation X) (A : Set ℕ) (μ : Measure X) : Set X :=
  {x | ∀ U : ℕ → Set X, IsMeasureTestIn P A μ U → ∃ m, x ∉ U m}

/-- A test relative to `A` is a test relative to every Turing-stronger oracle. -/
theorem IsMeasureTestIn.mono_oracle {P : Presentation X} {A B : Set ℕ} {μ : Measure X}
    {U : ℕ → Set X} (hU : IsMeasureTestIn P A μ U) (hAB : charOracle A ≤ᵀ charOracle B) :
    IsMeasureTestIn P B μ U := by
  exact ⟨isCeOpenFamilyIn_mono P A hAB hU.1, hU.2⟩

/-- Randomness relative to a stronger oracle implies randomness relative to a weaker one:
`R_B ⊆ R_A` when `B ≥_T A`. Blueprint node `meas:random`. -/
theorem randomPoints_anti_oracle (P : Presentation X) {A B : Set ℕ} (μ : Measure X)
    (hAB : charOracle A ≤ᵀ charOracle B) : randomPoints P B μ ⊆ randomPoints P A μ := by
  intro x hx U hU
  exact hx U (hU.mono_oracle hAB)

/-- A point is random as soon as it avoids one level of every test whose levels have measure
at most `2^{-m} c` for a fixed constant `c`: tests may be shifted.
Blueprint node `meas:random`. -/
theorem not_forall_mem_of_mem_randomPoints {P : Presentation X} {A : Set ℕ} {μ : Measure X}
    {x : X} (hx : x ∈ randomPoints P A μ) {U : ℕ → Set X} (hU : IsCeOpenFamilyIn P A U)
    {c : ℕ} (hμ : ∀ m, μ (U m) ≤ (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ m) : ∃ m, x ∉ U m := by
  have hg : Computable fun m : ℕ ↦ m + c :=
    (Primrec.nat_add.comp Primrec.id (Primrec.const c)).to_comp
  have htest : IsMeasureTestIn P A μ fun m ↦ U (m + c) := by
    refine ⟨hU.comp hg, fun m ↦ (hμ (m + c)).trans_eq ?_⟩
    rw [pow_add, ← mul_assoc, mul_comm ((2 : ℝ≥0∞) ^ c), mul_assoc, ← mul_pow,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]
  obtain ⟨m, hm⟩ := hx _ htest
  exact ⟨m + c, hm⟩

/-- There are countably many predicates relatively enumerable in a fixed oracle: such a
predicate is determined, through `Encodable.encode`, by a code of the universal oracle machine. -/
theorem countable_setOf_isREIn {α : Type*} [Primcodable α] (A : Set ℕ) :
    {F : α → Prop | IsREIn A F}.Countable := by
  refine (countable_range fun e : ℕ ↦ fun a : α ↦
    ∃ v t, oracleStage A t e (Encodable.encode a) = some v).mono ?_
  rintro F hF
  -- the predicate transported to the natural numbers
  have hG : IsREIn A fun n : ℕ ↦ ∃ a : α, Encodable.encode a = n ∧ F a := by
    obtain ⟨e, he, henum⟩ := (relative_enumeration A F).mp hF
    refine (relative_enumeration A _).mpr ⟨fun t ↦ (e t).map Encodable.encode, ?_, fun n ↦ ?_⟩
    · have hm : Computable fun o : Option α ↦ o.map Encodable.encode :=
        Computable.option_map Computable.id (Computable.encode.comp Computable.snd).to₂
      exact hm.computableIn.comp he
    · constructor
      · rintro ⟨a, rfl, ha⟩
        obtain ⟨t, ht⟩ := (henum a).mp ha
        exact ⟨t, by simp [ht]⟩
      · rintro ⟨t, ht⟩
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp ht
        exact ⟨a, rfl, (henum a).mpr ⟨t, ha⟩⟩
  obtain ⟨f, hf, hfG⟩ := hG
  obtain ⟨e, he⟩ := oracleStage_universal A f hf
  refine ⟨e, funext fun a ↦ propext ?_⟩
  have hdom : (∃ v t, oracleStage A t e (Encodable.encode a) = some v) ↔
      (f (Encodable.encode a)).Dom := by
    rw [Part.dom_iff_mem]
    exact exists_congr fun v ↦ (he _ v).symm
  change (∃ v t, oracleStage A t e (Encodable.encode a) = some v) ↔ F a
  rw [hdom, ← hfG]
  exact ⟨fun ⟨b, hb, hFb⟩ ↦ Encodable.encode_injective hb ▸ hFb, fun h ↦ ⟨a, rfl, h⟩⟩

/-- There are countably many tests, so the non-random points form a null set: `μ(R_A) = 1`
for a probability measure. Blueprint node `meas:random`. -/
theorem measure_compl_randomPoints [BorelSpace X] (P : Presentation X) (A : Set ℕ)
    (μ : Measure X) : μ (randomPoints P A μ)ᶜ = 0 := by
  classical
  -- the family of sets described by an index predicate
  let V : (ℕ × (ℕ × ℚ) → Prop) → ℕ → Set X := fun E m ↦ ⋃ b ∈ {b | E (m, b)}, basicBall P b
  let S : Set (ℕ × (ℕ × ℚ) → Prop) := {E | IsREIn A E ∧ ∀ m, μ (V E m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m}
  have hS : S.Countable := (countable_setOf_isREIn A).mono fun E hE ↦ hE.1
  have hsub : (randomPoints P A μ)ᶜ ⊆ ⋃ E ∈ S, ⋂ m, V E m := by
    intro x hx
    simp only [randomPoints, mem_compl_iff, mem_ofPred_eq, not_forall, not_exists,
      not_not] at hx
    obtain ⟨U, ⟨⟨E, hE, hUE⟩, hμU⟩, hxU⟩ := hx
    have hUV : U = V E := funext hUE
    subst hUV
    exact mem_biUnion (x := E) ⟨hE, hμU⟩ (mem_iInter.mpr hxU)
  refine measure_mono_null hsub ((measure_biUnion_null_iff hS).mpr fun E hE ↦ ?_)
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hne
  exact (hn.trans_le ((measure_mono (iInter_subset _ n)).trans (hE.2 n))).false

/-- Almost every point is random. -/
theorem ae_mem_randomPoints [BorelSpace X] (P : Presentation X) (A : Set ℕ) (μ : Measure X) :
    ∀ᵐ x ∂μ, x ∈ randomPoints P A μ := by
  rw [ae_iff]
  exact measure_compl_randomPoints P A μ

/-- A set of positive outer measure contains a random point. Blueprint node `meas:random`. -/
theorem exists_mem_randomPoints_of_measure_pos [BorelSpace X] (P : Presentation X) (A : Set ℕ)
    (μ : Measure X) {Z : Set X} (hZ : μ Z ≠ 0) : ∃ x ∈ Z, x ∈ randomPoints P A μ := by
  by_contra h
  exact hZ (measure_mono_null (fun x hx hxR ↦ h ⟨x, hx, hxR⟩) (measure_compl_randomPoints P A μ))

end Kolmogorov.PointToSet
