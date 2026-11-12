/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Defs
import KolmogorovMathlib.Oracle.Universal.Enumeration

/-!
# Basic properties of relative Martin-Löf randomness

This module proves the facts about `IsMartinLofRandomIn` that every use of it needs: randomness
relative to a stronger oracle implies randomness relative to a weaker one, randomness relative to
the empty oracle is the unrelativized `IsMartinLofRandom`, and almost every sequence is random.

## Conventions

Oracles are sets of natural numbers compared by Turing reducibility of their characteristic
functions, `charOracle A ≤ᵀ charOracle B`. Measures are arbitrary measures on `CantorSeq`; the
statements below need no finiteness.

## Main declarations

* `IsMartinLofRandomIn.mono_oracle` (blueprint node `vl:random-in-anti`): if `A ≤_T B`, every
  sequence random relative to `B` is random relative to `A`.
* `isMartinLofRandomIn_empty_iff` (blueprint node `vl:random-in-empty`): randomness relative to
  the empty oracle is `IsMartinLofRandom`.
* `measure_setOf_not_isMartinLofRandomIn` (blueprint node `vl:ae-random`): the non-random
  sequences form a `μ`-null set, for every measure `μ` and every oracle. There are countably many
  tests, since an enumeration computable in the oracle is determined by a code of the universal
  oracle machine (`PointToSet.oracleStage_universal`).
* `IsComputableMeasure.isComputableCantorMeasureIn`, `IsComputableCantorMeasureIn.isFiniteMeasure`
  (blueprint node `vl:computable-measure-in`): a computable measure is computable relative to
  every oracle, and a relatively computable measure is finite.

## Blind randomness

`IsMartinLofRandomIn A μ` quantifies over `A`-c.e. tests whose `μ`-measures are small; the tests
have no access to `μ`. When `μ` is not computable relative to `A` this is blind (Hippocratic)
randomness, not the notion in which tests may also query a representation of `μ`. When `μ` is
`A`-computable the two agree.

Used by `AlgorithmicRandomness/VanLambalgen/`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal
open scoped Computability

variable {A B : Set ℕ} {μ : Measure CantorSeq}

/-! ### Changing the oracle -/

/-- An enumeration computable in `A` is computable in every Turing-stronger oracle. -/
private lemma computableIn₂_mono_oracle {f : ℕ → ℕ → Option BitString}
    (hf : ComputableIn₂ {charOracle A} f) (hAB : charOracle A ≤ᵀ charOracle B) :
    ComputableIn₂ {charOracle B} f := by
  refine RecursiveIn.subst hf fun g hg ↦ ?_
  obtain rfl := Set.mem_singleton_iff.mp hg
  exact hAB

/-- The characteristic function of the empty set is partial recursive. -/
private lemma partrec_charOracle_empty : Partrec (charOracle ∅) := by
  have h : charOracle ∅ = fun _ ↦ Part.some 0 := by
    funext n
    simp [charOracle]
  rw [h]
  exact Partrec.const' _

/-- Computability relative to the empty oracle is computability. -/
private lemma computableIn₂_charOracle_empty_iff {f : ℕ → ℕ → Option BitString} :
    ComputableIn₂ {charOracle ∅} f ↔ Computable₂ f := by
  refine ⟨fun hf ↦ RecursiveIn.partrec_of_oracle (fun g hg ↦ ?_) hf,
    fun hf ↦ hf.computableIn₂⟩
  obtain rfl := Set.mem_singleton_iff.mp hg
  exact partrec_charOracle_empty

/-- Randomness relative to a Turing-stronger oracle implies randomness relative to a weaker one.
Blueprint node `vl:random-in-anti`. -/
theorem IsMartinLofRandomIn.mono_oracle {w : CantorSeq} (hw : IsMartinLofRandomIn B μ w)
    (hAB : charOracle A ≤ᵀ charOracle B) : IsMartinLofRandomIn A μ w := by
  rintro U ⟨⟨f, hf, hU⟩, hμU⟩
  exact hw U ⟨⟨f, computableIn₂_mono_oracle hf hAB, hU⟩, hμU⟩

/-- Joining the empty oracle on the left does not change randomness: `∅ ⊕ B` and `B` are Turing
equivalent. Blueprint node `vl:random-in-anti`. -/
theorem isMartinLofRandomIn_oracleJoin_empty_left {w : CantorSeq} :
    IsMartinLofRandomIn (PointToSet.oracleJoin ∅ B) μ w ↔ IsMartinLofRandomIn B μ w :=
  ⟨fun h ↦ h.mono_oracle (PointToSet.oracle_joins_right ∅ B),
    fun h ↦ h.mono_oracle (PointToSet.oracle_joins_least ∅ B B
      partrec_charOracle_empty.turingReducible TuringReducible.rfl)⟩

/-- Randomness relative to the empty oracle is unrelativized Martin-Löf randomness.
Blueprint node `vl:random-in-empty`. -/
theorem isMartinLofRandomIn_empty_iff {w : CantorSeq} :
    IsMartinLofRandomIn ∅ μ w ↔ IsMartinLofRandom μ w := by
  have htest : ∀ U, IsMartinLofTestIn ∅ μ U ↔ IsMartinLofTest μ U := fun U ↦ by
    simp only [IsMartinLofTestIn, IsMartinLofTest, IsUniformlyEffectiveOpenIn,
      IsUniformlyEffectiveOpen, computableIn₂_charOracle_empty_iff]
  simp only [IsMartinLofRandomIn, IsMartinLofRandom, htest]

/-! ### Almost every sequence is random -/

/-- There are countably many enumerations computable in a fixed oracle: such an enumeration is
determined, through its encoding as a partial function on `ℕ`, by a code of the universal oracle
machine. -/
private lemma countable_setOf_computableIn₂ (A : Set ℕ) :
    {f : ℕ → ℕ → Option BitString | ComputableIn₂ {charOracle A} f}.Countable := by
  -- the encoding of an enumeration as a partial function on `ℕ`
  let G : (ℕ → ℕ → Option BitString) → ℕ →. ℕ := fun f n ↦
    Part.bind ((Encodable.decode (α := ℕ × ℕ) n : Option (ℕ × ℕ)) : Part (ℕ × ℕ))
      fun p : ℕ × ℕ ↦ (Part.some (f p.1 p.2)).map Encodable.encode
  let R : ℕ → ℕ → ℕ → Prop := fun e n v ↦
    ∃ t, PointToSet.oracleStage A t e n = some v
  have hinj : Function.Injective fun f n v ↦ v ∈ G f n := by
    intro f f' h
    funext a b
    have hab := congrFun (congrFun h (Encodable.encode (a, b))) (Encodable.encode (f a b))
    simpa [G] using hab
  refine ((Set.countable_range R).preimage hinj).mono fun f hf ↦ ?_
  obtain ⟨e, he⟩ := PointToSet.oracleStage_universal A (G f) (PartrecIn.iff_nat.mpr hf)
  exact ⟨e, funext fun n ↦ funext fun v ↦ propext (he n v).symm⟩

/-- For every measure and every oracle, the sequences that are not random relative to the oracle
form a null set. Blueprint node `vl:ae-random`. -/
theorem measure_setOf_not_isMartinLofRandomIn (A : Set ℕ) (μ : Measure CantorSeq) :
    μ {w | ¬ IsMartinLofRandomIn A μ w} = 0 := by
  -- the sequence of open sets enumerated by `f`
  let V : (ℕ → ℕ → Option BitString) → ℕ → Set CantorSeq :=
    fun f n ↦ ⋃ i, (f n i).elim ∅ cantorCylinder
  let S : Set (ℕ → ℕ → Option BitString) :=
    {f | ComputableIn₂ {charOracle A} f ∧ ∀ n, μ (V f n) ≤ dyadicValue 1 n}
  have hS : S.Countable := (countable_setOf_computableIn₂ A).mono fun f hf ↦ hf.1
  have hsub : {w | ¬ IsMartinLofRandomIn A μ w} ⊆ ⋃ f ∈ S, ⋂ n, V f n := by
    intro w hw
    simp only [Set.mem_ofPred_eq, IsMartinLofRandomIn] at hw
    push Not at hw
    obtain ⟨U, ⟨⟨f, hf, hUf⟩, hμU⟩, hwU⟩ := hw
    have hUV : U = V f := funext hUf
    subst hUV
    exact Set.mem_biUnion (x := f) ⟨hf, hμU⟩ hwU
  refine measure_mono_null hsub ((measure_biUnion_null_iff hS).mpr fun f hf ↦ ?_)
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hne
  have hdy : dyadicValue 1 n = 2⁻¹ ^ n := by
    rw [dyadicValue, Nat.cast_one, one_div, ENNReal.inv_pow]
  exact (hn.trans_le ((measure_mono (Set.iInter_subset _ n)).trans
    ((hf.2 n).trans_eq hdy))).false

/-! ### Computable measures relative to an oracle -/

/-- A computable measure is computable relative to every oracle.
Blueprint node `vl:computable-measure-in`. -/
theorem IsComputableMeasure.isComputableCantorMeasureIn (hμ : IsComputableMeasure μ)
    (A : Set ℕ) : IsComputableCantorMeasureIn A μ := by
  obtain ⟨a, ha, h⟩ := hμ
  exact ⟨a, ha.computableIn₂, h⟩

/-- A measure computable relative to some oracle is finite: the mass of the empty cylinder,
which is the whole space, is within `1` of a dyadic rational.
Blueprint node `vl:computable-measure-in`. -/
theorem IsComputableCantorMeasureIn.isFiniteMeasure (hμ : IsComputableCantorMeasureIn A μ) :
    IsFiniteMeasure μ := by
  obtain ⟨a, -, h⟩ := hμ
  have hcyl : cantorCylinder [] = Set.univ := by
    ext w
    simp [cantorCylinder, IsCantorPrefix]
  have hbound := (h [] 0).2
  rw [cantorMass, hcyl] at hbound
  refine ⟨hbound.trans_lt (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)⟩ <;>
    exact lt_top_iff_ne_top.2 (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp))

end Kolmogorov
