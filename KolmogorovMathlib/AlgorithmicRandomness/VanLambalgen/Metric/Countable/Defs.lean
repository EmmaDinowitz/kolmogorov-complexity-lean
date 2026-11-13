/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Defs
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Countable.Defs
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Countable products of presented metric spaces: definitions

The countable form of the van Lambalgen theorem on a presented space `X` is about sequences
`x : ℕ → X` and a sequence of measures `μ i` on `X`. This file defines the presentation of `ℕ → X`,
uniform computability of a sequence of measures, the product basis of a basis of `X`, and the
mixture `∑ᵢ 2^{-(i+1)} μ i` through which one almost decidable basis serves every `μ i`.

## Conventions

The metric on `ℕ → X` is Mathlib's `PiCountable.metricSpace`,
`dist x y = ∑' i, min (2⁻¹ ^ i) (dist (x i) (y i))`. Mathlib does not register it as a global
instance; it is a local instance here and in the files stating results about `ℕ → X`. Its
uniformity, hence its topology, is definitionally the product one, so it agrees with
`MeasurableSpace.pi` and `Measure.infinitePi`.

The ideal point of `Presentation.pi P` with index `n` decodes `n` as a list `l` of indices and has
coordinate `j` equal to `P.ι (l.getD j 0)`: finitely many coordinates are prescribed, the rest
are `P.ι 0`.

The product basis `piBasis B` has, at the index `pair j k`, the set of sequences whose `j`-th
coordinate lies in `B k`, so the itinerary of `x` is the infinite join `cantorPiJoin` of the
itineraries of its coordinates.

## Main definitions

* `Presentation.pi` (blueprint node `vlm:pi-presentation`): the presentation of `ℕ → X`.
* `IsComputableMeasureFamilyIn` (blueprint node `vlm:measure-family`): a sequence of measures
  computable relative to `A`, uniformly in the index.
* `piBasis` (blueprint node `vlm:pi-basis`): the product of a family of sets of `X` over the
  coordinates.
* `mixMeasure` (blueprint node `vlm:mix`): the mixture `∑ᵢ 2^{-(i+1)} μ i`.

Used by `AlgorithmicRandomness/VanLambalgen/Metric/Countable/`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped ENNReal

variable {X : Type*} [MetricSpace X]

/-- The sequences listed by finite lists of ideal indices are dense in `ℕ → X` (product topology):
a basic open set constrains finitely many coordinates, each to an open set containing an ideal
point. Blueprint node `vlm:pi-presentation`. -/
theorem Presentation.denseRange_piIdeal (P : Presentation X) :
    DenseRange fun n : ℕ => fun j : ℕ =>
      P.ι (((Encodable.decode (α := List ℕ) n).getD []).getD j 0) := by
  refine dense_iff_inter_open.2 fun U hU ⟨y, hy⟩ => ?_
  obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hU y hy
  have hg : ∀ a, ∃ n, a ∈ I → P.ι n ∈ u a := by
    intro a
    by_cases ha : a ∈ I
    · obtain ⟨n, hn⟩ := P.dense.exists_mem_open (hu a ha).1 ⟨y a, (hu a ha).2⟩
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose g hg using hg
  refine ⟨fun j => P.ι (((List.range (I.sup id + 1)).map g).getD j 0), hIU fun a ha => ?_,
    Encodable.encode ((List.range (I.sup id + 1)).map g), by simp⟩
  have hlen : a < ((List.range (I.sup id + 1)).map g).length := by
    simpa using Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  change P.ι (((List.range (I.sup id + 1)).map g).getD a 0) ∈ u a
  rw [List.getD_eq_getElem _ _ hlen, List.getElem_map, List.getElem_range]
  exact hg a ha

attribute [local instance] PiCountable.metricSpace in
/-- The presentation of `ℕ → X` (metric `PiCountable.metricSpace`): the ideal point of index `n`
has coordinate `j` equal to `P.ι (l.getD j 0)`, where `l` is the list of indices decoded from `n`.
Blueprint node `vlm:pi-presentation`. -/
def Presentation.pi (P : Presentation X) : Presentation (ℕ → X) where
  ι n j := P.ι (((Encodable.decode (α := List ℕ) n).getD []).getD j 0)
  dense := P.denseRange_piIdeal
  complete := by
    have := P.complete
    infer_instance

variable [MeasurableSpace X]

/-- A sequence of measures is computable relative to `A`, uniformly in the index: the measures of
the finite unions of basic balls are lower semicomputable relative to `A`, uniformly in the index
and the list of balls. Blueprint node `vlm:measure-family`. -/
def IsComputableMeasureFamilyIn (P : Presentation X) (A : Set ℕ) (μ : ℕ → Measure X) : Prop :=
  IsLowerSemicomputableIn A fun p : ℕ × List (ℕ × ℚ) => (μ p.1 (ballUnion P p.2)).toReal

/-- The product of a family of sets of `X` over the coordinates of `ℕ → X`: at the index
`pair j k`, the sequences whose `j`-th coordinate lies in `B k`. Blueprint node `vlm:pi-basis`. -/
def piBasis (B : ℕ → Set X) : ℕ → Set (ℕ → X) :=
  fun n => {x | x (Nat.unpair n).1 ∈ B (Nat.unpair n).2}

/-- The mixture `∑ᵢ 2^{-(i+1)} μ i` of a sequence of measures; a probability measure when every
`μ i` is one. Blueprint node `vlm:mix`. -/
noncomputable def mixMeasure (μ : ℕ → Measure X) : Measure X :=
  Measure.sum fun i => ((2 : ℝ≥0∞)⁻¹ ^ (i + 1)) • μ i

end Kolmogorov.PointToSet
