/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs
import KolmogorovMathlib.PointToSet.Measure.Randomness

/-!
# The van Lambalgen theorem on presented metric spaces: definitions

The van Lambalgen theorem moves from Cantor space to presented metric spaces (`Presentation`,
randomness `randomPoints`) through the method of Hoyrup and Rojas: a basis of open sets whose
boundaries are effectively `μ`-null (an *almost decidable basis*) turns every point `x` into its
itinerary, the sequence of bits `x ∈ B k`, which carries `μ` to a measure on Cantor space and
preserves randomness in both directions.

## Conventions

A point is not an oracle, so "random relative to `x`" is stated through a Cauchy name `a` of `x`,
encoded as an oracle by its graph `nameOracle a = {⟨p, a p⟩}`. Names of one point can differ in
degree; the theorem asserts randomness relative to `A ⊕ a` for *some* name `a` (the itinerary of a
random point computes a name and is computed by every name, so this is the weakest name).

The product presentation `P.prod Q` lists the pairs of ideal points through `Nat.unpair`; its
metric is Mathlib's sup metric on `X × Y`. The product basis `prodBasis B C` puts the sets
`B k × Y` on the even indices and `X × C k` on the odd ones, matching `cantorJoin`.

An almost decidable basis relative to `A` for `μ` (`IsAlmostDecidableBasisIn`) is a family `B` of
open sets, uniformly c.e. open relative to `A`, with:
* exteriors: uniformly c.e. open sets `D k` disjoint from `B k`;
* null boundaries, effectively: the set `(B k ∪ D k)ᶜ` is covered at every level `n` by a
  uniformly c.e. open set of `μ`-measure at most `2^{-n}`;
* generation: every basic ball is an `A`-c.e. union of finite intersections of the `B k`.

## Main definitions

* `nameOracle` (blueprint node `vlm:name-oracle`): the graph of a name, as an oracle.
* `Presentation.prod` (blueprint node `vlm:prod-presentation`): the product presentation.
* `IsAlmostDecidableBasisIn` (blueprint node `vlm:ad-basis`): almost decidable bases.
* `itinerary` (blueprint node `vlm:itinerary`): the itinerary of a point in a family of sets.
* `prodBasis` (blueprint node `vlm:prod-basis`): the product of two families, interleaved.

Used by `AlgorithmicRandomness/VanLambalgen/Metric/`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped ENNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- The graph `{⟨p, a p⟩}` of a function `a : ℕ → ℕ`, as an oracle: the number `n` belongs to it
when `a (unpair n).1 = (unpair n).2`. For a Cauchy name `a` of a point `x`, oracles of the form
`A ⊕ nameOracle a` relativize to `x`. Blueprint node `vlm:name-oracle`. -/
def nameOracle (a : ℕ → ℕ) : Set ℕ := {n | a (Nat.unpair n).1 = (Nat.unpair n).2}

/-- The product of two presentations: the ideal point of index `n` is the pair of the ideal points
of indices `(unpair n).1` and `(unpair n).2`. The metric is Mathlib's sup metric on `X × Y`.
Blueprint node `vlm:prod-presentation`. -/
def Presentation.prod (P : Presentation X) (Q : Presentation Y) : Presentation (X × Y) where
  ι n := (P.ι (Nat.unpair n).1, Q.ι (Nat.unpair n).2)
  dense := by
    have hs : Function.Surjective Nat.unpair := fun p => ⟨Nat.pair p.1 p.2, Nat.unpair_pair _ _⟩
    have h : DenseRange (Prod.map P.ι Q.ι ∘ Nat.unpair) := by
      unfold DenseRange
      rw [hs.range_comp]
      exact P.dense.prodMap Q.dense
    exact h
  complete := by
    have := P.complete
    have := Q.complete
    infer_instance

/-- An almost decidable basis relative to `A` for `μ`: a family `B` of open sets, uniformly c.e.
open relative to `A`, with uniformly c.e. open exteriors `D k` disjoint from `B k`, whose
boundary sets `(B k ∪ D k)ᶜ` are covered at every level `n` by uniformly c.e. open sets of
`μ`-measure at most `2^{-n}`, and which generates the basic balls: each basic ball is the union
of an `A`-c.e. set of finite intersections of members of `B`. Blueprint node `vlm:ad-basis`. -/
structure IsAlmostDecidableBasisIn [MeasurableSpace X] (P : Presentation X) (A : Set ℕ)
    (μ : Measure X) (B : ℕ → Set X) : Prop where
  /-- The members are uniformly c.e. open relative to `A`. -/
  isCeOpenFamilyIn : IsCeOpenFamilyIn P A B
  /-- Exteriors and an effective null cover of the boundary sets. -/
  exists_exterior : ∃ D : ℕ → Set X, ∃ W : ℕ × ℕ → Set X,
    IsCeOpenFamilyIn P A D ∧ IsCeOpenFamilyIn P A W ∧
      ∀ k, Disjoint (B k) (D k) ∧
        ∀ n, (B k ∪ D k)ᶜ ⊆ W (k, n) ∧ μ (W (k, n)) ≤ (2 : ℝ≥0∞)⁻¹ ^ n
  /-- Every basic ball is an `A`-c.e. union of finite intersections of members. -/
  generates : ∃ E : (ℕ × ℚ) × List ℕ → Prop, IsREIn A E ∧
    ∀ b, basicBall P b = ⋃ L ∈ {L | E (b, L)}, ⋂ k ∈ L, B k

open Classical in
/-- The itinerary of `x` in the family `B`: bit `k` records whether `x ∈ B k`.
Blueprint node `vlm:itinerary`. -/
noncomputable def itinerary (B : ℕ → Set X) (x : X) : CantorSeq := fun k => decide (x ∈ B k)

/-- The product of two families of sets, interleaved: index `2k` carries `B k × Y` and index
`2k + 1` carries `X × C k`. Blueprint node `vlm:prod-basis`. -/
def prodBasis (B : ℕ → Set X) (C : ℕ → Set Y) : ℕ → Set (X × Y) :=
  fun n => if n % 2 = 0 then B (n / 2) ×ˢ Set.univ else Set.univ ×ˢ C (n / 2)

end Kolmogorov.PointToSet
