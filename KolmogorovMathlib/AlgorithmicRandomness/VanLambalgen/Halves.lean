/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs

/-!
# The two halves of an interleaved sequence

Every sequence `w` is the interleaving `cantorJoin (cantorEvens w) (cantorOdds w)` of its
even-indexed and odd-indexed subsequences, and a finite string `ρ` splits in the same way into
`evenBits ρ` and `oddBits ρ`. This module proves that a cylinder `[ρ]` is the set of sequences
whose two halves lie in `[evenBits ρ]` and `[oddBits ρ]`, and computes the joined product measure
of a set described through the halves: for a family of sets `T z` indexed by sequences, the set
`jointSet T = {z ⊕ y | y ∈ T z}` has `joinMeasure μ ν`-measure `∫⁻ z, ν (T z) ∂μ` (Fubini).

## Conventions

`cantorEvens w k = w (2k)` and `cantorOdds w k = w (2k+1)`, matching `cantorJoin`, which puts its
first argument on the even positions. For a string `ρ` of length `ℓ`, `evenBits ρ` has length
`⌈ℓ/2⌉` and `oddBits ρ` has length `⌊ℓ/2⌋`. Measures are in `ℝ≥0∞`; the Fubini formula needs only
s-finiteness of the second factor, as Mathlib's `Measure.prod_apply`.

## Main declarations

* `cantorEvens`, `cantorOdds`, `evenBits`, `oddBits` (blueprint node `vl:halves`): the two halves
  of a sequence and of a string.
* `mem_cantorCylinder_iff_halves` (blueprint node `vl:halves`): `w ∈ [ρ]` iff the halves of `w`
  lie in the cylinders of the halves of `ρ`.
* `jointSet` (blueprint node `vl:joint-set`): the set `{z ⊕ y | y ∈ T z}` of a family `T`.
* `joinMeasure_jointSet` (blueprint node `vl:joint-fubini`): its joined product measure is
  `∫⁻ z, ν (T z) ∂μ`.

Used by `AlgorithmicRandomness/VanLambalgen/OracleUniform/`, by the directions in
`AlgorithmicRandomness/VanLambalgen/Directions/`, and by `VanLambalgen/Join.lean` and
`VanLambalgen/Countable/Split.lean` (measurability of the interleaving).
-/

namespace Kolmogorov

open MeasureTheory

/-! ### Halves of sequences -/

/-- The even half of a sequence: `cantorEvens w k = w (2k)`. Blueprint node `vl:halves`. -/
def cantorEvens (w : CantorSeq) : CantorSeq := fun k => w (2 * k)

/-- The odd half of a sequence: `cantorOdds w k = w (2k+1)`. Blueprint node `vl:halves`. -/
def cantorOdds (w : CantorSeq) : CantorSeq := fun k => w (2 * k + 1)

/-- The even half of an interleaving is its first component. Blueprint node `vl:halves`. -/
@[simp] theorem cantorEvens_cantorJoin (x y : CantorSeq) : cantorEvens (cantorJoin x y) = x := by
  funext k
  have h1 : 2 * k % 2 = 0 := by omega
  have h2 : 2 * k / 2 = k := by omega
  simp [cantorEvens, cantorJoin, h1, h2]

/-- The odd half of an interleaving is its second component. Blueprint node `vl:halves`. -/
@[simp] theorem cantorOdds_cantorJoin (x y : CantorSeq) : cantorOdds (cantorJoin x y) = y := by
  funext k
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [cantorOdds, cantorJoin, h1, h2]

/-- Every sequence is the interleaving of its two halves. -/
private theorem cantorJoin_cantorEvens_cantorOdds (w : CantorSeq) :
    cantorJoin (cantorEvens w) (cantorOdds w) = w := by
  funext n
  unfold cantorJoin cantorEvens cantorOdds
  split_ifs with h
  · congr 1
    omega
  · congr 1
    omega

/-! ### Halves of strings -/

/-- The even half of a string: its entries at the positions `0, 2, 4, …`, a string of length
`⌈|ρ|/2⌉`. Blueprint node `vl:halves`. -/
def evenBits (ρ : BitString) : BitString :=
  (List.range ((ρ.length + 1) / 2)).map fun k => ρ.getD (2 * k) false

/-- The odd half of a string: its entries at the positions `1, 3, 5, …`, a string of length
`⌊|ρ|/2⌋`. Blueprint node `vl:halves`. -/
def oddBits (ρ : BitString) : BitString :=
  (List.range (ρ.length / 2)).map fun k => ρ.getD (2 * k + 1) false

/-- Taking the even half of a string is primitive recursive. Blueprint node `vl:halves`. -/
theorem primrec_evenBits : Primrec evenBits :=
  Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp
      (Primrec.nat_add.comp Primrec.list_length (Primrec.const 1)) (Primrec.const 2)))
    ((Primrec.list_getD false).comp₂ Primrec₂.left
      (Primrec.nat_mul.comp₂ (Primrec₂.const 2) Primrec₂.right))

/-- Taking the odd half of a string is primitive recursive. Blueprint node `vl:halves`. -/
theorem primrec_oddBits : Primrec oddBits :=
  Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)))
    ((Primrec.list_getD false).comp₂ Primrec₂.left
      (Primrec.nat_add.comp₂ (Primrec.nat_mul.comp₂ (Primrec₂.const 2) Primrec₂.right)
        (Primrec₂.const 1)))

/-- A sequence extends `ρ` exactly when its even half extends the even half of `ρ` and its odd
half extends the odd half of `ρ`. Blueprint node `vl:halves`. -/
theorem mem_cantorCylinder_iff_halves (ρ : BitString) (w : CantorSeq) :
    w ∈ cantorCylinder ρ ↔
      cantorEvens w ∈ cantorCylinder (evenBits ρ) ∧ cantorOdds w ∈ cantorCylinder (oddBits ρ) := by
  simp only [cantorCylinder, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have hk' : k < (ρ.length + 1) / 2 := by simpa [evenBits] using hk
      have h2 : 2 * k < ρ.length := by omega
      simp only [evenBits, List.getElem_map, List.getElem_range, cantorEvens,
        List.getD_eq_getElem _ _ h2]
      exact h _ h2
    · have hk' : k < ρ.length / 2 := by simpa [oddBits] using hk
      have h2 : 2 * k + 1 < ρ.length := by omega
      simp only [oddBits, List.getElem_map, List.getElem_range, cantorOdds,
        List.getD_eq_getElem _ _ h2]
      exact h _ h2
  · rintro ⟨he, ho⟩ i hi
    rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
    · have hk : k < (evenBits ρ).length := by simp [evenBits]; omega
      have := he k hk
      simpa only [evenBits, List.getElem_map, List.getElem_range, cantorEvens,
        List.getD_eq_getElem _ _ hi] using this
    · have hk : k < (oddBits ρ).length := by simp [oddBits]; omega
      have := ho k hk
      simpa only [oddBits, List.getElem_map, List.getElem_range, cantorOdds,
        List.getD_eq_getElem _ _ hi] using this

/-- The even half of the prefix of length `2L` of a sequence is the prefix of length `L` of its
even half. Blueprint node `vl:halves`. -/
theorem evenBits_cantorPrefix (w : CantorSeq) (L : ℕ) :
    evenBits (cantorPrefix w (2 * L)) = cantorPrefix (cantorEvens w) L := by
  apply List.ext_getElem
  · simp [evenBits]
    omega
  · intro k h1 h2
    have hk : k < L := by simpa using h2
    have h3 : 2 * k < (cantorPrefix w (2 * L)).length := by simp; omega
    simp only [evenBits, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ h3, cantorPrefix_getElem]
    rfl

/-- The odd half of the prefix of length `2L` of a sequence is the prefix of length `L` of its
odd half. Blueprint node `vl:halves`. -/
theorem oddBits_cantorPrefix (w : CantorSeq) (L : ℕ) :
    oddBits (cantorPrefix w (2 * L)) = cantorPrefix (cantorOdds w) L := by
  apply List.ext_getElem
  · simp [oddBits]
  · intro k h1 h2
    have hk : k < L := by simpa using h2
    have h3 : 2 * k + 1 < (cantorPrefix w (2 * L)).length := by simp; omega
    simp only [oddBits, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ h3, cantorPrefix_getElem]
    rfl

/-! ### Sets of pairs and their joined product measure -/

/-- The set of interleavings `z ⊕ y` with `y ∈ T z`, written through the halves: a sequence `w`
belongs to it when `cantorOdds w ∈ T (cantorEvens w)`. For `T` constantly empty it is empty.
Blueprint node `vl:joint-set`. -/
def jointSet (T : CantorSeq → Set CantorSeq) : Set CantorSeq :=
  {w | cantorOdds w ∈ T (cantorEvens w)}

/-- An interleaving `z ⊕ y` lies in `jointSet T` exactly when `y ∈ T z`.
Blueprint node `vl:joint-set`. -/
@[simp] theorem cantorJoin_mem_jointSet {T : CantorSeq → Set CantorSeq} {z y : CantorSeq} :
    cantorJoin z y ∈ jointSet T ↔ y ∈ T z := by
  simp [jointSet]

/-- A set of sequences is the joint set of its sections `{y | z ⊕ y ∈ W}`.
Blueprint node `vl:joint-set`. -/
theorem jointSet_sections (W : Set CantorSeq) :
    jointSet (fun z => {y | cantorJoin z y ∈ W}) = W := by
  ext w
  simp [jointSet, cantorJoin_cantorEvens_cantorOdds]

/-- Interleaving is measurable as a map from pairs of sequences. Blueprint node `vl:joint-set`. -/
theorem measurable_cantorJoin :
    Measurable (fun p : CantorSeq × CantorSeq => cantorJoin p.1 p.2) := by
  refine Measurable.of_eval fun n => ?_
  show Measurable fun p : CantorSeq × CantorSeq => cantorJoin p.1 p.2 n
  by_cases h : n % 2 = 0
  · have he : (fun p : CantorSeq × CantorSeq => cantorJoin p.1 p.2 n) = fun p => p.1 (n / 2) := by
      funext p
      simp [cantorJoin, h]
    rw [he]
    exact (measurable_pi_apply _).comp measurable_fst
  · have he : (fun p : CantorSeq × CantorSeq => cantorJoin p.1 p.2 n) = fun p => p.2 (n / 2) := by
      funext p
      simp [cantorJoin, h]
    rw [he]
    exact (measurable_pi_apply _).comp measurable_snd

/-- For a measurable joint set, the joined product measure is the
`μ`-integral of the `ν`-measures of the members of the family. Only `ν` needs to be s-finite.
Blueprint node `vl:joint-fubini`. -/
theorem joinMeasure_jointSet {μ ν : Measure CantorSeq} [SFinite ν]
    {T : CantorSeq → Set CantorSeq} (hT : MeasurableSet (jointSet T)) :
    joinMeasure μ ν (jointSet T) = ∫⁻ z, ν (T z) ∂μ := by
  rw [joinMeasure, Measure.map_apply measurable_cantorJoin hT,
    Measure.prod_apply (measurable_cantorJoin hT)]
  refine lintegral_congr fun z => ?_
  congr 1
  ext y
  simp

end Kolmogorov
