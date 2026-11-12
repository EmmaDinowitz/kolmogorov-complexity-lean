/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Pullback
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs

/-!
# Interleaving: oracles, the uniform measure and the swap

This module records how the interleaving `cantorJoin` interacts with oracles and measures:
the oracle of `x ⊕ y` is the oracle join of the oracles of `x` and `y`; the joined product of two
uniform measures is the uniform measure; and exchanging the two factors preserves randomness.

## Conventions

`cantorJoin x y` puts `x` on even positions, as `PointToSet.oracleJoin` puts its first argument
on even queries. The swap statement compares `joinMeasure μ ν` at `x ⊕ y` with `joinMeasure ν μ`
at `y ⊕ x`; it uses s-finiteness of both factors, which is what Mathlib's `Measure.prod_swap`
needs.

## Main declarations

* `seqOracle_cantorJoin` (blueprint node `vl:join-oracle`): `seqOracle (x ⊕ y)` is the oracle join
  of `seqOracle x` and `seqOracle y`.
* `exists_cantorJoin_eq` (blueprint node `vl:join`): every sequence is an interleaving.
* `joinMeasure_univ` (blueprint node `vl:join-measure`): the total mass of `joinMeasure μ ν` is
  `μ(univ) ν(univ)`.
* `joinMeasure_uniformMeasure` (blueprint node `vl:join-uniform`): the joined product of two
  uniform measures is the uniform measure.
* `isMartinLofRandomIn_joinMeasure_swap` (blueprint node `vl:swap`): `x ⊕ y` is random for
  `joinMeasure μ ν` relative to `A` if and only if `y ⊕ x` is random for `joinMeasure ν μ`.

Used by `AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory
open PointToSet (oracleJoin)

variable {A : Set ℕ} {μ ν : Measure CantorSeq}

/-! ### Oracles and decomposition -/

/-- The oracle of an interleaving is the oracle join of the oracles of its two halves.
Blueprint node `vl:join-oracle`. -/
theorem seqOracle_cantorJoin (x y : CantorSeq) :
    seqOracle (cantorJoin x y) = oracleJoin (seqOracle x) (seqOracle y) := by
  ext n
  by_cases h : n % 2 = 0 <;> simp [seqOracle, cantorJoin, PointToSet.oracleJoin, h]

/-- Every sequence is an interleaving: of its even-indexed and its odd-indexed subsequences.
Blueprint node `vl:join`. -/
theorem exists_cantorJoin_eq (z : CantorSeq) : ∃ x y, cantorJoin x y = z := by
  refine ⟨fun n => z (2 * n), fun n => z (2 * n + 1), funext fun n => ?_⟩
  by_cases h : n % 2 = 0
  · simp only [cantorJoin, h, ↓reduceIte]
    congr 1
    omega
  · simp only [cantorJoin, h, ↓reduceIte]
    congr 1
    omega

/-! ### The joined product measure -/

private lemma measurable_cantorJoin :
    Measurable fun p : CantorSeq × CantorSeq => cantorJoin p.1 p.2 := by
  refine Measurable.of_eval fun n => ?_
  by_cases h : n % 2 = 0
  · simp only [cantorJoin, h, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [cantorJoin, h, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_snd

/-- The total mass of the joined product is the product of the total masses.
Blueprint node `vl:join-measure`. -/
theorem joinMeasure_univ [SFinite ν] :
    joinMeasure μ ν Set.univ = μ Set.univ * ν Set.univ := by
  rw [joinMeasure, Measure.map_apply measurable_cantorJoin MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod]

/-- The pairs whose interleaving extends `τ` are those whose first coordinate extends the
even-indexed bits of `τ` and whose second coordinate extends the odd-indexed bits. -/
private lemma preimage_cantorJoin_cantorCylinder (τ : BitString) :
    (fun p : CantorSeq × CantorSeq => cantorJoin p.1 p.2) ⁻¹' cantorCylinder τ =
      cantorCylinder (List.ofFn fun i : Fin ((τ.length + 1) / 2) => τ.getD (2 * i) false) ×ˢ
        cantorCylinder (List.ofFn fun i : Fin (τ.length / 2) => τ.getD (2 * i + 1) false) := by
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Set.mem_prod, cantorCylinder, Set.mem_ofPred_eq, IsCantorPrefix,
    List.length_ofFn, List.getElem_ofFn]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hx := h (2 * i) (by omega)
      simp only [cantorJoin, show 2 * i % 2 = 0 by omega, show 2 * i / 2 = i by omega,
        ↓reduceIte] at hx
      rw [hx, List.getD_eq_getElem]
    · have hy := h (2 * i + 1) (by omega)
      simp only [cantorJoin, show (2 * i + 1) % 2 = 1 by omega,
        show (2 * i + 1) / 2 = i by omega, one_ne_zero, ↓reduceIte] at hy
      rw [hy, List.getD_eq_getElem]
  · rintro ⟨hx, hy⟩ i hi
    simp only [cantorJoin]
    by_cases h : i % 2 = 0
    · rw [ite_eq_left h, hx (i / 2) (by omega), List.getD_eq_getElem _ _ (by omega)]
      congr 1
      omega
    · rw [ite_eq_right h, hy (i / 2) (by omega), List.getD_eq_getElem _ _ (by omega)]
      congr 1
      omega

/-- The joined product of two uniform measures is the uniform measure.
Blueprint node `vl:join-uniform`. -/
theorem joinMeasure_uniformMeasure :
    joinMeasure uniformMeasure uniformMeasure = uniformMeasure := by
  have : IsProbabilityMeasure (joinMeasure uniformMeasure uniformMeasure) :=
    ⟨by rw [joinMeasure_univ, measure_univ, one_mul]⟩
  have hu : ∀ σ : BitString, uniformMeasure (cantorCylinder σ) = 2⁻¹ ^ σ.length :=
    cantorMass_uniformMeasure
  refine cantorMeasure_unique _ _ fun τ => ?_
  simp only [cantorMass]
  rw [joinMeasure, Measure.map_apply measurable_cantorJoin (measurableSet_cantorCylinder τ),
    preimage_cantorJoin_cantorCylinder, Measure.prod_prod, hu, hu, hu, List.length_ofFn,
    List.length_ofFn, ← pow_add]
  congr 1
  omega

/-! ### Exchanging the two halves -/

/-- The index map of the exchange of even and odd positions: `2m ↦ 2m + 1` and `2m + 1 ↦ 2m`. -/
private def swapIndex (n : ℕ) : ℕ := if n % 2 = 0 then n + 1 else n - 1

private lemma primrec_swapIndex : Primrec swapIndex :=
  Primrec.ite
    (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0))
    (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))

private lemma cantorJoin_comp_swapIndex (x y : CantorSeq) :
    cantorJoin x y ∘ swapIndex = cantorJoin y x := by
  funext n
  simp only [Function.comp_apply, swapIndex, cantorJoin]
  by_cases h : n % 2 = 0
  · have h1 : ¬ (n + 1) % 2 = 0 := by omega
    have h2 : (n + 1) / 2 = n / 2 := by omega
    simp only [h, h1, h2, ↓reduceIte]
  · have h1 : (n - 1) % 2 = 0 := by omega
    have h2 : (n - 1) / 2 = n / 2 := by omega
    simp only [h, h1, h2, ↓reduceIte]

/-- Pulling back along the exchange of even and odd positions turns `joinMeasure ν μ` into
`joinMeasure μ ν`. -/
private lemma joinMeasure_preimage_swap [SFinite μ] [SFinite ν] {S : Set CantorSeq}
    (hS : MeasurableSet S) :
    joinMeasure μ ν ((fun z : CantorSeq => z ∘ swapIndex) ⁻¹' S) = joinMeasure ν μ S := by
  have hs : Measurable fun z : CantorSeq => z ∘ swapIndex :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [joinMeasure, joinMeasure, Measure.map_apply measurable_cantorJoin (hs hS),
    Measure.map_apply measurable_cantorJoin hS, ← Measure.prod_swap (μ := μ) (ν := ν),
    Measure.map_apply measurable_swap (measurable_cantorJoin hS)]
  congr 1
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Prod.swap_prod_mk,
    cantorJoin_comp_swapIndex]

/-- One direction of `isMartinLofRandomIn_joinMeasure_swap`: a test for `joinMeasure ν μ` pulls
back along the exchange of even and odd positions to a test for `joinMeasure μ ν`. -/
private lemma IsMartinLofRandomIn.joinMeasure_swap [SFinite μ] [SFinite ν] {x y : CantorSeq}
    (h : IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y)) :
    IsMartinLofRandomIn A (joinMeasure ν μ) (cantorJoin y x) := by
  intro U hU hmem
  refine h (fun n => (fun z : CantorSeq => z ∘ swapIndex) ⁻¹' U n)
    ⟨hU.1.preimage_precomp primrec_swapIndex, fun n => ?_⟩ ?_
  · rw [joinMeasure_preimage_swap (hU.1.measurableSet n)]
    exact hU.2 n
  · simp only [Set.mem_iInter, Set.mem_preimage, cantorJoin_comp_swapIndex] at hmem ⊢
    exact hmem

/-- Exchanging the two factors preserves randomness: `x ⊕ y` is random for `joinMeasure μ ν`
relative to `A` exactly when `y ⊕ x` is random for `joinMeasure ν μ` relative to `A`.
Blueprint node `vl:swap`. -/
theorem isMartinLofRandomIn_joinMeasure_swap [SFinite μ] [SFinite ν] {x y : CantorSeq} :
    IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y) ↔
      IsMartinLofRandomIn A (joinMeasure ν μ) (cantorJoin y x) :=
  ⟨IsMartinLofRandomIn.joinMeasure_swap, IsMartinLofRandomIn.joinMeasure_swap⟩

end Kolmogorov
