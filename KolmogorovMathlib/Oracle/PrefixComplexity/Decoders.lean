/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic
import KolmogorovMathlib.AlgorithmicStatistics.Selector

/-!
# Charging a decoder on natural-number inputs

A program partial recursive in the oracle that reads three naturals and a pair of naturals
through the codes `natBits` and `pairCode` turns shortest descriptions of its inputs into a
description of its output: `K^A(q) ≤ K^A(i) + K^A(i') + K^A(Tp, Tm) + c` whenever
`q ∈ F (i, i', Tp, Tm)`, with `c` depending only on `F` (`oracleNatComplexity_le_of_decoder`,
from the library's `oracle_tuple_bounds_composition`). The pair term is bounded by
`2 log₂(Tp + 1) + 2 log₂(Tm + 1) + c` (`oraclePairComplexity_le_log`) and is therefore
sublinear in `Tp + Tm` (`oraclePairComplexity_sublinear`). Blueprint node
`eff:decoder-charging`.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

variable (A : Set ℕ)

/-- The complexity of a pair of naturals is at most `2 log₂(Tp+1) + 2 log₂(Tm+1) + c`
(two applications of the library's `oracle_tuple_bounds_overhead` and the projection bound).
Blueprint node `geo:orbit-to-location` (time code). -/
theorem oraclePairComplexity_le_log : ∃ c : ℝ, ∀ Tp Tm : ℕ,
    (oraclePairComplexity A Tp Tm : ℝ) ≤
      2 * Real.logb 2 ((Tp : ℝ) + 1) + 2 * Real.logb 2 ((Tm : ℝ) + 1) + c := by
  obtain ⟨c₁, hc₁⟩ := oracle_tuple_bounds_overhead A
  have hF : PartrecIn {charOracle A}
      ((fun xs : List BitString ↦ decodeSecond xs.headI) : List BitString →. BitString) :=
    (decodeSecond_computable.comp Primrec.list_headI.to_comp).computableIn.partrecIn
  obtain ⟨c₂, hc₂⟩ := oracle_tuple_bounds_composition A 1 _ hF
  have hnat : ∀ n, oracleNatComplexity A n ≤ oraclePairComplexity A 0 n + c₂ := by
    intro n
    have hmem : natBits n ∈ ((fun xs : List BitString ↦ decodeSecond xs.headI) :
        List BitString →. BitString) [pairCode (natBits 0) (natBits n)] := by
      change natBits n ∈ Part.some (decodeSecond ([pairCode (natBits 0) (natBits n)]).headI)
      rw [Part.mem_some_iff]
      simp [decodeSecond_pairCode]
    have := hc₂ [pairCode (natBits 0) (natBits n)] (natBits n) rfl hmem
    simpa [oracleNatComplexity, oraclePairComplexity] using this
  refine ⟨oracleNatComplexity A 0 + 2 * c₁ + c₂, fun Tp Tm ↦ ?_⟩
  have h1 := hc₁ Tp Tm
  have h2 := hc₁ 0 Tp
  have h3 : (oracleNatComplexity A Tp : ℝ) ≤ oraclePairComplexity A 0 Tp + c₂ := by
    exact_mod_cast hnat Tp
  linarith

/-- The time code is sublinear: for every `η > 0` it is at most `η (Tp + Tm)` plus a constant.
Blueprint nodes `geo:orbit-to-location`, `geo:precision-chain`. -/
theorem oraclePairComplexity_sublinear {η : ℝ} (hη : 0 < η) : ∃ c : ℝ, ∀ Tp Tm : ℕ,
    (oraclePairComplexity A Tp Tm : ℝ) ≤ η * ((Tp : ℝ) + Tm) + c := by
  obtain ⟨c, hc⟩ := oraclePairComplexity_le_log A
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set s : ℝ := η * Real.log 2 / 2 with hs
  have hs0 : 0 < s := by positivity
  have key : ∀ n : ℕ, 2 * Real.logb 2 ((n : ℝ) + 1) ≤
      η * n + 2 * (s - 1 - Real.log s) / Real.log 2 := by
    intro n
    have hn : (0 : ℝ) < n + 1 := by positivity
    have h1 : Real.log (s * (n + 1)) ≤ s * (n + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_mul hs0.ne' hn.ne'] at h1
    have h2 : 2 * ((s * (n + 1) - 1 - Real.log s) / Real.log 2) =
        η * n + 2 * (s - 1 - Real.log s) / Real.log 2 := by
      rw [hs]
      field_simp
      ring
    calc 2 * Real.logb 2 ((n : ℝ) + 1) = 2 * (Real.log ((n : ℝ) + 1) / Real.log 2) := by
          rw [Real.logb]
      _ ≤ 2 * ((s * (n + 1) - 1 - Real.log s) / Real.log 2) := by gcongr; linarith
      _ = _ := h2
  refine ⟨2 * (2 * (s - 1 - Real.log s) / Real.log 2) + c, fun Tp Tm ↦ ?_⟩
  have := hc Tp Tm
  have := key Tp
  have := key Tm
  linarith

/-- Composition of three shortest programs with a fixed `A`-partial recursive decoder on
natural-number inputs: if `F (i, i', (Tp, Tm))` halts with value `q` then
`K^A(q) ≤ K^A(i) + K^A(i') + K^A(Tp, Tm) + c`, `c` depending only on `F`
(library `oracle_tuple_bounds_composition` with `k = 3`, through the natural and pair codes).
Blueprint node `geo:orbit-to-location`. -/
theorem oracleNatComplexity_le_of_decoder (F : ℕ × ℕ × ℕ × ℕ →. ℕ)
    (hF : PartrecIn {charOracle A} F) :
    ∃ c : ℕ, ∀ i i' Tp Tm q, q ∈ F (i, i', Tp, Tm) →
      oracleNatComplexity A q ≤
        oracleNatComplexity A i + oracleNatComplexity A i' + oraclePairComplexity A Tp Tm + c := by
  let g : List BitString → ℕ × ℕ × ℕ × ℕ := fun xs ↦
    (bitsToNat (xs.getD 0 []), bitsToNat (xs.getD 1 []),
      bitsToNat (decodeFirst (xs.getD 2 [])), bitsToNat (decodeSecond (xs.getD 2 [])))
  have hget : ∀ k : ℕ, Computable fun xs : List BitString ↦ xs.getD k [] := fun k ↦
    ((Primrec.list_getD ([] : BitString)).comp Primrec.id (Primrec.const k)).to_comp
  have hg : Computable g :=
    (bitsToNat_computable.comp (hget 0)).pair
      ((bitsToNat_computable.comp (hget 1)).pair
        ((bitsToNat_computable.comp (decodeFirst_computable.comp (hget 2))).pair
          (bitsToNat_computable.comp (decodeSecond_computable.comp (hget 2)))))
  let F' : List BitString →. BitString := fun xs ↦ (F (g xs)).map natBits
  have hF' : PartrecIn {charOracle A} F' :=
    (hF.comp hg.computableIn).map (natBits_computable.comp Computable.snd).computableIn
  obtain ⟨c, hc⟩ := oracle_tuple_bounds_composition A 3 F' hF'
  refine ⟨c, fun i i' Tp Tm q hq ↦ ?_⟩
  have hgx : g [natBits i, natBits i', pairCode (natBits Tp) (natBits Tm)] = (i, i', Tp, Tm) := by
    simp [g, natBits, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  have hmem : natBits q ∈ F' [natBits i, natBits i', pairCode (natBits Tp) (natBits Tm)] := by
    change natBits q ∈ (F (g _)).map natBits
    rw [hgx, Part.mem_map_iff]
    exact ⟨q, hq, rfl⟩
  have := hc _ _ rfl hmem
  simpa [oracleNatComplexity, oraclePairComplexity, add_assoc] using this

end Kolmogorov.PointToSet
