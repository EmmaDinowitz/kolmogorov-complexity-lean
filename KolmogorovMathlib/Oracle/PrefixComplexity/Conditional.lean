/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Oracle.PrefixComplexity.TwoStage
import KolmogorovMathlib.Oracle.PrefixComplexity.NatBounds
import KolmogorovMathlib.AlgorithmicProbability.PairProjection

/-!
# Elementary conditional inequalities for `K^A`

Consequences of the two-stage machine and the recoding lemmas of
`KolmogorovMathlib.Oracle.PrefixComplexity.TwoStage`, in the natural-number form used by the
split-precision theory.  Throughout, `K(x | y)` is `oraclePrefixComplexityNat A x y` and `K(x)`
is `oracleComplexity A x`; every bound holds up to a constant depending only on the oracle `A`.

* Conditions: dropping the condition (`oraclePrefixComplexityNat_le_oracleComplexity`),
  dropping a component of a paired condition (`…_cond_pair_left_le`, `…_cond_pair_right_le`),
  swapping it (`…_cond_swap_le`), and the price of adding one
  (`oraclePrefixComplexityNat_le_cond_pair_add`:
  `K(x | y) ≤ K(x | ⟨y, z⟩) + K(z | y) + O(1)`).
* The complexity-value context `prefixComplexityContext y k = ⟨y, natCode k⟩`: it may be
  dropped (`oraclePrefixComplexityNat_context_le`), it costs `K(natCode k)` to add
  (`oraclePrefixComplexityNat_le_context_add`), and `⟨y, natCode (K(y | z))⟩` is as simple as
  `y` itself (`oraclePrefixComplexityNat_context_self_le`).
* Pairs: `K(⟨y, x⟩ | z) ≤ K(y | z) + K(x | z) + O(1)`, projections and the swap.
* Logarithmic bounds: `K(natBits n)` and `K(natCode n)` are at most
  `3 * (Nat.bits n).length + O(1)` (`oracleNatComplexity_le_bits`, `oracleComplexity_natCode_le`).

Blueprint node `split:conditional-calculus`.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

variable (A : Set ℕ)

/-! ### Conditions -/

/-- Dropping the condition: `K(x | y) ≤ K(x) + O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_le_oracleComplexity :
    ∃ c : ℕ, ∀ x y : BitString,
      oraclePrefixComplexityNat A x y ≤ oracleComplexity A x + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_cond_le_of_computableIn A (fun _ => [])
    (ComputableIn.const [])
  exact ⟨c, fun x y => hc x y⟩

/-- Dropping the right component of a paired condition. Blueprint node
`split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_cond_pair_left_le :
    ∃ c : ℕ, ∀ x y z : BitString,
      oraclePrefixComplexityNat A x (pairCode y z) ≤ oraclePrefixComplexityNat A x y + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_cond_le_of_computableIn A decodeFirst
    decodeFirst_computable.computableIn
  refine ⟨c, fun x y z => ?_⟩
  have := hc x (pairCode y z)
  rwa [decodeFirst_pairCode] at this

/-- Dropping the left component of a paired condition. Blueprint node
`split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_cond_pair_right_le :
    ∃ c : ℕ, ∀ x y z : BitString,
      oraclePrefixComplexityNat A x (pairCode y z) ≤ oraclePrefixComplexityNat A x z + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_cond_le_of_computableIn A decodeSecond
    decodeSecond_computable.computableIn
  refine ⟨c, fun x y z => ?_⟩
  have := hc x (pairCode y z)
  rwa [decodeSecond_pairCode] at this

/-- Swapping the components of a paired condition. Blueprint node
`split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_cond_swap_le :
    ∃ c : ℕ, ∀ x y z : BitString,
      oraclePrefixComplexityNat A x (pairCode y z) ≤
        oraclePrefixComplexityNat A x (pairCode z y) + c := by
  have hf : Computable (fun w : BitString => pairCode (decodeSecond w) (decodeFirst w)) :=
    (pairCode_computable.comp (decodeSecond_computable.pair decodeFirst_computable)).of_eq
      fun _ => rfl
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_cond_le_of_computableIn A _ hf.computableIn
  refine ⟨c, fun x y z => ?_⟩
  have := hc x (pairCode y z)
  beta_reduce at this
  rw [decodeFirst_pairCode, decodeSecond_pairCode] at this
  exact this

/-- The price of an additional condition: `K(x | y) ≤ K(x | ⟨y, z⟩) + K(z | y) + O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_le_cond_pair_add :
    ∃ c : ℕ, ∀ x y z : BitString,
      oraclePrefixComplexityNat A x y ≤
        oraclePrefixComplexityNat A x (pairCode y z) + oraclePrefixComplexityNat A z y + c := by
  obtain ⟨c₁, hc₁⟩ := oraclePrefixComplexityNat_triangle_pair A
  obtain ⟨c₂, hc₂⟩ := oraclePrefixComplexityNat_cond_swap_le A
  refine ⟨c₁ + c₂, fun x y z => ?_⟩
  have h1 := hc₁ x z y
  have h2 := hc₂ x z y
  omega

/-! ### The complexity-value context -/

/-- The complexity-value context is a pair code. -/
theorem prefixComplexityContext_eq (y : BitString) (k : ℕ) :
    prefixComplexityContext y k = pairCode y (natCode k) := rfl

/-- Dropping the complexity value from the context: `K(x | y, k) ≤ K(x | y) + O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_context_le :
    ∃ c : ℕ, ∀ (x y : BitString) (k : ℕ),
      oraclePrefixComplexityNat A x (prefixComplexityContext y k) ≤
        oraclePrefixComplexityNat A x y + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_cond_pair_left_le A
  exact ⟨c, fun x y k => hc x y (natCode k)⟩

/-- Adding a complexity value to the context costs its own complexity:
`K(x | y) ≤ K(x | y, k) + K(natCode k) + O(1)`. Blueprint node `split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_le_context_add :
    ∃ c : ℕ, ∀ (x y : BitString) (k : ℕ),
      oraclePrefixComplexityNat A x y ≤
        oraclePrefixComplexityNat A x (prefixComplexityContext y k) +
          oracleComplexity A (natCode k) + c := by
  obtain ⟨c₁, hc₁⟩ := oraclePrefixComplexityNat_le_cond_pair_add A
  obtain ⟨c₂, hc₂⟩ := oraclePrefixComplexityNat_le_oracleComplexity A
  refine ⟨c₁ + c₂, fun x y k => ?_⟩
  have h1 := hc₁ x y (natCode k)
  have h2 := hc₂ (natCode k) y
  rw [prefixComplexityContext_eq]
  omega

/-- A string together with its own conditional complexity is no more complex than the
string: `K(⟨y, natCode (K(y | z))⟩ | z) ≤ K(y | z) + O(1)`. The machine outputs the pair of
the output of a program and the program's length. Blueprint node `split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_context_self_le :
    ∃ c : ℕ, ∀ y z : BitString,
      oraclePrefixComplexityNat A (prefixComplexityContext y (oraclePrefixComplexityNat A y z)) z
        ≤ oraclePrefixComplexityNat A y z + c := by
  obtain ⟨hUd, hUp, hopt⟩ := exists_optimalOraclePrefix_spec A
  set U := optimalOraclePrefix A with hUdef
  let D : Map := fun pr => (U pr).map fun y => prefixComplexityContext y pr.1.length
  have hD : IsDecompressorIn (charOracle A) D := by
    rw [isDecompressorIn_iff_partrecIn] at hUd ⊢
    refine hUd.map ?_
    have h1 : ComputableIn {charOracle A}
        fun q : (BitString × BitString) × BitString => (q.2, q.1.1.length) :=
      ComputableIn.pair ComputableIn.snd
        (Primrec.list_length.to_comp.computableIn.comp (ComputableIn.fst.comp ComputableIn.fst))
    exact ComputableIn₂.mk
      ((prefixComplexityContext_computable.computableIn.comp h1).of_eq fun _ => rfl)
  have hDp : IsPrefixMachine D := by
    intro z p hp q hq hpre
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hp
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hq
    obtain ⟨y, hy, -⟩ := (Part.mem_map_iff _).mp ha
    obtain ⟨y', hy', -⟩ := (Part.mem_map_iff _).mp hb
    exact hUp.eq_of_prefix hy hy' hpre
  obtain ⟨c, hc⟩ := hopt D hD hDp
  refine ⟨c, fun y z => ?_⟩
  obtain ⟨p, hp, hl⟩ := exists_program_oraclePrefix A y z
  have hprod : produces D p z (prefixComplexityContext y (oraclePrefixComplexityNat A y z)) := by
    refine (Part.mem_map_iff _).mpr ⟨y, hp, ?_⟩
    simp only [hl]
  have hbound : KP U (prefixComplexityContext y (oraclePrefixComplexityNat A y z)) z ≤
      ((p.length + c : ℕ) : ENat) := by
    calc KP U (prefixComplexityContext y (oraclePrefixComplexityNat A y z)) z
        ≤ KP D (prefixComplexityContext y (oraclePrefixComplexityNat A y z)) z + (c : ENat) :=
          hc _ z
      _ ≤ (p.length : ENat) + (c : ENat) := by
          gcongr; exact KP_le_programLength_of_produces hprod
      _ = ((p.length + c : ℕ) : ENat) := by norm_cast
  have := oraclePrefixComplexityNat_le_of_KP_le hbound
  omega

/-! ### Pairs -/

/-- Projection to the first component: `K(y | z) ≤ K(⟨y, x⟩ | z) + O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_fst_le_pair :
    ∃ c : ℕ, ∀ y x z : BitString,
      oraclePrefixComplexityNat A y z ≤ oraclePrefixComplexityNat A (pairCode y x) z + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_map_le_of_computableIn A decodeFirst
    decodeFirst_computable.computableIn
  refine ⟨c, fun y x z => ?_⟩
  have := hc (pairCode y x) z
  rwa [decodeFirst_pairCode] at this

/-- Projection to the second component: `K(x | z) ≤ K(⟨y, x⟩ | z) + O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_snd_le_pair :
    ∃ c : ℕ, ∀ y x z : BitString,
      oraclePrefixComplexityNat A x z ≤ oraclePrefixComplexityNat A (pairCode y x) z + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_map_le_of_computableIn A decodeSecond
    decodeSecond_computable.computableIn
  refine ⟨c, fun y x z => ?_⟩
  have := hc (pairCode y x) z
  rwa [decodeSecond_pairCode] at this

/-- Swapping a pair: `K(⟨x, y⟩ | z) ≤ K(⟨y, x⟩ | z) + O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_pair_swap_le :
    ∃ c : ℕ, ∀ y x z : BitString,
      oraclePrefixComplexityNat A (pairCode x y) z ≤
        oraclePrefixComplexityNat A (pairCode y x) z + c := by
  have hf : Computable (fun w : BitString => pairCode (decodeSecond w) (decodeFirst w)) :=
    (pairCode_computable.comp (decodeSecond_computable.pair decodeFirst_computable)).of_eq
      fun _ => rfl
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_map_le_of_computableIn A _ hf.computableIn
  refine ⟨c, fun y x z => ?_⟩
  have := hc (pairCode y x) z
  beta_reduce at this
  rw [decodeFirst_pairCode, decodeSecond_pairCode] at this
  exact this

/-- Unconditional concatenation: `K(⟨y, x⟩) ≤ K(y) + K(x) + O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oracleComplexity_pair_le_add :
    ∃ c : ℕ, ∀ y x : BitString,
      oracleComplexity A (pairCode y x) ≤ oracleComplexity A y + oracleComplexity A x + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_pair_le_add A
  exact ⟨c, fun y x => hc y x []⟩

/-- Unconditional first projection: `K(y) ≤ K(⟨y, x⟩) + O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oracleComplexity_fst_le_pair :
    ∃ c : ℕ, ∀ y x : BitString, oracleComplexity A y ≤ oracleComplexity A (pairCode y x) + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_fst_le_pair A
  exact ⟨c, fun y x => hc y x []⟩

/-- Unconditional second projection: `K(x) ≤ K(⟨y, x⟩) + O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oracleComplexity_snd_le_pair :
    ∃ c : ℕ, ∀ y x : BitString, oracleComplexity A x ≤ oracleComplexity A (pairCode y x) + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_snd_le_pair A
  exact ⟨c, fun y x => hc y x []⟩

/-- Unconditional swap: `K(⟨x, y⟩) ≤ K(⟨y, x⟩) + O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oracleComplexity_pair_swap_le :
    ∃ c : ℕ, ∀ y x : BitString,
      oracleComplexity A (pairCode x y) ≤ oracleComplexity A (pairCode y x) + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_pair_swap_le A
  exact ⟨c, fun y x => hc y x []⟩

/-! ### Self-information -/

/-- An `A`-computable function of the condition is free: `K(f y | y) ≤ O(1)`.
Blueprint node `split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_map_self_le (f : BitString → BitString)
    (hf : ComputableIn {charOracle A} f) :
    ∃ c : ℕ, ∀ y : BitString, oraclePrefixComplexityNat A (f y) y ≤ c := by
  obtain ⟨c₁, hc₁⟩ := oraclePrefixComplexityNat_map_cond_le A (fun y _ => f y)
    (hf.comp ComputableIn.fst)
  obtain ⟨c₂, hc₂⟩ := oraclePrefixComplexityNat_le_oracleComplexity A
  refine ⟨oracleComplexity A [] + c₂ + c₁, fun y => ?_⟩
  have h1 := hc₁ [] y
  have h2 := hc₂ [] y
  beta_reduce at h1
  omega

/-- A string is free given itself: `K(y | y) ≤ O(1)`. Blueprint node
`split:conditional-calculus`. -/
theorem oraclePrefixComplexityNat_self_le :
    ∃ c : ℕ, ∀ y : BitString, oraclePrefixComplexityNat A y y ≤ c :=
  oraclePrefixComplexityNat_map_self_le A id ComputableIn.id

/-! ### Logarithmic bounds on the complexity of numbers -/

/-- `K(natBits n) ≤ 3 * (Nat.bits n).length + O(1)`, the natural-number form of
`oracleNatComplexity_le_log_add_loglog`. Blueprint node `split:conditional-calculus`. -/
theorem oracleNatComplexity_le_bits :
    ∃ c : ℕ, ∀ n : ℕ, oracleNatComplexity A n ≤ 3 * (Nat.bits n).length + c := by
  obtain ⟨c, hc⟩ := oracleNatComplexity_le_log_add_loglog A
  refine ⟨⌈c⌉₊, fun n => ?_⟩
  set L := (Nat.bits n).length with hL
  have hpow : ((n : ℝ) + 1) ≤ (2 : ℝ) ^ L := by
    have h : n + 1 ≤ 2 ^ L := by
      rw [hL, Nat.size_eq_bits_len]
      exact Nat.lt_size_self n
    exact_mod_cast h
  have hLpow : ((L : ℝ) + 1) ≤ (2 : ℝ) ^ L := by
    have h : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self (n := L)
    exact_mod_cast h
  have hlogpow : Real.logb 2 ((2 : ℝ) ^ L) = L := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    ring
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hlog1 : Real.logb 2 ((n : ℝ) + 1) ≤ L := by
    rw [← hlogpow]
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) hpow
  have hlog1_nonneg : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) hn1
  have hlog2 : Real.logb 2 (Real.logb 2 ((n : ℝ) + 1) + 1) ≤ L := by
    rw [← hlogpow]
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hfinal : (oracleNatComplexity A n : ℝ) ≤ 3 * L + (⌈c⌉₊ : ℝ) := by
    have h := hc n
    have hceil := Nat.le_ceil c
    linarith
  exact_mod_cast hfinal

/-- `K(natCode n) ≤ 3 * (Nat.bits n).length + O(1)`: the unary code of a number is computable
from its binary code. Blueprint node `split:conditional-calculus`. -/
theorem oracleComplexity_natCode_le :
    ∃ c : ℕ, ∀ n : ℕ, oracleComplexity A (natCode n) ≤ 3 * (Nat.bits n).length + c := by
  have hf : Computable (fun w : BitString => natCode (decodeBits w)) :=
    natCode_computable.comp decodeBits_computable
  obtain ⟨c₁, hc₁⟩ := oraclePrefixComplexityNat_map_le_of_computableIn A _ hf.computableIn
  obtain ⟨c₂, hc₂⟩ := oracleNatComplexity_le_bits A
  refine ⟨c₂ + c₁, fun n => ?_⟩
  have h1 := hc₁ (natBits n) []
  beta_reduce at h1
  rw [natBits, decodeBits_natBits] at h1
  have h2 := hc₂ n
  unfold oracleNatComplexity at h2
  have e1 : oraclePrefixComplexityNat A (natCode n) [] = oracleComplexity A (natCode n) := rfl
  have e2 : oraclePrefixComplexityNat A (Nat.bits n) [] = oracleComplexity A (natBits n) := rfl
  omega

end Kolmogorov.PointToSet
