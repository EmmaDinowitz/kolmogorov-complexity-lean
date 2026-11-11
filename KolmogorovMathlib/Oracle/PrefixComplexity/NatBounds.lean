/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Oracle.KraftChaitin

/-!
# Self-delimiting codes of naturals

The relative prefix complexity of a natural `n` is at most its binary length plus twice the
binary length of that length, up to a constant: the request `n ↦ (natBits n, |n| + 2 ||n|| + 3)`
has total mass at most one, so the oracle Kraft–Chaitin theorem produces a prefix-free
description of every `n` of that length. In logarithmic form,
`K^A(n) ≤ log₂(n + 1) + 2 log₂(log₂(n + 1) + 1) + c` (`oracleNatComplexity_le_log_add_loglog`).
Blueprint node `eff:nat-bounds`.
-/

namespace Kolmogorov.PointToSet

open scoped ENNReal Computability

/-- Grouping the naturals by binary length: at most `2 ^ ℓ` naturals have binary length `ℓ`,
so `∑ₙ 2^{-|n|} a(|n|) ≤ ∑_ℓ a(ℓ)`. -/
private lemma tsum_inv_two_pow_size_mul_le (a : ℕ → ℝ≥0∞) :
    ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (Nat.size n) * a (Nat.size n) ≤ ∑' ℓ : ℕ, a ℓ := by
  let F : ℕ × ℕ → ℝ≥0∞ := fun p ↦ if p.2 < 2 ^ p.1 then (2 : ℝ≥0∞)⁻¹ ^ p.1 * a p.1 else 0
  have hinj : Function.Injective fun n : ℕ ↦ (Nat.size n, n) :=
    fun n m h ↦ (Prod.ext_iff.mp h).2
  have h1 : ∀ n, (2 : ℝ≥0∞)⁻¹ ^ (Nat.size n) * a (Nat.size n) = F (Nat.size n, n) := by
    intro n
    simp only [F, Nat.lt_size_self n, ↓reduceIte]
  calc ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (Nat.size n) * a (Nat.size n)
      = ∑' n : ℕ, F (Nat.size n, n) := tsum_congr h1
    _ ≤ ∑' p : ℕ × ℕ, F p := ENNReal.tsum_comp_le_tsum_of_injective hinj F
    _ = ∑' ℓ : ℕ, ∑' n : ℕ, F (ℓ, n) := ENNReal.tsum_prod (f := fun ℓ n ↦ F (ℓ, n))
    _ = ∑' ℓ : ℕ, a ℓ := by
        refine tsum_congr fun ℓ ↦ ?_
        have hsum : ∑' n : ℕ, F (ℓ, n) =
            ∑ n ∈ Finset.range (2 ^ ℓ), (2 : ℝ≥0∞)⁻¹ ^ ℓ * a ℓ := by
          rw [tsum_eq_sum (s := Finset.range (2 ^ ℓ))]
          · refine Finset.sum_congr rfl fun n hn ↦ ?_
            simp only [F, Finset.mem_range.mp hn, ↓reduceIte]
          · intro n hn
            simp only [F, Finset.mem_range.not.mp hn, ↓reduceIte]
        rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow,
          Nat.cast_ofNat, ← mul_assoc, ← ENNReal.inv_pow,
          ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
            (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
          one_mul]

/-- Relative prefix complexity of a natural is at most its binary length plus twice the
binary length of that length, up to a constant: the self-delimiting code
`n ↦ (natBits n, |natBits n| + 2 |natBits |natBits n|| + 3)` has request mass at most one, so
Kraft–Chaitin applies. In logarithmic form:
`K^A(n) ≤ log₂(n + 1) + 2 log₂(log₂(n + 1) + 1) + c`. -/
theorem oracleNatComplexity_le_log_add_loglog (A : Set ℕ) :
    ∃ c : ℝ, ∀ n : ℕ, (oracleNatComplexity A n : ℝ) ≤
      Real.logb 2 (n + 1) + 2 * Real.logb 2 (Real.logb 2 (n + 1) + 1) + c := by
  let len : ℕ → ℕ := fun n ↦
    (Nat.bits n).length + 2 * (Nat.bits (Nat.bits n).length).length + 3
  let req : ℕ → Option (BitString × ℕ) := fun n ↦ some (natBits n, len n)
  have hb : Primrec fun n : ℕ ↦ (Nat.bits n).length := Primrec.list_length.comp primrec_natBits
  have hlen : Primrec len :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hb
      (Primrec.nat_mul.comp (Primrec.const 2) (hb.comp hb))) (Primrec.const 3)
  have hreq : ComputableIn {charOracle A} req :=
    (Primrec.option_some.comp (primrec_natBits.pair hlen)).to_comp.computableIn
  have hmass : oracleRequestMass req ≤ 1 := by
    have h1 : oracleRequestMass req = ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (len n) := by
      simp only [oracleRequestMass, req, Option.elim_some]
    have hsz : ∀ n, len n = Nat.size n + (2 * Nat.size (Nat.size n) + 3) := by
      intro n
      simp only [len, Nat.size_eq_bits_len]
      ring
    rw [h1]
    calc ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (len n)
        = ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (Nat.size n) *
            (2 : ℝ≥0∞)⁻¹ ^ (2 * Nat.size (Nat.size n) + 3) := by
          refine tsum_congr fun n ↦ ?_
          rw [hsz n, pow_add]
      _ ≤ ∑' ℓ : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (2 * Nat.size ℓ + 3) :=
          tsum_inv_two_pow_size_mul_le (fun ℓ ↦ (2 : ℝ≥0∞)⁻¹ ^ (2 * Nat.size ℓ + 3))
      _ = (2 : ℝ≥0∞)⁻¹ ^ 3 *
            ∑' ℓ : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (Nat.size ℓ) * (2 : ℝ≥0∞)⁻¹ ^ (Nat.size ℓ) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun ℓ ↦ ?_
          ring
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 3 * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ j :=
          mul_le_mul_right (tsum_inv_two_pow_size_mul_le (fun j ↦ (2 : ℝ≥0∞)⁻¹ ^ j)) _
      _ = (2 : ℝ≥0∞)⁻¹ ^ 2 * (2⁻¹ * 2) := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
          ring
      _ = (2 : ℝ≥0∞)⁻¹ ^ 2 := by
          rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
      _ ≤ 1 := pow_le_one₀ zero_le (ENNReal.inv_le_one.mpr one_le_two)
  obtain ⟨c, hc⟩ := oracle_kraftChaitin_bound A req hreq hmass
  refine ⟨c + 8, fun n ↦ ?_⟩
  have hK : oracleNatComplexity A n ≤ len n + c := hc n (natBits n) (len n) rfl
  have hKr : (oracleNatComplexity A n : ℝ) ≤ len n + c := by exact_mod_cast hK
  have hlenr : (len n : ℝ) =
      (Nat.bits n).length + 2 * (Nat.bits (Nat.bits n).length).length + 3 := by
    simp only [len]
    push_cast
    ring
  have hL0 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg one_lt_two (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have h1 : ((Nat.bits n).length : ℝ) ≤ Real.logb 2 (n + 1) + 1 := length_bits_le_logb_add_one n
  have h2 : ((Nat.bits (Nat.bits n).length).length : ℝ) ≤
      Real.logb 2 ((Nat.bits n).length + 1) + 1 := length_bits_le_logb_add_one _
  have h3 : Real.logb 2 (((Nat.bits n).length : ℝ) + 1) ≤
      Real.logb 2 (Real.logb 2 (n + 1) + 1) + 1 := by
    have hle : ((Nat.bits n).length : ℝ) + 1 ≤ 2 * (Real.logb 2 (n + 1) + 1) := by linarith
    calc Real.logb 2 (((Nat.bits n).length : ℝ) + 1)
        ≤ Real.logb 2 (2 * (Real.logb 2 (n + 1) + 1)) :=
          Real.logb_le_logb_of_le one_lt_two (by positivity) hle
      _ = Real.logb 2 (Real.logb 2 (n + 1) + 1) + 1 := by
          rw [Real.logb_mul two_ne_zero (by linarith), Real.logb_self_eq_one one_lt_two, add_comm]
  linarith

end Kolmogorov.PointToSet
