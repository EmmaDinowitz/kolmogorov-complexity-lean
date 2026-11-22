/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupLower

/-!
# The symbolic lower bound (Hoyrup's theorem)

Input (I3), `liminf` half, of the note *Orbit complexity of Martin-Löf random points equals
entropy*: if `ν` is an `A`-computable, shift-invariant, ergodic measure on `ℕ → α` and `ω` is
`ν`-random relative to `A`, then `liminf_n K^A(ω↾n) / n ≥ h_ν(σ)`.

* `shiftEntropy_le_liminf_wordComplexity_bool`: the binary case. This is Hoyrup's theorem
  (M. Hoyrup, *The dimension of ergodic random sequences*, STACS 2012), relativized to `A`; the
  note states it for `{0,1}^ℕ` and says the proof relativizes verbatim. It is proved, relativized,
  in `HoyrupLower` (`shiftEntropy_le_liminf_wordComplexity_bool_of_hoyrup`).
* `shiftEntropy_le_liminf_wordComplexity`: a finite alphabet `Fin p`, from the binary case by the
  reduction of the note ("Binary suffices in (I3)"): code each symbol by a block of `b` bits,
  `C : (ℕ → Fin p) → (ℕ → Bool)`, `ν' = C_* ν` (`σ^b`-invariant),
  `ν'' = (1/b) ∑_{j<b} σ^j_* ν'` (`σ`-invariant and ergodic, `A`-computable, `ν' ≤ b ν''`, so
  `C(ω)` is `ν''`-random), `h_{ν''}(σ) ≥ h_ν(σ) / b` (concavity of entropy, and
  `H(ξ^{j+m}) ≤ H(ξ^j) + H(σ^{-j} ξ^m)`), and `K^A(ω↾n) ≥ K^A(C(ω)↾bn) - O(1)`. Any injective
  computable code works; the formalization uses the one-hot code with `b = p`
  (`SymbolicLower.blockCode`). The measure theory and the entropy inequality are in
  `SymbolicLowerBoundAux`, the computability, randomness and complexity transfers in
  `SymbolicLowerBoundEffective`; the case `p = 0` is vacuous (no probability measure).

The `limsup` half of (I3) is not needed as a separate input: see `BlockCoding`.
Blueprint node `erg:symbolic-lower`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-- Hoyrup's theorem, relativized, binary alphabet: at a sequence that is Martin-Löf random
relative to `A` for an `A`-computable shift-invariant ergodic measure `ν` on `ℕ → Bool`,
`liminf_n K^A(ω↾n) / n ≥ h_ν(σ)` (Hoyrup, STACS 2012), proved in `HoyrupLower`.
Blueprint node `erg:symbolic-lower`. -/
theorem shiftEntropy_le_liminf_wordComplexity_bool (A : Set ℕ) (ν : Measure (ℕ → Bool))
    [IsProbabilityMeasure ν] (hν : Ergodic shiftMap ν) (hc : IsComputableWordMeasureIn A ν)
    {ω : ℕ → Bool} (hω : ω ∈ wordRandomPoints A ν) :
    shiftEntropy ν ≤ liminf (fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n) atTop :=
  shiftEntropy_le_liminf_wordComplexity_bool_of_hoyrup A ν hν hc hω

/-- Input (I3), `liminf` half, finite alphabet: at a sequence that is Martin-Löf random relative
to `A` for an `A`-computable shift-invariant ergodic measure `ν` on `ℕ → Fin p`,
`liminf_n K^A(ω↾n) / n ≥ h_ν(σ)`. Proved from the binary case.
Blueprint node `erg:symbolic-lower`. -/
theorem shiftEntropy_le_liminf_wordComplexity {p : ℕ} (A : Set ℕ) (ν : Measure (ℕ → Fin p))
    [IsProbabilityMeasure ν] (hν : Ergodic shiftMap ν) (hc : IsComputableWordMeasureIn A ν)
    {ω : ℕ → Fin p} (hω : ω ∈ wordRandomPoints A ν) :
    shiftEntropy ν ≤ liminf (fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n) atTop := by
  open SymbolicLower in
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : IsEmpty (ℕ → Fin 0) := ⟨fun f ↦ (f 0).elim0⟩
    exact absurd (Measure.eq_zero_of_isEmpty ν) (IsProbabilityMeasure.ne_zero ν)
  have := isProbabilityMeasure_blockAvg ν hp
  have h1 := shiftEntropy_le_mul_blockAvg ν hp hν.toMeasurePreserving.map_eq
  have h2 := shiftEntropy_le_liminf_wordComplexity_bool A (blockAvg ν) (ergodic_blockAvg hp hν)
    (isComputableWordMeasureIn_blockAvg ν hp hc) (blockCode_mem_wordRandomPoints ν hp hω)
  obtain ⟨c, hcK⟩ := exists_wordComplexity_blockCode_le A p
  set b : ℕ → ℝ≥0∞ := fun m ↦ (wordComplexity A (blockCode p ω) m : ℝ≥0∞) / m with hb
  set a : ℕ → ℝ≥0∞ := fun n ↦ (wordComplexity A ω n : ℝ≥0∞) / n with ha
  -- the liminf along the subsequence `p n` is at least the full liminf
  have hsub : liminf b atTop ≤ liminf (fun n ↦ b (p * n)) atTop := by
    refine (le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)).2 fun x hx ↦ ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf hx)
    exact eventually_atTop.2 ⟨N, fun n hn ↦ hN _ (hn.trans (Nat.le_mul_of_pos_left n hp))⟩
  have hmul : (p : ℝ≥0∞) * liminf (fun n ↦ b (p * n)) atTop ≤
      liminf (fun n ↦ (p : ℝ≥0∞) * b (p * n)) atTop := by
    have := ENNReal.le_liminf_mul (u := fun _ : ℕ ↦ (p : ℝ≥0∞)) (v := fun n ↦ b (p * n))
      (f := atTop)
    simpa [liminf_const, Pi.mul_def] using this
  -- `p K^A(C(ω)↾pn) / (pn) ≤ (K^A(ω↾n) + c) / n`
  have hcmp : ∀ᶠ n in atTop, (p : ℝ≥0∞) * b (p * n) ≤ (a + fun n : ℕ ↦ (c : ℝ≥0∞) / n) n := by
    refine eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩
    simp only [hb, ha, Pi.add_apply]
    rw [Nat.cast_mul, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ (by exact_mod_cast hp.ne')
      (ENNReal.natCast_ne_top p), ← ENNReal.add_div]
    gcongr
    exact_mod_cast hcK ω n
  have hlim : Tendsto (fun n : ℕ ↦ (c : ℝ≥0∞) / n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top c))
    simpa [div_eq_mul_inv] using this
  calc shiftEntropy ν ≤ p * shiftEntropy (blockAvg ν) := h1
    _ ≤ p * liminf b atTop := by gcongr
    _ ≤ p * liminf (fun n ↦ b (p * n)) atTop := by gcongr
    _ ≤ liminf (fun n ↦ (p : ℝ≥0∞) * b (p * n)) atTop := hmul
    _ ≤ liminf (a + fun n : ℕ ↦ (c : ℝ≥0∞) / n) atTop := liminf_le_liminf hcmp
    _ = liminf a atTop := ENNReal.liminf_add_of_right_tendsto_zero hlim a

end Kolmogorov.PointToSet
