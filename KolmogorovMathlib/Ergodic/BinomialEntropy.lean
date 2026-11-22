/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Binomial coefficients and the binary entropy function

`binEntropyBits θ = -θ log₂ θ - (1 - θ) log₂ (1 - θ)` is the binary entropy in bits, and
`choose_le_two_rpow_binEntropyBits`: if `k ≤ θ n` with `θ ≤ 1/2` then
`C(n, k) ≤ 2^{n H₂(θ)}`. Used in Step 4 of the proof of Theorem 1(b) of the note *Orbit
complexity of Martin-Löf random points equals entropy* (encoding a set of `≤ θ n` positions).
Blueprint node `erg:binomial`.
-/

noncomputable section

open Filter Topology

namespace Kolmogorov.Ergodic

/-- The binary entropy in bits, `H₂(θ) = -θ log₂ θ - (1 - θ) log₂ (1 - θ)`.
Blueprint node `erg:binomial`. -/
def binEntropyBits (θ : ℝ) : ℝ :=
  Real.binEntropy θ / Real.log 2

/-- `C(n, k) ≤ 2^{n H₂(θ)}` when `k ≤ θ n` and `0 ≤ θ ≤ 1/2`. Blueprint node `erg:binomial`. -/
theorem choose_le_two_rpow_binEntropyBits {n k : ℕ} {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ : θ ≤ 1 / 2)
    (hk : (k : ℝ) ≤ θ * n) :
    (n.choose k : ℝ) ≤ (2 : ℝ) ^ (n * binEntropyBits θ) := by
  rcases hθ₀.eq_or_lt with rfl | hθpos
  · have hk0 : k = 0 := by exact_mod_cast le_antisymm (by simpa using hk) (Nat.cast_nonneg k)
    simp [hk0, binEntropyBits]
  have h1θ : 0 < 1 - θ := by linarith
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := hk.trans (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    exact_mod_cast this
  -- one term of the binomial expansion of `(θ + (1 - θ))^n = 1`
  have hterm : (n.choose k : ℝ) * (θ ^ k * (1 - θ) ^ (n - k)) ≤ 1 := by
    have hsum := add_pow θ (1 - θ) n
    rw [add_sub_cancel, one_pow] at hsum
    have hle := Finset.single_le_sum (f := fun m ↦ θ ^ m * (1 - θ) ^ (n - m) * (n.choose m : ℝ))
      (fun m _ ↦ by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
    rw [← hsum] at hle
    linarith
  have hpos : 0 < θ ^ k * (1 - θ) ^ (n - k) := by positivity
  have hexp : θ ^ k * (1 - θ) ^ (n - k) =
      Real.exp (k * Real.log θ + ((n - k : ℕ) : ℝ) * Real.log (1 - θ)) := by
    rw [Real.exp_add, ← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity),
      Real.exp_log (by positivity)]
  have hlog : Real.log θ ≤ Real.log (1 - θ) := Real.log_le_log hθpos (by linarith)
  have hcast : ((n - k : ℕ) : ℝ) = n - k := by push_cast [hkn]; ring
  have hkey : -(k * Real.log θ + ((n - k : ℕ) : ℝ) * Real.log (1 - θ)) ≤
      n * Real.binEntropy θ := by
    rw [hcast, Real.binEntropy, Real.log_inv, Real.log_inv]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hlog)]
  have h2 : (2 : ℝ) ^ (n * binEntropyBits θ) = Real.exp (n * Real.binEntropy θ) := by
    rw [Real.rpow_def_of_pos two_pos, binEntropyBits]
    congr 1
    field_simp
  rw [h2]
  calc (n.choose k : ℝ) ≤ 1 / (θ ^ k * (1 - θ) ^ (n - k)) := (le_div_iff₀ hpos).mpr hterm
    _ = Real.exp (-(k * Real.log θ + ((n - k : ℕ) : ℝ) * Real.log (1 - θ))) := by
        rw [hexp, one_div, ← Real.exp_neg]
    _ ≤ Real.exp (n * Real.binEntropy θ) := Real.exp_le_exp.mpr hkey

/-- `H₂(θ) → 0` as `θ → 0⁺`. Blueprint node `erg:binomial`. -/
theorem tendsto_binEntropyBits_zero :
    Tendsto binEntropyBits (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun θ ↦ Real.binEntropy θ / Real.log 2) (𝓝 0) (𝓝 (0 / Real.log 2)) := by
    simpa only [Real.binEntropy_zero] using
      (Real.binEntropy_continuous.tendsto 0).div_const (Real.log 2)
  rw [zero_div] at h
  exact h.mono_left nhdsWithin_le_nhds

end Kolmogorov.Ergodic
