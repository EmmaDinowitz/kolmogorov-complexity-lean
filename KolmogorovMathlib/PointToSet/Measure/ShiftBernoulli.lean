/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Shift
import KolmogorovMathlib.PointToSet.Measure.EntropyLaw
import KolmogorovMathlib.PointToSet.Measure.EssentialBounds
import KolmogorovMathlib.AlgorithmicRandomness.StrongLaw
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Bernoulli measures and their mixtures on the full shift (Example 5.3)

On Cantor space `ℕ → Bool` with the metric `cantorMetricSpace` and the left shift `σ`, let
`ν_p` be the Bernoulli measure with parameter `0 < p < 1` (probability `p` of a one) and
`H(p) = -p log₂ p - (1 - p) log₂ (1 - p)` its entropy in bits (`binEntropyBits`).
(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*, §5,
Example 5.3 and §6.1.)

Bernoulli measures.

* `bernoulliMeasure_cylinder`: `ν_p[x↾n] = p^{#ones} (1 - p)^{#zeros}`;
* `infoBits_bernoulliMeasure_cylinder`: `-log₂ ν_p[x↾n] = ∑_{i<n} Y_i(x)` with
  `Y_i(x) = -log₂ p` or `-log₂ (1 - p)` according to `x i` (`bitInfo`);
* `ae_localEntropy_bernoulliMeasure`: by the strong law of large numbers, `ν_p`-a.e.
  `Φ_{ν_p}(x) = (H(p), H(p))`, so `entropyLaw_bernoulliMeasure`: `Λ_{ν_p} = δ_{(H(p), H(p))}`;
* `lintegral_infoBits_bernoulliMeasure_cylinder`: `∫ -log₂ ν_p[x↾n] dν_p = n H(p)`, so
  `informationRate_bernoulliMeasure`: `H̲_{ν_p} = H̄_{ν_p} = H(p)`.

Example 5.3 (invariant, non-ergodic): `μ = ½ (ν_p + ν_q)` (`bernoulliMixture`) with
`H(p) < H(q)`.

* `ae_localEntropy_bernoulliMixture`: the local entropy exists a.e. and is `H(p)` or `H(q)`;
* `entropyLaw_bernoulliMixture` (§6.1): `Λ_μ = ½ δ_{(H(p), H(p))} + ½ δ_{(H(q), H(q))}`;
* `measureEntropy_bernoulliMixture`: `h̲_μ = h̄_μ = (H(p) + H(q))/2`;
* `essInf_essSup_bernoulliMixture`: `ess inf = H(p)`, `ess sup = H(q)` for both local
  entropies;
* `lowerEntropy_randomPoints_bernoulliMixture`: by Theorem 4.3(a) the set of `μ`-random points
  has Bowen entropy `H(q)`;
* `informationRate_bernoulliMixture`: `H̲_μ = H̄_μ = (H(p) + H(q))/2`, from
  `n (H(p) + H(q))/2 ≤ ∫ -log₂ μ[x↾n] dμ ≤ n (H(p) + H(q))/2 + 1` (Gibbs' inequality for the
  lower bound, `μ ≥ ½ ν_p, ½ ν_q` for the upper one).

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory Finset
open scoped Topology ENNReal NNReal

attribute [local instance] cantorMetricSpace

/-! ### Bits of information -/

/-- The binary entropy in bits, `H(p) = -p log₂ p - (1 - p) log₂ (1 - p)`, as an element of
`[0, ∞]`. Blueprint node `meas:examples`. -/
noncomputable def binEntropyBits (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.binEntropy p / Real.log 2)

/-- The information `Y_i(x)` carried by one symbol under the Bernoulli measure of parameter
`p`: `-log₂ p` for a one and `-log₂ (1 - p)` for a zero. Blueprint node `meas:examples`. -/
noncomputable def bitInfo (p : ℝ) (b : Bool) : ℝ :=
  if b then -Real.logb 2 p else -Real.logb 2 (1 - p)

/-- The information of a symbol is nonnegative for `0 ≤ p ≤ 1`. -/
lemma bitInfo_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : 0 ≤ bitInfo p b := by
  cases b
  · simp only [bitInfo, Bool.false_eq_true, ite_false, neg_nonneg]
    exact Real.logb_nonpos one_lt_two (by linarith) (by linarith)
  · simp only [bitInfo, ite_true, neg_nonneg]
    exact Real.logb_nonpos one_lt_two hp0 hp1

/-- The mean information of a symbol is the binary entropy in bits:
`p (-log₂ p) + (1 - p) (-log₂ (1 - p)) = H(p)`. -/
lemma mean_bitInfo (p : ℝ) :
    p * bitInfo p true + (1 - p) * bitInfo p false = Real.binEntropy p / Real.log 2 := by
  simp only [bitInfo, ite_true, Bool.false_eq_true, ite_false, Real.logb, Real.binEntropy,
    Real.log_inv]
  ring

/-! ### Bernoulli measures -/

section bernoulli

variable (p : ℝ≥0) (hp : p ≤ 1)

/-- The one-coordinate Bernoulli law gives `{b}` mass `p` or `1 - p`. -/
private lemma bernoulli_singleton (b : Bool) :
    ProbabilityTheory.bernoulliMeasure true false ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩ {b} =
      if b then (p : ℝ≥0∞) else 1 - (p : ℝ≥0∞) := by
  cases b
  · have hcoe : unitInterval.toNNReal
        (unitInterval.symm ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩) = 1 - p := by
      ext
      simp [unitInterval.coe_symm_eq, NNReal.coe_sub hp]
    rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem _
      (measurableSet_singleton _) (by simp) rfl, hcoe]
    simp [ENNReal.coe_sub]
  · rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem _
      (measurableSet_singleton _) rfl (by simp)]
    rfl

/-- A cylinder of length `n` is the box fixing the first `n` coordinates. -/
private lemma cylinder_eq_pi (x : ℕ → Bool) (n : ℕ) :
    PiNat.cylinder x n = Set.pi (Finset.range n : Set ℕ) fun i ↦ {x i} := by
  ext y
  simp [PiNat.mem_cylinder_iff]

/-- The Bernoulli mass of a cylinder as a product of per-symbol weights. -/
theorem bernoulliMeasure_cylinder_prod (x : ℕ → Bool) (n : ℕ) :
    bernoulliMeasure p hp (PiNat.cylinder x n) =
      ∏ i ∈ Finset.range n, if x i then (p : ℝ≥0∞) else 1 - (p : ℝ≥0∞) := by
  rw [cylinder_eq_pi, bernoulliMeasure, Measure.infinitePi_pi _
    fun _ _ ↦ measurableSet_singleton _]
  exact Finset.prod_congr rfl fun i _ ↦ bernoulli_singleton p hp (x i)

/-- Example 5.3 (and the opening of §5): the Bernoulli mass of the cylinder `[x↾n]` is
`p^{#ones} (1 - p)^{#zeros}`, the counts being over the first `n` coordinates of `x`.
Blueprint node `meas:examples`. -/
theorem bernoulliMeasure_cylinder (x : ℕ → Bool) (n : ℕ) :
    bernoulliMeasure p hp (PiNat.cylinder x n) =
      (p : ℝ≥0∞) ^ ((Finset.range n).filter fun i ↦ x i = true).card *
        (1 - (p : ℝ≥0∞)) ^ ((Finset.range n).filter fun i ↦ x i = false).card := by
  rw [bernoulliMeasure_cylinder_prod, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp

include hp in
/-- The real value of a per-symbol weight. -/
private lemma toReal_weight (b : Bool) :
    (if b then (p : ℝ≥0∞) else 1 - (p : ℝ≥0∞)).toReal = if b then (p : ℝ) else 1 - p := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [← ENNReal.coe_one, ← ENNReal.coe_sub, ENNReal.coe_toReal, NNReal.coe_sub hp,
      NNReal.coe_one]
  · simp

/-- The weights `p` and `1 - p` are nonzero for `0 < p < 1`. -/
private lemma weight_ne_zero (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    (if b then (p : ℝ) else 1 - p) ≠ 0 := by
  have h0 : (0 : ℝ) < p := hp0
  have h1 : (p : ℝ) < 1 := hp1
  cases b <;> simp <;> linarith

/-- For `0 < p < 1` every cylinder has positive Bernoulli mass. -/
theorem bernoulliMeasure_cylinder_ne_zero (hp0 : 0 < p) (hp1 : p < 1) (x : ℕ → Bool) (n : ℕ) :
    bernoulliMeasure p hp (PiNat.cylinder x n) ≠ 0 := by
  rw [bernoulliMeasure_cylinder_prod, Finset.prod_ne_zero_iff]
  intro i _ h
  have := congrArg ENNReal.toReal h
  rw [toReal_weight p hp, ENNReal.toReal_zero] at this
  exact weight_ne_zero p hp0 hp1 _ this

/-- Example 5.3: the information of the cylinder `[x↾n]` is `∑_{i<n} Y_i(x)`, where `Y_i(x)`
is `-log₂ p` or `-log₂ (1 - p)` according to `x i`. Blueprint node `meas:examples`. -/
theorem infoBits_bernoulliMeasure_cylinder (hp0 : 0 < p) (hp1 : p < 1) (x : ℕ → Bool)
    (n : ℕ) :
    infoBits (bernoulliMeasure p hp (PiNat.cylinder x n)) =
      ENNReal.ofReal (∑ i ∈ Finset.range n, bitInfo p (x i)) := by
  have hpos := weight_ne_zero p hp0 hp1
  have hne := bernoulliMeasure_cylinder_ne_zero p hp hp0 hp1 x n
  rw [infoBits_of_ne hne, bernoulliMeasure_cylinder_prod, ENNReal.toReal_prod]
  simp only [toReal_weight p hp]
  rw [Real.logb_prod _ _ fun i _ ↦ hpos (x i), ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases x i <;> simp [bitInfo]

/-- The strong law for the symbol informations: `ν_p`-a.e.
`(1/n) ∑_{i<n} Y_i(x) → H(p)`. -/
theorem ae_tendsto_bitInfo :
    ∀ᵐ x ∂bernoulliMeasure p hp, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n,
      bitInfo p (x i)) / n) atTop (𝓝 (Real.binEntropy p / Real.log 2)) := by
  have hae := ProbabilityTheory.strong_law_ae_real (μ := bernoulliMeasure p hp)
    (fun (i : ℕ) (w : ℕ → Bool) ↦ bitVal (w i))
    (bernoulli_integrable_coord p hp)
    (fun i j hij ↦ (bernoulli_iIndepFun p hp).indepFun hij)
    (bernoulli_identDistrib p hp)
  rw [bernoulli_integral_coord p hp] at hae
  filter_upwards [hae] with x hx
  have hH : bitInfo p false + (bitInfo p true - bitInfo p false) * p =
      Real.binEntropy p / Real.log 2 := by
    rw [← mean_bitInfo (p : ℝ)]; ring
  have hlim : Tendsto (fun n : ℕ ↦ bitInfo p false + (bitInfo p true - bitInfo p false) *
      ((∑ i ∈ Finset.range n, bitVal (x i)) / n)) atTop
      (𝓝 (Real.binEntropy p / Real.log 2)) := hH ▸ tendsto_const_nhds.add (hx.const_mul _)
  refine hlim.congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  have hsum : ∑ i ∈ Finset.range n, bitInfo p (x i) =
      ∑ i ∈ Finset.range n, (bitInfo p false + (bitInfo p true - bitInfo p false) *
        bitVal (x i)) :=
    Finset.sum_congr rfl fun i _ ↦ by cases x i <;> simp [bitVal]
  dsimp only
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum]
  field_simp

/-- The Cantor metric is the first-difference metric with ratio `1/2`. -/
private lemma hd_cantor : ∀ x y : ℕ → Bool, x ≠ y →
    dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y := fun _ _ ↦ cantorMetricSpace_dist_eq

/-- If `a n / n → c` in `ℝ` and `a n ≥ 0`, the `ℝ≥0∞` rates of `ofReal (a n)` both equal
`ofReal c`. -/
private lemma liminf_limsup_ofReal_div {a : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n : ℕ ↦ a n / n) atTop (𝓝 c)) :
    liminf (fun n : ℕ ↦ ENNReal.ofReal (a n) / n) atTop = ENNReal.ofReal c ∧
      limsup (fun n : ℕ ↦ ENNReal.ofReal (a n) / n) atTop = ENNReal.ofReal c := by
  have h' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (a n) / n) atTop (𝓝 (ENNReal.ofReal c)) := by
    refine (ENNReal.tendsto_ofReal h).congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [ENNReal.ofReal_div_of_pos hn0, ENNReal.ofReal_natCast]
  exact ⟨h'.liminf_eq, h'.limsup_eq⟩

/-- Example 5.3: for a Bernoulli measure `ν_p` with `0 < p < 1`, `ν_p`-almost every point has
lower and upper local entropies `H(p)` under the shift (strong law of large numbers).
Blueprint node `meas:examples`. -/
theorem ae_localEntropy_bernoulliMeasure (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᵐ x ∂bernoulliMeasure p hp,
      localEntropy (bernoulliMeasure p hp) shiftMap x = (binEntropyBits p, binEntropyBits p) := by
  filter_upwards [ae_tendsto_bitInfo p hp] with x hx
  rw [localEntropy_shiftMap (by norm_num) (by norm_num) hd_cantor]
  simp only [infoBits_bernoulliMeasure_cylinder p hp hp0 hp1]
  obtain ⟨h1, h2⟩ := liminf_limsup_ofReal_div hx
  rw [h1, h2, binEntropyBits]

/-- Example 5.3 / §6.1: the entropy law of a Bernoulli measure `ν_p` (`0 < p < 1`) is the point
mass at `(H(p), H(p))`. Blueprint node `meas:examples`. -/
theorem entropyLaw_bernoulliMeasure (hp0 : 0 < p) (hp1 : p < 1) :
    entropyLaw (bernoulliMeasure p hp) shiftMap =
      Measure.dirac (binEntropyBits p, binEntropyBits p) := by
  rw [entropyLaw, Measure.map_congr (ae_localEntropy_bernoulliMeasure p hp hp0 hp1),
    Measure.map_const, measure_univ, one_smul]

/-- The mean information of one coordinate: `∫ Y_i dν_p = H(p)`. -/
private lemma lintegral_bitInfo (hp0 : 0 < p) (hp1 : p < 1) (i : ℕ) :
    ∫⁻ x, ENNReal.ofReal (bitInfo p (x i)) ∂bernoulliMeasure p hp = binEntropyBits p := by
  have hmp := measurePreserving_eval_infinitePi
    (fun _ : ℕ ↦ ProbabilityTheory.bernoulliMeasure true false
      ⟨p, p.2, NNReal.coe_le_one.mpr hp⟩) i
  have hg : Measurable fun b : Bool ↦ ENNReal.ofReal (bitInfo p b) := measurable_of_countable _
  calc ∫⁻ x, ENNReal.ofReal (bitInfo p (x i)) ∂bernoulliMeasure p hp
      = ∫⁻ b, ENNReal.ofReal (bitInfo p b)
          ∂(Measure.map (Function.eval i) (bernoulliMeasure p hp)) :=
        (lintegral_map hg (measurable_pi_apply i)).symm
    _ = binEntropyBits p := ?_
  rw [bernoulliMeasure, hmp.map_eq, lintegral_fintype]
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, bernoulli_singleton p hp, ite_true,
    Bool.false_eq_true, ite_false]
  have h0 : (0 : ℝ) ≤ p := hp0.le
  have h1 : (p : ℝ) ≤ 1 := hp
  rw [show (1 : ℝ≥0∞) - p = ENNReal.ofReal (1 - p) by
      rw [ENNReal.ofReal_sub _ h0, ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal],
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (bitInfo_nonneg h0 h1 _),
    ← ENNReal.ofReal_mul (bitInfo_nonneg h0 h1 _),
    ← ENNReal.ofReal_add (mul_nonneg (bitInfo_nonneg h0 h1 _) h0)
      (mul_nonneg (bitInfo_nonneg h0 h1 _) (by linarith)), binEntropyBits, ← mean_bitInfo]
  congr 1
  ring

/-- Example 5.3: the exact mean information of the cylinders of a Bernoulli measure,
`∫ -log₂ ν_p[x↾n] dν_p(x) = n H(p)`. Blueprint node `meas:examples`. -/
theorem lintegral_infoBits_bernoulliMeasure_cylinder (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    ∫⁻ x, infoBits (bernoulliMeasure p hp (PiNat.cylinder x n)) ∂bernoulliMeasure p hp =
      n * binEntropyBits p := by
  have h0 : (0 : ℝ) ≤ p := hp0.le
  have h1 : (p : ℝ) ≤ 1 := hp
  simp only [infoBits_bernoulliMeasure_cylinder p hp hp0 hp1]
  simp_rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ bitInfo_nonneg h0 h1 _]
  rw [lintegral_finsetSum]
  swap
  · exact fun i _ ↦ (measurable_of_countable fun b : Bool ↦ ENNReal.ofReal (bitInfo p b)).comp
      (measurable_pi_apply i)
  simp only [lintegral_bitInfo p hp hp0 hp1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- If `a n = n c` for all `n` then both `ℝ≥0∞` growth rates of `a` are `c`. -/
private lemma liminf_limsup_mul_div {a : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ n, a n = n * c) :
    liminf (fun n : ℕ ↦ a n / n) atTop = c ∧ limsup (fun n : ℕ ↦ a n / n) atTop = c := by
  have h' : (fun n : ℕ ↦ a n / n) =ᶠ[atTop] fun _ ↦ c :=
    (eventually_ge_atTop 1).mono fun n hn ↦ by
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
      dsimp only
      rw [h, mul_comm, ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n)]
  rw [liminf_congr h', limsup_congr h', liminf_const, limsup_const]
  exact ⟨rfl, rfl⟩

/-- Example 5.3: the information rates of a Bernoulli measure `ν_p` (`0 < p < 1`) under the
shift are both `H(p)`. Blueprint node `meas:examples`. -/
theorem informationRate_bernoulliMeasure (hp0 : 0 < p) (hp1 : p < 1) :
    informationRate (bernoulliMeasure p hp) shiftMap = (binEntropyBits p, binEntropyBits p) := by
  rw [informationRate_shiftMap (by norm_num) (by norm_num) hd_cantor]
  obtain ⟨h1, h2⟩ := liminf_limsup_mul_div
    (lintegral_infoBits_bernoulliMeasure_cylinder p hp hp0 hp1)
  rw [h1, h2, binEntropyBits]

end bernoulli

/-! ### Gibbs' inequality on cylinders -/

section gibbs

/-- The restriction of a sequence to its first `n` coordinates. -/
private def restrictFin (n : ℕ) (x : ℕ → Bool) : Fin n → Bool := fun i ↦ x i

/-- The restriction to the first `n` coordinates is measurable. -/
private lemma measurable_restrictFin (n : ℕ) : Measurable (restrictFin n) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (i : ℕ)

/-- The cylinder `[x↾n]` is the fibre of the restriction through `x`. -/
private lemma cylinder_eq_preimage (x : ℕ → Bool) (n : ℕ) :
    PiNat.cylinder x n = restrictFin n ⁻¹' {restrictFin n x} := by
  ext y
  simp only [PiNat.mem_cylinder_iff, Set.mem_preimage, Set.mem_singleton_iff, restrictFin,
    funext_iff,
    Fin.forall_iff]

/-- Every word of length `n` is the restriction of some sequence. -/
private lemma restrictFin_surjective (n : ℕ) : Function.Surjective (restrictFin n) :=
  fun s ↦ ⟨fun i ↦ if h : i < n then s ⟨i, h⟩ else false, funext fun i ↦ by
    simp [restrictFin, i.2]⟩

/-- The integral of a function of the cylinder `[x↾n]` is a finite sum over the words of
length `n`. -/
private lemma lintegral_cylinder (ν : Measure (ℕ → Bool)) (n : ℕ) (g : (Fin n → Bool) → ℝ≥0∞) :
    ∫⁻ x, g (restrictFin n x) ∂ν = ∑ s, g s * ν (restrictFin n ⁻¹' {s}) := by
  rw [← lintegral_map (measurable_of_countable g) (measurable_restrictFin n), lintegral_fintype]
  simp only [Measure.map_apply (measurable_restrictFin n) (measurableSet_singleton _)]

/-- The masses of the cylinders of length `n` add up to the total mass. -/
private lemma sum_measure_cylinder (ν : Measure (ℕ → Bool)) (n : ℕ) :
    ∑ s, ν (restrictFin n ⁻¹' {s}) = ν univ := by
  have := lintegral_cylinder ν n fun _ ↦ 1
  simp only [lintegral_const, one_mul] at this
  exact this.symm

/-- Gibbs' inequality on the cylinders of length `n`: if all these cylinders have positive
mass for the probability measures `ν` and `μ`, then
`∫ -log₂ ν[x↾n] dν ≤ ∫ -log₂ μ[x↾n] dν`. -/
theorem lintegral_infoBits_cylinder_le (ν μ : Measure (ℕ → Bool)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (n : ℕ) (hν : ∀ x, ν (PiNat.cylinder x n) ≠ 0)
    (hμ : ∀ x, μ (PiNat.cylinder x n) ≠ 0) :
    ∫⁻ x, infoBits (ν (PiNat.cylinder x n)) ∂ν ≤ ∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂ν := by
  set A : (Fin n → Bool) → ℝ≥0∞ := fun s ↦ ν (restrictFin n ⁻¹' {s})
  set B : (Fin n → Bool) → ℝ≥0∞ := fun s ↦ μ (restrictFin n ⁻¹' {s})
  have hA0 : ∀ s, A s ≠ 0 := fun s ↦ by
    obtain ⟨x, rfl⟩ := restrictFin_surjective n s
    simpa [A, cylinder_eq_preimage] using hν x
  have hB0 : ∀ s, B s ≠ 0 := fun s ↦ by
    obtain ⟨x, rfl⟩ := restrictFin_surjective n s
    simpa [B, cylinder_eq_preimage] using hμ x
  have hAt : ∀ s, A s ≠ ⊤ := fun s ↦ measure_ne_top _ _
  have hBt : ∀ s, B s ≠ ⊤ := fun s ↦ measure_ne_top _ _
  have hApos : ∀ s, 0 < (A s).toReal := fun s ↦ ENNReal.toReal_pos (hA0 s) (hAt s)
  have hBpos : ∀ s, 0 < (B s).toReal := fun s ↦ ENNReal.toReal_pos (hB0 s) (hBt s)
  have hA1 : ∀ s, (A s).toReal ≤ 1 := fun s ↦ ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have hB1 : ∀ s, (B s).toReal ≤ 1 := fun s ↦ ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have hsumA : ∑ s, (A s).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun s _ ↦ hAt s, sum_measure_cylinder, measure_univ,
      ENNReal.toReal_one]
  have hsumB : ∑ s, (B s).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun s _ ↦ hBt s, sum_measure_cylinder, measure_univ,
      ENNReal.toReal_one]
  -- rewrite both sides as finite sums
  have hL : ∫⁻ x, infoBits (ν (PiNat.cylinder x n)) ∂ν =
      ENNReal.ofReal (∑ s, -Real.logb 2 (A s).toReal * (A s).toReal) := by
    simp_rw [cylinder_eq_preimage]
    rw [lintegral_cylinder ν n fun s ↦ infoBits (A s), ENNReal.ofReal_sum_of_nonneg fun s _ ↦
      mul_nonneg (neg_nonneg.2 (Real.logb_nonpos one_lt_two (hApos s).le (hA1 s)))
        (hApos s).le]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [infoBits_of_ne (hA0 s), ENNReal.ofReal_mul
      (neg_nonneg.2 (Real.logb_nonpos one_lt_two (hApos s).le (hA1 s))),
      ENNReal.ofReal_toReal (hAt s)]
  have hR : ∫⁻ x, infoBits (μ (PiNat.cylinder x n)) ∂ν =
      ENNReal.ofReal (∑ s, -Real.logb 2 (B s).toReal * (A s).toReal) := by
    simp_rw [cylinder_eq_preimage]
    rw [lintegral_cylinder ν n fun s ↦ infoBits (B s), ENNReal.ofReal_sum_of_nonneg fun s _ ↦
      mul_nonneg (neg_nonneg.2 (Real.logb_nonpos one_lt_two (hBpos s).le (hB1 s)))
        (hApos s).le]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [infoBits_of_ne (hB0 s), ENNReal.ofReal_mul
      (neg_nonneg.2 (Real.logb_nonpos one_lt_two (hBpos s).le (hB1 s))),
      ENNReal.ofReal_toReal (hAt s)]
  rw [hL, hR]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `a (log₂ b - log₂ a) ≤ (b - a) / log 2`
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : ∀ s, (A s).toReal * (Real.logb 2 (B s).toReal - Real.logb 2 (A s).toReal) ≤
      ((B s).toReal - (A s).toReal) / Real.log 2 := fun s ↦ by
    have ha := hApos s
    have hb := hBpos s
    have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at h
    rw [Real.logb, Real.logb, ← sub_div, mul_div_assoc', div_le_div_iff_of_pos_right hlog2]
    calc (A s).toReal * (Real.log (B s).toReal - Real.log (A s).toReal)
        ≤ (A s).toReal * ((B s).toReal / (A s).toReal - 1) :=
          mul_le_mul_of_nonneg_left h ha.le
      _ = (B s).toReal - (A s).toReal := by field_simp
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) ↦ key s
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hsumA, hsumB, sub_self, zero_div] at hsum
  have : ∑ s, -Real.logb 2 (B s).toReal * (A s).toReal -
      ∑ s, -Real.logb 2 (A s).toReal * (A s).toReal =
      ∑ s, (A s).toReal * (Real.logb 2 (A s).toReal - Real.logb 2 (B s).toReal) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  have h2 : ∑ s, (A s).toReal * (Real.logb 2 (A s).toReal - Real.logb 2 (B s).toReal) =
      -∑ s, (A s).toReal * (Real.logb 2 (B s).toReal - Real.logb 2 (A s).toReal) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  linarith

end gibbs

/-! ### Example 5.3: a mixture of two Bernoulli measures -/

section mixture

variable (p : ℝ≥0) (hp : p ≤ 1) (q : ℝ≥0) (hq : q ≤ 1)

/-- The mixture `μ = ½ (ν_p + ν_q)` of two Bernoulli measures (Example 5.3).
Blueprint node `meas:examples`. -/
noncomputable def bernoulliMixture : Measure (ℕ → Bool) :=
  (2⁻¹ : ℝ≥0∞) • (bernoulliMeasure p hp + bernoulliMeasure q hq)

/-- The mixture of two Bernoulli measures is a probability measure. -/
instance : IsProbabilityMeasure (bernoulliMixture p hp q hq) :=
  ⟨by simp [bernoulliMixture, measure_univ, ENNReal.inv_two_add_inv_two]⟩

/-- Integrals against the mixture are averages of the integrals against its components. -/
private lemma lintegral_bernoulliMixture (g : (ℕ → Bool) → ℝ≥0∞) :
    ∫⁻ x, g x ∂bernoulliMixture p hp q hq =
      2⁻¹ * (∫⁻ x, g x ∂bernoulliMeasure p hp + ∫⁻ x, g x ∂bernoulliMeasure q hq) := by
  rw [bernoulliMixture, lintegral_smul_measure, lintegral_add_measure, smul_eq_mul]

/-- Images of the mixture are averages of the images of its components. -/
private lemma map_bernoulliMixture {β : Type*} [MeasurableSpace β] {g : (ℕ → Bool) → β}
    (hg : Measurable g) :
    Measure.map g (bernoulliMixture p hp q hq) =
      (2⁻¹ : ℝ≥0∞) • (Measure.map g (bernoulliMeasure p hp) +
        Measure.map g (bernoulliMeasure q hq)) := by
  rw [bernoulliMixture, Measure.map_smul, Measure.map_add _ _ hg]
  exact hg.aemeasurable

/-- `ν_p ≪ μ`. -/
private lemma absolutelyContinuous_left :
    bernoulliMeasure p hp ≪ bernoulliMixture p hp q hq := fun s hs ↦ by
  simp only [bernoulliMixture, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.ofNat_ne_top, false_or, add_eq_zero] at hs
  exact hs.1

/-- `ν_q ≪ μ`. -/
private lemma absolutelyContinuous_right :
    bernoulliMeasure q hq ≪ bernoulliMixture p hp q hq := fun s hs ↦ by
  simp only [bernoulliMixture, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.ofNat_ne_top, false_or, add_eq_zero] at hs
  exact hs.2

/-- `ν_p`-a.e. the local entropies of the mixture are `(H(p), H(p))`. -/
private lemma ae_left (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᵐ x ∂bernoulliMeasure p hp,
      localEntropy (bernoulliMixture p hp q hq) shiftMap x =
        (binEntropyBits p, binEntropyBits p) := by
  filter_upwards [ae_localEntropy_eq_of_absolutelyContinuous continuous_shiftMap_cantor
      (absolutelyContinuous_left p hp q hq),
    ae_localEntropy_bernoulliMeasure p hp hp0 hp1] with x h1 h2
  rw [← h1, h2]

/-- `ν_q`-a.e. the local entropies of the mixture are `(H(q), H(q))`. -/
private lemma ae_right (hq0 : 0 < q) (hq1 : q < 1) :
    ∀ᵐ x ∂bernoulliMeasure q hq,
      localEntropy (bernoulliMixture p hp q hq) shiftMap x =
        (binEntropyBits q, binEntropyBits q) := by
  filter_upwards [ae_localEntropy_eq_of_absolutelyContinuous continuous_shiftMap_cantor
      (absolutelyContinuous_right p hp q hq),
    ae_localEntropy_bernoulliMeasure q hq hq0 hq1] with x h1 h2
  rw [← h1, h2]

/-- Example 5.3: for `μ = ½ (ν_p + ν_q)` with `0 < p, q < 1`, the local entropy exists
`μ`-a.e. and equals `H(p)` or `H(q)` (each with probability `½`, see
`entropyLaw_bernoulliMixture`). Blueprint node `meas:examples`. -/
theorem ae_localEntropy_bernoulliMixture (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hq1 : q < 1) :
    ∀ᵐ x ∂bernoulliMixture p hp q hq,
      localEntropy (bernoulliMixture p hp q hq) shiftMap x =
          (binEntropyBits p, binEntropyBits p) ∨
        localEntropy (bernoulliMixture p hp q hq) shiftMap x =
          (binEntropyBits q, binEntropyBits q) := by
  rw [bernoulliMixture, Measure.ae_ennreal_smul_measure_iff (by norm_num), ae_add_measure_iff]
  exact ⟨(ae_left p hp q hq hp0 hp1).mono fun _ h ↦ Or.inl h,
    (ae_right p hp q hq hq0 hq1).mono fun _ h ↦ Or.inr h⟩

/-- Example 5.3 and §6.1: the entropy law of `μ = ½ (ν_p + ν_q)` (`0 < p, q < 1`) is
`½ δ_{(H(p), H(p))} + ½ δ_{(H(q), H(q))}`. The paper assumes `H(p) < H(q)`; the formula holds
without it. Blueprint node `meas:examples`. -/
theorem entropyLaw_bernoulliMixture (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    entropyLaw (bernoulliMixture p hp q hq) shiftMap =
      (2⁻¹ : ℝ≥0∞) • Measure.dirac (binEntropyBits p, binEntropyBits p) +
        (2⁻¹ : ℝ≥0∞) • Measure.dirac (binEntropyBits q, binEntropyBits q) := by
  have hm := measurable_localEntropy (bernoulliMixture p hp q hq) continuous_shiftMap_cantor
  rw [entropyLaw, map_bernoulliMixture p hp q hq hm,
    Measure.map_congr (ae_left p hp q hq hp0 hp1), Measure.map_congr (ae_right p hp q hq hq0 hq1),
    Measure.map_const, Measure.map_const, measure_univ, measure_univ, one_smul, one_smul,
    smul_add]

/-- A pair of functions that is a.e. equal to `(c, c)` has both integrals `c`. -/
private lemma lintegral_fst_snd_of_ae {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    {F : (ℕ → Bool) → ℝ≥0∞ × ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ᵐ x ∂ν, F x = (c, c)) :
    ∫⁻ x, (F x).1 ∂ν = c ∧ ∫⁻ x, (F x).2 ∂ν = c := by
  constructor <;>
    rw [lintegral_congr_ae (g := fun _ ↦ c) (h.mono fun x hx ↦ by simp [hx]), lintegral_const,
      measure_univ, mul_one]

/-- Example 5.3: the Feng–Huang entropies of `μ = ½ (ν_p + ν_q)` (`0 < p, q < 1`) are both
`(H(p) + H(q))/2`. (The paper also identifies this with the Kolmogorov–Sinai entropy `h_μ(σ)`,
which this library does not define.) Blueprint node `meas:examples`. -/
theorem measureEntropy_bernoulliMixture (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hq1 : q < 1) :
    measureEntropy (bernoulliMixture p hp q hq) shiftMap =
      ((binEntropyBits p + binEntropyBits q) / 2, (binEntropyBits p + binEntropyBits q) / 2) := by
  have hl := ae_left p hp q hq hp0 hp1
  have hr := ae_right p hp q hq hq0 hq1
  obtain ⟨hl1, hl2⟩ := lintegral_fst_snd_of_ae hl
  obtain ⟨hr1, hr2⟩ := lintegral_fst_snd_of_ae hr
  simp only [measureEntropy, lintegral_bernoulliMixture, hl1, hl2, hr1, hr2,
    ENNReal.div_eq_inv_mul]

/-- Essential bounds of a function that is `a` on one component and `b ≥ a` on the other. -/
private lemma essInf_essSup_of_two {μ ν₁ ν₂ : Measure (ℕ → Bool)} [NeZero ν₁] [NeZero ν₂]
    {f : (ℕ → Bool) → ℝ≥0∞} {a b : ℝ≥0∞} (hab : a ≤ b) (h₁ : ν₁ ≪ μ) (h₂ : ν₂ ≪ μ)
    (hμ : ∀ᵐ x ∂μ, f x = a ∨ f x = b) (hf₁ : ∀ᵐ x ∂ν₁, f x = a) (hf₂ : ∀ᵐ x ∂ν₂, f x = b) :
    essInf f μ = a ∧ essSup f μ = b := by
  constructor
  · refine le_antisymm ?_ (le_essInf_of_ae_le a (hμ.mono fun x hx ↦ ?_))
    · calc essInf f μ ≤ essInf f ν₁ := essInf_antitone_measure h₁
        _ = a := by rw [essInf_congr_ae hf₁, essInf_const' a]
    · rcases hx with hx | hx <;> simp [hx, hab]
  · refine le_antisymm (essSup_le_of_ae_le b (hμ.mono fun x hx ↦ ?_)) ?_
    · rcases hx with hx | hx <;> simp [hx, hab]
    · calc b = essSup f ν₂ := by rw [essSup_congr_ae hf₂, essSup_const' b]
        _ ≤ essSup f μ := essSup_mono_measure h₂

/-- Example 5.3: for `μ = ½ (ν_p + ν_q)` with `0 < p, q < 1` and `H(p) ≤ H(q)`, the essential
infimum of each local entropy is `H(p)` and the essential supremum is `H(q)`. (The paper
assumes `H(p) < H(q)`; `≤` suffices.) Blueprint node `meas:examples`. -/
theorem essInf_essSup_bernoulliMixture (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hpq : binEntropyBits p ≤ binEntropyBits q) :
    (essInf (fun x ↦ (localEntropy (bernoulliMixture p hp q hq) shiftMap x).1)
          (bernoulliMixture p hp q hq) = binEntropyBits p ∧
        essInf (fun x ↦ (localEntropy (bernoulliMixture p hp q hq) shiftMap x).2)
          (bernoulliMixture p hp q hq) = binEntropyBits p) ∧
      essSup (fun x ↦ (localEntropy (bernoulliMixture p hp q hq) shiftMap x).1)
          (bernoulliMixture p hp q hq) = binEntropyBits q ∧
        essSup (fun x ↦ (localEntropy (bernoulliMixture p hp q hq) shiftMap x).2)
          (bernoulliMixture p hp q hq) = binEntropyBits q := by
  have hμ := ae_localEntropy_bernoulliMixture p hp q hq hp0 hp1 hq0 hq1
  have hl := ae_left p hp q hq hp0 hp1
  have hr := ae_right p hp q hq hq0 hq1
  have h1 := essInf_essSup_of_two (f := fun x ↦
      (localEntropy (bernoulliMixture p hp q hq) shiftMap x).1) hpq
    (absolutelyContinuous_left p hp q hq) (absolutelyContinuous_right p hp q hq)
    (hμ.mono fun x hx ↦ by rcases hx with hx | hx <;> simp [hx])
    (hl.mono fun x hx ↦ by simp [hx]) (hr.mono fun x hx ↦ by simp [hx])
  have h2 := essInf_essSup_of_two (f := fun x ↦
      (localEntropy (bernoulliMixture p hp q hq) shiftMap x).2) hpq
    (absolutelyContinuous_left p hp q hq) (absolutelyContinuous_right p hp q hq)
    (hμ.mono fun x hx ↦ by rcases hx with hx | hx <;> simp [hx])
    (hl.mono fun x hx ↦ by simp [hx]) (hr.mono fun x hx ↦ by simp [hx])
  exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩

/-- Example 5.3 via Theorem 4.3(a): for `μ = ½ (ν_p + ν_q)` with `0 < p, q < 1` and
`H(p) ≤ H(q)`, for every presentation `P` of Cantor space and every oracle `A` admissible for
`(ℕ → Bool, d, σ, μ)`, the set of `μ`-random points has Bowen entropy `H(q)`. (The paper
assumes `H(p) < H(q)`.) Blueprint node `meas:examples`. -/
theorem lowerEntropy_randomPoints_bernoulliMixture (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hpq : binEntropyBits p ≤ binEntropyBits q) (P : Presentation (ℕ → Bool))
    (A : Set ℕ) (hA : IsMeasureAdmissible P shiftMap (bernoulliMixture p hp q hq) A) :
    lowerEntropy shiftMap (randomPoints P A (bernoulliMixture p hp q hq)) = binEntropyBits q := by
  rw [lowerEntropy_randomPoints P shiftMap continuous_shiftMap_cantor A _ hA]
  exact (essInf_essSup_bernoulliMixture p hp q hq hp0 hp1 hq0 hq1 hpq).2.1

/-- The mixture gives every cylinder at least half its `ν_p`-mass. -/
private lemma le_mixture_left (s : Set (ℕ → Bool)) :
    2⁻¹ * bernoulliMeasure p hp s ≤ bernoulliMixture p hp q hq s := by
  simp only [bernoulliMixture, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  gcongr
  exact le_self_add

/-- The mixture gives every cylinder at least half its `ν_q`-mass. -/
private lemma le_mixture_right (s : Set (ℕ → Bool)) :
    2⁻¹ * bernoulliMeasure q hq s ≤ bernoulliMixture p hp q hq s := by
  simp only [bernoulliMixture, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  gcongr
  exact le_add_self

/-- Halving a mass costs at most one bit: `-log₂ (m/2) ≤ -log₂ m + 1`, so for `m' ≥ m/2`,
`-log₂ m' ≤ -log₂ m + 1`. -/
private lemma infoBits_le_of_half_le {m m' : ℝ≥0∞} (h : 2⁻¹ * m ≤ m') :
    infoBits m' ≤ infoBits m + 1 := by
  refine (infoBits_antitone h).trans ((infoBits_mul_le (by norm_num) (by norm_num) m).trans ?_)
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat, Real.logb_inv, Real.logb_self_eq_one one_lt_two,
    abs_neg, abs_one, ENNReal.ofReal_one]

/-- The mean cylinder information of the mixture against one of its components is within one
bit of that component's own: `n H(p) ≤ ∫ -log₂ μ[x↾n] dν_p ≤ n H(p) + 1`. -/
private lemma lintegral_mixture_component (r : ℝ≥0) (hr : r ≤ 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hle : ∀ s, 2⁻¹ * bernoulliMeasure r hr s ≤ bernoulliMixture p hp q hq s) (n : ℕ) :
    n * binEntropyBits r ≤ ∫⁻ x, infoBits (bernoulliMixture p hp q hq (PiNat.cylinder x n))
        ∂bernoulliMeasure r hr ∧
      ∫⁻ x, infoBits (bernoulliMixture p hp q hq (PiNat.cylinder x n))
        ∂bernoulliMeasure r hr ≤ n * binEntropyBits r + 1 := by
  have hne := bernoulliMeasure_cylinder_ne_zero r hr hr0 hr1
  constructor
  · rw [← lintegral_infoBits_bernoulliMeasure_cylinder r hr hr0 hr1]
    refine lintegral_infoBits_cylinder_le _ _ n (hne · n) fun x h ↦ ?_
    have := (hle (PiNat.cylinder x n)).trans_eq h
    simp only [nonpos_iff_eq_zero, mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.ofNat_ne_top,
      false_or] at this
    exact hne x n this
  · calc ∫⁻ x, infoBits (bernoulliMixture p hp q hq (PiNat.cylinder x n))
          ∂bernoulliMeasure r hr
        ≤ ∫⁻ x, (infoBits (bernoulliMeasure r hr (PiNat.cylinder x n)) + 1)
          ∂bernoulliMeasure r hr :=
          lintegral_mono fun x ↦ infoBits_le_of_half_le (hle _)
      _ = n * binEntropyBits r + 1 := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_infoBits_bernoulliMeasure_cylinder r hr hr0 hr1]

/-- Example 5.3: bounds on the mean cylinder information of `μ = ½ (ν_p + ν_q)`:
`n (H(p) + H(q))/2 ≤ ∫ -log₂ μ[x↾n] dμ ≤ n (H(p) + H(q))/2 + 1`. The lower bound is Gibbs'
inequality (concavity of the Shannon entropy of the cylinder partition), the upper bound the
fact that the entropy of a two-component mixture exceeds the average by at most one bit.
Blueprint node `meas:examples`. -/
theorem lintegral_infoBits_bernoulliMixture_cylinder (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (n : ℕ) :
    n * ((binEntropyBits p + binEntropyBits q) / 2) ≤
        ∫⁻ x, infoBits (bernoulliMixture p hp q hq (PiNat.cylinder x n))
          ∂bernoulliMixture p hp q hq ∧
      ∫⁻ x, infoBits (bernoulliMixture p hp q hq (PiNat.cylinder x n))
          ∂bernoulliMixture p hp q hq ≤
        n * ((binEntropyBits p + binEntropyBits q) / 2) + 1 := by
  obtain ⟨hl1, hl2⟩ := lintegral_mixture_component p hp q hq p hp hp0 hp1
    (le_mixture_left p hp q hq) n
  obtain ⟨hr1, hr2⟩ := lintegral_mixture_component p hp q hq q hq hq0 hq1
    (le_mixture_right p hp q hq) n
  have hsplit : ∫⁻ x, infoBits (bernoulliMixture p hp q hq (PiNat.cylinder x n))
      ∂bernoulliMixture p hp q hq =
      2⁻¹ * (∫⁻ x, infoBits (bernoulliMixture p hp q hq (PiNat.cylinder x n))
          ∂bernoulliMeasure p hp +
        ∫⁻ x, infoBits (bernoulliMixture p hp q hq (PiNat.cylinder x n))
          ∂bernoulliMeasure q hq) :=
    lintegral_bernoulliMixture p hp q hq _
  rw [hsplit, ENNReal.div_eq_inv_mul]
  constructor
  · calc (n : ℝ≥0∞) * (2⁻¹ * (binEntropyBits p + binEntropyBits q))
        = 2⁻¹ * (n * binEntropyBits p + n * binEntropyBits q) := by ring
      _ ≤ _ := by gcongr
  · calc 2⁻¹ * (∫⁻ x, infoBits (bernoulliMixture p hp q hq (PiNat.cylinder x n))
            ∂bernoulliMeasure p hp +
          ∫⁻ x, infoBits (bernoulliMixture p hp q hq (PiNat.cylinder x n))
            ∂bernoulliMeasure q hq)
        ≤ 2⁻¹ * (n * binEntropyBits p + 1 + (n * binEntropyBits q + 1)) := by gcongr
      _ = n * (2⁻¹ * (binEntropyBits p + binEntropyBits q)) + 2⁻¹ * 2 := by ring
      _ = _ := by rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- Example 5.3: the information rates of `μ = ½ (ν_p + ν_q)` (`0 < p, q < 1`) under the shift
are both `(H(p) + H(q))/2`. Blueprint node `meas:examples`. -/
theorem informationRate_bernoulliMixture (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hq1 : q < 1) :
    informationRate (bernoulliMixture p hp q hq) shiftMap =
      ((binEntropyBits p + binEntropyBits q) / 2, (binEntropyBits p + binEntropyBits q) / 2) := by
  set m := (binEntropyBits p + binEntropyBits q) / 2
  have hm : m ≠ ⊤ := ENNReal.div_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.ofReal_ne_top⟩) (by norm_num)
  have hT : Tendsto (fun n : ℕ ↦ (∫⁻ x, infoBits (bernoulliMixture p hp q hq
      (PiNat.cylinder x n)) ∂bernoulliMixture p hp q hq) / n) atTop (𝓝 m) := by
    have hup : Tendsto (fun n : ℕ ↦ m + (n : ℝ≥0∞)⁻¹) atTop (𝓝 m) := by
      simpa using tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
      rw [ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n)), mul_comm]
      exact (lintegral_infoBits_bernoulliMixture_cylinder p hp q hq hp0 hp1 hq0 hq1 n).1
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
      refine (ENNReal.div_le_div_right
        (lintegral_infoBits_bernoulliMixture_cylinder p hp q hq hp0 hp1 hq0 hq1 n).2 _).trans_eq ?_
      rw [ENNReal.add_div, mul_comm, ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n),
        one_div]
  rw [informationRate_shiftMap (by norm_num) (by norm_num) hd_cantor, hT.liminf_eq,
    hT.limsup_eq]

end mixture

end Kolmogorov.PointToSet
