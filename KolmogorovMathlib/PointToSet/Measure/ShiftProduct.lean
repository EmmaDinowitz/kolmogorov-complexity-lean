/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Shift
import KolmogorovMathlib.PointToSet.Measure.EntropyLaw
import KolmogorovMathlib.PointToSet.Measure.InformationRate
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Non-stationary product measures on the shift (Example 5.1)

On Cantor space `ℕ → Bool` with the shift and the Cantor metric, let
`μ_β = ⨂_i Bernoulli(β_i)` (`productBernoulli β`) for biases `β_i ∈ [δ, 1 - δ]`, `δ > 0`
(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*,
Example 5.1). Entropies are in bits: `H(p) = Real.binEntropy p / log 2` (`bitEntropy`).

* `productBernoulli_cylinder`, `infoBits_productBernoulli_cylinder`: `μ_β[x↾n]` is the product
  of the symbol masses, so `-log₂ μ_β[x↾n] = ∑_{i<n} Y_i(x)` with `Y_i` independent, bounded,
  of mean `H(β_i)` (`integral_symbolInfo`).
* `lintegral_infoBits_productBernoulli`, `informationRate_productBernoulli`: the mean information
  is exactly `∑_{i<n} H(β_i)`, so the information rates are `(a̲, ā)`, the lower and upper limits
  of the Cesàro averages of `H(β_i)` (`lowerEntropyAverage`, `upperEntropyAverage`).
* `ae_tendsto_avg_of_iIndepFun_bounded`: the strong law of large numbers for independent,
  uniformly bounded, centred (not necessarily identically distributed) real variables, proved by
  the fourth-moment bound `E[S_n⁴] ≤ 3 n² C⁴` and Borel–Cantelli.
* `ae_localEntropy_productBernoulli`, `entropyLaw_productBernoulli`: hence `Φ_μ = (a̲, ā)` almost
  everywhere, `Λ_μ = δ_{(a̲, ā)}`, and the Feng–Huang entropies and essential bounds are `a̲`, `ā`.
* The block pattern of the concrete case (Example 5.1, end):
  `blockPattern i ↔ i ∈ ⋃_j [4^j, 2·4^j)`;
  `liminf_blockAverage`, `limsup_blockAverage`: the density of the pattern oscillates between
  `1/3` and `2/3`; `liminf_limsup_ofReal_of_blockFrequency`: lower and upper limits of sequences
  that are affine in that density.

The concrete biases with `a̲ = (1 + 2a)/3 < ā = (2 + a)/3` and the anti-phase mixtures of
Examples 5.2 and 6.8 are in `Measure/ShiftAntiPhase.lean`.

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal unitInterval

attribute [local instance] cantorMetricSpace

/-! ### The strong law for independent bounded variables -/

section strongLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A measurable bounded function is integrable for a probability measure. -/
private lemma integrable_of_abs_le {f : Ω → ℝ} (hf : Measurable f) {K : ℝ}
    (hK : ∀ ω, |f ω| ≤ K) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable K (.of_forall fun ω ↦ by simpa using hK ω)

/-- Products of powers of two bounded measurable functions are integrable. -/
private lemma integrable_pow_mul_pow {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {K L : ℝ} (hK : ∀ ω, |f ω| ≤ K) (hL : ∀ ω, |g ω| ≤ L) (k m : ℕ) :
    Integrable (fun ω ↦ f ω ^ k * g ω ^ m) P :=
  integrable_of_abs_le ((hf.pow_const k).mul (hg.pow_const m)) (K := K ^ k * L ^ m)
    fun ω ↦ by
      rw [abs_mul, abs_pow, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hK ω) k)
        (pow_le_pow_left₀ (abs_nonneg _) (hL ω) m) (by positivity)
        (pow_nonneg ((abs_nonneg _).trans (hK ω)) k)

/-- The moment bounds: for independent centred variables bounded by `C`, the partial sums
satisfy `E[S_n] = 0`, `E[S_n²] ≤ n C²` and `E[S_n⁴] ≤ 3 n² C⁴`. By induction, with
`S_{n+1} = S_n + Z_n`, `Z_n` independent of `S_n`, and the binomial expansion. -/
private lemma moments_partialSum {Z : ℕ → Ω → ℝ} (hind : iIndepFun Z P)
    (hmeas : ∀ i, Measurable (Z i)) {C : ℝ} (hC : ∀ i ω, |Z i ω| ≤ C)
    (hmean : ∀ i, ∫ ω, Z i ω ∂P = 0) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Z i ω) ∂P = 0 ∧
      ∫ ω, (∑ i ∈ Finset.range n, Z i ω) ^ 2 ∂P ≤ n * C ^ 2 ∧
      ∫ ω, (∑ i ∈ Finset.range n, Z i ω) ^ 4 ∂P ≤ 3 * n ^ 2 * C ^ 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2, h4⟩ := ih
    set S : Ω → ℝ := fun ω ↦ ∑ i ∈ Finset.range n, Z i ω with hS
    have hSm : Measurable S := Finset.measurable_sum _ fun i _ ↦ hmeas i
    have hSb : ∀ ω, |S ω| ≤ n * C := fun ω ↦ by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.range n) ↦ hC i ω
    have hind' : IndepFun S (Z n) P := by
      have := hind.indepFun_finsetSum_of_notMem hmeas (s := Finset.range n) (i := n)
        (by simp)
      convert this using 1
      ext ω; simp [hS]
    have hprod : ∀ k m : ℕ, ∫ ω, S ω ^ k * Z n ω ^ m ∂P =
        (∫ ω, S ω ^ k ∂P) * ∫ ω, Z n ω ^ m ∂P := fun k m ↦
      (hind'.comp (measurable_id.pow_const k)
        (measurable_id.pow_const m)).integral_fun_mul_eq_mul_integral
        ((hSm.pow_const k).aestronglyMeasurable) ((hmeas n).pow_const m).aestronglyMeasurable
    have hI : ∀ k m : ℕ, Integrable (fun ω ↦ S ω ^ k * Z n ω ^ m) P := fun k m ↦
      integrable_pow_mul_pow hSm (hmeas n) hSb (hC n) k m
    have hZ2 : ∫ ω, Z n ω ^ 2 ∂P ≤ C ^ 2 := by
      have : ∀ ω, Z n ω ^ 2 ≤ C ^ 2 := fun ω ↦ by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC n ω) 2
      refine (integral_mono (by simpa using hI 0 2) (integrable_const (C ^ 2)) this).trans ?_
      simp
    have hZ4 : ∫ ω, Z n ω ^ 4 ∂P ≤ C ^ 4 := by
      have : ∀ ω, Z n ω ^ 4 ≤ C ^ 4 := fun ω ↦ by
        rw [show Z n ω ^ 4 = |Z n ω| ^ 4 by rw [pow_abs, abs_of_nonneg (by positivity)]]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC n ω) 4
      refine (integral_mono (by simpa using hI 0 4) (integrable_const (C ^ 4)) this).trans ?_
      simp
    have hsum : ∀ ω, ∑ i ∈ Finset.range (n + 1), Z i ω = S ω + Z n ω := fun ω ↦
      Finset.sum_range_succ _ _
    simp only [hsum]
    replace h2 : ∫ ω, S ω ^ 2 ∂P ≤ n * C ^ 2 := h2
    replace h4 : ∫ ω, S ω ^ 4 ∂P ≤ 3 * n ^ 2 * C ^ 4 := h4
    have hexp : ∀ N : ℕ, ∫ ω, (S ω + Z n ω) ^ N ∂P = ∑ k ∈ Finset.range (N + 1),
        (∫ ω, S ω ^ k ∂P) * (∫ ω, Z n ω ^ (N - k) ∂P) * (N.choose k : ℝ) := by
      intro N
      simp_rw [add_pow]
      rw [integral_finsetSum _ fun k _ ↦ (hI k (N - k)).mul_const _]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [integral_mul_const, hprod]
    have hZ2' : 0 ≤ ∫ ω, Z n ω ^ 2 ∂P := integral_nonneg fun ω ↦ sq_nonneg _
    have hm1 := hmean n
    have e2 : ∫ ω, (S ω + Z n ω) ^ 2 ∂P = ∫ ω, Z n ω ^ 2 ∂P + ∫ ω, S ω ^ 2 ∂P := by
      rw [hexp]
      simp [Finset.sum_range_succ, h1, hm1]
    have e4 : ∫ ω, (S ω + Z n ω) ^ 4 ∂P = ∫ ω, Z n ω ^ 4 ∂P +
        6 * ((∫ ω, S ω ^ 2 ∂P) * ∫ ω, Z n ω ^ 2 ∂P) + ∫ ω, S ω ^ 4 ∂P := by
      rw [hexp]
      simp [Finset.sum_range_succ, h1, hm1, Nat.choose]
      ring
    have hC4 : 0 ≤ C ^ 4 := by positivity
    have hSZ : (∫ ω, S ω ^ 2 ∂P) * ∫ ω, Z n ω ^ 2 ∂P ≤ n * C ^ 4 := by
      calc (∫ ω, S ω ^ 2 ∂P) * ∫ ω, Z n ω ^ 2 ∂P ≤ (n * C ^ 2) * C ^ 2 :=
            mul_le_mul h2 hZ2 hZ2' (by positivity)
        _ = n * C ^ 4 := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [show (fun ω ↦ S ω + Z n ω) = fun ω ↦ (S ω + Z n ω) ^ 1 by simp, hexp]
      simp [Finset.sum_range_succ, h1, hm1]
    · rw [e2]
      push_cast
      linarith
    · rw [e4]
      push_cast
      nlinarith

/-- The strong law of large numbers for independent, uniformly bounded, centred real random
variables (not necessarily identically distributed): `(1/n) ∑_{i<n} Z_i → 0` almost surely.
Proof: Markov's inequality for `S_n⁴` and the bound `E[S_n⁴] ≤ 3 n² C⁴` give
`P(|S_n| ≥ n ε) ≤ 3 C⁴ / (ε⁴ n²)`, which is summable, and Borel–Cantelli. This is the input
of Example 5.1 that Mathlib does not provide (Mathlib's `strong_law_ae` is the i.i.d. case).
Blueprint node `meas:examples`. -/
theorem ae_tendsto_avg_of_iIndepFun_bounded {Z : ℕ → Ω → ℝ} (hind : iIndepFun Z P)
    (hmeas : ∀ i, Measurable (Z i)) {C : ℝ} (hC : ∀ i ω, |Z i ω| ≤ C)
    (hmean : ∀ i, ∫ ω, Z i ω ∂P = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Z i ω) / n) atTop (𝓝 0) := by
  set S : ℕ → Ω → ℝ := fun n ω ↦ ∑ i ∈ Finset.range n, Z i ω with hS
  have hSm : ∀ n, Measurable (S n) := fun n ↦ Finset.measurable_sum _ fun i _ ↦ hmeas i
  have hSb : ∀ n ω, |S n ω| ≤ n * C := fun n ω ↦ by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.range n) ↦ hC i ω
  have hP : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, P {ω | ε * (n + 1) ≤ |S (n + 1) ω|} ≤
      ENNReal.ofReal (3 * C ^ 4 / ε ^ 4 / ((n : ℝ) + 1) ^ 2) := by
    intro ε hε n
    have hset : {ω | ε * (n + 1) ≤ |S (n + 1) ω|} =
        {ω | (ε * (n + 1)) ^ 4 ≤ S (n + 1) ω ^ 4} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [show S (n + 1) ω ^ 4 = |S (n + 1) ω| ^ 4 from (Even.pow_abs ⟨2, rfl⟩ _).symm,
        pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) (by norm_num)]
    have hint : Integrable (fun ω ↦ S (n + 1) ω ^ 4) P := by
      simpa using integrable_pow_mul_pow (P := P) (hSm (n + 1)) measurable_const
        (hSb (n + 1)) (fun _ ↦ le_refl |(1 : ℝ)|) 4 0
    have hM := mul_meas_ge_le_integral_of_nonneg (.of_forall fun ω ↦ by positivity) hint
      ((ε * (n + 1)) ^ 4)
    have h4 := (moments_partialSum hind hmeas hC hmean (n + 1)).2.2
    rw [hset, ← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    set q := P.real {ω | (ε * (n + 1)) ^ 4 ≤ S (n + 1) ω ^ 4}
    rw [div_div, le_div_iff₀ (by positivity)]
    push_cast at h4
    have key : ((n : ℝ) + 1) ^ 2 * (q * (ε ^ 4 * ((n : ℝ) + 1) ^ 2)) ≤
        ((n : ℝ) + 1) ^ 2 * (3 * C ^ 4) := by
      calc ((n : ℝ) + 1) ^ 2 * (q * (ε ^ 4 * ((n : ℝ) + 1) ^ 2))
          = (ε * (n + 1)) ^ 4 * q := by ring
        _ ≤ ∫ ω, S (n + 1) ω ^ 4 ∂P := hM
        _ ≤ 3 * ((n : ℝ) + 1) ^ 2 * C ^ 4 := h4
        _ = ((n : ℝ) + 1) ^ 2 * (3 * C ^ 4) := by ring
    exact le_of_mul_le_mul_left key (by positivity)
  have hsum : ∀ K : ℝ, 0 ≤ K → ∑' n : ℕ, ENNReal.ofReal (K / ((n : ℝ) + 1) ^ 2) ≠ ∞ := by
    intro K hK
    have hs : Summable fun n : ℕ ↦ K / ((n : ℝ) + 1) ^ 2 := by
      have := ((summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.2 one_lt_two)).mul_left K
      simpa [div_eq_mul_inv] using this
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hs]
    exact ENNReal.ofReal_ne_top
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n in atTop,
      |S (n + 1) ω| < 1 / ((k : ℝ) + 1) * (n + 1) := by
    refine ae_all_iff.2 fun k ↦ ?_
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have := ae_eventually_notMem (ne_top_of_le_ne_top (hsum _ (by positivity))
      (ENNReal.tsum_le_tsum (hP _ hε)))
    filter_upwards [this] with ω hω
    exact hω.mono fun n hn ↦ by simpa [not_le] using hn
  filter_upwards [hall] with ω hω
  rw [← tendsto_add_atTop_iff_nat 1]
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.dist_eq, sub_zero]
  push_cast
  rw [abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
  calc |S (n + 1) ω| < 1 / ((k : ℝ) + 1) * (n + 1) := hn
    _ ≤ ε * (n + 1) := by gcongr

end strongLaw

/-! ### Limits of `ofReal` sequences -/

/-- If `u_n - v_n → 0` then `ofReal u_n` and `ofReal v_n` have the same lower and upper limits
in `ℝ≥0∞`. -/
theorem liminf_limsup_ofReal_congr {u v : ℕ → ℝ}
    (h : Tendsto (fun n ↦ u n - v n) atTop (𝓝 0)) :
    liminf (fun n ↦ ENNReal.ofReal (u n)) atTop = liminf (fun n ↦ ENNReal.ofReal (v n)) atTop ∧
      limsup (fun n ↦ ENNReal.ofReal (u n)) atTop =
        limsup (fun n ↦ ENNReal.ofReal (v n)) atTop := by
  have hd : Tendsto (fun n ↦ ENNReal.ofReal |u n - v n|) atTop (𝓝 0) := by
    have h' : Tendsto (fun n ↦ |u n - v n|) atTop (𝓝 0) := by
      have := (continuous_abs.tendsto (0 : ℝ)).comp h
      rwa [abs_zero] at this
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h'
    rwa [ENNReal.ofReal_zero] at this
  have hd' : Tendsto (fun n ↦ ENNReal.ofReal |v n - u n|) atTop (𝓝 0) := by
    simpa [abs_sub_comm] using hd
  have h1 : ∀ a b : ℝ, ENNReal.ofReal a ≤ ENNReal.ofReal b + ENNReal.ofReal |a - b| :=
    fun a b ↦ (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (a - b)])).trans
      ENNReal.ofReal_add_le
  exact ⟨le_antisymm (liminf_le_liminf_of_le_add_tendsto_zero (.of_forall fun n ↦ h1 _ _) hd)
      (liminf_le_liminf_of_le_add_tendsto_zero (.of_forall fun n ↦ h1 _ _) hd'),
    le_antisymm (limsup_le_limsup_of_le_add_tendsto_zero (.of_forall fun n ↦ h1 _ _) hd)
      (limsup_le_limsup_of_le_add_tendsto_zero (.of_forall fun n ↦ h1 _ _) hd')⟩

/-- `ofReal S / n = ofReal (S / n)` for `n ≥ 1`. -/
lemma ofReal_div_natCast {S : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal S / n = ENNReal.ofReal (S / n) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn)]
  simp

/-! ### The block pattern `⋃_j [4^j, 2·4^j)` -/

/-- The block pattern of Example 5.1: `i ∈ ⋃_{j ≥ 0} [4^j, 2·4^j)`.
Blueprint node `meas:examples`. -/
def blockPattern (i : ℕ) : Prop := ∃ j, 4 ^ j ≤ i ∧ i < 2 * 4 ^ j

instance : DecidablePred blockPattern := fun i ↦
  decidable_of_iff (∃ j < i + 1, 4 ^ j ≤ i ∧ i < 2 * 4 ^ j)
    ⟨fun ⟨j, _, h⟩ ↦ ⟨j, h⟩, fun ⟨j, h⟩ ↦
      ⟨j, by have := Nat.lt_pow_self (n := j) (by norm_num : 1 < 4); omega, h⟩⟩

/-- The number `#{i < n : i ∈ ⋃_j [4^j, 2·4^j)}` of pattern positions below `n`. -/
def blockCount (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, if blockPattern i then 1 else 0

/-- The density `(1/n) #{i < n : i ∈ ⋃_j [4^j, 2·4^j)}` of the block pattern.
Blueprint node `meas:examples`. -/
noncomputable def blockFrequency (n : ℕ) : ℝ := (blockCount n : ℝ) / n

/-- The positions in `[4^j, 2·4^j)` belong to the pattern. -/
lemma blockPattern_of_mem {i j : ℕ} (h1 : 4 ^ j ≤ i) (h2 : i < 2 * 4 ^ j) : blockPattern i :=
  ⟨j, h1, h2⟩

/-- The positions in `[2·4^j, 4^{j+1})` do not belong to the pattern. -/
lemma not_blockPattern_of_mem {i j : ℕ} (h1 : 2 * 4 ^ j ≤ i) (h2 : i < 4 ^ (j + 1)) :
    ¬ blockPattern i := by
  rintro ⟨k, hk1, hk2⟩
  rcases le_or_gt k j with hkj | hkj
  · have := Nat.pow_le_pow_right (by norm_num : 0 < 4) hkj
    omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < 4) (Nat.succ_le_of_lt hkj)
    omega

/-- One step of the counting function. -/
lemma blockCount_succ (n : ℕ) :
    blockCount (n + 1) = blockCount n + if blockPattern n then 1 else 0 :=
  Finset.sum_range_succ _ _

/-- On a block the counting function increases by one at each step. -/
lemma blockCount_block (j m : ℕ) (hm : m ≤ 4 ^ j) :
    blockCount (4 ^ j + m) = blockCount (4 ^ j) + m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hb : blockPattern (4 ^ j + m) := blockPattern_of_mem (j := j) (by omega) (by omega)
    rw [← add_assoc, blockCount_succ, ih (by omega)]
    simp [hb, add_assoc]

/-- On a gap the counting function is constant. -/
lemma blockCount_gap (j m : ℕ) (hm : m ≤ 2 * 4 ^ j) :
    blockCount (2 * 4 ^ j + m) = blockCount (2 * 4 ^ j) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hb : ¬ blockPattern (2 * 4 ^ j + m) :=
      not_blockPattern_of_mem (j := j) (by omega) (by rw [pow_succ]; omega)
    rw [← add_assoc, blockCount_succ, ih (by omega)]
    simp [hb]

/-- At the end of the `j`-th block the count has grown by `4^j`. -/
lemma blockCount_two_mul (j : ℕ) : blockCount (2 * 4 ^ j) = blockCount (4 ^ j) + 4 ^ j := by
  rw [two_mul, blockCount_block j _ le_rfl]

/-- `#{i < 4^j : i in the pattern} = (4^j - 1)/3`. -/
lemma blockCount_pow (j : ℕ) : 3 * blockCount (4 ^ j) + 1 = 4 ^ j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h := blockCount_gap j (2 * 4 ^ j) le_rfl
    rw [show 2 * 4 ^ j + 2 * 4 ^ j = 4 ^ (j + 1) by rw [pow_succ]; ring,
      blockCount_two_mul] at h
    rw [h, pow_succ]
    omega

/-- For `n ≥ 1`, `n - 1 ≤ 3 #{i < n : pattern} ≤ 2 n`. -/
lemma blockCount_bounds {n : ℕ} (hn : 1 ≤ n) :
    n ≤ 3 * blockCount n + 1 ∧ 3 * blockCount n ≤ 2 * n := by
  obtain ⟨j, h1, h2⟩ : ∃ j, 4 ^ j ≤ n ∧ n < 4 ^ (j + 1) :=
    ⟨Nat.log 4 n, Nat.pow_log_le_self 4 (by omega), Nat.lt_pow_succ_log_self (by norm_num) n⟩
  have hc := blockCount_pow j
  rw [pow_succ] at h2
  rcases le_or_gt n (2 * 4 ^ j) with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = 4 ^ j + m := ⟨n - 4 ^ j, by omega⟩
    rw [blockCount_block j m (by omega)]
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * 4 ^ j + m := ⟨n - 2 * 4 ^ j, by omega⟩
    rw [blockCount_gap j m (by omega), blockCount_two_mul]
    omega

/-- The density of the pattern is nonnegative. -/
lemma blockFrequency_nonneg (n : ℕ) : 0 ≤ blockFrequency n := by
  unfold blockFrequency; positivity

/-- For `n ≥ 1`, `1/3 - 1/(3n) ≤ blockFrequency n ≤ 2/3`. -/
lemma blockFrequency_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / 3 - 1 / (3 * n) ≤ blockFrequency n ∧ blockFrequency n ≤ 2 / 3 := by
  obtain ⟨h1, h2⟩ := blockCount_bounds hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1' : (n : ℝ) ≤ 3 * blockCount n + 1 := by exact_mod_cast h1
  have h2' : 3 * (blockCount n : ℝ) ≤ 2 * n := by exact_mod_cast h2
  unfold blockFrequency
  constructor
  · rw [le_div_iff₀ hn']
    have : (1 / 3 - 1 / (3 * (n : ℝ))) * n = n / 3 - 1 / 3 := by field_simp
    linarith
  · rw [div_le_iff₀ hn']; linarith

/-- The density of the pattern is at most `2/3`. -/
lemma blockFrequency_le (n : ℕ) : blockFrequency n ≤ 2 / 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [blockFrequency]
  · exact (blockFrequency_bounds hn).2

/-- At the start of a block, `blockFrequency (4^j) = 1/3 - 1/(3·4^j)`. -/
lemma blockFrequency_pow (j : ℕ) : blockFrequency (4 ^ j) = 1 / 3 - 1 / (3 * 4 ^ j) := by
  have hc : 3 * (blockCount (4 ^ j) : ℝ) + 1 = 4 ^ j := by exact_mod_cast blockCount_pow j
  unfold blockFrequency
  have h4 : (0 : ℝ) < 4 ^ j := by positivity
  push_cast
  field_simp
  linarith

/-- At the end of a block, `blockFrequency (2·4^j) = 2/3 - 1/(6·4^j)`. -/
lemma blockFrequency_two_mul_pow (j : ℕ) :
    blockFrequency (2 * 4 ^ j) = 2 / 3 - 1 / (6 * 4 ^ j) := by
  have hc : 3 * (blockCount (4 ^ j) : ℝ) + 1 = 4 ^ j := by exact_mod_cast blockCount_pow j
  unfold blockFrequency
  rw [blockCount_two_mul]
  have h4 : (0 : ℝ) < 4 ^ j := by positivity
  push_cast
  field_simp
  linarith

/-- `1/(c·4^j) → 0`. -/
private lemma tendsto_inv_pow_four (c : ℝ) :
    Tendsto (fun j : ℕ ↦ 1 / (c * 4 ^ j)) atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num)).const_mul c⁻¹
  rw [mul_zero] at this
  refine this.congr fun j ↦ ?_
  rw [one_div_pow, one_div, one_div, mul_inv]

/-- Along the block starts the density tends to `1/3`. -/
lemma tendsto_blockFrequency_pow :
    Tendsto (fun j ↦ blockFrequency (4 ^ j)) atTop (𝓝 (1 / 3)) := by
  simp only [blockFrequency_pow]
  simpa using (tendsto_inv_pow_four 3).const_sub (1 / 3 : ℝ)

/-- Along the block ends the density tends to `2/3`. -/
lemma tendsto_blockFrequency_two_mul_pow :
    Tendsto (fun j ↦ blockFrequency (2 * 4 ^ j)) atTop (𝓝 (2 / 3)) := by
  simp only [blockFrequency_two_mul_pow]
  simpa using (tendsto_inv_pow_four 6).const_sub (2 / 3 : ℝ)

/-- `4^j → ∞`. -/
private lemma tendsto_four_pow : Tendsto (fun j : ℕ ↦ 4 ^ j) atTop atTop :=
  tendsto_atTop_mono (fun _ ↦ (Nat.lt_pow_self (by norm_num)).le) tendsto_id

/-- `2·4^j → ∞`. -/
private lemma tendsto_two_mul_four_pow : Tendsto (fun j : ℕ ↦ 2 * 4 ^ j) atTop atTop :=
  tendsto_four_pow.const_mul_atTop' (by norm_num)

/-- Example 5.1 (concrete case): the density `(1/n) #{i < n : i ∈ ⋃_j [4^j, 2·4^j)}` has lower
limit `1/3` (attained along `n = 4^{j+1}`). This confirms the value claimed in the paper.
Blueprint node `meas:examples`. -/
theorem liminf_blockAverage : liminf blockFrequency atTop = 1 / 3 := by
  have hb : IsBoundedUnder (· ≥ ·) atTop blockFrequency :=
    isBoundedUnder_of ⟨0, blockFrequency_nonneg⟩
  have hb' : IsBoundedUnder (· ≤ ·) atTop blockFrequency :=
    isBoundedUnder_of ⟨2 / 3, blockFrequency_le⟩
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε ↦ ?_)
    (le_of_forall_pos_lt_add fun ε hε ↦ ?_)
  · have hev : ∀ᶠ j in atTop, blockFrequency (4 ^ j) < 1 / 3 + ε / 2 :=
      tendsto_blockFrequency_pow.eventually (gt_mem_nhds (by linarith))
    have hfr := tendsto_four_pow.frequently
      (p := fun n ↦ blockFrequency n ≤ 1 / 3 + ε / 2) (hev.mono fun _ h ↦ h.le).frequently
    exact (liminf_le_of_frequently_le hfr hb).trans_lt (by linarith)
  · have hev : ∀ᶠ n : ℕ in atTop, 1 / 3 - ε / 2 ≤ blockFrequency n := by
      have h0 : ∀ᶠ n : ℕ in atTop, (1 / 3 : ℝ) / n < ε / 2 :=
        (tendsto_const_div_atTop_nhds_zero_nat (1 / 3 : ℝ)).eventually
          (gt_mem_nhds (by linarith))
      filter_upwards [h0, eventually_ge_atTop 1] with n hn hn1
      have := (blockFrequency_bounds hn1).1
      rw [div_div] at hn
      linarith
    have := le_liminf_of_le hb'.isCoboundedUnder_ge hev
    linarith

/-- Example 5.1 (concrete case): the density `(1/n) #{i < n : i ∈ ⋃_j [4^j, 2·4^j)}` has upper
limit `2/3` (attained along `n = 2·4^j`). This confirms the value claimed in the paper.
Blueprint node `meas:examples`. -/
theorem limsup_blockAverage : limsup blockFrequency atTop = 2 / 3 := by
  have hb : IsBoundedUnder (· ≥ ·) atTop blockFrequency :=
    isBoundedUnder_of ⟨0, blockFrequency_nonneg⟩
  have hb' : IsBoundedUnder (· ≤ ·) atTop blockFrequency :=
    isBoundedUnder_of ⟨2 / 3, blockFrequency_le⟩
  refine le_antisymm (limsup_le_of_le hb.isCoboundedUnder_le
    (.of_forall blockFrequency_le)) (le_of_forall_pos_lt_add fun ε hε ↦ ?_)
  have hev : ∀ᶠ j in atTop, 2 / 3 - ε / 2 < blockFrequency (2 * 4 ^ j) :=
    tendsto_blockFrequency_two_mul_pow.eventually (lt_mem_nhds (by linarith))
  have hfr := tendsto_two_mul_four_pow.frequently
    (p := fun n ↦ 2 / 3 - ε / 2 ≤ blockFrequency n) (hev.mono fun _ h ↦ h.le).frequently
  have := le_limsup_of_frequently_le hfr hb'
  linarith

/-- If `u_n` is within `c/n` of `A + B·f_n`, with `f_n` the density of the block pattern, then
`u_n ≥ L - d/n` and `u_n ≤ U + d/n`, with `L, U = A + B/2 ∓ |B|/6`, `d = |B|/3 + c`. -/
private lemma bounds_of_blockFrequency {u : ℕ → ℝ} {A B c : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → |u n - (A + B * blockFrequency n)| ≤ c / n) {n : ℕ} (hn : 1 ≤ n) :
    A + B / 2 - |B| / 6 - (|B| / 3 + c) / n ≤ u n ∧
      u n ≤ A + B / 2 + |B| / 6 + (|B| / 3 + c) / n := by
  obtain ⟨f1, f2⟩ := blockFrequency_bounds hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hu1, hu2⟩ := abs_le.1 (h n hn)
  have e1 : B * (1 / 3 - 1 / (3 * (n : ℝ))) = B / 3 - B / 3 * (1 / n) := by field_simp
  have e2 : (|B| / 3 + c) / n = |B| / 3 * (1 / n) + c / n := by ring
  have hpos : 0 ≤ |B| / 3 * (1 / n) := by positivity
  rw [e2]
  rcases le_or_gt 0 B with hB | hB
  · have hab : |B| = B := abs_of_nonneg hB
    have g1 : B * (1 / 3 - 1 / (3 * n)) ≤ B * blockFrequency n :=
      mul_le_mul_of_nonneg_left f1 hB
    have g2 : B * blockFrequency n ≤ B * (2 / 3) := mul_le_mul_of_nonneg_left f2 hB
    rw [hab] at hpos ⊢
    constructor <;> linarith
  · have hab : |B| = -B := abs_of_neg hB
    have g1 : B * blockFrequency n ≤ B * (1 / 3 - 1 / (3 * n)) :=
      mul_le_mul_of_nonpos_left f1 hB.le
    have g2 : B * (2 / 3) ≤ B * blockFrequency n := mul_le_mul_of_nonpos_left f2 hB.le
    rw [hab] at hpos ⊢
    constructor <;> linarith

/-- Along a subsequence `φ → ∞` on which the density converges to `f₀`, `u ∘ φ → A + B f₀`. -/
private lemma tendsto_comp_of_blockFrequency {u : ℕ → ℝ} {A B c : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → |u n - (A + B * blockFrequency n)| ≤ c / n) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) {f₀ : ℝ}
    (hf : Tendsto (fun j ↦ blockFrequency (φ j)) atTop (𝓝 f₀)) :
    Tendsto (fun j ↦ u (φ j)) atTop (𝓝 (A + B * f₀)) := by
  have h0 : Tendsto (fun j ↦ u (φ j) - (A + B * blockFrequency (φ j))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_div_atTop_nhds_zero_nat c).comp hφ)
    filter_upwards [hφ.eventually (eventually_ge_atTop 1)] with j hj
    exact h _ hj
  have := h0.add ((hf.const_mul B).const_add A)
  simpa using this

/-- The rate computation behind Examples 5.1, 5.2 and 6.8: if `u_n` is within `c/n` of an affine
function `A + B·f_n` of the density `f_n` of the block pattern, then `ofReal u_n` has lower limit
`A + B/2 - |B|/6` and upper limit `A + B/2 + |B|/6` (that is, `A + B/3` and `A + 2B/3` in some
order, since `f_n` oscillates between `1/3` and `2/3`). Blueprint node `meas:examples`. -/
theorem liminf_limsup_ofReal_of_blockFrequency {u : ℕ → ℝ} {A B c : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → |u n - (A + B * blockFrequency n)| ≤ c / n) :
    liminf (fun n ↦ ENNReal.ofReal (u n)) atTop = ENNReal.ofReal (A + B / 2 - |B| / 6) ∧
      limsup (fun n ↦ ENNReal.ofReal (u n)) atTop = ENNReal.ofReal (A + B / 2 + |B| / 6) := by
  set d := |B| / 3 + c
  have hd : Tendsto (fun n : ℕ ↦ d / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat d
  have hL : ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      Tendsto (fun j ↦ u (φ j)) atTop (𝓝 (A + B / 2 - |B| / 6)) := by
    rcases le_or_gt 0 B with hB | hB
    · refine ⟨_, tendsto_four_pow, ?_⟩
      convert tendsto_comp_of_blockFrequency h tendsto_four_pow tendsto_blockFrequency_pow
        using 2
      rw [abs_of_nonneg hB]; ring
    · refine ⟨_, tendsto_two_mul_four_pow, ?_⟩
      convert tendsto_comp_of_blockFrequency h tendsto_two_mul_four_pow
        tendsto_blockFrequency_two_mul_pow using 2
      rw [abs_of_neg hB]; ring
  have hU : ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      Tendsto (fun j ↦ u (φ j)) atTop (𝓝 (A + B / 2 + |B| / 6)) := by
    rcases le_or_gt 0 B with hB | hB
    · refine ⟨_, tendsto_two_mul_four_pow, ?_⟩
      convert tendsto_comp_of_blockFrequency h tendsto_two_mul_four_pow
        tendsto_blockFrequency_two_mul_pow using 2
      rw [abs_of_nonneg hB]; ring
    · refine ⟨_, tendsto_four_pow, ?_⟩
      convert tendsto_comp_of_blockFrequency h tendsto_four_pow tendsto_blockFrequency_pow
        using 2
      rw [abs_of_neg hB]; ring
  obtain ⟨φ, hφ, hφL⟩ := hL
  obtain ⟨ψ, hψ, hψU⟩ := hU
  have hφL' := (ENNReal.continuous_ofReal.tendsto _).comp hφL
  have hψU' := (ENNReal.continuous_ofReal.tendsto _).comp hψU
  constructor
  · refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun y hy ↦ ?_) ?_
    · have hev : ∀ᶠ j in atTop, ENNReal.ofReal (u (φ j)) < y :=
        hφL'.eventually (gt_mem_nhds hy)
      exact liminf_le_of_frequently_le' (hφ.frequently (p := fun n ↦ ENNReal.ofReal (u n) ≤ y)
        (hev.mono fun _ h ↦ h.le).frequently)
    · have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (A + B / 2 - |B| / 6 - d / n)) atTop
          (𝓝 (ENNReal.ofReal (A + B / 2 - |B| / 6))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (by simpa using hd.const_sub _)
      rw [← ht.liminf_eq]
      exact liminf_le_liminf ((eventually_ge_atTop 1).mono fun n hn ↦
        ENNReal.ofReal_le_ofReal (bounds_of_blockFrequency h hn).1)
  · refine le_antisymm ?_ (le_of_forall_lt_imp_le_of_dense fun y hy ↦ ?_)
    · have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (A + B / 2 + |B| / 6 + d / n)) atTop
          (𝓝 (ENNReal.ofReal (A + B / 2 + |B| / 6))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (by simpa using hd.const_add _)
      rw [← ht.limsup_eq]
      exact limsup_le_limsup ((eventually_ge_atTop 1).mono fun n hn ↦
        ENNReal.ofReal_le_ofReal (bounds_of_blockFrequency h hn).2)
    · have hev : ∀ᶠ j in atTop, y < ENNReal.ofReal (u (ψ j)) :=
        hψU'.eventually (lt_mem_nhds hy)
      exact le_limsup_of_frequently_le' (hψ.frequently (p := fun n ↦ y ≤ ENNReal.ofReal (u n))
        (hev.mono fun _ h ↦ h.le).frequently)

/-! ### Non-stationary product measures (Example 5.1) -/

/-- The binary entropy in bits, `H(p) = -p log₂ p - (1 - p) log₂ (1 - p)`. -/
noncomputable def bitEntropy (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- The binary entropy in bits is nonnegative on `[0, 1]`. -/
lemma bitEntropy_nonneg (q : I) : 0 ≤ bitEntropy q :=
  div_nonneg (Real.binEntropy_nonneg q.2.1 q.2.2) (Real.log_nonneg one_le_two)

/-- The binary entropy in bits is at most `1`. -/
lemma bitEntropy_le_one (q : ℝ) : bitEntropy q ≤ 1 :=
  div_le_one_of_le₀ Real.binEntropy_le_log_two (Real.log_nonneg one_le_two)

/-- The product measure `μ_β = ⨂_i Bernoulli(β_i)` on Cantor space (`β_i` is the probability of
the symbol `true`). Blueprint node `meas:examples`. -/
noncomputable def productBernoulli (β : ℕ → I) : Measure (ℕ → Bool) :=
  Measure.infinitePi fun i ↦ ProbabilityTheory.bernoulliMeasure true false (β i)

instance (β : ℕ → I) : IsProbabilityMeasure (productBernoulli β) := by
  unfold productBernoulli; infer_instance

/-- The mass `q` of `true` and `1 - q` of `false` under `Bernoulli(q)`. -/
noncomputable def bitMass (q : I) (b : Bool) : ℝ := if b then (q : ℝ) else 1 - q

/-- Symbol masses are nonnegative. -/
lemma bitMass_nonneg (q : I) (b : Bool) : 0 ≤ bitMass q b := by
  unfold bitMass; split_ifs
  · exact q.2.1
  · exact sub_nonneg.2 q.2.2

/-- Symbol masses are at most `1`. -/
lemma bitMass_le_one (q : I) (b : Bool) : bitMass q b ≤ 1 := by
  unfold bitMass; split_ifs
  · exact q.2.2
  · linarith [q.2.1]

/-- Symbol masses are positive for a bias in `(0, 1)`. -/
lemma bitMass_pos {q : I} (h0 : 0 < (q : ℝ)) (h1 : (q : ℝ) < 1) (b : Bool) :
    0 < bitMass q b := by
  unfold bitMass; split_ifs <;> linarith

/-- The Bernoulli measure of a singleton. -/
lemma bernoulli_singleton (q : I) (b : Bool) :
    ProbabilityTheory.bernoulliMeasure true false q {b} = ENNReal.ofReal (bitMass q b) := by
  cases b
  · rw [bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by simp) rfl]
    simp only [bitMass, Bool.false_eq_true, ↓reduceIte, ENNReal.ofReal]
    congr 1; ext; simp [Real.coe_toNNReal _ (sub_nonneg.2 q.2.2)]
  · rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) rfl (by simp)]
    simp only [bitMass, ↓reduceIte, ENNReal.ofReal]
    congr 1; ext; simp [Real.coe_toNNReal _ q.2.1]

/-- A cylinder is a finite box. -/
lemma cylinder_eq_pi (x : ℕ → Bool) (n : ℕ) :
    PiNat.cylinder x n = Set.pi (Finset.range n : Set ℕ) fun i ↦ {x i} := by
  ext y; simp [PiNat.mem_cylinder_iff]

/-- Example 5.1: `μ_β[x↾n] = ∏_{i<n} β_i^{x_i} (1 - β_i)^{1 - x_i}`.
Blueprint node `meas:examples`. -/
theorem productBernoulli_cylinder (β : ℕ → I) (x : ℕ → Bool) (n : ℕ) :
    productBernoulli β (PiNat.cylinder x n) =
      ENNReal.ofReal (∏ i ∈ Finset.range n, bitMass (β i) (x i)) := by
  rw [cylinder_eq_pi, productBernoulli,
    Measure.infinitePi_pi _ (fun _ _ ↦ measurableSet_singleton _),
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ bitMass_nonneg _ _]
  simp only [bernoulli_singleton]

/-- The information `Y_i(x) = -log₂ β_i` if `x_i = 1`, `-log₂ (1 - β_i)` if `x_i = 0`, of the
`i`-th symbol (Example 5.1). -/
noncomputable def symbolInfo (β : ℕ → I) (i : ℕ) (x : ℕ → Bool) : ℝ :=
  -Real.logb 2 (bitMass (β i) (x i))

/-- The symbol information is nonnegative. -/
lemma symbolInfo_nonneg (β : ℕ → I) (i : ℕ) (x : ℕ → Bool) : 0 ≤ symbolInfo β i x :=
  neg_nonneg.2 (Real.logb_nonpos one_lt_two (bitMass_nonneg _ _) (bitMass_le_one _ _))

/-- Example 5.1: `-log₂ μ_β[x↾n] = ∑_{i<n} Y_i(x)` for biases in `(0, 1)`.
Blueprint node `meas:examples`. -/
theorem infoBits_productBernoulli_cylinder {β : ℕ → I}
    (hβ : ∀ i, 0 < (β i : ℝ) ∧ (β i : ℝ) < 1) (x : ℕ → Bool) (n : ℕ) :
    infoBits (productBernoulli β (PiNat.cylinder x n)) =
      ENNReal.ofReal (∑ i ∈ Finset.range n, symbolInfo β i x) := by
  rw [productBernoulli_cylinder,
    infoBits_ofReal (Finset.prod_pos fun i _ ↦ bitMass_pos (hβ i).1 (hβ i).2 _),
    Real.logb_prod _ _ (fun i _ ↦ (bitMass_pos (hβ i).1 (hβ i).2 _).ne')]
  simp [symbolInfo, Finset.sum_neg_distrib]

/-- A function of the `i`-th coordinate is integrable. -/
lemma integrable_comp_eval (β : ℕ → I) (i : ℕ) (g : Bool → ℝ) :
    Integrable (fun x ↦ g (x i)) (productBernoulli β) := by
  have h := measurePreserving_eval_infinitePi
    (fun i ↦ ProbabilityTheory.bernoulliMeasure true false (β i)) i
  have hi : Integrable g (ProbabilityTheory.bernoulliMeasure true false (β i)) :=
    integrable_bernoulliMeasure _ _ _ _
  rw [← h.map_eq] at hi
  exact (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
    h.measurable.aemeasurable).1 hi

/-- The mean of a function of the `i`-th coordinate. -/
lemma integral_comp_eval (β : ℕ → I) (i : ℕ) (g : Bool → ℝ) :
    ∫ x, g (x i) ∂productBernoulli β = (β i : ℝ) * g true + (1 - β i) * g false := by
  have h := measurePreserving_eval_infinitePi
    (fun i ↦ ProbabilityTheory.bernoulliMeasure true false (β i)) i
  have : ∫ x, g (x i) ∂productBernoulli β =
      ∫ b, g b ∂(ProbabilityTheory.bernoulliMeasure true false (β i)) := by
    rw [← h.map_eq, integral_map h.measurable.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable]
    rfl
  rw [this, integral_bernoulliMeasure]
  simp

/-- Example 5.1: the symbol information `Y_i` has mean `H(β_i)`.
Blueprint node `meas:examples`. -/
theorem integral_symbolInfo (β : ℕ → I) (i : ℕ) :
    ∫ x, symbolInfo β i x ∂productBernoulli β = bitEntropy (β i) := by
  rw [show (fun x ↦ symbolInfo β i x) = fun x ↦ (fun b ↦ -Real.logb 2 (bitMass (β i) b)) (x i)
    from rfl, integral_comp_eval β i (fun b ↦ -Real.logb 2 (bitMass (β i) b))]
  simp only [bitMass, bitEntropy, Real.binEntropy, Real.logb, Real.log_inv, ↓reduceIte,
    Bool.false_eq_true]
  ring

/-- The Cesàro average `(1/n) ∑_{i<n} H(β_i)`. -/
noncomputable def entropyAverage (β : ℕ → I) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, bitEntropy (β i)) / n

/-- `a̲ = liminf_n (1/n) ∑_{i<n} H(β_i)` (Example 5.1), as an element of `[0, ∞]`.
Blueprint node `meas:examples`. -/
noncomputable def lowerEntropyAverage (β : ℕ → I) : ℝ≥0∞ :=
  liminf (fun n ↦ ENNReal.ofReal (entropyAverage β n)) atTop

/-- `ā = limsup_n (1/n) ∑_{i<n} H(β_i)` (Example 5.1), as an element of `[0, ∞]`.
Blueprint node `meas:examples`. -/
noncomputable def upperEntropyAverage (β : ℕ → I) : ℝ≥0∞ :=
  limsup (fun n ↦ ENNReal.ofReal (entropyAverage β n)) atTop

/-- Example 5.1, exact means: `∫ -log₂ μ_β[x↾n] dμ_β = ∑_{i<n} H(β_i)` (`= H_μ(ξ^n)`).
The paper assumes `β_i ∈ [δ, 1 - δ]`; biases in `(0, 1)` suffice here.
Blueprint node `meas:examples`. -/
theorem lintegral_infoBits_productBernoulli {β : ℕ → I}
    (hβ : ∀ i, 0 < (β i : ℝ) ∧ (β i : ℝ) < 1) (n : ℕ) :
    ∫⁻ x, infoBits (productBernoulli β (PiNat.cylinder x n)) ∂productBernoulli β =
      ENNReal.ofReal (∑ i ∈ Finset.range n, bitEntropy (β i)) := by
  simp_rw [infoBits_productBernoulli_cylinder hβ]
  have hint : ∀ i, Integrable (symbolInfo β i) (productBernoulli β) := fun i ↦
    integrable_comp_eval β i (fun b ↦ -Real.logb 2 (bitMass (β i) b))
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ fun i _ ↦ hint i)
    (.of_forall fun x ↦ Finset.sum_nonneg fun i _ ↦ symbolInfo_nonneg β i x),
    integral_finsetSum _ fun i _ ↦ hint i]
  simp [integral_symbolInfo]

/-- Example 5.1: the information rates of `μ_β` are `(a̲, ā)`, the lower and upper limits of the
Cesàro averages of `H(β_i)`. No law of large numbers is needed. The paper assumes
`β_i ∈ [δ, 1 - δ]`; biases in `(0, 1)` suffice here. Blueprint node `meas:examples`. -/
theorem informationRate_productBernoulli {β : ℕ → I}
    (hβ : ∀ i, 0 < (β i : ℝ) ∧ (β i : ℝ) < 1) :
    informationRate (productBernoulli β) shiftMap =
      (lowerEntropyAverage β, upperEntropyAverage β) := by
  have h : (fun n : ℕ ↦ (∫⁻ x, infoBits (productBernoulli β (PiNat.cylinder x n))
      ∂productBernoulli β) / n) =ᶠ[atTop] fun n ↦ ENNReal.ofReal (entropyAverage β n) :=
    (eventually_ge_atTop 1).mono fun n hn ↦ by
      simp only [lintegral_infoBits_productBernoulli hβ, entropyAverage, ofReal_div_natCast hn]
  rw [informationRate_shiftMap (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (fun _ _ ↦ cantorMetricSpace_dist_eq), liminf_congr h, limsup_congr h]
  rfl

/-- Example 5.1: for biases in `[δ, 1 - δ]`, `(1/n) ∑_{i<n} Y_i - (1/n) ∑_{i<n} H(β_i) → 0`
almost surely (the strong law `ae_tendsto_avg_of_iIndepFun_bounded` applied to the independent
bounded centred variables `Y_i - H(β_i)`). -/
theorem ae_tendsto_symbolInfo_sub {β : ℕ → I} {δ : ℝ} (hδ : 0 < δ)
    (hβ : ∀ i, δ ≤ (β i : ℝ) ∧ (β i : ℝ) ≤ 1 - δ) :
    ∀ᵐ x ∂productBernoulli β, Tendsto (fun n : ℕ ↦
      (∑ i ∈ Finset.range n, symbolInfo β i x) / n - entropyAverage β n) atTop (𝓝 0) := by
  set g : ℕ → Bool → ℝ := fun i b ↦ -Real.logb 2 (bitMass (β i) b) - bitEntropy (β i)
  have hind : iIndepFun (fun i (x : ℕ → Bool) ↦ g i (x i)) (productBernoulli β) :=
    iIndepFun_infinitePi (P := fun i ↦ ProbabilityTheory.bernoulliMeasure true false (β i))
      (X := g) fun _ ↦ Measurable.of_discrete
  have hmass : ∀ i b, δ ≤ bitMass (β i) b := fun i b ↦ by
    unfold bitMass; split_ifs
    · exact (hβ i).1
    · linarith [(hβ i).2]
  have hC : ∀ i (x : ℕ → Bool), |g i (x i)| ≤ -Real.logb 2 δ + 1 := fun i x ↦ by
    have h0 := symbolInfo_nonneg β i x
    have h1 : symbolInfo β i x ≤ -Real.logb 2 δ :=
      neg_le_neg (Real.logb_le_logb_of_le one_lt_two hδ (hmass i (x i)))
    have h2 := bitEntropy_nonneg (β i)
    have h3 := bitEntropy_le_one (β i)
    rw [abs_le]
    constructor <;> simp only [g] <;> unfold symbolInfo at h0 h1 <;> linarith
  have hmean : ∀ i, ∫ x, g i (x i) ∂productBernoulli β = 0 := fun i ↦ by
    simp only [g]
    have hI : Integrable (fun x : ℕ → Bool ↦ -Real.logb 2 (bitMass (β i) (x i)))
        (productBernoulli β) :=
      integrable_comp_eval β i (fun b ↦ -Real.logb 2 (bitMass (β i) b))
    rw [integral_sub hI (integrable_const _)]
    have := integral_symbolInfo β i
    simp only [symbolInfo] at this
    simp [this]
  filter_upwards [ae_tendsto_avg_of_iIndepFun_bounded hind (fun i ↦
    (Measurable.of_discrete (f := g i)).comp (measurable_pi_apply i)) hC hmean] with x hx
  refine hx.congr fun n ↦ ?_
  simp only [g, entropyAverage, Finset.sum_sub_distrib, sub_div, symbolInfo]

/-- Example 5.1: for biases in `[δ, 1 - δ]` with `δ > 0`, `μ_β`-almost every point has local
entropies `Φ_μ(x) = (a̲, ā)` under the shift. The paper also asks `β` to be computable, which
plays no role here. Blueprint node `meas:examples`. -/
theorem ae_localEntropy_productBernoulli {β : ℕ → I} {δ : ℝ} (hδ : 0 < δ)
    (hβ : ∀ i, δ ≤ (β i : ℝ) ∧ (β i : ℝ) ≤ 1 - δ) :
    ∀ᵐ x ∂productBernoulli β, localEntropy (productBernoulli β) shiftMap x =
      (lowerEntropyAverage β, upperEntropyAverage β) := by
  have hβ' : ∀ i, 0 < (β i : ℝ) ∧ (β i : ℝ) < 1 := fun i ↦
    ⟨hδ.trans_le (hβ i).1, by linarith [(hβ i).2]⟩
  filter_upwards [ae_tendsto_symbolInfo_sub hδ hβ] with x hx
  have h : (fun n : ℕ ↦ infoBits (productBernoulli β (PiNat.cylinder x n)) / n) =ᶠ[atTop]
      fun n ↦ ENNReal.ofReal ((∑ i ∈ Finset.range n, symbolInfo β i x) / n) :=
    (eventually_ge_atTop 1).mono fun n hn ↦ by
      dsimp only
      rw [infoBits_productBernoulli_cylinder hβ', ofReal_div_natCast hn]
  rw [localEntropy_shiftMap (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (fun _ _ ↦ cantorMetricSpace_dist_eq), liminf_congr h, limsup_congr h,
    (liminf_limsup_ofReal_congr hx).1, (liminf_limsup_ofReal_congr hx).2]
  rfl

/-- If the local entropies of a probability measure on Cantor space are almost surely equal to
a constant `c`, then the entropy law is `δ_c`, the Feng–Huang entropies are `c`, and the
essential infima and suprema of the lower and upper local entropies are `c.1` and `c.2`. -/
theorem entropyStatistics_of_ae_eq {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ]
    {c : ℝ≥0∞ × ℝ≥0∞} (h : ∀ᵐ x ∂μ, localEntropy μ shiftMap x = c) :
    entropyLaw μ shiftMap = Measure.dirac c ∧ measureEntropy μ shiftMap = c ∧
      (essInf (fun x ↦ (localEntropy μ shiftMap x).1) μ = c.1 ∧
        essSup (fun x ↦ (localEntropy μ shiftMap x).1) μ = c.1) ∧
      (essInf (fun x ↦ (localEntropy μ shiftMap x).2) μ = c.2 ∧
        essSup (fun x ↦ (localEntropy μ shiftMap x).2) μ = c.2) := by
  have h1 : (fun x ↦ (localEntropy μ shiftMap x).1) =ᵐ[μ] fun _ ↦ c.1 :=
    h.mono fun x hx ↦ by simp only [hx]
  have h2 : (fun x ↦ (localEntropy μ shiftMap x).2) =ᵐ[μ] fun _ ↦ c.2 :=
    h.mono fun x hx ↦ by simp only [hx]
  have hμ : μ ≠ 0 := IsProbabilityMeasure.ne_zero μ
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [entropyLaw, Measure.map_congr h, Measure.map_const, measure_univ, one_smul]
  · rw [measureEntropy, lintegral_congr_ae h1, lintegral_congr_ae h2]
    simp
  · rw [essInf_congr_ae h1, essInf_const _ hμ]
  · rw [essSup_congr_ae h1, essSup_const _ hμ]
  · rw [essInf_congr_ae h2, essInf_const _ hμ]
  · rw [essSup_congr_ae h2, essSup_const _ hμ]

/-- Example 5.1 and §6.1: the entropy law of `μ_β` is the point mass `Λ_μ = δ_{(a̲, ā)}`, the
Feng–Huang entropies are `(a̲, ā)`, and the essential bounds of the lower (upper) local entropy
both equal `a̲` (`ā`). Blueprint node `meas:examples`. -/
theorem entropyLaw_productBernoulli {β : ℕ → I} {δ : ℝ} (hδ : 0 < δ)
    (hβ : ∀ i, δ ≤ (β i : ℝ) ∧ (β i : ℝ) ≤ 1 - δ) :
    entropyLaw (productBernoulli β) shiftMap =
        Measure.dirac (lowerEntropyAverage β, upperEntropyAverage β) ∧
      measureEntropy (productBernoulli β) shiftMap =
        (lowerEntropyAverage β, upperEntropyAverage β) ∧
      (essInf (fun x ↦ (localEntropy (productBernoulli β) shiftMap x).1) (productBernoulli β) =
          lowerEntropyAverage β ∧
        essSup (fun x ↦ (localEntropy (productBernoulli β) shiftMap x).1) (productBernoulli β) =
          lowerEntropyAverage β) ∧
      (essInf (fun x ↦ (localEntropy (productBernoulli β) shiftMap x).2) (productBernoulli β) =
          upperEntropyAverage β ∧
        essSup (fun x ↦ (localEntropy (productBernoulli β) shiftMap x).2) (productBernoulli β) =
          upperEntropyAverage β) :=
  entropyStatistics_of_ae_eq (ae_localEntropy_productBernoulli hδ hβ)

end Kolmogorov.PointToSet
