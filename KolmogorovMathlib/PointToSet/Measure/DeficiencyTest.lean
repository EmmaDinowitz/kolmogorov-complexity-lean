/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Randomness
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The incompressibility test (Lemma 3.2)

For a rational `ε > 0` the test function of Lemma 3.2 of E. Dinowitz, *Entropy of non-invariant
measures and orbit complexity of random points*, is

`t_ε(y) = ∑_{n ≥ 1} ∑_i 2^{-K^A(i)} n^{-2} 1_{B_n(x_i, T, ε)}(y) / μ(B̄_n(x_i, T, ε))`,

with the convention `1/0 = ∞` (`testFunction`). It is positive, its integral is less than `2`
(`lintegral_testFunction_lt_two`) and for every point `x` and `n ≥ 1`

`-log₂ μ(B_n(x, T, 2ε)) ≤ K_n^A(x, T, ε) + 2 log₂ n + log₂ t_ε(x)`

(`testFunction_mul_measure_bowenBall_ge`, in multiplicative form, where `t_ε(x) < ∞`).

The part of the lemma that uses randomness is realized by a Martin-Löf test built from the
single summands rather than from the sum (blueprint mark ◇): the sets

`V_m = ⋃ {B_n(x_i, T, ε) : μ(B̄_n(x_i, T, ε)) < 2^{-K^A(i) - m} n^{-2}}`

are uniformly `A`-c.e. open by (M1), (M2) and the upper semicomputability of `K^A`, and
`μ(V_m) ≤ 2^{-m} π²/6`. A random point leaves some `V_m`, which is the bound
`exists_deficiency_bound`; minimizing over the ideal points of the Bowen ball gives
`exists_measure_bowenBall_ge_of_mem_randomPoints`, the inequality of Lemma 3.2 with the
constant `m` in place of `log₂ t_ε(x)`. The finiteness of the sum `t_ε` itself at random
points is `testFunction_lt_top_of_mem_randomPoints` in `Measure/TestFunctionFinite.lean`.

Auxiliary results: `tsum_inv_sq_lt_two` (`∑_{n ≥ 1} n^{-2} < 2` in `ℝ≥0∞`),
`tsum_tsum_weight_le` (summing the weights `2^{-K^A(i) - m} n^{-2}` with the Kraft inequality)
and `IsCeOpenFamilyIn.iUnion_of_isREIn` (unions of a c.e. open family over an r.e. set of
indices).

Blueprint node `meas:test`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### Summing the weights -/

/-- The series `∑_{n ≥ 1} n^{-2} = π²/6` is less than `2`, in `ℝ≥0∞`. -/
theorem tsum_inv_sq_lt_two :
    ∑' n : ℕ, (if n = 0 then 0 else ((n : ℝ≥0∞) ^ 2)⁻¹) < 2 := by
  have h : ∀ n : ℕ, (if n = 0 then 0 else ((n : ℝ≥0∞) ^ 2)⁻¹) =
      ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp only [hn.ne', ↓reduceIte]
      rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity),
        ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  simp_rw [h]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hasSum_zeta_two.summable,
    hasSum_zeta_two.tsum_eq, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  nlinarith

/-- The double series of the weights `2^{-K^A(i) - m} n^{-2}` (`n ≥ 1`) is at most
`(∑_{n ≥ 1} n^{-2}) 2^{-m}`, by the Kraft inequality. -/
theorem tsum_tsum_weight_le (A : Set ℕ) (m : ℕ) :
    ∑' (n : ℕ) (i : ℕ), (if n = 0 then 0 else
      (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A i + m) / (n : ℝ≥0∞) ^ 2) ≤
      (∑' n : ℕ, (if n = 0 then 0 else ((n : ℝ≥0∞) ^ 2)⁻¹)) * (2 : ℝ≥0∞)⁻¹ ^ m := by
  have h : ∀ n i : ℕ, (if n = 0 then 0 else
      (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A i + m) / (n : ℝ≥0∞) ^ 2) =
      ((if n = 0 then 0 else ((n : ℝ≥0∞) ^ 2)⁻¹) * (2 : ℝ≥0∞)⁻¹ ^ m) *
        (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i := by
    intro n i
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv]; ring
  simp_rw [h, ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum fun n ↦ mul_le_of_le_one_right (by simp) (oracle_kraft A)

/-- The test function `t_ε` of Lemma 3.2, with the convention `1/0 = ∞`.
Blueprint node `meas:test`. -/
noncomputable def testFunction (P : Presentation X) (T : X → X) (A : Set ℕ) (μ : Measure X)
    (ε : ℝ) (y : X) : ℝ≥0∞ :=
  ∑' (n : ℕ) (i : ℕ), if n = 0 then 0 else
    (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i / (n : ℝ≥0∞) ^ 2 *
      ((bowenBall T n (P.ι i) ε).indicator (fun _ ↦ (1 : ℝ≥0∞)) y /
        μ (closedBowenBall T n (P.ι i) ε))

omit [BorelSpace X] in
/-- The test function is positive everywhere. Blueprint node `meas:test`. -/
theorem testFunction_pos (P : Presentation X) (T : X → X) (hT : Continuous T) (A : Set ℕ)
    (μ : Measure X) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) (y : X) :
    0 < testFunction P T A μ ε y := by
  obtain ⟨i, hi⟩ := bowen_ball_dense P T hT y 1 le_rfl ε hε
  have hy : y ∈ bowenBall T 1 (P.ι i) ε := mem_bowenBall_symm hi
  unfold testFunction
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum 1)
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum i)
  simp only [one_ne_zero, ↓reduceIte, indicator_of_mem hy, Nat.cast_one, one_pow, div_one]
  exact ENNReal.mul_pos (by simp) (ENNReal.div_pos one_ne_zero (measure_ne_top μ _)).ne'

/-- The integral of the test function is less than `2`. Blueprint node `meas:test`. -/
theorem lintegral_testFunction_lt_two (P : Presentation X) (T : X → X) (hT : Continuous T)
    (A : Set ℕ) (μ : Measure X) [IsFiniteMeasure μ] (ε : ℝ) :
    ∫⁻ y, testFunction P T A μ ε y ∂μ < 2 := by
  have hmeas : ∀ n i : ℕ, Measurable fun y ↦ (if n = 0 then 0 else
      (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i / (n : ℝ≥0∞) ^ 2 *
        ((bowenBall T n (P.ι i) ε).indicator (fun _ ↦ (1 : ℝ≥0∞)) y /
          μ (closedBowenBall T n (P.ι i) ε))) := by
    intro n i
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact measurable_const
    · simp only [hn, ↓reduceIte]
      exact measurable_const.mul ((measurable_const.indicator
        (bowen_ball_dense_open T hT n _ ε).measurableSet).div_const _)
  have hterm : ∀ n i : ℕ, ∫⁻ y, (if n = 0 then 0 else
      (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i / (n : ℝ≥0∞) ^ 2 *
        ((bowenBall T n (P.ι i) ε).indicator (fun _ ↦ (1 : ℝ≥0∞)) y /
          μ (closedBowenBall T n (P.ι i) ε))) ∂μ ≤ (if n = 0 then 0 else
      (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A i + 0) / (n : ℝ≥0∞) ^ 2) := by
    intro n i
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte, add_zero]
      set c := (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i / (n : ℝ≥0∞) ^ 2
      set d := μ (closedBowenBall T n (P.ι i) ε)
      have hfun : (fun y ↦ c * ((bowenBall T n (P.ι i) ε).indicator (fun _ ↦ (1 : ℝ≥0∞)) y /
          d)) = (bowenBall T n (P.ι i) ε).indicator (fun _ ↦ c * d⁻¹) := by
        ext y
        by_cases hy : y ∈ bowenBall T n (P.ι i) ε <;> simp [hy, div_eq_mul_inv]
      rw [hfun, lintegral_indicator_const (bowen_ball_dense_open T hT n _ ε).measurableSet,
        mul_assoc]
      refine mul_le_of_le_one_right (by simp) ?_
      rw [mul_comm, ← div_eq_mul_inv]
      exact ENNReal.div_le_of_le_mul (by
        rw [one_mul]; exact measure_mono (bowenBall_subset_closedBowenBall T n _ ε))
  unfold testFunction
  rw [lintegral_tsum fun n ↦ (Measurable.tsum (hmeas n)).aemeasurable]
  simp_rw [lintegral_tsum fun i ↦ (hmeas _ i).aemeasurable]
  calc _ ≤ ∑' (n : ℕ) (i : ℕ), (if n = 0 then 0 else
          (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A i + 0) / (n : ℝ≥0∞) ^ 2) :=
        ENNReal.tsum_le_tsum fun n ↦ ENNReal.tsum_le_tsum fun i ↦ hterm n i
    _ ≤ (∑' n : ℕ, (if n = 0 then 0 else ((n : ℝ≥0∞) ^ 2)⁻¹)) * (2 : ℝ≥0∞)⁻¹ ^ 0 :=
        tsum_tsum_weight_le A 0
    _ < 2 := by
        rw [pow_zero, mul_one]
        exact tsum_inv_sq_lt_two

omit [BorelSpace X] in
/-- The inequality of Lemma 3.2 in multiplicative form, at a point where the test function is
finite: `2^{-K_n^A(x, T, ε)} n^{-2} ≤ t_ε(x) μ(B_n(x, T, 2ε))`. (Where `t_ε(x) = ∞` the
additive form of the lemma is vacuous.) Blueprint node `meas:test`. -/
theorem testFunction_mul_measure_bowenBall_ge (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε)
    (x : X) (hx : testFunction P T A μ ε x ≠ ⊤) {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ≥0∞)⁻¹ ^ orbitComplexityNat P T A x n ε / (n : ℝ≥0∞) ^ 2 ≤
      testFunction P T A μ ε x * μ (bowenBall T n x (2 * ε)) := by
  obtain ⟨i, hi, hK⟩ := entropiesAndOrbitComplexities_attained P T hT A x n hn ε hε
  have hKn : orbitComplexityNat P T A x n ε = oracleNatComplexity A i := by
    rw [orbitComplexityNat, hK, ENat.toNat_natCast]
  rw [hKn]
  have hxi : x ∈ bowenBall T n (P.ι i) ε := mem_bowenBall_symm hi
  set c := (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i / (n : ℝ≥0∞) ^ 2
  set d := μ (closedBowenBall T n (P.ι i) ε)
  have hle : c * (1 / d) ≤ testFunction P T A μ ε x := by
    unfold testFunction
    refine le_trans ?_ (ENNReal.le_tsum n)
    refine le_trans ?_ (ENNReal.le_tsum i)
    simp only [show n ≠ 0 by omega, ↓reduceIte, indicator_of_mem hxi]
    exact le_rfl
  have hc0 : c ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by simp, by simp⟩
  have hd0 : d ≠ 0 := by
    intro h0
    apply hx
    rw [h0, ENNReal.div_zero one_ne_zero, ENNReal.mul_top hc0] at hle
    exact top_le_iff.mp hle
  calc c = c * (1 / d) * d := by
        rw [mul_assoc, one_div, ENNReal.inv_mul_cancel hd0 (measure_ne_top μ _), mul_one]
    _ ≤ testFunction P T A μ ε x * μ (bowenBall T n x (2 * ε)) :=
        mul_le_mul' hle (measure_mono (closedBowenBall_subset_bowenBall_two_mul hi))

/-- The levels of the incompressibility test: the union of the Bowen balls about ideal points
whose closed Bowen ball has measure less than `2^{-K^A(i) - m} n^{-2}`.
Blueprint node `meas:test`. -/
def deficiencyLevel (P : Presentation X) (T : X → X) (A : Set ℕ) (μ : Measure X) (ε : ℝ)
    (m : ℕ) : Set X :=
  ⋃ (n : ℕ) (i : ℕ) (_ : 1 ≤ n)
    (_ : μ (closedBowenBall T n (P.ι i) ε) <
      (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A i + m) / (n : ℝ≥0∞) ^ 2),
    bowenBall T n (P.ι i) ε

omit [MeasurableSpace X] [BorelSpace X] in
/-- A union of the members of a c.e. open family over an r.e. set of indices, uniformly in a
parameter, is c.e. open. -/
theorem IsCeOpenFamilyIn.iUnion_of_isREIn {P : Presentation X} {A : Set ℕ} {ι κ : Type*}
    [Primcodable ι] [Primcodable κ] {U : κ → Set X} (hU : IsCeOpenFamilyIn P A U)
    {C : ι × κ → Prop} (hC : IsREIn A C) :
    IsCeOpenFamilyIn P A fun i ↦ ⋃ k ∈ {k | C (i, k)}, U k := by
  obtain ⟨E, hE, hU⟩ := hU
  refine ⟨fun ib ↦ ∃ k, C (ib.1, k) ∧ E (k, ib.2), ?_, fun i ↦ ?_⟩
  · have h₁ : IsREIn A fun p : (ι × (ℕ × ℚ)) × κ ↦ C (p.1.1, p.2) :=
      hC.comp ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
    have h₂ : IsREIn A fun p : (ι × (ℕ × ℚ)) × κ ↦ E (p.2, p.1.2) :=
      hE.comp (Computable.snd.pair (Computable.snd.comp Computable.fst)).computableIn
    exact (h₁.and h₂).exists
  · ext y
    simp only [mem_iUnion, mem_ofPred_eq, hU, exists_prop]
    constructor
    · rintro ⟨k, hk, b, hb, hy⟩
      exact ⟨b, ⟨k, hk, hb⟩, hy⟩
    · rintro ⟨b, ⟨k, hk, hb⟩, hy⟩
      exact ⟨k, hk, b, hb, hy⟩

/-- The rational `2^{-j} n^{-2}` (with `n` replaced by `1` when `n = 0`). -/
private def weightRat (j n : ℕ) : ℚ := 1 / ((max 1 n ^ 2 * 2 ^ j : ℕ) : ℚ)

/-- The rationals `2^{-j} n^{-2}` are computable. -/
private lemma computable_weightRat : Computable fun p : ℕ × ℕ ↦ weightRat p.1 p.2 := by
  have hD : Primrec fun p : ℕ × ℕ ↦ max 1 p.2 ^ 2 * 2 ^ p.1 :=
    Primrec.nat_mul.comp (nat_pow_primrec₂.comp (Primrec.nat_max.comp (Primrec.const 1)
      Primrec.snd) (Primrec.const 2)) (nat_pow_primrec₂.comp (Primrec.const 2) Primrec.fst)
  refine computable_of_num_den (N := fun _ ↦ 1) (Computable.const 1) hD.to_comp
    (fun p ↦ by positivity) fun p ↦ ?_
  simp [weightRat]

/-- For `n ≥ 1`, the real value of `weightRat j n` is that of `2^{-j} n^{-2}` in `ℝ≥0∞`. -/
private lemma weightRat_cast {j n : ℕ} (hn : 1 ≤ n) :
    (weightRat j n : ℝ) = ((2 : ℝ≥0∞)⁻¹ ^ j / (n : ℝ≥0∞) ^ 2).toReal := by
  rw [weightRat, max_eq_right hn, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  push_cast
  rw [inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- `2^{-j} n^{-2}` is finite for `n ≥ 1`. -/
private lemma weight_ne_top {j n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ≥0∞)⁻¹ ^ j / (n : ℝ≥0∞) ^ 2 ≠ ⊤ :=
  ENNReal.div_ne_top (by simp) (by positivity)

/-- The rationals `weightRat j n` decrease in `j`. -/
private lemma weightRat_anti {j j' n : ℕ} (h : j ≤ j') : weightRat j' n ≤ weightRat j n := by
  unfold weightRat
  gcongr

omit [MetricSpace X] [BorelSpace X] in
/-- The condition defining the levels of the incompressibility test in terms of an upper bound
for `K^A(i)` and a strict rational upper bound for the measure. -/
private lemma measure_lt_weight_iff (μ : Measure X) [IsFiniteMeasure μ] (S : Set X)
    (K m n : ℕ) (hn : 1 ≤ n) :
    μ S < (2 : ℝ≥0∞)⁻¹ ^ (K + m) / (n : ℝ≥0∞) ^ 2 ↔
      ∃ k : ℕ, (K : ℝ) < (((k + 1 : ℕ) : ℚ) : ℝ) ∧ (μ S).toReal < (weightRat (k + m) n : ℝ) := by
  constructor
  · intro h
    refine ⟨K, by push_cast; linarith, ?_⟩
    rw [weightRat_cast hn]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top μ S) (weight_ne_top hn)).mpr h
  · rintro ⟨k, hk, hS⟩
    have hKk : K ≤ k := by
      have : (K : ℝ) < k + 1 := by exact_mod_cast hk
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    have h₁ : (weightRat (k + m) n : ℝ) ≤ weightRat (K + m) n := by
      exact_mod_cast weightRat_anti (by omega)
    rw [weightRat_cast (j := K + m) hn] at h₁
    exact (ENNReal.toReal_lt_toReal (measure_ne_top μ S) (weight_ne_top hn)).mp
      (hS.trans_le h₁)

/-- The levels of the incompressibility test are uniformly c.e. open relative to an
admissible oracle. Blueprint node `meas:test`. -/
theorem isCeOpenFamilyIn_deficiencyLevel (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) :
    IsCeOpenFamilyIn P A fun m : ℕ ↦ deficiencyLevel P T A μ (ε : ℝ) m := by
  let F : (ℕ × ℕ × ℕ) × ℕ → Prop := fun p ↦ 1 ≤ p.1.2.1 ∧
    ((oracleNatComplexity A p.1.2.2 : ℝ) < (((p.2 + 1 : ℕ) : ℚ) : ℝ) ∧
    (μ (closedBowenBall T p.1.2.1 (P.ι p.1.2.2) (ε : ℝ))).toReal <
      (weightRat (p.2 + p.1.1) p.1.2.1 : ℝ))
  have hF : IsREIn A F := by
    have hn : Primrec fun p : (ℕ × ℕ × ℕ) × ℕ ↦ p.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hi : Primrec fun p : (ℕ × ℕ × ℕ) × ℕ ↦ p.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have h₁ : IsREIn A fun p : (ℕ × ℕ × ℕ) × ℕ ↦ 1 ≤ p.1.2.1 :=
      isREIn_of_computable_decide (Primrec.nat_le.comp (Primrec.const 1) hn).decide.to_comp
    have h₂ : IsREIn A fun p : (ℕ × ℕ × ℕ) × ℕ ↦
        (oracleNatComplexity A p.1.2.2 : ℝ) < (((p.2 + 1 : ℕ) : ℚ) : ℝ) :=
      (isREIn_oracleNatComplexity_lt A).comp
        (f := fun p : (ℕ × ℕ × ℕ) × ℕ ↦ (p.1.2.2, ((p.2 + 1 : ℕ) : ℚ)))
        (hi.to_comp.pair (ComputableReals.computable_natCastRat.comp
          (Primrec.succ.comp Primrec.snd).to_comp)).computableIn
    have h₃ : IsREIn A fun p : (ℕ × ℕ × ℕ) × ℕ ↦
        (μ (closedBowenBall T p.1.2.1 (P.ι p.1.2.2) (ε : ℝ))).toReal <
          (weightRat (p.2 + p.1.1) p.1.2.1 : ℝ) :=
      hA.isREIn_measure_closedBowenBall_lt.comp
        (f := fun p : (ℕ × ℕ × ℕ) × ℕ ↦
          ((p.1.2.1, p.1.2.2, ε), weightRat (p.2 + p.1.1) p.1.2.1))
        ((hn.to_comp.pair (hi.to_comp.pair (Computable.const ε))).pair
          (computable_weightRat.comp ((Primrec.nat_add.comp Primrec.snd
            (Primrec.fst.comp Primrec.fst)).to_comp.pair hn.to_comp))).computableIn
    exact h₁.and (h₂.and h₃)
  have hU := (isCeOpenFamilyIn_bowenBall P T A hA.1 hA.2.1).comp
    (g := fun k : ℕ × ℕ ↦ (k.1, k.2, ε))
    (Computable.fst.pair (Computable.snd.pair (Computable.const ε)))
  have h := hU.iUnion_of_isREIn (ι := ℕ) hF.exists
  convert h using 2 with m
  ext y
  simp only [deficiencyLevel, mem_iUnion, mem_ofPred_eq, exists_prop, F, Prod.exists]
  constructor
  · rintro ⟨n, i, hn, hc, hy⟩
    obtain ⟨k, hk⟩ := (measure_lt_weight_iff μ _ _ m n hn).mp hc
    exact ⟨n, i, ⟨k, hn, hk⟩, hy⟩
  · rintro ⟨n, i, ⟨k, hn, hk⟩, hy⟩
    exact ⟨n, i, hn, (measure_lt_weight_iff μ _ _ m n hn).mpr ⟨k, hk⟩, hy⟩

omit [BorelSpace X] in
/-- The level `m` of the incompressibility test has measure at most `2 · 2^{-m}`.
Blueprint node `meas:test`. -/
theorem measure_deficiencyLevel_le (P : Presentation X) (T : X → X)
    (A : Set ℕ) (μ : Measure X) [IsFiniteMeasure μ] (ε : ℝ) (m : ℕ) :
    μ (deficiencyLevel P T A μ ε m) ≤ (2 : ℝ≥0∞) ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ m := by
  have hterm : ∀ n i : ℕ, μ (⋃ (_ : 1 ≤ n)
      (_ : μ (closedBowenBall T n (P.ι i) ε) <
        (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A i + m) / (n : ℝ≥0∞) ^ 2),
      bowenBall T n (P.ι i) ε) ≤ (if n = 0 then 0 else
        (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A i + m) / (n : ℝ≥0∞) ^ 2) := by
    intro n i
    by_cases hn : 1 ≤ n
    · by_cases hc : μ (closedBowenBall T n (P.ι i) ε) <
          (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A i + m) / (n : ℝ≥0∞) ^ 2
      · simp only [hn, hc, iUnion_true, show n ≠ 0 by omega, ↓reduceIte]
        exact (measure_mono (bowenBall_subset_closedBowenBall T n _ ε)).trans hc.le
      · simp [hc]
    · simp [hn]
  calc μ (deficiencyLevel P T A μ ε m)
      ≤ ∑' (n : ℕ) (i : ℕ), (if n = 0 then 0 else
          (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A i + m) / (n : ℝ≥0∞) ^ 2) :=
        (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun n ↦
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun i ↦ hterm n i))
    _ ≤ (∑' n : ℕ, (if n = 0 then 0 else ((n : ℝ≥0∞) ^ 2)⁻¹)) * (2 : ℝ≥0∞)⁻¹ ^ m :=
        tsum_tsum_weight_le A m
    _ ≤ (2 : ℝ≥0∞) ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ m := by
        rw [pow_one]
        exact mul_le_mul_left tsum_inv_sq_lt_two.le _

/-- The incompressibility bound at a random point (Lemma 3.2, test form): there is `m` such
that every ideal point `x_i` of every Bowen ball `B_n(x, T, ε)` satisfies
`μ(B̄_n(x_i, T, ε)) ≥ 2^{-K^A(i) - m} n^{-2}`. Blueprint node `meas:test`. -/
theorem exists_deficiency_bound (P : Presentation X) (T : X → X)
    (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A)
    (ε : ℚ) {x : X} (hx : x ∈ randomPoints P A μ) :
    ∃ m : ℕ, ∀ n i : ℕ, 1 ≤ n → P.ι i ∈ bowenBall T n x (ε : ℝ) →
      (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A i + m) / (n : ℝ≥0∞) ^ 2 ≤
        μ (closedBowenBall T n (P.ι i) (ε : ℝ)) := by
  obtain ⟨m, hm⟩ := not_forall_mem_of_mem_randomPoints hx
    (isCeOpenFamilyIn_deficiencyLevel P T A μ hA ε) (c := 1)
    (measure_deficiencyLevel_le P T A μ (ε : ℝ))
  refine ⟨m, fun n i hn hi ↦ not_lt.mp fun hlt ↦ hm ?_⟩
  exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hn,
    mem_iUnion.mpr ⟨hlt, mem_bowenBall_symm hi⟩⟩⟩⟩

/-- Lemma 3.2 at a random point: there is `m` such that for all `n ≥ 1`,
`μ(B_n(x, T, 2ε)) ≥ 2^{-K_n^A(x, T, ε) - m} n^{-2}`, that is,
`-log₂ μ(B_n(x, T, 2ε)) ≤ K_n^A(x, T, ε) + 2 log₂ n + m`. Blueprint node `meas:test`. -/
theorem exists_measure_bowenBall_ge_of_mem_randomPoints (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) {x : X}
    (hx : x ∈ randomPoints P A μ) :
    ∃ m : ℕ, ∀ n : ℕ, 1 ≤ n →
      (2 : ℝ≥0∞)⁻¹ ^ (orbitComplexityNat P T A x n (ε : ℝ) + m) / (n : ℝ≥0∞) ^ 2 ≤
        μ (bowenBall T n x (2 * (ε : ℝ))) := by
  obtain ⟨m, hm⟩ := exists_deficiency_bound P T A μ hA ε hx
  refine ⟨m, fun n hn ↦ ?_⟩
  obtain ⟨i, hi, hK⟩ := entropiesAndOrbitComplexities_attained P T hT A x n hn (ε : ℝ)
    (by exact_mod_cast hε)
  have hKn : orbitComplexityNat P T A x n (ε : ℝ) = oracleNatComplexity A i := by
    rw [orbitComplexityNat, hK, ENat.toNat_natCast]
  rw [hKn]
  exact (hm n i hn hi).trans (measure_mono (closedBowenBall_subset_bowenBall_two_mul hi))

end Kolmogorov.PointToSet
