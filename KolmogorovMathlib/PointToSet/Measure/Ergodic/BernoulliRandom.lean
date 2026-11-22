/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.RemarksRates
import KolmogorovMathlib.PointToSet.Measure.Ergodic.TypicalPoints
import Mathlib.Probability.Independence.ZeroOne

/-!
# Bernoulli cross-entropy at every random point (Remark 7.2)

On Cantor space `ℕ → Bool` with the metric `cantorMetricSpace` and the left shift `σ`, let `ν_q`
be the Bernoulli measure of parameter `q`.

* `bernRand_measurePreserving`, `bernRand_ergodic`: `σ` preserves `ν_q` and is ergodic for it
  (an invariant set is a tail event, Kolmogorov's zero-one law).
* `bernRand_isCeOpenIn_coord`: for every presentation `P` and every oracle `A`, the cylinders
  `{y | y 0 = b}` are `A`-c.e. open: each is a single basic ball `B(x_a, 1)` about an ideal point
  with `x_a 0 = b`. No computability of the symbols of the ideal points is needed.
* `bernRand_tendsto_freq`: at every `ν_q`-random point relative to an oracle admissible for `ν_q`,
  the frequency of ones tends to `q` (input (I2′), `typical_eventually_lt_visitFrequency`, for
  the two cylinders `[1]` and `[0]`).
* `localEntropy_bernoulliMeasure_eq_crossEntropy_of_mem_randomPoints`: Remark 7.2, last
  sentence, in the paper's pointwise form: at every `ν_q`-random point,
  `Φ_{ν_q}(x) = (H(q), H(q))` and `Φ_{ν_p}(x) = (H(q‖p), H(q‖p))`.

Blueprint node `meas:remarks`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

attribute [local instance] cantorMetricSpace

/-- The left shift of Cantor space is measurable. -/
theorem bernRand_measurable_shiftMap : Measurable (shiftMap : (ℕ → Bool) → ℕ → Bool) :=
  Measurable.of_eval fun j ↦ measurable_pi_apply (j + 1)

/-- The left shift preserves every Bernoulli measure. Blueprint node `meas:remarks`. -/
theorem bernRand_measurePreserving (q : ℝ≥0) (hq : q ≤ 1) :
    MeasurePreserving shiftMap (bernoulliMeasure q hq) (bernoulliMeasure q hq) := by
  refine ⟨bernRand_measurable_shiftMap, ?_⟩
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  have hpre : shiftMap ⁻¹' Set.pi (s : Set ℕ) t =
      Set.pi ((s.map (addRightEmbedding 1) : Finset ℕ) : Set ℕ) fun i ↦ t (i - 1) := by
    ext y
    simp [shiftMap]
  rw [Measure.map_apply bernRand_measurable_shiftMap
    (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i), hpre, bernoulliMeasure,
    Measure.infinitePi_pi _ fun i _ ↦ ht _, Finset.prod_map]
  simp

/-- The coordinates shifted by `n`: `y ↦ (y (j + n))_j`. -/
private def bernRand_shiftBy (n : ℕ) (y : ℕ → Bool) : ℕ → Bool := fun j ↦ y (j + n)

/-- A strictly shift-invariant set is invariant under every shifted-coordinate map. -/
private lemma bernRand_preimage_shiftBy {s : Set (ℕ → Bool)} (hs : shiftMap ⁻¹' s = s)
    (n : ℕ) : bernRand_shiftBy n ⁻¹' s = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : bernRand_shiftBy (n + 1) = shiftMap ∘ bernRand_shiftBy n := by
      funext y j
      simp only [bernRand_shiftBy, shiftMap, Function.comp_apply]
      congr 1; omega
    rw [h, Set.preimage_comp, hs, ih]

/-- The left shift is ergodic for every Bernoulli measure: a strictly invariant measurable set
is a tail event of the independent coordinates, so it has measure `0` or `1`.
Blueprint node `meas:remarks`. -/
theorem bernRand_ergodic (q : ℝ≥0) (hq : q ≤ 1) :
    Ergodic shiftMap (bernoulliMeasure q hq) := by
  refine Ergodic.of_preimage_eq (bernRand_measurePreserving q hq) fun s hs hinv ↦ ?_
  let m : ℕ → MeasurableSpace (ℕ → Bool) := fun i ↦
    MeasurableSpace.comap (fun y : ℕ → Bool ↦ y i) inferInstance
  have hle : ∀ i, m i ≤ MeasurableSpace.pi := fun i ↦ (measurable_pi_apply i).comap_le
  have hind : ProbabilityTheory.iIndep m (bernoulliMeasure q hq) :=
    (ProbabilityTheory.iIndepFun_iff_iIndep _ _ _).1
      (ProbabilityTheory.iIndepFun_infinitePi (X := fun _ (ω : Bool) ↦ ω)
        fun _ ↦ measurable_id)
  have htail : MeasurableSet[limsup m atTop] s := by
    rw [limsup_eq_iInf_iSup_of_nat', MeasurableSpace.measurableSet_iInf]
    intro n
    have hmeas : Measurable[⨆ i, m (i + n)] (bernRand_shiftBy n) := by
      refine @Measurable.of_eval _ _ _ (⨆ i, m (i + n)) _ _ fun j ↦ ?_
      exact Measurable.of_comap_le (le_iSup (fun i ↦ m (i + n)) j)
    rw [← bernRand_preimage_shiftBy hinv n]
    exact hmeas hs
  rcases ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop hle hind htail
    with h | h
  · exact eventuallyEmptyOrUniv_iff'.2 (Or.inl (ae_eq_empty.2 h))
  · refine eventuallyEmptyOrUniv_iff'.2 (Or.inr (ae_eq_univ.2 ?_))
    rwa [prob_compl_eq_zero_iff hs]

/-- The `j`-th iterate of the shift reads the sequence from index `j`. -/
private lemma bernRand_iterate_apply (x : ℕ → Bool) (j i : ℕ) :
    (shiftMap^[j] x) i = x (i + j) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [shiftMap]
    rw [Nat.add_assoc]

/-- The cylinder `{y | y 0 = b}` is the ball of radius `1` about any point `z` with `z 0 = b`. -/
private lemma bernRand_ball_one (z : ℕ → Bool) :
    Metric.ball z 1 = {y : ℕ → Bool | y 0 = z 0} := by
  ext y
  simp only [Metric.mem_ball, mem_ofPred_eq]
  constructor
  · intro h
    exact PiNat.apply_eq_of_dist_lt (n := 0) (by simpa using h) le_rfl
  · intro h
    have h1 : y ∈ PiNat.cylinder z 1 := by
      rw [PiNat.mem_cylinder_iff]
      intro i hi
      rw [Nat.lt_one_iff.1 hi, h]
    have h2 := PiNat.mem_cylinder_iff_dist_le.1 h1
    norm_num at h2
    linarith

/-- For every presentation of Cantor space and every oracle, the cylinder `{y | y 0 = b}` is
c.e. open: it is a single basic ball of radius `1`. Blueprint node `meas:remarks`. -/
theorem bernRand_isCeOpenIn_coord (P : Presentation (ℕ → Bool)) (A : Set ℕ) (b : Bool) :
    IsCeOpenIn P A {y : ℕ → Bool | y 0 = b} := by
  obtain ⟨a, ha⟩ := P.dense.exists_dist_lt (fun _ ↦ b) one_pos
  have hb : P.ι a 0 = b :=
    (PiNat.apply_eq_of_dist_lt (n := 0) (by simpa using ha) le_rfl).symm
  refine ⟨fun c ↦ c = (a, 1), isREIn_of_computable_decide
    (Primrec.eq.comp Primrec.id (Primrec.const _)).decide.to_comp, ?_⟩
  ext y
  simp only [mem_iUnion, mem_ofPred_eq, exists_prop, exists_eq_left, basicBall]
  rw [Rat.cast_one, bernRand_ball_one, mem_ofPred_eq, hb]

/-- The Bernoulli mass of `{y | y 0 = b}` is `q` or `1 - q`. -/
private lemma bernRand_measure_coord (q : ℝ≥0) (hq : q ≤ 1) (b : Bool) :
    (bernoulliMeasure q hq {y : ℕ → Bool | y 0 = b}).toReal = if b then (q : ℝ) else 1 - q := by
  have hcyl : {y : ℕ → Bool | y 0 = b} = PiNat.cylinder (fun _ ↦ b) 1 := by
    ext y
    simp only [mem_ofPred_eq, PiNat.mem_cylinder_iff]
    exact ⟨fun h i hi ↦ by rw [Nat.lt_one_iff.1 hi, h], fun h ↦ h 0 one_pos⟩
  rw [hcyl, bernoulliMeasure_cylinder_prod, Finset.prod_range_one]
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hq) ENNReal.one_ne_top]
    simp
  · simp

/-- The visit count of the orbit of `x` to `{y | y 0 = true}` is the number of ones of `x↾n`. -/
private lemma bernRand_visitCount_true (x : ℕ → Bool) (n : ℕ) :
    (typicalVisitCount shiftMap {y : ℕ → Bool | y 0 = true} n x : ℝ) =
      ∑ i ∈ Finset.range n, bitVal (x i) := by
  classical
  unfold typicalVisitCount
  simp only [mem_ofPred_eq, bernRand_iterate_apply, Nat.zero_add, bitVal]
  rw [Finset.sum_boole]

/-- At every `ν_q`-random point (relative to an oracle admissible for `ν_q`) the frequency of
ones tends to `q`. No computability of the ideal points is assumed: the two cylinders of length
one are basic balls. Blueprint node `meas:remarks`. -/
theorem bernRand_tendsto_freq (P : Presentation (ℕ → Bool)) (A : Set ℕ) (q : ℝ≥0) (hq : q ≤ 1)
    (hAq : IsMeasureAdmissible P shiftMap (bernoulliMeasure q hq) A) {x : ℕ → Bool}
    (hx : x ∈ randomPoints P A (bernoulliMeasure q hq)) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, bitVal (x i)) / n) atTop (𝓝 (q : ℝ)) := by
  have herg := bernRand_ergodic q hq
  have hlow : ∀ b : Bool, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (if b then (q : ℝ) else 1 - q) - ε <
        (typicalVisitCount shiftMap {y : ℕ → Bool | y 0 = b} n x : ℝ) / n := by
    intro b ε hε
    have h := typical_eventually_lt_visitFrequency P shiftMap A _ hAq herg
      (bernRand_isCeOpenIn_coord P A b) hx hε
    rwa [bernRand_measure_coord] at h
  have hcompl : ∀ n, (typicalVisitCount shiftMap {y : ℕ → Bool | y 0 = false} n x : ℝ) =
      n - ∑ i ∈ Finset.range n, bitVal (x i) := by
    intro n
    have h := typicalVisitCount_add_compl shiftMap {y : ℕ → Bool | y 0 = true} n x
    have hset : {y : ℕ → Bool | y 0 = true}ᶜ = {y : ℕ → Bool | y 0 = false} := by
      ext y
      simp
    rw [hset] at h
    rw [← bernRand_visitCount_true]
    have h' : ((typicalVisitCount shiftMap {y : ℕ → Bool | y 0 = true} n x +
        typicalVisitCount shiftMap {y : ℕ → Bool | y 0 = false} n x : ℕ) : ℝ) = n := by
      exact_mod_cast h
    push_cast at h'
    linarith
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · filter_upwards [hlow true (q - a) (by linarith)] with n hn
    simp only [ite_true, bernRand_visitCount_true] at hn
    linarith
  · filter_upwards [hlow false (a - q) (by linarith), eventually_ge_atTop 1] with n hn hn1
    simp only [Bool.false_eq_true, ite_false, hcompl] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [sub_div, div_self hn0.ne'] at hn
    linarith

/-- If the frequency of ones of `x` tends to `q`, then `Φ_{ν_p}(x) = (H(q‖p), H(q‖p))` for
`0 < p < 1` (the computation of `ae_localEntropy_bernoulliMeasure_crossEntropy`).
Blueprint node `meas:remarks`. -/
theorem bernRand_localEntropy_of_tendsto (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (q : ℝ) {x : ℕ → Bool}
    (hfreq : Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, bitVal (x i)) / n) atTop (𝓝 q)) :
    localEntropy (bernoulliMeasure p hp) shiftMap x =
      (ENNReal.ofReal (crossEntropyBits q p), ENNReal.ofReal (crossEntropyBits q p)) := by
  have hx : Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, bitInfo p (x i)) / n) atTop
      (𝓝 (crossEntropyBits q p)) := by
    have hH : bitInfo p false + (bitInfo p true - bitInfo p false) * q =
        crossEntropyBits q p := by
      rw [crossEntropyBits]; ring
    have hlim : Tendsto (fun n : ℕ ↦ bitInfo p false + (bitInfo p true - bitInfo p false) *
        ((∑ i ∈ Finset.range n, bitVal (x i)) / n)) atTop (𝓝 (crossEntropyBits q p)) :=
      hH ▸ tendsto_const_nhds.add (hfreq.const_mul _)
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
  rw [localEntropy_shiftMap (by norm_num) (by norm_num) (fun _ _ ↦ cantorMetricSpace_dist_eq)]
  simp only [infoBits_bernoulliMeasure_cylinder p hp hp0 hp1]
  have h' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (∑ i ∈ Finset.range n, bitInfo p (x i)) / n)
      atTop (𝓝 (ENNReal.ofReal (crossEntropyBits q p))) := by
    refine (ENNReal.tendsto_ofReal hx).congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
    exact (ofReal_div_natCast hn).symm
  rw [h'.liminf_eq, h'.limsup_eq]

/-- Remark 7.2, last sentence, in the paper's pointwise form: for `0 < p, q < 1` and an oracle
`A` admissible for both `ν_p` and `ν_q`, at every `ν_q`-random point `x` (relative to `A`),
`Φ_{ν_q}(x) = (H(q), H(q))` and `Φ_{ν_p}(x) = (H(q‖p), H(q‖p))`. Only the admissibility for
`ν_q` is used: the frequency of ones of `x` tends to `q` (`bernRand_tendsto_freq`).
Blueprint node `meas:remarks`. -/
theorem localEntropy_bernoulliMeasure_eq_crossEntropy_of_mem_randomPoints
    (P : Presentation (ℕ → Bool)) (A : Set ℕ) (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p)
    (hp1 : p < 1) (q : ℝ≥0) (hq : q ≤ 1) (hq0 : 0 < q) (hq1 : q < 1)
    (_hAp : IsMeasureAdmissible P shiftMap (bernoulliMeasure p hp) A)
    (hAq : IsMeasureAdmissible P shiftMap (bernoulliMeasure q hq) A) {x : ℕ → Bool}
    (hx : x ∈ randomPoints P A (bernoulliMeasure q hq)) :
    localEntropy (bernoulliMeasure q hq) shiftMap x = (binEntropyBits q, binEntropyBits q) ∧
      localEntropy (bernoulliMeasure p hp) shiftMap x =
        (ENNReal.ofReal (crossEntropyBits q p), ENNReal.ofReal (crossEntropyBits q p)) := by
  have hfreq := bernRand_tendsto_freq P A q hq hAq hx
  refine ⟨?_, bernRand_localEntropy_of_tendsto p hp hp0 hp1 q hfreq⟩
  rw [bernRand_localEntropy_of_tendsto q hq hq0 hq1 q hfreq, crossEntropyBits_self]
  rfl

end Kolmogorov.PointToSet
