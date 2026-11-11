/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Pointwise
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# The universal measure and the dual principle (§6.3)

For an oracle `A` the universal measure is the purely atomic measure
`m^A = ∑_i 2^{-K^A(i)} δ_{x_i}` carried by the ideal points (Definition 6.11 of E. Dinowitz,
*Entropy of non-invariant measures and orbit complexity of random points*). Its total mass
lies in `(0, 1]`, and every Bowen ball of positive radius has positive mass.

* `universalMeasure_bowenBall_ge` and `orbitComplexityNat_le_of_lt_universalMeasure`
  (Proposition 6.12): `-log₂ m^A(B_n(x, T, ε)) ≤ K_n^A(x, T, ε)` and
  `K_n^A(x, T, 6ε) ≤ I + 2 log₂ n + 2 log₂ (I + 2) + c` with `I = -log₂ m^A(B_n(x, T, ε))`.
* `orbitComplexities_eq_localEntropy_universalMeasure`: consequently the orbit complexities
  are the local entropies of `m^A`, at every point of the space.
* `lowerEntropy_eq_iInf_measure`, `upperEntropy_eq_iInf_measure` (Corollary 6.14, the dual
  principle): the Bowen and packing entropies of an arbitrary set are the minima over Borel
  probability measures of the supremum over the set of the lower and upper local entropies;
  `exists_atomic_measure_lowerEntropy_eq` and `exists_atomic_measure_upperEntropy_eq` give a
  purely atomic minimizer.

Blueprint nodes `meas:universal`, `meas:dual`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The universal measure `m^A = ∑_i 2^{-K^A(i)} δ_{x_i}` of an oracle `A`
(Definition 6.11). Blueprint node `meas:universal`. -/
noncomputable def universalMeasure (P : Presentation X) (A : Set ℕ) : Measure X :=
  Measure.sum fun i : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i • Measure.dirac (P.ι i)

omit [BorelSpace X] in
/-- The universal measure of a measurable set is the sum of the weights of its ideal
points. -/
theorem universalMeasure_apply (P : Presentation X) (A : Set ℕ) {s : Set X}
    (hs : MeasurableSet s) :
    universalMeasure P A s =
      ∑' i : ℕ, s.indicator (fun _ ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i) (P.ι i) := by
  rw [universalMeasure, Measure.sum_apply _ hs]
  refine tsum_congr fun i ↦ ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  by_cases h : P.ι i ∈ s <;> simp [h]

omit [BorelSpace X] in
/-- The universal measure has total mass at most one. Blueprint node `meas:universal`. -/
theorem universalMeasure_univ_le_one (P : Presentation X) (A : Set ℕ) :
    universalMeasure P A univ ≤ 1 := by
  rw [universalMeasure_apply P A MeasurableSet.univ]
  simpa using oracle_kraft A

/-- The universal measure is finite. -/
instance instIsFiniteMeasureUniversalMeasure (P : Presentation X) (A : Set ℕ) :
    IsFiniteMeasure (universalMeasure P A) :=
  ⟨(universalMeasure_univ_le_one P A).trans_lt ENNReal.one_lt_top⟩

omit [BorelSpace X] in
/-- The universal measure is not the zero measure. -/
theorem universalMeasure_univ_ne_zero (P : Presentation X) (A : Set ℕ) :
    universalMeasure P A univ ≠ 0 := by
  rw [universalMeasure_apply P A MeasurableSet.univ]
  simp [ENNReal.tsum_eq_zero]

/-- The universal measure is carried by the countable set of ideal points.
Blueprint node `meas:universal`. -/
theorem universalMeasure_compl_range (P : Presentation X) (A : Set ℕ) :
    universalMeasure P A (range P.ι)ᶜ = 0 := by
  rw [universalMeasure_apply P A (countable_range P.ι).measurableSet.compl]
  simp

/-- Proposition 6.12, first inequality: `m^A(B_n(x, T, ε)) ≥ 2^{-K_n^A(x, T, ε)}`, that is,
`-log₂ m^A(B_n(x, T, ε)) ≤ K_n^A(x, T, ε)`. Blueprint node `meas:universal`. -/
theorem universalMeasure_bowenBall_ge (P : Presentation X) (T : X → X) (hT : Continuous T)
    (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ≥0∞)⁻¹ ^ orbitComplexityNat P T A x n ε ≤
      universalMeasure P A (bowenBall T n x ε) := by
  obtain ⟨i, hi, heq⟩ := entropiesAndOrbitComplexities_attained P T hT A x n hn ε hε
  rw [universalMeasure_apply P A (bowen_ball_dense_open T hT n x ε).measurableSet,
    orbitComplexityNat, heq, ENat.toNat_natCast]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum i)
  rw [indicator_of_mem hi]

/-- `2^{-K}` as an extended real. -/
private theorem ofReal_two_rpow_neg_natCast (K : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(K : ℝ))) = (2 : ℝ≥0∞)⁻¹ ^ K := by
  rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ENNReal.inv_pow]

/-! ### Computability of the universal measure -/

/-- The weight `2^{-k}` of an optional exponent `some k`, and `0` for `none`. -/
private def optWeight (o : Option ℕ) : ℚ :=
  Option.elim o 0 fun k ↦ (2 : ℚ)⁻¹ ^ k

/-- The total weight of a list of optional exponents. -/
private def listMass (ks : List (Option ℕ)) : ℚ :=
  ks.foldr (fun o s ↦ optWeight o + s) 0

/-- The weight of an optional exponent is computable. -/
private theorem computable_optWeight : Computable optWeight :=
  (Computable.option_casesOn Computable.id (Computable.const (0 : ℚ))
    (computable_pow_half.comp Computable.snd).to₂).of_eq fun o ↦ by cases o <;> rfl

/-- The total weight of a list of optional exponents is computable. -/
private theorem computable_listMass : Computable listMass :=
  Computable.list_foldr (h := fun _ p ↦ optWeight p.1 + p.2) Computable.id
    (Computable.const (0 : ℚ))
    (computable₂_ratAdd.comp (computable_optWeight.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂

/-- The weight of an optional exponent is nonnegative. -/
private theorem optWeight_nonneg (o : Option ℕ) : 0 ≤ optWeight o := by
  cases o <;> simp [optWeight]

/-- The weight of an optional exponent, as an extended real. -/
private theorem ofReal_optWeight (o : Option ℕ) :
    ENNReal.ofReal (optWeight o) = o.elim 0 fun k ↦ (2 : ℝ≥0∞)⁻¹ ^ k := by
  cases o with
  | none => simp [optWeight]
  | some k =>
    simp only [optWeight, Option.elim_some]
    push_cast
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- The total weight of a list is nonnegative. -/
private theorem listMass_nonneg (ks : List (Option ℕ)) : 0 ≤ listMass ks := by
  induction ks with
  | nil => simp [listMass]
  | cons o ks ih =>
    simp only [listMass, List.foldr_cons] at ih ⊢
    exact add_nonneg (optWeight_nonneg o) ih

/-- The total weight of a list as a finite sum of extended reals. -/
private theorem ofReal_listMass (ks : List (Option ℕ)) :
    ENNReal.ofReal (listMass ks) =
      ∑ i ∈ Finset.range ks.length, (ks.getD i none).elim 0 fun k ↦ (2 : ℝ≥0∞)⁻¹ ^ k := by
  induction ks with
  | nil => simp [listMass]
  | cons o ks ih =>
    have hcons : listMass (o :: ks) = optWeight o + listMass ks := rfl
    rw [hcons, Rat.cast_add, ENNReal.ofReal_add (by exact_mod_cast optWeight_nonneg o)
      (by exact_mod_cast listMass_nonneg ks), ih,
      ofReal_optWeight, List.length_cons, Finset.sum_range_succ', add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero]

/-- An entry of a certificate list for a lower bound on the universal measure of a finite
union of balls: either empty, or an upper bound `k` on `K^A(i)` for an ideal point `x_i` of the
union. -/
private def GoodEntry (P : Presentation X) (A : Set ℕ) (L : List (ℕ × ℚ)) (i : ℕ)
    (o : Option ℕ) : Prop :=
  o = none ∨ ∃ k : ℕ, o = some k ∧ (oracleNatComplexity A i : ℝ) < (((k + 1 : ℕ) : ℚ) : ℝ) ∧
    P.ι i ∈ ballUnion P L

omit [MeasurableSpace X] [BorelSpace X] in
/-- Finite unions of basic balls are open. -/
private theorem isOpen_ballUnion (P : Presentation X) (L : List (ℕ × ℚ)) :
    IsOpen (ballUnion P L) :=
  isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball

/-- A rational lies below the universal measure of a finite union of balls iff it lies below
the total weight of a certificate list. -/
private theorem lt_universalMeasure_ballUnion_iff (P : Presentation X) (A : Set ℕ)
    (L : List (ℕ × ℚ)) (q : ℚ) :
    (q : ℝ) < (universalMeasure P A (ballUnion P L)).toReal ↔
      ∃ ks : List (Option ℕ), (∀ k (h : k < ks.length), GoodEntry P A L k (ks.get ⟨k, h⟩)) ∧
        q < listMass ks := by
  classical
  have hU := (isOpen_ballUnion P L).measurableSet
  have hne : universalMeasure P A (ballUnion P L) ≠ ⊤ := measure_ne_top _ _
  constructor
  · intro hq
    rcases lt_or_ge q 0 with hq0 | hq0
    · exact ⟨[], fun k h ↦ absurd h (by simp), by simpa [listMass] using hq0⟩
    have hq' : ENNReal.ofReal q < universalMeasure P A (ballUnion P L) :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by exact_mod_cast hq0) hne).2 hq
    rw [universalMeasure_apply P A hU, ENNReal.tsum_eq_iSup_nat] at hq'
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 hq'
    let g : ℕ → Option ℕ := fun i ↦
      if P.ι i ∈ ballUnion P L then some (oracleNatComplexity A i) else none
    refine ⟨(List.range n).map g, fun k hk ↦ ?_, ?_⟩
    · simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, g]
      split_ifs with h
      · exact Or.inr ⟨_, rfl, by push_cast; exact lt_add_one _, h⟩
      · exact Or.inl rfl
    · have hsum : ENNReal.ofReal (listMass ((List.range n).map g)) =
          ∑ i ∈ Finset.range n, (ballUnion P L).indicator
            (fun _ ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i) (P.ι i) := by
        rw [ofReal_listMass, List.length_map, List.length_range]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
        by_cases h : P.ι i ∈ ballUnion P L <;> simp [g, h]
      rw [← hsum] at hn
      have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by exact_mod_cast hq0)).1 hn
      exact_mod_cast this
  · rintro ⟨ks, hgood, hq⟩
    have hle : ENNReal.ofReal (listMass ks) ≤ universalMeasure P A (ballUnion P L) := by
      rw [ofReal_listMass, universalMeasure_apply P A hU]
      refine le_trans (Finset.sum_le_sum fun i hi ↦ ?_) (ENNReal.sum_le_tsum _)
      have hi' : i < ks.length := Finset.mem_range.1 hi
      have h := hgood i hi'
      rw [List.get_eq_getElem] at h
      rw [List.getD_eq_getElem _ _ hi']
      rcases h with h | ⟨k, hk, hK, hmem⟩
      · simp [h]
      · rw [hk, Option.elim_some, indicator_of_mem hmem]
        have hK' : oracleNatComplexity A i < k + 1 := by exact_mod_cast hK
        exact pow_le_pow_of_le_one (by positivity) (ENNReal.inv_le_one.2 one_le_two)
          (Nat.lt_succ_iff.1 hK')
    have h2 := (ENNReal.ofReal_le_iff_le_toReal hne).1 hle
    exact lt_of_lt_of_le (by exact_mod_cast hq) h2

omit [MeasurableSpace X] [BorelSpace X] in
/-- Membership of ideal points in finite unions of basic balls is relatively enumerable in an
oracle computing the metric table, uniformly in the list and the index. -/
private theorem isREIn_mem_ballUnion (P : Presentation X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) :
    IsREIn A fun d : List (ℕ × ℚ) × ℕ ↦ P.ι d.2 ∈ ballUnion P d.1 := by
  have h1 : IsREIn A fun e : (List (ℕ × ℚ) × ℕ) × (ℕ × ℚ) ↦ e.2 ∈ e.1.1 := by
    have h : Computable fun e : (List (ℕ × ℚ) × ℕ) × (ℕ × ℚ) ↦
        decide (e.1.1.idxOf e.2 < e.1.1.length) :=
      (PrimrecPred.decide (Primrec.nat_lt.comp
        (Primrec.list_idxOf.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))).to_comp
    exact isREIn_of_computable_decide (h.of_eq fun e ↦ by simp only [List.idxOf_lt_length_iff])
  have h2 : IsREIn A fun e : (List (ℕ × ℚ) × ℕ) × (ℕ × ℚ) ↦ P.ι e.1.2 ∈ basicBall P e.2 :=
    (isREIn_mem_basicBall_of_names (ι := ℕ) hP (x := P.ι) (a := fun i _ ↦ i)
      (fun i ↦ isCauchyName_const P i) ComputableIn.fst).comp
      (f := fun e : (List (ℕ × ℚ) × ℕ) × (ℕ × ℚ) ↦ (e.1.2, e.2))
      ((Computable.snd.comp Computable.fst).pair Computable.snd).computableIn
  have heq : (fun d : List (ℕ × ℚ) × ℕ ↦ P.ι d.2 ∈ ballUnion P d.1) =
      fun d ↦ ∃ b, (d, b).2 ∈ (d, b).1.1 ∧ P.ι (d, b).1.2 ∈ basicBall P (d, b).2 := by
    funext d
    simp [ballUnion]
  rw [heq]
  exact (h1.and h2).exists

/-- The universal measure is computable relative to any oracle that computes the metric
table. Blueprint node `meas:universal`. -/
theorem isComputableMeasureIn_universalMeasure (P : Presentation X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) : IsComputableMeasureIn P A (universalMeasure P A) := by
  have hmem := isREIn_mem_ballUnion P A hP
  have hgood : IsREIn A fun d : List (ℕ × ℚ) × ℕ × Option ℕ ↦ GoodEntry P A d.1 d.2.1 d.2.2 := by
    have hnone : IsREIn A fun d : List (ℕ × ℚ) × ℕ × Option ℕ ↦ d.2.2 = none :=
      isREIn_of_computable_decide
        (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const none)).decide.to_comp
    have hsome : IsREIn A fun e : (List (ℕ × ℚ) × ℕ × Option ℕ) × ℕ ↦
        e.1.2.2 = some e.2 ∧
          ((oracleNatComplexity A e.1.2.1 : ℝ) < (((e.2 + 1 : ℕ) : ℚ) : ℝ) ∧
            P.ι e.1.2.1 ∈ ballUnion P e.1.1) := by
      refine IsREIn.and ?_ (IsREIn.and ?_ ?_)
      · exact isREIn_of_computable_decide (Primrec.eq.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.option_some.comp Primrec.snd)).decide.to_comp
      · exact (isREIn_oracleNatComplexity_lt A).comp
          (f := fun e : (List (ℕ × ℚ) × ℕ × Option ℕ) × ℕ ↦ (e.1.2.1, ((e.2 + 1 : ℕ) : ℚ)))
          ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
            (computable_nat_to_rat.comp (Computable.succ.comp Computable.snd))).computableIn
      · exact hmem.comp (f := fun e : (List (ℕ × ℚ) × ℕ × Option ℕ) × ℕ ↦ (e.1.1, e.1.2.1))
          ((Computable.fst.comp Computable.fst).pair
            (Computable.fst.comp (Computable.snd.comp Computable.fst))).computableIn
    exact hnone.or hsome.exists
  have hall := (hgood.list_forall_get).comp
    (f := fun e : (List (ℕ × ℚ) × ℚ) × List (Option ℕ) ↦ (e.1.1, e.2))
    ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
  have hlt : IsREIn A fun e : (List (ℕ × ℚ) × ℚ) × List (Option ℕ) ↦ e.1.2 < listMass e.2 :=
    isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.snd.comp Computable.fst)
      (computable_listMass.comp Computable.snd))
  have heq : (fun w : List (ℕ × ℚ) × ℚ ↦
      (w.2 : ℝ) < (universalMeasure P A (ballUnion P w.1)).toReal) = fun w ↦
      ∃ ks : List (Option ℕ), (∀ k (h : k < ks.length), GoodEntry P A w.1 k (ks.get ⟨k, h⟩)) ∧
        w.2 < listMass ks := by
    funext w
    exact propext (lt_universalMeasure_ballUnion_iff P A w.1 w.2)
  change IsREIn A fun w : List (ℕ × ℚ) × ℚ ↦
    (w.2 : ℝ) < (universalMeasure P A (ballUnion P w.1)).toReal
  rw [heq]
  exact (hall.and hlt).exists

/-- An oracle that computes the metric table and represents the dynamics is admissible for
its own universal measure. -/
theorem isMeasureAdmissible_universalMeasure (P : Presentation X) (T : X → X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) :
    IsMeasureAdmissible P T (universalMeasure P A) A :=
  ⟨hP, hTA, isComputableMeasureIn_universalMeasure P A hP⟩

/-- Proposition 6.12, second inequality: with any `k` such that
`2^{-k} < m^A(B_n(x, T, ε))`, `K_n^A(x, T, 6ε) ≤ k + 2 log₂ n + 2 log₂ (k + 1) + c`.
Blueprint node `meas:universal`. -/
theorem orbitComplexityNat_le_of_lt_universalMeasure (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (hP : ComputablePresentationIn P A)
    (hTA : IsRepresentedMapIn P P A T) (ε : ℚ) (hε : 0 < ε) :
    ∃ c : ℕ, ∀ (x : X) (n k : ℕ), 1 ≤ n →
      (2 : ℝ≥0∞)⁻¹ ^ k < universalMeasure P A (bowenBall T n x (ε : ℝ)) →
      (orbitComplexityNat P T A x n (6 * (ε : ℝ)) : ℝ) ≤
        k + 2 * Real.logb 2 n + 2 * Real.logb 2 (k + 1) + c :=
  coding_by_measure P T hT A (universalMeasure P A) (universalMeasure_univ_le_one P A)
    (isMeasureAdmissible_universalMeasure P T A hP hTA) ε hε

/-- Proposition 6.12: the orbit complexities relative to an oracle computing the metric table
and representing the dynamics are the local entropies of its universal measure, at every
point: `Ψ^A(x) = Φ_{m^A}(x)`. Blueprint node `meas:universal`. -/
theorem orbitComplexities_eq_localEntropy_universalMeasure (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (hP : ComputablePresentationIn P A)
    (hTA : IsRepresentedMapIn P P A T) (x : X) :
    orbitComplexities P T A x = localEntropy (universalMeasure P A) T x := by
  have hle := orbitComplexities_le_localEntropy P T hT A (universalMeasure P A)
    (universalMeasure_univ_le_one P A) (isMeasureAdmissible_universalMeasure P T A hP hTA) x
  have hrate : ∀ p : ℕ, ∀ᶠ n in atTop,
      localEntropyRate (universalMeasure P A) T x n (dyadicRadius p) ≤
        finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p) := by
    intro p
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [localEntropyRate, entropiesAndOrbitComplexities_rate P T hT A x n hn _
      (dyadicRadius_pos p)]
    gcongr
    calc infoBits (universalMeasure P A (bowenBall T n x (dyadicRadius p)))
        ≤ ENNReal.ofReal (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) := by
          refine infoBits_le_of_rpow_le (by positivity) ?_
          rw [ofReal_two_rpow_neg_natCast]
          exact universalMeasure_bowenBall_ge P T hT A x hn (dyadicRadius_pos p)
      _ = _ := ENNReal.ofReal_natCast _
  rw [orbitComplexities_eq_iSup_orbitComplexityAt] at hle ⊢
  refine Prod.ext (le_antisymm hle.1 (iSup_le fun p ↦ ?_)) (le_antisymm hle.2 (iSup_le fun p ↦ ?_))
  · exact (liminf_le_liminf (hrate p)).trans (le_iSup (fun p ↦
      (orbitComplexityAt P T A x (dyadicRadius p)).1) p)
  · exact (limsup_le_limsup (hrate p)).trans (le_iSup (fun p ↦
      (orbitComplexityAt P T A x (dyadicRadius p)).2) p)

/-! ### The dual principle (Corollary 6.14) -/

omit [BorelSpace X] in
/-- The normalized universal measure of an oracle is a probability measure. -/
private theorem isProbabilityMeasure_normalized (P : Presentation X) (A : Set ℕ) :
    IsProbabilityMeasure ((universalMeasure P A univ)⁻¹ • universalMeasure P A) := by
  have h0 := universalMeasure_univ_ne_zero P A
  have htop := measure_ne_top (universalMeasure P A) univ
  exact ⟨by simp [Measure.smul_apply, ENNReal.inv_mul_cancel h0 htop]⟩

/-- The normalized universal measure of an admissible oracle realizes the orbit complexities
as local entropies, and is carried by the ideal points. -/
private theorem exists_admissible_normalized (P : Presentation X) (T : X → X) (hT : Continuous T)
    (B : Set ℕ) :
    ∃ A : Set ℕ, charOracle B ≤ᵀ charOracle A ∧ ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      (∃ S : Set X, S.Countable ∧ μ Sᶜ = 0) ∧
      ∀ x, orbitComplexities P T A x = localEntropy μ T x := by
  obtain ⟨C, hC⟩ := exists_admissible_base P T hT (fun j : Fin 0 ↦ j.elim0) (fun j ↦ j.elim0)
  have hAd := hC (oracleJoin B C) (oracle_joins_right B C)
  have h0 := universalMeasure_univ_ne_zero P (oracleJoin B C)
  have htop := measure_ne_top (universalMeasure P (oracleJoin B C)) univ
  refine ⟨oracleJoin B C, oracle_joins B C,
    (universalMeasure P (oracleJoin B C) univ)⁻¹ • universalMeasure P (oracleJoin B C),
    isProbabilityMeasure_normalized P _,
    ⟨range P.ι, countable_range _, ?_⟩, fun x ↦ ?_⟩
  · simp [Measure.smul_apply, universalMeasure_compl_range]
  · rw [localEntropy_smul _ T x (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0)]
    exact orbitComplexities_eq_localEntropy_universalMeasure P T hT _ hAd.1 hAd.2.1 x

/-- Corollary 6.14, lower entropy, attainment: there is a purely atomic Borel probability
measure whose lower local entropy has supremum over `Z` equal to the Bowen entropy of `Z`.
Blueprint node `meas:dual`. -/
theorem exists_atomic_measure_lowerEntropy_eq (P : Presentation X) (T : X → X)
    (hT : Continuous T) (Z : Set X) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ (∃ S : Set X, S.Countable ∧ μ Sᶜ = 0) ∧
      lowerEntropy T Z = ⨆ x ∈ Z, (localEntropy μ T x).1 := by
  obtain ⟨B, hB⟩ := entropy_effectiveCharacterization_allOracles_cone P T hT Z
  obtain ⟨A, hBA, μ, hμ, hS, heq⟩ := exists_admissible_normalized P T hT B
  refine ⟨μ, hμ, hS, ?_⟩
  rw [hB A hBA]
  exact iSup_congr fun x ↦ iSup_congr fun _ ↦ by rw [heq x]

/-- Corollary 6.14, upper entropy, attainment: there is a purely atomic Borel probability
measure whose upper local entropy has supremum over `Z` equal to the packing entropy of `Z`.
Blueprint node `meas:dual`. -/
theorem exists_atomic_measure_upperEntropy_eq (P : Presentation X) (T : X → X)
    (hT : Continuous T) (Z : Set X) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ (∃ S : Set X, S.Countable ∧ μ Sᶜ = 0) ∧
      upperEntropy P T Z = ⨆ x ∈ Z, (localEntropy μ T x).2 := by
  obtain ⟨B, hB⟩ := upperEntropy_pointToSet_cone P T hT Z
  obtain ⟨A, hBA, μ, hμ, hS, heq⟩ := exists_admissible_normalized P T hT B
  refine ⟨μ, hμ, hS, ?_⟩
  rw [hB A hBA]
  exact iSup_congr fun x ↦ iSup_congr fun _ ↦ by rw [heq x]

/-- Corollary 6.14 (dual principle), lower entropy: the Bowen entropy of an arbitrary set is
the minimum over Borel probability measures of the supremum over the set of the lower local
entropy, `h̲(Z, T) = min_μ sup_{x ∈ Z} h̲_μ(T, x)`. Blueprint node `meas:dual`. -/
theorem lowerEntropy_eq_iInf_measure (P : Presentation X) (T : X → X) (hT : Continuous T)
    (Z : Set X) :
    lowerEntropy T Z =
      ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ), ⨆ x ∈ Z, (localEntropy μ T x).1 := by
  refine le_antisymm (le_iInf₂ fun μ hμ ↦ ?_) ?_
  · exact lowerEntropy_le_of_localEntropy_le P T hT μ Z _ fun x hx ↦
      le_iSup₂ (f := fun x _ ↦ (localEntropy μ T x).1) x hx
  · obtain ⟨μ, hμ, -, heq⟩ := exists_atomic_measure_lowerEntropy_eq P T hT Z
    exact iInf₂_le_of_le μ hμ heq.ge

/-- Corollary 6.14 (dual principle), upper entropy: the packing entropy of an arbitrary set
is the minimum over Borel probability measures of the supremum over the set of the upper local
entropy, `h̄(Z, T) = min_μ sup_{x ∈ Z} h̄_μ(T, x)`. Blueprint node `meas:dual`. -/
theorem upperEntropy_eq_iInf_measure (P : Presentation X) (T : X → X) (hT : Continuous T)
    (Z : Set X) :
    upperEntropy P T Z =
      ⨅ (μ : Measure X) (_ : IsProbabilityMeasure μ), ⨆ x ∈ Z, (localEntropy μ T x).2 := by
  refine le_antisymm (le_iInf₂ fun μ hμ ↦ ?_) ?_
  · exact upperEntropy_le_of_localEntropy_le P T hT μ Z _ fun x hx ↦
      le_iSup₂ (f := fun x _ ↦ (localEntropy μ T x).2) x hx
  · obtain ⟨μ, hμ, -, heq⟩ := exists_atomic_measure_upperEntropy_eq P T hT Z
    exact iInf₂_le_of_le μ hμ heq.ge

end Kolmogorov.PointToSet
