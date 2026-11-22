/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.UniversalMeasure
import KolmogorovMathlib.PointToSet.Measure.Ergodic.WordRandomness
import KolmogorovMathlib.Oracle.PrefixComplexity.Conditional

/-!
# The universal measure of a cylinder and the complexity of the word (Remark 6.6)

On Cantor space `ℕ → Bool` with the metric `cantorMetricSpace`, for a presentation `P` whose
ideal points have `A`-computable bits, the information of a cylinder under the universal measure
`m^A = ∑_i 2^{-K^A(i)} δ_{x_i}` is the prefix complexity of the word up to `O(log |w|)`:

* `umWords_infoBits_le_oracleComplexity` (upper bound, `-log₂ m^A[w] ≤ K^A(w) + O(1)`): an ideal
  point of `[w]` is found from `w` by an `A`-computable search, so its index `i_w` has
  `K^A(i_w) ≤ K^A(w) + O(1)`, and `m^A[w] ≥ 2^{-K^A(i_w)}`.
* `umWords_oracleComplexity_le_kmin` (private; lower bound, `K^A(w) ≤ k_w + K^A(|w|) + O(1)`
  with `k_w` the least `k` such that `2^{-k} < m^A[w]`): the cost `w ↦ k_w + K^A(|w|)` is `A`-upper
  semicomputable (the rational lower cut of `w ↦ m^A[w]` is `A`-r.e.) and its exponential mass is
  at most `∑_i 2^{-K^A(i)} ∑_n 2^{-K^A(n)} ≤ 1`, so the coding theorem
  `oracle_coding_finite_mass` applies.
* `abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le'`: the combination,
  `|-log₂ m^A[x↾n] - K^A(x↾n)| ≤ c log₂ n + c` for `n ≥ 1`.

Blueprint node `meas:remarks`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

section cantor

attribute [local instance] cantorMetricSpace

/-! ### Word cylinders on Cantor space -/

/-- The cylinder of a word is the cylinder of any of its extensions at the word's length. -/
private lemma umWords_listCylinder_eq (w : List Bool) :
    listCylinder w = PiNat.cylinder (fun i ↦ w.getD i false) w.length := by
  ext y
  simp only [listCylinder, PiNat.mem_cylinder_iff, mem_ofPred_eq]
  refine ⟨fun h i hi ↦ ?_, fun h i hi ↦ ?_⟩
  · rw [h i hi, List.getD_eq_getElem _ _ hi]
  · rw [h i hi, List.getD_eq_getElem _ _ hi]

/-- The cylinder `[x↾n]` is the cylinder of the word `cantorPrefix x n`. -/
lemma umWords_cylinder_eq_listCylinder (x : ℕ → Bool) (n : ℕ) :
    PiNat.cylinder x n = listCylinder (cantorPrefix x n) :=
  (listCylinder_wordPrefix x n).symm

/-- Word cylinders are open in Cantor space. -/
private lemma umWords_isOpen_listCylinder (w : List Bool) : IsOpen (listCylinder w) := by
  rw [umWords_listCylinder_eq]
  exact PiNat.isOpen_cylinder (E := fun _ : ℕ ↦ Bool) _ _

/-- Word cylinders are nonempty. -/
private lemma umWords_listCylinder_nonempty (w : List Bool) : (listCylinder w).Nonempty := by
  refine ⟨fun i ↦ w.getD i false, ?_⟩
  rw [umWords_listCylinder_eq]
  exact PiNat.self_mem_cylinder _ _

/-- A sequence lies in the cylinder of a word iff the word is its prefix of that length. -/
private lemma umWords_mem_listCylinder_iff (y : ℕ → Bool) (w : List Bool) :
    y ∈ listCylinder w ↔ w = wordPrefix y w.length := by
  constructor
  · intro h
    refine List.ext_getElem (by simp [wordPrefix]) fun i h1 h2 ↦ ?_
    simp [wordPrefix, h i h1]
  · intro h
    rw [h]
    exact mem_listCylinder_wordPrefix y _

/-- Membership of an ideal point in a word cylinder is `A`-r.e. (in fact `A`-decidable) when
the symbols of the ideal points are `A`-computable (any alphabet). -/
private lemma umWords_isREIn_mem_gen {α : Type*} [Primcodable α] {A : Set ℕ} {ι : ℕ → ℕ → α}
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ ι q.1 q.2) :
    IsREIn A fun d : ℕ × List α ↦ ι d.1 ∈ listCylinder d.2 := by
  classical
  have hF : IsREIn A fun d : ℕ × ℕ × α ↦ ι d.1 d.2.1 = d.2.2 := by
    refine isREIn_of_computableIn_decide A _ ?_
    have h1 : ComputableIn {charOracle A} fun d : ℕ × ℕ × α ↦ ι d.1 d.2.1 :=
      hP.comp (ComputableIn.fst.pair (ComputableIn.fst.comp ComputableIn.snd))
    have h2 : ComputableIn {charOracle A} fun d : ℕ × ℕ × α ↦ d.2.2 :=
      ComputableIn.snd.comp ComputableIn.snd
    exact (Primrec.eq.decide.to_comp.computableIn).comp (h1.pair h2)
  have h := hF.list_forall_get
  convert h using 2 with d
  simp [listCylinder]

/-- Membership of an ideal point in a word cylinder is `A`-r.e. when the bits of the ideal
points are `A`-computable. -/
private lemma umWords_isREIn_mem {P : Presentation (ℕ → Bool)} {A : Set ℕ}
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    IsREIn A fun d : ℕ × List Bool ↦ P.ι d.1 ∈ listCylinder d.2 :=
  umWords_isREIn_mem_gen (ι := P.ι) hP

/-- An `A`-computable choice of an ideal point in each word cylinder. -/
private lemma umWords_exists_choice (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    ∃ f : List Bool → ℕ, ComputableIn {charOracle A} f ∧ ∀ w, P.ι (f w) ∈ listCylinder w := by
  have hG : IsREIn A fun p : List Bool × ℕ ↦ P.ι p.2 ∈ listCylinder p.1 :=
    (umWords_isREIn_mem hP).comp (Computable.snd.pair Computable.fst).computableIn
  refine hG.exists_computableIn_choice fun w ↦ ?_
  exact P.dense.exists_mem_open (umWords_isOpen_listCylinder w)
    (umWords_listCylinder_nonempty w)

/-! ### The upper bound -/

/-- An ideal point of a word cylinder bounds its universal mass from below. -/
private lemma umWords_le_universalMeasure (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    {w : List Bool} {i : ℕ} (hi : P.ι i ∈ listCylinder w) :
    (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i ≤ universalMeasure P A (listCylinder w) := by
  rw [universalMeasure_apply P A (umWords_isOpen_listCylinder w).measurableSet]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum i)
  rw [indicator_of_mem hi]

/-- Every word cylinder has positive universal mass. -/
private lemma umWords_universalMeasure_ne_zero (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (w : List Bool) : universalMeasure P A (listCylinder w) ≠ 0 := by
  obtain ⟨i, hi⟩ := P.dense.exists_mem_open (umWords_isOpen_listCylinder w)
    (umWords_listCylinder_nonempty w)
  exact (lt_of_lt_of_le (ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) _)
    (umWords_le_universalMeasure P A hi)).ne'

/-- The universal mass of a word cylinder is at most one. -/
private lemma umWords_universalMeasure_le_one (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (w : List Bool) : universalMeasure P A (listCylinder w) ≤ 1 :=
  (measure_mono (subset_univ _)).trans (universalMeasure_univ_le_one P A)

/-- Upper bound of Remark 6.6 on words: `-log₂ m^A[w] ≤ K^A(w) + O(1)`. -/
theorem umWords_infoBits_le_oracleComplexity (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    ∃ c : ℕ, ∀ w : List Bool,
      (infoBits (universalMeasure P A (listCylinder w))).toReal ≤ oracleComplexity A w + c := by
  obtain ⟨f, hf, hfw⟩ := umWords_exists_choice P A hP
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_map_le_of_computableIn A (fun w ↦ natBits (f w))
    (natBits_computable.computableIn.comp hf)
  refine ⟨c, fun w ↦ ?_⟩
  have hK : oracleNatComplexity A (f w) ≤ oracleComplexity A w + c := hc w []
  have hinfo : infoBits (universalMeasure P A (listCylinder w)) ≤
      ENNReal.ofReal (oracleNatComplexity A (f w) : ℝ) := by
    refine infoBits_le_of_rpow_le (Nat.cast_nonneg _) ?_
    rw [ofReal_two_rpow_neg_natCast]
    exact umWords_le_universalMeasure P A (hfw w)
  have h1 := ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg _) hinfo
  have h2 : (oracleNatComplexity A (f w) : ℝ) ≤ (oracleComplexity A w : ℝ) + c := by
    exact_mod_cast hK
  linarith

/-! ### The rational lower cut of the universal mass of a word cylinder -/

/-- The weight `2^{-k}` of an optional exponent `some k`, and `0` for `none`. -/
private def umWords_optWeight (o : Option ℕ) : ℚ :=
  Option.elim o 0 fun k ↦ (2 : ℚ)⁻¹ ^ k

/-- The total weight of a list of optional exponents. -/
private def umWords_listMass (ks : List (Option ℕ)) : ℚ :=
  ks.foldr (fun o s ↦ umWords_optWeight o + s) 0

/-- The weight of an optional exponent is computable. -/
private lemma umWords_computable_optWeight : Computable umWords_optWeight :=
  (Computable.option_casesOn Computable.id (Computable.const (0 : ℚ))
    (computable_pow_half.comp Computable.snd).to₂).of_eq fun o ↦ by cases o <;> rfl

/-- The total weight of a list of optional exponents is computable. -/
private lemma umWords_computable_listMass : Computable umWords_listMass :=
  Computable.list_foldr (h := fun _ p ↦ umWords_optWeight p.1 + p.2) Computable.id
    (Computable.const (0 : ℚ))
    (computable₂_ratAdd.comp
      (umWords_computable_optWeight.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂

/-- The weight of an optional exponent is nonnegative. -/
private lemma umWords_optWeight_nonneg (o : Option ℕ) : 0 ≤ umWords_optWeight o := by
  cases o <;> simp [umWords_optWeight]

/-- The weight of an optional exponent, as an extended real. -/
private lemma umWords_ofReal_optWeight (o : Option ℕ) :
    ENNReal.ofReal (umWords_optWeight o) = o.elim 0 fun k ↦ (2 : ℝ≥0∞)⁻¹ ^ k := by
  cases o with
  | none => simp [umWords_optWeight]
  | some k =>
    simp only [umWords_optWeight, Option.elim_some]
    push_cast
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- The total weight of a list is nonnegative. -/
private lemma umWords_listMass_nonneg (ks : List (Option ℕ)) : 0 ≤ umWords_listMass ks := by
  induction ks with
  | nil => simp [umWords_listMass]
  | cons o ks ih =>
    simp only [umWords_listMass, List.foldr_cons] at ih ⊢
    exact add_nonneg (umWords_optWeight_nonneg o) ih

/-- The total weight of a list as a finite sum of extended reals. -/
private lemma umWords_ofReal_listMass (ks : List (Option ℕ)) :
    ENNReal.ofReal (umWords_listMass ks) =
      ∑ i ∈ Finset.range ks.length, (ks.getD i none).elim 0 fun k ↦ (2 : ℝ≥0∞)⁻¹ ^ k := by
  induction ks with
  | nil => simp [umWords_listMass]
  | cons o ks ih =>
    have hcons : umWords_listMass (o :: ks) = umWords_optWeight o + umWords_listMass ks := rfl
    rw [hcons, Rat.cast_add, ENNReal.ofReal_add (by exact_mod_cast umWords_optWeight_nonneg o)
      (by exact_mod_cast umWords_listMass_nonneg ks), ih,
      umWords_ofReal_optWeight, List.length_cons, Finset.sum_range_succ', add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero]

/-- An entry of a certificate list for a lower bound on the universal mass of the cylinder of
`w`: either empty, or an upper bound `k` on `K^A(i)` for an ideal point `x_i ∈ [w]`. -/
private def UmWordsGoodEntry (P : Presentation (ℕ → Bool)) (A : Set ℕ) (w : List Bool) (i : ℕ)
    (o : Option ℕ) : Prop :=
  o = none ∨ ∃ k : ℕ, o = some k ∧ (oracleNatComplexity A i : ℝ) < (((k + 1 : ℕ) : ℚ) : ℝ) ∧
    P.ι i ∈ listCylinder w

/-- A rational lies below the universal mass of a word cylinder iff it lies below the total
weight of a certificate list. -/
private lemma umWords_lt_universalMeasure_iff (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (w : List Bool) (q : ℚ) :
    (q : ℝ) < (universalMeasure P A (listCylinder w)).toReal ↔
      ∃ ks : List (Option ℕ),
        (∀ k (h : k < ks.length), UmWordsGoodEntry P A w k (ks.get ⟨k, h⟩)) ∧
        q < umWords_listMass ks := by
  classical
  have hU := (umWords_isOpen_listCylinder w).measurableSet
  have hne : universalMeasure P A (listCylinder w) ≠ ⊤ := measure_ne_top _ _
  constructor
  · intro hq
    rcases lt_or_ge q 0 with hq0 | hq0
    · exact ⟨[], fun k h ↦ absurd h (by simp), by simpa [umWords_listMass] using hq0⟩
    have hq' : ENNReal.ofReal q < universalMeasure P A (listCylinder w) :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by exact_mod_cast hq0) hne).2 hq
    rw [universalMeasure_apply P A hU, ENNReal.tsum_eq_iSup_nat] at hq'
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 hq'
    let g : ℕ → Option ℕ := fun i ↦
      if P.ι i ∈ listCylinder w then some (oracleNatComplexity A i) else none
    refine ⟨(List.range n).map g, fun k hk ↦ ?_, ?_⟩
    · simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, g]
      split_ifs with h
      · exact Or.inr ⟨_, rfl, by push_cast; exact lt_add_one _, h⟩
      · exact Or.inl rfl
    · have hsum : ENNReal.ofReal (umWords_listMass ((List.range n).map g)) =
          ∑ i ∈ Finset.range n, (listCylinder w).indicator
            (fun _ ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i) (P.ι i) := by
        rw [umWords_ofReal_listMass, List.length_map, List.length_range]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
        by_cases h : P.ι i ∈ listCylinder w <;> simp [g, h]
      rw [← hsum] at hn
      have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by exact_mod_cast hq0)).1 hn
      exact_mod_cast this
  · rintro ⟨ks, hgood, hq⟩
    have hle : ENNReal.ofReal (umWords_listMass ks) ≤ universalMeasure P A (listCylinder w) := by
      rw [umWords_ofReal_listMass, universalMeasure_apply P A hU]
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

/-- The rational lower cut of `w ↦ m^A[w]` is `A`-r.e.: the universal mass of word cylinders is
`A`-lower semicomputable. -/
theorem umWords_isREIn_lt_universalMeasure (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    IsREIn A fun d : List Bool × ℚ ↦
      (d.2 : ℝ) < (universalMeasure P A (listCylinder d.1)).toReal := by
  have hmem : IsREIn A fun d : List Bool × ℕ ↦ P.ι d.2 ∈ listCylinder d.1 :=
    (umWords_isREIn_mem hP).comp (Computable.snd.pair Computable.fst).computableIn
  have hgood : IsREIn A fun d : List Bool × ℕ × Option ℕ ↦
      UmWordsGoodEntry P A d.1 d.2.1 d.2.2 := by
    have hnone : IsREIn A fun d : List Bool × ℕ × Option ℕ ↦ d.2.2 = none :=
      isREIn_of_computable_decide
        (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const none)).decide.to_comp
    have hsome : IsREIn A fun e : (List Bool × ℕ × Option ℕ) × ℕ ↦
        e.1.2.2 = some e.2 ∧
          ((oracleNatComplexity A e.1.2.1 : ℝ) < (((e.2 + 1 : ℕ) : ℚ) : ℝ) ∧
            P.ι e.1.2.1 ∈ listCylinder e.1.1) := by
      refine IsREIn.and ?_ (IsREIn.and ?_ ?_)
      · exact isREIn_of_computable_decide (Primrec.eq.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.option_some.comp Primrec.snd)).decide.to_comp
      · exact (isREIn_oracleNatComplexity_lt A).comp
          (f := fun e : (List Bool × ℕ × Option ℕ) × ℕ ↦ (e.1.2.1, ((e.2 + 1 : ℕ) : ℚ)))
          ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
            (computable_nat_to_rat.comp (Computable.succ.comp Computable.snd))).computableIn
      · exact hmem.comp (f := fun e : (List Bool × ℕ × Option ℕ) × ℕ ↦ (e.1.1, e.1.2.1))
          ((Computable.fst.comp Computable.fst).pair
            (Computable.fst.comp (Computable.snd.comp Computable.fst))).computableIn
    exact hnone.or hsome.exists
  have hall := (hgood.list_forall_get).comp
    (f := fun e : (List Bool × ℚ) × List (Option ℕ) ↦ (e.1.1, e.2))
    ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
  have hlt : IsREIn A fun e : (List Bool × ℚ) × List (Option ℕ) ↦
      e.1.2 < umWords_listMass e.2 :=
    isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.snd.comp Computable.fst)
      (umWords_computable_listMass.comp Computable.snd))
  have heq : (fun d : List Bool × ℚ ↦
      (d.2 : ℝ) < (universalMeasure P A (listCylinder d.1)).toReal) = fun d ↦
      ∃ ks : List (Option ℕ),
        (∀ k (h : k < ks.length), UmWordsGoodEntry P A d.1 k (ks.get ⟨k, h⟩)) ∧
        d.2 < umWords_listMass ks := by
    funext d
    exact propext (umWords_lt_universalMeasure_iff P A d.1 d.2)
  rw [heq]
  exact (hall.and hlt).exists

/-! ### The lower bound -/

/-- Some power `2^{-k}` lies below the universal mass of a word cylinder. -/
private lemma umWords_exists_pow_lt (P : Presentation (ℕ → Bool)) (A : Set ℕ) (w : List Bool) :
    ∃ k : ℕ, (2 : ℝ)⁻¹ ^ k < (universalMeasure P A (listCylinder w)).toReal :=
  exists_pow_lt_of_lt_one
    (ENNReal.toReal_pos (umWords_universalMeasure_ne_zero P A w) (measure_ne_top _ _))
    (by norm_num)

open Classical in
/-- The least `k` with `2^{-k} < m^A[w]`. -/
private noncomputable def umWords_kmin (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (w : List Bool) : ℕ :=
  Nat.find (umWords_exists_pow_lt P A w)

open Classical in
/-- `2^{-k_w} < m^A[w]`. -/
private lemma umWords_kmin_spec (P : Presentation (ℕ → Bool)) (A : Set ℕ) (w : List Bool) :
    (2 : ℝ)⁻¹ ^ umWords_kmin P A w < (universalMeasure P A (listCylinder w)).toReal :=
  Nat.find_spec (umWords_exists_pow_lt P A w)

open Classical in
/-- `k_w` is least. -/
private lemma umWords_kmin_le_of (P : Presentation (ℕ → Bool)) (A : Set ℕ) (w : List Bool)
    {k : ℕ} (hk : (2 : ℝ)⁻¹ ^ k < (universalMeasure P A (listCylinder w)).toReal) :
    umWords_kmin P A w ≤ k :=
  Nat.find_min' (umWords_exists_pow_lt P A w) hk

open Classical in
/-- Below `k_w` the power is not below the mass. -/
private lemma umWords_not_lt_of_lt_kmin (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (w : List Bool) {k : ℕ} (hk : k < umWords_kmin P A w) :
    ¬ (2 : ℝ)⁻¹ ^ k < (universalMeasure P A (listCylinder w)).toReal :=
  Nat.find_min (umWords_exists_pow_lt P A w) hk

/-- `k_w ≤ -log₂ m^A[w] + 1`. -/
private lemma umWords_kmin_le_infoBits (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (w : List Bool) :
    (umWords_kmin P A w : ℝ) ≤ (infoBits (universalMeasure P A (listCylinder w))).toReal + 1 := by
  rcases Nat.eq_zero_or_eq_succ_pred (umWords_kmin P A w) with h0 | hk
  · rw [h0, Nat.cast_zero]
    linarith [ENNReal.toReal_nonneg (a := infoBits (universalMeasure P A (listCylinder w)))]
  set k := (umWords_kmin P A w).pred
  have hlt : k < umWords_kmin P A w := by omega
  have hle := not_lt.1 (umWords_not_lt_of_lt_kmin P A w hlt)
  have hpos : 0 < (universalMeasure P A (listCylinder w)).toReal :=
    ENNReal.toReal_pos (umWords_universalMeasure_ne_zero P A w) (measure_ne_top _ _)
  have hlog := Real.logb_le_logb_of_le one_lt_two hpos hle
  rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one one_lt_two] at hlog
  rw [toReal_infoBits (umWords_universalMeasure_ne_zero P A w)
    (umWords_universalMeasure_le_one P A w), hk]
  push_cast
  linarith

/-- `2^{-k_w} ≤ m^A[w]` as extended reals. -/
private lemma umWords_pow_kmin_le (P : Presentation (ℕ → Bool)) (A : Set ℕ) (w : List Bool) :
    (2 : ℝ≥0∞)⁻¹ ^ umWords_kmin P A w ≤ universalMeasure P A (listCylinder w) := by
  have h := (umWords_kmin_spec P A w).le
  have h2 := ENNReal.ofReal_le_ofReal h
  rwa [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat] at h2

/-- For an ideal point `y`, the words whose cylinder contains `y`, weighted by
`2^{-K^A(|w|)}`, have total weight at most one. -/
private lemma umWords_tsum_mem_le (A : Set ℕ) (y : ℕ → Bool) :
    ∑' w : List Bool, {w : List Bool | y ∈ listCylinder w}.indicator
      (fun w ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A w.length) w ≤ 1 := by
  have hinj : Function.Injective (wordPrefix y) := by
    intro n m h
    have := congrArg List.length h
    simpa [wordPrefix] using this
  rw [← hinj.tsum_eq]
  · have h : ∀ n, {w : List Bool | y ∈ listCylinder w}.indicator
        (fun w ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A w.length) (wordPrefix y n) =
        (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A n := fun n ↦ by
      rw [indicator_of_mem (show wordPrefix y n ∈ {w : List Bool | y ∈ listCylinder w} from
        mem_listCylinder_wordPrefix y n)]
      simp [wordPrefix]
    simp only [h]
    simpa using oracle_kraft A
  · intro w hw
    have hmem : y ∈ listCylinder w := by
      by_contra h
      exact hw (indicator_of_notMem (show w ∉ {w : List Bool | y ∈ listCylinder w} from h) _)
    exact ⟨w.length, ((umWords_mem_listCylinder_iff y w).1 hmem).symm⟩

/-- The exponential mass of the cost `k_w + K^A(|w|)` is at most one. -/
private lemma umWords_mass_le_one (P : Presentation (ℕ → Bool)) (A : Set ℕ) :
    ∑' w : List Bool, (2 : ℝ≥0∞)⁻¹ ^ (umWords_kmin P A w + oracleNatComplexity A w.length) ≤
      1 := by
  have hpt : ∀ w : List Bool,
      (2 : ℝ≥0∞)⁻¹ ^ (umWords_kmin P A w + oracleNatComplexity A w.length) ≤
        ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i *
          {w : List Bool | P.ι i ∈ listCylinder w}.indicator
            (fun w ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A w.length) w := by
    intro w
    rw [pow_add]
    calc (2 : ℝ≥0∞)⁻¹ ^ umWords_kmin P A w * (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A w.length
        ≤ universalMeasure P A (listCylinder w) *
            (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A w.length := by
          gcongr
          exact umWords_pow_kmin_le P A w
      _ = _ := by
          rw [universalMeasure_apply P A (umWords_isOpen_listCylinder w).measurableSet,
            ← ENNReal.tsum_mul_right]
          refine tsum_congr fun i ↦ ?_
          by_cases h : P.ι i ∈ listCylinder w <;> simp [h]
  calc ∑' w : List Bool, (2 : ℝ≥0∞)⁻¹ ^ (umWords_kmin P A w + oracleNatComplexity A w.length)
      ≤ ∑' w : List Bool, ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i *
          {w : List Bool | P.ι i ∈ listCylinder w}.indicator
            (fun w ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A w.length) w := ENNReal.tsum_le_tsum hpt
    _ = ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i * ∑' w : List Bool,
          {w : List Bool | P.ι i ∈ listCylinder w}.indicator
            (fun w ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A w.length) w := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun i ↦ ENNReal.tsum_mul_left
    _ ≤ ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i * 1 :=
        ENNReal.tsum_le_tsum fun i ↦ by gcongr; exact umWords_tsum_mem_le A (P.ι i)
    _ ≤ 1 := by simpa using oracle_kraft A

/-- Lower bound of Remark 6.6 on words: `K^A(w) ≤ k_w + K^A(|w|) + O(1)`, by the coding
theorem for the `A`-upper semicomputable cost `w ↦ k_w + K^A(|w|)`. -/
private lemma umWords_oracleComplexity_le_kmin (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    ∃ c : ℕ, ∀ w : List Bool, (oracleComplexity A w : ℝ) ≤
      umWords_kmin P A w + oracleNatComplexity A w.length + c := by
  let F : BitString → Prop := fun _ ↦ True
  let g : Subtype F → ℝ := fun w ↦
    ((umWords_kmin P A w.1 + oracleNatComplexity A w.1.length : ℕ) : ℝ)
  have hcut := umWords_isREIn_lt_universalMeasure P A hP
  let U : List Bool × ℚ → Prop := fun d ↦ ∃ k : ℕ,
    (((2 : ℚ)⁻¹ ^ k : ℚ) : ℝ) < (universalMeasure P A (listCylinder d.1)).toReal ∧
      (oracleNatComplexity A d.1.length : ℝ) < ((d.2 - k : ℚ) : ℝ)
  have hU : IsREIn A U := by
    have h1 : IsREIn A fun e : (List Bool × ℚ) × ℕ ↦
        (((2 : ℚ)⁻¹ ^ e.2 : ℚ) : ℝ) < (universalMeasure P A (listCylinder e.1.1)).toReal :=
      hcut.comp (f := fun e : (List Bool × ℚ) × ℕ ↦ (e.1.1, (2 : ℚ)⁻¹ ^ e.2))
        ((Computable.fst.comp Computable.fst).pair
          (computable_pow_half.comp Computable.snd)).computableIn
    have h2 : IsREIn A fun e : (List Bool × ℚ) × ℕ ↦
        (oracleNatComplexity A e.1.1.length : ℝ) < ((e.1.2 - e.2 : ℚ) : ℝ) :=
      (isREIn_oracleNatComplexity_lt A).comp
        (f := fun e : (List Bool × ℚ) × ℕ ↦ (e.1.1.length, e.1.2 - (e.2 : ℚ)))
        ((Primrec.list_length.to_comp.comp (Computable.fst.comp Computable.fst)).pair
          (computable₂_ratSub.comp (Computable.snd.comp Computable.fst)
            (computable_nat_to_rat.comp Computable.snd))).computableIn
    exact (h1.and h2).exists
  have hg : IsUpperSemicomputableOnIn A F g := by
    refine ⟨U, hU, fun w q ⟨k, hk1, hk2⟩ ↦ ⟨trivial, ?_⟩, fun w ε hε ↦ ?_⟩
    · have hk1' : (2 : ℝ)⁻¹ ^ k < (universalMeasure P A (listCylinder w)).toReal := by
        dsimp only at hk1
        push_cast at hk1
        exact hk1
      have hle := umWords_kmin_le_of P A w hk1'
      have hle' : (umWords_kmin P A w : ℝ) ≤ k := by exact_mod_cast hle
      change ((umWords_kmin P A w + oracleNatComplexity A w.length : ℕ) : ℝ) < q
      push_cast at hk2 ⊢
      linarith
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (g w) hε)
      refine ⟨q, ⟨umWords_kmin P A w.1, ?_, ?_⟩, hq2⟩
      · dsimp only
        push_cast
        exact umWords_kmin_spec P A w.1
      · simp only [g] at hq1
        push_cast at hq1 ⊢
        linarith
  have hM : (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w)) ≤ 1 := by
    have h : ∀ w : Subtype F, (2 : ℝ≥0∞) ^ (-g w) =
        (2 : ℝ≥0∞)⁻¹ ^ (umWords_kmin P A w.1 + oracleNatComplexity A w.1.length) := by
      intro w
      rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]
    simp only [h]
    have he : (∑' w : Subtype F,
        (2 : ℝ≥0∞)⁻¹ ^ (umWords_kmin P A w.1 + oracleNatComplexity A w.1.length)) =
        ∑' w : BitString,
          (2 : ℝ≥0∞)⁻¹ ^ (umWords_kmin P A w + oracleNatComplexity A w.length) :=
      (Equiv.subtypeUnivEquiv (fun _ ↦ trivial : ∀ w : BitString, F w)).tsum_eq
        (fun w : BitString ↦
          (2 : ℝ≥0∞)⁻¹ ^ (umWords_kmin P A w + oracleNatComplexity A w.length))
    rw [he]
    exact umWords_mass_le_one P A
  obtain ⟨c, hc⟩ := oracle_coding_finite_mass A F g hg 1 hM ENNReal.one_lt_top
  refine ⟨c, fun w ↦ ?_⟩
  have := hc ⟨w, trivial⟩
  simp only [g] at this
  push_cast at this
  exact this

/-- Remark 6.6 (and Proposition 6.12) on Cantor space, at the level of words: if `A` computes
the symbols of the ideal points, the information `-log₂ m^A[w]` of a cylinder under the
universal measure `m^A = ∑_i 2^{-K^A(i)} δ_{x_i}` is `K^A(w) + O(log |w|)`, for every word
`w = x↾n`. Proved from `umWords_infoBits_le_oracleComplexity` (upper bound, `O(1)`) and the
coding theorem for the cost `w ↦ k_w + K^A(|w|)` (lower bound, with `K^A(n) = O(log n)` by
`oracleNatComplexity_le_bits`). Blueprint node `meas:remarks`. -/
theorem abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le'
    (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    ∃ c : ℝ, ∀ (x : ℕ → Bool) (n : ℕ), 1 ≤ n →
      |(infoBits (universalMeasure P A (PiNat.cylinder x n))).toReal -
          oracleComplexity A (cantorPrefix x n)| ≤ c * Real.logb 2 n + c := by
  obtain ⟨c₁, h₁⟩ := umWords_infoBits_le_oracleComplexity P A hP
  obtain ⟨c₂, h₂⟩ := umWords_oracleComplexity_le_kmin P A hP
  obtain ⟨c₀, h₀⟩ := oracleNatComplexity_le_bits A
  refine ⟨(c₁ : ℝ) + c₂ + c₀ + 7, fun x n hn ↦ ?_⟩
  rw [umWords_cylinder_eq_listCylinder]
  set w := cantorPrefix x n
  have hw : w.length = n := cantorPrefix_length x n
  have e1 := h₁ w
  have e2 := h₂ w
  have e3 := umWords_kmin_le_infoBits P A w
  have e4 : (oracleNatComplexity A n : ℝ) ≤ 3 * ((Nat.bits n).length : ℝ) + c₀ := by
    exact_mod_cast h₀ n
  have e5 := length_bits_le_logb_add_one n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e6 : Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 n + 1 := by
    have h2n : (n : ℝ) + 1 ≤ 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 (2 * n) :=
          Real.logb_le_logb_of_le one_lt_two (by positivity) h2n
      _ = Real.logb 2 n + 1 := by
          rw [Real.logb_mul two_ne_zero hn0.ne', Real.logb_self_eq_one one_lt_two]
          ring
  have hl : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  have hc3 : 3 * Real.logb 2 n ≤ ((c₁ : ℝ) + c₂ + c₀ + 7) * Real.logb 2 n := by
    refine mul_le_mul_of_nonneg_right ?_ hl
    have : (0 : ℝ) ≤ (c₁ : ℝ) + c₂ + c₀ := by positivity
    linarith
  rw [hw] at e2
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) c₁, Nat.cast_nonneg (α := ℝ) c₂,
    Nat.cast_nonneg (α := ℝ) c₀]

end cantor

end Kolmogorov.PointToSet
