/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Oracle.PrefixComplexity.Information
import KolmogorovMathlib.Oracle.KraftChaitin

/-!
# The lower direction of symmetry of information for `K^A`

For every oracle `A` the Levin–Gács inequality `K^A(x) + K^A(y | x, K^A(x)) ≤ K^A(⟨x, y⟩) + O(1)`
holds (`oracleSymmetryLower`), which discharges the hypothesis `OracleSymmetryLower A` of
`KolmogorovMathlib.Oracle.PrefixComplexity.Information` for an arbitrary oracle.  Write `U` for
the optimal `A`-prefix machine `optimalOraclePrefix A` and `μ(x) = ∑_y m_U(⟨x, y⟩)` for the
`pairMarginal`: the total Kraft mass of the `U`-programs whose output is a pair code with first
component `x`.

* `oracle_pairMarginal_coding_bound`: the marginal coding bound `μ(x) ≤ 2^{c} · 2^{-K^A(x)}`.
  The halting pair triples `(p, x, y)` are enumerated without repetition relative to `A`, the
  partial sums of their dyadic weights are `A`-computable rationals, so the thresholds
  `2^{-n} < μ(x)` form an `A`-c.e. set; realizing them (with one extra bit) by the relative
  Kraft–Chaitin theorem `oracle_kraftChaitin_bound` gives `K^A(x) ≤ -log₂ μ(x) + O(1)`.
* `oracleSymmetryLower`: in the context `⟨x, natCode k⟩` the stream requesting
  `(y, |p| + c - k)` for every halting pair triple `(p, x, y)` has Kraft mass
  `2^{k - c} μ(x) ≤ 1` when `k = K^A(x)`; the context-uniform relative Kraft–Chaitin theorem
  `oracle_kraftChaitin_cond` realizes it by a single `A`-prefix machine, and optimality of `U`
  gives `K^A(y | x, K^A(x)) ≤ K^A(⟨x, y⟩) - K^A(x) + O(1)`.

Blueprint node `split:symmetry-lower`.
-/

namespace Kolmogorov.PointToSet

open scoped ENNReal Computability

/-! ### Dyadic arithmetic -/

/-- `2^n · 2^{-n} = 1` in `ℝ≥0∞`. -/
private lemma two_pow_mul_inv_two_pow (n : ℕ) :
    (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ n = 1 := by
  rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]

/-- Shifting the exponent of a dyadic weight. -/
private lemma inv_two_pow_eq_mul (a b : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ a = (2 : ℝ≥0∞) ^ b * (2 : ℝ≥0∞)⁻¹ ^ (a + b) := by
  rw [pow_add, mul_left_comm, two_pow_mul_inv_two_pow, mul_one]

/-- A truncated subtraction in the exponent of a dyadic weight. -/
private lemma inv_two_pow_sub (L k : ℕ) (h : k ≤ L) :
    (2 : ℝ≥0∞)⁻¹ ^ (L - k) = (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ L := by
  rw [inv_two_pow_eq_mul (L - k) k, Nat.sub_add_cancel h]

/-- The dyadic rational `2^{-n}` casts to the dyadic weight `2^{-n}` of `ℝ≥0∞`. -/
private lemma ofReal_rat_inv_two_pow (n : ℕ) :
    ENNReal.ofReal ((((2 : ℚ) ^ n)⁻¹ : ℚ) : ℝ) = (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ENNReal.inv_pow]

/-- The rational sequence of inverse powers of two is computable. -/
private lemma rat_inv_two_pow_computable : Computable (fun n : ℕ ↦ ((2 : ℚ) ^ n)⁻¹) := by
  have H : (fun n : ℕ ↦ ((2 : ℚ) ^ n)⁻¹) = fun n ↦ ((1 : ℤ) : ℚ) / ((2 ^ n : ℕ) : ℚ) := by
    ext n
    push_cast
    rw [inv_eq_one_div]
  rw [H]
  exact computable_of_num_den (Computable.const (1 : ℤ)) comp_pow (fun n ↦ by positivity)
    (fun n ↦ rfl)

/-- The dyadic masses `2^{-(n+1)}` over the exponents `n` with `2^{-n} < a` add up to at most
`a`. -/
private lemma tsum_ite_inv_two_pow_lt_le (a : ℝ≥0∞) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n, P n ↔ (2 : ℝ≥0∞)⁻¹ ^ n < a) :
    ∑' n : ℕ, (if P n then (2 : ℝ≥0∞)⁻¹ ^ (n + 1) else 0) ≤ a := by
  by_cases ha : a = 0
  · subst ha
    have h0 : ∀ n, ¬ P n := fun n hn ↦ ENNReal.not_lt_zero ((hP n).mp hn)
    simp [h0]
  · obtain ⟨n₀, hn₀, hmin⟩ : ∃ n₀ : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n₀ < a ∧
        ∀ m, m < n₀ → ¬ (2 : ℝ≥0∞)⁻¹ ^ m < a := by
      classical
      have hex : ∃ n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n < a := ENNReal.exists_inv_two_pow_lt ha
      exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩
    have hiff : ∀ n, P n ↔ n₀ ≤ n := by
      intro n
      rw [hP]
      constructor
      · intro h
        by_contra hlt
        exact hmin n (not_le.mp hlt) h
      · intro h
        exact lt_of_le_of_lt
          (pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two) h) hn₀
    have hf : ∀ n, (if P n then (2 : ℝ≥0∞)⁻¹ ^ (n + 1) else 0) =
        if n₀ ≤ n then (2 : ℝ≥0∞)⁻¹ ^ (n + 1) else 0 := by
      intro n
      by_cases h : P n
      · rw [ite_eq_left h, ite_eq_left ((hiff n).mp h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h ((hiff n).mpr h'))]
    calc ∑' n : ℕ, (if P n then (2 : ℝ≥0∞)⁻¹ ^ (n + 1) else 0)
        = ∑' n : ℕ, (if n₀ ≤ n then (2 : ℝ≥0∞)⁻¹ ^ (n + 1) else 0) := tsum_congr hf
      _ = (∑ i ∈ Finset.range n₀, (if n₀ ≤ i then (2 : ℝ≥0∞)⁻¹ ^ (i + 1) else 0)) +
          ∑' i : ℕ, (if n₀ ≤ i + n₀ then (2 : ℝ≥0∞)⁻¹ ^ (i + n₀ + 1) else 0) :=
        (Summable.sum_add_tsum_nat_add'
          (f := fun n ↦ if n₀ ≤ n then (2 : ℝ≥0∞)⁻¹ ^ (n + 1) else 0) (k := n₀)
          ENNReal.summable).symm
      _ = ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n₀ + 1) * (2 : ℝ≥0∞)⁻¹ ^ i := by
        rw [Finset.sum_eq_zero, zero_add]
        · refine tsum_congr fun i ↦ ?_
          rw [ite_eq_left (Nat.le_add_left n₀ i), ← pow_add]
          congr 1
          omega
        · intro i hi
          exact ite_eq_right (not_le.mpr (Finset.mem_range.mp hi))
      _ = (2 : ℝ≥0∞)⁻¹ ^ (n₀ + 1) * 2 := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
      _ = (2 : ℝ≥0∞)⁻¹ ^ n₀ := by
        rw [pow_succ, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
          mul_one]
      _ ≤ a := hn₀.le

open Classical in
/-- Summing a weight over the stages of an enumeration without repetitions is summing it over
the enumerated values. -/
private lemma tsum_option_elim_eq {α : Type*} (e : ℕ → Option α)
    (hinj : ∀ s t a, e s = some a → e t = some a → s = t) (f : α → ℝ≥0∞) :
    ∑' s, (e s).elim 0 f = ∑' a, if ∃ s, e s = some a then f a else 0 := by
  have h1 : ∀ s, (e s).elim 0 f = ∑' a, if e s = some a then f a else 0 := by
    intro s
    cases h : e s with
    | none => simp
    | some a =>
      rw [Option.elim_some, tsum_eq_single a]
      · rw [ite_eq_left rfl]
      · intro b hb
        rw [ite_eq_right]
        intro hab
        exact hb (Option.some_injective _ hab).symm
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a ↦ ?_
  by_cases ha : ∃ s, e s = some a
  · obtain ⟨s₀, hs₀⟩ := ha
    rw [ite_eq_left ⟨s₀, hs₀⟩, tsum_eq_single s₀]
    · rw [ite_eq_left hs₀]
    · intro s hs
      rw [ite_eq_right]
      intro h
      exact hs (hinj s s₀ a h hs₀)
  · rw [ite_eq_right ha]
    exact ENNReal.tsum_eq_zero.mpr fun s ↦ ite_eq_right fun h ↦ ha ⟨s, h⟩

/-! ### Halting pair triples and their section mass -/

/-- The triples `(p, x, y)` such that `p` produces the pair code `⟨x, y⟩` on `U` in the empty
context. -/
private def pairHalting (U : Map) (t : BitString × BitString × BitString) : Prop :=
  produces U t.1 [] (pairCode t.2.1 t.2.2)

/-- The halting pair triples of the optimal oracle machine are relatively enumerable. -/
private lemma pairHalting_isREIn (A : Set ℕ) :
    IsREIn A (pairHalting (optimalOraclePrefix A)) := by
  obtain ⟨hUd, -, -⟩ := exists_optimalOraclePrefix_spec A
  rw [isDecompressorIn_iff_partrecIn] at hUd
  refine ⟨fun t ↦ (optimalOraclePrefix A (t.1, [])).bind fun out ↦
    cond (decide (out = pairCode t.2.1 t.2.2)) (Part.some 0) Part.none, ?_, fun t ↦ ?_⟩
  · have hrun : PartrecIn {charOracle A}
        fun t : BitString × BitString × BitString ↦ optimalOraclePrefix A (t.1, []) :=
      hUd.comp (ComputableIn.pair ComputableIn.fst (ComputableIn.const []))
    have hpc : Computable fun q : (BitString × BitString × BitString) × BitString ↦
        pairCode q.1.2.1 q.1.2.2 :=
      (pairCode_computable.comp (Computable.pair
        (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.snd.comp (Computable.snd.comp Computable.fst)))).of_eq fun _ ↦ rfl
    have heq : Computable fun v : BitString × BitString ↦ decide (v.1 = v.2) :=
      (PrimrecPred.decide (PrimrecRel.comp Primrec.eq Primrec.fst Primrec.snd)).to_comp
    have hguard : ComputableIn {charOracle A}
        fun q : (BitString × BitString × BitString) × BitString ↦
          decide (q.2 = pairCode q.1.2.1 q.1.2.2) :=
      ((heq.comp (Computable.snd.pair hpc)).of_eq fun _ ↦ rfl).computableIn
    exact hrun.bind
      (PartrecIn.cond hguard (ComputableIn.const 0).partrecIn PartrecIn.none).to₂
  · constructor
    · intro h
      exact Part.dom_iff_mem.mpr ⟨0, Part.mem_bind_iff.mpr ⟨_, h, by simp⟩⟩
    · intro h
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
      obtain ⟨out, hout, hv'⟩ := Part.mem_bind_iff.mp hv
      by_cases hc : out = pairCode t.2.1 t.2.2
      · change pairCode t.2.1 t.2.2 ∈ optimalOraclePrefix A (t.1, [])
        rw [← hc]
        exact hout
      · simp [hc] at hv'

/-- The Kraft weight that a stage of an enumeration of halting pair triples contributes to the
section mass of the first component `x`. -/
private noncomputable def stageWeight (x : BitString)
    (o : Option (BitString × BitString × BitString)) : ℝ≥0∞ :=
  o.elim 0 fun t ↦ if t.2.1 = x then (2 : ℝ≥0∞)⁻¹ ^ t.1.length else 0

/-- The rational counterpart of `stageWeight`. -/
private def stageWeightQ (x : BitString) (o : Option (BitString × BitString × BitString)) : ℚ :=
  o.elim 0 fun t ↦ if t.2.1 = x then ((2 : ℚ) ^ t.1.length)⁻¹ else 0

/-- Rational stage weights are nonnegative. -/
private lemma stageWeightQ_nonneg (x : BitString) (o : Option (BitString × BitString × BitString)) :
    0 ≤ stageWeightQ x o := by
  cases o with
  | none => exact le_rfl
  | some t =>
    simp only [stageWeightQ, Option.elim_some]
    split_ifs <;> positivity

/-- The rational stage weight casts to the extended stage weight. -/
private lemma ofReal_stageWeightQ (x : BitString) (o : Option (BitString × BitString × BitString)) :
    ENNReal.ofReal (stageWeightQ x o) = stageWeight x o := by
  cases o with
  | none => simp [stageWeightQ, stageWeight]
  | some t =>
    simp only [stageWeightQ, stageWeight, Option.elim_some]
    split_ifs
    · exact ofReal_rat_inv_two_pow _
    · simp

/-- The rational stage weight is computable. -/
private lemma stageWeightQ_computable :
    Computable fun q : BitString × Option (BitString × BitString × BitString) ↦
      stageWeightQ q.1 q.2 := by
  have hdec : Computable fun v : (BitString × Option (BitString × BitString × BitString)) ×
      (BitString × BitString × BitString) ↦ decide (v.2.2.1 = v.1.1) :=
    (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.fst.comp Primrec.fst))).to_comp
  have hval : Computable fun v : (BitString × Option (BitString × BitString × BitString)) ×
      (BitString × BitString × BitString) ↦ ((2 : ℚ) ^ v.2.1.length)⁻¹ :=
    rat_inv_two_pow_computable.comp
      (Computable.list_length.comp (Computable.fst.comp Computable.snd))
  have hif : Computable₂ fun (q : BitString × Option (BitString × BitString × BitString))
      (t : BitString × BitString × BitString) ↦
        if t.2.1 = q.1 then ((2 : ℚ) ^ t.1.length)⁻¹ else 0 :=
    (Computable.cond hdec hval (Computable.const 0)).of_eq fun _ ↦ by
      simp only [Bool.cond_decide]
  exact (Computable.option_casesOn Computable.snd (Computable.const 0) hif).of_eq
    fun ⟨_, o⟩ ↦ by cases o <;> rfl

/-- The stage weights of an enumeration without repetitions of the halting pair triples add up
to the pair marginal. -/
private lemma tsum_stageWeight (U : Map) (e : ℕ → Option (BitString × BitString × BitString))
    (henum : ∀ t, pairHalting U t ↔ ∃ s, e s = some t)
    (hinj : ∀ s s' t, e s = some t → e s' = some t → s = s') (x : BitString) :
    ∑' s, stageWeight x (e s) = pairMarginal U x [] := by
  classical
  have h := tsum_option_elim_eq e hinj
    (fun t : BitString × BitString × BitString ↦
      if t.2.1 = x then (2 : ℝ≥0∞)⁻¹ ^ t.1.length else 0)
  change ∑' s, (e s).elim 0
    (fun t : BitString × BitString × BitString ↦
      if t.2.1 = x then (2 : ℝ≥0∞)⁻¹ ^ t.1.length else 0) = _
  rw [h, pairMarginal_def]
  simp only [aprioriMeasure]
  rw [ENNReal.tsum_comm, ENNReal.tsum_prod']
  refine tsum_congr fun p ↦ ?_
  rw [ENNReal.tsum_prod', tsum_eq_single x]
  · refine tsum_congr fun y ↦ ?_
    have hiff : (∃ s, e s = some (p, x, y)) ↔ produces U p [] (pairCode x y) :=
      (henum (p, x, y)).symm
    by_cases hpy : produces U p [] (pairCode x y)
    · rw [ite_eq_left (hiff.mpr hpy), ite_eq_left rfl, ite_eq_left hpy]
      rfl
    · rw [ite_eq_right (fun h' ↦ hpy (hiff.mp h')), ite_eq_right hpy]
  · intro x' hx'
    exact ENNReal.tsum_eq_zero.mpr fun y ↦ by simp [hx']

/-- Partial sums of the rational stage weights, as a primitive recursion. -/
private def sectionApprox (e : ℕ → Option (BitString × BitString × BitString))
    (x : BitString) (t : ℕ) : ℚ :=
  @Nat.rec (fun _ ↦ ℚ) 0 (fun s ih ↦ ih + stageWeightQ x (e s)) t

/-- The recursion step of `sectionApprox`. -/
private lemma sectionApprox_succ (e : ℕ → Option (BitString × BitString × BitString))
    (x : BitString) (t : ℕ) :
    sectionApprox e x (t + 1) = sectionApprox e x t + stageWeightQ x (e t) := rfl

/-- The rational partial sums are nonnegative. -/
private lemma sectionApprox_nonneg (e : ℕ → Option (BitString × BitString × BitString))
    (x : BitString) (t : ℕ) : 0 ≤ sectionApprox e x t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [sectionApprox_succ]
    exact add_nonneg ih (stageWeightQ_nonneg x _)

/-- The rational partial sums cast to the partial sums of the extended stage weights. -/
private lemma ofReal_sectionApprox (e : ℕ → Option (BitString × BitString × BitString))
    (x : BitString) (t : ℕ) :
    ENNReal.ofReal (sectionApprox e x t) = ∑ s ∈ Finset.range t, stageWeight x (e s) := by
  induction t with
  | zero => simp [sectionApprox]
  | succ t ih =>
    rw [sectionApprox_succ, Finset.sum_range_succ, ← ih, ← ofReal_stageWeightQ, Rat.cast_add,
      ENNReal.ofReal_add (by exact_mod_cast sectionApprox_nonneg e x t)
        (by exact_mod_cast stageWeightQ_nonneg x _)]

/-- The rational partial sums are computable relative to the enumeration. -/
private lemma sectionApprox_computableIn (A : Set ℕ)
    (e : ℕ → Option (BitString × BitString × BitString)) (he : ComputableIn {charOracle A} e) :
    ComputableIn {charOracle A} fun w : BitString × ℕ ↦ sectionApprox e w.1 w.2 := by
  have h1 : ComputableIn {charOracle A} fun v : (BitString × ℕ) × ℕ × ℚ ↦ (v.1.1, e v.2.1) :=
    ComputableIn.pair (ComputableIn.fst.comp ComputableIn.fst)
      (he.comp (ComputableIn.fst.comp ComputableIn.snd))
  have h2 : ComputableIn {charOracle A}
      fun v : (BitString × ℕ) × ℕ × ℚ ↦ stageWeightQ v.1.1 (e v.2.1) :=
    (stageWeightQ_computable.computableIn.comp h1).of_eq fun _ ↦ rfl
  have hstep : ComputableIn₂ {charOracle A}
      fun (w : BitString × ℕ) (v : ℕ × ℚ) ↦ v.2 + stageWeightQ w.1 (e v.1) :=
    ComputableIn₂.mk ((computable₂_ratAdd.computableIn.comp
      (ComputableIn.pair (ComputableIn.snd.comp ComputableIn.snd) h2)).of_eq fun _ ↦ rfl)
  exact (ComputableIn.nat_rec ComputableIn.snd (ComputableIn.const (0 : ℚ)) hstep).of_eq
    fun _ ↦ rfl

/-! ### The marginal coding bound -/

/-- **Marginal coding bound.** The total `A`-a priori mass `∑_y m_U(⟨x, y⟩)` of the encoded
pairs with first component `x` is at most `2^{c} · 2^{-K^A(x)}`, for a constant `c` depending
only on `A`. Blueprint node `split:symmetry-lower`. -/
theorem oracle_pairMarginal_coding_bound (A : Set ℕ) :
    ∃ c : ℕ, ∀ x : BitString, pairMarginal (optimalOraclePrefix A) x [] ≤
      (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ oracleComplexity A x := by
  classical
  obtain ⟨-, hUp, -⟩ := exists_optimalOraclePrefix_spec A
  obtain ⟨e, ⟨he, henum⟩, hinj⟩ := relative_enumeration_injective A _ (pairHalting_isREIn A)
  have hsum : ∀ x, ∑' s, stageWeight x (e s) = pairMarginal (optimalOraclePrefix A) x [] :=
    tsum_stageWeight (optimalOraclePrefix A) e henum hinj
  have hle_one : ∀ x, pairMarginal (optimalOraclePrefix A) x [] ≤ 1 := fun x ↦
    (ENNReal.le_tsum x).trans (tsum_pairMarginal_le_one _ [] hUp)
  -- The dyadic thresholds exceeded by the stage approximations of the section mass.
  let R : BitString × ℕ → Prop := fun w ↦ ∃ t, ((2 : ℚ) ^ w.2)⁻¹ < sectionApprox e w.1 t
  have hR_iff : ∀ x n, R (x, n) ↔
      (2 : ℝ≥0∞)⁻¹ ^ n < pairMarginal (optimalOraclePrefix A) x [] := by
    intro x n
    rw [← hsum x, ENNReal.tsum_eq_iSup_nat, lt_iSup_iff]
    refine exists_congr fun t ↦ ?_
    rw [← ofReal_sectionApprox, ← ofReal_rat_inv_two_pow,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), Rat.cast_lt]
  have hR : IsREIn A R := by
    have hlt : Computable fun v : ℚ × ℚ ↦ decide (v.1 < v.2) :=
      (PrimrecRel.decide Kolmogorov.ComputableReals.primrec_ratLt).to_comp
    have h1 : ComputableIn {charOracle A} fun w : (BitString × ℕ) × ℕ ↦ ((2 : ℚ) ^ w.1.2)⁻¹ :=
      rat_inv_two_pow_computable.computableIn.comp (ComputableIn.snd.comp ComputableIn.fst)
    have h2 : ComputableIn {charOracle A}
        fun w : (BitString × ℕ) × ℕ ↦ sectionApprox e w.1.1 w.2 :=
      ((sectionApprox_computableIn A e he).comp
        (ComputableIn.pair (ComputableIn.fst.comp ComputableIn.fst) ComputableIn.snd)).of_eq
          fun _ ↦ rfl
    have hdec : ComputableIn {charOracle A} fun w : (BitString × ℕ) × ℕ ↦
        decide (((2 : ℚ) ^ w.1.2)⁻¹ < sectionApprox e w.1.1 w.2) :=
      (hlt.computableIn.comp (h1.pair h2)).of_eq fun _ ↦ rfl
    exact (isREIn_of_computableIn_decide A
      (fun w : (BitString × ℕ) × ℕ ↦ ((2 : ℚ) ^ w.1.2)⁻¹ < sectionApprox e w.1.1 w.2)
      hdec).exists
  obtain ⟨e', ⟨he', henum'⟩, hinj'⟩ := relative_enumeration_injective A R hR
  -- The request stream: each threshold `n` of `x` is requested with one extra bit.
  let str : ℕ → Option (BitString × ℕ) := fun s ↦ (e' s).map fun r ↦ (r.1, r.2 + 1)
  have hstr : ComputableIn {charOracle A} str := by
    have hm : Computable fun o : Option (BitString × ℕ) ↦ o.map fun r ↦ (r.1, r.2 + 1) :=
      Computable.option_map Computable.id
        ((Computable.fst.comp Computable.snd).pair
          (Computable.succ.comp (Computable.snd.comp Computable.snd))).to₂
    exact hm.computableIn.comp he'
  have hmass : oracleRequestMass str ≤ 1 := by
    have hterm : ∀ s, (str s).elim 0 (fun r ↦ (2 : ℝ≥0∞)⁻¹ ^ r.2) =
        (e' s).elim 0 fun r ↦ (2 : ℝ≥0∞)⁻¹ ^ (r.2 + 1) := by
      intro s
      cases h : e' s <;> simp [str, h]
    calc oracleRequestMass str
        = ∑' w : BitString × ℕ,
            if ∃ s, e' s = some w then (2 : ℝ≥0∞)⁻¹ ^ (w.2 + 1) else 0 := by
          unfold oracleRequestMass
          simp_rw [hterm]
          exact tsum_option_elim_eq e' hinj' _
      _ = ∑' x, ∑' n, if ∃ s, e' s = some (x, n) then (2 : ℝ≥0∞)⁻¹ ^ (n + 1) else 0 :=
          ENNReal.tsum_prod'
      _ ≤ ∑' x, pairMarginal (optimalOraclePrefix A) x [] := by
          refine ENNReal.tsum_le_tsum fun x ↦ ?_
          exact tsum_ite_inv_two_pow_lt_le _ (fun n ↦ ∃ s, e' s = some (x, n))
            fun n ↦ (henum' (x, n)).symm.trans (hR_iff x n)
      _ ≤ 1 := tsum_pairMarginal_le_one _ [] hUp
  obtain ⟨c, hc⟩ := oracle_kraftChaitin_bound A str hstr hmass
  refine ⟨c + 2, fun x ↦ ?_⟩
  by_cases hx : pairMarginal (optimalOraclePrefix A) x [] = 0
  · rw [hx]
    exact zero_le
  · obtain ⟨n₀, hn₀, hmin⟩ : ∃ n₀ : ℕ,
        (2 : ℝ≥0∞)⁻¹ ^ n₀ < pairMarginal (optimalOraclePrefix A) x [] ∧
        ∀ m, m < n₀ → ¬ (2 : ℝ≥0∞)⁻¹ ^ m < pairMarginal (optimalOraclePrefix A) x [] := by
      have hex : ∃ n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n < pairMarginal (optimalOraclePrefix A) x [] :=
        ENNReal.exists_inv_two_pow_lt hx
      exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩
    -- `μ(x) ≤ 2 · 2^{-n₀}` by minimality of `n₀`.
    have hupper : pairMarginal (optimalOraclePrefix A) x [] ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ n₀ := by
      cases n₀ with
      | zero =>
        rw [pow_zero, mul_one]
        exact (hle_one x).trans one_le_two
      | succ m =>
        rw [pow_succ, mul_left_comm, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
          mul_one]
        exact not_lt.mp (hmin m (Nat.lt_succ_self m))
    -- The request `(x, n₀ + 1)` is in the stream, so `K(x) ≤ n₀ + 1 + c`.
    obtain ⟨s, hs⟩ := (henum' (x, n₀)).mp ((hR_iff x n₀).mpr hn₀)
    have hstrs : str s = some (x, n₀ + 1) := by simp [str, hs]
    have hK : oracleComplexity A x ≤ n₀ + 1 + c := hc s x (n₀ + 1) hstrs
    have hw : (2 : ℝ≥0∞)⁻¹ ^ (n₀ + (1 + c)) ≤ (2 : ℝ≥0∞)⁻¹ ^ oracleComplexity A x :=
      pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two) (by omega)
    calc pairMarginal (optimalOraclePrefix A) x [] ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ n₀ := hupper
      _ = 2 * ((2 : ℝ≥0∞) ^ (1 + c) * (2 : ℝ≥0∞)⁻¹ ^ (n₀ + (1 + c))) := by
          rw [← inv_two_pow_eq_mul]
      _ ≤ 2 * ((2 : ℝ≥0∞) ^ (1 + c) * (2 : ℝ≥0∞)⁻¹ ^ oracleComplexity A x) :=
          mul_le_mul_right (mul_le_mul_right hw _) _
      _ = (2 : ℝ≥0∞) ^ (c + 2) * (2 : ℝ≥0∞)⁻¹ ^ oracleComplexity A x := by
          rw [show c + 2 = 1 + (1 + c) by omega]
          ring

/-! ### The lower direction of symmetry of information -/

/-- **Lower direction of symmetry of information** (Levin–Gács), for every oracle `A`:
`K^A(x) + K^A(y | x, K^A(x)) ≤ K^A(⟨x, y⟩) + O(1)`. Blueprint node `split:symmetry-lower`. -/
theorem oracleSymmetryLower (A : Set ℕ) : OracleSymmetryLower A := by
  classical
  obtain ⟨-, -, hopt⟩ := exists_optimalOraclePrefix_spec A
  obtain ⟨c, hc⟩ := oracle_pairMarginal_coding_bound A
  obtain ⟨c₂, hc₂⟩ := oracleComplexity_fst_le_pair A
  obtain ⟨e, ⟨he, henum⟩, hinj⟩ := relative_enumeration_injective A _ (pairHalting_isREIn A)
  -- In the context `⟨x, natCode k⟩`, request `(y, |p| + c + c₂ - k)` for every halting
  -- pair triple `(p, x, y)`.
  let req : BitString → ℕ → Option (BitString × ℕ) := fun ctx s ↦
    (e s).bind fun t ↦
      if t.2.1 = decodeFirst ctx then some (t.2.2, t.1.length + (c + c₂) - decodeNat ctx)
      else none
  have hreq : ComputableIn {charOracle A} fun q : BitString × ℕ ↦ req q.1 q.2 := by
    have hpre : ComputableIn {charOracle A}
        fun q : BitString × ℕ ↦ ((decodeFirst q.1, decodeNat q.1), e q.2) :=
      ComputableIn.pair
        (ComputableIn.pair (decodeFirst_computable.computableIn.comp ComputableIn.fst)
          (decodeNat_computable.computableIn.comp ComputableIn.fst))
        (he.comp ComputableIn.snd)
    have hdec : Computable fun v : ((BitString × ℕ) × Option (BitString × BitString × BitString)) ×
        (BitString × BitString × BitString) ↦ decide (v.2.2.1 = v.1.1.1) :=
      (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).to_comp
    have hval : Primrec fun v : ((BitString × ℕ) × Option (BitString × BitString × BitString)) ×
        (BitString × BitString × BitString) ↦ (v.2.2.2, v.2.1.length + (c + c₂) - v.1.1.2) :=
      Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.nat_sub.comp
          (Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.const (c + c₂)))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    have hif : Computable₂ fun (w : (BitString × ℕ) × Option (BitString × BitString × BitString))
        (t : BitString × BitString × BitString) ↦
          if t.2.1 = w.1.1 then some (t.2.2, t.1.length + (c + c₂) - w.1.2) else none :=
      (Computable.cond hdec (Computable.option_some.comp hval.to_comp)
        (Computable.const none)).of_eq fun _ ↦ by simp only [Bool.cond_decide]
    have hinner : Computable
        fun w : (BitString × ℕ) × Option (BitString × BitString × BitString) ↦
          w.2.bind fun t ↦
            if t.2.1 = w.1.1 then some (t.2.2, t.1.length + (c + c₂) - w.1.2) else none :=
      Computable.option_bind Computable.snd hif
    exact (hinner.computableIn.comp hpre).of_eq fun _ ↦ rfl
  obtain ⟨D, hDd, hDp, hDprod⟩ := oracle_kraftChaitin_cond A req hreq
  obtain ⟨c₃, hc₃⟩ := hopt D hDd hDp
  refine ⟨c + c₂ + c₃, fun x y ↦ ?_⟩
  set k := oracleComplexity A x with hk
  -- At `k = K(x)` the stream of the context `⟨x, natCode k⟩` has mass `2^{k - c - c₂} μ(x) ≤ 1`.
  have hmass : oracleRequestMass (req (prefixComplexityContext x k)) ≤ 1 := by
    have hterm : ∀ s, (req (prefixComplexityContext x k) s).elim 0
        (fun r ↦ (2 : ℝ≥0∞)⁻¹ ^ r.2) =
          (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ (c + c₂) * stageWeight x (e s) := by
      intro s
      have hhalt : ∀ t, e s = some t →
          produces (optimalOraclePrefix A) t.1 [] (pairCode t.2.1 t.2.2) :=
        fun t ht ↦ (henum t).mpr ⟨s, ht⟩
      change ((e s).bind fun t ↦
        if t.2.1 = decodeFirst (prefixComplexityContext x k) then
          some (t.2.2, t.1.length + (c + c₂) - decodeNat (prefixComplexityContext x k))
        else none).elim 0 (fun r ↦ (2 : ℝ≥0∞)⁻¹ ^ r.2) = _
      rw [prefixComplexityContext_eq_pairCode, decodeFirst_pairCode, decodeNat_pairCode]
      generalize e s = o at hhalt ⊢
      rcases o with _ | ⟨p, x', y⟩
      · simp [stageWeight]
      · by_cases hx : x' = x
        · subst x'
          have hT : produces (optimalOraclePrefix A) p [] (pairCode x y) := hhalt (p, x, y) rfl
          have hlen : oracleComplexity A (pairCode x y) ≤ p.length :=
            oraclePrefixComplexityNat_le_of_KP_le (KP_le_programLength_of_produces hT)
          have hk' : k ≤ p.length + (c + c₂) := by
            have := hc₂ x y
            omega
          simp only [stageWeight, Option.bind_some, Option.elim_some, ite_true]
          rw [inv_two_pow_sub _ _ hk', pow_add]
          ring
        · simp [stageWeight, hx]
    unfold oracleRequestMass
    rw [tsum_congr hterm, ENNReal.tsum_mul_left, tsum_stageWeight _ e henum hinj x]
    calc (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ (c + c₂) * pairMarginal (optimalOraclePrefix A) x []
        ≤ (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ (c + c₂) *
            ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ k) := mul_le_mul_right (hc x) _
      _ = ((2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ k) * ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ c) *
            (2 : ℝ≥0∞)⁻¹ ^ c₂ := by
          rw [pow_add]
          ring
      _ = (2 : ℝ≥0∞)⁻¹ ^ c₂ := by
          rw [two_pow_mul_inv_two_pow, two_pow_mul_inv_two_pow, one_mul, one_mul]
      _ ≤ 1 := pow_le_one' (ENNReal.inv_le_one.mpr one_le_two) _
  -- A shortest program for `⟨x, y⟩` yields the request `(y, K(⟨x, y⟩) + c + c₂ - k)`.
  obtain ⟨p, hp, hpl⟩ := exists_program_oraclePrefix A (pairCode x y) []
  obtain ⟨s, hs⟩ := (henum (p, x, y)).mp hp
  have hreqs : req (prefixComplexityContext x k) s = some (y, p.length + (c + c₂) - k) := by
    simp [req, hs, decodeFirst_pairCode, decodeNat_pairCode]
  obtain ⟨q, hql, hq⟩ := hDprod _ hmass s y _ hreqs
  have hbound : KP (optimalOraclePrefix A) y (prefixComplexityContext x k) ≤
      ((q.length + c₃ : ℕ) : ENat) := by
    calc KP (optimalOraclePrefix A) y (prefixComplexityContext x k)
        ≤ KP D y (prefixComplexityContext x k) + (c₃ : ENat) := hc₃ y _
      _ ≤ (q.length : ENat) + (c₃ : ENat) := by
          gcongr
          exact KP_le_programLength_of_produces hq
      _ = ((q.length + c₃ : ℕ) : ENat) := by norm_cast
  have h1 := oraclePrefixComplexityNat_le_of_KP_le hbound
  have h2 := hc₂ x y
  have hpl' : p.length = oracleComplexity A (pairCode x y) := hpl
  omega

end Kolmogorov.PointToSet
