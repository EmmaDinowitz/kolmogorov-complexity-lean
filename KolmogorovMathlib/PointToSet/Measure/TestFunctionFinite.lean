/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.DeficiencyTest
import KolmogorovMathlib.PointToSet.Measure.EffectiveNull

/-!
# The test function is finite at random points (Lemma 3.2)

The test function `t_ε` of Lemma 3.2 (`testFunction`, `Measure/DeficiencyTest.lean`) is lower
semicomputable relative to an admissible oracle and has integral less than `2`, so it is finite
at every random point (E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of
random points*, §2.2 and Lemma 3.2). The levels `{t_ε > 2^m}` have measure at most
`2 · 2^{-m}` by Markov's inequality, and they are uniformly c.e. open: a point lies in the
level `m` exactly when it lies in the intersection of finitely many Bowen balls
`B_n(x_i, T, ε)` carrying certified rational lower bounds for their summands whose sum exceeds
`2^m`.

A certificate is a list of entries `(n, i, k, a, N)` with pairwise distinct pairs `(n, i)`,
`n ≥ 1`, `K^A(i) < k + 1` and `μ(B̄_n(x_i, T, ε)) < (a + 1)/(N + 1)`; the entry contributes the
rational lower bound `2^{-k} n^{-2} (N + 1)/(a + 1)` of the summand of `(n, i)`
(`ofReal_listVal_le`), and every point of a level carries such a certificate
(`exists_certificate_of_lt`).

* `testFunction_lt_top_of_mem_randomPoints`: `t_ε(x) < ∞` for `x ∈ R_A`.

Blueprint node `meas:test`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### Certificate entries and their rational values -/

/-- A certificate entry `(n, i, k, a, N)`: the pair `(n, i)` of a summand of the test function,
an upper bound `k` for `K^A(i)` and the rational `(a + 1)/(N + 1)`, a strict upper bound for
the measure of the closed Bowen ball. -/
private abbrev TestEntry : Type := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The pair `(n, i)` of a certificate entry. -/
private def entryPair (e : TestEntry) : ℕ × ℕ := (e.1, e.2.1)

/-- The rational `(a + 1)/(N + 1)` of a certificate entry. -/
private def entryBound (e : TestEntry) : ℚ :=
  ((e.2.2.2.1 + 1 : ℕ) : ℚ) / ((e.2.2.2.2 + 1 : ℕ) : ℚ)

/-- The rational value `2^{-k} n^{-2} (N + 1)/(a + 1)` of a certificate entry (with `n`
replaced by `1` when `n = 0`). -/
private def entryVal (e : TestEntry) : ℚ :=
  ((e.2.2.2.2 + 1 : ℕ) : ℚ) / ((max 1 e.1 ^ 2 * 2 ^ e.2.2.1 * (e.2.2.2.1 + 1) : ℕ) : ℚ)

/-- The total value of a certificate list. -/
private def listVal (L : List TestEntry) : ℚ :=
  L.foldr (fun e s ↦ entryVal e + s) 0

/-- The pair of an entry is primitive recursive. -/
private lemma primrec_entryPair : Primrec entryPair :=
  (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).of_eq fun _ ↦ rfl

/-- The rational bound of an entry is computable. -/
private lemma computable_entryBound : Computable entryBound := by
  have hN : Computable fun e : TestEntry ↦ ((e.2.2.2.1 + 1 : ℕ) : ℤ) :=
    ComputableReals.primrec_natCastInt.to_comp.comp
      (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.snd)))).to_comp
  have hD : Computable fun e : TestEntry ↦ e.2.2.2.2 + 1 :=
    (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)))).to_comp
  exact computable_of_num_den hN hD (fun _ ↦ Nat.succ_pos _) fun e ↦ by
    simp [entryBound]

/-- The rational value of an entry is computable. -/
private lemma computable_entryVal : Computable entryVal := by
  have hN : Computable fun e : TestEntry ↦ ((e.2.2.2.2 + 1 : ℕ) : ℤ) :=
    ComputableReals.primrec_natCastInt.to_comp.comp
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.snd)))).to_comp
  have hD : Primrec fun e : TestEntry ↦ max 1 e.1 ^ 2 * 2 ^ e.2.2.1 * (e.2.2.2.1 + 1) :=
    Primrec.nat_mul.comp (Primrec.nat_mul.comp
      (nat_pow_primrec₂.comp (Primrec.nat_max.comp (Primrec.const 1) Primrec.fst)
        (Primrec.const 2))
      (nat_pow_primrec₂.comp (Primrec.const 2)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact computable_of_num_den hN hD.to_comp (fun _ ↦ by positivity) fun e ↦ by
    simp [entryVal]

/-- The total value of a certificate list is computable. -/
private lemma computable_listVal : Computable listVal :=
  Computable.list_foldr (h := fun _ p ↦ entryVal p.1 + p.2) Computable.id
    (Computable.const (0 : ℚ))
    (computable₂_ratAdd.comp (computable_entryVal.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂

/-- The value of an entry is nonnegative. -/
private lemma entryVal_nonneg (e : TestEntry) : 0 ≤ entryVal e := by
  unfold entryVal
  positivity

/-- The total value of a list is nonnegative. -/
private lemma listVal_nonneg (L : List TestEntry) : 0 ≤ listVal L := by
  induction L with
  | nil => simp [listVal]
  | cons e L ih => exact add_nonneg (entryVal_nonneg e) ih

/-- The total value of a list, as a sum of extended reals. -/
private lemma ofReal_listVal (L : List TestEntry) :
    ENNReal.ofReal (listVal L) = (L.map fun e ↦ ENNReal.ofReal (entryVal e)).sum := by
  induction L with
  | nil => simp [listVal]
  | cons e L ih =>
    have hcons : listVal (e :: L) = entryVal e + listVal L := rfl
    rw [hcons, Rat.cast_add, ENNReal.ofReal_add (by exact_mod_cast entryVal_nonneg e)
      (by exact_mod_cast listVal_nonneg L), ih, List.map_cons, List.sum_cons]

/-- The real weight `2^{-k} n^{-2}` as an extended real, for `n ≥ 1`. -/
private lemma ofReal_weight (k n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k / (n : ℝ) ^ 2) = (2 : ℝ≥0∞)⁻¹ ^ k / (n : ℝ≥0∞) ^ 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn) 2
  rw [ENNReal.ofReal_div_of_pos hn', ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast]

/-- The value of an entry with `n ≥ 1` is `2^{-k} n^{-2} / b`, `b = (a + 1)/(N + 1)`. -/
private lemma ofReal_entryVal (e : TestEntry) (hn : 1 ≤ e.1) :
    ENNReal.ofReal (entryVal e) =
      (2 : ℝ≥0∞)⁻¹ ^ e.2.2.1 / (e.1 : ℝ≥0∞) ^ 2 / ENNReal.ofReal (entryBound e) := by
  obtain ⟨n, i, k, a, N⟩ := e
  dsimp only at hn ⊢
  have hb : (0 : ℝ) < (entryBound (n, i, k, a, N) : ℝ) := by
    simp only [entryBound]
    push_cast
    positivity
  rw [← ofReal_weight k n hn, ← ENNReal.ofReal_div_of_pos hb]
  congr 1
  simp only [entryVal, entryBound, max_eq_right hn]
  push_cast
  field_simp
  rw [← mul_pow]
  norm_num
/-- The power `2^m` as the extended real of a rational. -/
private lemma ofReal_two_pow (m : ℕ) :
    ENNReal.ofReal ((((2 ^ m : ℕ) : ℚ)) : ℝ) = (2 : ℝ≥0∞) ^ m := by
  push_cast
  rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-! ### The summands of the test function -/

/-- The summand of the pair `(n, i)` of the test function at the point `y`. -/
private noncomputable def testTerm (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) (ε : ℝ) (y : X) (p : ℕ × ℕ) : ℝ≥0∞ :=
  if p.1 = 0 then 0 else
    (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A p.2 / (p.1 : ℝ≥0∞) ^ 2 *
      ((bowenBall T p.1 (P.ι p.2) ε).indicator (fun _ ↦ (1 : ℝ≥0∞)) y /
        μ (closedBowenBall T p.1 (P.ι p.2) ε))

omit [BorelSpace X] in
/-- The test function as a sum over pairs `(n, i)`. -/
private lemma testFunction_eq_tsum (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) (ε : ℝ) (y : X) :
    testFunction P T A μ ε y = ∑' p : ℕ × ℕ, testTerm P T A μ ε y p :=
  (ENNReal.tsum_prod (f := fun n i ↦ testTerm P T A μ ε y (n, i))).symm

omit [BorelSpace X] in
/-- At a point of the Bowen ball, the summand of a pair `(n, i)` with `n ≥ 1` is
`2^{-K^A(i)} n^{-2} / μ(B̄_n(x_i, T, ε))`. -/
private lemma testTerm_of_mem (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) (ε : ℝ) {y : X} {n i : ℕ} (hn : n ≠ 0)
    (hy : y ∈ bowenBall T n (P.ι i) ε) :
    testTerm P T A μ ε y (n, i) = (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i / (n : ℝ≥0∞) ^ 2 /
      μ (closedBowenBall T n (P.ι i) ε) := by
  simp only [testTerm, hn, ↓reduceIte, indicator_of_mem hy, mul_one_div]

/-- The condition on the entry `e` at position `j` of a certificate list `L`: the pair `(n, i)`
occurs first at position `j` among the pairs of `L`, `n ≥ 1`, `K^A(i) < k + 1` and
`μ(B̄_n(x_i, T, ε)) < (a + 1)/(N + 1)`. -/
private def EntryGood (P : Presentation X) (T : X → X) (A : Set ℕ) (μ : Measure X) (ε : ℝ)
    (w : List TestEntry × ℕ × TestEntry) : Prop :=
  (w.1.map entryPair).idxOf (entryPair w.2.2) = w.2.1 ∧ 1 ≤ w.2.2.1 ∧
    (oracleNatComplexity A w.2.2.2.1 : ℝ) < (((w.2.2.2.2.1 + 1 : ℕ) : ℚ) : ℝ) ∧
    (μ (closedBowenBall T w.2.2.1 (P.ι w.2.2.2.1) ε)).toReal < (entryBound w.2.2 : ℝ)

omit [BorelSpace X] in
/-- A certified list gives a lower bound for the test function at every point of the
intersection of its Bowen balls. -/
private lemma ofReal_listVal_le (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) [IsFiniteMeasure μ] (ε : ℝ) (L : List TestEntry)
    (hL : ∀ j (h : j < L.length), EntryGood P T A μ ε (L, j, L.get ⟨j, h⟩)) {y : X}
    (hy : ∀ e ∈ L, y ∈ bowenBall T e.1 (P.ι e.2.1) ε) :
    ENNReal.ofReal (listVal L) ≤ testFunction P T A μ ε y := by
  classical
  have hgood : ∀ e ∈ L, ENNReal.ofReal (entryVal e) ≤ testTerm P T A μ ε y (entryPair e) := by
    intro e he
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
    obtain ⟨-, hn, hK, hd⟩ := hL j hj
    simp only [List.get_eq_getElem] at hn hK hd
    rw [ofReal_entryVal _ hn, show entryPair L[j] = (L[j].1, L[j].2.1) from rfl,
      testTerm_of_mem P T A μ ε (by omega) (hy _ he)]
    have hKk : oracleNatComplexity A L[j].2.1 ≤ L[j].2.2.1 := by
      have : (oracleNatComplexity A L[j].2.1 : ℝ) < L[j].2.2.1 + 1 := by exact_mod_cast hK
      exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
    have hdb : μ (closedBowenBall T L[j].1 (P.ι L[j].2.1) ε) ≤
        ENNReal.ofReal (entryBound L[j]) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal hd.le
    exact ENNReal.div_le_div (ENNReal.div_le_div_right (pow_le_pow_of_le_one (by positivity)
      (ENNReal.inv_le_one.2 one_le_two) hKk) _) hdb
  have hnodup : (L.map entryPair).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map] at hij
    have hi' := (hL i hi).1
    have hj' := (hL j hj).1
    simp only [List.get_eq_getElem] at hi' hj'
    rw [hij] at hi'
    exact Fin.ext (hi'.symm.trans hj')
  rw [ofReal_listVal, testFunction_eq_tsum]
  calc (L.map fun e ↦ ENNReal.ofReal (entryVal e)).sum
      ≤ (L.map fun e ↦ testTerm P T A μ ε y (entryPair e)).sum := List.sum_le_sum hgood
    _ = ∑ p ∈ (L.map entryPair).toFinset, testTerm P T A μ ε y p := by
        rw [List.sum_toFinset _ hnodup, List.map_map]
        rfl
    _ ≤ ∑' p : ℕ × ℕ, testTerm P T A μ ε y p := ENNReal.sum_le_tsum _

omit [BorelSpace X] in
/-- A point where the test function exceeds `2^m` carries a certified list. -/
private lemma exists_certificate_of_lt (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) [IsFiniteMeasure μ] (ε : ℝ) (m : ℕ) {y : X}
    (hy : (2 : ℝ≥0∞) ^ m < testFunction P T A μ ε y) :
    ∃ L : List TestEntry, ((2 ^ m : ℕ) : ℚ) < listVal L ∧
      (∀ j (h : j < L.length), EntryGood P T A μ ε (L, j, L.get ⟨j, h⟩)) ∧
      ∀ e ∈ L, y ∈ bowenBall T e.1 (P.ι e.2.1) ε := by
  classical
  rw [testFunction_eq_tsum, ENNReal.tsum_eq_iSup_sum] at hy
  obtain ⟨S, hS⟩ := lt_iSup_iff.mp hy
  set S' := S.filter fun p : ℕ × ℕ ↦ p.1 ≠ 0 ∧ y ∈ bowenBall T p.1 (P.ι p.2) ε with hS'
  have hmem : ∀ p ∈ S', p.1 ≠ 0 ∧ y ∈ bowenBall T p.1 (P.ι p.2) ε := fun p hp ↦
    (Finset.mem_filter.mp hp).2
  -- the weights and the measures of the closed balls
  let c : ℕ × ℕ → ℝ≥0∞ := fun p ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A p.2 / (p.1 : ℝ≥0∞) ^ 2
  let d : ℕ × ℕ → ℝ≥0∞ := fun p ↦ μ (closedBowenBall T p.1 (P.ι p.2) ε)
  have hsum : ∑ p ∈ S, testTerm P T A μ ε y p = ∑ p ∈ S', c p / d p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    split_ifs with h
    · exact testTerm_of_mem P T A μ ε h.1 h.2
    · by_cases h0 : p.1 = 0
      · simp [testTerm, h0]
      · have hy' : y ∉ bowenBall T p.1 (P.ι p.2) ε := fun hy' ↦ h ⟨h0, hy'⟩
        simp [testTerm, h0, hy']
  rw [hsum] at hS
  -- rational upper bounds `(⌊d (N + 1)⌋ + 1)/(N + 1)` for the measures
  let e : ℕ → ℕ × ℕ → TestEntry := fun N p ↦
    (p.1, p.2, oracleNatComplexity A p.2, ⌊(d p).toReal * (N + 1)⌋₊, N)
  have hlow : ∀ N p, (d p).toReal < (entryBound (e N p) : ℝ) := by
    intro N p
    simp only [entryBound, e]
    push_cast
    rw [lt_div_iff₀ (by positivity)]
    exact Nat.lt_floor_add_one _
  have hup : ∀ N p, (entryBound (e N p) : ℝ) ≤ (d p).toReal + 1 / ((N : ℝ) + 1) := by
    intro N p
    simp only [entryBound, e]
    push_cast
    rw [div_le_iff₀ (by positivity), add_mul, one_div_mul_cancel (by positivity)]
    gcongr
    exact Nat.floor_le (by positivity)
  have hlim : ∀ p, Tendsto (fun N ↦ ENNReal.ofReal (entryBound (e N p))) atTop (𝓝 (d p)) := by
    intro p
    have h0 : Tendsto (fun N : ℕ ↦ (d p).toReal + 1 / ((N : ℝ) + 1)) atTop
        (𝓝 (d p).toReal) := by
      have h1 := (tendsto_const_nhds (x := (d p).toReal) (f := (atTop : Filter ℕ))).add
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h1
    have h := ENNReal.tendsto_ofReal (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h0 (fun N ↦ (hlow N p).le) (fun N ↦ hup N p))
    rwa [ENNReal.ofReal_toReal (measure_ne_top μ _)] at h
  have hval : Tendsto (fun N ↦ ∑ p ∈ S', c p / ENNReal.ofReal (entryBound (e N p))) atTop
      (𝓝 (∑ p ∈ S', c p / d p)) := by
    refine tendsto_finsetSum _ fun p _ ↦ ?_
    exact ENNReal.Tendsto.div tendsto_const_nhds
      (Or.inl (ENNReal.div_ne_zero.mpr ⟨by simp, by simp⟩)) (hlim p)
      (Or.inl (measure_ne_top _ _))
  obtain ⟨N, hN⟩ := (hval.eventually (lt_mem_nhds hS)).exists
  refine ⟨S'.toList.map (e N), ?_, fun j hj ↦ ?_, fun f hf ↦ ?_⟩
  · have h1 : ENNReal.ofReal (listVal (S'.toList.map (e N))) =
        ∑ p ∈ S', c p / ENNReal.ofReal (entryBound (e N p)) := by
      rw [ofReal_listVal, List.map_map, Finset.sum_map_toList]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      exact ofReal_entryVal (e N p) (Nat.one_le_iff_ne_zero.mpr (hmem p hp).1)
    rw [← h1, ← ofReal_two_pow, ENNReal.ofReal_lt_ofReal_iff'] at hN
    exact_mod_cast hN.1
  · have hj' : j < S'.toList.length := by simpa using hj
    have hp : S'.toList[j] ∈ S' := Finset.mem_toList.mp (List.getElem_mem hj')
    have hpairs : (S'.toList.map (e N)).map entryPair = S'.toList := by
      rw [List.map_map]
      exact List.map_id'' (fun _ ↦ rfl) _
    simp only [EntryGood, List.get_eq_getElem, List.getElem_map]
    refine ⟨?_, Nat.one_le_iff_ne_zero.mpr (hmem _ hp).1, ?_, hlow N _⟩
    · rw [hpairs]
      exact (Finset.nodup_toList S').idxOf_getElem j hj'
    · push_cast
      simp [e]
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    exact (hmem p (Finset.mem_toList.mp hp)).2

/-! ### The levels of the test function form a test -/

/-- The certificate condition is relatively enumerable in an admissible oracle. -/
private lemma isREIn_entryGood (P : Presentation X) (T : X → X) (A : Set ℕ) (μ : Measure X)
    [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) :
    IsREIn A (EntryGood P T A μ (ε : ℝ)) := by
  have hn : Primrec fun w : List TestEntry × ℕ × TestEntry ↦ w.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec fun w : List TestEntry × ℕ × TestEntry ↦ w.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hk : Primrec fun w : List TestEntry × ℕ × TestEntry ↦ w.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hidx : IsREIn A fun w : List TestEntry × ℕ × TestEntry ↦
      (w.1.map entryPair).idxOf (entryPair w.2.2) = w.2.1 :=
    isREIn_of_computable_decide (Primrec.eq.comp (Primrec.list_idxOf.comp
      (primrec_entryPair.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_map Primrec.fst (primrec_entryPair.comp Primrec.snd).to₂))
      (Primrec.fst.comp Primrec.snd)).decide.to_comp
  have hn1 : IsREIn A fun w : List TestEntry × ℕ × TestEntry ↦ 1 ≤ w.2.2.1 :=
    isREIn_of_computable_decide (Primrec.nat_le.comp (Primrec.const 1) hn).decide.to_comp
  have hK : IsREIn A fun w : List TestEntry × ℕ × TestEntry ↦
      (oracleNatComplexity A w.2.2.2.1 : ℝ) < (((w.2.2.2.2.1 + 1 : ℕ) : ℚ) : ℝ) :=
    (isREIn_oracleNatComplexity_lt A).comp
      (f := fun w : List TestEntry × ℕ × TestEntry ↦ (w.2.2.2.1, ((w.2.2.2.2.1 + 1 : ℕ) : ℚ)))
      (hi.to_comp.pair (ComputableReals.computable_natCastRat.comp
        (Primrec.succ.comp hk).to_comp)).computableIn
  have hd : IsREIn A fun w : List TestEntry × ℕ × TestEntry ↦
      (μ (closedBowenBall T w.2.2.1 (P.ι w.2.2.2.1) (ε : ℝ))).toReal < (entryBound w.2.2 : ℝ) :=
    hA.isREIn_measure_closedBowenBall_lt.comp
      (f := fun w : List TestEntry × ℕ × TestEntry ↦ ((w.2.2.1, w.2.2.2.1, ε), entryBound w.2.2))
      ((hn.to_comp.pair (hi.to_comp.pair (Computable.const ε))).pair
        (computable_entryBound.comp (Computable.snd.comp Computable.snd))).computableIn
  exact hidx.and (hn1.and (hK.and hd))

/-- The test function of Lemma 3.2 is finite at every random point.
Blueprint node `meas:test`. -/
theorem testFunction_lt_top_of_mem_randomPoints (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) {x : X}
    (hx : x ∈ randomPoints P A μ) : testFunction P T A μ (ε : ℝ) x < ⊤ := by
  -- the certificate predicate
  let C : ℕ × (Unit × List TestEntry) → Prop := fun p ↦
    ((2 ^ p.1 : ℕ) : ℚ) < listVal p.2.2 ∧
      ∀ j (h : j < p.2.2.length), EntryGood P T A μ (ε : ℝ) (p.2.2, j, p.2.2.get ⟨j, h⟩)
  have hC : IsREIn A C := by
    have h1 : IsREIn A fun p : ℕ × (Unit × List TestEntry) ↦
        ((2 ^ p.1 : ℕ) : ℚ) < listVal p.2.2 :=
      isREIn_of_computable_decide (computable₂_ratLt.comp
        (ComputableReals.computable_natCastRat.comp
          (nat_pow_primrec₂.comp (Primrec.const 2) Primrec.fst).to_comp)
        (computable_listVal.comp (Computable.snd.comp Computable.snd)))
    have h2 : IsREIn A fun p : ℕ × (Unit × List TestEntry) ↦
        ∀ j (h : j < p.2.2.length), EntryGood P T A μ (ε : ℝ) (p.2.2, j, p.2.2.get ⟨j, h⟩) :=
      (isREIn_entryGood P T A μ hA ε).list_forall_get.comp
        (f := fun p : ℕ × (Unit × List TestEntry) ↦ (p.2.2, p.2.2))
        ((Computable.snd.comp Computable.snd).pair
          (Computable.snd.comp Computable.snd)).computableIn
    exact h1.and h2
  have hU : IsCeOpenFamilyIn P A fun ue : Unit × TestEntry ↦
      bowenBall T ue.2.1 (P.ι ue.2.2.1) (ε : ℝ) :=
    (isCeOpenFamilyIn_bowenBall P T A hA.1 hA.2.1).comp
      (g := fun ue : Unit × TestEntry ↦ (ue.2.1, ue.2.2.1, ε))
      ((Computable.fst.comp Computable.snd).pair ((Computable.fst.comp
        (Computable.snd.comp Computable.snd)).pair (Computable.const ε)))
  -- the levels of the test
  let V : ℕ → Set X := fun m ↦
    ⋃ uL ∈ {uL | C (m, uL)}, ⋂ e ∈ uL.2, bowenBall T e.1 (P.ι e.2.1) (ε : ℝ)
  have hV : IsCeOpenFamilyIn P A V := (hU.biInter_list hA.1).iUnion_of_isREIn hC
  have hVsub : ∀ m, V m ⊆ {y | (2 : ℝ≥0∞) ^ m < testFunction P T A μ (ε : ℝ) y} := by
    intro m y hy
    obtain ⟨uL, ⟨hlt, hgood⟩, hyL⟩ := mem_iUnion₂.mp hy
    refine lt_of_lt_of_le ?_ (ofReal_listVal_le P T A μ (ε : ℝ) uL.2 hgood
      fun e he ↦ mem_iInter₂.mp hyL e he)
    have hpos : (0 : ℝ) < (listVal uL.2 : ℝ) := by
      have : (0 : ℚ) < listVal uL.2 := lt_trans (by positivity) hlt
      exact_mod_cast this
    rw [← ofReal_two_pow, ENNReal.ofReal_lt_ofReal_iff hpos]
    exact_mod_cast hlt
  have hVopen : ∀ m, MeasurableSet (V m) := by
    obtain ⟨E, -, hE⟩ := hV
    intro m
    rw [hE m]
    exact (isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball).measurableSet
  -- Markov's inequality
  have hμV : ∀ m, μ (V m) ≤ (2 : ℝ≥0∞) ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ m := by
    intro m
    have h1 : (2 : ℝ≥0∞) ^ m * μ (V m) ≤ 2 := by
      rw [← lintegral_indicator_const (hVopen m)]
      refine le_trans (lintegral_mono fun y ↦ ?_)
        (lintegral_testFunction_lt_two P T hT A μ (ε : ℝ)).le
      by_cases hy : y ∈ V m
      · rw [indicator_of_mem hy]
        exact (hVsub m hy).le
      · rw [indicator_of_notMem hy]
        exact zero_le
    calc μ (V m) = (2 : ℝ≥0∞)⁻¹ ^ m * ((2 : ℝ≥0∞) ^ m * μ (V m)) := by
          rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
            one_pow, one_mul]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m * 2 := by gcongr
      _ = (2 : ℝ≥0∞) ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ m := by rw [pow_one, mul_comm]
  obtain ⟨m, hm⟩ := not_forall_mem_of_mem_randomPoints hx hV (c := 1) hμV
  refine lt_top_iff_ne_top.mpr fun htop ↦ hm ?_
  have hlt : (2 : ℝ≥0∞) ^ m < testFunction P T A μ (ε : ℝ) x := by
    rw [htop]
    exact ENNReal.pow_lt_top (by simp)
  obtain ⟨L, hL1, hL2, hL3⟩ := exists_certificate_of_lt P T A μ (ε : ℝ) m hlt
  exact mem_iUnion₂.mpr ⟨((), L), ⟨hL1, hL2⟩, mem_iInter₂.mpr hL3⟩

end Kolmogorov.PointToSet
