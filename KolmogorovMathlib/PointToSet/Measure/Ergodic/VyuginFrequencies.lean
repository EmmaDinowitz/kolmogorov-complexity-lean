/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Ergodic.Upcrossing
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ShiftRandomness

/-!
# Word frequencies converge at random points (V'yugin, non-ergodic)

For a shift-invariant (not necessarily ergodic) probability measure `μ` on `ℕ → α` with a
first-difference metric, an oracle `A` admissible for `μ` that computes the symbols of the ideal
points, and a `μ`-random point `x` relative to `A`, the frequency of every word `w` in `x`
converges. Proof: for rationals `a < b` the sets
`U_m = {y | ∃ L, the visit frequencies of [w] upcross [a, b] at least 2^m c₀ times by L}` are
uniformly `A`-c.e. open (`vyuginFreq_isCeOpenFamilyIn_upcrosses`), and `μ(U_m) ≤ 2^{-m}` by
Bishop's inequality (`measureReal_upcrossesAtLeast_le`), so they form a test; a random `x`
avoids some `U_m`, hence its frequencies upcross each rational interval only boundedly often,
and they converge (`exists_tendsto_of_forall_not_upcrossesAtLeast`).

The word frequencies are the Cesàro averages of `f = 1_{[w]}` along the shift orbit
(`vyuginFreq_ncard_eq_typicalVisitCount`, `vyuginFreq_cesaroAvg_indicator`). For `n ≥ 1` the
conditions "average `< a` at time `n`" and "average `> b` at time `n`" are the counting
conditions `(1 - a) n < #{j < n | σ^j y ∉ [w]}` and `b n < #{j < n | σ^j y ∈ [w]}`
(`vyuginFreq_cesaroAvg_lt_iff`, `vyuginFreq_lt_cesaroAvg_iff`), which are uniformly c.e. open by
`isCeOpenFamilyIn_typicalVisitCount_gt` (cylinders and their complements are c.e. open,
`isCeOpenFamilyIn_listCylinder`). A crossing set is then a union, over the decidable set of
witness lists `[(u₀, v₀), …]` (`VyuginFreqGoodList`), of finite intersections of such sets. The
test uses neither ergodicity nor the computability of `μ`.

Blueprint node `erg:vyugin`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability
open Kolmogorov.Ergodic

variable {α : Type*} [Finite α] [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]
  [BorelSpace (ℕ → α)] {β : ℝ}

omit [Finite α] [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]
  [BorelSpace (ℕ → α)] in
/-- The number of occurrences of a word `w` in `x` starting before time `n` is the number of
visits of the shift orbit of `x` to the cylinder `[w]` before time `n`. -/
theorem vyuginFreq_ncard_eq_typicalVisitCount (x : ℕ → α) {k : ℕ} (w : Fin k → α) (n : ℕ) :
    ({j | j < n ∧ ∀ i : Fin k, x (j + i) = w i} : Set ℕ).ncard =
      typicalVisitCount shiftMap (listCylinder (List.ofFn w)) n x := by
  rw [← ncard_eq_typicalVisitCount]
  congr 1
  ext j
  simp only [mem_ofPred_eq, iterate_shiftMap, listCylinder, List.length_ofFn,
    List.getElem_ofFn]
  refine and_congr_right fun _ ↦ ⟨fun h i hi ↦ ?_, fun h i ↦ ?_⟩
  · rw [add_comm]
    exact h ⟨i, hi⟩
  · rw [add_comm]
    exact h i i.2

/-- The Cesàro averages of the indicator of `V` along an orbit are the visit frequencies. -/
theorem vyuginFreq_cesaroAvg_indicator {X : Type*} (T : X → X) (V : Set X) (y : X) (n : ℕ) :
    cesaroAvg (fun i ↦ V.indicator (1 : X → ℝ) (T^[i] y)) n =
      (typicalVisitCount T V n y : ℝ) / n := by
  rw [← birkhoffSum_indicator_eq_typicalVisitCount]
  rfl

/-- For `n ≥ 1`, the frequency of visits to `V` is below `a` iff the number of visits to `Vᶜ`
exceeds `(1 - a) n`. -/
theorem vyuginFreq_cesaroAvg_lt_iff {X : Type*} (T : X → X) (V : Set X) (y : X) {n : ℕ}
    (hn : 1 ≤ n) (a : ℚ) :
    cesaroAvg (fun i ↦ V.indicator (1 : X → ℝ) (T^[i] y)) n < a ↔
      ((((1 - a) * n : ℚ)) : ℝ) < typicalVisitCount T Vᶜ n y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (typicalVisitCount T V n y : ℝ) + typicalVisitCount T Vᶜ n y = n := by
    exact_mod_cast typicalVisitCount_add_compl T V n y
  rw [vyuginFreq_cesaroAvg_indicator, div_lt_iff₀ hn0]
  push_cast
  constructor <;> intro h <;> linarith

/-- For `n ≥ 1`, the frequency of visits to `V` is above `b` iff the number of visits to `V`
exceeds `b n`. -/
theorem vyuginFreq_lt_cesaroAvg_iff {X : Type*} (T : X → X) (V : Set X) (y : X) {n : ℕ}
    (hn : 1 ≤ n) (b : ℚ) :
    (b : ℝ) < cesaroAvg (fun i ↦ V.indicator (1 : X → ℝ) (T^[i] y)) n ↔
      (((b * n : ℚ)) : ℝ) < typicalVisitCount T V n y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [vyuginFreq_cesaroAvg_indicator, lt_div_iff₀ hn0]
  push_cast
  rfl

/-- A list of pairs `(u_j, v_j)` is a crossing witness with `k` crossings when it has length `k`
and `1 ≤ u₀ < v₀ < u₁ < ⋯ < u_{k-1} < v_{k-1}`. -/
def VyuginFreqGoodList (d : ℕ × List (ℕ × ℕ)) : Prop :=
  d.2.length = d.1 ∧ ∀ j < d.2.length, 1 ≤ (d.2.getD j (0, 0)).1 ∧
    (d.2.getD j (0, 0)).1 < (d.2.getD j (0, 0)).2 ∧
    (¬ j + 1 < d.2.length ∨ (d.2.getD j (0, 0)).2 < (d.2.getD (j + 1) (0, 0)).1)

/-- Crossing witnesses are recognized primitive recursively. -/
theorem vyuginFreq_primrecPred_goodList : PrimrecPred VyuginFreqGoodList := by
  have hg : Primrec fun p : ℕ × (ℕ × List (ℕ × ℕ)) ↦ p.2.2.getD p.1 (0, 0) :=
    (Primrec.list_getD (0, 0)).comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  have hg' : Primrec fun p : ℕ × (ℕ × List (ℕ × ℕ)) ↦ p.2.2.getD (p.1 + 1) (0, 0) :=
    (Primrec.list_getD (0, 0)).comp (Primrec.snd.comp Primrec.snd)
      (Primrec.succ.comp Primrec.fst)
  have hlen : Primrec fun p : ℕ × (ℕ × List (ℕ × ℕ)) ↦ p.2.2.length :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
  have hR : PrimrecRel fun (j : ℕ) (d : ℕ × List (ℕ × ℕ)) ↦ 1 ≤ (d.2.getD j (0, 0)).1 ∧
      (d.2.getD j (0, 0)).1 < (d.2.getD j (0, 0)).2 ∧
      (¬ j + 1 < d.2.length ∨ (d.2.getD j (0, 0)).2 < (d.2.getD (j + 1) (0, 0)).1) :=
    (Primrec.nat_le.comp (Primrec.const 1) (Primrec.fst.comp hg)).and
      ((Primrec.nat_lt.comp (Primrec.fst.comp hg) (Primrec.snd.comp hg)).and
        ((Primrec.nat_lt.comp (Primrec.succ.comp Primrec.fst) hlen).not.or
          (Primrec.nat_lt.comp (Primrec.snd.comp hg) (Primrec.fst.comp hg'))))
  have h2 := hR.forall_mem_list.comp
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) Primrec.id
  refine (PrimrecPred.and (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst)
    h2).of_eq fun d ↦ ?_
  simp [VyuginFreqGoodList]

omit [Finite α] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- The sets of points whose visit frequencies to a cylinder `[w]` upcross `[a, b]` at least
`k` times are `A`-c.e. open, uniformly in `k`. -/
theorem vyuginFreq_isCeOpenFamilyIn_upcrosses (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ) (hPc : ComputablePresentationIn P A)
    (hTA : IsRepresentedMapIn P P A shiftMap)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) (w : List α) (a b : ℚ) :
    IsCeOpenFamilyIn P A fun k : ℕ ↦ {y | ∃ L, UpcrossesAtLeast a b
      (fun i ↦ (listCylinder w).indicator (1 : (ℕ → α) → ℝ) (shiftMap^[i] y)) k L} := by
  classical
  have hcyl := isCeOpenFamilyIn_listCylinder hβ hβ₁ hd P A hPc hP
  have hC : IsREIn A fun d : List α × List α ↦ d.2.length = d.1.length ∧ d.2 ≠ d.1 :=
    isREIn_of_computable_decide (PrimrecPred.and
      (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.list_length.comp Primrec.fst))
      (PrimrecPred.not (Primrec.eq.comp Primrec.snd Primrec.fst))).decide.to_comp
  have hcompl : IsCeOpenFamilyIn P A fun l : List α ↦ (listCylinder l)ᶜ := by
    have h := hcyl.iUnion_of_isREIn hC
    simp only [iUnion_listCylinder_ne_eq_compl] at h
    exact h
  have hHigh := isCeOpenFamilyIn_typicalVisitCount_gt hPc hTA hcyl
  have hLow := isCeOpenFamilyIn_typicalVisitCount_gt hPc hTA hcompl
  have g1 : Computable fun p : ℕ × ℕ ↦ (w, p.1, (1 - a) * (p.1 : ℚ)) :=
    (Computable.const w).pair (Computable.fst.pair (computable₂_ratMul.comp
      (Computable.const (1 - a)) (computable_nat_to_rat.comp Computable.fst)))
  have g2 : Computable fun p : ℕ × ℕ ↦ (w, p.2, b * (p.2 : ℚ)) :=
    (Computable.const w).pair (Computable.snd.pair (computable₂_ratMul.comp
      (Computable.const b) (computable_nat_to_rat.comp Computable.snd)))
  have hQ := (IsCeOpenFamilyIn.inter P A hPc (hLow.comp g1) (hHigh.comp g2)).comp
    (Computable.snd (α := ℕ) (β := ℕ × ℕ))
  have H := ((hQ.biInter_list hPc).ite
    vyuginFreq_primrecPred_goodList.decide.to_comp).iUnion
  convert H using 1
  funext k
  ext y
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨L, u, v, huv⟩
    refine ⟨(List.range k).map fun i ↦ (u i, v i), ?_⟩
    have hget : ∀ j < k, ((List.range k).map fun i ↦ (u i, v i)).getD j (0, 0) = (u j, v j) := by
      intro j hj
      rw [List.getD_eq_getElem _ _ (by simpa using hj)]
      simp
    have hgood : VyuginFreqGoodList (k, (List.range k).map fun i ↦ (u i, v i)) := by
      refine ⟨by simp, fun j hj ↦ ?_⟩
      simp only [List.length_map, List.length_range] at hj ⊢
      obtain ⟨h1, h2, -, h4, -, -⟩ := huv j hj
      rw [hget j hj]
      refine ⟨h1, h2, ?_⟩
      by_cases hj1 : j + 1 < k
      · exact Or.inr (by rw [hget (j + 1) hj1]; exact h4 hj1)
      · exact Or.inl hj1
    simp only [hgood, ↓reduceIte, mem_iInter, mem_inter_iff, mem_ofPred_eq]
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, -, -, h5, h6⟩ := huv i (List.mem_range.mp hi)
    exact ⟨(vyuginFreq_cesaroAvg_lt_iff _ _ _ h1 a).1 h5,
      (vyuginFreq_lt_cesaroAvg_iff _ _ _ (h1.trans h2.le) b).1 h6⟩
  · rintro ⟨l, hl⟩
    by_cases hgood : VyuginFreqGoodList (k, l)
    · simp only [hgood, ↓reduceIte, mem_iInter, mem_inter_iff, mem_ofPred_eq] at hl
      obtain ⟨hlen, hord⟩ := hgood
      dsimp only at hlen hord
      refine ⟨(Finset.range k).sup fun i ↦ (l.getD i (0, 0)).2, fun i ↦ (l.getD i (0, 0)).1,
        fun i ↦ (l.getD i (0, 0)).2, fun i hi ↦ ?_⟩
      have hi' : i < l.length := by omega
      obtain ⟨h1, h2, h3⟩ := hord i hi'
      have hmem : l.getD i (0, 0) ∈ l := by
        rw [List.getD_eq_getElem _ _ hi']
        exact List.getElem_mem hi'
      obtain ⟨hlo, hhi⟩ := hl _ hmem
      refine ⟨h1, h2, Finset.le_sup (f := fun i ↦ (l.getD i (0, 0)).2) (Finset.mem_range.2 hi),
        fun hi1 ↦ h3.resolve_left (by omega),
        (vyuginFreq_cesaroAvg_lt_iff _ _ _ h1 a).2 hlo,
        (vyuginFreq_lt_cesaroAvg_iff _ _ _ (h1.trans h2.le) b).2 hhi⟩
    · simp only [hgood, ↓reduceIte, mem_empty_iff_false] at hl

omit [Finite α] in
/-- V'yugin's effective ergodic theorem for word frequencies, relativized, for a shift-invariant
measure that need not be ergodic: at every random point every word frequency converges.
Blueprint node `erg:vyugin`. -/
theorem exists_tendsto_frequency_of_mem_randomPoints (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → α)) [IsProbabilityMeasure μ] (hμ : MeasurePreserving shiftMap μ μ)
    (hA : IsMeasureAdmissible P shiftMap μ A) {x : ℕ → α} (hx : x ∈ randomPoints P A μ)
    (k : ℕ) (w : Fin k → α) :
    ∃ l : ℝ, Tendsto
      (fun n : ℕ ↦ ((({j | j < n ∧ ∀ i : Fin k, x (j + i) = w i} : Set ℕ).ncard : ℝ) / n))
      atTop (𝓝 l) := by
  set W : Set (ℕ → α) := listCylinder (List.ofFn w) with hW_def
  have hcyl := isCeOpenFamilyIn_listCylinder hβ hβ₁ hd P A hA.1 hP
  have hWm : MeasurableSet W := (isOpen_of_isCeOpenFamilyIn_typical hcyl _).measurableSet
  set f : (ℕ → α) → ℝ := W.indicator 1 with hf_def
  have hf : Measurable f := measurable_one.indicator hWm
  have hf01 : ∀ y, 0 ≤ f y ∧ f y ≤ 1 := fun y ↦ by
    by_cases hy : y ∈ W <;> simp [hf_def, hy]
  have hfC : ∀ y, |f y| ≤ 1 := fun y ↦ abs_le.2 ⟨by linarith [(hf01 y).1], (hf01 y).2⟩
  -- the test: the frequencies upcross `[a, b]` at least `2^m c` times
  have key : ∀ a b : ℚ, a < b → ∃ K, ∀ L,
      ¬ UpcrossesAtLeast a b (fun i ↦ f (shiftMap^[i] x)) K L := by
    intro a b hab
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    obtain ⟨c₀, hc₀⟩ := exists_nat_ge ((1 + |(a : ℝ)|) / ((b : ℝ) - a))
    set c : ℕ := c₀ + 1 with hc_def
    let U : ℕ → Set (ℕ → α) := fun m ↦
      {y | ∃ L, UpcrossesAtLeast a b (fun i ↦ f (shiftMap^[i] y)) (2 ^ m * c) L}
    have hUce : IsCeOpenFamilyIn P A U :=
      (vyuginFreq_isCeOpenFamilyIn_upcrosses hβ hβ₁ hd P A hA.1 hA.2.1 hP (List.ofFn w) a b).comp
        (g := fun m ↦ 2 ^ m * c)
        (Primrec.nat_mul.comp (nat_pow_primrec₂.comp (Primrec.const 2) Primrec.id)
          (Primrec.const c)).to_comp
    have hint : ∫ y, max (f y - a) 0 ∂μ ≤ 1 + |(a : ℝ)| := by
      have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y ↦ max (f y - a) 0)
        (C := 1 + |(a : ℝ)|) (Eventually.of_forall fun y ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
          refine max_le ?_ (by positivity)
          linarith [(hf01 y).2, neg_abs_le (a : ℝ)])
      rw [probReal_univ, mul_one] at h
      exact (le_abs_self _).trans h
    have hUμ : ∀ m, μ (U m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
      intro m
      have hK : 1 ≤ 2 ^ m * c := Nat.one_le_iff_ne_zero.2 (by positivity)
      have h := measureReal_upcrossesAtLeast_le hμ hf hfC hab' hK
      have hc1 : (1 + |(a : ℝ)|) ≤ ((b : ℝ) - a) * c := by
        rw [div_le_iff₀ (sub_pos.2 hab')] at hc₀
        have : (c₀ : ℝ) ≤ c := by rw [hc_def]; push_cast; linarith
        nlinarith [sub_pos.2 hab']
      have hreal : μ.real (U m) ≤ (2 : ℝ)⁻¹ ^ m := by
        refine h.trans ?_
        have hpos : (0 : ℝ) < ((b : ℝ) - a) * ((2 ^ m * c : ℕ) : ℝ) := by
          have : (0 : ℝ) < ((2 ^ m * c : ℕ) : ℝ) := by exact_mod_cast hK
          exact mul_pos (sub_pos.2 hab') this
        rw [div_le_iff₀ hpos]
        calc ∫ y, max (f y - a) 0 ∂μ ≤ 1 + |(a : ℝ)| := hint
          _ ≤ ((b : ℝ) - a) * c := hc1
          _ = (2 : ℝ)⁻¹ ^ m * (((b : ℝ) - a) * ((2 ^ m * c : ℕ) : ℝ)) := by
            have h2 : (2 : ℝ)⁻¹ ^ m * 2 ^ m = 1 := by
              rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
            push_cast
            linear_combination (-((b : ℝ) - a) * c) * h2
      rw [← ofReal_measureReal]
      refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
        ENNReal.ofReal_ofNat]
    obtain ⟨m, hm⟩ := hx U ⟨hUce, hUμ⟩
    exact ⟨2 ^ m * c, fun L hL ↦ hm ⟨L, hL⟩⟩
  obtain ⟨l, hl⟩ := exists_tendsto_of_forall_not_upcrossesAtLeast (C := 1) (fun i ↦ hfC _) key
  refine ⟨l, hl.congr fun n ↦ ?_⟩
  rw [vyuginFreq_cesaroAvg_indicator, vyuginFreq_ncard_eq_typicalVisitCount]

end Kolmogorov.PointToSet
