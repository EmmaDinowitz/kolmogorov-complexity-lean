/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ShiftRandomness
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupBasic
import KolmogorovMathlib.Oracle.PrefixComplexity.TwoStage

/-!
# The Levin–Schnorr estimate on Cantor space with the complexity of the word (Remark 3.4(b))

On Cantor space `ℕ → Bool` with the metric `2^{-firstDiff}`, for an oracle `A` admissible for a
measure `μ` (of mass at most one) that also computes the symbols of the ideal points of the
presentation:

* `oracleComplexity_cantorPrefix_le_infoBits'` (coding direction, every point):
  `K^A(x↾n) ≤ -log₂ μ[x↾n] + O(log n)` whenever `μ[x↾n] > 0`.
* `infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints'` (incompressibility
  direction, random points of a probability measure): `-log₂ μ[x↾n] ≤ K^A(x↾n) + O(1)`.

The coding direction applies the coding theorem `oracle_coding_finite_mass` to the words `w`
with `μ[w] > 0` and the integer cost `k₀(w) + 2 (⌊log₂ |w|⌋ + 1)`, `k₀(w)` the least `k` with
`2^{-k} < μ[w]`; it is upper semicomputable because `w ↦ μ[w]` is lower semicomputable (the
cylinders are uniformly c.e. open, `isCeOpenFamilyIn_listCylinder`). Its mass is at most
`∑_n 2^{-2(⌊log₂ n⌋+1)} ∑_{|w| = n} μ[w] < ∞`, since the cylinders of the words of a given
length are pairwise disjoint.

The incompressibility direction is a translation of the Levin–Schnorr step of the Hoyrup files
(`exists_infoBits_le_wordComplexity_add`) through `mem_wordRandomPoints_of_mem_randomPoints`
and `isComputableWordMeasureIn_of_isComputableMeasureIn`, with
`K^A(encode w) ≤ K^A(w) + O(1)`.

Blueprint node `meas:remarks`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

section cantor

attribute [local instance] cantorMetricSpace

/-- The cylinder of the word `x↾n` is the cylinder `PiNat.cylinder x n`. Blueprint node
`meas:remarks`. -/
theorem cantorLS_listCylinder_cantorPrefix (x : ℕ → Bool) (n : ℕ) :
    listCylinder (cantorPrefix x n) = PiNat.cylinder x n :=
  listCylinder_wordPrefix x n

/-- The code of a binary word as a natural number costs at most a constant more than the word:
`K^A(encode w) ≤ K^A(w) + c`. Blueprint node `meas:remarks`. -/
theorem cantorLS_exists_oracleNatComplexity_encode_le (A : Set ℕ) :
    ∃ c : ℕ, ∀ w : List Bool,
      oracleNatComplexity A (Encodable.encode w) ≤ oracleComplexity A w + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_map_le_of_computableIn A
    (fun w : BitString ↦ natBits (Encodable.encode w))
    (natBits_computable.comp Computable.encode).computableIn
  exact ⟨c, fun w ↦ hc w []⟩

/-! ### Incompressibility direction -/

/-- Remark 3.4(b), incompressibility direction (primed copy of
`infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints`): at every `x ∈ R_A^μ`,
`-log₂ μ[x↾n] ≤ K^A(x↾n) + O(log n)` (in fact `+ O(1)`). Blueprint node `meas:remarks`. -/
theorem infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints'
    (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P shiftMap μ A)
    {x : ℕ → Bool} (hx : x ∈ randomPoints P A μ) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n →
      (infoBits (μ (PiNat.cylinder x n))).toReal ≤
        oracleComplexity A (cantorPrefix x n) + c * Real.logb 2 n + c := by
  have hc := isComputableWordMeasureIn_of_isComputableMeasureIn (by norm_num) (by norm_num)
    cantor_hd P A hA.1 hP μ hA.2.2
  have hw := mem_wordRandomPoints_of_mem_randomPoints (by norm_num) (by norm_num)
    cantor_hd P A hA.1 hP μ hx
  obtain ⟨c₁, h₁⟩ := exists_infoBits_le_wordComplexity_add hc hw
  obtain ⟨c₂, h₂⟩ := cantorLS_exists_oracleNatComplexity_encode_le A
  refine ⟨((c₁ + c₂ : ℕ) : ℝ), fun n _ ↦ ?_⟩
  have hK : wordComplexity A x n ≤ oracleComplexity A (cantorPrefix x n) + c₂ := h₂ _
  have h : infoBits (μ (PiNat.cylinder x n)) ≤
      ((oracleComplexity A (cantorPrefix x n) + c₂ + c₁ : ℕ) : ℝ≥0∞) := by
    have h₁n := h₁ n
    rw [show wordPrefix x n = cantorPrefix x n from rfl,
      cantorLS_listCylinder_cantorPrefix] at h₁n
    refine h₁n.trans ?_
    exact_mod_cast Nat.add_le_add_right hK c₁
  have hr := ENNReal.toReal_mono (by simp) h
  rw [ENNReal.toReal_natCast] at hr
  have hl : 0 ≤ ((c₁ + c₂ : ℕ) : ℝ) * Real.logb 2 n :=
    mul_nonneg (by positivity) (logb_natCast_nonneg n)
  push_cast at hr hl ⊢
  linarith

/-! ### Coding direction -/

/-- The length part `2 (⌊log₂ |w|⌋ + 1)` of the coding cost of a word. Blueprint node
`meas:remarks`. -/
def cantorLS_lenCost (w : List Bool) : ℕ := 2 * (Nat.log 2 w.length + 1)

/-- The length cost is primitive recursive. -/
private lemma cantorLS_primrec_lenCost : Primrec cantorLS_lenCost :=
  (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.succ.comp (primrec_natLogTwo.comp Primrec.list_length))).of_eq fun _ ↦ rfl

/-- The words of a given length carry total mass at most `μ univ`. -/
private lemma cantorLS_tsum_length_eq_le (μ : Measure (ℕ → Bool)) (n : ℕ) :
    ∑' w : List Bool, (if w.length = n then μ (listCylinder w) else 0) ≤ μ univ := by
  classical
  let C : List Bool → Set (ℕ → Bool) := fun w ↦ if w.length = n then listCylinder w else ∅
  have hC : ∀ w, (if w.length = n then μ (listCylinder w) else 0) = μ (C w) := by
    intro w
    by_cases hw : w.length = n <;> simp [C, hw]
  have hmeas : ∀ w, MeasurableSet (C w) := by
    intro w
    by_cases hw : w.length = n
    · simpa [C, hw] using measurableSet_listCylinder w
    · simp [C, hw]
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro w w' hne
    by_cases hw : w.length = n
    · by_cases hw' : w'.length = n
      · simp only [Function.onFun, C, hw, hw', ↓reduceIte]
        refine Set.disjoint_left.2 fun y hy hy' ↦ hne ?_
        refine List.ext_getElem (hw.trans hw'.symm) fun i h1 h2 ↦ ?_
        exact (hy i h1).symm.trans (hy' i h2)
      · simp [Function.onFun, C, hw']
    · simp [Function.onFun, C, hw]
  simp_rw [hC]
  rw [← measure_iUnion hdisj hmeas]
  exact measure_mono (subset_univ _)

/-- The coding theorem for cylinders without change of scale: for a measure of mass at most one
computed by `A`, there is `c` such that `K^A(w) ≤ k + 2 (⌊log₂ |w|⌋ + 1) + c` whenever
`2^{-k} < μ[w]`. Blueprint node `meas:remarks`. -/
theorem cantorLS_exists_oracleComplexity_le (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible P shiftMap μ A) :
    ∃ c : ℕ, ∀ (w : List Bool) (k : ℕ), (2 : ℝ≥0∞)⁻¹ ^ k < μ (listCylinder w) →
      (oracleComplexity A w : ℝ) ≤ k + cantorLS_lenCost w + c := by
  classical
  have hlsc : IsLowerSemicomputableIn A fun w : List Bool ↦ (μ (listCylinder w)).toReal :=
    hA.2.2.lowerSemicomputable_ceOpen
      (isCeOpenFamilyIn_listCylinder (by norm_num) (by norm_num) cantor_hd P A hA.1 hP)
  have hlt : ∀ (w : List Bool) (k : ℕ), (2 : ℝ≥0∞)⁻¹ ^ k < μ (listCylinder w) ↔
      (((2 ^ k : ℚ)⁻¹ : ℚ) : ℝ) < (μ (listCylinder w)).toReal := by
    intro w k
    rw [← toReal_two_inv_pow, ENNReal.toReal_lt_toReal (by simp) (measure_ne_top _ _)]
  let F : BitString → Prop := fun w ↦ μ (listCylinder w) ≠ 0
  have hex : ∀ w, F w → ∃ k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k < μ (listCylinder w) :=
    fun w hw ↦ ENNReal.exists_inv_two_pow_lt hw
  let k₀ : Subtype F → ℕ := fun w ↦ Nat.find (hex w.1 w.2)
  let g : Subtype F → ℝ := fun w ↦ ((k₀ w + cantorLS_lenCost w.1 : ℕ) : ℝ)
  have hg : IsUpperSemicomputableOnIn A F g := by
    let U : BitString × ℚ → Prop := fun z ↦ ∃ k : ℕ,
      (((2 ^ k : ℚ)⁻¹ : ℚ) : ℝ) < (μ (listCylinder z.1)).toReal ∧
        (((k + cantorLS_lenCost z.1 : ℕ) : ℚ)) < z.2
    have hU : IsREIn A U := by
      have h1 : IsREIn A fun y : (BitString × ℚ) × ℕ ↦
          (((2 ^ y.2 : ℚ)⁻¹ : ℚ) : ℝ) < (μ (listCylinder y.1.1)).toReal :=
        hlsc.comp (f := fun y : (BitString × ℚ) × ℕ ↦ (y.1.1, ((2 ^ y.2 : ℚ)⁻¹ : ℚ)))
          ((Computable.fst.comp Computable.fst).pair
            (computable_rat_inv_two_pow.comp Computable.snd)).computableIn
      have hcost : Primrec fun y : (BitString × ℚ) × ℕ ↦ y.2 + cantorLS_lenCost y.1.1 :=
        Primrec.nat_add.comp Primrec.snd
          (cantorLS_primrec_lenCost.comp (Primrec.fst.comp Primrec.fst))
      have h2 : IsREIn A fun y : (BitString × ℚ) × ℕ ↦
          (((y.2 + cantorLS_lenCost y.1.1 : ℕ) : ℚ)) < y.1.2 :=
        isREIn_of_computable_decide (computable₂_ratLt.comp
          (computable_nat_to_rat.comp hcost.to_comp) (Computable.snd.comp Computable.fst))
      exact (h1.and h2).exists
    refine ⟨U, hU, ?_, ?_⟩
    · rintro w q ⟨k, hk, hq⟩
      have hk' := (hlt w k).2 hk
      have hF : F w := fun h0 ↦ by simp [h0] at hk'
      refine ⟨hF, ?_⟩
      have hmin : k₀ ⟨w, hF⟩ ≤ k := Nat.find_min' (hex w hF) hk'
      have hq' : ((k + cantorLS_lenCost w : ℕ) : ℝ) < q := by exact_mod_cast hq
      have hle : ((k₀ ⟨w, hF⟩ + cantorLS_lenCost w : ℕ) : ℝ) ≤
          ((k + cantorLS_lenCost w : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hmin _
      exact lt_of_le_of_lt hle hq'
    · intro w ε hε
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (g w) hε)
      refine ⟨q, ⟨k₀ w, (hlt w.1 (k₀ w)).1 (Nat.find_spec (hex w.1 w.2)), ?_⟩, hq2⟩
      have hq1' : ((k₀ w + cantorLS_lenCost w.1 : ℕ) : ℝ) < q := hq1
      exact_mod_cast hq1'
  -- the mass
  let a : ℕ → ℝ≥0∞ := fun m ↦ (2 : ℝ≥0∞)⁻¹ ^ (2 * (Nat.log 2 m + 1))
  let M : ℝ≥0∞ := ∑' w : List Bool, μ (listCylinder w) * a w.length
  have hM : ∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w) ≤ M := by
    have hterm : ∀ w : Subtype F, (2 : ℝ≥0∞) ^ (-g w) ≤ μ (listCylinder w.1) * a w.1.length := by
      intro w
      have hk : (2 : ℝ≥0∞)⁻¹ ^ k₀ w < μ (listCylinder w.1) := Nat.find_spec (hex w.1 w.2)
      rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow, pow_add]
      exact mul_le_mul' hk.le le_rfl
    calc ∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w)
        ≤ ∑' w : Subtype F, μ (listCylinder w.1) * a w.1.length := ENNReal.tsum_le_tsum hterm
      _ ≤ M := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
          (fun w : List Bool ↦ μ (listCylinder w) * a w.length)
  have hMfin : M < ⊤ := by
    have hsplit : ∀ w : List Bool, μ (listCylinder w) * a w.length =
        ∑' m : ℕ, a m * (if w.length = m then μ (listCylinder w) else 0) := by
      intro w
      rw [tsum_eq_single w.length fun m hm ↦ by simp [Ne.symm hm]]
      simp [mul_comm]
    calc M = ∑' m : ℕ, ∑' w : List Bool, a m * (if w.length = m then μ (listCylinder w) else 0) :=
          by rw [show M = ∑' w : List Bool, μ (listCylinder w) * a w.length from rfl,
              tsum_congr hsplit, ENNReal.tsum_comm]
      _ = ∑' m : ℕ, a m * ∑' w : List Bool, (if w.length = m then μ (listCylinder w) else 0) :=
          tsum_congr fun m ↦ ENNReal.tsum_mul_left
      _ ≤ ∑' m : ℕ, a m * 1 := ENNReal.tsum_le_tsum fun m ↦
          mul_le_mul' le_rfl ((cantorLS_tsum_length_eq_le μ m).trans hμ)
      _ < ⊤ := by simpa using tsum_inv_two_pow_log_lt_top
  obtain ⟨c, hc⟩ := oracle_coding_finite_mass A F g hg M hM hMfin
  refine ⟨c, fun w k hk ↦ ?_⟩
  have hF : F w := fun h0 ↦ by simp [h0] at hk
  have h := hc ⟨w, hF⟩
  have hmin : k₀ ⟨w, hF⟩ ≤ k := Nat.find_min' (hex w hF) hk
  have hle : g ⟨w, hF⟩ ≤ (k : ℝ) + cantorLS_lenCost w := by
    change ((k₀ ⟨w, hF⟩ + cantorLS_lenCost w : ℕ) : ℝ) ≤ _
    push_cast
    have : (k₀ ⟨w, hF⟩ : ℝ) ≤ k := by exact_mod_cast hmin
    linarith
  linarith

/-- Remark 3.4(b), coding direction (primed copy of
`oracleComplexity_cantorPrefix_le_infoBits`): if `A` computes a measure `μ` of mass at most one
and the symbols of the ideal points, then `K^A(x↾n) ≤ -log₂ μ[x↾n] + O(log n)` for every point
`x` and every `n ≥ 1` with `μ[x↾n] > 0`. Blueprint node `meas:remarks`. -/
theorem oracleComplexity_cantorPrefix_le_infoBits' (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible P shiftMap μ A) :
    ∃ c : ℝ, ∀ (x : ℕ → Bool) (n : ℕ), 1 ≤ n → μ (PiNat.cylinder x n) ≠ 0 →
      (oracleComplexity A (cantorPrefix x n) : ℝ) ≤
        (infoBits (μ (PiNat.cylinder x n))).toReal + c * Real.logb 2 n + c := by
  obtain ⟨c, hc⟩ := cantorLS_exists_oracleComplexity_le P A hP μ hμ hA
  refine ⟨(c : ℝ) + 3, fun x n _ h0 ↦ ?_⟩
  set q := μ (PiNat.cylinder x n) with hqdef
  have hq1 : q ≤ 1 := (measure_mono (subset_univ _)).trans hμ
  have hqpos : 0 < q.toReal := ENNReal.toReal_pos h0 (measure_ne_top _ _)
  set I := (infoBits q).toReal with hIdef
  have hI : I = -Real.logb 2 q.toReal := toReal_infoBits h0 hq1
  have hI0 : 0 ≤ I := ENNReal.toReal_nonneg
  let k : ℕ := ⌊I⌋₊ + 1
  have hkI : I < k := by
    simp only [k]
    push_cast
    exact Nat.lt_floor_add_one I
  have hkI' : (k : ℝ) ≤ I + 1 := by
    have := Nat.floor_le hI0
    simp only [k]
    push_cast
    linarith
  -- `2^{-k} < μ[x↾n]`
  have hreal : (2 : ℝ)⁻¹ ^ k < q.toReal := by
    have e1 : (2 : ℝ)⁻¹ ^ k = (2 : ℝ) ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
    have e2 : q.toReal = (2 : ℝ) ^ (Real.logb 2 q.toReal) :=
      (Real.rpow_logb (by norm_num) (by norm_num) hqpos).symm
    rw [e1, e2, Real.rpow_lt_rpow_left_iff (by norm_num)]
    linarith
  have hk : (2 : ℝ≥0∞)⁻¹ ^ k < μ (listCylinder (cantorPrefix x n)) := by
    rw [cantorLS_listCylinder_cantorPrefix, ← hqdef,
      ← ENNReal.toReal_lt_toReal (by simp) (measure_ne_top _ _)]
    simpa [ENNReal.toReal_pow, ENNReal.toReal_inv] using hreal
  have h := hc (cantorPrefix x n) k hk
  have hlen : (cantorPrefix x n).length = n := by simp [cantorPrefix]
  have hlog : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := Real.natLog_le_logb n 2
  have hl0 := logb_natCast_nonneg n
  have hcost : (cantorLS_lenCost (cantorPrefix x n) : ℝ) ≤ 2 * Real.logb 2 n + 2 := by
    simp only [cantorLS_lenCost, hlen]
    push_cast
    linarith
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hmul : 2 * Real.logb 2 n ≤ ((c : ℝ) + 3) * Real.logb 2 n := by nlinarith
  linarith

end cantor

end Kolmogorov.PointToSet
